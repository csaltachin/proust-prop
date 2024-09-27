use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::rc::Rc;

use crate::ast::{Expr, HoleWithEffect, PureExpr, Ty};
use crate::check::{type_check, Context, TypeError};

// Maps goal IDs to (ty, context) pairs.

type GoalMap<'so> = HashMap<usize, (Rc<Ty<'so>>, Context<'so>)>;

fn push_goal<'so>(map: &mut GoalMap<'so>, id: usize, ty: Rc<Ty<'so>>, ctx: Context<'so>) {
    map.insert(id, (ty, ctx));
}

fn pop_goal<'so>(map: &mut GoalMap<'so>, id: usize) {
    let _ = map.remove(&id);
}

// A hole type for use in an assistant session; attaches a goal ID and updates goals when checked

struct Goal<'so> {
    id: usize,
    map: Rc<RefCell<GoalMap<'so>>>,
}

impl Display for Goal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.id)
    }
}

impl Debug for Goal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_goal_{}", self.id)
    }
}

impl PartialEq for Goal<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Goal<'_> {}

impl<'so> HoleWithEffect<'so> for Goal<'so> {
    fn check(&self, ty: Rc<Ty<'so>>, ctx: &Context<'so>) {
        push_goal(&mut self.map.borrow_mut(), self.id, ty.clone(), ctx.clone());
    }
}

// A type alias for expressions with goals

type GoalExpr<'so> = Expr<'so, Goal<'so>>;

// Assistant state

enum AssistantError<'so> {
    CannotRefine(TypeError<'so>),
    BadGoalID(usize),
}

struct Assistant<'so> {
    task: Rc<Ty<'so>>,
    current_expr: Option<Expr<'so, Goal<'so>>>, // None means uninitialized
    goal_counter: usize,
    goal_map: Rc<RefCell<GoalMap<'so>>>,
}

impl<'so> Assistant<'so> {
    fn make_assistant(task: Rc<Ty<'so>>) -> Assistant<'so> {
        let mut map: GoalMap<'so> = HashMap::new();
        map.insert(0, (task.clone(), vec![].into()));
        let goal_map = Rc::new(RefCell::new(map));
        let mut assistant = Self {
            task,
            current_expr: None,
            goal_counter: 1,
            goal_map,
        };
        let init_expr: GoalExpr<'so> = Expr::ExpHole(Goal {
            id: 0,
            map: assistant.goal_map.clone(),
        });
        let _ = assistant.current_expr.insert(init_expr);
        assistant
    }

    fn refine_goal(
        &mut self,
        id: usize,
        pure_expr: PureExpr<'so>,
    ) -> Result<(), AssistantError<'so>> {
        // Retrieve the task's type and context
        let (task_ty, mut task_ctx) = self
            .goal_map
            .borrow_mut()
            .remove(&id)
            .ok_or(AssistantError::BadGoalID(id))?;
        // Typecheck the pure expression with the task's (ty, ctx); no side effects
        match type_check(&mut task_ctx, &pure_expr, task_ty.clone()) {
            Err(ty_err) => {
                self.goal_map.borrow_mut().insert(id, (task_ty, task_ctx));
                Err(AssistantError::CannotRefine(ty_err))
            }
            Ok(()) => {
                // Convert holes into goals and check again with goal side effects
                let goal_expr = self.number_holes(pure_expr);
                // Should not panic because the previous check worked
                type_check(&mut task_ctx, &goal_expr, task_ty).unwrap();
                // Update current_expr by substituting into hole id
                let old_curr_expr = self.current_expr.take();
                self.current_expr = old_curr_expr.map(|old| {
                    let (new_curr_expr, _) = self.fill_goal(old, id, goal_expr);
                    new_curr_expr
                });
                // Done!
                Ok(())
            }
        }
    }

    // Include the repl in return if no substitution happened
    fn fill_goal(
        &mut self,
        expr: GoalExpr<'so>,
        repl_id: usize,
        repl: GoalExpr<'so>,
    ) -> (GoalExpr<'so>, Option<GoalExpr<'so>>) {
        use Expr::*;
        match expr {
            ExpVar { ident } => (ExpVar { ident }, Some(repl)),
            Lambda { var_ident, body } => {
                let (new_body, maybe_repl) = self.fill_goal(*body, repl_id, repl);
                (
                    Lambda {
                        var_ident,
                        body: new_body.into(),
                    },
                    maybe_repl,
                )
            }
            App { func, arg } => match self.fill_goal(*func, repl_id, repl) {
                (new_func, None) => (
                    App {
                        func: new_func.into(),
                        arg,
                    },
                    None,
                ),
                (same_func, Some(same_repl)) => {
                    let (new_arg, maybe_repl) = self.fill_goal(*arg, repl_id, same_repl);
                    (
                        App {
                            func: same_func.into(),
                            arg: new_arg.into(),
                        },
                        maybe_repl,
                    )
                }
            },
            Ann { expr: inner, ty } => {
                let (new_inner, maybe_repl) = self.fill_goal(*inner, repl_id, repl);
                (
                    Ann {
                        expr: new_inner.into(),
                        ty,
                    },
                    maybe_repl,
                )
            }
            ExpHole(Goal { id, map }) => {
                if id == repl_id {
                    (repl, None)
                } else {
                    (ExpHole(Goal { id, map }), Some(repl))
                }
            }
        }
    }

    fn number_holes(&mut self, expr: PureExpr<'so>) -> GoalExpr<'so> {
        use Expr::*;
        match expr {
            ExpVar { ident } => ExpVar { ident },
            Lambda { var_ident, body } => Lambda {
                var_ident,
                body: self.number_holes(*body).into(),
            },
            App { func, arg } => {
                // TODO: does this panic?
                // (I think it shouldn't, we are just cloning an Rc at the leafs)
                let new_func = self.number_holes(*func);
                let new_arg = self.number_holes(*arg);
                App {
                    func: new_func.into(),
                    arg: new_arg.into(),
                }
            }
            Ann { expr: inner, ty } => Ann {
                expr: self.number_holes(*inner).into(),
                ty,
            },
            ExpHole(()) => {
                let id = self.goal_counter;
                self.goal_counter += 1;
                ExpHole(Goal {
                    id,
                    map: self.goal_map.clone(),
                })
            }
        }
    }
}
