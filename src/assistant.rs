use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::rc::Rc;

use crate::ast::{Expr, HoleKind, IdentKind, PureExpr, Ty};
use crate::check::{type_check, Context, TypeError};

// Maps goal IDs to (ty, context) pairs.

type GoalMap<'so, S> = HashMap<usize, (Rc<Ty<'so, S>>, Context<'so, S>)>;

fn push_goal<'so, S>(map: &mut GoalMap<'so, S>, id: usize, ty: Rc<Ty<'so, S>>, ctx: Context<'so, S>)
where
    S: IdentKind<'so>,
{
    map.insert(id, (ty, ctx));
}

// A hole type for use in an assistant session; attaches a goal ID and updates goals when checked

struct Goal<'so, S: IdentKind<'so>> {
    id: usize,
    map: Rc<RefCell<GoalMap<'so, S>>>,
}

impl<'so, S> Display for Goal<'so, S>
where
    S: IdentKind<'so>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.id)
    }
}

impl<'so, S> Debug for Goal<'so, S>
where
    S: IdentKind<'so>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_goal_{}", self.id)
    }
}

impl<'so, S> PartialEq for Goal<'so, S>
where
    S: IdentKind<'so>,
{
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<'so, S> Eq for Goal<'so, S> where S: IdentKind<'so> {}

impl<'so, S> HoleKind<'so, S> for Goal<'so, S>
where
    S: IdentKind<'so>,
{
    fn check(&self, ty: Rc<Ty<'so, S>>, ctx: &Context<'so, S>) {
        push_goal(&mut self.map.borrow_mut(), self.id, ty.clone(), ctx.clone());
    }
}

// A type alias for expressions with goals

type GoalExpr<'so, S> = Expr<'so, S, Goal<'so, S>>;

// Assistant state

pub enum AssistantError<'so, S>
where
    S: IdentKind<'so>,
{
    CannotRefine(TypeError<'so, S>),
    BadGoalID(usize),
}

// Assistant is parametric on the ident kind, but in the REPL we'll use owned String idents

pub struct Assistant<'so, S>
where
    S: IdentKind<'so>,
{
    task: Rc<Ty<'so, S>>,
    current_expr: Option<Expr<'so, S, Goal<'so, S>>>, // None means uninitialized
    goal_counter: usize,
    goal_map: Rc<RefCell<GoalMap<'so, S>>>,
}

impl<'so, S> Assistant<'so, S>
where
    S: IdentKind<'so>,
{
    pub fn make_assistant(task: Ty<'so, S>) -> Assistant<'so, S> {
        let task = Rc::new(task);
        let mut map: GoalMap<'so, S> = HashMap::new();
        map.insert(0, (task.clone(), vec![].into()));
        let goal_map = Rc::new(RefCell::new(map));
        let mut assistant = Self {
            task,
            current_expr: None,
            goal_counter: 1,
            goal_map,
        };
        let init_expr: GoalExpr<'so, S> = Expr::ExpHole(Goal {
            id: 0,
            map: assistant.goal_map.clone(),
        });
        let _ = assistant.current_expr.insert(init_expr);
        assistant
    }

    pub fn refine_goal(
        &mut self,
        id: usize,
        pure_expr: PureExpr<'so, S>,
    ) -> Result<(), AssistantError<'so, S>> {
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
        expr: GoalExpr<'so, S>,
        repl_id: usize,
        repl: GoalExpr<'so, S>,
    ) -> (GoalExpr<'so, S>, Option<GoalExpr<'so, S>>) {
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
            First { pair } => {
                let (new_pair, maybe_repl) = self.fill_goal(*pair, repl_id, repl);
                (
                    First {
                        pair: new_pair.into(),
                    },
                    maybe_repl,
                )
            }
            Second { pair } => {
                let (new_pair, maybe_repl) = self.fill_goal(*pair, repl_id, repl);
                (
                    Second {
                        pair: new_pair.into(),
                    },
                    maybe_repl,
                )
            }
            Left { inner } => {
                let (new_inner, maybe_repl) = self.fill_goal(*inner, repl_id, repl);
                (
                    Left {
                        inner: new_inner.into(),
                    },
                    maybe_repl,
                )
            }
            Right { inner } => {
                let (new_inner, maybe_repl) = self.fill_goal(*inner, repl_id, repl);
                (
                    Right {
                        inner: new_inner.into(),
                    },
                    maybe_repl,
                )
            }
            Never { inner } => {
                let (new_inner, maybe_repl) = self.fill_goal(*inner, repl_id, repl);
                (
                    Never {
                        inner: new_inner.into(),
                    },
                    maybe_repl,
                )
            }
            Pair { left, right } => match self.fill_goal(*left, repl_id, repl) {
                (new_left, None) => (
                    Pair {
                        left: new_left.into(),
                        right,
                    },
                    None,
                ),
                (same_left, Some(same_repl)) => {
                    let (new_right, maybe_repl) = self.fill_goal(*right, repl_id, same_repl);
                    (
                        Pair {
                            left: same_left.into(),
                            right: new_right.into(),
                        },
                        maybe_repl,
                    )
                }
            },
            Match {
                arg,
                f_left,
                f_right,
            } => match self.fill_goal(*arg, repl_id, repl) {
                (new_arg, None) => (
                    Match {
                        arg: new_arg.into(),
                        f_left,
                        f_right,
                    },
                    None,
                ),
                (same_arg, Some(same_repl)) => match self.fill_goal(*f_left, repl_id, same_repl) {
                    (new_f_left, None) => (
                        Match {
                            arg: same_arg.into(),
                            f_left: new_f_left.into(),
                            f_right,
                        },
                        None,
                    ),
                    (same_f_left, Some(same_repl_again)) => {
                        let (new_f_right, maybe_repl) =
                            self.fill_goal(*f_right, repl_id, same_repl_again);
                        (
                            Match {
                                arg: same_arg.into(),
                                f_left: same_f_left.into(),
                                f_right: new_f_right.into(),
                            },
                            maybe_repl,
                        )
                    }
                },
            },
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
            ExpHole(Goal { id, map }) => {
                if id == repl_id {
                    (repl, None)
                } else {
                    (ExpHole(Goal { id, map }), Some(repl))
                }
            }
        }
    }

    fn number_holes(&mut self, expr: PureExpr<'so, S>) -> GoalExpr<'so, S> {
        use Expr::*;
        match expr {
            ExpVar { ident } => ExpVar { ident },
            Lambda { var_ident, body } => Lambda {
                var_ident,
                body: self.number_holes(*body).into(),
            },
            Ann { expr: inner, ty } => Ann {
                expr: self.number_holes(*inner).into(),
                ty,
            },
            First { pair } => First {
                pair: self.number_holes(*pair).into(),
            },
            Second { pair } => Second {
                pair: self.number_holes(*pair).into(),
            },
            Left { inner } => Left {
                inner: self.number_holes(*inner).into(),
            },
            Right { inner } => Right {
                inner: self.number_holes(*inner).into(),
            },
            Never { inner } => Never {
                inner: self.number_holes(*inner).into(),
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
            Pair { left, right } => {
                let new_left = self.number_holes(*left);
                let new_right = self.number_holes(*right);
                Pair {
                    left: new_left.into(),
                    right: new_right.into(),
                }
            }
            Match {
                arg,
                f_left,
                f_right,
            } => {
                let new_arg = self.number_holes(*arg);
                let new_f_left = self.number_holes(*f_left);
                let new_f_right = self.number_holes(*f_right);
                Match {
                    arg: new_arg.into(),
                    f_left: new_f_left.into(),
                    f_right: new_f_right.into(),
                }
            }
            ExpHole(_) => {
                let id = self.goal_counter;
                self.goal_counter += 1;
                ExpHole(Goal {
                    id,
                    map: self.goal_map.clone(),
                })
            }
        }
    }

    // Some helper methods for REPL printing

    pub fn pretty_print_goals(&self) -> Vec<String> {
        self.goal_map
            .borrow()
            .iter()
            .map(|(id, (ty, ctx))| {
                let ctx_str = if ctx.is_empty() {
                    String::new()
                } else {
                    let pairs_str = ctx
                        .get_bindings()
                        .iter()
                        .map(|(var, ty)| format!("\n|     {var} : {ty}"))
                        .collect::<Vec<_>>()
                        .concat();
                    format!("\n|   with context:{pairs_str}")
                };
                format!("* ?{id} : {ty}{ctx_str}")
            })
            .collect()
    }

    pub fn pretty_print_status(&self) -> String {
        let goals_left = self.goal_map.borrow().len();
        let task_str = self.task.to_string();
        let expr_str = self
            .current_expr
            .as_ref()
            .map(|ex| ex.to_string())
            .unwrap_or("<uninitialized>".to_string());

        if goals_left == 0 {
            format!("Task complete! Found a proof of {task_str}:\n  {expr_str}")
        } else {
            let s = if goals_left == 1 { "" } else { "s" };
            format!("Task with {goals_left} goal{s} is now:\n  {expr_str} : {task_str}")
        }
    }
}
