use std::{fmt::Display, marker::PhantomData, rc::Rc};

use crate::ast::{Expr, HoleKind, IdentKind, Ty};

#[derive(Debug, PartialEq, Eq)]
pub enum TypeError<'so, S>
where
    S: IdentKind<'so>,
{
    CannotSynth,
    CannotCheck,
    NotInContext(S, PhantomData<&'so ()>),
}

impl<'so, S> Display for TypeError<'so, S>
where
    S: IdentKind<'so>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CannotSynth => write!(f, "Cannot synthesize"),
            Self::CannotCheck => write!(f, "Cannot check"),
            Self::NotInContext(ident, _) => {
                write!(f, "Cannot find variable \"{ident}\" in context")
            }
        }
    }
}

type TypeResult<'so, S, T> = Result<T, TypeError<'so, S>>;

#[derive(Clone)]
pub struct Context<'so, S>
where
    S: IdentKind<'so>,
{
    ty_bindings: Vec<(S, Rc<Ty<'so, S>>)>,
}

impl<'so, S> From<Vec<(S, Rc<Ty<'so, S>>)>> for Context<'so, S>
where
    S: IdentKind<'so>,
{
    fn from(ty_bindings: Vec<(S, Rc<Ty<'so, S>>)>) -> Self {
        Self { ty_bindings }
    }
}

impl<'so, S> Context<'so, S>
where
    S: IdentKind<'so>,
{
    fn lookup(&self, name: &S) -> Option<Rc<Ty<'so, S>>> {
        self.ty_bindings
            .iter()
            .rev()
            .find_map(|(k, v)| if *k == *name { Some(v.clone()) } else { None })
    }

    fn push(&mut self, name: &S, ty: Rc<Ty<'so, S>>) {
        // TODO: This clones the key to insert it, is there a better way to parametrize this?
        self.ty_bindings.push((name.clone(), ty));
    }

    fn pop(&mut self) -> Option<(S, Rc<Ty<'so, S>>)> {
        self.ty_bindings.pop()
    }

    pub fn is_empty(&self) -> bool {
        self.ty_bindings.is_empty()
    }

    pub fn get_bindings(&self) -> &Vec<(S, Rc<Ty<'so, S>>)> {
        &self.ty_bindings
    }
}

pub fn type_check<'so, S, H>(
    ctx: &mut Context<'so, S>,
    expr: &Expr<'so, S, H>,
    ty: Rc<Ty<'so, S>>,
) -> TypeResult<'so, S, ()>
where
    S: IdentKind<'so>,
    H: HoleKind<'so, S>,
{
    use Expr::*;
    use Ty::*;
    use TypeError::*;

    match expr {
        // Holes check trivially. We just inject the hole effect
        ExpHole(hole) => {
            hole.check(ty, ctx);
            Ok(())
        }
        // Handle lambdas
        Lambda { var_ident, body } => match ty.as_ref() {
            // We can check lambda : T -> W by checking if, given var_ident : T, we can check body : W
            Arrow { domain, range } => {
                ctx.push(var_ident, domain.clone());
                let check_res = type_check(ctx, body, range.clone());
                let _ = ctx.pop();
                check_res
            }
            // But if ty is not of the form T -> W, then we failed, because we can't synth lambdas
            _ => Err(CannotCheck),
        },
        // Handle products
        Pair { left, right } => match ty.as_ref() {
            // To check Pair as T & W, check left : T and right : W
            Con {
                left: left_ty,
                right: right_ty,
            } => {
                type_check(ctx, left, left_ty.clone())?;
                type_check(ctx, right, right_ty.clone())?;
                Ok(())
            }
            // If ty is not a conjunction, it's a mismatch for a pair
            _ => Err(CannotCheck),
        },
        // Handle sums
        Left { inner } => match ty.as_ref() {
            Dis { left: left_ty, .. } => {
                type_check(ctx, inner, left_ty.clone())?;
                Ok(())
            }
            _ => Err(CannotCheck),
        },
        Right { inner } => match ty.as_ref() {
            Dis {
                right: right_ty, ..
            } => {
                type_check(ctx, inner, right_ty.clone())?;
                Ok(())
            }
            _ => Err(CannotCheck),
        },
        // Matching on a sum
        Match {
            arg,
            f_left,
            f_right,
        } => match type_synth(ctx, arg)?.as_ref() {
            Dis {
                left: left_ty,
                right: right_ty,
            } => {
                let left_arrow = Arrow {
                    domain: left_ty.clone(),
                    range: ty.clone(),
                };
                type_check(ctx, f_left, left_arrow.into())?;

                let right_arrow = Arrow {
                    domain: right_ty.clone(),
                    range: ty.clone(),
                };
                type_check(ctx, f_right, right_arrow.into())?;

                Ok(())
            }
            _ => Err(CannotCheck),
        },
        // Handle Never
        Never { inner } => {
            type_check(ctx, inner, Bottom.into())?;
            Ok(())
        }
        // For all other exprs we use [Turn]: try to synth T' for expr, and verify that T' === T
        _ => type_synth(ctx, expr).and_then(|actual_ty| {
            if actual_ty == ty {
                Ok(())
            } else {
                Err(CannotCheck)
            }
        }),
    }
}

pub fn type_synth<'so, S, H>(
    ctx: &mut Context<'so, S>,
    expr: &Expr<'so, S, H>,
) -> TypeResult<'so, S, Rc<Ty<'so, S>>>
where
    S: IdentKind<'so>,
    H: HoleKind<'so, S>,
{
    use Expr::*;
    use Ty::*;
    use TypeError::*;

    match expr {
        // Cannot synth lambdas
        Lambda { .. } => Err(CannotSynth),
        // To synth App as some W, try to synth func as T -> W, then check arg : T
        App { func, arg } => {
            let func_synth = type_synth(ctx, func)?;
            match &*func_synth {
                Arrow { domain, range } => {
                    type_check(ctx, arg, domain.clone())?;
                    Ok(range.clone())
                }
                _ => Err(CannotSynth),
            }
        }
        // To synth Ann as the annotated T, just check expr : T
        Ann { expr, ty } => type_check(ctx, expr, ty.clone())
            .map(|()| ty.clone())
            .map_err(|_| CannotSynth),
        // To synth First as some T, try to synth pair as T & W and pick T
        First { pair } => {
            let pair_synth = type_synth(ctx, pair)?;
            match &*pair_synth {
                Con { left, .. } => Ok(left.clone()),
                _ => Err(CannotSynth),
            }
        }
        // To synth Second as some W, try to synth pair as T & W and pick W
        Second { pair } => {
            let pair_synth = type_synth(ctx, pair)?;
            match &*pair_synth {
                Con { right, .. } => Ok(right.clone()),
                _ => Err(CannotSynth),
            }
        }
        // The only way to synth an ExpVar is if the context has a binding for the ident
        ExpVar { ident } => ctx
            .lookup(ident)
            // The ident is cloned to be held by the error
            .ok_or(NotInContext(ident.clone(), PhantomData)),
        ExpHole(..) => Err(CannotSynth),
        // TODO: do we want synth rules for Pair, First, Second, etc?
        _ => Err(CannotSynth),
    }
}

// Tests

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::UnitHole;
    use Expr::*;
    use Ty::*;
    use TypeError::*;

    type PureExprWithBorrowedIdents<'so> = Expr<'so, &'so str, UnitHole>;
    type StaticContext = Context<'static, &'static str>;

    fn ty_var<'so, S>(ident: S) -> Ty<'so, S>
    where
        S: IdentKind<'so>,
    {
        TyVar {
            ident,
            phantom: PhantomData,
        }
    }

    fn err_not_in_context<'so, S, T>(ident: S) -> TypeResult<'so, S, T>
    where
        S: IdentKind<'so>,
    {
        Err(NotInContext(ident, PhantomData))
    }

    #[test]
    fn simple_checks() {
        // Check ExpVar that is already in context...
        let expr: PureExprWithBorrowedIdents = ExpVar { ident: "x" };
        let ty = Rc::new(ty_var("T"));
        let mut ctx: StaticContext = vec![("x", ty.clone())].into();
        let check_res = type_check(&mut ctx, &expr, ty.clone());
        assert_eq!(check_res, Ok(()));

        // ...and without context
        let mut ctx: StaticContext = vec![].into();
        let check_res = type_check(&mut ctx, &expr, ty);
        // The check tries a synth and propagates the synth error
        assert_eq!(check_res, err_not_in_context("x"));

        // Check identity lambda as T -> T (with empty context)
        let expr: PureExprWithBorrowedIdents = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "x" }).into(),
        };
        let ty = Rc::new(Arrow {
            // These two idents can be whatever as long as they're equal
            domain: (ty_var("T")).into(),
            range: (ty_var("T")).into(),
        });
        let mut ctx: StaticContext = vec![].into();
        let check_res = type_check(&mut ctx, &expr, ty);
        assert_eq!(check_res, Ok(()));

        // Check constant lambda as T -> W with (c : W) in context...
        let expr: PureExprWithBorrowedIdents = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "c" }).into(),
        };
        let lambda_ty = Rc::new(Arrow {
            domain: (ty_var("T")).into(),
            range: (ty_var("W")).into(),
        });
        let c_ty = Rc::new(ty_var("W"));
        let mut ctx: StaticContext = vec![("c", c_ty)].into();
        let check_res = type_check(&mut ctx, &expr, lambda_ty.clone());
        assert_eq!(check_res, Ok(()));

        // ... and without (c : W) in context
        let mut ctx: StaticContext = vec![].into();
        let check_res = type_check(&mut ctx, &expr, lambda_ty);
        // This will check (c : W), use Turn, fail to synth, and forward the synth error
        assert_eq!(check_res, err_not_in_context("c"));

        // Check application (f a : T) with both f, a in context...
        let expr: PureExprWithBorrowedIdents = App {
            func: (ExpVar { ident: "f" }).into(),
            arg: (ExpVar { ident: "a" }).into(),
        };
        let app_ty = Rc::new(ty_var("W"));
        let f_ty = Rc::new(Arrow {
            domain: (ty_var("T")).into(),
            range: (ty_var("W")).into(),
        });
        let a_ty = Rc::new(ty_var("T"));
        let mut ctx: StaticContext = vec![("f", f_ty), ("a", a_ty)].into();
        let check_res = type_check(&mut ctx, &expr, app_ty.clone());
        assert_eq!(check_res, Ok(()));

        // ...and with neither in context
        let mut ctx: StaticContext = vec![].into();
        let check_res = type_check(&mut ctx, &expr, app_ty);
        // The synth error is from turning on either (f : T -> W) or (a : T)
        assert_eq!(check_res, err_not_in_context("f"));

        // Check application of un-annotated identity lambda to identity lambda...
        let id1: PureExprWithBorrowedIdents = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "x" }).into(),
        };
        let id2: PureExprWithBorrowedIdents = Lambda {
            var_ident: "y",
            body: (ExpVar { ident: "y" }).into(),
        };
        let expr: PureExprWithBorrowedIdents = App {
            func: id1.into(),
            arg: id2.into(),
        };
        // Checking for T -> T
        let ty = Rc::new(Arrow {
            domain: (ty_var("T")).into(),
            range: (ty_var("T")).into(),
        });
        let mut ctx: StaticContext = vec![].into(); // Empty context
        let check_res = type_check(&mut ctx, &expr, ty);
        // Should fail with CannotSynth; it will try to synth id1, but we can't synth lambdas
        assert_eq!(check_res, Err(CannotSynth));

        // ...and check the same application but with the left identity annotated correctly
        let id1: PureExprWithBorrowedIdents = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "x" }).into(),
        };
        let id2: PureExprWithBorrowedIdents = Lambda {
            var_ident: "y",
            body: (ExpVar { ident: "y" }).into(),
        };
        // We annotate id1 with (T -> T) -> (T -> T)...
        let id1_ty = Arrow {
            domain: (Arrow {
                domain: (ty_var("T")).into(),
                range: (ty_var("T")).into(),
            })
            .into(),
            range: (Arrow {
                domain: (ty_var("T")).into(),
                range: (ty_var("T")).into(),
            })
            .into(),
        };
        let ann_expr: PureExprWithBorrowedIdents = App {
            func: (Ann {
                expr: id1.into(),
                ty: id1_ty.into(),
            })
            .into(),
            arg: id2.into(),
        };
        // ...so that after application, we can infer T -> T
        let ty = Rc::new(Arrow {
            domain: (ty_var("T")).into(),
            range: (ty_var("T")).into(),
        });
        let mut ctx: StaticContext = vec![].into();
        let check_res = type_check(&mut ctx, &ann_expr, ty);
        assert_eq!(check_res, Ok(()))
    }

    #[test]
    fn simple_synths() {
        // Synth for ExpVar that is already in context
        let expr: PureExprWithBorrowedIdents = ExpVar { ident: "x" };
        let ty = Rc::new(ty_var("T"));
        let mut ctx: StaticContext = vec![("x", ty.clone())].into();
        let synth_res = type_synth(&mut ctx, &expr);
        assert_eq!(synth_res, Ok(ty));

        // Synth for ExpVar not in context
        let expr: PureExprWithBorrowedIdents = ExpVar { ident: "x" };
        let mut ctx: StaticContext = vec![].into();
        let synth_res = type_synth(&mut ctx, &expr);
        assert_eq!(synth_res, err_not_in_context("x"));

        // TODO: add more synth tests
    }
}
