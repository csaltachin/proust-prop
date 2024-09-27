use std::rc::Rc;

use crate::ast::{Expr, HoleWithEffect, Ty};

#[derive(Debug, PartialEq, Eq)]
pub enum TypeError<'so> {
    CannotSynth,
    CannotCheck,
    NotInContext(&'so str),
}

type TypeResult<'so, T> = Result<T, TypeError<'so>>;

#[derive(Clone)]
pub struct Context<'so> {
    ty_bindings: Vec<(&'so str, Rc<Ty<'so>>)>,
}

impl<'so> From<Vec<(&'so str, Rc<Ty<'so>>)>> for Context<'so> {
    fn from(ty_bindings: Vec<(&'so str, Rc<Ty<'so>>)>) -> Self {
        Self { ty_bindings }
    }
}

impl<'so> Context<'so> {
    fn lookup(&self, name: &'so str) -> Option<Rc<Ty<'so>>> {
        self.ty_bindings
            .iter()
            .rev()
            .find_map(|(k, v)| if *k == name { Some(v.clone()) } else { None })
    }

    fn push(&mut self, name: &'so str, ty: Rc<Ty<'so>>) {
        self.ty_bindings.push((name, ty));
    }

    fn pop(&mut self) -> Option<(&'so str, Rc<Ty<'so>>)> {
        self.ty_bindings.pop()
    }
}

pub fn type_check<'so, H>(
    ctx: &mut Context<'so>,
    expr: &Expr<'so, H>,
    ty: Rc<Ty<'so>>,
) -> TypeResult<'so, ()>
where
    H: HoleWithEffect<'so>,
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
        // For all other exprs we use [Turn]: try to synth T' for expr, and verify that T' === T
        _ => type_synth(ctx, expr).and_then(|actual_ty| {
            // NOTE: This uses the Eq trait, but it should be tweaked if we want to allow, for
            // example, actual_ty being a subtype of ty (hence casting to ty)
            if actual_ty == ty {
                Ok(())
            } else {
                Err(CannotCheck)
            }
        }),
    }
}

pub fn type_synth<'so, H>(
    ctx: &mut Context<'so>,
    expr: &Expr<'so, H>,
) -> TypeResult<'so, Rc<Ty<'so>>>
where
    H: HoleWithEffect<'so>,
{
    use Expr::*;
    use Ty::*;
    use TypeError::*;

    match expr {
        // Cannot synth lambdas
        Lambda { .. } => Err(CannotSynth),
        // To synth App as W, try to synth func as T -> W, then check arg : T
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
        // The only way to synth an ExpVar is if the context has a binding for the ident
        ExpVar { ident } => ctx.lookup(ident).ok_or(NotInContext(ident)),
        ExpHole(..) => Err(CannotSynth),
    }
}

// Tests

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::PureExpr;
    use Expr::*;
    use Ty::*;
    use TypeError::*;

    #[test]
    fn simple_checks() {
        // Check ExpVar that is already in context...
        let expr: PureExpr = ExpVar { ident: "x" };
        let ty = Rc::new(TyVar { ident: "T" });
        let mut ctx: Context = vec![("x", ty.clone())].into();
        let check_res = type_check(&mut ctx, &expr, ty.clone());
        assert_eq!(check_res, Ok(()));

        // ...and without context
        let mut ctx: Context = vec![].into();
        let check_res = type_check(&mut ctx, &expr, ty);
        // The check tries a synth and propagates the synth error
        assert_eq!(check_res, Err(NotInContext("x")));

        // Check identity lambda as T -> T (with empty context)
        let expr: PureExpr = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "x" }).into(),
        };
        let ty = Rc::new(Arrow {
            // These two idents can be whatever as long as they're equal
            domain: (TyVar { ident: "T" }).into(),
            range: (TyVar { ident: "T" }).into(),
        });
        let mut ctx: Context = vec![].into();
        let check_res = type_check(&mut ctx, &expr, ty);
        assert_eq!(check_res, Ok(()));

        // Check constant lambda as T -> W with (c : W) in context...
        let expr: PureExpr = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "c" }).into(),
        };
        let lambda_ty = Rc::new(Arrow {
            domain: (TyVar { ident: "T" }).into(),
            range: (TyVar { ident: "W" }).into(),
        });
        let c_ty = Rc::new(TyVar { ident: "W" });
        let mut ctx: Context = vec![("c", c_ty)].into();
        let check_res = type_check(&mut ctx, &expr, lambda_ty.clone());
        assert_eq!(check_res, Ok(()));

        // ... and without (c : W) in context
        let mut ctx: Context = vec![].into();
        let check_res = type_check(&mut ctx, &expr, lambda_ty);
        // This will check (c : W), use Turn, fail to synth, and forward the synth error
        assert_eq!(check_res, Err(NotInContext("c")));

        // Check application (f a : T) with both f, a in context...
        let expr: PureExpr = App {
            func: (ExpVar { ident: "f" }).into(),
            arg: (ExpVar { ident: "a" }).into(),
        };
        let app_ty = Rc::new(TyVar { ident: "W" });
        let f_ty = Rc::new(Arrow {
            domain: (TyVar { ident: "T" }).into(),
            range: (TyVar { ident: "W" }).into(),
        });
        let a_ty = Rc::new(TyVar { ident: "T" });
        let mut ctx: Context = vec![("f", f_ty), ("a", a_ty)].into();
        let check_res = type_check(&mut ctx, &expr, app_ty.clone());
        assert_eq!(check_res, Ok(()));

        // ...and with neither in context
        let mut ctx: Context = vec![].into();
        let check_res = type_check(&mut ctx, &expr, app_ty);
        // The synth error is from turning on either (f : T -> W) or (a : T)
        assert_eq!(check_res, Err(NotInContext("f")));

        // Check application of un-annotated identity lambda to identity lambda...
        let id1: PureExpr = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "x" }).into(),
        };
        let id2: PureExpr = Lambda {
            var_ident: "y",
            body: (ExpVar { ident: "y" }).into(),
        };
        let expr: PureExpr = App {
            func: id1.into(),
            arg: id2.into(),
        };
        // Checking for T -> T
        let ty = Rc::new(Arrow {
            domain: (TyVar { ident: "T" }).into(),
            range: (TyVar { ident: "T" }).into(),
        });
        let mut ctx: Context = vec![].into(); // Empty context
        let check_res = type_check(&mut ctx, &expr, ty);
        // Should fail with CannotSynth; it will try to synth id1, but we can't synth lambdas
        assert_eq!(check_res, Err(CannotSynth));

        // ...and check the same application but with the left identity annotated correctly
        let id1: PureExpr = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "x" }).into(),
        };
        let id2: PureExpr = Lambda {
            var_ident: "y",
            body: (ExpVar { ident: "y" }).into(),
        };
        // We annotate id1 with (T -> T) -> (T -> T)...
        let id1_ty = Arrow {
            domain: (Arrow {
                domain: (TyVar { ident: "T" }).into(),
                range: (TyVar { ident: "T" }).into(),
            })
            .into(),
            range: (Arrow {
                domain: (TyVar { ident: "T" }).into(),
                range: (TyVar { ident: "T" }).into(),
            })
            .into(),
        };
        let ann_expr: PureExpr = App {
            func: (Ann {
                expr: id1.into(),
                ty: id1_ty.into(),
            })
            .into(),
            arg: id2.into(),
        };
        // ...so that after application, we can infer T -> T
        let ty = Rc::new(Arrow {
            domain: (TyVar { ident: "T" }).into(),
            range: (TyVar { ident: "T" }).into(),
        });
        let mut ctx: Context = vec![].into();
        let check_res = type_check(&mut ctx, &ann_expr, ty);
        assert_eq!(check_res, Ok(()))
    }

    #[test]
    fn simple_synths() {
        // Synth for ExpVar that is already in context
        let expr: PureExpr = ExpVar { ident: "x" };
        let ty = Rc::new(TyVar { ident: "T" });
        let mut ctx: Context = vec![("x", ty.clone())].into();
        let synth_res = type_synth(&mut ctx, &expr);
        assert_eq!(synth_res, Ok(ty));

        // Synth for ExpVar not in context
        let expr: PureExpr = ExpVar { ident: "x" };
        let mut ctx: Context = vec![].into();
        let synth_res = type_synth(&mut ctx, &expr);
        assert_eq!(synth_res, Err(NotInContext("x")));

        // TODO: add more synth tests
    }
}
