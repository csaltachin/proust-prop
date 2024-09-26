use crate::ast::{Expr, Ty};

#[derive(Debug, PartialEq, Eq)]
pub enum TypeError<'so> {
    CannotSynth,
    CannotCheck,
    NotInContext(&'so str),
}

type TypeResult<'so, T> = Result<T, TypeError<'so>>;

pub struct Context<'so> {
    ty_bindings: Vec<(&'so str, &'so Ty<'so>)>,
}

impl<'so> From<Vec<(&'so str, &'so Ty<'so>)>> for Context<'so> {
    fn from(ty_bindings: Vec<(&'so str, &'so Ty<'so>)>) -> Self {
        Self { ty_bindings }
    }
}

impl<'so> Context<'so> {
    fn lookup(&self, name: &'so str) -> Option<&'so Ty<'so>> {
        self.ty_bindings
            .iter()
            .rev()
            .find_map(|(k, v)| if *k == name { Some(*v) } else { None })
    }

    fn push(&mut self, name: &'so str, ty: &'so Ty<'so>) {
        self.ty_bindings.push((name, ty));
    }

    fn pop(&mut self) -> Option<(&'so str, &'so Ty<'so>)> {
        self.ty_bindings.pop()
    }
}

// In these functions, the Expr and Ty input borrows are annotated with 'so for convenience,
// because any lifetimes 'ex >= 'so and 'ty >= 'so work. It makes no sense for an Expr<'so> borrow
// to outlive the 'so lifetime, etc.

pub fn type_check<'so>(
    ctx: &mut Context<'so>,
    expr: &'so Expr<'so>,
    ty: &'so Ty<'so>,
) -> TypeResult<'so, ()> {
    use Expr::*;
    use Ty::*;
    use TypeError::*;

    match expr {
        // We first handle lambdas
        Lambda { var_ident, body } => match ty {
            // We can check lambda : T -> W by checking if, given var_ident : T, we can check body : W
            Arrow { domain, range } => {
                ctx.push(var_ident, domain);
                let check_res = type_check(ctx, body, range);
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

pub fn type_synth<'so>(
    ctx: &mut Context<'so>,
    expr: &'so Expr<'so>,
) -> TypeResult<'so, &'so Ty<'so>> {
    use Expr::*;
    use Ty::*;
    use TypeError::*;

    match expr {
        // Cannot synth lambdas
        Lambda { .. } => Err(CannotSynth),
        // To synth App as W, try to synth func as T -> W, then check arg : T
        App { func, arg } => match type_synth(ctx, func)? {
            Arrow { domain, range } => {
                type_check(ctx, arg, domain)?;
                Ok(range)
            }
            _ => Err(CannotSynth),
        },
        // To synth Ann as the annotated T, just check expr : T
        Ann { expr, ty } => type_check(ctx, expr, ty)
            .map(|()| &**ty) // This is a re-borrow to unbox the Box<Ty>
            .map_err(|_| CannotSynth),
        // The only way to synth an ExpVar is if the context has a binding for the ident
        ExpVar { ident } => ctx.lookup(ident).ok_or(NotInContext(ident)),
    }
}

// Tests

#[cfg(test)]
mod tests {
    use super::*;
    use Expr::*;
    use Ty::*;
    use TypeError::*;

    #[test]
    fn simple_checks() {
        // Check ExpVar that is already in context...
        let expr = ExpVar { ident: "x" };
        let ty = TyVar { ident: "T" };
        let mut ctx: Context = vec![("x", &ty)].into();
        let check_res = type_check(&mut ctx, &expr, &ty);
        assert_eq!(check_res, Ok(()));

        // ...and without context
        let mut ctx: Context = vec![].into();
        let check_res = type_check(&mut ctx, &expr, &ty);
        // The check tries a synth and propagates the synth error
        assert_eq!(check_res, Err(NotInContext("x")));

        // Check identity lambda as T -> T (with empty context)
        let expr = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "x" }).into(),
        };
        let ty = Arrow {
            // These two idents can be whatever as long as they're equal
            domain: (TyVar { ident: "T" }).into(),
            range: (TyVar { ident: "T" }).into(),
        };
        let mut ctx: Context = vec![].into();
        let check_res = type_check(&mut ctx, &expr, &ty);
        assert_eq!(check_res, Ok(()));

        // Check constant lambda as T -> W with (c : W) in context...
        let expr = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "c" }).into(),
        };
        let lambda_ty = Arrow {
            domain: (TyVar { ident: "T" }).into(),
            range: (TyVar { ident: "W" }).into(),
        };
        let c_ty = TyVar { ident: "W" };
        let mut ctx: Context = vec![("c", &c_ty)].into();
        let check_res = type_check(&mut ctx, &expr, &lambda_ty);
        assert_eq!(check_res, Ok(()));

        // ... and without (c : W) in context
        let mut ctx: Context = vec![].into();
        let check_res = type_check(&mut ctx, &expr, &lambda_ty);
        // This will check (c : W), use Turn, fail to synth, and forward the synth error
        assert_eq!(check_res, Err(NotInContext("c")));

        // Check application (f a : T) with both f, a in context...
        let expr = App {
            func: (ExpVar { ident: "f" }).into(),
            arg: (ExpVar { ident: "a" }).into(),
        };
        let app_ty = TyVar { ident: "W" };
        let f_ty = Arrow {
            domain: (TyVar { ident: "T" }).into(),
            range: (TyVar { ident: "W" }).into(),
        };
        let a_ty = TyVar { ident: "T" };
        let mut ctx: Context = vec![("f", &f_ty), ("a", &a_ty)].into();
        let check_res = type_check(&mut ctx, &expr, &app_ty);
        assert_eq!(check_res, Ok(()));

        // ...and with neither in context
        let mut ctx: Context = vec![].into();
        let check_res = type_check(&mut ctx, &expr, &app_ty);
        // The synth error is from turning on either (f : T -> W) or (a : T)
        assert_eq!(check_res, Err(NotInContext("f")));

        // Check application of un-annotated identity lambda to identity lambda...
        let id1 = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "x" }).into(),
        };
        let id2 = Lambda {
            var_ident: "y",
            body: (ExpVar { ident: "y" }).into(),
        };
        let expr = App {
            func: id1.into(),
            arg: id2.into(),
        };
        // Checking for T -> T
        let ty = Arrow {
            domain: (TyVar { ident: "T" }).into(),
            range: (TyVar { ident: "T" }).into(),
        };
        let mut ctx: Context = vec![].into(); // Empty context
        let check_res = type_check(&mut ctx, &expr, &ty);
        // [Should fail with CannotSynth; it will try to synth id1, but we can't synth lambdas]
        assert_eq!(check_res, Err(CannotSynth));

        // ...and check the same application but with the left identity annotated correctly
        let id1 = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "x" }).into(),
        };
        let id2 = Lambda {
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
        let ann_expr = App {
            func: (Ann {
                expr: id1.into(),
                ty: id1_ty.into(),
            })
            .into(),
            arg: id2.into(),
        };
        // ...so that after application, we can infer T -> T
        let ty = Arrow {
            domain: (TyVar { ident: "T" }).into(),
            range: (TyVar { ident: "T" }).into(),
        };
        let mut ctx: Context = vec![].into();
        let check_res = type_check(&mut ctx, &ann_expr, &ty);
        assert_eq!(check_res, Ok(()))
    }

    #[test]
    fn simple_synths() {
        // Synth for ExpVar that is already in context
        let expr = ExpVar { ident: "x" };
        let ty = TyVar { ident: "T" };
        let mut ctx: Context = vec![("x", &ty)].into();
        let synth_res = type_synth(&mut ctx, &expr);
        assert_eq!(synth_res, Ok(&ty));

        // Synth for ExpVar not in context
        let expr = ExpVar { ident: "x" };
        let mut ctx: Context = vec![].into();
        let synth_res = type_synth(&mut ctx, &expr);
        assert_eq!(synth_res, Err(NotInContext("x")));

        // TODO: add more synth tests
    }
}