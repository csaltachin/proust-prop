use std::{
    fmt::{Debug, Display},
    marker::PhantomData,
    rc::Rc,
};

use crate::check::Context;

// A trait for representing variable identifiers. This is so we can choose whether our expression
// and type trees (and contexts) hold variable names as owned Strings, or as owned ints, or as str
// borrows with the lifetime of the source being parsed.
//
// This is useful because, if we don't dispose the source string, then there's no need to
// separately own each of the short slices for each identifier that we keep in the AST. But if
// we're operating the assistant REPL, then we constantly parse and use expressions out of user
// input, and we don't want to store all of those input strings for the entire session. So we might
// decide to simply own the identifiers on those ASTs.

pub trait IdentKind<'so>: Debug + Clone + Display + Eq {
    fn parse_ident(ident: &'so str) -> Self;
}

impl IdentKind<'_> for String {
    fn parse_ident(ident: &str) -> Self {
        ident.to_string()
    }
}

impl IdentKind<'_> for Rc<String> {
    fn parse_ident(ident: &str) -> Self {
        Rc::new(ident.to_string())
    }
}

impl<'so> IdentKind<'so> for &'so str {
    fn parse_ident(ident: &'so str) -> Self {
        ident
    }
}

// AST nodes for types: either a type variable, or an arrow type

#[derive(Debug, PartialEq, Eq)]
pub enum Ty<'so, S>
where
    S: IdentKind<'so>,
{
    TyVar {
        ident: S,
        phantom: PhantomData<&'so ()>,
    },
    Arrow {
        domain: Rc<Ty<'so, S>>,
        range: Rc<Ty<'so, S>>,
    },
    Con {
        left: Rc<Ty<'so, S>>,
        right: Rc<Ty<'so, S>>,
    },
}

impl<'so, S> Display for Ty<'so, S>
where
    S: IdentKind<'so>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TyVar { ident, .. } => write!(f, "{ident}"),
            Self::Arrow { domain, range } => {
                write!(f, "({domain} -> {range})")
            }
            Self::Con { left, right } => {
                write!(f, "({left} & {right})")
            }
        }
    }
}

// A trait for attaching data to holes and injecting side-effects when type-checking them. This is
// mainly so that we can inject effects when refining expressions in the assistant REPL. The unit
// impl is the trivial hole: no data or effects.

pub trait HoleKind<'so, S>: Debug + Eq
where
    S: IdentKind<'so>,
{
    fn check(&self, ty: Rc<Ty<'so, S>>, ctx: &Context<'so, S>);
}

impl<'so, S> HoleKind<'so, S> for ()
where
    S: IdentKind<'so>,
{
    fn check(&self, _: Rc<Ty<'so, S>>, _: &Context<'so, S>) {}
}

// AST nodes for expressions, parametrized over the ident and hole types

#[derive(Debug, PartialEq, Eq)]
pub enum Expr<'so, S, H>
where
    S: IdentKind<'so>,
    H: HoleKind<'so, S>,
{
    ExpVar {
        ident: S,
    },
    Lambda {
        var_ident: S,
        body: Box<Expr<'so, S, H>>,
    },
    App {
        func: Box<Expr<'so, S, H>>,
        arg: Box<Expr<'so, S, H>>,
    },
    Ann {
        expr: Box<Expr<'so, S, H>>,
        ty: Rc<Ty<'so, S>>,
    },
    ExpHole(H),
    Pair {
        left: Box<Expr<'so, S, H>>,
        right: Box<Expr<'so, S, H>>,
    },
    First {
        pair: Box<Expr<'so, S, H>>,
    },
    Second {
        pair: Box<Expr<'so, S, H>>,
    },
}

// We implement this directly for H = () expressions, because we don't want to rely on a Display
// impl for ()

impl<'so, S> Display for Expr<'so, S, ()>
where
    S: IdentKind<'so>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExpVar { ident } => write!(f, "{ident}"),
            Self::Lambda { var_ident, body } => {
                write!(f, "(Lam {var_ident} => {body})")
            }
            Self::App { func, arg } => write!(f, "({func} {arg})"),
            Self::Ann { expr, ty } => write!(f, "({expr} : {ty})"),
            Self::ExpHole(..) => write!(f, "_"),
            Self::Pair { left, right } => write!(f, "(Cons {left} {right})"),
            Self::First { pair } => write!(f, "(First {pair})"),
            Self::Second { pair } => write!(f, "(Second {pair})"),
        }
    }
}

// A handy type alias for expressions with trivial holes

pub type PureExpr<'so, S> = Expr<'so, S, ()>;

// Tests

#[cfg(test)]
mod tests {
    use crate::ast::{Expr::*, Ty::*};
    use std::marker::PhantomData;

    use super::Expr;

    type PureExprWithBorrowedIdents<'so> = Expr<'so, &'so str, ()>;

    #[test]
    fn print_simple_exps() {
        let expected = "x";
        let ast: PureExprWithBorrowedIdents = ExpVar { ident: "x" };
        assert_eq!(expected, ast.to_string());

        let expected = "(Lam x => x)";
        let ast: PureExprWithBorrowedIdents = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "x" }).into(),
        };
        assert_eq!(expected, ast.to_string());

        let expected = "(f a)";
        let ast: PureExprWithBorrowedIdents = App {
            func: (ExpVar { ident: "f" }).into(),
            arg: (ExpVar { ident: "a" }).into(),
        };
        assert_eq!(expected, ast.to_string());

        let expected = "(x : T)";
        let ast: PureExprWithBorrowedIdents = Ann {
            expr: (ExpVar { ident: "x" }).into(),
            ty: (TyVar {
                ident: "T",
                phantom: PhantomData,
            })
            .into(),
        };
        assert_eq!(expected, ast.to_string());

        let expected = "((Lam x => a) : (T -> W))";
        let lam: PureExprWithBorrowedIdents = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "a" }).into(),
        };
        let annot = Arrow {
            domain: (TyVar {
                ident: "T",
                phantom: PhantomData,
            })
            .into(),
            range: (TyVar {
                ident: "W",
                phantom: PhantomData,
            })
            .into(),
        };
        let ast: PureExprWithBorrowedIdents = Ann {
            expr: lam.into(),
            ty: annot.into(),
        };
        assert_eq!(expected, ast.to_string());
    }
}
