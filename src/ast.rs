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
}

impl<'so, S> Display for Ty<'so, S>
where
    S: IdentKind<'so>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TyVar { ident, .. } => write!(f, "{ident}"),
            Self::Arrow { domain, range } => {
                write!(f, "({} -> {})", domain.to_string(), range.to_string())
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
}

impl<'so, S> Display for Expr<'so, S, ()>
where
    S: IdentKind<'so>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExpVar { ident } => write!(f, "{ident}"),
            Self::Lambda { var_ident, body } => {
                write!(f, "(Lam {var_ident} => {})", body.to_string())
            }
            Self::App { func, arg } => write!(f, "({} {})", func.to_string(), arg.to_string()),
            Self::Ann { expr, ty } => write!(f, "({} : {})", expr.to_string(), ty.to_string()),
            Self::ExpHole(..) => write!(f, "_"),
        }
    }
}

// Some handy type aliases for expressions with trivial holes, and in particular with borrowed
// idents

pub type PureExpr<'so, S> = Expr<'so, S, ()>;
pub type PureExprWithBorrowedIdents<'so> = Expr<'so, &'so str, ()>;
pub type PureExprWithOwnedIdents = Expr<'static, String, ()>;

// Now, parser stuff.

enum ParseError {
    ExpectedChar(char),
    ExpectedIdent,
    ExpectedToken(&'static str),
    ExpectedEof,
    ExpectedHole,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExpectedIdent => write!(f, "Expected identifier"),
            Self::ExpectedChar(c) => write!(f, "Expected character '{c}'"),
            Self::ExpectedToken(tok) => write!(f, "Expected token {tok}"),
            Self::ExpectedEof => write!(f, "Expected end of string"),
            Self::ExpectedHole => write!(f, "Expected hole"),
        }
    }
}

type ParseResult<T> = Result<T, ParseError>;

struct Parser<'so> {
    source: &'so str,
    cursor: usize,
}

impl<'so> From<&'so str> for Parser<'so> {
    fn from(source: &'so str) -> Self {
        Self { source, cursor: 0 }
    }
}

impl<'so> Parser<'so> {
    fn at_end(&self) -> bool {
        self.source.len() <= self.cursor
    }

    fn peek_char(&self) -> Option<char> {
        self.source[self.cursor..].chars().next()
    }

    fn eat_whitespace(&mut self) {
        while let Some(ch_len) = self
            .peek_char()
            .filter(|it| it.is_ascii_whitespace())
            .map(|it| it.len_utf8())
        {
            self.cursor += ch_len;
        }
    }

    fn expect_eof(&self) -> ParseResult<()> {
        self.at_end().then_some(()).ok_or(ParseError::ExpectedEof)
    }

    fn expect_advance_char(&mut self, expected: char) -> ParseResult<()> {
        if let Some(ch_len) = self
            .peek_char()
            .filter(|it| *it == expected)
            .map(|it| it.len_utf8())
        {
            self.cursor += ch_len;
            Ok(())
        } else {
            Err(ParseError::ExpectedChar(expected))
        }
    }

    fn try_consume_token(&mut self, tok: &'static str) -> bool {
        let tok_right = self.cursor + tok.len();
        if self.source.is_char_boundary(tok_right)
            && self.source[self.cursor..tok_right] == *tok
            && self.source[tok_right..]
                .chars()
                .next()
                .map_or(true, |it| it.is_ascii_whitespace())
        {
            self.cursor = tok_right;
            true
        } else {
            false
        }
    }

    fn try_parse_hole<S>(&mut self) -> Option<S>
    where
        S: IdentKind<'so>,
    {
        let left = self.cursor;
        self.expect_advance_char('_').ok()?;
        let _ = self.try_parse_ident::<S>().is_some();
        Some(IdentKind::parse_ident(&self.source[left..self.cursor]))
    }

    fn try_parse_ident<S>(&mut self) -> Option<S>
    where
        S: IdentKind<'so>,
    {
        let left = self.cursor;

        while let Some(ch_len) = self
            .peek_char()
            .filter(|it| it.is_ascii_alphabetic())
            .map(|it| it.len_utf8())
        {
            self.cursor += ch_len;
        }

        if self.cursor == left {
            None
        } else {
            Some(IdentKind::parse_ident(&self.source[left..self.cursor]))
        }
    }

    fn parse_sexp<S>(&mut self) -> ParseResult<PureExpr<'so, S>>
    where
        S: IdentKind<'so>,
    {
        use Expr::*;

        match self.peek_char() {
            Some('(') => {
                self.expect_advance_char('(')?;
                self.eat_whitespace();

                let expr_res = if self.try_consume_token("Lam") {
                    // Lambda
                    self.eat_whitespace();
                    let var_ident = self.try_parse_ident().ok_or(ParseError::ExpectedIdent)?;
                    self.eat_whitespace();
                    self.try_consume_token("=>")
                        .then_some(())
                        .ok_or(ParseError::ExpectedToken("=>"))?;
                    self.eat_whitespace();
                    let body = self.parse_sexp()?;
                    Ok(Lambda {
                        var_ident,
                        body: body.into(),
                    })
                } else {
                    // Parse a first expression
                    let first_expr = self.parse_sexp()?;
                    self.eat_whitespace();

                    if self.peek_char().map_or(false, |it| it == ':') {
                        // Type-annotated expression
                        self.expect_advance_char(':')?;
                        self.eat_whitespace();
                        let ty_ann = self.parse_ty()?;
                        Ok(Ann {
                            expr: first_expr.into(),
                            ty: ty_ann.into(),
                        })
                    } else {
                        // Application
                        let second_expr = self.parse_sexp()?;
                        Ok(App {
                            func: first_expr.into(),
                            arg: second_expr.into(),
                        })
                    }
                };

                self.eat_whitespace();
                self.expect_advance_char(')')?;
                expr_res
            }
            Some('_') => self
                .try_parse_hole::<S>()
                .map(|_| ExpHole(()))
                .ok_or(ParseError::ExpectedHole),
            _ => self
                .try_parse_ident()
                .map(|ident| ExpVar { ident })
                .ok_or(ParseError::ExpectedIdent),
        }
    }

    fn parse_ty<S>(&mut self) -> ParseResult<Ty<'so, S>>
    where
        S: IdentKind<'so>,
    {
        use Ty::*;

        if self.peek_char().map_or(false, |it| it == '(') {
            // Arrow
            self.expect_advance_char('(')?;
            self.eat_whitespace();

            let left_ty = self.parse_ty()?;

            self.eat_whitespace();
            self.try_consume_token("->")
                .then_some(())
                .ok_or(ParseError::ExpectedToken("->"))?;
            self.eat_whitespace();

            let right_ty = self.parse_ty()?;

            self.eat_whitespace();
            self.expect_advance_char(')')?;

            Ok(Arrow {
                domain: left_ty.into(),
                range: right_ty.into(),
            })
        } else {
            // Type variable
            self.try_parse_ident()
                .map(|ident| TyVar {
                    ident: IdentKind::parse_ident(ident),
                    phantom: PhantomData,
                })
                .ok_or(ParseError::ExpectedIdent)
        }
    }

    fn parse_pure_expr_with_borrowed_idents(
        &mut self,
    ) -> ParseResult<PureExprWithBorrowedIdents<'so>> {
        self.eat_whitespace();
        let expr = self.parse_sexp()?;
        self.eat_whitespace();
        self.expect_eof()?;
        Ok(expr)
    }

    fn parse_ty_with_borrowed_idents(&mut self) -> ParseResult<Ty<'so, &'so str>> {
        self.eat_whitespace();
        let ty = self.parse_ty()?;
        self.eat_whitespace();
        self.expect_eof()?;
        Ok(ty)
    }
}

impl<'so> TryFrom<&'so str> for PureExprWithBorrowedIdents<'so> {
    type Error = String;

    fn try_from(source: &'so str) -> Result<Self, Self::Error> {
        let mut parser: Parser<'so> = source.into();
        parser
            .parse_pure_expr_with_borrowed_idents()
            .map_err(|e| e.to_string())
    }
}

// Tests

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::{Expr::*, PureExprWithBorrowedIdents, Ty::*};

    #[test]
    fn parse_simple_exps() {
        let source = "x";
        let expected = ExpVar { ident: "x" };
        assert_eq!(Ok(expected), source.try_into());

        let source = "  x ";
        let expected = ExpVar { ident: "x" };
        assert_eq!(Ok(expected), source.try_into());

        let source = "(Lam x => x)";
        let expected = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "x" }).into(),
        };
        assert_eq!(Ok(expected), source.try_into());

        let source = "(f a)";
        let expected = App {
            func: (ExpVar { ident: "f" }).into(),
            arg: (ExpVar { ident: "a" }).into(),
        };
        assert_eq!(Ok(expected), source.try_into());

        let source = "(x: T)";
        let expected = Ann {
            expr: (ExpVar { ident: "x" }).into(),
            ty: (TyVar {
                ident: "T",
                phantom: PhantomData,
            })
            .into(),
        };
        assert_eq!(Ok(expected), source.try_into());

        let source = "((Lam x => a) : (T -> W))";
        let lam = Lambda {
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
        let expected = Ann {
            expr: lam.into(),
            ty: annot.into(),
        };
        assert_eq!(Ok(expected), source.try_into());
    }

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
