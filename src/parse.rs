use std::{fmt::Display, marker::PhantomData, str::FromStr};

use crate::ast::{Expr, IdentKind, PureExpr, Ty, UnitHole};

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
        if self.source.is_char_boundary(tok_right) && self.source[self.cursor..tok_right] == *tok {
            self.cursor = tok_right;
            true
        } else {
            false
        }
    }

    // Parsing holes and idents parametrized over 'so...

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

    fn try_parse_hole<S>(&mut self) -> Option<S>
    where
        S: IdentKind<'so>,
    {
        let left = self.cursor;
        self.expect_advance_char('_').ok()?;
        let _ = self.try_parse_ident::<S>().is_some();
        Some(IdentKind::parse_ident(&self.source[left..self.cursor]))
    }

    // ...and owned-ident versions

    fn try_parse_owned_ident(&mut self) -> Option<String> {
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
            Some(self.source[left..self.cursor].to_string())
        }
    }

    fn try_parse_owned_hole(&mut self) -> Option<String> {
        let left = self.cursor;
        self.expect_advance_char('_').ok()?;
        let _ = self.try_parse_ident::<&str>().is_some(); // We only care if it's some or none
        Some(IdentKind::parse_ident(
            &self.source[left..self.cursor].to_string(),
        ))
    }

    // Main internal parsers for PureExpr and Ty

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
                } else if self.try_consume_token("Cons") {
                    // Cons (&-intro)
                    self.eat_whitespace();
                    let left = self.parse_sexp()?;
                    self.eat_whitespace();
                    let right = self.parse_sexp()?;
                    self.eat_whitespace();
                    Ok(Pair {
                        left: left.into(),
                        right: right.into(),
                    })
                } else if self.try_consume_token("First") {
                    // First (&-elim0)
                    self.eat_whitespace();
                    let pair = self.parse_sexp()?;
                    self.eat_whitespace();
                    Ok(First { pair: pair.into() })
                } else if self.try_consume_token("Second") {
                    // Second (&-elim1)
                    self.eat_whitespace();
                    let pair = self.parse_sexp()?;
                    self.eat_whitespace();
                    Ok(Second { pair: pair.into() })
                } else if self.try_consume_token("Left") {
                    // Left (|-intro0)
                    self.eat_whitespace();
                    let inner = self.parse_sexp()?;
                    self.eat_whitespace();
                    Ok(Left {
                        inner: inner.into(),
                    })
                } else if self.try_consume_token("Right") {
                    // Right (|-intro1)
                    self.eat_whitespace();
                    let inner = self.parse_sexp()?;
                    self.eat_whitespace();
                    Ok(Right {
                        inner: inner.into(),
                    })
                } else if self.try_consume_token("Match") {
                    // Match (|-elim)
                    self.eat_whitespace();
                    let arg = self.parse_sexp()?;
                    self.eat_whitespace();
                    let f_left = self.parse_sexp()?;
                    self.eat_whitespace();
                    let f_right = self.parse_sexp()?;
                    self.eat_whitespace();
                    Ok(Match {
                        arg: arg.into(),
                        f_left: f_left.into(),
                        f_right: f_right.into(),
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
                .map(|_| ExpHole(UnitHole {}))
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
            // Single or binary op
            self.expect_advance_char('(')?;
            self.eat_whitespace();

            let left_ty = self.parse_ty()?;
            self.eat_whitespace();

            let ty = if self.try_consume_token("->") {
                // Arrow type
                self.eat_whitespace();
                let right_ty = self.parse_ty()?;
                Arrow {
                    domain: left_ty.into(),
                    range: right_ty.into(),
                }
            } else if self.try_consume_token("&") {
                // Conjunction
                self.eat_whitespace();
                let right_ty = self.parse_ty()?;
                Con {
                    left: left_ty.into(),
                    right: right_ty.into(),
                }
            } else if self.try_consume_token("|") {
                // Disjunction
                self.eat_whitespace();
                let right_ty = self.parse_ty()?;
                Con {
                    left: left_ty.into(),
                    right: right_ty.into(),
                }
            } else {
                // Single
                left_ty
            };

            self.eat_whitespace();
            self.expect_advance_char(')')?;

            Ok(ty)
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

    // A couple convenience methods for ident-owned parsing without depending on the source
    // lifetime 'so
    // TODO: can we avoid repeating this code?

    fn parse_sexp_with_owned_idents(&mut self) -> ParseResult<PureExpr<'static, String>> {
        use Expr::*;

        match self.peek_char() {
            Some('(') => {
                self.expect_advance_char('(')?;
                self.eat_whitespace();

                let expr_res = if self.try_consume_token("Lam") {
                    // Lambda
                    self.eat_whitespace();
                    let var_ident = self
                        .try_parse_owned_ident()
                        .ok_or(ParseError::ExpectedIdent)?;
                    self.eat_whitespace();
                    self.try_consume_token("=>")
                        .then_some(())
                        .ok_or(ParseError::ExpectedToken("=>"))?;
                    self.eat_whitespace();
                    let body = self.parse_sexp_with_owned_idents()?;
                    Ok(Lambda {
                        var_ident,
                        body: body.into(),
                    })
                } else if self.try_consume_token("Cons") {
                    // Cons (&-intro)
                    self.eat_whitespace();
                    let left = self.parse_sexp_with_owned_idents()?;
                    self.eat_whitespace();
                    let right = self.parse_sexp_with_owned_idents()?;
                    self.eat_whitespace();
                    Ok(Pair {
                        left: left.into(),
                        right: right.into(),
                    })
                } else if self.try_consume_token("First") {
                    // First (&-elim0)
                    self.eat_whitespace();
                    let pair = self.parse_sexp_with_owned_idents()?;
                    self.eat_whitespace();
                    Ok(First { pair: pair.into() })
                } else if self.try_consume_token("Second") {
                    // Second (&-elim1)
                    self.eat_whitespace();
                    let pair = self.parse_sexp_with_owned_idents()?;
                    self.eat_whitespace();
                    Ok(Second { pair: pair.into() })
                } else if self.try_consume_token("Left") {
                    // Left (|-intro0)
                    self.eat_whitespace();
                    let inner = self.parse_sexp_with_owned_idents()?;
                    self.eat_whitespace();
                    Ok(Left {
                        inner: inner.into(),
                    })
                } else if self.try_consume_token("Right") {
                    // Right (|-intro1)
                    self.eat_whitespace();
                    let inner = self.parse_sexp_with_owned_idents()?;
                    self.eat_whitespace();
                    Ok(Right {
                        inner: inner.into(),
                    })
                } else if self.try_consume_token("Match") {
                    // Match (|-elim)
                    self.eat_whitespace();
                    let arg = self.parse_sexp_with_owned_idents()?;
                    self.eat_whitespace();
                    let f_left = self.parse_sexp_with_owned_idents()?;
                    self.eat_whitespace();
                    let f_right = self.parse_sexp_with_owned_idents()?;
                    self.eat_whitespace();
                    Ok(Match {
                        arg: arg.into(),
                        f_left: f_left.into(),
                        f_right: f_right.into(),
                    })
                } else {
                    // Parse a first expression
                    let first_expr = self.parse_sexp_with_owned_idents()?;
                    self.eat_whitespace();

                    if self.peek_char().map_or(false, |it| it == ':') {
                        // Type-annotated expression
                        self.expect_advance_char(':')?;
                        self.eat_whitespace();
                        let ty_ann = self.parse_ty_with_owned_idents()?;
                        Ok(Ann {
                            expr: first_expr.into(),
                            ty: ty_ann.into(),
                        })
                    } else {
                        // Application
                        let second_expr = self.parse_sexp_with_owned_idents()?;
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
                .try_parse_owned_hole()
                .map(|_| ExpHole(UnitHole {}))
                .ok_or(ParseError::ExpectedHole),
            _ => self
                .try_parse_owned_ident()
                .map(|ident| ExpVar { ident })
                .ok_or(ParseError::ExpectedIdent),
        }
    }

    fn parse_ty_with_owned_idents(&mut self) -> ParseResult<Ty<'static, String>> {
        use Ty::*;

        if self.peek_char().map_or(false, |it| it == '(') {
            // Single or binary op
            self.expect_advance_char('(')?;
            self.eat_whitespace();

            let left_ty = self.parse_ty_with_owned_idents()?;
            self.eat_whitespace();

            let ty = if self.try_consume_token("->") {
                // Arrow type
                self.eat_whitespace();
                let right_ty = self.parse_ty_with_owned_idents()?;
                Arrow {
                    domain: left_ty.into(),
                    range: right_ty.into(),
                }
            } else if self.try_consume_token("&") {
                // Conjunction
                self.eat_whitespace();
                let right_ty = self.parse_ty_with_owned_idents()?;
                Con {
                    left: left_ty.into(),
                    right: right_ty.into(),
                }
            } else if self.try_consume_token("|") {
                // Disjunction
                self.eat_whitespace();
                let right_ty = self.parse_ty_with_owned_idents()?;
                Dis {
                    left: left_ty.into(),
                    right: right_ty.into(),
                }
            } else {
                // Single
                left_ty
            };

            self.eat_whitespace();
            self.expect_advance_char(')')?;

            Ok(ty)
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

    // Wrappers for parsing PureExpr and Ty, parametrized over 'so...

    fn parse_entire_pure_expr<S>(&mut self) -> ParseResult<PureExpr<'so, S>>
    where
        S: IdentKind<'so>,
    {
        self.eat_whitespace();
        let expr = self.parse_sexp()?;
        self.eat_whitespace();
        self.expect_eof()?;
        Ok(expr)
    }

    fn parse_entire_ty<S>(&mut self) -> ParseResult<Ty<'so, S>>
    where
        S: IdentKind<'so>,
    {
        self.eat_whitespace();
        let ty = self.parse_ty()?;
        self.eat_whitespace();
        self.expect_eof()?;
        Ok(ty)
    }

    // and for ('static, String) PureExpr and Ty

    fn parse_entire_pure_expr_with_owned_idents(
        &mut self,
    ) -> ParseResult<PureExpr<'static, String>> {
        self.eat_whitespace();
        let expr = self.parse_sexp_with_owned_idents()?;
        self.eat_whitespace();
        self.expect_eof()?;
        Ok(expr)
    }

    fn parse_entire_ty_with_owned_idents(&mut self) -> ParseResult<Ty<'static, String>> {
        self.eat_whitespace();
        let ty = self.parse_ty_with_owned_idents()?;
        self.eat_whitespace();
        self.expect_eof()?;
        Ok(ty)
    }
}

// PureExpr and Ty parsing, parametrized over the 'so lifetime...

impl<'so, S> TryFrom<&'so str> for PureExpr<'so, S>
where
    S: IdentKind<'so>,
{
    type Error = String;

    fn try_from(source: &'so str) -> Result<Self, Self::Error> {
        let mut parser: Parser<'so> = source.into();
        parser.parse_entire_pure_expr().map_err(|e| e.to_string())
    }
}

impl<'so, S> TryFrom<&'so str> for Ty<'so, S>
where
    S: IdentKind<'so>,
{
    type Error = String;

    fn try_from(source: &'so str) -> Result<Self, Self::Error> {
        let mut parser: Parser<'so> = source.into();
        parser.parse_entire_ty().map_err(|e| e.to_string())
    }
}

// ...and for ('static, String) PureExpr and Ty

impl FromStr for Ty<'static, String> {
    type Err = String;

    fn from_str(source: &str) -> Result<Self, Self::Err> {
        let mut parser: Parser = source.into();
        parser
            .parse_entire_ty_with_owned_idents()
            .map_err(|e| e.to_string())
    }
}

impl FromStr for PureExpr<'static, String> {
    type Err = String;

    fn from_str(source: &str) -> Result<Self, Self::Err> {
        let mut parser: Parser = source.into();
        parser
            .parse_entire_pure_expr_with_owned_idents()
            .map_err(|e| e.to_string())
    }
}

// Tests

#[cfg(test)]
mod tests {
    use crate::ast::{
        Expr::*,
        IdentKind,
        Ty::{self, *},
    };
    use std::marker::PhantomData;

    fn ty_var<'so, S>(ident: S) -> Ty<'so, S>
    where
        S: IdentKind<'so>,
    {
        TyVar {
            ident,
            phantom: PhantomData,
        }
    }

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

        let source = "  (    Lam    x    =>x  )  ";
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
            ty: (ty_var("T")).into(),
        };
        assert_eq!(Ok(expected), source.try_into());

        let source = "((Lam x => a) : (T -> W))";
        let lam = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "a" }).into(),
        };
        let annot = Arrow {
            domain: (ty_var("T")).into(),
            range: (ty_var("W")).into(),
        };
        let expected = Ann {
            expr: lam.into(),
            ty: annot.into(),
        };
        assert_eq!(Ok(expected), source.try_into());
    }

    #[test]
    fn parse_simple_types() {
        let source = "T";
        let expected = ty_var("T");
        assert_eq!(Ok(expected), source.try_into());

        let source = "     T     ";
        let expected = ty_var("T");
        assert_eq!(Ok(expected), source.try_into());

        let source = "(T -> W)";
        let expected = Arrow {
            domain: ty_var("T").into(),
            range: ty_var("W").into(),
        };
        assert_eq!(Ok(expected), source.try_into());

        let source = "(T->W)";
        let expected = Arrow {
            domain: ty_var("T").into(),
            range: ty_var("W").into(),
        };
        assert_eq!(Ok(expected), source.try_into());

        let source = "   (   T   ->     W    )      ";
        let expected = Arrow {
            domain: ty_var("T").into(),
            range: ty_var("W").into(),
        };
        assert_eq!(Ok(expected), source.try_into());
    }
}
