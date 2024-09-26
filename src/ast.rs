use std::fmt::Display;

#[derive(Debug, PartialEq, Eq)]
pub enum Expr<'so> {
    ExpVar {
        ident: &'so str,
    },
    Lambda {
        var_ident: &'so str,
        body: Box<Expr<'so>>,
    },
    App {
        func: Box<Expr<'so>>,
        arg: Box<Expr<'so>>,
    },
    Ann {
        expr: Box<Expr<'so>>,
        ty: Box<Ty<'so>>,
    },
}

impl Display for Expr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExpVar { ident } => write!(f, "{ident}"),
            Expr::Lambda { var_ident, body } => {
                write!(f, "(Lam {var_ident} => {})", body.to_string())
            }
            Expr::App { func, arg } => write!(f, "({} {})", func.to_string(), arg.to_string()),
            Expr::Ann { expr, ty } => write!(f, "({} : {})", expr.to_string(), ty.to_string()),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Ty<'so> {
    TyVar {
        ident: &'so str,
    },
    Arrow {
        domain: Box<Ty<'so>>,
        range: Box<Ty<'so>>,
    },
}

impl Display for Ty<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TyVar { ident } => write!(f, "{ident}"),
            Self::Arrow { domain, range } => {
                write!(f, "({} -> {})", domain.to_string(), range.to_string())
            }
        }
    }
}

enum ParseError {
    ExpectedChar(char),
    ExpectedIdent,
    ExpectedToken(&'static str),
    ExpectedEof,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExpectedIdent => write!(f, "Expected identifier"),
            Self::ExpectedChar(c) => write!(f, "Expected character '{c}'"),
            Self::ExpectedToken(tok) => write!(f, "Expected token {tok}"),
            Self::ExpectedEof => write!(f, "Expected end of string"),
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

    fn try_parse_ident(&mut self) -> Option<&'so str> {
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
            Some(&self.source[left..self.cursor])
        }
    }

    fn parse_sexp(&mut self) -> ParseResult<Expr<'so>> {
        use Expr::*;

        if self.peek_char().map_or(false, |it| it == '(') {
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
        } else {
            // Expr variable
            self.try_parse_ident()
                .map(|ident| ExpVar { ident })
                .ok_or(ParseError::ExpectedIdent)
        }
    }

    fn parse_ty(&mut self) -> ParseResult<Ty<'so>> {
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
                .map(|ident| TyVar { ident })
                .ok_or(ParseError::ExpectedIdent)
        }
    }

    fn parse_source(&mut self) -> ParseResult<Expr<'so>> {
        self.eat_whitespace();
        let expr = self.parse_sexp()?;
        self.eat_whitespace();
        self.expect_eof()?;
        Ok(expr)
    }
}

impl<'so> TryFrom<&'so str> for Expr<'so> {
    type Error = String;

    fn try_from(source: &'so str) -> Result<Self, Self::Error> {
        let mut parser: Parser<'so> = source.into();
        parser.parse_source().map_err(|e| e.to_string())
    }
}

// Tests

#[cfg(test)]
mod tests {
    use super::*;
    use Expr::*;
    use Ty::*;

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
            ty: (TyVar { ident: "T" }).into(),
        };
        assert_eq!(Ok(expected), source.try_into());

        let source = "((Lam x => a) : (T -> W))";
        let lam = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "a" }).into(),
        };
        let annot = Arrow {
            domain: (TyVar { ident: "T" }).into(),
            range: (TyVar { ident: "W" }).into(),
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
        let ast = ExpVar { ident: "x" };
        assert_eq!(expected, ast.to_string());

        let expected = "(Lam x => x)";
        let ast = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "x" }).into(),
        };
        assert_eq!(expected, ast.to_string());

        let expected = "(f a)";
        let ast = App {
            func: (ExpVar { ident: "f" }).into(),
            arg: (ExpVar { ident: "a" }).into(),
        };
        assert_eq!(expected, ast.to_string());

        let expected = "(x : T)";
        let ast = Ann {
            expr: (ExpVar { ident: "x" }).into(),
            ty: (TyVar { ident: "T" }).into(),
        };
        assert_eq!(expected, ast.to_string());

        let expected = "((Lam x => a) : (T -> W))";
        let lam = Lambda {
            var_ident: "x",
            body: (ExpVar { ident: "a" }).into(),
        };
        let annot = Arrow {
            domain: (TyVar { ident: "T" }).into(),
            range: (TyVar { ident: "W" }).into(),
        };
        let ast = Ann {
            expr: lam.into(),
            ty: annot.into(),
        };
        assert_eq!(expected, ast.to_string());
    }
}