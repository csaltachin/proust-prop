use std::io::{self, stdin, stdout, Write};
use std::str::FromStr;

use assistant::{Assistant, AssistantError};
use ast::{PureExpr, Ty};

mod assistant;
mod ast;
mod check;

fn is_only_whitespace(s: &str) -> bool {
    s.split_ascii_whitespace().next().is_none()
}

enum ReplCommand {
    Task(Ty<'static, String>),
    Refine(usize, PureExpr<'static, String>),
    Quit,
    Nothing,
}

impl FromStr for ReplCommand {
    type Err = String;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        use ReplCommand::*;

        let (com, arg) = input
            .trim_end_matches('\n')
            .split_once(' ')
            // If arg is just whitespace, we filter it as None
            .map_or((input, None), |(p, s)| {
                (p, Some(s.trim_ascii()).filter(|ss| !ss.is_empty()))
            });

        //println!("Read com: [{com}] with arg: [{maybe_arg:?}]");

        match (com, arg) {
            // Just parse type and print it back
            ("parse-type", None) => {
                println!("No type specified.");
                Ok(Nothing)
            }
            ("parse-type", Some(ty_str)) => {
                let ty: Ty<&str> = ty_str
                    .try_into()
                    .map_err(|parse_err| format!("[Error while parsing type] {parse_err}."))?;
                println!("Parsed type: [{ty}]");
                Ok(Nothing)
            }
            // Just parse expr and print it back
            ("parse-expr", None) => {
                println!("No expression specified.");
                Ok(Nothing)
            }
            ("parse-expr", Some(ty_str)) => {
                let expr: PureExpr<&str> = ty_str
                    .try_into()
                    .map_err(|parse_err| format!("[Error while parsing type] {parse_err}."))?;
                println!("Parsed expression: [{expr}]");
                Ok(Nothing)
            }
            // Set task
            ("task", None) => {
                println!("No task specified; use \"task <type>\" to set a task.");
                Ok(Nothing)
            }
            ("task", Some(ty_str)) => {
                let ty = ty_str
                    .parse()
                    .map_err(|parse_err| format!("[Error while parsing type] {parse_err}."))?;
                Ok(Task(ty))
            }
            // Refine
            ("refine", None) => {
                println!("No goal or expression specified; use \"refine <goal> <expr>\".");
                Ok(Nothing)
            }
            ("refine", Some(id_and_expr)) => {
                let (id_str, expr_str) = match id_and_expr.split_once(' ') {
                    // Two args
                    Some((p, s)) if !s.is_empty() => (p, s),
                    // One or zero args
                    _ => {
                        println!("\"refine\" takes two arguments: a goal number <goal> and an expression <expr>.");
                        return Ok(Nothing);
                    }
                };

                let id: usize = id_str
                    .parse()
                    .map_err(|e| format!("[Error while parsing goal number] {e}."))?;

                let expr = expr_str.parse().map_err(|parse_err| {
                    format!("[Error while parsing expression] {parse_err}.")
                })?;

                Ok(Refine(id, expr))
            }
            // Quit
            ("quit", None) => Ok(Quit),
            ("quit", Some(_)) => {
                println!("To quit, just press <C-d> or type \"quit\" with no arguments.");
                Ok(Nothing)
            }
            // Empty line
            (s, None) if is_only_whitespace(s) => Ok(Nothing),
            // Unknown command
            (bad_com, _) => Err(format!("Unknown command \"{bad_com}\".")),
        }
    }
}

fn assistant_repl() -> io::Result<()> {
    println!(">> Proust REPL started.");
    println!(
        ">> Type \"task <type>\" to set a task, then \"refine <hole> <expr>\" to narrow down goals."
    );
    let mut input_buf = String::new();
    let mut assistant: Option<Assistant<'static, String>> = None;

    loop {
        input_buf.clear();
        print!("$ ");
        stdout().flush()?;

        match stdin().read_line(&mut input_buf) {
            Err(io_e) => {
                return Err(io_e);
            }
            Ok(0) => {
                println!("<C-d>");
                println!("Bye!");
                break;
            }
            Ok(_) => {
                use ReplCommand::*;

                match input_buf.as_str().trim_end_matches('\n').parse() {
                    Ok(Task(ty)) => {
                        assistant = Some(Assistant::make_assistant(ty));
                        assistant
                            .as_ref()
                            .map(|asst| println!("{}", asst.pretty_print_status()));
                    }
                    Ok(Refine(id, pure_expr)) => match assistant.as_mut() {
                        Some(asst) => match asst.refine_goal(id, pure_expr) {
                            Err(AssistantError::BadGoalID(bad_id)) => {
                                println!("Goal {bad_id} not found.");
                            }
                            Err(AssistantError::CannotRefine(ty_err)) => {
                                println!("[Type error at goal {id}] {ty_err}.");
                            }
                            Ok(()) => {
                                println!("Goal {id} successfully refined!");
                                println!("{}", asst.pretty_print_status());
                            }
                        },
                        None => {
                            println!("No task has been set yet; use \"task <type>\".");
                        }
                    },
                    Ok(Nothing) => {
                        continue;
                    }
                    Ok(Quit) => {
                        println!("Bye!");
                        break;
                    }
                    Err(parse_err) => {
                        println!("{parse_err}");
                    }
                };
            }
        }
    }

    Ok(())
}

fn main() {
    assistant_repl().unwrap_or_else(|e| {
        println!("Unexpected IO error: {e:?}");
        ()
    })
}
