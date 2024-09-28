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
                (p, Some(s).filter(|ss| !is_only_whitespace(ss)))
            });

        //println!("Read com: [{com}] with arg: [{maybe_arg:?}]");

        match (com, arg) {
            ("quit", None) => Ok(Quit),
            ("quit", Some(_)) => {
                println!("To quit, just press <C-d> or type \"quit\" with no arguments.");
                Ok(Nothing)
            }
            (s, None) if is_only_whitespace(s) => Ok(Nothing),
            (bad_com, _) => Err(format!("Unknown command \"{bad_com}\".")),
        }
    }
}

fn assistant_repl() -> io::Result<()> {
    println!("Proust REPL started.");
    println!(
        "Type \"task <type>\" to set a task, then \"refine <hole> <expr>\" to narrow down goals."
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
                    }
                    Ok(Refine(id, pure_expr)) => match assistant.as_mut() {
                        Some(assistant) => match assistant.refine_goal(id, pure_expr) {
                            Err(AssistantError::BadGoalID(bad_id)) => {
                                println!("Goal {bad_id} not found.");
                            }
                            Err(AssistantError::CannotRefine(ty_err)) => {
                                println!("[Type error at goal {id}] {ty_err}.");
                            }
                            Ok(()) => {
                                println!("Goal {id} successfully refined!")
                            }
                        },
                        None => {
                            println!("No task provided!");
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
