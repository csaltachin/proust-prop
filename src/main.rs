use std::io::{self, stdin, stdout, Write};
use std::str::FromStr;

use assistant::{Assistant, AssistantError};
use ast::{PureExpr, Ty};

mod assistant;
mod ast;
mod check;

enum ReplCommand {
    Task(Ty<'static, String>),
    Refine(usize, PureExpr<'static, String>),
    Quit,
}

impl FromStr for ReplCommand {
    type Err = String;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        match input
            .trim_end_matches('\n')
            .split_once(' ')
            .map_or((input, None), |(p, s)| {
                (p, Some(s).filter(|ss| ss.is_empty()))
            }) {
            // TODO: parse commands properly
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
                break;
            }
            Ok(_) => {
                match input_buf.as_str().parse() {
                    Ok(ReplCommand::Task(ty)) => {
                        assistant = Some(Assistant::make_assistant(ty));
                    }
                    Ok(ReplCommand::Refine(id, pure_expr)) => match assistant.as_mut() {
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
                    Ok(ReplCommand::Quit) => {
                        break;
                    }
                    Err(err_s) => {
                        println!("{err_s}");
                    }
                };
            }
        }
    }

    println!("Bye!");
    Ok(())
}

fn main() {
    assistant_repl().unwrap_or_else(|e| {
        println!("Unexpected IO error: {e:?}");
        ()
    })
}
