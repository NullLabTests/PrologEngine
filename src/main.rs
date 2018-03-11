#[macro_use] extern crate lazy_static;
#[macro_use] extern crate downcast;
extern crate termion;

mod prolog;
#[macro_use] mod test_utils;

use prolog::ast::*;
use prolog::io::*;
use prolog::machine::*;
use prolog::similarity::*;
use std::env;
use std::collections::HashMap;

#[cfg(test)]
mod tests;

pub static LISTS: &str   = include_str!("./prolog/lib/lists.pl");
pub static CONTROL: &str = include_str!("./prolog/lib/control.pl");
pub static QUEUES: &str = include_str!("./prolog/lib/queues.pl");

fn parse_and_compile_line(wam: &mut Machine, buffer: &str, similarity_table: SimilarityTable)
{
    match parse_code(wam, buffer, similarity_table) {
        Ok(packet) => {
            let result = compile_packet(wam, packet);
            print(wam, result);
        },
        Err(s) => println!("{:?}", s)
    }
}

fn load_init_str(wam: &mut Machine, src_str: &str)
{
    match compile_listing(wam, src_str, SimilarityTable::new()) {
        EvalSession::Error(_) => panic!("failed to parse batch from string."),
        _ => {}
    }
}

fn prolog_repl(similarity_tbl: SimilarityTable) {
    let mut wam = Machine::new();

    load_init_str(&mut wam, LISTS);
    load_init_str(&mut wam, CONTROL);
    load_init_str(&mut wam, QUEUES);

    loop {
        print!("prolog> ");

        match read() {
            Input::Line(line) => parse_and_compile_line(&mut wam, line.as_str(), similarity_tbl),
            Input::Batch(batch) =>
                match compile_listing(&mut wam, batch.as_str(), similarity_tbl) {
                    EvalSession::Error(e) => println!("{}", e),
                    _ => {}
                },
            Input::Quit => break,
            Input::Clear => {
                wam.clear();
                continue;
            }
        };

        wam.reset();
    }
}

fn main() {
    let similarity_table = parse_similarity_table(env::args().nth(1).unwrap());
    prolog_repl(similarity_table);
}
