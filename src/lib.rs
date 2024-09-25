pub mod analyzer;
pub mod compiler;
pub mod error;
pub mod parser;
mod tree;

use std::io::Write;

use analyzer::{builder::Analyzer, type_checker::TypeChecker};
use compiler::JIT;
use parser::Parser;

pub type Span = core::ops::Range<usize>;

use error::{Error, ErrorKind};

use crate::analyzer::AnalysisResult;

pub fn compile(file: String, source: &str) -> Result<i64, Vec<Error>> {
    let parsed = Parser::new(source).parse();
    // println!("{:?}\n", parsed.parse);
    let analyzed = Analyzer::new(source, parsed).analyze();
    // println!("{}\n", analyzed.analyzed.tree);
    let AnalysisResult {
        mut errors,
        analyzed,
    } = TypeChecker::new(source, analyzed).analyze();
    println!("{}\n", analyzed.tree);
    if errors.is_empty() {
        let mut jit = JIT::new(source);
        match jit.compile(analyzed) {
            Err(err) => Err(vec![Error::error(
                ErrorKind::CraneliftError(err),
                0..source.len(),
                source,
            )
            .with_path(file)]),
            Ok(code) => Ok({
                let res = code();
                std::io::stdout().flush().unwrap();
                res
            }),
        }
    } else {
        for error in &mut errors {
            error.set_path(file.clone());
        }
        Err(errors)
    }
}
