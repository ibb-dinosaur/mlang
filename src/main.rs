use std::sync::OnceLock;

use clap::Parser;
use compile::Compiler;
//use allocator::Allocator;
use lalrpop_util::lalrpop_mod;
//use parser::LangParser;

mod allocator;
mod ast;
mod lexer;
lalrpop_mod!(grammar);
mod parser;
mod typeck;
mod typeck2;
mod semantic;
mod compile;
mod rt;
mod llvm_extras;
mod util;
mod refcountpass;
mod run;
//mod gccjit;
//mod mir;

#[derive(clap::ValueEnum, Clone, Copy, PartialEq, Eq)]
enum CliCommand {
    #[value(alias("c"))]
    Compile,
    #[value(alias("r"))]
    Run
}

#[derive(clap::Parser, Clone)]
#[command()]
struct CliOptions {
    #[arg(value_enum)]
    cmd: CliCommand,
    file: String,
    #[arg(long, help = "Print the AST", default_value = "false")]
    print_ast: bool,
    #[arg(long, help = "Print typechecking information for specified functions", default_value = "")]
    print_typeck: Vec<String>,
    #[arg(long, help = "Print LLVM IR", default_value = "false")]
    print_llvm: bool,
    #[arg(long, help = "Optimize the LLVM IR", default_value = "false")]
    opt: bool,
    #[arg(long, help = "Run using the LLVM JIT", default_value = "false")]
    jit: bool,
}

pub(crate) static OPTIONS: OnceLock<CliOptions> = OnceLock::new();

fn main() {
    let opts = CliOptions::parse();
    OPTIONS.set(opts.clone()).map_err(|_| ()).unwrap();

    let code = std::fs::read_to_string(&opts.file).unwrap();

    let l = lexer::Lexer::new(&code);
    let p = grammar::ProgParser::new();
    let mut f: ast::Program = p.parse(l).unwrap();

    //println!("{}", f);

    let tl = typeck::TypeLookup::new();
    tl.lookup_all(&mut f);

    let mut sc = semantic::SemanticPreTypingChecker {};
    sc.check_all(&mut f);

    let mut tc = typeck2::TypeChecker::new();
    tc.check(&mut f);

    //println!("{}", f);

    let mut rcp = refcountpass::RefCountPass2::new();
    rcp.run(&mut f);
    //println!("{}", f);

    refcountpass::DropPropagationPass::run(&mut f);
    if opts.print_ast {
        println!("{}", f);
    }

    let llvm_ctx = inkwell::context::Context::create();
    let c = Compiler::new(&llvm_ctx);
    let module = c.emit_program(&f);

    if opts.cmd == CliCommand::Run {
        let r = run::Runner::new(&module, opts.jit);
        //rt::RT_ALLOCATOR.lock().unwrap().dump_debug();
        let x = r.test_fn(&module, "main", None);
        match x {
            Ok(x) => println!("{}", x),
            Err(e) => println!("{}", e)
        }
        //rt::RT_ALLOCATOR.lock().unwrap().dump_debug();
    }
}
