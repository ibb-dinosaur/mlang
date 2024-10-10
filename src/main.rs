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
mod tyunify;
mod semantic;
mod compile;
mod rt;
mod llvm_extras;
mod util;
mod refcountpass;
//mod gccjit;
//mod mir;

fn main() {
    let code = std::fs::read_to_string("test.lang").unwrap();

    let l = lexer::Lexer::new(&code);
    let p = grammar::ProgParser::new();
    let mut f: ast::Program = p.parse(l).unwrap();

    println!("{}", f);

    let tl = typeck::TypeLookup::new();
    tl.lookup_all(&mut f);

    let mut sc = semantic::SemanticPreTypingChecker {};
    sc.check_all(&mut f);

    let mut tc = typeck::TypeChecker::new();
    tc.check(&mut f);

    println!("{}", f);
    //println!("{:?}", tc);

    let mut rcp = refcountpass::RefCountPass::new();
    rcp.run(&mut f);
    println!("{}", f);

    let llvm_ctx = inkwell::context::Context::create();
    let mut c = Compiler::new(&llvm_ctx);
    c.emit_program(&f);
}
