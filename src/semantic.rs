//! Various semantic checks for the AST

use crate::ast::{Expr, ExprKind, Function, Program, Statement, Ty};

pub struct SemanticPreTypingChecker {

}

impl SemanticPreTypingChecker {
    pub fn check_all(&mut self, p: &mut Program) {
        for f in &mut p.functions {
            self.infer_function_return_type(f);
            self.check_function_returns(f);
        }
    }

    /// For functions witout an explicit return type:
    /// - if the function has no return statements, infer the return type as void
    /// - otherwise, infer the return type as any
    fn infer_function_return_type(&mut self, f: &mut Function) {
        if f.return_type == Ty::Unk {
            let mut found_explicit_return = false;
            for stmt in &f.body {
                if let Statement::Return(_) = stmt {
                    found_explicit_return = true;
                    break;
                }
            }
            if found_explicit_return {
                f.return_type = Ty::Any;
            } else {
                f.return_type = Ty::Void;
            }
        }
    }

    fn check_function_returns(&mut self, f: &mut Function) {
        if f.return_type != Ty::Void {
            // function must have explicit return
            if let Some(Statement::Return(_)) = f.body.last() {
                // ok
            } else {
                panic!("function {} missing return statement", f.name);
            }
        } else {
            // if function type is void, insert implicit return at the end
            f.body.push(Statement::Return(Expr { 
                ty: Ty::Void,
                kind: ExprKind::Literal(crate::ast::Literal::Void)
             }))
        }
    }
}