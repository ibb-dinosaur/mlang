//! Various semantic checks for the AST

use crate::{ast::{ExprKind, Function, Program, Statement, Stmt, Ty}, report::CompileError};

pub struct SemanticPreTypingChecker {

}

fn has_return_recursive(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| {
        match &s.s {
            Statement::Return(_) => true,
            Statement::If(_, then_, else_) => 
                has_return_recursive(then_) || has_return_recursive(else_),
            _ => false
        }
    })
}

fn does_every_branch_return(stmts: &[Stmt]) -> bool {
    match stmts.last().map(|s| &s.s) {
        Some(Statement::Return(_)) => true,
        Some(Statement::If(_, then_, else_)) =>
            does_every_branch_return(then_) && does_every_branch_return(else_),
        _ => false
    }
}

impl SemanticPreTypingChecker {
    pub fn check_all(&mut self, p: &mut Program) {
        for f in &mut p.functions {
            self.infer_function_return_type(f);
            self.check_function_returns(f);
            self.check_assignment_lhs(&f.body);
        }
    }

    /// For functions witout an explicit return type:
    /// - if the function has no return statements, infer the return type as void
    /// - otherwise, infer the return type as any
    fn infer_function_return_type(&mut self, f: &mut Function) {
        if f.return_type == Ty::Unk {
            let has_explicit_return = has_return_recursive(&f.body);
            if has_explicit_return {
                f.return_type = Ty::Any;
            } else {
                f.return_type = Ty::Void;
            }
        }
    }

    fn check_function_returns(&mut self, f: &mut Function) {
        if f.return_type != Ty::Void {
            // function must have explicit return
            if does_every_branch_return(&f.body) {
                // ok
            } else {
                panic!("function {} missing return statement", f.name);
            }
        } else if !matches!(f.body.last().map(|s| &s.s), Some(Statement::Return(_))) {
            // if function type is void, insert implicit return at the end
            f.body.push(Stmt::new(Statement::Return(
                ExprKind::Literal(crate::ast::Literal::Void).expr_typed(Ty::Void))));
        }
    }

    fn check_assignment_lhs(&mut self, stmts: &[Stmt]) {
        for s in stmts {
            match &s.s {
                Statement::Assign(lhs, _) => {
                    // valid lhs: variable, field
                    match lhs.kind {
                        ExprKind::Var(_) | ExprKind::Field(_, _) => {},
                        _ => panic!("invalid left-hand side of assignment")
                    }
                },
                Statement::If(_, then_, else_) => {
                    self.check_assignment_lhs(then_);
                    self.check_assignment_lhs(else_);
                },
                _ => {}
            }
        }
    }
}