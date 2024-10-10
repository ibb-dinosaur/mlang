//! Handles automatic reference counting (inserts refcount operations)
//! 
//! Our refcounting semantics are (simplified) as follows:
//! - All values are treated like "linear types"
//! - Whenever a value is *used* more than once, it must be *dupped*
//! - A *use* is defined as any operation taking a reference to the value
//! - Accessing a field of an object is _not_ a *use* of the object itself
//! - When a reference to an object is lost (e.g. reassigning a variable), it must be *dropped*

use std::collections::{HashMap, HashSet};

use crate::ast::{Expr, ExprKind, Function, Program, Statement, Ty};

pub struct RefCountPass {
    vars_uses: HashMap<String, usize>,
    unused_vars: HashMap<String, Ty>
}

impl RefCountPass {
    pub fn new() -> Self {
        Self {
            vars_uses: HashMap::new(),
            unused_vars: HashMap::new()
        }
    }

    pub fn run(&mut self, p: &mut Program) {
        for f in &mut p.functions {
            self.visit_function(f);
        }
    }

    fn visit_function(&mut self, f: &mut Function) {
        self.vars_uses.clear();
        self.unused_vars.clear();
        for p in &f.params {
            self.unused_vars.insert(p.0.clone(), p.1.clone());
        }

        for s in &f.body {
            self.find_used_variables_stmt(s);
        }
        // now we have a map of variables and their usage count
        // insert refcount operations
        for s in &mut f.body {
            self.insert_refcount_ops_stmt(s);
        }
    }

    fn insert_refcount_ops_stmt(&mut self, s: &mut Statement) {
        match s {
            Statement::ExprStmt(expr) => { // basically a discard statement
                self.insert_refcount_ops_expr(expr, false);
            },
            Statement::Return(val) => {
                self.insert_refcount_ops_expr(val, true);
                // all unused variables must be dropped here
                let drops: Vec<_> = self.unused_vars.iter()
                    .filter(|v| v.1.is_managed())
                    .map(|v| {
                        ExprKind::Var(v.0.clone()).expr_typed(v.1.clone())
                    }).collect();
                let return_val = std::mem::take(val);
                *s = Statement::RcDropsReturn { drops, returns: Some(Box::new(return_val)) };
            },
            Statement::Let(name, val) => {
                self.insert_refcount_ops_expr(val, true);
            },
            Statement::Assign(lhs, rhs) => {
                self.insert_refcount_ops_expr(lhs, false);
                self.insert_refcount_ops_expr(rhs, true);
                // the old value of lhs must be dropped
                make_drop(lhs);
            },
            Statement::If(expr, vec, vec1) => todo!(),
            Statement::RcDropsReturn { .. } => unreachable!(),
        }
    }

    fn insert_refcount_ops_expr(&mut self, e: &mut Expr, is_considered_use: bool) {
        match &mut e.kind {
            ExprKind::Literal(_) => {},
            ExprKind::Var(v) => {
                if !is_considered_use {}
                else if self.vars_uses[v] <= 1 {
                    // this is the last use, don't dup
                } else {
                    // dup
                    *self.vars_uses.get_mut(v).unwrap() -= 1;
                    make_dup(e);
                }
            },
            ExprKind::Call(f, args) => {
                self.insert_refcount_ops_expr(f, true);
                for a in args {
                    self.insert_refcount_ops_expr(a, true);
                }
                if !is_considered_use {
                    // if the result is not used, drop it
                    make_drop(e);
                }
            }
            ExprKind::BinOp(_, expr, expr1) => {
                // we consider binary operations as ordinary functions of two arguments
                self.insert_refcount_ops_expr(expr, true);
                self.insert_refcount_ops_expr(expr1, true);
                if !is_considered_use {
                    make_drop(e);
                }
            },
            ExprKind::TypeCast(_, expr) => {
                self.insert_refcount_ops_expr(expr, is_considered_use);
            },
            ExprKind::New(_, vec) => {
                for e in vec {
                    self.insert_refcount_ops_expr(e, true);
                }
                if !is_considered_use {
                    make_drop(e);
                }
            },
            ExprKind::Field(obj, _) => {
                // object is not considered used
                self.insert_refcount_ops_expr(obj, false);
            },
            ExprKind::RcDup(_) => unreachable!(),
            ExprKind::RcDrop(_) => unreachable!()
        }
    }

    /// `is_expr_used` is false if this expression itself is not considered a "use"
    /// (note that subexpressions such as function arguments may still be considered a used)
    fn find_used_variables_expr(&mut self, e: &Expr, is_considered_use: bool) {
        match &e.kind {
            ExprKind::Literal(_) => {},
            ExprKind::Var(n) => { 
                if is_considered_use { // if this expression is not "used", the variable is not considered used
                    *self.vars_uses.entry(n.clone()).or_insert(0) += 1;
                    // variable is used at least once
                    self.unused_vars.remove(n);
                }
            },
            ExprKind::BinOp(_, expr, expr1) => {
                self.find_used_variables_expr(expr, true);
                self.find_used_variables_expr(expr1, true);
            },
            ExprKind::TypeCast(_, expr) => {
                self.find_used_variables_expr(expr, is_considered_use);
            },
            ExprKind::Call(f, args) => {
                self.find_used_variables_expr(f, true);
                for a in args {
                    self.find_used_variables_expr(a, true);
                }
            },
            ExprKind::New(_, vec) => {
                for e in vec {
                    self.find_used_variables_expr(e, true);
                }
            },
            ExprKind::Field(obj, _) => {
                // object is not considered used
                self.find_used_variables_expr(obj, false);
            },

            ExprKind::RcDup(_) => unreachable!(),
            ExprKind::RcDrop(_) => unreachable!(),
        }
    }

    fn find_used_variables_stmt(&mut self, s: &Statement) {
        match s {
            // this is basically a `discard` statement
            Statement::ExprStmt(expr) =>
                self.find_used_variables_expr(expr, false),
            Statement::Return(val) => // the return value is "used"
                self.find_used_variables_expr(val, true),
            Statement::Let(name, val) => {
                self.find_used_variables_expr(val, true);
                self.unused_vars.insert(name.clone(), val.ty.clone());
            }
            Statement::Assign(lhs, rhs) => {
                self.find_used_variables_expr(lhs, false);
                self.find_used_variables_expr(rhs, true);
            }
            Statement::If(expr, vec, vec1) => todo!(),
            Statement::RcDropsReturn { .. } => unreachable!(),
        }
    }
}

fn make_dup(e: &mut Expr) {
    if !e.ty.is_managed() {
        return; // avoid extraneous refcount operations
    }
    let expr_orig = std::mem::take(e);
    let expr_ty = expr_orig.ty.clone();
    let dup = ExprKind::RcDup(Box::new(expr_orig)).expr_typed(expr_ty);
    *e = dup;
}

fn make_drop(e: &mut Expr) {
    if !e.ty.is_managed() {
        return; // avoid extraneous refcount operations
    }

    let expr_orig = std::mem::take(e);
    let expr_ty = expr_orig.ty.clone();
    let dup = ExprKind::RcDrop(Box::new(expr_orig)).expr_typed(expr_ty);
    *e = dup;
}