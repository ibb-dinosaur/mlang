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

pub struct RefCountPass2 {}

// go backwards (from the end) in just one pass (vs RefCountPass)
impl RefCountPass2 {
    pub fn new() -> Self {
        Self {}
    }

    fn visit_expr(&mut self, e: &mut Expr, is_considered_use: bool, used_vars: &mut HashSet<String>) {
        match &mut e.kind {
            ExprKind::Literal(_) => {}
            ExprKind::Var(name) => {
                if is_considered_use {
                    if used_vars.contains(name) {
                        // not a last use, dup
                        make_dup(e);
                    } else {
                        // last use, don't dup
                        used_vars.insert(name.clone());
                    }
                }
            },
            ExprKind::BinOp(_, expr, expr1) => {
                self.visit_expr(expr1, true, used_vars);
                self.visit_expr(expr, true, used_vars);
                if !is_considered_use {
                    make_drop(e);
                }
            },
            ExprKind::TypeCast(_, expr) => {
                self.visit_expr(expr, is_considered_use, used_vars);
            }
            ExprKind::Call(f, args) => {
                for a in args.iter_mut().rev() {
                    self.visit_expr(a, true, used_vars);
                }
                self.visit_expr(f, true, used_vars);
                if !is_considered_use {
                    // if the result is not used, drop it
                    make_drop(e);
                }
            },
            ExprKind::New(_, args) => {
                for a in args.iter_mut().rev() {
                    self.visit_expr(a, true, used_vars);
                }
                if !is_considered_use {
                    make_drop(e);
                }
            },
            ExprKind::Field(obj, _) => {
                // object is not considered used
                self.visit_expr(obj, false, used_vars);
            },
            ExprKind::RcDup(_) | ExprKind::RcDrop(_) => unreachable!(),
        }
    }

    fn visit_stmt(&mut self, s: &mut Statement, used_vars: &mut HashSet<String>, defined_vars: &mut HashMap<String, Ty>) {
        match s {
            Statement::ExprStmt(e) => {
                // this is basically a `discard` statement
                self.visit_expr(e, false, used_vars);
            },
            Statement::Return(e) => {
                // return is a use
                self.visit_expr(e, true, used_vars);
            },
            Statement::Let(name, expr) => {
                self.visit_expr(expr, true, used_vars);
                defined_vars.insert(name.clone(), expr.ty.clone());
            },
            Statement::Assign(lhs, rhs) => {
                self.visit_expr(rhs, true, used_vars);
                self.visit_expr(lhs, false, used_vars);
                // the old value of lhs must be dropped
                make_drop(lhs);
            }
            Statement::If(cond, then_, else_) => {
                self.visit_expr(cond, false, used_vars);
                let used_vars_then = self.visit_block(then_, None);
                let used_vars_else = self.visit_block(else_, None);
                // vars used in both blocks are just used
                for v in used_vars_then.intersection(&used_vars_else) {
                    used_vars.insert(v.clone());
                }
                // vars used in just one block are also considered used, but must be dropped in the other block
                for v in used_vars_then.difference(&used_vars_else) {
                    used_vars.insert(v.clone());
                    // drop in else block
                    let var = ExprKind::Var(v.clone()).expr_typed(defined_vars[v].clone());
                    let drop_ = Statement::ExprStmt(ExprKind::RcDrop(Box::new(var)).expr());
                    else_.push(drop_);
                }
                for v in used_vars_else.difference(&used_vars_then) {
                    used_vars.insert(v.clone());
                    // drop in then block
                    let var = ExprKind::Var(v.clone()).expr_typed(defined_vars[v].clone());
                    let drop_ = Statement::ExprStmt(ExprKind::RcDrop(Box::new(var)).expr());
                    then_.push(drop_);
                }
            },
            Statement::RcDropsReturn { .. } => unreachable!(),
        }
    }

    /// Visit a block (with its own scope)
    /// 
    /// Returns variables defined in an outer scope which are used in this block
    // `extra_defs` are variables which should be treated as defined in this block
    fn visit_block(&mut self, stmts: &mut Vec<Statement>, extra_defs: Option<HashMap<String,Ty>>) -> HashSet<String> {
        let mut defined_vars = extra_defs.unwrap_or_default(); // vars defined in this scope (block)
        let mut used_vars = HashSet::new();
        for s in stmts.iter_mut().rev() {
            self.visit_stmt(s, &mut used_vars, &mut defined_vars);
        }
        // variables which are defined but not used must be dropped
        let drops: Vec<_> = defined_vars.iter()
            .filter(|v| !used_vars.contains(v.0))
            .filter(|v| v.1.is_managed())
            .map(|v| {
                ExprKind::Var(v.0.clone()).expr_typed(v.1.clone())
            }).collect();
        if let Some(Statement::Return(ret_val)) = stmts.last_mut() {
            let ret_val = std::mem::take(ret_val);
            *stmts.last_mut().unwrap() = Statement::RcDropsReturn { drops, returns: Some(Box::new(ret_val)) };
        } else {
            // no return
            stmts.push(Statement::RcDropsReturn { drops, returns: None });
        }
        // variables which are used but not defined must be from an outer scope
        for v in defined_vars {
            used_vars.remove(&v.0);
        }
        used_vars
    }

    fn visit_func(&mut self, f: &mut Function) {
        self.visit_block(&mut f.body, Some(f.params.iter().cloned().collect()));
    }

    pub fn run(&mut self, p: &mut Program) {
        for f in &mut p.functions {
            self.visit_func(f);
        }
    }
}

// If a block returns early, it must execute all drops
// from its own scope *and* all blocks above
pub struct DropPropagationPass {
    parent_drops: HashMap<String, Ty>
}

impl DropPropagationPass {
    pub fn run(p: &mut Program) {
        let mut this = Self { parent_drops: HashMap::new() };
        for f in &mut p.functions {
            this.visit_block(&mut f.body);
            debug_assert!(this.parent_drops.is_empty());
        }
    }

    fn visit_block(&mut self, stmts: &mut [Statement]) {
        let parent_drops_save = self.parent_drops.clone();
        if let Statement::RcDropsReturn { drops, .. }  = stmts.last_mut().unwrap() {
            // drop parent blocks' drops
            for (name, ty) in &self.parent_drops {
                drops.push(ExprKind::Var(name.clone()).expr_typed(ty.clone()));
            }
            // drop our own drops in children blocks
            for d in drops.iter() {
                if let ExprKind::Var(name) = &d.kind {
                    if self.parent_drops.contains_key(name) { continue } 
                    self.parent_drops.insert(name.clone(), d.ty.clone());
                }
            }
        } else { unreachable!() }
        // visit children blocks
        for s in stmts.iter_mut() {
            #[allow(clippy::single_match)]
            match s {
                Statement::If(_, then_, else_) => {
                    self.visit_block(then_);
                    self.visit_block(else_);
                },
                _ => {}
            }
        }
        self.parent_drops = parent_drops_save;
    }
}