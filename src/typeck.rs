/*
Type-checking takes several stages:
1. Collecting type-variables into an inference context
2. "Unifying" type-variables to the most general type
3. Assigning types to expressions and inserting type casts where needed
*/

use std::collections::HashMap;

use crate::{ast::*, util::ScopedMap};

#[derive(Debug)]
struct InferenceContext {
    pairs: Vec<Option<Box<InferencePair>>>,
    results: Vec<Option<Ty>>,
}

impl InferenceContext {
    pub fn new() -> Self {
        Self { pairs: vec![], results: vec![] }
    }

    pub fn new_var(&mut self) -> Ty {
        let ty = Ty::TyVar(self.results.len());
        self.results.push(None);
        ty
    }

    pub fn add_pair(&mut self, src_ty: Ty, dst_ty: Ty) {
        self.pairs.push(Some(Box::new(InferencePair { src_ty, dst_ty })));
    }

    fn set_var(&mut self, i: usize, ty: Ty) {
        println!("Setting tv${} to {}", i, ty);
        self.results[i] = Some(ty);
    }

    // returns true if the unification was productive
    fn unify_pair(&mut self, p: InferencePair) -> bool {
        println!("Unifying {} =>(assign) {}", p.src_ty, p.dst_ty);
        if p.src_ty.is_nominal() && p.dst_ty.is_nominal() {
            return true; // nothing to do here
        }
        // check if the types are aggregates
        #[allow(clippy::single_match)]
        match (&p.src_ty, &p.dst_ty) {
            (Ty::Func(src_ret, src_params), Ty::Func(dst_ret, dst_params)) => {
                // src_params -> dst_params
                for (src, dst) in src_params.iter().zip(dst_params) {
                    self.add_pair(src.clone(), dst.clone());
                }
                // dst_ret -> src_ret (!)
                self.add_pair(*dst_ret.clone(), *src_ret.clone());
                return true;
            },
            _ => {}
        }
        if p.dst_ty == Ty::Any {
            // any type is assignable to Any, provides no information
            return true;
        }
        // check if the types are type variables
        if let Ty::TyVar(i) = p.src_ty {
            if !p.dst_ty.is_var() {
                if let Some(prev_ty) = self.results[i].clone() {
                    self.set_var(i, self.most_general_type(prev_ty, p.dst_ty));
                    return true;
                } else {
                    self.set_var(i, p.dst_ty);
                    return true;
                }
            }
        }
        if let Ty::TyVar(i) = p.dst_ty {
            if let Ty::TyVar(j) = p.src_ty {
                if let (Some(a), Some(b)) = (self.results[i].clone(), self.results[j].clone()) {
                    let mgt = self.most_general_type(a, b);
                    self.set_var(i, mgt.clone());
                    self.set_var(j, mgt);
                    return true;
                } else { return false; }
            } else if let Some(prev_ty) = self.results[i].clone() {
                self.set_var(i, self.most_general_type(prev_ty, p.src_ty));
                return true;
            } else {
                self.set_var(i, p.src_ty);
                return true;
            }
        }
        unreachable!()
    }

    fn most_general_type(&self, a: Ty, b: Ty) -> Ty {
        assert!(!a.is_var() && !b.is_var());
        if a == b {
            a
        } else {
            Ty::Any
        }
    }

    pub fn unify_all(&mut self) {
        // pairs must be modifiable while being iterated over
        let mut i = 0;
        let mut iter_limit = 100;
        while i < self.pairs.len() && iter_limit > 0 {
            if let Some(p) = self.pairs[i].take() {
                let resolved = self.unify_pair((*p).clone());
                if !resolved {
                    self.pairs[i] = Some(p);
                }
            }
            i += 1;
            iter_limit -= 1;
        }
        // if any type variables were left unresolved, assign them to Any
        for ty in &mut self.results {
            if ty.is_none() {
                *ty = Some(Ty::Any);
            }
        }
    }
}

#[derive(Debug, Clone)]
struct InferencePair { src_ty: Ty, dst_ty: Ty }

pub struct TypeChecker {
    globals: HashMap<String, Ty>,
    // local to a function
    ctx: InferenceContext,
    vars: ScopedMap<String, Ty>,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self { globals: HashMap::new(), ctx: InferenceContext::new(), vars: ScopedMap::new() }
    }

    fn get_symbol_type(&self, name: &str) -> Ty {
        match self.vars.get(name) {
            Some(lty) => lty.clone(),
            None => match self.globals.get(name) {
                Some(gty) => gty.clone(),
                None => panic!("Unknown symbol: {}", name)
            }   
        }
    }

    pub fn check(&mut self, prog: &mut Program) {
        // collect globals
        for func in &prog.functions {
            self.globals.insert(func.name.clone(), func.create_ftype());
        }
        for func in &mut prog.functions {
            self.check_func(func);
        }
    }

    fn check_func(&mut self, func: &mut Function) {
        self.vars.reset();
        self.ctx = InferenceContext::new();
        for (name, ty) in &func.params {
            self.vars.insert_new(name.clone(), ty.clone());
        }
        self.vars.insert_new("$return".to_string(), func.return_type.clone());
        // 1. collect type variables
        self.vars.enter_new_scope();
        for stmt in &mut func.body {
            self.check_stmt(stmt);
        }
        self.vars.exit_scope();
        // 2. unify type variables
        self.ctx.unify_all();
        // 3. assign types to expressions, insert casts
        self.vars.enter_new_scope();
        for stmt in &mut func.body {
            self.resolve_stmt(stmt);
        }
        self.vars.exit_scope();
        // done! (hopefully)
    }

    fn check_stmt(&mut self, stmt: &mut Statement) {
        match stmt {
            Statement::ExprStmt(expr) => {
                self.check_expr(expr);
            }
            Statement::Return(expr) => {
                self.check_expr(expr);
                self.ctx.add_pair(expr.ty.clone(), self.vars["$return"].clone());
            }
            Statement::Let(name, expr) => {
                let var_ty = self.ctx.new_var();
                self.check_expr(expr);
                self.vars.insert_new(name.clone(), var_ty.clone());
                self.ctx.add_pair(expr.ty.clone(), var_ty.clone());
                // save the typevar assigned to this variable
                expr.set_extra(var_ty);
            }
            Statement::Assign(name, expr) => {
                self.check_expr(expr);
                let var_ty = self.vars.get(name).unwrap();
                self.ctx.add_pair(expr.ty.clone(), var_ty.clone());
            }
            Statement::If(cond, then_, else_) => {
                self.check_expr(cond);
                self.ctx.add_pair(cond.ty.clone(), Ty::Bool);
                self.vars.enter_new_scope();
                for stmt in then_ {
                    self.check_stmt(stmt);
                }
                self.vars.exit_scope();
                self.vars.enter_new_scope();
                for stmt in else_ {
                    self.check_stmt(stmt);
                }
                self.vars.exit_scope();
            }
        }
    }

    fn check_expr(&mut self, expr: &mut Expr) {
        let Expr { ty: expr_type, kind, .. } = expr;
        match kind {
            ExprKind::Literal(lit) => {
                *expr_type = match lit {
                    Literal::Void => Ty::Void,
                    Literal::Int(_) => Ty::Int,
                    Literal::Bool(_) => Ty::Bool,
                }
            },
            ExprKind::Var(name) => {
                *expr_type = self.get_symbol_type(name);
            },
            ExprKind::BinOp(op, lhs, rhs) => {
                self.check_expr(lhs);
                self.check_expr(rhs);
                if op.is_arithmetic() { // (int, int) -> int
                    self.ctx.add_pair(lhs.ty.clone(), Ty::Int);
                    self.ctx.add_pair(rhs.ty.clone(), Ty::Int);
                    *expr_type = Ty::Int
                } else if op.is_ord_comparison() { // (int, int) -> bool
                    self.ctx.add_pair(lhs.ty.clone(), Ty::Int);
                    self.ctx.add_pair(rhs.ty.clone(), Ty::Int);
                    *expr_type = Ty::Bool;
                } else if op.is_eq_comparison() { // (T, T) -> bool (have to be the same type)
                    self.ctx.add_pair(lhs.ty.clone(), rhs.ty.clone());
                    self.ctx.add_pair(rhs.ty.clone(), lhs.ty.clone());
                    *expr_type = Ty::Bool;
                } else { unreachable!() }
            },
            ExprKind::TypeCast(_, _) => unreachable!(), // generated only after this phase
            ExprKind::Call(callee, args) => {
                self.check_expr(callee);
                let mut arg_types = vec![];
                let ret_type = self.ctx.new_var();
                *expr_type = ret_type.clone();
                for a in args {
                    self.check_expr(a);
                    arg_types.push(a.ty.clone());
                }
                let expected_fty = Ty::Func(Box::new(ret_type), arg_types.into());
                self.ctx.add_pair(expected_fty, callee.ty.clone());
            }
            ExprKind::New(ty, args) => {
                let obj_ty = ty.get_struct().get();
                if obj_ty.fields.len() != args.len() {
                    panic!("wrong number of arguments to constructor")
                }
                for i in 0..args.len() {
                    self.check_expr(&mut args[i]);
                    self.ctx.add_pair(args[i].ty.clone(), obj_ty.fields[i].1.clone());
                }
                *expr_type = ty.clone();
            }
        }
    }

    fn get_resolved(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::TyVar(i) => self.ctx.results[*i].as_ref().unwrap().clone(),
            Ty::Func(ret, params) => {
                let params_resolved = params.iter().map(|p| self.get_resolved(p)).collect();
                Ty::Func(Box::new(self.get_resolved(ret)), params_resolved)
            }
            _ => ty.clone(),
        }
    }

    fn resolve_stmt(&mut self, stmt: &mut Statement) {
        match stmt {
            Statement::ExprStmt(expr) => {
                self.resolve_expr(expr);
            }
            Statement::Return(expr) => {
                self.resolve_expr(expr);
                let ret_ty = self.get_resolved(&self.vars["$return"]);
                insert_cast(expr, ret_ty);
            }
            Statement::Let(name, expr) => {
                // restore the type var assigned to this variable
                let var_ty: Ty = expr.get_extra::<Ty>().unwrap().clone();
                self.resolve_expr(expr);
                insert_cast(expr, var_ty);
            }
            Statement::Assign(name, expr) => {
                self.resolve_expr(expr);
                let var_ty = self.get_resolved(&self.vars[name.as_str()]);
                insert_cast(expr, var_ty);
            }
            Statement::If(cond, then_, else_) => {
                self.resolve_expr(cond);
                insert_cast(cond, Ty::Bool);
                self.vars.enter_new_scope();
                for stmt in then_ {
                    self.resolve_stmt(stmt);
                }
                self.vars.exit_scope();
                self.vars.enter_new_scope();
                for stmt in else_ {
                    self.resolve_stmt(stmt);
                }
                self.vars.exit_scope();
            }
        }
    }

    fn resolve_expr(&mut self, expr: &mut Expr) {
        let Expr { ty: expr_type, kind, .. } = expr;
        match kind {
            ExprKind::Literal(_) => {},
            ExprKind::Var(name) => {
                let var_type = self.get_resolved(&self.get_symbol_type(name));
                let expected_type = self.get_resolved(expr_type);
                *expr_type = var_type; // actual type of the variable value
                insert_cast(expr, expected_type);
            },
            ExprKind::BinOp(op, lhs, rhs) => {
                self.resolve_expr(lhs);
                self.resolve_expr(rhs);
                if op.is_arithmetic() {
                    insert_cast(lhs, Ty::Int);
                    insert_cast(rhs, Ty::Int);
                    *expr_type = Ty::Int;
                } else if op.is_ord_comparison() {
                    insert_cast(lhs, Ty::Int);
                    insert_cast(rhs, Ty::Int);
                    *expr_type = Ty::Bool;
                } else if op.is_eq_comparison() {
                    let lhs_type = self.get_resolved(&lhs.ty);
                    insert_cast(rhs, lhs_type);
                    *expr_type = Ty::Bool;
                } else { unreachable!() }
                let expected_type = self.get_resolved(expr_type);
                insert_cast(expr, expected_type);
            },
            ExprKind::Call(callee, args) => {
                self.resolve_expr(callee);
                let (ret_ty, params_ty) = match &callee.ty {
                    Ty::Func(r, p) => (*r.clone(), p.clone()),
                    _ => panic!()
                };
                for (i, a) in args.iter_mut().enumerate() {
                    self.resolve_expr(a);
                    insert_cast(a, params_ty[i].clone());
                }
                let expected_type = self.get_resolved(expr_type);
                *expr_type = ret_ty;
                insert_cast(expr, expected_type);
            }
            ExprKind::New(ty, args) => {
                {
                    let obj_ty = ty.get_struct().get();
                    for (i, arg) in args.iter_mut().enumerate() {
                        self.resolve_expr(arg);
                        insert_cast(arg, obj_ty.fields[i].1.clone());
                    }
                }
                let expected_type = self.get_resolved(expr_type);
                *expr_type = ty.clone();
                insert_cast(expr, expected_type);
            }
            ExprKind::TypeCast(_, _) => unreachable!()
        }
    }
}

// this is to get around the borrow checker
fn insert_cast(e: &mut Expr, expected_ty: Ty) {
    let expr = std::mem::replace(e, ExprKind::Literal(Literal::Void).expr()); // temporary expression
    *e = cast(expr, expected_ty);
}

fn cast(e: Expr, expected_ty: Ty) -> Expr {
    if e.ty == expected_ty {
        e
    } else if expected_ty == Ty::Any {
        ExprKind::TypeCast(TypeCastKind::ToAny, Box::new(e)).expr_typed(Ty::Any)
    } else if expected_ty == Ty::Bool {
        // TODO: should arbitrary types be implicitly cast to bool?
        unimplemented!()
    } else if e.ty == Ty::Any && expected_ty.is_primitive() {
        ExprKind::TypeCast(TypeCastKind::FromAnySimple, Box::new(e)).expr_typed(expected_ty)
    } /*else if e.ty == Ty::Any && expected_ty.is_func() {
        ExprKind::TypeCast(TypeCastKind::FromAnyToFunc, Box::new(e)).expr_typed(expected_ty)
    }*/ else {
        panic!("Static type error: cannot cast from {:?} to {:?}", e.ty, expected_ty)
    }
}

pub struct TypeLookup {
    type_dict: HashMap<String, Ty>
}

impl TypeLookup {
    pub fn new() -> Self {
        Self { type_dict: HashMap::new() }
    }

    fn init_builtin_types(&mut self) {
        self.type_dict.insert("int".to_string(), Ty::Int);
        self.type_dict.insert("bool".to_string(), Ty::Bool);
        self.type_dict.insert("void".to_string(), Ty::Void);
        self.type_dict.insert("any".to_string(), Ty::Any);
    }

    fn collect_user_types(&mut self, p: &Program) {
        for typedef in &p.user_types {
            let name = typedef.get().name.clone();
            let ty = Ty::UserTy(typedef.clone());
            assert!(!self.type_dict.contains_key(&name));
            self.type_dict.insert(name, ty);
        }
    }

    fn lookup_ty(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Named(name) => self.type_dict.get(name).unwrap().clone(),
            Ty::Func(ret, args) => {
                let ret_ty = Box::new(self.lookup_ty(ret));
                let args_ty = args.iter().map(|a| self.lookup_ty(a)).collect();
                Ty::Func(ret_ty, args_ty)
            },
            _ => ty.clone()
        }
    }

    pub fn lookup_all(mut self, p: &mut Program) {
        // 1. collect all
        self.init_builtin_types();
        self.collect_user_types(p);
        // 2. find all NamedTypes and replace them
        for typedef in &p.user_types {
            let mut typedef = typedef.get_mut();
            for (_, field_ty) in &mut typedef.fields {
                *field_ty = self.lookup_ty(field_ty);
            }
        }
        for func in &mut p.functions {
            for (_, ty) in &mut func.params {
                *ty = self.lookup_ty(ty);
            }
            func.return_type = self.lookup_ty(&func.return_type);
            for stmt in &mut func.body {
                self.lookup_in_stmt(stmt);
            }
        }
        //p.type_map = self.type_dict;
    }

    fn lookup_in_stmt(&self, stmt: &mut Statement) {
        match stmt {
            Statement::ExprStmt(expr)
            | Statement::Return(expr)
            | Statement::Let(_, expr) => {
                self.lookup_in_expr(expr);
            },
            Statement::Assign(_, expr) => {
                self.lookup_in_expr(expr);
            }
            Statement::If(cond, then_, else_) => {
                self.lookup_in_expr(cond);
                then_.iter_mut().for_each(|stmt| self.lookup_in_stmt(stmt));
                else_.iter_mut().for_each(|stmt| self.lookup_in_stmt(stmt));
            }
        }
    }

    fn lookup_in_expr(&self, expr: &mut Expr) {
        match &mut expr.kind {
            ExprKind::Literal(_) => {},
            ExprKind::Var(_) => {},
            ExprKind::BinOp(_, lhs, rhs) => {
                self.lookup_in_expr(lhs);
                self.lookup_in_expr(rhs);
            },
            ExprKind::Call(callee, args) => {
                self.lookup_in_expr(callee);
                args.iter_mut().for_each(|a| self.lookup_in_expr(a));
            },
            ExprKind::New(ty, args) => {
                args.iter_mut().for_each(|a| self.lookup_in_expr(a));
                *ty = self.lookup_ty(ty);
            }
            ExprKind::TypeCast(_, _) => unreachable!()
        }
    }
}