/*
Type-checking takes several stages:
1. Collecting type-variables into an inference context
2. "Unifying" type-variables to the most general type
3. Assigning types to expressions and inserting type casts where needed
*/

use std::collections::HashMap;

use crate::{ast::*, tyunify::InferenceContext, util::ScopedMap};

pub struct TypeChecker {
    globals: HashMap<String, Ty>,
    // local to a function
    ctx: InferenceContext,
    vars: ScopedMap<String, Ty>,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self { globals: HashMap::new(), ctx: InferenceContext::new(), vars: ScopedMap::new(false) }
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
            let prev = self.globals.insert(func.name.clone(), func.create_ftype());
            if prev.is_some() {
                panic!("Duplicate function: {}", func.name);
            }
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
        self.ctx.dump();
        println!("{}", func);
        // 2. unify type variables
        println!("Solving {}", func.name);
        self.ctx.solve_all();
        self.ctx.dump();
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
                self.ctx.add_assignable(&expr.ty, &self.vars["$return"]);
            }
            Statement::Let(name, expr) => {
                let var_ty = self.ctx.new_tyvar();
                self.check_expr(expr);
                self.vars.insert_new(name.clone(), var_ty.clone());
                self.ctx.add_assignable(&expr.ty, &var_ty);
                // save the typevar assigned to this variable
                expr.set_extra(var_ty);
            }
            Statement::Assign(lhs, expr) => {
                self.check_expr(lhs);
                self.check_expr(expr);
                self.ctx.add_assignable(&expr.ty, &lhs.ty);
            }
            Statement::If(cond, then_, else_) => {
                self.check_expr(cond);
                self.ctx.add_assignable(&cond.ty, &Ty::Bool);
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
            Statement::RcDropsReturn { .. } => unreachable!()
        }
    }

    fn check_expr(&mut self, expr: &mut Expr) {
        let Expr { ty: expr_type, kind, .. } = expr;
        *expr_type = self.ctx.new_tyvar();
        let expected_ty;
        match kind {
            ExprKind::Literal(lit) => {
                expected_ty = match lit {
                    Literal::Void => Ty::Void,
                    Literal::Int(_) => Ty::Int,
                    Literal::Bool(_) => Ty::Bool,
                }
            },
            ExprKind::Var(name) => {
                expected_ty = self.get_symbol_type(name);
            },
            ExprKind::BinOp(op, lhs, rhs) => {
                self.check_expr(lhs);
                self.check_expr(rhs);
                if op.is_arithmetic() { // (int, int) -> int
                    self.ctx.add_assignable(&lhs.ty, &Ty::Int);
                    self.ctx.add_assignable(&rhs.ty, &Ty::Int);
                    expected_ty = Ty::Int
                } else if op.is_ord_comparison() { // (int, int) -> bool
                    self.ctx.add_assignable(&lhs.ty, &Ty::Int);
                    self.ctx.add_assignable(&rhs.ty, &Ty::Int);
                    expected_ty = Ty::Bool
                } else if op.is_eq_comparison() { // (T, T) -> bool (have to be the same type)
                    self.ctx.add_equal(&lhs.ty, &rhs.ty);
                    expected_ty = Ty::Bool
                } else { unreachable!() }
            },
            ExprKind::TypeCast(_, _) => unreachable!(), // generated only after this phase
            ExprKind::Call(callee, args) => {
                self.check_expr(callee);
                let mut arg_types = vec![];
                let ret_type = self.ctx.new_tyvar();
                expected_ty = ret_type.clone();
                for a in args {
                    self.check_expr(a);
                    arg_types.push(a.ty.clone());
                }
                let expected_fty = Ty::Func(Box::new(ret_type), arg_types.into());
                self.ctx.add_assignable(&expected_fty, &callee.ty);
            }
            ExprKind::New(ty, args) => {
                let obj_ty = ty.get_struct().get();
                if obj_ty.fields.len() != args.len() {
                    panic!("wrong number of arguments to constructor")
                }
                for i in 0..args.len() {
                    self.check_expr(&mut args[i]);
                    self.ctx.add_assignable(&args[i].ty, &obj_ty.fields[i].1);
                }
                expected_ty = ty.clone();
            }
            ExprKind::Field(obj, field) => {
                self.check_expr(obj);
                expected_ty = self.ctx.new_tyvar();
                self.ctx.add_field(&obj.ty, field, &expected_ty);
            }
            ExprKind::RcDup(_) => unreachable!(),
            ExprKind::RcDrop(_) => unreachable!(),
        }
        self.ctx.add_assignable(&expected_ty, expr_type);
    }

    fn get_resolved(&self, ty: &Ty) -> Ty {
        self.ctx.get_resolved(ty)
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
                insert_cast(expr, self.get_resolved(&var_ty));
            }
            Statement::Assign(lhs, expr) => {
                self.resolve_expr(expr);
                self.resolve_expr(lhs);
                insert_cast(expr, lhs.ty.clone());
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
            Statement::RcDropsReturn { .. } => unreachable!(),
        }
    }

    fn resolve_expr(&mut self, expr: &mut Expr) {
        let Expr { ty: expr_type, kind, .. } = expr;
        let value_type; // The actual type of the expression result
        match kind {
            ExprKind::Literal(lit) => {
                value_type = match lit {
                    Literal::Void => Ty::Void,
                    Literal::Int(_) => Ty::Int,
                    Literal::Bool(_) => Ty::Bool,
                }
            },
            ExprKind::Var(name) => {
                let var_type = self.get_resolved(&self.get_symbol_type(name));
                value_type = var_type;
            },
            ExprKind::BinOp(op, lhs, rhs) => {
                self.resolve_expr(lhs);
                self.resolve_expr(rhs);
                if op.is_arithmetic() {
                    insert_cast(lhs, Ty::Int);
                    insert_cast(rhs, Ty::Int);
                    value_type = Ty::Int;
                } else if op.is_ord_comparison() {
                    insert_cast(lhs, Ty::Int);
                    insert_cast(rhs, Ty::Int);
                    value_type = Ty::Bool;
                } else if op.is_eq_comparison() {
                    let lhs_type = self.get_resolved(&lhs.ty);
                    insert_cast(rhs, lhs_type);
                    value_type = Ty::Bool;
                } else { unreachable!() }
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
                value_type = ret_ty;
            }
            ExprKind::New(ty, args) => {
                {
                    let obj_ty = ty.get_struct().get();
                    for (i, arg) in args.iter_mut().enumerate() {
                        self.resolve_expr(arg);
                        insert_cast(arg, obj_ty.fields[i].1.clone());
                    }
                }
                value_type = ty.clone();
            }
            ExprKind::Field(obj, field) => {
                self.resolve_expr(obj);
                let resolved_field_ty = match &obj.ty {
                    Ty::UserTy(td) => {
                        td.get().get_field_ty(field).unwrap().clone()
                    }
                    _ => panic!()
                };
                value_type = resolved_field_ty;
            }
            ExprKind::TypeCast(_, _) => unreachable!(),
            ExprKind::RcDup(_) => unreachable!(),
            ExprKind::RcDrop(_) => unreachable!(),
        }
        let expected_type = self.get_resolved(expr_type);
        *expr_type = value_type;
        insert_cast(expr, expected_type);
    }
}

// this is to get around the borrow checker
fn insert_cast(e: &mut Expr, expected_ty: Ty) {
    let expr = std::mem::take(e);
    *e = cast(expr, expected_ty);
}

fn cast(e: Expr, expected_ty: Ty) -> Expr {
    if e.ty == expected_ty {
        e
    } else if expected_ty == Ty::Any {
        ExprKind::TypeCast(TypeCastKind::ToAny, Box::new(e)).expr_typed(Ty::Any)
    } else if e.ty == Ty::Any && expected_ty.is_primitive() {
        ExprKind::TypeCast(TypeCastKind::FromAnySimple, Box::new(e)).expr_typed(expected_ty)
    } else if expected_ty == Ty::Bool {
        // TODO: should arbitrary types be implicitly cast to bool?
        unimplemented!()
    }/*else if e.ty == Ty::Any && expected_ty.is_func() {
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
            Statement::RcDropsReturn { .. } => unreachable!(),
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
            ExprKind::Field(obj, _) => {
                self.lookup_in_expr(obj);
            }
            ExprKind::TypeCast(_, _) => unreachable!(),
            ExprKind::RcDup(_) => unreachable!(),
            ExprKind::RcDrop(_) => unreachable!(),
        }
    }
}