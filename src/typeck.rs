use std::collections::HashMap;

use crate::{ast::*, report::CompileError};

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

    fn lookup_ty(&self, ty: &Ty, loc: &SourceLoc) -> Ty {
        match ty {
            Ty::Named(name) => match self.type_dict.get(name) {
                Some(ty) => ty.clone(),
                None => CompileError::throw(format!("Type {} does not exist", name), loc)
            }
            Ty::Func(ret, args) => {
                let ret_ty = Box::new(self.lookup_ty(ret, loc));
                let args_ty = args.iter().map(|a| self.lookup_ty(a, loc)).collect();
                Ty::Func(ret_ty, args_ty)
            },
            Ty::Option(inner) => {
                let inner_ty = Box::new(self.lookup_ty(inner, loc));
                assert!(matches!(&*inner_ty, Ty::UserTy(_)));
                Ty::Option(inner_ty)
            }
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
            let loc = typedef.loc.clone();
            for (_, field_ty) in &mut typedef.fields {
                *field_ty = self.lookup_ty(field_ty, &loc);
            }
        }
        for func in &mut p.functions {
            for (_, ty) in &mut func.params {
                *ty = self.lookup_ty(ty, &func.loc);
            }
            func.return_type = self.lookup_ty(&func.return_type, &func.loc);
            for stmt in &mut func.body {
                self.lookup_in_stmt(stmt);
            }
        }
        //p.type_map = self.type_dict;
    }

    fn lookup_in_stmt(&self, stmt: &mut Stmt) {
        match &mut stmt.s {
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
                *ty = self.lookup_ty(ty, &expr.loc);
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