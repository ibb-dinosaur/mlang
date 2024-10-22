/*
We use canrun (Rust impl of miniKanren) to solve types.
Type-checking takes several stages:
1. Collecting type-variables into a canrun program
2. Unifying the types
3. Assigning types to expressions and inserting type casts where needed
*/

use std::{cell::RefCell, collections::HashMap};

use crate::{ast::{Expr, ExprKind, Function, Literal, Program, SourceLoc, Statement, Stmt, Ty, TypeCastKind, TypeDef}, report::CompileError, util::ScopedMap};

fn make_fty(ret: logica::Term, mut args: Vec<logica::Term>) -> logica::Term {
    // ('func' ret args...)
    args.insert(0, ret);
    logica::Term::Comp("func".into(), args.into())
}

fn make_opt(inner: logica::Term) -> logica::Term {
    // ('opt' inner)
    logica::Term::Comp("opt".into(), vec![inner].into())
}

#[derive(Debug, Clone)]
pub struct UnifTy(logica::Term);

impl From<logica::Term> for UnifTy {
    fn from(value: logica::Term) -> Self { Self(value) }
}
impl From<UnifTy> for logica::Term {
    fn from(value: UnifTy) -> Self { value.0 }
}

impl std::fmt::Display for UnifTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl PartialEq for UnifTy {
    fn eq(&self, _other: &Self) -> bool {
        panic!("comparing type variables is not supported")
    }
}
impl Eq for UnifTy {}
impl PartialOrd for UnifTy {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for UnifTy {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        panic!("ordering type variables is not supported")
    }
}

pub struct TypeChecker {
    globals: HashMap<String, logica::Term>,
    vars: ScopedMap<String, logica::Term>,
    goals: Vec<logica::BoxedGoal>,
    tyvars: Vec<logica::TVar>,
    solutions: HashMap<logica::TVar, logica::Term>,
    dump_info: bool,
}

thread_local! {
    static IVBA: [logica::Term; 4] = [
        logica::Term::atom("int"),
        logica::Term::atom("void"),
        logica::Term::atom("bool"),
        logica::Term::atom("any")];
    // must be global because the Reify trait doesn't have a context parameter
    // and it needs to access this to get the type definitions
    static USER_TYPES: RefCell<HashMap<String, TypeDef>> = RefCell::new(HashMap::new());
}

fn logic_ty(t: &Ty) -> logica::Term {
    match t {
        Ty::Unk | Ty::Named(_) => panic!(),
        Ty::Int => IVBA.with(|ivba| ivba[0].clone()),
        Ty::Void => IVBA.with(|ivba| ivba[1].clone()),
        Ty::Bool => IVBA.with(|ivba| ivba[2].clone()),
        Ty::Any => IVBA.with(|ivba| ivba[3].clone()),
        Ty::UserTy(td) => {
            let name = format!("struct_{}", td.get().name);
            logica::Term::atom(name)
        }
        Ty::Func(ret, args) => {
            let args = args.iter().map(logic_ty).collect();
            make_fty(logic_ty(ret), args)
        }
        Ty::Var(x) => x.0.clone(),
        Ty::Option(inner) => make_opt(logic_ty(inner)),
    }
}

impl TypeChecker {
    pub fn new() -> Self {
        Self { globals: HashMap::new(), 
            vars: ScopedMap::new(false),
            goals: vec![],
            tyvars: vec![],
            solutions: HashMap::new(),
            dump_info: false }
    }

    fn get_symbol_type(&self, name: &str, loc: &SourceLoc) -> logica::Term {
        match self.vars.get(name) {
            Some(lty) => lty.clone(),
            None => match self.globals.get(name) {
                Some(gty) => gty.clone(),
                None => CompileError::throw(format!("Unknown symbol: {}", name), loc)
            }   
        }
    }

    pub fn check(&mut self, prog: &mut Program) {
        // collect globals
        let mut user_types = HashMap::new();
        for td in &prog.user_types {
            user_types.insert(td.get().name.clone(), td.clone());
        }
        USER_TYPES.replace(user_types);

        for func in &prog.functions {
            let prev = self.globals.insert(func.name.clone(), 
                logic_ty(&func.create_ftype()));
            if prev.is_some() {
                CompileError::throw("Duplicate function definition".to_string(), &func.loc);
            }
        }
        for func in &mut prog.functions {
            self.check_func(func);
        }
    }

    fn check_func(&mut self, func: &mut Function) {
        self.vars.reset();
        self.goals.clear();
        self.tyvars.clear();
        self.solutions.clear();
        self.dump_info = crate::OPTIONS.get().unwrap().print_typeck.contains(&func.name);

        for (name, ty) in &func.params {
            self.vars.insert_new(name.clone(), logic_ty(ty));
        }
        self.vars.insert_new("$return".to_string(), logic_ty(&func.return_type));
        // 1. collect type variables
        self.vars.enter_new_scope();
        for stmt in &mut func.body {
            self.visit_stmt(stmt);
        }
        self.vars.exit_scope();
        if self.dump_info {
            // print AST with type variables
            println!("{}", func);
        }
        // 2. solve constraints
        let q = logica::Term::Comp(
            "list".into(),
            self.tyvars.iter().map(|x| logica::Term::Var(*x)).collect());
        let goal = logica::all(std::mem::take(&mut self.goals));
        let sol = match logica::solve(goal,q).next() {
            Some(x) => x,
            None => CompileError::throw(
                format!("Type-checking failed for function {}: no solution found", func.name),
                &func.loc
            )
        };
        
        let logica::Term::Comp(_, solution) = sol else { unreachable!() };
        for (lv, t) in self.tyvars.iter().zip(solution) {
            self.solutions.insert(*lv, t);
        }
        // 3. assign types to expressions, insert casts
        self.vars.enter_new_scope();
        for stmt in &mut func.body {
            self.resolve_stmt(stmt);
        }
        self.vars.exit_scope();
        // done! (hopefully)
    }

    // `from` must be (implicitly) castable to `to`
    fn restrict_castable(&mut self, from: &logica::Term, to: &logica::Term) {
        if self.dump_info {
            println!("restrict_castable {} -> {}", from, to);
        }
        let tmp = logica::Term::Var(logica::TVar::new());
        let goal = logica::any([
            logica::unify(from.clone(), to.clone()), // from ~ to
            logica::unify(to.clone(), make_opt(from.clone())), // from : t, to : option t
            logica::unify(from.clone(), make_opt(to.clone())), // from : option t, to : t
            logica::all([  // from : option t, to : bool
                logica::unify(from.clone(), make_opt(tmp.clone())),
                logica::unify(to.clone(), logic_ty(&Ty::Bool))
            ]),
            logica::unify(from.clone(), logic_ty(&Ty::Any)), // from ~ any
            logica::unify(logic_ty(&Ty::Any), to.clone()) // to ~ any
        ]);
        self.goals.push(goal);
    }

    fn restrict_equal(&mut self, from: &logica::Term, to: &logica::Term) {
        if self.dump_info {
            println!("restrict_equal {} ~ {}", from, to);
        }
        let goal = logica::unify(from.clone(), to.clone());
        self.goals.push(goal);
    }

    fn restrict_field(&mut self, obj: &logica::Term, field_name: &str, field: &logica::Term) {
        if self.dump_info {
            println!("restrict_field {}.{} -> {}", obj, field_name, field);
        }
        let field_name = field_name.to_string();
        let field = field.clone();
        let goal = logica::project(obj.clone(),
            move |obj_ty| {
                if let logica::Term::Atom(s) = &obj_ty {
                    if let Some(struct_name) = s.strip_prefix("struct_") {
                        USER_TYPES.with_borrow(|user_types| {
                            match user_types.get(struct_name).unwrap().get().get_field_ty(&field_name) {
                                None => logica::fail(),
                                Some(field_ty) =>
                                    logica::unify(field.clone(), logic_ty(&field_ty)),
                            }
                        })
                    } else {
                        logica::fail()
                    }
                } else { logica::fail() }
            });
        self.goals.push(goal);
    }

    fn visit_stmt(&mut self, stmt: &mut Stmt) {
        match &mut stmt.s {
            Statement::ExprStmt(expr) => {
                self.visit_expr(expr);
            }
            Statement::Return(expr) => {
                self.visit_expr(expr);
                let expr_ty = logic_ty(&expr.ty);
                let ret_ty = self.vars["$return"].clone();
                self.restrict_castable(&expr_ty, &ret_ty);
            }
            Statement::Let(name, expr) => {
                let var_ty = logica::Term::Var(self.new_tyvar());
                self.visit_expr(expr);
                let rhs_ty = logic_ty(&expr.ty);
                self.vars.insert_new(name.clone(), var_ty.clone());
                self.restrict_castable(&rhs_ty, &var_ty);
                // save the typevar assigned to this variable
                stmt.set_extra(var_ty);
            }
            Statement::Assign(lhs, expr) => {
                self.visit_expr(lhs);
                let lhs_ty = logic_ty(&lhs.ty);
                self.visit_expr(expr);
                let rhs_ty = logic_ty(&expr.ty);
                self.restrict_castable(&rhs_ty, &lhs_ty);
            }
            Statement::If(cond, then_, else_) => {
                self.visit_expr(cond);
                let cond_ty = logic_ty(&cond.ty);
                self.restrict_castable(&cond_ty, &logic_ty(&Ty::Bool));
                self.vars.enter_new_scope();
                for stmt in then_ {
                    self.visit_stmt(stmt);
                }
                self.vars.exit_scope();
                self.vars.enter_new_scope();
                for stmt in else_ {
                    self.visit_stmt(stmt);
                }
                self.vars.exit_scope();
            }
            Statement::RcDropsReturn { .. } => unreachable!()
        }
    }

    // Only insert casts when an expression is *used*, not when it's produced
    fn visit_expr(&mut self, expr: &mut Expr) {
        let Expr { ty: expr_type, kind, .. } = expr;
        match kind {
            ExprKind::Literal(lit) => {
                *expr_type = match lit {
                    Literal::Void => Ty::Void,
                    Literal::Int(_) => Ty::Int,
                    Literal::Bool(_) => Ty::Bool,
                    Literal::Null => { // null : option t
                        let literal_ty = self.new_tyvar().into();
                        let t = self.new_tyvar().into();
                        self.restrict_equal(&literal_ty, &make_opt(t));
                        Ty::Var(literal_ty.into())
                    }
                };
            },
            ExprKind::Var(name) => {
                *expr_type = Ty::Var(self.get_symbol_type(name, &expr.loc).into());
            },
            ExprKind::BinOp(op, lhs, rhs) => {
                let lhs_ty = self.visit_and_add_implicit_cast(lhs);
                let rhs_ty = self.visit_and_add_implicit_cast(rhs);
                let int = logic_ty(&Ty::Int);
                if op.is_arithmetic() { // (int, int) -> int
                    self.restrict_castable(&lhs_ty, &int);
                    self.restrict_castable(&rhs_ty, &int);
                    *expr_type = Ty::Var(int.into());
                } else if op.is_ord_comparison() { // (int, int) -> bool
                    self.restrict_castable(&lhs_ty, &int);
                    self.restrict_castable(&rhs_ty, &int);
                    *expr_type = Ty::Var(logic_ty(&Ty::Bool).into());
                } else if op.is_eq_comparison() { // (T, T) -> bool (have to be the same type)
                    self.restrict_equal(&lhs_ty, &rhs_ty);
                    *expr_type = Ty::Var(logic_ty(&Ty::Bool).into());
                } else { unreachable!() }
            },
            ExprKind::TypeCast(_, _) => unreachable!(), // generated only after this phase
            ExprKind::Call(callee, args) => {
                self.visit_expr(callee);
                let mut arg_tyvars = vec![];
                let ret_type = logica::Term::Var(self.new_tyvar());
                *expr_type = Ty::Var(ret_type.clone().into());
                for arg in args {
                    let arg_t = self.visit_and_add_implicit_cast(arg);
                    arg_tyvars.push(arg_t);
                }
                let expected_fty = make_fty(ret_type, arg_tyvars);
                // function types are not castable
                self.restrict_equal(&expected_fty, &logic_ty(&callee.ty));
            }
            ExprKind::New(ty, args) => {
                let obj_ty = ty.get_struct().get();
                if obj_ty.fields.len() != args.len() {
                    CompileError::throw("wrong number of arguments to constructor".to_string(), &expr.loc);
                }
                for i in 0..args.len() {
                    let arg_t = self.visit_and_add_implicit_cast(&mut args[i]);
                    self.restrict_equal(&arg_t, &logic_ty(&obj_ty.fields[i].1));
                }
                *expr_type = ty.clone();
            }
            ExprKind::Field(obj, field) => {
                self.visit_and_add_implicit_cast(obj);
                let obj_ty = logic_ty(&obj.ty);
                let field_ty = self.new_tyvar().into();
                self.restrict_field(&obj_ty, field, &field_ty);
                *expr_type = Ty::Var(field_ty.into());
            }
            ExprKind::RcDup(_) => unreachable!(),
            ExprKind::RcDrop(_) => unreachable!(),
        }
    }

    /// When an expression result is used, add (possible) implicit cast
    fn visit_and_add_implicit_cast(&mut self, e: &mut Expr) -> logica::Term {
        self.visit_expr(e);
        let original_expr_type = logic_ty(&e.ty);
        let cast_var = logica::Term::Var(self.new_tyvar());
        e.ty = Ty::Var(UnifTy(cast_var.clone()));
        self.restrict_castable(&original_expr_type, &cast_var);
        cast_var
    }

    fn new_tyvar(&mut self) -> logica::TVar {
        let v = logica::TVar::new();
        self.tyvars.push(v);
        v
    }

    fn get_resolved_kr(&self, ty: &logica::Term) -> Ty {
        match ty {
            logica::Term::Atom(s) => {
                match &**s {
                    "int" => Ty::Int,
                    "void" => Ty::Void,
                    "bool" => Ty::Bool,
                    "any" => Ty::Any,
                    _ if s.starts_with("struct_") => {
                        let name = &s[7..];
                        USER_TYPES.with_borrow(|user_types| {
                            Ty::UserTy(user_types.get(name).unwrap().clone())
                        })
                    }
                    // reified type variables which haven't been assigned
                    // a concrete type are written as _.N and are treated as Any
                    _ if s.starts_with("_.") => Ty::Any,
                    _ => panic!()
                }
            }
            logica::Term::Comp(f, args) => {
                if &**f == "func" {
                    let ret = self.get_resolved_kr(&args[0]);
                    let args: Vec<_> = args.iter().skip(1).map(|x| self.get_resolved_kr(x)).collect();
                    Ty::Func(Box::new(ret), args.into_boxed_slice())
                } else if &**f == "opt" {
                    Ty::Option(Box::new(self.get_resolved_kr(&args[0])))
                } else { panic!() }
            }
            logica::Term::Var(v) => 
                self.get_resolved_kr(self.solutions.get(v).unwrap())
        }
    }

    fn get_resolved_t(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Var(UnifTy(x)) => self.get_resolved_kr(x),
            // recursively resolve functions
            Ty::Func(ret, args) => {
                let ret = self.get_resolved_t(ret);
                let args = args.iter().map(|x| self.get_resolved_t(x)).collect();
                Ty::Func(Box::new(ret), args)
            }
            _ => ty.clone()
        }
    }

    fn resolve_stmt(&mut self, stmt: &mut Stmt) {
        match &mut stmt.s {
            Statement::ExprStmt(expr) => {
                self.resolve_expr(expr);
            }
            Statement::Return(expr) => {
                self.resolve_expr(expr);
                let ret_ty = self.get_resolved_kr(&self.vars["$return"]);
                insert_cast(expr, ret_ty);
            }
            Statement::Let(_, expr) => {
                // restore the type var assigned to this variable
                let var_ty= stmt.extra.take().unwrap().downcast().unwrap();
                self.resolve_expr(expr);
                insert_cast(expr, self.get_resolved_kr(&var_ty));
            }
            Statement::Assign(lhs, expr) => {
                self.resolve_expr(expr);
                self.resolve_expr(lhs);
                insert_cast(expr, self.get_resolved_t(&lhs.ty));
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
                    Literal::Null => self.get_resolved_t(expr_type)
                }
            },
            ExprKind::Var(name) => {
                let var_type = self.get_resolved_kr(&self.get_symbol_type(name, &expr.loc));
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
                    let lhs_type = self.get_resolved_t(&lhs.ty);
                    insert_cast(rhs, lhs_type);
                    value_type = Ty::Bool;
                } else { unreachable!() }
            },
            ExprKind::Call(callee, args) => {
                self.resolve_expr(callee);
                let (ret_ty, params_ty) = match &callee.ty {
                    Ty::Func(r, p) => (*r.clone(), p.clone()),
                    _ => panic!("{}", callee.ty)
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
                        match td.get().get_field_ty(field) {
                            Some(ty) => ty.clone(),
                            None => CompileError::throw(
                                format!("field {} does not exist on type {}", field, td.get().name), &expr.loc),
                        }
                    }
                    _ => CompileError::throw("field access on non-struct".to_string(), &expr.loc)
                };
                value_type = resolved_field_ty;
            }
            ExprKind::TypeCast(_, _) => unreachable!(),
            ExprKind::RcDup(_) => unreachable!(),
            ExprKind::RcDrop(_) => unreachable!(),
        }
        let expected_type = self.get_resolved_t(expr_type);
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
    let e_loc = e.loc.clone();
    if e.ty == expected_ty {
        e
    } else if expected_ty == Ty::Any {
        ExprKind::TypeCast(TypeCastKind::ToAny, Box::new(e)).expr_typed(Ty::Any).located(e_loc)
    } else if e.ty == Ty::Any && expected_ty.is_primitive() {
        ExprKind::TypeCast(TypeCastKind::FromAnySimple, Box::new(e)).expr_typed(expected_ty).located(e_loc)
    } else if matches!((&e.ty, &expected_ty), (Ty::Option(_), Ty::Bool)) {
        // option t -> bool
        ExprKind::TypeCast(TypeCastKind::OptionToBool, Box::new(e)).expr_typed(expected_ty).located(e_loc)
    } else if expected_ty == Ty::Option(Box::new(e.ty.clone())) {
        // t -> option t
        ExprKind::TypeCast(TypeCastKind::WrapOption, Box::new(e)).expr_typed(expected_ty).located(e_loc)
    } else if e.ty == Ty::Option(Box::new(expected_ty.clone())) {
        // option t -> t
        ExprKind::TypeCast(TypeCastKind::UnwrapOption, Box::new(e)).expr_typed(expected_ty).located(e_loc)
    } else if expected_ty == Ty::Bool {
        // TODO: should arbitrary types be implicitly cast to bool?
        unimplemented!()
    }/*else if e.ty == Ty::Any && expected_ty.is_func() {
        ExprKind::TypeCast(TypeCastKind::FromAnyToFunc, Box::new(e)).expr_typed(expected_ty)
    }*/ else {
        CompileError::throw(
            format!("Static type error: cannot cast from {:?} to {:?}", e.ty, expected_ty), &e.loc)
    }
}