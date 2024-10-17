/*
We use canrun (Rust impl of miniKanren) to solve types.
Type-checking takes several stages:
1. Collecting type-variables into a canrun program
2. Unifying the types
3. Assigning types to expressions and inserting type casts where needed
*/

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use canrun::{Query, Reify};

use crate::{ast::{Expr, ExprKind, Function, Literal, Program, Statement, Ty, TypeCastKind, TypeDef}, util::ScopedMap};

/// Kanren term, imitates a Lisp
#[derive(Debug)]
enum KrTerm {
    Atom(Rc<str>),
    List(Rc<canrun::lvec::LVec<KrTerm>>)
}

type KrVal = canrun::Value<KrTerm>;

impl canrun::Unify for KrTerm {
    fn unify(state: canrun::State, a: Rc<Self>, b: Rc<Self>) -> Option<canrun::State> {
        match (&*a, &*b) {
            (KrTerm::Atom(a), KrTerm::Atom(b)) if a == b => Some(state),
            (KrTerm::List(a), KrTerm::List(b)) => 
                canrun::lvec::LVec::unify(state, a.clone(), b.clone()),
            _ => None
        }
    }
}

impl canrun::Reify for KrTerm {
    type Reified = Ty;

    fn reify_in(&self, state: &canrun::ReadyState) -> Option<Self::Reified> {
        match self {
            KrTerm::Atom(s) => match &**s {
                "int" => Some(Ty::Int),
                "void" => Some(Ty::Void),
                "bool" => Some(Ty::Bool),
                "any" => Some(Ty::Any),
                "func" => Some(Ty::Named("$FUNC".to_string())), // a little hack
                _ if s.starts_with("struct_") => {
                    let name = &s[7..];
                    USER_TYPES.with_borrow(|user_types| {
                        Some(Ty::UserTy(user_types.get(name).unwrap().clone()))
                    })
                }
                _ => unreachable!()
            },
            KrTerm::List(rc) => {
                let mut v = rc.reify_in(state).unwrap();
                if v[0] == Ty::Named("$FUNC".to_string()) {
                    v.remove(0); // the $FUNC tag
                    let ret = v.remove(0);
                    let args = v;
                    Some(Ty::Func(Box::new(ret), args.into_boxed_slice()))
                } else { unreachable!() }
            },
        }
    }
}

impl KrTerm {
    fn make_fty(ret: KrVal, mut args: Vec<KrVal>) -> KrVal {
        // ('func' ret args...)
        args.insert(0, ret);
        args.insert(0, IVBAF.with(|x| x[4].clone()));
        KrTerm::List(Rc::new(args.into())).into()
    }
}

#[derive(Debug, Clone)]
pub struct UnifTy(KrVal);

impl From<KrVal> for UnifTy {
    fn from(value: KrVal) -> Self { Self(value) }
}
impl From<UnifTy> for KrVal {
    fn from(value: UnifTy) -> Self { value.0 }
}

impl std::fmt::Display for UnifTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            canrun::Value::Var(v) =>
                write!(f, "tv${}", lvar_get_usize(v)),
            canrun::Value::Resolved(rc) =>
                write!(f, "{:?}", rc), // TODO
        }
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
    globals: HashMap<String, KrVal>,
    vars: ScopedMap<String, KrVal>,
    goals: Vec<Box<dyn canrun::Goal>>,
    tyvars: Vec<canrun::LVar<KrTerm>>,
    solutions: HashMap<usize, Ty>
}

thread_local! {
    static IVBAF: [KrVal; 5] = [
        KrTerm::Atom("int".into()).into(),
        KrTerm::Atom("void".into()).into(),
        KrTerm::Atom("bool".into()).into(),
        KrTerm::Atom("any".into()).into(),
        KrTerm::Atom("func".into()).into()];
    // must be global because the Reify trait doesn't have a context parameter
    // and it needs to access this to get the type definitions
    static USER_TYPES: RefCell<HashMap<String, TypeDef>> = RefCell::new(HashMap::new());
}

fn logic_ty(t: &Ty) -> KrVal {
    match t {
        Ty::Unk | Ty::Named(_) => panic!(),
        Ty::Int => IVBAF.with(|ivba| ivba[0].clone()),
        Ty::Void => IVBAF.with(|ivba| ivba[1].clone()),
        Ty::Bool => IVBAF.with(|ivba| ivba[2].clone()),
        Ty::Any => IVBAF.with(|ivba| ivba[3].clone()),
        Ty::UserTy(td) => {
            let name = format!("struct_{}", td.get().name);
            KrTerm::Atom(name.into()).into()
        }
        Ty::Func(ret, args) => {
            let args = args.iter().map(logic_ty).collect();
            KrTerm::make_fty(logic_ty(ret), args)
        }
        Ty::Var(x) => x.0.clone(),
    }
}

impl TypeChecker {
    pub fn new() -> Self {
        Self { globals: HashMap::new(), 
            vars: ScopedMap::new(false),
            goals: vec![],
            tyvars: vec![],
            solutions: HashMap::new() }
    }

    fn get_symbol_type(&self, name: &str) -> KrVal {
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
        let mut user_types = HashMap::new();
        for td in &prog.user_types {
            user_types.insert(td.get().name.clone(), td.clone());
        }
        USER_TYPES.replace(user_types);

        for func in &prog.functions {
            let prev = self.globals.insert(func.name.clone(), 
                logic_ty(&func.create_ftype()));
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
        self.goals.clear();
        self.tyvars.clear();
        self.solutions.clear();

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
        // 2. solve constraints
        let q = canrun::Value::var();
        let q_v: canrun::lvec::LVec<_> = self.tyvars.iter().cloned().map(canrun::Value::Var).collect();
        self.goals.push(Box::new(canrun::unify(q.clone(), q_v)));

        let solution = 
            canrun::goals::All::from(std::mem::take(&mut self.goals))
            .query(q).next().unwrap();
        
        for (lv, t) in self.tyvars.iter().zip(solution) {
            self.solutions.insert(lvar_get_usize(lv), t);
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
    fn restrict_castable(&mut self, from: &KrVal, to: &KrVal) {
        //println!("restrict_castable {:?} -> {:?}", from, to);
        let goal = canrun::any![
            canrun::unify(from.clone(), to.clone()),
            canrun::unify(from.clone(), logic_ty(&Ty::Any)),
            canrun::unify(logic_ty(&Ty::Any), to.clone())
        ];
        self.goals.push(Box::new(goal));
    }

    fn restrict_equal(&mut self, from: &KrVal, to: &KrVal) {
        //println!("restrict_equal {:?} ~ {:?}", from, to);
        let goal = canrun::unify(from.clone(), to.clone());
        self.goals.push(Box::new(goal));
    }

    fn restrict_field(&mut self, obj: &KrVal, field_name: &str, field: &KrVal) {
        //println!("restrict_field {:?}.{} -> {:?}", obj, field_name, field);
        let field_name = field_name.to_string();
        let field = field.clone();
        let goal = canrun::project::project_1(obj.clone(),
            move |obj_ty| {
                if let KrTerm::Atom(s) = &*obj_ty {
                    let struct_name = &s[7..];
                    USER_TYPES.with_borrow(|user_types| -> Box<dyn canrun::Goal> {
                        match user_types.get(struct_name).unwrap().get().get_field_ty(&field_name) {
                            None => Box::new(canrun::Fail),
                            Some(field_ty) =>
                                Box::new(canrun::unify(field.clone(), logic_ty(&field_ty))),
                        }
                    })
                } else {
                    Box::new(canrun::Fail)
                }
            });
        self.goals.push(Box::new(goal));
    }

    fn visit_stmt(&mut self, stmt: &mut Statement) {
        match stmt {
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
                let var_ty = canrun::Value::Var(self.new_tyvar());
                self.visit_expr(expr);
                let rhs_ty = logic_ty(&expr.ty);
                self.vars.insert_new(name.clone(), var_ty.clone());
                self.restrict_castable(&rhs_ty, &var_ty);
                // save the typevar assigned to this variable
                expr.set_extra(var_ty);
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
                };
            },
            ExprKind::Var(name) => {
                *expr_type = Ty::Var(self.get_symbol_type(name).into());
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
                let ret_type = canrun::Value::Var(self.new_tyvar());
                *expr_type = Ty::Var(ret_type.clone().into());
                for arg in args {
                    let arg_t = self.visit_and_add_implicit_cast(arg);
                    arg_tyvars.push(arg_t);
                }
                let expected_fty = KrTerm::make_fty(ret_type, arg_tyvars);
                // function types are not castable
                self.restrict_equal(&expected_fty, &logic_ty(&callee.ty));
            }
            ExprKind::New(ty, args) => {
                let obj_ty = ty.get_struct().get();
                if obj_ty.fields.len() != args.len() {
                    panic!("wrong number of arguments to constructor")
                }
                for i in 0..args.len() {
                    let arg_t = self.visit_and_add_implicit_cast(&mut args[i]);
                    self.restrict_equal(&arg_t, &logic_ty(&obj_ty.fields[i].1));
                }
                *expr_type = ty.clone();
            }
            ExprKind::Field(obj, field) => {
                self.visit_expr(obj);
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
    fn visit_and_add_implicit_cast(&mut self, e: &mut Expr) -> KrVal {
        self.visit_expr(e);
        let original_expr_type = logic_ty(&e.ty);
        let cast_var = canrun::Value::Var(self.new_tyvar());
        e.ty = Ty::Var(UnifTy(cast_var.clone()));
        self.restrict_castable(&original_expr_type, &cast_var);
        cast_var
    }

    fn new_tyvar(&mut self) -> canrun::LVar<KrTerm> {
        let v = canrun::LVar::new();
        self.tyvars.push(v.clone());
        v
    }
    
    /*fn get_resolved(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::TyVar(id) => self.solutions[id].clone(),
            _ => ty.clone()
        }
    }

    fn get_resolved_tt(&self, ty: &TTyt) -> Ty {
        match ty {
            canrun::Value::Resolved(t) => t.reify_in(
                &canrun::State::new().ready().unwrap()).unwrap(),
            canrun::Value::Var(v) =>
                self.get_resolved(&Ty::TyVar(lvar_get_usize(v)))
        }
    }*/

    fn get_resolved_kr(&self, ty: &KrVal) -> Ty {
        match ty {
            canrun::Value::Resolved(t) =>
                t.reify_in(&canrun::State::new().ready().unwrap()).unwrap(),
            canrun::Value::Var(v) => {
                self.solutions[&lvar_get_usize(v)].clone()
            }
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

    fn resolve_stmt(&mut self, stmt: &mut Statement) {
        match stmt {
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
                let var_ty= expr.get_extra::<KrVal>().unwrap().clone();
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
                }
            },
            ExprKind::Var(name) => {
                let var_type = self.get_resolved_kr(&self.get_symbol_type(name));
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
        let expected_type = self.get_resolved_t(expr_type);
        *expr_type = value_type;
        insert_cast(expr, expected_type);
    }
}

// this is horifically unsafe unfortunately we don't really have a choice
fn lvar_get_usize<T>(tv: &canrun::LVar<T>) -> usize {
    unsafe { *(tv as *const canrun::LVar<T> as *const usize) }
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