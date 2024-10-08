use std::collections::BTreeMap;

use crate::ast::Ty;

pub struct InferenceContext {
    tyvar_counter: usize,
    pairs: Vec<InferencePair>,
    /// Solutions for type variables, may not be final
    partial_solutions: BTreeMap<Ty, Ty>,
    /// Definite solutions for type variables
    full_solutions: BTreeMap<Ty, Ty>,
}

enum InferencePair {
    /// Type 1 must be assignable to Type 2
    Assign(Ty, Ty),
    /// Type 1 must be equal to Type 2
    Equal(Ty, Ty),
    /// Type 1 must have a field named String of type Type 2
    Field(Ty, String, Ty),
}

impl InferenceContext {
    pub fn new() -> Self {
        InferenceContext {
            tyvar_counter: 1, pairs: Vec::new(),
            partial_solutions: BTreeMap::new(),
            full_solutions: BTreeMap::new(),
        }
    }

    pub fn new_tyvar(&mut self) -> Ty {
        let tyvar = Ty::TyVar(self.tyvar_counter);
        self.tyvar_counter += 1;
        tyvar
    }

    pub fn add_assignable(&mut self, src: &Ty, dst: &Ty) {
        self.pairs.push(InferencePair::Assign(src.clone(), dst.clone()));
    }

    pub fn add_equal(&mut self, src: &Ty, dst: &Ty) {
        self.pairs.push(InferencePair::Equal(src.clone(), dst.clone()));
    }

    pub fn add_field(&mut self, src: &Ty, field: &str, dst: &Ty) {
        self.pairs.push(InferencePair::Field(src.clone(), field.to_string(), dst.clone()));
    }

    pub fn solve_all(&mut self) {
        while !self.pairs.is_empty() {
            println!("Next round. {} pairs left.", self.pairs.len());
            self.dump();
            let pairs = std::mem::take(&mut self.pairs);
            for pair in pairs {
                self.solve_pair(&pair);
            }
        }
        // look for unsolved type variables
        for i in 0..self.tyvar_counter {
            let key = Ty::TyVar(i);
            if !self.partial_solutions.contains_key(&key) {
                self.partial_solutions.insert(key, Ty::Any);
            }
        }
        // after solving is done, finish up the solutions
        for (tv, v) in self.partial_solutions.iter() {
            let v = self.get_solved(v.clone());
            self.full_solutions.insert(tv.clone(), v);
        }
        self.partial_solutions.clear();
    }

    fn solve_pair(&mut self, p: &InferencePair) {
        match p {
            InferencePair::Assign(ty_from, ty_to) => {
                let ty_from = self.get_solved(ty_from.clone());
                let ty_to = self.get_solved(ty_to.clone());

                // TODO: Implement properly
                if ty_to == Ty::Any || ty_from == Ty::Any { // any can be cast arbitrarily
                    return
                }
                if let (Ty::Func(r1, p1), Ty::Func(r2, p2)) = (&ty_from, &ty_to) {
                    for (t1, t2) in p1.iter().zip(p2) {
                        self.add_assignable(t1, t2);
                    }
                    self.add_assignable(r1, r2);
                    return
                }
                if ty_from.is_var() || ty_to.is_var() {
                    let (tvar, not_var) = if ty_from.is_var() { (ty_from, ty_to) } else { (ty_to, ty_from) };
                    self.add_solution(tvar.clone(), not_var.clone());
                } else {
                    self.add_equal(&ty_from, &ty_to);
                }
            },
            InferencePair::Equal(ty1, ty2) => {
                let ty1 = self.get_solved(ty1.clone());
                let ty2 = self.get_solved(ty2.clone());

                if let (Ty::Func(r1, p1), Ty::Func(r2, p2)) = (&ty1, &ty2) {
                    for (t1, t2) in p1.iter().zip(p2) {
                        self.add_equal(t1, t2);
                    }
                    self.add_equal(r1, r2);
                    return
                }
                if !ty1.is_var() && !ty2.is_var() {
                    if ty1 != ty2 {
                        panic!("Type mismatch: {} != {}", ty1, ty2);
                    } else { return } // solved
                }
                let (tvar, not_var) = if ty1.is_var() { (ty1, ty2) } else { (ty2, ty1) };
                self.add_solution(tvar.clone(), not_var.clone());
            },
            InferencePair::Field(obj_ty, field_name, val_ty) => {
                let obj_ty = self.get_solved(obj_ty.clone());
                let val_ty = self.get_solved(val_ty.clone());

                if obj_ty.is_var() {
                    // can't solve yet
                    self.add_field(&obj_ty, field_name, &val_ty);
                    return
                }

                if let Ty::UserTy(td) = obj_ty {
                    if let Some(field_ty) = td.get().get_field_ty(field_name) {
                        self.add_equal(&field_ty, &val_ty);
                    } else {
                        panic!("Field {} not found in struct", field_name);
                    }
                } else {
                    panic!("Field access on non-struct type");
                }
            },
        }
    }

    fn add_solution(&mut self, tvar: Ty, mut ty: Ty) {
        assert!(tvar.is_var());
        if ty.is_var() {
            ty = self.get_solved(ty);
        }
        match self.partial_solutions.get(&tvar) {
            None => {
                self.partial_solutions.insert(tvar, ty);
            }
            Some(prev) => {
                let prev = self.get_solved(prev.clone());
                // temporary solution, if prev isn't a definite type, "return" it to the unifier
                if prev.is_var() {
                    self.add_assignable(&prev, &tvar);
                    return
                }
                let ty = most_general_type(&prev, ty);
                self.partial_solutions.insert(tvar, ty);
            }
        }
    }

    fn get_solved(&self, mut tvar: Ty) -> Ty {
        if let Ty::Func(ret, params) = &tvar {
            let ret = self.get_solved(*ret.clone());
            let params = params.iter().map(|p| self.get_solved(p.clone())).collect();
            return Ty::Func(Box::new(ret), params);
        }
        loop {
            if !tvar.is_var() {
                return tvar;
            }
            if let Some(v) = self.partial_solutions.get(&tvar) {
                tvar = v.clone();
            } else {
                return tvar;
            }
        }
    }

    pub fn get_resolved(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::TyVar(_) => self.full_solutions.get(ty).unwrap().clone(),
            Ty::Func(ret, params) => {
                let params_resolved = params.iter().map(|p| self.get_resolved(p)).collect();
                Ty::Func(Box::new(self.get_resolved(ret)), params_resolved)
            }
            _ => ty.clone(),
        }
    }
    
    pub fn dump(&self) {
        for pair in &self.pairs {
            match pair {
                InferencePair::Assign(src, dst) => {
                    println!("{} ~> {}", src, dst);
                }
                InferencePair::Equal(src, dst) => {
                    println!("{} ~ {}", src, dst);
                }
                InferencePair::Field(src, field, dst) => {
                    println!("{}::{} ~ {}", src, field, dst);
                }
            }
        }
        for (k, v) in &self.partial_solutions {
            println!("{} ?= {}", k, v);
        }
        for (k, v) in &self.full_solutions {
            println!("{} = {}", k, v);
        }
    }
}

fn most_general_type(a: &Ty, b: Ty) -> Ty {
    assert!(!a.is_var() && !b.is_var(), "a = {}, b = {}", a, b);
    if a == &b {
        b
    } else {
        Ty::Any
    }
}