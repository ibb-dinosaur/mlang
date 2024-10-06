use std::collections::{BTreeMap, HashMap};

use inkwell::{attributes::{Attribute, AttributeLoc}, basic_block::BasicBlock, builder::Builder, context::Context, intrinsics::Intrinsic, llvm_sys::LLVMAttributeFunctionIndex, module::Module, types::{AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, IntType, PointerType, StructType, VoidType}, values::{AnyValue, AsValueRef, BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, GlobalValue, IntValue, PointerValue}, AddressSpace, IntPredicate};

use crate::ast::*;

pub struct Compiler<'a> {
    ctx: &'a Context,
    m: Module<'a>,
    b: Builder<'a>,
    tys: PrimTypes<'a>,
    builtins: Builtins<'a>,
    globals: HashMap<String, GlobalValue<'a>>,
    // all locals are `alloca`d
    locals: HashMap<String, PointerValue<'a>>,
    obj_type_tags: BTreeMap<Ty, GlobalValue<'a>>
}

pub struct PrimTypes<'a> {
    int: IntType<'a>,
    c_void: VoidType<'a>,
    any: StructType<'a>,
    ptr: PointerType<'a>,
    bool: IntType<'a>,
}

pub struct Builtins<'a> {
    type_cast_fail_fn: FunctionValue<'a>,
    cmp_any_fn: FunctionValue<'a>,
}

impl<'a> Compiler<'a> {
    pub fn new(ctx: &'a Context) -> Self {
        let m = ctx.create_module("main");
        let b = ctx.create_builder();
        // initialize basic types
        let int = ctx.i64_type();
        let c_void = ctx.void_type();
        let ptr = ctx.ptr_type(AddressSpace::default());
        let bool = ctx.custom_width_int_type(1);
        let any = ctx.struct_type(&[int.into(), int.into()], false);
        // initialize builtins
        let t1 = c_void.fn_type(&[int.into(), int.into(), int.into()], false);
        let type_cast_fail_fn = m.add_function("__tc_fail1", t1, None);
        type_cast_fail_fn.add_attribute(AttributeLoc::Function, ctx.create_enum_attribute(5, 0)); // cold
        type_cast_fail_fn.add_attribute(AttributeLoc::Function, ctx.create_enum_attribute(33, 0)); // noreturn
        type_cast_fail_fn.add_attribute(AttributeLoc::Function, ctx.create_enum_attribute(38, 0)); // nounwind
        let cmp_any_fn = m.add_function("__cmp_any", bool.fn_type(&[any.into(), any.into()], false), None);
        cmp_any_fn.add_attribute(AttributeLoc::Function, ctx.create_enum_attribute(38, 0)); // nounwind
        Self { ctx, m, b, tys: PrimTypes { int, c_void, any, ptr, bool }, builtins: Builtins { type_cast_fail_fn, cmp_any_fn }, globals: HashMap::new(), locals: HashMap::new(), obj_type_tags: BTreeMap::new() }
    }

    pub fn emit_program(&mut self, p: &Program) {
        // declare all functions
        for f in &p.functions {
            let argtys = f.params.iter().map(|(_, ty)| self.lower_ty(ty).into()).collect::<Vec<BasicMetadataTypeEnum<'_>>>();
            let fty = self.lower_ty(&f.return_type).fn_type(&argtys, false);
            let func = self.m.add_function(&f.name, fty, None);
            self.globals.insert(f.name.clone(), func.as_global_value());

            // generate type tag for function
            let type_tag_ptr = self.get_type_tag(&f.create_ftype());
            // we want the function pointer to be 16-byte aligned, so the prefix data must be 16 bytes
            let prefix_data = self.tys.int.const_array(&[self.tys.int.const_zero(), type_tag_ptr]);
            set_function_prefix_data(func, prefix_data);
        }
        // emit all functions
        for f in &p.functions {
            self.emit_function(f);
        }

        self.m.print_to_stderr();
        let _ = self.m.verify().inspect_err(|e| println!("LLVM Validation Error:\n{}", e.to_string()));
    }

    fn emit_function(&mut self, f: &Function) {
        let func = self.m.get_function(&f.name).unwrap();

        let entry_bb = self.ctx.append_basic_block(func, "entry");
        self.b.position_at_end(entry_bb);

        for (i, p_val) in func.get_param_iter().enumerate() {
            // all locals must be `alloca`d, so make space for the arguments and store them
            let place = self.b.build_alloca(p_val.get_type(), &f.params[i].0).unwrap();
            self.b.build_store(place, p_val).unwrap();
            self.locals.insert(f.params[i].0.clone(), place);
        }

        for stmt in &f.body {
            self.emit_statement(stmt);
        }

        if self.b.get_insert_block().unwrap().get_terminator().is_none() {
            // if the function doesn't end with a return statement, add a return void
            // a void value is represented as an undef i64
            self.b.build_return(Some(&self.tys.int.get_undef())).unwrap();
        }
        //func.verify(true);
    }

    fn emit_statement(&mut self, s: &Statement) {
        match s {
            Statement::ExprStmt(expr) => {
                self.emit_expr(expr);
            },
            Statement::Return(expr) => {
                let val = self.emit_expr(expr);
                self.b.build_return(Some(&val)).unwrap();
            },
            Statement::Let(name, expr) => {
                let val = self.emit_expr(expr);
                // allocate space
                let place = self.b.build_alloca(self.lower_ty(&expr.ty), name).unwrap();
                self.b.build_store(place, val).unwrap();
                self.locals.insert(name.clone(), place);
            },
            Statement::Assign(name, expr) => {
                let val = self.emit_expr(expr);
                let place = self.locals[name];
                self.b.build_store(place, val).unwrap();
            },
        }
    }

    fn emit_expr(&mut self, e: &Expr) -> BasicValueEnum<'a> {
        match &e.kind {
            ExprKind::IntLiteral(n) => {
                self.tys.int.const_int(*n as u64, false).into()
            },
            ExprKind::Var(name) => {
                match self.locals.get(name) {
                    Some(place) => { // locals are `alloca`d, load the value
                        let var_ty = self.lower_ty(&e.ty);
                        self.b.build_load(var_ty, *place, "").unwrap()
                    }
                    None => {
                        let global = self.globals.get(name).unwrap();
                        global.as_pointer_value().into()
                    }
                }
            },
            ExprKind::BinOp(op, lhs, rhs) => {
                if op.is_eq_comparison() {
                    let lhs_v = self.emit_expr(lhs);
                    let rhs_v = self.emit_expr(rhs);
                    let cmp = self.build_eq_comparison(&lhs.ty, lhs_v, rhs_v);
                    if *op == BinOp::CmpNe {
                        // not
                        self.b.build_int_compare(IntPredicate::EQ, cmp, self.tys.bool.const_zero(), "").unwrap()
                    } else {
                        cmp
                    }.into()
                } else {
                    let lhs = self.emit_expr(lhs).into_int_value();
                    let rhs = self.emit_expr(rhs).into_int_value();
                    match op {
                        BinOp::Add => self.b.build_int_add(lhs, rhs, "").unwrap().into(),
                        BinOp::Sub => self.b.build_int_sub(lhs, rhs, "").unwrap().into(),
                        BinOp::Mul => self.b.build_int_mul(lhs, rhs, "").unwrap().into(),
                        BinOp::CmpLt => self.b.build_int_compare(IntPredicate::SLT, lhs, rhs, "").unwrap().into(),
                        BinOp::CmpGt => self.b.build_int_compare(IntPredicate::SGT, lhs, rhs, "").unwrap().into(),
                        BinOp::CmpLe => self.b.build_int_compare(IntPredicate::SLE, lhs, rhs, "").unwrap().into(),
                        BinOp::CmpGe => self.b.build_int_compare(IntPredicate::SGE, lhs, rhs, "").unwrap().into(),
                        _ => unreachable!()
                    }
                }
            },
            ExprKind::TypeCast(type_cast_kind, expr) => {
                let val = self.emit_expr(expr);
                match type_cast_kind {
                    TypeCastKind::ToAny => {
                        let type_tag = any_tag_of_type(&expr.ty);
                        let payload = self.convert_val_to_any_payload(val, &expr.ty);
                        // the struct has to be a constant, so we use undef in the second field
                        // and then insert (at runtime) the actual value
                        let any_val = self.tys.any.const_named_struct(&[
                            self.tys.int.const_int(type_tag, false).into(),
                            self.tys.int.get_undef().into()
                        ]);
                        self.b.build_insert_value(any_val, payload, 1, "").unwrap().into_struct_value().into()
                    },
                    TypeCastKind::FromAnySimple => {
                        let any_val = val.into_struct_value();
                        assert!(any_val.get_type() == self.tys.any);
                        let fail_branch = self.new_bb("tcfail");
                        let success_branch = self.new_bb("");
                        let any_val_tag = self.b.build_extract_value(any_val, 0, "tag").unwrap().into_int_value();
                        let type_tag = self.tys.int.const_int(any_tag_of_type(&e.ty), false);
                        let any_val_payload = self.b.build_extract_value(any_val, 1, "").unwrap();
                        let cmp = self.b.build_int_compare(inkwell::IntPredicate::EQ, any_val_tag, type_tag, "").unwrap();
                        self.b.build_conditional_branch(cmp, success_branch, fail_branch).unwrap();
                        // fail branch
                        self.b.position_at_end(fail_branch);
                        self.build_typecast_fail(type_tag, any_val_tag, any_val_payload);
                        // success branch
                        self.b.position_at_end(success_branch);
                        self.convert_any_payload_to_type(any_val_payload.into_int_value(), &e.ty)
                    },
                    TypeCastKind::FromAnyToFunc => todo!()
                }
            },
            ExprKind::Call(callee_e, args_e) => {
                let callee = self.emit_expr(callee_e).into_pointer_value();
                let mut args: Vec<BasicMetadataValueEnum<'a>> = vec![];
                for arg_e in args_e { args.push(self.emit_expr(arg_e).into()); }
                if callee.as_any_value_enum().is_function_value() {
                    // direct call
                    let callee = callee.as_any_value_enum().into_function_value();
                    self.b.build_direct_call(callee, &args, "").unwrap()
                } else {
                    // indirect call
                    let arg_tys = args_e.iter().map(|e| self.lower_ty(&e.ty).into()).collect::<Vec<BasicMetadataTypeEnum<'_>>>();
                    let ret_ty = self.lower_ty(&e.ty);
                    let fty = ret_ty.fn_type(&arg_tys, false);
                    self.b.build_indirect_call(fty, callee, &args, "").unwrap()
                }.try_as_basic_value().unwrap_left()
            },
        }
    }

    fn new_bb(&self, name: &str) -> BasicBlock<'a> {
        self.ctx.append_basic_block(self.b.get_insert_block().unwrap().get_parent().unwrap(), name)
    }

    fn build_typecast_fail(&self, expected_tag: IntValue<'a>, actual_tag: IntValue<'a>, payload: BasicValueEnum<'a>) {
        /*let trap_intr = Intrinsic::find("llvm.trap").unwrap();
        let trap_fn = trap_intr.get_declaration(&self.m, &[]).unwrap();
        self.b.build_call(trap_fn, &[], "").unwrap();*/
        let fail_fn = self.builtins.type_cast_fail_fn;
        self.b.build_call(fail_fn, &[expected_tag.into(), actual_tag.into(), payload.into()], "").unwrap();
        self.b.build_unreachable().unwrap();
    }

    fn lower_ty(&self, ty: &Ty) -> BasicTypeEnum<'a> {
        match ty {
            Ty::Int => self.tys.int.into(),
            Ty::Void => self.tys.int.into(),
            Ty::Bool => self.tys.bool.into(),
            Ty::Any => self.tys.any.into(),
            Ty::Func(_, _) => self.tys.ptr.into(),
            Ty::Unk | Ty::TyVar(_) => unreachable!(),
        }
    }

    fn get_type_tag(&mut self, ty: &Ty) -> IntValue<'a> {
        match ty {
            Ty::Int => self.tys.int.const_int(1, false),
            Ty::Bool => self.tys.int.const_int(2, false),
            Ty::Void => self.tys.int.const_int(7, false),
            Ty::Any => self.tys.int.const_int(14, false),
            Ty::Func(_, _) => {
                if let Some(g) = self.obj_type_tags.get(ty) {
                    g.as_pointer_value().const_to_int(self.tys.int)
                } else {
                    self.make_func_type_tag(ty)
                }
            },
            Ty::Unk | Ty::TyVar(_) => unreachable!()            
        }
    }

    fn make_func_type_tag(&mut self, f: &Ty) -> IntValue<'a> {
        let Ty::Func(ret, params) = f else { panic!(); };
        let size = params.len() as u32 + 3;
        let arr_ty = self.tys.int.array_type(size);
        let g = self.m.add_global(arr_ty, None, "ftag");
        self.obj_type_tags.insert(f.clone(), g);
        let mut func_obj = vec![self.tys.int.const_int(1, false)];
        func_obj.push(self.get_type_tag(ret));
        for p in params {
            func_obj.push(self.get_type_tag(p));
        }
        func_obj.push(self.tys.int.const_zero()); // terminator
        g.set_initializer(&self.tys.int.const_array(&func_obj));
        g.set_unnamed_addr(true); // allow LLVM to merge identical globals
        g.as_pointer_value().const_to_int(self.tys.int)
    }

    /// Convert a value to an i64 payload for the `any` type
    fn convert_val_to_any_payload(&mut self, val: BasicValueEnum<'a>, val_ty: &Ty) -> IntValue<'a> {
        match val_ty {
            Ty::Int => val.into_int_value(), // already i64
            Ty::Void => val.into_int_value(), // already i64
            Ty::Bool => // i1 -> i64
                self.b.build_int_z_extend(val.into_int_value(), self.tys.int, "").unwrap(),
            Ty::Func(_, _) => // ptr -> i64
                self.b.build_ptr_to_int(val.into_pointer_value(), self.tys.int, "").unwrap(),
            Ty::Any | Ty::Unk | Ty::TyVar(_) => unreachable!(),
        }
    }

    /// Convert a value to an i64 payload for the `any` type
    fn convert_any_payload_to_type(&mut self, payload: IntValue<'a>, val_ty: &Ty) -> BasicValueEnum<'a> {
        match val_ty {
            Ty::Int => payload.into(),
            Ty::Void => self.tys.int.get_undef().into(), // void values don't carry any information
            Ty::Bool => // i64 -> i1
                self.b.build_int_truncate(payload, self.tys.bool, "").unwrap().into(),
            Ty::Func(_, _) => // i64 -> ptr
                self.b.build_int_to_ptr(payload, self.tys.ptr, "").unwrap().into(),
            Ty::Any | Ty::Unk | Ty::TyVar(_) => unreachable!(),
        }
    }

    fn build_eq_comparison(&mut self, ty: &Ty, lhs: BasicValueEnum<'a>, rhs: BasicValueEnum<'a>) -> IntValue<'a> {
        match ty {
            Ty::Int => // just int comparison
                self.b.build_int_compare(IntPredicate::EQ, lhs.into_int_value(), rhs.into_int_value(), "iseq").unwrap(),
            Ty::Void => // void values are always equal
                self.tys.bool.const_all_ones(),
            Ty::Bool => // also just int comparison
                self.b.build_int_compare(IntPredicate::EQ, lhs.into_int_value(), rhs.into_int_value(), "iseq").unwrap(),
            Ty::Func(_, _) => // functions are equal if their pointers are equal
                self.b.build_int_compare(IntPredicate::EQ, lhs.into_pointer_value(), rhs.into_pointer_value(), "iseq").unwrap(),
            Ty::Any => // call a runtime function
                self.b.build_call(self.builtins.cmp_any_fn, &[lhs.into(), rhs.into()], "iseq").unwrap().try_as_basic_value().unwrap_left().into_int_value(),
            Ty::Unk | Ty::TyVar(_) => unreachable!(),
        }
    }
}

fn any_tag_of_type(ty: &Ty) -> u64 {
    match ty {
        Ty::Int => 1,
        Ty::Void => 7,
        Ty::Bool => 2,
        // assume COMFUNC format
        Ty::Func(_,_) => 15,
        _ => unreachable!()
    }
}

fn set_function_prefix_data<'a>(f: FunctionValue<'a>, data: impl BasicValue<'a>) {
    let data = data.as_value_ref();
    let fptr = f.as_value_ref();
    unsafe { crate::llvm_extras::LLVMSetPrefixData(fptr, data); }
}