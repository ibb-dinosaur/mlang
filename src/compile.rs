use std::{collections::{BTreeMap, HashMap}, hash::Hasher};

use inkwell::{attributes::{Attribute, AttributeLoc}, basic_block::BasicBlock, builder::Builder, context::Context, module::Module, passes::{PassBuilderOptions, PassManager}, targets::{InitializationConfig, Target, TargetTriple}, types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, IntType, PointerType, StructType, VoidType}, values::{AnyValue, AsValueRef, BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, GlobalValue, IntValue, PointerValue}, AddressSpace, IntPredicate, OptimizationLevel};

use crate::{ast::*, util::ScopedMap};

static CORE_BC: &[u8] = include_bytes!("core.bc");

pub struct Compiler<'a> {
    ctx: &'a Context,
    m: Module<'a>,
    b: Builder<'a>,
    tys: PrimTypes<'a>,
    globals: HashMap<String, GlobalValue<'a>>,
    // all locals are `alloca`d
    locals: ScopedMap<String, PointerValue<'a>>,
    obj_type_tags: BTreeMap<Ty, GlobalValue<'a>>,
    user_type_structs: BTreeMap<TypeDef, StructType<'a>>
}

pub struct PrimTypes<'a> {
    int: IntType<'a>,
    c_void: VoidType<'a>,
    any: StructType<'a>,
    ptr: PointerType<'a>,
    bool: IntType<'a>,
    int32: IntType<'a>,
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
        let int32 = ctx.i32_type();
        Self { ctx, m, b, tys: PrimTypes { int, c_void, any, ptr, bool, int32 }, globals: HashMap::new(), locals: ScopedMap::new(false), obj_type_tags: BTreeMap::new(), user_type_structs: BTreeMap::new() }
    }

    fn declare_builtins(&mut self) {
        let t1: inkwell::types::FunctionType<'_> = self.tys.c_void.fn_type(&[self.tys.int.into(), self.tys.int.into(), self.tys.int.into()], false);
        let type_cast_fail_fn = self.m.add_function("__tc_fail1", t1, None);
        type_cast_fail_fn.add_attribute(AttributeLoc::Function, self.ctx.create_enum_attribute(5, 0)); // cold
        type_cast_fail_fn.add_attribute(AttributeLoc::Function, self.ctx.create_enum_attribute(33, 0)); // noreturn

        let _cmp_any_fn = self.m.add_function("__cmp_any", 
            self.tys.bool.fn_type(&[self.tys.any.into(), self.tys.any.into()], false), None);
    
        let alloc_fn = self.m.add_function("__allocm", 
            self.tys.ptr.fn_type(&[self.tys.int.into()], false), None);
        alloc_fn.add_attribute(AttributeLoc::Function, self.ctx.create_string_attribute("allockind", "alloc"));
        alloc_fn.add_attribute(AttributeLoc::Function, self.ctx.create_string_attribute("alloc-family", "__allocm"));
        alloc_fn.add_attribute(AttributeLoc::Function, self.ctx.create_enum_attribute(
            Attribute::get_named_enum_kind_id("allocsize"), 0));
        alloc_fn.add_attribute(AttributeLoc::Return, self.ctx.create_enum_attribute(
            Attribute::get_named_enum_kind_id("nonnull"), 0));
        alloc_fn.add_attribute(AttributeLoc::Return, self.ctx.create_enum_attribute(
            Attribute::get_named_enum_kind_id("noundef"), 0));
    
        let free_fn = self.m.add_function("__freem",
            self.tys.c_void.fn_type(&[self.tys.ptr.into(), self.tys.int.into()], false), None);
        free_fn.add_attribute(AttributeLoc::Function, self.ctx.create_string_attribute("allockind", "free"));
        free_fn.add_attribute(AttributeLoc::Function, self.ctx.create_string_attribute("alloc-family", "__allocm"));
    }

    fn load_core_ll(&mut self) {
        let buf = inkwell::memory_buffer::MemoryBuffer::create_from_memory_range(CORE_BC, "core.bc");
        let core_mod = self.ctx.create_module_from_ir(buf).unwrap();
        self.m.link_in_module(core_mod).unwrap();
        //self.m.print_to_stderr();
    }

    pub fn emit_program(mut self, p: &Program) -> inkwell::module::Module<'a> {
        self.declare_builtins();
        self.load_core_ll();
        // declare all user types
        for td in &p.user_types {
            let t = td.get();
            let mut fields = vec![];
            for (_, field_ty) in &t.fields {
                fields.push(self.lower_ty(field_ty));
            }
            let s = self.ctx.struct_type(&fields, false);
            self.user_type_structs.insert(td.clone(), s);
            // also generate type tag
            self.make_usertype_type_tag(td);
            // and constructor
            self.emit_default_constructor(td);
            self.emit_destructor(td);
        }
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
            self.locals.reset();
        }

        let _ = self.m.verify().inspect_err(|e| println!("LLVM Validation Error:\n{}", e.to_string()));
    
        if crate::OPTIONS.get().unwrap().opt {
            Target::initialize_native(&InitializationConfig::default()).unwrap();

            let triple = TargetTriple::create("x86_64-unknown-linux-gnu");
            let target = Target::from_triple(&triple).unwrap();

            let machine = target.create_target_machine(&triple,
                "generic", "",
                OptimizationLevel::Less, // -O1
                inkwell::targets::RelocMode::DynamicNoPic,
                inkwell::targets::CodeModel::Small).unwrap();
            self.m.run_passes(
                "default<O1>", &machine,
                PassBuilderOptions::create()).unwrap();
        }
        if crate::OPTIONS.get().unwrap().print_llvm {
            self.m.print_to_stderr();
        }
        self.m
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
            // if the current block doesn't end with return,
            // it must be unreachable
            self.b.build_unreachable().unwrap();
        }
    }

    fn emit_statement(&mut self, s: &Statement) {
        let mut drops = vec![];
        // return after drops
        let mut late_return = None;
        match s {
            Statement::ExprStmt(expr) => {
                self.emit_expr(expr, &mut drops);
            },
            Statement::Return(expr) => {
                let val = self.emit_expr(expr, &mut drops);
                self.b.build_return(Some(&val)).unwrap();
            },
            Statement::Let(name, expr) => {
                let val = self.emit_expr(expr, &mut drops);
                // allocate space
                let place = self.b.build_alloca(self.lower_ty(&expr.ty), name).unwrap();
                self.b.build_store(place, val).unwrap();
                self.locals.insert(name.clone(), place);
            },
            Statement::Assign(lhs, expr) => {
                let val = self.emit_expr(expr, &mut drops);
                let place = self.emit_lvalue(lhs, &mut drops);
                self.b.build_store(place, val).unwrap();
            },
            Statement::If(cond, then_, else_) => {
                let cond = self.emit_expr(cond, &mut drops);
                let then_bb = self.new_bb("then");
                let else_bb = self.new_bb("else");
                let join_bb = self.new_bb("");
                self.b.build_conditional_branch(cond.into_int_value(), then_bb, else_bb).unwrap();
                // then branch
                self.b.position_at_end(then_bb);
                self.locals.enter_new_scope();
                for stmt in then_ {
                    self.emit_statement(stmt);
                }
                self.locals.exit_scope();
                if self.b.get_insert_block().unwrap().get_terminator().is_none() {
                    self.b.build_unconditional_branch(join_bb).unwrap();
                }
                // else branch
                self.b.position_at_end(else_bb);
                self.locals.enter_new_scope();
                for stmt in else_ {
                    self.emit_statement(stmt);
                }
                self.locals.exit_scope();
                if self.b.get_insert_block().unwrap().get_terminator().is_none() {
                    self.b.build_unconditional_branch(join_bb).unwrap();
                }
                self.b.position_at_end(join_bb);
            },
            Statement::RcDropsReturn { drops: drop_exprs, returns } => {
                for e in drop_exprs {
                    let val = self.emit_expr(e, &mut drops);
                    drops.push((val, e.ty.clone()));
                }
                if let Some(expr) = returns {
                    let val = self.emit_expr(expr, &mut drops);
                    late_return = Some(val);
                }
            },
        }
        // drop all values that are no longer needed
        for (val, ty) in drops {
            self.build_drop(val, &ty);
        }
        if let Some(val) = late_return {
            self.b.build_return(Some(&val)).unwrap();
        }
    }

    /// `drops` is a list of values that will be dropped at the end of current statement
    fn emit_expr(&mut self, e: &Expr, drops: &mut Vec<(BasicValueEnum<'a>,Ty)>) -> BasicValueEnum<'a> {
        match &e.kind {
            ExprKind::Literal(Literal::Int(n)) => {
                self.tys.int.const_int(*n as u64, false).into()
            },
            ExprKind::Literal(Literal::Bool(b)) => {
                self.tys.bool.const_int(*b as u64, false).into()
            },
            ExprKind::Literal(Literal::Void) => {
                self.tys.int.get_undef().into()
            },
            ExprKind::Literal(Literal::Null) => {
                match &e.ty {
                    Ty::Option(x) => match &**x {
                        Ty::UserTy(_) => {
                            // null of a pointer type is just a null pointer
                            self.tys.ptr.const_null().into()
                        },
                        Ty::Any => {
                            // null : any = { 3, 0 }
                            self.tys.any.const_named_struct(&[
                                self.tys.int.const_int(3, false).into(),
                                self.tys.int.const_zero().into()
                            ]).into()
                        }
                        _ => todo!(),
                    }
                    _ => unreachable!()
                }
            }
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
                    let lhs_v = self.emit_expr(lhs, drops);
                    let rhs_v = self.emit_expr(rhs, drops);
                    let cmp = self.build_eq_comparison(&lhs.ty, lhs_v, rhs_v);
                    if *op == BinOp::CmpNe {
                        // not
                        self.b.build_int_compare(IntPredicate::EQ, cmp, self.tys.bool.const_zero(), "").unwrap()
                    } else {
                        cmp
                    }.into()
                } else {
                    let lhs = self.emit_expr(lhs, drops).into_int_value();
                    let rhs = self.emit_expr(rhs, drops).into_int_value();
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
                let val = self.emit_expr(expr, drops);
                match type_cast_kind {
                    TypeCastKind::ToAny => {
                        // special case: any? -> any is a no-op
                        if expr.ty == Ty::Option(Box::new(Ty::Any)) {
                            return val;
                        }
                        let type_tag = any_tag_of_type(&expr.ty);
                        let payload = self.convert_val_to_any_payload(val, &expr.ty);
                        self.b.build_direct_call(
                            self.m.get_function(".toany_simple").unwrap(),
                            &[self.tys.int.const_int(type_tag, false).into(), payload.into()], 
                            "").unwrap().try_as_basic_value().unwrap_left()
                    },
                    TypeCastKind::FromAnySimple => {
                        let any_val = val.into_struct_value();
                        assert!(any_val.get_type() == self.tys.any);
                        let type_tag = self.tys.int.const_int(any_tag_of_type(&e.ty), false);
                        let payload = self.b.build_direct_call(
                            self.m.get_function(".fromany_simple").unwrap(),
                            &[type_tag.into(), any_val.into()],
                            "").unwrap().try_as_basic_value().unwrap_left();
                        self.convert_any_payload_to_type(payload.into_int_value(), &e.ty)
                    },
                    TypeCastKind::FromAnyToFunc => todo!(),
                    TypeCastKind::FromNullableToAny => {
                        let type_tag = any_tag_of_type(&expr.ty);
                        let payload = self.convert_val_to_any_payload(val, &expr.ty);
                        self.b.build_direct_call(
                            self.m.get_function(".toany_nullable").unwrap(),
                            &[self.tys.int.const_int(type_tag, false).into(), payload.into()], 
                            "").unwrap().try_as_basic_value().unwrap_left()
                    },
                    TypeCastKind::FromAnyToNullable => {
                        let any_val = val.into_struct_value();
                        assert!(any_val.get_type() == self.tys.any);
                        let type_tag = self.tys.int.const_int(any_tag_of_type(&e.ty), false);
                        let payload = self.b.build_direct_call(
                            self.m.get_function(".fromany_nullable").unwrap(),
                            &[type_tag.into(), any_val.into()],
                            "").unwrap().try_as_basic_value().unwrap_left();
                        self.convert_any_payload_to_type(payload.into_int_value(), &e.ty)
                    },
                    TypeCastKind::WrapOption => {
                        // t -> option t
                        // if t is a reference, option t is just a nullable pointer (conversion is a no-op)
                        if expr.ty.is_managed() {
                            val
                        } else { todo!() }
                    },
                    TypeCastKind::UnwrapOption => {
                        if e.ty.is_managed() {
                            let type_tag = self.get_type_tag(&e.ty).into();
                            self.b.build_direct_call(
                                self.m.get_function(".unwrap_nullable").unwrap(), 
                                &[val.into(), type_tag], ""
                            ).unwrap().try_as_basic_value().unwrap_left()
                        } else { todo!() }
                    },
                    TypeCastKind::OptionToBool => {
                        if expr.ty.is_managed() {
                            let cmp = self.b.build_int_compare(IntPredicate::EQ, 
                                val.into_pointer_value(), self.tys.ptr.const_null(), "").unwrap();
                            self.b.build_select(cmp, 
                                self.tys.bool.const_zero(),
                                self.tys.bool.const_int(1, false), "").unwrap()
                        } else { todo!() }
                    }
                }
            },
            ExprKind::Call(callee_e, args_e) => {
                let callee = self.emit_expr(callee_e, drops).into_pointer_value();
                let mut args: Vec<BasicMetadataValueEnum<'a>> = vec![];
                for arg_e in args_e { args.push(self.emit_expr(arg_e, drops).into()); }
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
            ExprKind::New(ty, args) => {
                let mut args_v = Vec::<BasicMetadataValueEnum<'_>>::new();
                for arg in args {
                    args_v.push(self.emit_expr(arg, drops).into());
                }
                let constructor = self.m.get_function(&format!("{}.ctor", ty.get_struct().get().name)).unwrap();
                self.b.build_call(constructor, &args_v, "").unwrap().try_as_basic_value().unwrap_left()
            }
            ExprKind::Field(_, _) => {
                let field_ptr = self.emit_lvalue(e, drops);
                self.b.build_load(self.lower_ty(&e.ty), field_ptr, "").unwrap()
            }
            ExprKind::RcDup(expr) => {
                let val = self.emit_expr(expr, drops);
                self.build_dup(val, &expr.ty);
                val
            },
            ExprKind::RcDrop(expr) => {
                let val = self.emit_expr(expr, drops);
                drops.push((val, expr.ty.clone()));
                val
            },
        }
    }

    fn emit_lvalue(&mut self, e: &Expr, drops: &mut Vec<(BasicValueEnum<'a>,Ty)>) -> PointerValue<'a> {
        match &e.kind {
            ExprKind::Var(name) => {
                match self.locals.get(name) {
                    Some(place) => *place,
                    None => panic!("can't assign to globals")
                }
            }
            ExprKind::Field(obj, field) => {
                let obj_v = self.emit_expr(obj, drops).into_pointer_value();
                let struct_ty = self.user_type_structs[obj.ty.get_struct()];
                let field_n = obj.ty.get_struct().get().get_field_idx(field).unwrap();
                self.b.build_struct_gep(struct_ty, obj_v, field_n as _, "").unwrap()
            }
            ExprKind::RcDrop(expr) => {
                let val = self.emit_lvalue(expr, drops);
                // lvalue is a pointer to the value, so we have to load it
                let val_loaded = self.b.build_load(self.lower_ty(&expr.ty), val, "").unwrap();
                drops.push((val_loaded, expr.ty.clone()));
                val
            }
            _ => unreachable!()
        }
    }

    fn new_bb(&self, name: &str) -> BasicBlock<'a> {
        self.ctx.append_basic_block(self.b.get_insert_block().unwrap().get_parent().unwrap(), name)
    }

    fn lower_ty(&self, ty: &Ty) -> BasicTypeEnum<'a> {
        match ty {
            Ty::Int => self.tys.int.into(),
            Ty::Void => self.tys.int.into(),
            Ty::Bool => self.tys.bool.into(),
            Ty::Any => self.tys.any.into(),
            Ty::Func(_, _) => self.tys.ptr.into(),
            Ty::UserTy(_) => self.tys.ptr.into(),
            Ty::Option(inner) => {
                if matches!(&**inner, Ty::UserTy(_)) {
                    self.tys.ptr.into()
                } else { todo!() }
            },
            Ty::Unk | Ty::Var(_) | Ty::Named(_) => unreachable!(),
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
            Ty::UserTy(_) =>
                self.obj_type_tags.get(ty).unwrap().as_pointer_value().const_to_int(self.tys.int),
            Ty::Option(_) => {
                if let Some(g) = self.obj_type_tags.get(ty) {
                    g.as_pointer_value().const_to_int(self.tys.int)
                } else {
                    self.make_option_type_tag(ty)
                }
            },
            Ty::Unk | Ty::Var(_) | Ty::Named(_) => unreachable!()            
        }
    }

    /// See [`crate::rt::TypeDescObj`] and [`crate::rt::FuncDesc`]
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
        g.set_alignment(8);
        g.as_pointer_value().const_to_int(self.tys.int)
    }

    /// See [`crate::rt::TypeDescObj`] and [`crate::rt::StructDesc`]
    fn make_usertype_type_tag(&mut self, td: &TypeDef) -> IntValue<'a> {
        let t = td.get();
        let size = t.fields.len() as u32 + 3;
        let arr_ty = self.tys.int.array_type(size);
        let g = self.m.add_global(arr_ty, None, format!("objtag.{}", t.name).as_str());
        debug_assert!(self.obj_type_tags.insert(Ty::UserTy(td.clone()), g).is_none());
        let mut obj = vec![self.tys.int.const_int(2, false)];
        obj.push(self.tys.int.const_int(name_hash(&t.name), false));
        for field in &t.fields {
            obj.push(self.get_type_tag(&field.1));
        }
        obj.push(self.tys.int.const_zero()); // terminator
        g.set_initializer(&self.tys.int.const_array(&obj));
        g.set_alignment(8);
        g.as_pointer_value().const_to_int(self.tys.int)
    }

    /// See [`crate::rt::TypeDescObj`] and [`crate::rt::OptionDesc`]
    fn make_option_type_tag(&mut self, t: &Ty) -> IntValue<'a> {
        let inner = match t {
            Ty::Option(x) => &**x,
            _ => panic!()
        };
        let arr_ty = self.tys.int.array_type(2);
        let g = self.m.add_global(arr_ty, None, "opttag");
        let obj = vec![
            self.tys.int.const_int(4, false),
            self.get_type_tag(inner)
        ];
        self.obj_type_tags.insert(t.clone(), g);
        g.set_initializer(&self.tys.int.const_array(&obj));
        g.set_unnamed_addr(true);
        g.set_alignment(8);
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
            Ty::UserTy(_) => todo!(),
            Ty::Option(_) => todo!(),
            Ty::Any | Ty::Unk | Ty::Var(_) | Ty::Named(_) => unreachable!(),
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
            Ty::UserTy(_) => todo!(),
            Ty::Option(_) => todo!(),
            Ty::Any | Ty::Unk | Ty::Var(_) | Ty::Named(_) => unreachable!(),
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
                self.b.build_call(self.m.get_function("__cmp_any").unwrap(), 
                    &[lhs.into(), rhs.into()], "iseq").unwrap().try_as_basic_value().unwrap_left().into_int_value(),
            Ty::UserTy(_) => todo!(),
            Ty::Option(_) => todo!(),
            Ty::Unk | Ty::Var(_) | Ty::Named(_) => unreachable!(),
        }
    }

    fn emit_default_constructor(&mut self, td: &TypeDef) {
        let t = td.get();
        let struct_ty = self.user_type_structs.get(td).unwrap();
        let argtys: Vec<_> = t.fields.iter().map(|x| self.lower_ty(&x.1).into()).collect();
        let fty = self.tys.ptr.fn_type(&argtys, false);
        let f = self.m.add_function(&format!("{}.ctor", t.name), fty, None);
        let entry_bb = self.ctx.append_basic_block(f, "entry");
        self.b.position_at_end(entry_bb);
        let alloc_size = struct_ty.size_of().unwrap();
        let obj = self.b.build_call(self.m.get_function("__allocm").unwrap(),
            &[alloc_size.into()], "obj").unwrap().try_as_basic_value().unwrap_left().into_pointer_value();
        for i in 0..t.fields.len() {
            let field = self.b.build_struct_gep(*struct_ty, obj, i as u32, "").unwrap();
            let arg = f.get_nth_param(i as u32).unwrap();
            self.b.build_store(field, arg).unwrap();
        }
        self.b.build_return(Some(&obj)).unwrap();
    }

    fn emit_destructor(&mut self, td: &TypeDef) {
        let t = td.get();
        let struct_ty = *self.user_type_structs.get(td).unwrap();
        let fty = self.tys.c_void.fn_type(&[self.tys.ptr.into()], false);
        let f = self.m.add_function(&format!("{}.dtor", t.name), fty, None);
        let entry_bb = self.ctx.append_basic_block(f, "entry");
        self.b.position_at_end(entry_bb);
        let alloc_size = struct_ty.size_of().unwrap();
        let obj = f.get_first_param().unwrap().into_pointer_value();
        // drop all fields
        for i in 0..t.fields.len() {
            let field_ty = &t.fields[i].1;
            if !field_ty.is_managed() { continue }
            let field = self.b.build_struct_gep(struct_ty, obj, i as u32, "").unwrap();
            let val = self.b.build_load(self.lower_ty(field_ty), field, "").unwrap();
            self.build_drop(val, field_ty);
        }
        // deallocate
        self.b.build_call(self.m.get_function("__freem").unwrap(),
            &[obj.into(), alloc_size.into()], "").unwrap();
        self.b.build_return(None).unwrap();
    }

    fn build_dup(&mut self, v: BasicValueEnum<'a>, ty: &Ty) {
        if !ty.is_managed() { return }
        if let Ty::UserTy(_) = ty {
            // LLVM code as described in [`rt::__rcdup`]
            let refcount_ptr = unsafe { self.b.build_in_bounds_gep(self.tys.int32, v.into_pointer_value(), &[self.tys.int.const_int(-1isize as _, true)], "").unwrap() };
            let refcount = self.b.build_load(self.tys.int32, refcount_ptr, "").unwrap();
            let new_refcount = self.b.build_int_add(refcount.into_int_value(), self.tys.int32.const_int(1, false), "").unwrap();
            self.b.build_store(refcount_ptr, new_refcount).unwrap();
        } else if ty == &Ty::Any {
            todo!()
        } else if let Ty::Option(inner) = ty {
            if let Ty::UserTy(_) = &**inner {
                // option of a reference type,
                // if the value is null, do nothing, otherwise dup it ordinarily
                let cmp = self.b.build_int_compare(IntPredicate::EQ, v.into_pointer_value(), self.tys.ptr.const_null(), "").unwrap();
                let dup_bb = self.new_bb("");
                let continue_bb = self.new_bb("");
                self.b.build_conditional_branch(cmp, continue_bb, dup_bb).unwrap();
                self.b.position_at_end(dup_bb);
                self.build_dup(v, inner);
                self.b.build_unconditional_branch(continue_bb).unwrap();
                self.b.position_at_end(continue_bb);
            } else { todo!() }
        } else { unreachable!() }
    }

    fn build_drop(&mut self, v: BasicValueEnum<'a>, ty: &Ty) {
        if !ty.is_managed() { return }
        if let Ty::UserTy(td) = ty {
            let refcount_ptr = unsafe { self.b.build_in_bounds_gep(self.tys.int32, v.into_pointer_value(), &[self.tys.int.const_int(-1isize as _, true)], "").unwrap() };
            let refcount = self.b.build_load(self.tys.int32, refcount_ptr, "").unwrap();
            let new_refcount = self.b.build_int_add(refcount.into_int_value(), self.tys.int32.const_int(-1isize as _, true), "").unwrap();
            self.b.build_store(refcount_ptr, new_refcount).unwrap();
            let cmp = self.b.build_int_compare(IntPredicate::EQ, new_refcount, self.tys.int32.const_zero(), "").unwrap();
            let dtor_call_bb = self.new_bb("dtorcall");
            let continue_bb = self.new_bb("");
            self.b.build_conditional_branch(cmp, dtor_call_bb, continue_bb).unwrap();
            // 
            self.b.position_at_end(dtor_call_bb);
            let dtor = self.m.get_function(format!("{}.dtor", td.get().name).as_str()).unwrap();
            self.b.build_call(dtor, &[v.into()], "").unwrap();
            self.b.build_unconditional_branch(continue_bb).unwrap();
            //
            self.b.position_at_end(continue_bb);
        } else if let Ty::Option(inner) = ty {
            if let Ty::UserTy(_) = &**inner {
                // option of a reference type,
                // if the value is null, do nothing, otherwise drop it ordinarily
                let cmp = self.b.build_int_compare(IntPredicate::EQ, v.into_pointer_value(), self.tys.ptr.const_null(), "").unwrap();
                let drop_bb = self.new_bb("");
                let continue_bb = self.new_bb("");
                self.b.build_conditional_branch(cmp, continue_bb, drop_bb).unwrap();
                self.b.position_at_end(drop_bb);
                self.build_drop(v, inner);
                self.b.build_unconditional_branch(continue_bb).unwrap();
                self.b.position_at_end(continue_bb);
            }
        } else if ty == &Ty::Any {
            todo!()
        } else { unreachable!() }
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

/// Reproducible hash function for strings
fn name_hash(s: &str) -> u64 {
    let mut h = fnv::FnvHasher::default();
    h.write(s.as_bytes());
    h.finish()
}