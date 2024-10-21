use inkwell::{context::ContextRef, execution_engine::ExecutionEngine, module::Module, targets::{InitializationConfig, Target}, values::GenericValue};

pub struct Runner<'a> {
    ctx: ContextRef<'a>,
    ee: ExecutionEngine<'a>,
    is_jit: bool,
}

impl<'a> Runner<'a> {
    pub fn new(m: &'a Module, jit: bool) -> Self {
        Target::initialize_native(&InitializationConfig::default()).unwrap();

        let ee = 
            if jit {
                m.create_jit_execution_engine(inkwell::OptimizationLevel::Less)
            } else {
                m.create_interpreter_execution_engine()
            }.unwrap();
        let r = Runner { ee, ctx: m.get_context(), is_jit: jit };
        r.load_rt(m);
        crate::rt::init_rt_allocator(1 << 23); // 8 MB
        r
    }

    fn load_rt(&self, m: &Module) {
        macro_rules! load_fn {
            ($name:ident) => {
                self.ee.add_global_mapping(
                    &m.get_function(stringify!($name)).unwrap(), 
                    crate::rt::$name as *const () as usize);
            };
        }
        load_fn!(__tc_fail1);
        load_fn!(__tc_fail_null);
        load_fn!(__cmp_any);
        load_fn!(__allocm);
        load_fn!(__freem);
    }

    // Calls function with 0 or 1 integer arguments, returns an integer result
    pub unsafe fn test_fn(&self, m: &Module, name: &str, arg: Option<isize>) -> isize {
        if !self.is_jit {
            // use `run_function` because it's safer
            let arg: Option<GenericValue<'a>> = arg.map(|x| self.ctx.i64_type().create_generic_value(x as _, true));
            let result = self.ee.run_function(
                m.get_function(name).unwrap(),
                arg.as_ref().as_slice());
            result.as_int(true) as isize
        } else {
            // use getFunctionAddress if JITing
            match arg {
                None => { // int fn(void)
                    let f = 
                        self.ee.get_function::<unsafe extern "C" fn() -> isize>(name).unwrap();
                    f.call()
                }
                Some(x) => { // int fn(int)
                    let f = 
                        self.ee.get_function::<unsafe extern "C" fn(isize) -> isize>(name).unwrap();
                    f.call(x)
                }
            }
        }
    }
}