//! Runtime types and functions
#![allow(unused)]

use std::sync::Mutex;

use crate::allocator::Allocator;

/// The `any` type
/// 16 bytes, first word = tag, second word = actual value (can be scalar or pointer)
/// The any_tag is different(!) from the type tag
#[repr(C)]
pub(crate) struct AnyT {
    any_tag: usize,
    value: usize,
}

/// integer (i64) value
const ANY_TAG_INT: usize = 1;
/// boolean value (only 0 or 1 are valid)
const ANY_TAG_BOOL: usize = 2;
/// void "value"
/// NOTE: the void type is implemented as an undefined (LLVM undef) usize value
const ANY_TAG_VOID: usize = 7;
/// A Compressed Function pointer
///
/// This means that the second field is directly a pointer to the function
/// and the function type data (pointer to [`TypeDescObj`]) is stored as the function prefix
const ANY_TAG_COMFUN: usize = 15;
/// Tag >= 16 -> pointer type
const ANY_TAG_PTR_START: usize = 16;

#[cold]
extern "C" fn __tc_fail1(expected_ty: usize, actual_ty: usize, payload: usize) -> ! {
    // note: panicking across FFI boundaries is UB
    panic!("runtime error: implicit type cast failed")
}

extern "C" fn __cmp_any(a: AnyT, b: AnyT) -> bool {
    if a.any_tag != b.any_tag {
        return false;
    }
    match a.any_tag {
        ANY_TAG_INT | ANY_TAG_BOOL => a.value == b.value,
        ANY_TAG_VOID => true,
        // pointer equality
        ANY_TAG_COMFUN => a.value == b.value,
        // note: panicking across FFI boundaries is UB
        _ => panic!("internal error: unknown any tag")
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
union TypeTag {
    prim_tag: usize,
    ptr_tag: *const TypeDescObj
}

const TAG_NONE: usize = 0;
const TAG_INT: usize = 1;
const TAG_BOOL: usize = 2;
const TAG_VOID: usize = 7;
const TAG_ANY: usize = 14;
const TAG_PTR_START: usize = 16;

#[repr(C)]
#[derive(Clone, Copy)]
struct TypeDescObj {
    obj_tag: usize,
    desc: TypeDesc
}

const OBJ_TAG_FUNC: usize = 1;
const OBJ_TAG_USER_STRUCT: usize = 2;

#[repr(C)]
#[derive(Clone, Copy)]
union TypeDesc {
    func: FuncDesc,
    struct_: StructDesc,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct FuncDesc {
    ret: TypeTag,
    params: [TypeTag; 0]
}

#[repr(C)]
#[derive(Clone, Copy)]
struct StructDesc {
    name_hash: [u8; 8], // mostly for debugging
    fields: [TypeTag; 0]
}

#[allow(unused)]
extern "C" fn __rcdup(ptr: *mut u8) { unsafe {
    // note: this function is not called directly, instead LLVM IR is generated
    // however its correctness depends on the allocator module
    // the expected LLVM IR is:
    // %0 = getelementptr inbounds i8, ptr %ptr, i64 -4
    // %1 = load i32, ptr %0, align 4
    // %2 = add i32 %1, 1
    // store i32 %2, ptr %0, align 4
    Allocator::inc_refcount(ptr);
} }

#[allow(unused)]
extern "C" fn __rcdrop(ptr: *mut u8, dtor: unsafe extern "C" fn(*mut u8)) { unsafe {
    // note: this function is not called directly, instead LLVM IR is generated
    // the expected LLVM IR is:
    /*
    %0 = getelementptr inbounds i8, ptr %ptr, i64 -4
    %1 = load i32, ptr %0, align 4
    %2 = add i32 %1, -1
    store i32 %2, ptr %0, align 4
    %3 = icmp eq i32 %2, 0
    br i1 %3, label %calldtor, label %continue

    calldtor:
    call void %dtor(ptr noundef nonnull %ptr) #3
    br label %continue

    continue:
     */
    if Allocator::dec_and_read_refcount(ptr) == 0 {
        dtor(ptr);
    }
} }

pub(crate) static RT_ALLOCATOR: Mutex<Allocator> = Mutex::new(unsafe {
    Allocator::new(std::ptr::null_mut(), std::ptr::null_mut()) });

/// Must be called before any calls to __allocm and __freem
pub fn init_rt_allocator(mem_size: usize) {
    let mut a = RT_ALLOCATOR.lock().unwrap();
    *a = Allocator::new_mmap(mem_size).unwrap();
    a.init();
}

pub extern "C" fn __allocm(size: u64) -> *mut u8 {
    // allocate managed memory
    let a = RT_ALLOCATOR.lock().unwrap();
    let ptr = a.alloc(size as usize).unwrap();
    // the allocator sets refcount to zero, increase it to one
    unsafe { Allocator::inc_refcount(ptr); }
    ptr
}

pub extern "C" fn __freem(ptr: *mut u8, size: u64) {
    RT_ALLOCATOR.lock().unwrap().dealloc_cheap(ptr, size as _);
}