//! Runtime types and functions
#![allow(unused)]

/// The `any` type
/// 16 bytes, first word = tag, second word = actual value (can be scalar or pointer)
/// The any_tag is different(!) from the type tag
#[repr(C)]
struct AnyT {
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