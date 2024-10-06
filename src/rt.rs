//! Runtime types and functions

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

extern "C" {
    #[cold]
    fn __tc_fail1(expected_ty: usize, actual_ty: usize, payload: usize) -> !;
}

#[repr(C)]
#[derive(Clone, Copy)]
union TypeTag {
    prim_tag: usize,
    ptr_tag: *const TypeDescObj
}

const TAG_NONE: usize = 0;
const TAG_INT: usize = 1;
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

#[repr(C)]
#[derive(Clone, Copy)]
union TypeDesc {
    func: FuncDesc,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct FuncDesc {
    ret: TypeTag,
    params: [TypeTag; 0]
}