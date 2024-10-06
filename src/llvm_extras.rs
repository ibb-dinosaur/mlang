use inkwell::llvm_sys::LLVMValue;

extern "C" {
    pub fn LLVMSetPrefixData(Fn: *mut LLVMValue, prefixData: *mut LLVMValue);
}