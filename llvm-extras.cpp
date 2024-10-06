#include "llvm-extras.h"
#include <llvm-18/llvm/IR/Function.h>
#include <llvm-18/llvm/IR/Constant.h>

extern "C" void LLVMSetPrefixData(LLVMValueRef Fn, LLVMValueRef prefixData) {
    llvm::Function *F = llvm::unwrap<llvm::Function>(Fn);
    llvm::Constant *prefix = llvm::unwrap<llvm::Constant>(prefixData);
    F->setPrefixData(prefix);
}