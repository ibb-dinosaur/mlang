#include <llvm-c-18/llvm-c/Core.h>

#ifdef __cplusplus
extern "C" {
#endif

void LLVMSetPrefixData(LLVMValueRef Fn, LLVMValueRef prefixData);

#ifdef __cplusplus
}
#endif