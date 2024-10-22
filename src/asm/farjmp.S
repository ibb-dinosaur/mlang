; implement a longjmp-like mechanism for handling panics across the FFI boundary

global __callwexcep
global __throwexcep

struc farjmpbuf
    buf_rbx: resq 1
    buf_rbp: resq 1
    buf_r12: resq 1
    buf_r13: resq 1
    buf_r14: resq 1
    buf_r15: resq 1
    buf_rflags: resq 1
    ; Don't bother with FS, GS
    buf_mxcsr: resd 1
    buf_87cw: resw 1
    buf_pad: resw 1
endstruc

                                    
; u64 callwexcep(save_pointer: void**, inner_fn: (void) -> u64, result: u64*)
__callwexcep:
    ; Save neccessary registers
    push rdx                        ; align stack and save third argument
    sub rsp, farjmpbuf_size         ; allocate buffer
    mov [rsp + buf_rbx], rbx
    mov [rsp + buf_rbp], rbp
    mov [rsp + buf_r12], r12
    mov [rsp + buf_r13], r13
    mov [rsp + buf_r14], r14
    mov [rsp + buf_r15], r15
    pushfq                          ; push rflags to stack
    pop rax                         ; pop rflags to rax
    mov [rsp + buf_rflags], rax
    stmxcsr [rsp + buf_mxcsr]       ; store mxcsr
    fnstcw [rsp + buf_87cw]         ; store x87 control word
    ; save the buffer pointer to [rdi]
    mov [rdi], rsp
    ; call the inner function
    call rsi
    ; the function either returns normally here or calls throwexcep (->common_ret)
    ; if the function returned normally, save its result
    mov rdx, [rsp + farjmpbuf_size]
    mov [rdx], rax
    mov rax, 0 ; signals the inner function returned normally
common_ret:
    ; if the function returned normally, all registers are restored
    ; if the function threw an exception, the registers are restored in throwexcep
    ; the payload is in rax
    add rsp, farjmpbuf_size         ; deallocate buffer
    add rsp, 8                      ; restore stack alignment
    ret

; throw exception from inside callwexcep
; throwexcep(save_pointer: ptr, payload: nonzero_u64)
__throwexcep:
    ; restore the stack pointer = address of the buffer
    mov rsp, [rdi]
    ; restore all registers
    mov rbx, [rsp + buf_rbx]
    mov rbp, [rsp + buf_rbp]
    mov r12, [rsp + buf_r12]
    mov r13, [rsp + buf_r13]
    mov r14, [rsp + buf_r14]
    mov r15, [rsp + buf_r15]
    mov rax, [rsp + buf_rflags]     ; restore rflags
    push rax
    popfq
    ldmxcsr [rsp + buf_mxcsr]       ; restore mxcsr
    fldcw [rsp + buf_87cw]          ; restore x87 control word
    ; save the payload to rax
    mov rax, rsi
    jmp common_ret

