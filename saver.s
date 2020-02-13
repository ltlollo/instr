; This is free and unencumbered software released into the public domain.
; For more information, see LICENSE

; Dump addresses at previous page in `instr.address`
; To print the dump in a readable format: $xxd -e -g8 mminstr.dump

refs equ 0x1000                         ; dist between code page and RW data
start:                                  ; rax is the input addr to be saved
    push rdx
    push rsi
    mov rdx, [rel start-refs + 0x8]     ; buffer size [0 ~ 0xff0]
    cmp rdx, 0x1000 - 0x10
    je FLUSH_BUF
PUSH:
    mov rsi, [rsp + 24]                 ; read or write bit [0 ~ 1]
    shl rsi, 63
    or  rax, rsi                        ; addr | (write << 63)
    lea rsi, [rel start-refs]           ; begin of RW page, buffer is at 0x10
    mov [rsi + rdx + 0x10], rax         ; save input data
    add rdx, 8                          ; increment buffer size
    mov [rel start-refs + 0x8], rdx     ; save buffer size
    pop rsi
    pop rdx
    ret
FLUSH_BUF:
    push rax
    push rdi
    push rsi
    push rdx
    push rcx
    push r11
    mov rdi, [rel start-refs + 0x0]     ; output file descriptor
    cmp rdi, 0
    je OPEN_FILE
WRITE_FILE:
    mov rax, 1                          ; sys_write
    lea rsi, [rel start-refs + 0x10]    ; begin of output buffer
                                        ; rdx is still output buffer size
    syscall
    pop r11
    pop rcx
    pop rdx
    pop rsi
    pop rdi
    pop rax
    mov rdx, 0                          ; reset buffer size to 0
    mov qword [rel start-refs + 0x8], 0 ; save buffer size
    jmp PUSH
OPEN_FILE:
    push rdx
    mov rax, 2                          ; sys_open
    lea rdi, [rel fname]                ; file name
    mov rsi,  0x241                     ; flags: O_WRONLY|O_CREAT|O_TRUNC
    mov rdx, 0x1b6                      ; mode: 0666
    syscall
    pop rdx
    mov [rel start-refs + 0x0], rax     ; save output file descriptor
    mov rdi, rax                        ; output fd
    jmp WRITE_FILE
FLUSH_REMAINING:
    push rdx                            ; to match pop rdx @:23
    push rsi                            ; to match pop rsi @:22
    mov rdx, [rel start-refs + 0x8]     ; buffer size
    jmp FLUSH_BUF

fname: db 'instr.address', 0            ; output file name
dq   $ - FLUSH_REMAINING                ; FLUSH_REMAINING distance from bottom

; LICENSE
; This is free and unencumbered software released into the public domain.
;
; Anyone is free to copy, modify, publish, use, compile, sell, or
; distribute this software, either in source code form or as a compiled
; binary, for any purpose, commercial or non-commercial, and by any
; means.
;
; In jurisdictions that recognize copyright laws, the author or authors
; of this software dedicate any and all copyright interest in the
; software to the public domain. We make this dedication for the benefit
; of the public at large and to the detriment of our heirs and
; successors. We intend this dedication to be an overt act of
; relinquishment in perpetuity of all present and future rights to this
; software under copyright law.
;
; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
; IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
; OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
; ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
; OTHER DEALINGS IN THE SOFTWARE.
;
; For more information, please refer to <http://unlicense.org/>
