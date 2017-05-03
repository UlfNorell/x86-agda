.section __TEXT,__text
.globl _main
_main:
  push %rbp
  mov %rsp, %rbp
  add %rdi, %rcx
  imul $0x10203040, %rcx, %rdi
  ret
