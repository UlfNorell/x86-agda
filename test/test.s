# Simple exit program
.section __TEXT,__text
.globl _main
_main:
  push %rbp
  mov %rsp, %rbp
  ret
