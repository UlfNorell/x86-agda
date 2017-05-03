.section __TEXT,__text
.globl _main
_main:
  sub $0x10203040, %rdi
  mov %rdi, %rax
  ret
