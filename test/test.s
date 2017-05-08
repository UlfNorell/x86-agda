.section __TEXT,__text
.globl _main
_main:
  idivq %rax
  divq 0x10203040
  ret
