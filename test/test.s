.section __TEXT,__text
.globl _main
_main:
  cqto
  idivq %rax
  ret
