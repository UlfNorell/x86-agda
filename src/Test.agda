
module Test where

open import Prelude
open import Asm
open import Memory

prologue : Asm
prologue
  = push %rbp
  ∷ mov  %rsp %rbp
  ∷ []

epilogue : Asm
epilogue
  = pop %rbp
  ∷ ret
  ∷ []

code : Asm
code
  = imul %rdi %rdi
  ∷ mov  %rdi %rax
  ∷ []

jit : Asm → IO (Nat → Nat)
jit code = writeMachineCode $ compile $ prologue ++ code ++ epilogue

main : IO ⊤
main =
  do fun ← jit code
  -| print (fun 201)
