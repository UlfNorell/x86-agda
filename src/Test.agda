
module Test where

open import Prelude
open import X86
open import Memory
open import Container.Traversable
open import Text.Printf

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

usage : IO ⊤
usage =
  do prog ← getProgName
  -| putStrLn ("Usage: " & prog & " N₁ .. Nₙ")

run : List Nat → IO ⊤
run xs =
  do fun ← jit code
  -| print (map fun xs)


main : IO ⊤
main =
  do args ← getArgs
  -| maybe usage run (traverse parseNat args)
