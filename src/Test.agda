
module Test where

open import Prelude
open import X86
open import Memory
open import Container.Traversable
open import Container.Path
open import Text.Printf

prologue : X86Code _ _
prologue
  = push %rbp
  ∷ mov  %rsp %rbp
  ∷ []

epilogue : X86Code _ _
epilogue
  = pop %rbp
  ∷ ret
  ∷ []

code : X86Code _ _
code
  = mov  %rdi %rdx
  ∷ add  %rdi %rdx
  ∷ push %rdx
  ∷ add  0x10 %rdx
  ∷ mov  %rdx %rax
  ∷ pop  %rdi
  ∷ imul %rdi %rax
  ∷ imul 2    %rax
  ∷ []

jit : ∀ {i j} → X86Code i j → IO (Nat → Nat)
jit code = writeMachineCode $ compile $ prologue <+> code <+> epilogue

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
