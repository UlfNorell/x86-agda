
module Test where

open import Prelude
open import X86
open import Memory
open import Container.Traversable
open import Container.Path
open import Text.Printf

code : X86Fun (λ x → (x + x + 1) * (x + x) * 2)
code = mkFun
  ( mov  %rdi %rdx
  ∷ add  %rdi %rdx
  ∷ push %rdx
  ∷ add  1    %rdx
  ∷ mov  %rdx %rax
  ∷ pop  %rdi
  ∷ imul %rdi %rax
  ∷ imul 2    %rax
  ∷ ret
  ∷ [] )

jit : ∀ {f} → X86Fun f → IO (Nat → Nat)
jit (mkFun code) = writeMachineCode $ compile code

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
