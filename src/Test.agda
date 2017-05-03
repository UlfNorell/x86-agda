
module Test where

open import Prelude
open import X86
open import Memory
open import Container.Traversable
open import Container.Path
open import Text.Printf

-- prologue : ∀ {s} → X86Code s _
-- prologue
--   = push %rbp
--   ∷ mov  %rsp %rbp
--   ∷ []

-- epilogue : ∀ {s} {{_ : isRet s ≡ false}} → X86Code s _
-- epilogue
--   = pop %rbp
--   ∷ ret
--   ∷ []

code : X86Fun (λ x → 2 * ((x + x) * (16 + (x + x))))
code = mkFun
  ( push %rbp
  ∷ mov  %rsp %rbp
  --
  ∷ mov  %rdi %rdx
  ∷ add  %rdi %rdx
  ∷ push %rdx
  ∷ add  0x10 %rdx
  ∷ mov  %rdx %rax
  ∷ pop  %rdi
  ∷ imul %rdi %rax
  ∷ imul 2    %rax
  --
  ∷ pop %rbp
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
