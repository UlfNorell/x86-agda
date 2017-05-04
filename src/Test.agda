
module Test where

open import Prelude
open import X86
open import Memory
open import Container.Traversable
open import Container.Path
open import Text.Printf

import X86.Compile as C
import X86.Untyped as Raw


code : X86Code initialState _
code
  = mov  %rdi %rdx
  ∷ add  %rdi %rdx
  ∷ push %rdx
  ∷ sub  100  %rdx
  ∷ mov  %rdx %rax
  ∷ pop  %rdi
  ∷ imul %rdi %rax
  ∷ imul 2    %rax
  ∷ ret
  ∷ []

fun : X86Fun (λ x → (x + x - 100) * (x + x) * 2)
fun = mkFun code

finalState : ∀ {f} → X86Fun f → S
finalState (mkFun {s = s} _) = s

compileFun : ∀ {f} → X86Fun f → MachineCode
compileFun (mkFun code) = compile code

jit : ∀ {f} → X86Fun f → IO (Int → Int)
jit = writeMachineCode ∘ compileFun

usage : IO ⊤
usage =
  do prog ← getProgName
  -| putStrLn ("Usage: " & prog & " N₁ .. Nₙ")

run : List Nat → IO ⊤
run xs =
  do f ← jit fun
  -| print (map (f ∘ pos) xs)

main : IO ⊤
main =
  do args ← getArgs
  -| maybe usage run (traverse parseNat args)
