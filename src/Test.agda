
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
code = mov 0 %rdx
     ∷ mov %rdi %rax
     ∷ add %rsi %rax
     ∷ mov 2 %rdi
     ∷ idiv %rdi
     ∷ ret
     ∷ []
  -- = mov  %rdi %rdx
  -- ∷ add  %rsi %rdx
  -- ∷ push %rdx
  -- ∷ sub  100  %rdx
  -- ∷ mov  %rdx %rax
  -- ∷ pop  %rdi
  -- ∷ imul %rdi %rax
  -- ∷ mov  0    %rdx
  -- ∷ idiv 2
  -- ∷ ret
  -- ∷ []

-- fun : X86Fun λ x y → ((x + y - 100) * (x + y)) quot 2
-- fun : X86Fun λ x y → (x + y - 100) * (x + y)
fun : X86Fun λ x y → (x + y) quot 2
fun = mkFun code

finalState : ∀ {f} → X86Fun f → S
finalState (mkFun {s = s} _) = s

compileFun : ∀ {f} → X86Fun f → MachineCode
compileFun (mkFun code) = compile code

showMachineCode : ∀ {s s₁} → X86Code s s₁ → String
showMachineCode = foldr (printf "%02x %s") "" ∘ compile

jit : ∀ {f} → X86Fun f → IO (Int → Int → Int)
jit = writeMachineCode ∘ compileFun

usage : IO ⊤
usage =
  do prog ← getProgName
  -| putStrLn ("Usage: " & prog & " X Y")

run : List Nat → IO ⊤
run (x ∷ y ∷ []) =
  do f ← jit fun
  -| print (f (pos x) (pos y))
run _ = usage

main : IO ⊤
main =
  do args ← getArgs
  -| maybe usage run (traverse parseNat args)
