
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
  ∷ push %rdx {{pushPre refl refl}}
  ∷ sub  100  %rdx
  ∷ mov  %rdx %rax
  ∷ pop  %rdi {{popPre refl refl refl}} -- gah: instance search fail!
  ∷ imul %rdi %rax
  ∷ imul 2    %rax
  ∷ ret
  ∷ []

testfun : X86Fun (λ x → (x + x - 100) * (x + x) * 2)
testfun = mkFun code

finalState : ∀ {f} → X86Fun f → S
finalState (mkFun {s = s} _) = s

jit : ∀ {f} → X86Fun f → IO (Int → Int)
jit (mkFun code) = writeMachineCode $ compile code

usage : IO ⊤
usage =
  do prog ← getProgName
  -| putStrLn ("Usage: " & prog & " N₁ .. Nₙ")

run : List Nat → IO ⊤
run xs =
  do fun ← jit testfun
  -| print (map (fun ∘ pos) xs)

main : IO ⊤
main =
  do args ← getArgs
  -| maybe usage run (traverse parseNat args)
