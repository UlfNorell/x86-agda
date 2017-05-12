
module Test where

open import Prelude
open import X86
open import Memory
open import Container.Traversable
open import Container.Path
open import Text.Printf

import X86.Compile as C
import X86.Untyped as Raw

Pre : Precondition
Pre _ y = NonZeroInt y

code : X86Code Pre initS _
code = mov %rdi %rax
     ∷ idiv %rsi
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

blumblumshubStep : X86Fun Pre λ x M → x * x rem M
blumblumshubStep = mkFun
  $ imul %rdi %rdi
  ∷ mov  %rdi %rax
  ∷ idiv %rsi
  ∷ mov  %rdx %rax
  ∷ ret
  ∷ []

rawCode : Raw.X86Code
rawCode
  = Raw.mov %rdi %rcx
  ∷ Raw.label
  ∷ Raw.imul %rsi %rsi
  ∷ Raw.loop 0
  ∷ Raw.mov %rsi %rax
  ∷ Raw.ret
  ∷ []

-- fun : X86Fun λ x y → ((x + y - 100) * (x + y)) quot 2
-- fun : X86Fun λ x y → (x + y - 100) * (x + y)
fun : X86Fun Pre λ x y → x quot y
fun = mkFun code

finalState : ∀ {P f} → X86Fun P f → S _
finalState (mkFun {s = s} _) = s

compileFun : ∀ {P f} → X86Fun P f → MachineCode
compileFun (mkFun code) = compile code

showMachineCode : MachineCode → String
showMachineCode = foldr (printf "%02x %s") ""

showCode : ∀ {P s s₁} → X86Code P s s₁ → String
showCode = showMachineCode ∘ compile

jit : ∀ {P f} → X86Fun P f → IO (∀ x y {{_ : P x y}} → Int)
jit fun =
  do f ← writeMachineCode (compileFun fun)
  -| pure (λ x y {{_}} → f x y)

jitRaw : Raw.X86Code → IO (Int → Int → Int)
jitRaw code = writeMachineCode (C.compile code)

usage : IO ⊤
usage =
  do prog ← getProgName
  -| putStrLn ("Usage: " & prog & " X Y")

runRaw : Raw.X86Code → List Nat → IO ⊤
runRaw code (x ∷ y ∷ []) =
  do f ← jitRaw code
  -| print (f (pos x) (pos y))
runRaw _ _ = usage

run : List Nat → IO ⊤
run (x ∷ zero ∷ []) = putStrLn "Sorry, no division by 0."
run (x ∷ suc y ∷ []) =
  do f ← jit fun
  -| print (f (pos x) (pos (suc y)))
run _ = usage

iterate : {A : Set} → Nat → (A → A) → A → A
iterate zero    f x = x
iterate (suc n) f x = iterate n f $! f x

p q M : Int
p = 32707
q = 50023
M = p * q

runBBS : List Nat → IO ⊤
runBBS (0 ∷ x ∷ n ∷ []) =
  do step ← jit blumblumshubStep
  -| print (iterate n (λ x → step x M) (pos x))
runBBS (1 ∷ x ∷ n ∷ []) =
  print (iterate n (λ x → x * x rem M) (pos x))
runBBS _ = usage

main : IO ⊤
main =
  do args ← getArgs
  -- -| maybe usage runBBS (traverse parseNat args)
  -| maybe usage (runRaw rawCode) (traverse parseNat args)
