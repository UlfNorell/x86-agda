
module Talk where

open import Prelude
open import X86
open import Memory
open import Container.Traversable
open import Container.Path
open import Text.Printf

import X86.Compile as C
import X86.Untyped as Raw
open Raw using (mov; add; sub; imul; idiv; label; loop; push; pop; ret)

-- Helpers --

Function : (Int → Int → Int) → Set
Function f = X86Fun (λ _ _ → ⊤) (λ x y → f x y)

usage : {A : Set} → Nat → IO A
usage n =
  do putStrLn ("Expected " & show n & " natural number arguments")
  ~| exitWith (Failure 1)

getIntArgs : ∀ n → IO (Vec Int n)
getIntArgs n =
  do args ← getArgs
  -| case traverse parseNat args of λ where
       nothing   → usage n
       (just xs) →
         case length xs == n of λ where
           (yes refl) → pure (pos <$> listToVec xs)
           (no _)     → usage n

M : Int
M = 1636102261

iterate : {A : Set} → Nat → (A → A) → A → A
iterate zero    f x = x
iterate (suc n) f x = iterate n f $! f x


--- === Title slide

{-

   Mystery Talk
    Ulf Norell
     AIM XXV


-}
















--- === Code

fun : X86Fun (λ x y → NonZeroInt y) λ x y → x quot′ y
fun = mkFun
  ( mov %rdi %rax
  ∷ sub 8 %rsp
  ∷ push %rsi
  ∷ idiv %rsi
  ∷ add 16 %rsp
  ∷ ret
  ∷ [] )

loop' : X86Fun (λ _ y → PosInt y) (λ x y → x + y)
loop' = mkFun
  ( mov %rsi %rcx
  ∷ label (λ l s → set %rdi (%rdi + var l) s)
  ∷ add 1 %rdi
  ∷ loop 0
  ∷ mov %rdi %rax
  ∷ ret
  ∷ []
  )

blumblumLoopTyped : (M : Int) {{_ : NonZeroInt M}} → X86Code' (λ _ y → PosInt y) initS _
blumblumLoopTyped M
  = mov %rsi %rcx
  ∷ mov %rdi %rax
  ∷ mov (imm M) %rdi
  ∷ label (λ l → set %rax (loopInv l (λ x → x * x modE (imm M)) %rdi) ∘ set %rdx undef)
  ∷ imul %rax %rax
  ∷ idiv %rdi
  ∷ mov %rdx %rax
  ∷ loop 0
  ∷ ret
  ∷ []

blumblumTyped : (M : Int) {{_ : NonZeroInt M}} →
                 X86Fun (λ _ y → PosInt y)
                        (λ x y → iterInt y (λ z → z * z rem′ M) x)
blumblumTyped M = mkFun (blumblumLoopTyped M)

















--- === Main

main : IO ⊤
main =
  do f ← loadMachineCode (compileFun (blumblumTyped M))
  -| caseM getIntArgs 3 of λ where
       (pos 0 ∷ x ∷ y ∷ []) → print (f x y)
       (_ ∷ x ∷ pos y ∷ []) → print (iterate y (λ x → x * x rem M) x)
       _ → return _
