
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




--- === Title slide

{-

   Mystery Talk
    Ulf Norell
     AIM XXV


-}








--- === Code


fun : Function λ x y → x + y
fun = mkFun
  ( mov %rdi %rax
  ∷ add %rsi %rax
  ∷ ret ∷ [] )







--- === Main




main : IO ⊤
main =
  do f ← loadMachineCode (compileFun fun)
  -| caseM getIntArgs 2 of λ where
       (x ∷ y ∷ []) → print (f x y)
