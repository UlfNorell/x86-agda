
module X86.Typed where

open import Prelude
open import Container.Path

open import X86.Common
import X86.Untyped as Untyped
open Untyped using (ret; mov; add; imul; push; pop)

S = ⊤

data Instr : S → S → Set where
  ret  : Instr _ _
  mov  : Val → Dst → Instr _ _
  add  : Val → Dst → Instr _ _
  imul : Val → Dst → Instr _ _
  push : Val → Instr _ _
  pop  : Dst → Instr _ _

X86Code = Path Instr

eraseInstr : ∀ {i j} → Instr i j → Untyped.Instr
eraseInstr ret = ret
eraseInstr (mov src dst)  = mov src dst
eraseInstr (add src dst)  = add src dst
eraseInstr (imul val dst) = imul val dst
eraseInstr (push val)     = push val
eraseInstr (pop dst)      = pop dst

erase : ∀ {i j} → X86Code i j → Untyped.X86Code
erase = foldPath (_∷_ ∘ eraseInstr) []
