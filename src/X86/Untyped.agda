
module X86.Untyped where

open import Prelude
open import X86.Common

data Instr : Set where
  ret   : Instr
  mov   : Val → Dst → Instr
  add   : Val → Dst → Instr
  sub   : Val → Dst → Instr
  imul  : Val → Dst → Instr
  idiv  : Dst → Instr
  push  : Val → Instr
  pop   : Dst → Instr
  label : Instr
  loop  : Nat → Instr

X86Code = List Instr
