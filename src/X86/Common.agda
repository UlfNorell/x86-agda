
module X86.Common where

open import Prelude

data Reg : Set where
  rax rcx rdx rbx rsp rbp rsi rdi : Reg

data Val : Set where
  reg : Reg → Val
  imm : Nat → Val

data Dst : Set where
  reg : Reg → Dst

data Exp : Set where
  undef : Exp
  reg : Reg → Exp
  imm : Nat → Exp
  _⊕_ : Exp → Exp → Exp
  _⊛_ : Exp → Exp → Exp

eval : (Reg → Nat) → Exp → Maybe Nat
eval φ undef   = nothing
eval φ (reg r) = just (φ r)
eval φ (imm n) = just n
eval φ (e ⊕ e₁) = ⦇ eval φ e + eval φ e₁ ⦈
eval φ (e ⊛ e₁) = ⦇ eval φ e * eval φ e₁ ⦈

pattern %rax = reg rax
pattern %rcx = reg rcx
pattern %rdx = reg rdx
pattern %rbx = reg rbx
pattern %rsp = reg rsp
pattern %rbp = reg rbp
pattern %rsi = reg rsi
pattern %rdi = reg rdi

instance
  NumVal : Number Val
  Number.Constraint NumVal _ = ⊤
  fromNat {{NumVal}} n = imm n
