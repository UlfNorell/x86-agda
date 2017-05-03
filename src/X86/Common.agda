
module X86.Common where

open import Prelude

data Reg : Set where
  rax rcx rdx rbx rsp rbp rsi rdi : Reg

data Val : Set where
  reg : Reg → Val
  imm : Int → Val

data Dst : Set where
  reg : Reg → Dst

data Exp : Set where
  undef : Exp
  reg : Reg → Exp
  imm : Int → Exp
  _⊕_ _⊝_ _⊛_ : Exp → Exp → Exp

eval : (Reg → Int) → Exp → Maybe Int
eval φ undef   = nothing
eval φ (reg r) = just (φ r)
eval φ (imm n) = just n
eval φ (e ⊕ e₁) = ⦇ eval φ e + eval φ e₁ ⦈
eval φ (e ⊝ e₁) = ⦇ eval φ e - eval φ e₁ ⦈
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
  fromNat {{NumVal}} n = imm (pos n)

  NegVal : Negative Val
  Negative.Constraint NegVal _ = ⊤
  fromNeg {{NegVal}} n = imm (fromNeg n)
