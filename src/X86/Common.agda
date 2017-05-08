
module X86.Common where

open import Prelude
open import Tactic.Deriving.Eq

NonZeroM : Maybe Int → Set
NonZeroM nothing  = ⊤
NonZeroM (just x) = NonZeroInt x

data Reg : Set where
  rax rcx rdx rbx rsp rbp rsi rdi : Reg

data Val : Set where
  reg : Reg → Val
  imm : Int → Val

data Dst : Set where
  reg : Reg → Dst

unquoteDecl EqReg = deriveEq EqReg (quote Reg)
unquoteDecl EqVal = deriveEq EqVal (quote Val)
unquoteDecl EqDst = deriveEq EqDst (quote Dst)

data Exp : Set
eval : (Reg → Maybe Int) → Exp → Maybe Int

NonZeroE : Exp → Set
NonZeroE e = ∀ {φ} → NonZeroM (eval φ e)

data Exp where
  undef : Exp
  reg : Reg → Exp
  imm : Int → Exp
  _⊕_ _⊝_ _⊛_ : Exp → Exp → Exp
  divE-by modE-by : (b : Exp) {{nz : NonZeroE b}} → Exp → Exp

syntax divE-by y x = x divE y
syntax modE-by y x = x modE y

evalNZ : ((b : Int) {{_ : NonZeroInt b}} → Int → Int) →
         (Reg → Maybe Int) → (b : Exp) {{_ : NonZeroE b}} → Exp → Maybe Int
evalNZ f φ e₁ {{nz}} e with eval φ e₁ | mkInstance (nz {φ})
... | nothing | _ = nothing
... | just v  | _ = (| (f v) (eval φ e) |)

eval φ undef   = nothing
eval φ (reg r) = φ r
eval φ (imm n) = just n
eval φ (e ⊕ e₁) = (| eval φ e + eval φ e₁ |)
eval φ (e ⊝ e₁) = (| eval φ e - eval φ e₁ |)
eval φ (e ⊛ e₁) = (| eval φ e * eval φ e₁ |)
eval φ (e divE e₁) = evalNZ quotInt-by φ e₁ e
eval φ (e modE e₁) = evalNZ remInt-by  φ e₁ e

Polynomial = List Int
NF = Maybe Polynomial

infixr 5 _∷p_
_∷p_ : Int → Polynomial → Polynomial
pos 0 ∷p [] = []
x ∷p xs = x ∷ xs

infixl 6 _+n_ _-n_
infixl 7 _*n_
_+n_ : Polynomial → Polynomial → Polynomial
xs       +n []       = xs
[]       +n (y ∷ ys) = y ∷ ys
(x ∷ xs) +n (y ∷ ys) = x + y ∷p xs +n ys

_-n_ : Polynomial → Polynomial → Polynomial
xs       -n []       = xs
[]       -n (y ∷ ys) = map negate (y ∷ ys)
(x ∷ xs) -n (y ∷ ys) = x - y ∷p xs -n ys

_*n_ : Polynomial → Polynomial → Polynomial
[]       *n ys = []
(x ∷ xs) *n [] = []
(x ∷ xs) *n (y ∷ ys) = x * y ∷p map (x *_) ys +n map (_* y) xs +n (0 ∷p xs *n ys)

singleRegEnv : Reg → Reg → NF
singleRegEnv r r₁ =
  case r == r₁ of λ where
    (yes _) → just (0 ∷ 1 ∷ [])
    (no  _) → nothing

norm : (Reg → NF) → Exp → NF
norm φ undef = nothing
norm φ (reg r) = φ r
norm φ (imm n) = just (n ∷ [])
norm φ (e ⊕ e₁) = (| norm φ e +n norm φ e₁ |)
norm φ (e ⊝ e₁) = (| norm φ e -n norm φ e₁ |)
norm φ (e ⊛ e₁) = (| norm φ e *n norm φ e₁ |)
norm φ (e divE e₁) = nothing    -- this is used for register preservation:
norm φ (e modE e₁) = nothing  -- we don't allow div and mod for that

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
  fromNat {{NumVal}} n = imm (fromNat n)

  NegVal : Negative Val
  Negative.Constraint NegVal _ = ⊤
  fromNeg {{NegVal}} n = imm (fromNeg n)

  NumExp : Number Exp
  Number.Constraint NumExp _ = ⊤
  fromNat {{NumExp}} n = imm (fromNat n)

  NegExp : Negative Exp
  Negative.Constraint NegExp _ = ⊤
  fromNeg {{NegExp}} n = imm (fromNeg n)

  SemiringExp : Semiring Exp
  zro {{SemiringExp}} = 0
  one {{SemiringExp}} = 1
  _+_ {{SemiringExp}} a (imm (pos 0)) = a
  _+_ {{SemiringExp}} (imm (pos 0)) b = b
  _+_ {{SemiringExp}} (a ⊝ imm b) (imm c) = a + imm (c - b)
  _+_ {{SemiringExp}} a b = a ⊕ b
  _*_ {{SemiringExp}} (imm (pos 0)) b = imm (pos 0)
  _*_ {{SemiringExp}} a (imm (pos 0)) = imm (pos 0)
  _*_ {{SemiringExp}} a b = a ⊛ b

  SubExp : Subtractive Exp
  _-_    {{SubExp}} (a ⊕ imm b) (imm c) = a + imm (b - c)
  _-_    {{SubExp}} a b = a ⊝ b
  negate {{SubExp}} a   = 0 - a

  ShowReg : Show Reg
  showsPrec {{ShowReg}} _ rax = showString "%rax"
  showsPrec {{ShowReg}} _ rcx = showString "%rcx"
  showsPrec {{ShowReg}} _ rdx = showString "%rdx"
  showsPrec {{ShowReg}} _ rbx = showString "%rbx"
  showsPrec {{ShowReg}} _ rsp = showString "%rsp"
  showsPrec {{ShowReg}} _ rbp = showString "%rbp"
  showsPrec {{ShowReg}} _ rsi = showString "%rsi"
  showsPrec {{ShowReg}} _ rdi = showString "%rdi"

  ShowExp : Show Exp
  showsPrec {{ShowExp}} p undef = showString "undef"
  showsPrec {{ShowExp}} p (reg r) = shows r
  showsPrec {{ShowExp}} p (imm n) = shows n
  showsPrec {{ShowExp}} p (e ⊕ e₁) = showParen (p >? 6) (showsPrec 6 e ∘ showString " + " ∘ showsPrec 7 e₁)
  showsPrec {{ShowExp}} p (e ⊝ e₁) = showParen (p >? 6) (showsPrec 6 e ∘ showString " - " ∘ showsPrec 7 e₁)
  showsPrec {{ShowExp}} p (e ⊛ e₁) = showParen (p >? 7) (showsPrec 7 e ∘ showString " * " ∘ showsPrec 8 e₁)
  showsPrec {{ShowExp}} p (e divE e₁) = showParen (p >? 7) (showsPrec 7 e ∘ showString " / " ∘ showsPrec 8 e₁)
  showsPrec {{ShowExp}} p (e modE e₁) = showParen (p >? 7) (showsPrec 7 e ∘ showString " % " ∘ showsPrec 8 e₁)
