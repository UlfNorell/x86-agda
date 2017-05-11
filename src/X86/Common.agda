
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

Env = Reg → Int

data Exp (P : Env → Set) : Set
eval : ∀ {P} (φ : Env) {{_ : P φ}} → Exp P → Maybe Int

NonZeroE : ∀ {P} → Exp P → Set
NonZeroE {P} e = ∀ {φ} {{_ : P φ}} → NonZeroM (eval φ e)

data Exp P where
  undef : Exp P
  reg : Reg → Exp P
  imm : Int → Exp P
  _⊕_ _⊝_ _⊛_ : Exp P → Exp P → Exp P
  divE-by modE-by : (b : Exp P) {{nz : NonZeroE b}} → Exp P → Exp P

syntax divE-by y x = x divE y
syntax modE-by y x = x modE y

evalNZ : ∀ {P} → ((b : Int) {{_ : NonZeroInt b}} → Int → Int) →
         (φ : Env) {{_ : P φ}} → (b : Exp P) {{_ : NonZeroE b}} → Exp P → Maybe Int
evalNZ f φ e₁ {{nz}} e with eval φ e₁ | mkInstance (nz {φ})
... | nothing | _ = nothing
... | just v  | _ = (| (f v) (eval φ e) |)

eval φ undef   = nothing
eval φ (reg r) = just (φ r)
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

norm : ∀ {P} → (Reg → NF) → Exp P → NF
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

  NumExp : ∀ {P} → Number (Exp P)
  Number.Constraint NumExp _ = ⊤
  fromNat {{NumExp}} n = imm (fromNat n)

  NegExp : ∀ {P} → Negative (Exp P)
  Negative.Constraint NegExp _ = ⊤
  fromNeg {{NegExp}} n = imm (fromNeg n)

  SemiringExp : ∀ {P} → Semiring (Exp P)
  zro {{SemiringExp}} = 0
  one {{SemiringExp}} = 1
  _+_ {{SemiringExp}} a (imm (pos 0)) = a
  _+_ {{SemiringExp}} (imm (pos 0)) b = b
  _+_ {{SemiringExp}} (a ⊝ imm b) (imm c) = a + imm (c - b)
  _+_ {{SemiringExp}} a b = a ⊕ b
  _*_ {{SemiringExp}} (imm (pos 0)) b = imm (pos 0)
  _*_ {{SemiringExp}} a (imm (pos 0)) = imm (pos 0)
  _*_ {{SemiringExp}} a b = a ⊛ b

  SubExp : ∀ {P} → Subtractive (Exp P)
  _-_    {{SubExp}} (a ⊕ imm b) (imm c) = a + imm (b - c)
  _-_    {{SubExp}} (a ⊝ imm b) (imm c) = a - imm (b + c)
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

  ShowExp : ∀ {P} → Show (Exp P)
  showsPrec {{ShowExp}} p undef = showString "undef"
  showsPrec {{ShowExp}} p (reg r) = shows r
  showsPrec {{ShowExp}} p (imm n) = shows n
  showsPrec {{ShowExp}} p (e ⊕ e₁) = showParen (p >? 6) (showsPrec 6 e ∘ showString " + " ∘ showsPrec 7 e₁)
  showsPrec {{ShowExp}} p (e ⊝ e₁) = showParen (p >? 6) (showsPrec 6 e ∘ showString " - " ∘ showsPrec 7 e₁)
  showsPrec {{ShowExp}} p (e ⊛ e₁) = showParen (p >? 7) (showsPrec 7 e ∘ showString " * " ∘ showsPrec 8 e₁)
  showsPrec {{ShowExp}} p (e divE e₁) = showParen (p >? 7) (showsPrec 7 e ∘ showString " / " ∘ showsPrec 8 e₁)
  showsPrec {{ShowExp}} p (e modE e₁) = showParen (p >? 7) (showsPrec 7 e ∘ showString " % " ∘ showsPrec 8 e₁)
