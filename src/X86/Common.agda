
module X86.Common where

open import Prelude
open import Tactic.Deriving.Eq

iterInt : {A : Set} → Int → (A → A) → A → A
iterInt (pos (suc n)) f z = f (iterInt (pos n) f z)
iterInt _             f z = z

infixl 7 _quot′_ _rem′_

_quot′_ : Int → Int → Int
_ quot′ (pos 0) = 0
a quot′ b@(pos (suc _)) = a quot b
a quot′ b@(negsuc _)    = a quot b

_rem′_ : Int → Int → Int
_ rem′ (pos 0) = 0
a rem′ b@(pos (suc _)) = a rem b
a rem′ b@(negsuc _)    = a rem b

WhenJust : {A : Set} → (P : A → Set) → Maybe A → Set
WhenJust _ nothing = ⊥
WhenJust P (just x) = P x

SmashWhenJust : ∀ {A} {P : A → Set} → (∀ {x} → Smashed (P x)) → ∀ {x} → Smashed (WhenJust P x)
SmashWhenJust smP {nothing} = it
SmashWhenJust smP {just x}  = smP

data PosInt : Int → Set where
  instance mkPosInt : ∀ {n} → PosInt (pos (suc n))

record _∧_ (A B : Set) : Set where
  instance constructor ∧I
  field {{fst}} : A
        {{snd}} : B

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

_[_:=_] : (Nat → Maybe Int) → Nat → Maybe Int → Nat → Maybe Int
(ρ [ x := v ]) y = ifYes x == y then v else ρ y

data Exp (P : Env → Set) : Set
eval : ∀ {P} (φ : Env) {{_ : P φ}} → Exp P → Maybe Int

ExpP : ∀ {P} → (Int → Set) → Exp P → Set
ExpP {P} Q e = ∀ {φ} {{pφ : P φ}} → WhenJust Q (eval φ e)

infixl 6 _⊕_ _⊝_
infixl 7 _⊛_ _divE_ _modE_

data Exp P where
  var : Nat → Exp P
  undef : Exp P
  reg : Reg → Exp P
  imm : Int → Exp P
  _⊕_ _⊝_ _⊛_ _divE_ _modE_ : Exp P → Exp P → Exp P
  iterE : (n : Exp P) (x : Nat) (f z : Exp P) → Exp P
  -- iterate n (λ x → f) z

evalFun : ∀ {P} (φ : Env) {{_ : P φ}} → Nat → Exp P → Maybe (Int → Int)

eval φ (var _) = nothing
eval φ undef   = nothing
eval φ (reg r) = just (φ r)
eval φ (imm n) = just n
eval φ (e ⊕ e₁) = (| eval φ e + eval φ e₁ |)
eval φ (e ⊝ e₁) = (| eval φ e - eval φ e₁ |)
eval φ (e ⊛ e₁) = (| eval φ e * eval φ e₁ |)
eval φ (e divE e₁) = (| eval φ e quot′ eval φ e₁ |)
eval φ (e modE e₁) = (| eval φ e rem′ eval φ e₁ |)
eval φ (iterE n x f z) = (| iterInt (eval φ n) (evalFun φ x f) (eval φ z) |)

evalFun φ x (var y) = ifYes x == y then just id else nothing
evalFun φ x undef = nothing
evalFun φ x (reg r) = just λ _ → φ r
evalFun φ x (imm n) = just λ _ → n
evalFun φ x (f ⊕ f₁) = (| (λ f g n → f n + g n) (evalFun φ x f) (evalFun φ x f₁) |)
evalFun φ x (f ⊝ f₁) = (| (λ f g n → f n - g n) (evalFun φ x f) (evalFun φ x f₁) |)
evalFun φ x (f ⊛ f₁) = (| (λ f g n → f n * g n) (evalFun φ x f) (evalFun φ x f₁) |)
evalFun φ x (f divE f₁) = (| (λ f g n → f n quot′ g n) (evalFun φ x f) (evalFun φ x f₁) |)
evalFun φ x (f modE f₁) = (| (λ f g n → f n rem′  g n) (evalFun φ x f) (evalFun φ x f₁) |)
evalFun φ x (iterE n y f z) = nothing -- TODO: nested loops
-- (| (λ n f z i → iterInt (n i) (f i) (z i)) (evalFun φ x n) nothing (evalFun φ x z) |)

infix 2 _⊑ᵉ_ _⊑ˡ_

_⊑ᵉ_ : ∀ {P} → Exp P → Exp P → Set
undef ⊑ᵉ _  = ⊤
e     ⊑ᵉ e₁ = e ≡ e₁

_⊑ˡ_ : ∀ {P} → List (Exp P) → List (Exp P) → Set
[] ⊑ˡ _ = ⊤
x ∷ xs ⊑ˡ [] = ⊥
x ∷ xs ⊑ˡ y ∷ ys = (x ⊑ᵉ y) ∧ (xs ⊑ˡ ys)

nogo-l : (_∙_ : Int → Int → Int) (a b : Maybe Int) → a ≡ nothing → (| a ∙ b |) ≡ nothing
nogo-l _∙_ a b refl = refl

nogo-r : (_∙_ : Int → Int → Int) (a b : Maybe Int) → b ≡ nothing → (| a ∙ b |) ≡ nothing
nogo-r _∙_ nothing  _ _    = refl
nogo-r _∙_ (just _) b refl = refl

nz-cong : {A : Set} {P : A → Set} {{_ : ∀ {x} → Smashed (P x)}} (f : ∀ (x : A) {{_ : P x}} → A → A) →
          ∀ a b c d {{_ : P a}} {{_ : P c}} → a ≡ c → b ≡ d → f a b ≡ f c d
nz-cong f a b c d refl refl = (λ nz → f a {{nz}} b) $≡ smashed

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
norm φ (var _) = nothing
norm φ undef = nothing
norm φ (reg r) = φ r
norm φ (imm n) = just (n ∷ [])
norm φ (e ⊕ e₁) = (| norm φ e +n norm φ e₁ |)
norm φ (e ⊝ e₁) = (| norm φ e -n norm φ e₁ |)
norm φ (e ⊛ e₁) = (| norm φ e *n norm φ e₁ |)
norm φ (e divE e₁) = nothing    -- this is used for register preservation:
norm φ (e modE e₁) = nothing  -- we don't allow div and mod for that
norm φ (iterE _ _ _ _) = nothing

pattern %rax = reg rax
pattern %rcx = reg rcx
pattern %rdx = reg rdx
pattern %rbx = reg rbx
pattern %rsp = reg rsp
pattern %rbp = reg rbp
pattern %rsi = reg rsi
pattern %rdi = reg rdi

sameExp : ∀ {P} (a b : Exp P) → Maybe (a ≡ b)
sameExp (var x) (var y) = (λ e → var $≡ e) <$> maybeYes (x == y)
sameExp (imm x) (imm y) = (λ e → imm $≡ e) <$> maybeYes (x == y)
sameExp (reg r) (reg s) = (λ e → reg $≡ e) <$> maybeYes (r == s)
sameExp _ _ = nothing

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
  _+_ {{SemiringExp}} a (b ⊕ c) = (a + b) ⊕ c
  _+_ {{SemiringExp}} a (b ⊝ c) = (a + b) ⊝ c
  _+_ {{SemiringExp}} (imm (pos 0)) b = b
  _+_ {{SemiringExp}} (a ⊝ imm b) (imm c) = a + imm (c - b)
  _+_ {{SemiringExp}} (a ⊝ b) b′ = maybe (a ⊝ b ⊕ b′) (λ _ → a) (sameExp b b′)
  _+_ {{SemiringExp}} a b = a ⊕ b
  _*_ {{SemiringExp}} (imm (pos 0)) b = imm (pos 0)
  _*_ {{SemiringExp}} a (imm (pos 0)) = imm (pos 0)
  _*_ {{SemiringExp}} a b = a ⊛ b

  SubExp : ∀ {P} → Subtractive (Exp P)
  _-_    {{SubExp}} (a ⊕ imm b) (imm c) = a + imm (b - c)
  _-_    {{SubExp}} (a ⊝ imm b) (imm c) = a - imm (b + c)
  _-_    {{SubExp}} a (b ⊕ c) = (a - b) ⊝ c
  _-_    {{SubExp}} a (b ⊝ c) = (a - b) ⊕ c
  _-_    {{SubExp}} (a ⊕ b) b′ = maybe (a ⊕ b ⊝ b′) (λ _ → a) (sameExp b b′)
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
  showsPrec {{ShowExp}} p (var i) = showString "x" ∘ shows i
  showsPrec {{ShowExp}} p undef = showString "undef"
  showsPrec {{ShowExp}} p (reg r) = shows r
  showsPrec {{ShowExp}} p (imm n) = shows n
  showsPrec {{ShowExp}} p (e ⊕ e₁) = showParen (p >? 6) (showsPrec 6 e ∘ showString " + " ∘ showsPrec 7 e₁)
  showsPrec {{ShowExp}} p (e ⊝ e₁) = showParen (p >? 6) (showsPrec 6 e ∘ showString " - " ∘ showsPrec 7 e₁)
  showsPrec {{ShowExp}} p (e ⊛ e₁) = showParen (p >? 7) (showsPrec 7 e ∘ showString " * " ∘ showsPrec 8 e₁)
  showsPrec {{ShowExp}} p (e divE e₁) = showParen (p >? 7) (showsPrec 7 e ∘ showString " / " ∘ showsPrec 8 e₁)
  showsPrec {{ShowExp}} p (e modE e₁) = showParen (p >? 7) (showsPrec 7 e ∘ showString " % " ∘ showsPrec 8 e₁)
  showsPrec {{ShowExp}} p (iterE n x f z) =
    showParen (p >? 9) (showString "iterE " ∘ showsPrec 10 n ∘
                        showString " (λ x" ∘ shows x ∘ showString " → " ∘ showsPrec 0 f ∘ showString " )" ∘
                        showsPrec 10 z)

{-# TERMINATING #-}
subst : ∀ {P} → Nat → Exp P → Exp P → Exp P

iterE' : ∀ {P} → Exp P → Nat → Exp P → Exp P → Exp P
iterE' (imm (pos 0)) _ _ z = z
iterE' (a ⊕ imm (pos 1)) x f z = subst x (iterE a x f z) f
iterE' n x f z = iterE n x f z

-- data SubstLem {P} Q i (u v : Exp P) : Set where
--   notFree : subst i u v ≡ v → SubstLem i u v
--   free    : (∀ {φ} {{pφ : P φ}} → eval φ v ≡ nothing) → SubstLem i u v

-- substLem : ∀ {P} i (u v : Exp P) → SubstLem i u v

postulate -- TODO
  substCor : ∀ {P Q} i (u v : Exp P) {{pv : ExpP Q v}} → ExpP Q (subst i u v)
-- substCor i u v {{pv}} {φ} with substLem i u v | pv {φ} {{it}}
-- ... | notFree nop | _   = {!!}
-- ... | free nogo   | pvφ rewrite nogo {φ} {{it}} = ⊥-elim pvφ

subst i u (var j) = ifYes i == j then u else var j
subst i u undef = undef
subst i u (reg r) = reg r
subst i u (imm x) = imm x
subst i u (v ⊕ v₁) = subst i u v + subst i u v₁
subst i u (v ⊝ v₁) = subst i u v - subst i u v₁
subst i u (v ⊛ v₁) = subst i u v * subst i u v₁
subst i u (v divE v₁) = subst i u v divE subst i u v₁
subst i u (v modE v₁) = subst i u v modE subst i u v₁
subst i u (iterE n x f b) =
  -- TODO: capture avoidance!
  iterE' (subst i u n) x (subst i u f) (subst i u b)

-- substLem i u (var j) with i == j | notFree {i = i} {u} {var j}
-- ... | yes _ | _  = free refl
-- ... | no  _ | nf = nf refl
-- substLem i u undef   = notFree refl
-- substLem i u (reg r) = notFree refl
-- substLem i u (imm x) = notFree refl
-- substLem i u (v ⊕ v₁) with substLem i u v | substLem i u v₁
-- ... | notFree eqv | notFree eqv₁ = notFree (_⊕_ $≡ eqv *≡ eqv₁)
-- ... | free p | _ = free (λ {φ} → nogo-l _+Z_ (eval φ v) (eval φ v₁) (p {φ}))
-- ... | _ | free p = free (λ {φ} → nogo-r _+Z_ (eval φ v) (eval φ v₁) (p {φ}))
-- substLem i u (v ⊝ v₁) with substLem i u v | substLem i u v₁
-- ... | notFree eqv | notFree eqv₁ = notFree (_⊝_ $≡ eqv *≡ eqv₁)
-- ... | free p | _ = free (λ {φ} → nogo-l _-Z_ (eval φ v) (eval φ v₁) (p {φ}))
-- ... | _ | free p = free (λ {φ} → nogo-r _-Z_ (eval φ v) (eval φ v₁) (p {φ}))
-- substLem i u (v ⊛ v₁) with substLem i u v | substLem i u v₁
-- ... | notFree eqv | notFree eqv₁ = notFree (_⊛_ $≡ eqv *≡ eqv₁)
-- ... | free p | _ = free (λ {φ} → nogo-l _*Z_ (eval φ v) (eval φ v₁) (p {φ}))
-- ... | _ | free p = free (λ {φ} → nogo-r _*Z_ (eval φ v) (eval φ v₁) (p {φ}))
-- substLem i u (divE-by v {{nzv}} v₁) with substLem i u v | substLem i u v₁
-- ... | notFree eqv | notFree eqv₁ = notFree (nz-cong {{{!!}}} divE-by (subst i u v) (subst i u v₁) v v₁ eqv eqv₁)
-- ... | _ | _ = {!!}
-- substLem i u (modE-by v v₁) = {!!}



loopInv : ∀ {P} → Nat → (Exp P → Exp P) → Exp P → Exp P
loopInv l f z = iterE (var l) (suc l) (f (var (suc l))) z
