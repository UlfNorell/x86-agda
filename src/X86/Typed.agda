
module X86.Typed where

open import Prelude hiding (IsJust; fromJust)
open import Container.Path
open import Numeric.Nat.Divide

open import X86.Common
import X86.Untyped as Untyped
open Untyped using (ret; mov; add; sub; imul; idiv; push; pop; label; loop)

data IsJust {A : Set} : Maybe A → Set where
  instance just : ∀ x → IsJust (just x)

fromJust : ∀ {A} {m : Maybe A} → IsJust m → A
fromJust (just x) = x

_≠_ : ∀ {a} {A : Set a} {{_ : Eq A}} → A → A → Set
x ≠ y = isYes (x == y) ≡ false

_≃_ : ∀ {P} → Exp P → Exp P → Set
_≃_ {P} e e₁ = ∀ φ {{_ : P φ}} → eval φ e ≡ eval φ e₁

record Obligation (t s : String) {P : Set} : Set where
  instance constructor proof
  field {{getProof}} : P

data Error (t s : String) : Set where





Label = Nat

record S P : Set where
  inductive
  no-eta-equality
  field
    [rax] [rcx] [rdx] [rbx] [rsp] [rbp] [rsi] [rdi] : Exp P
    stack  : List (Exp P)
    labels : List (S P)
    isRet  : Bool







open S public

initS : ∀ {P} → S P
[rax]  initS = %rax
[rcx]  initS = %rcx
[rdx]  initS = %rdx
[rbx]  initS = %rbx
[rsp]  initS = %rsp
[rbp]  initS = %rbp
[rsi]  initS = %rsi
[rdi]  initS = %rdi
stack  initS = []
labels initS = []
isRet  initS = false

record _⊑_ {P} (s₁ : S P) (s₂ : S P) : Set where
  instance constructor mkLeq
  field
    [rax]  : [rax] s₁ ⊑ᵉ [rax] s₂
    [rcx]  : [rcx] s₁ ⊑ᵉ [rcx] s₂
    [rdx]  : [rdx] s₁ ⊑ᵉ [rdx] s₂
    [rbx]  : [rbx] s₁ ⊑ᵉ [rbx] s₂
    [rsp]  : [rsp] s₁ ⊑ᵉ [rsp] s₂
    [rbp]  : [rbp] s₁ ⊑ᵉ [rbp] s₂
    [rsi]  : [rsi] s₁ ⊑ᵉ [rsi] s₂
    [rdi]  : [rdi] s₁ ⊑ᵉ [rdi] s₂
    stack  : stack s₁ ⊑ˡ stack s₂

substS : ∀ {P} → Label → Exp P → S P → S P
substS i e s =
  record s
    { [rax]  = subst i e ([rax] s)
    ; [rcx]  = subst i e ([rcx] s)
    ; [rdx]  = subst i e ([rdx] s)
    ; [rbx]  = subst i e ([rbx] s)
    ; [rsp]  = subst i e ([rsp] s)
    ; [rbp]  = subst i e ([rbp] s)
    ; [rsi]  = subst i e ([rsi] s)
    ; [rdi]  = subst i e ([rdi] s)
    ; stack  = map (subst i e) (stack s)
    ; labels = [] -- map (substS i e) (labels s)
    ; isRet  = isRet s }

-- [rax] (substS i e s) = subst i e ([rax] s)
-- [rcx] (substS i e s) = subst i e ([rcx] s)
-- [rdx] (substS i e s) = subst i e ([rdx] s)
-- [rbx] (substS i e s) = subst i e ([rbx] s)
-- [rsp] (substS i e s) = subst i e ([rsp] s)
-- [rbp] (substS i e s) = subst i e ([rbp] s)
-- [rsi] (substS i e s) = subst i e ([rsi] s)
-- [rdi] (substS i e s) = subst i e ([rdi] s)
-- stack (substS i e s) = map (subst i e) (stack s)
-- labels (substS i e s) = map (substS i e) (labels s)
-- isRet (substS i e s) = isRet s

get : ∀ {P} → Val → S P → Exp P
get %rax s = [rax] s
get %rcx s = [rcx] s
get %rdx s = [rdx] s
get %rbx s = [rbx] s
get %rsp s = [rsp] s
get %rbp s = [rbp] s
get %rsi s = [rsi] s
get %rdi s = [rdi] s
get (imm n) _ = imm n

getD : ∀ {P} → Dst → S P → Exp P
getD (reg r) s = get (reg r) s

set : ∀ {P} → Dst → Exp P → S P → S P
set %rax e s = record s { [rax] = e }
set %rcx e s = record s { [rcx] = e }
set %rdx e s = record s { [rdx] = e }
set %rbx e s = record s { [rbx] = e }
set %rsp e s = record s { [rsp] = e }
set %rbp e s = record s { [rbp] = e }
set %rsi e s = record s { [rsi] = e }
set %rdi e s = record s { [rdi] = e }











getStackOffs : ∀ {P} → Exp P → Maybe Nat
getStackOffs sp =
  case norm (singleRegEnv rsp) sp of λ where
    (just (pos 0 ∷ pos 1 ∷ [])) → just 0
    -- sp = %rsp - n
    (just (negsuc n ∷ pos 1 ∷ [])) →
      case 8 divides? (suc n) of λ where
        (yes (factor q eq)) → just q
        (no  _) → nothing
    _ → nothing





getStackElem : ∀ {P} → Exp P → List (Exp P) → Maybe (Exp P)
getStackElem sp st =
  case getStackOffs sp of λ where
    (just (suc n)) → index st n
    _              → nothing

storeNth : {A : Set} → Nat → A → A → List A → List A
storeNth zero _ y []          = y ∷ []
storeNth zero _ y (x ∷ xs)    = y ∷ xs
storeNth (suc n) z y []       = z ∷ storeNth n z y []
storeNth (suc n) z y (x ∷ xs) = x ∷ storeNth n z y xs

data Instr (P : Env → Set) (s : S P) : S P → Set

-- ret --

ret-next : ∀ {P} → S P → S P
ret-next s = record s { isRet = true }

RetType : ∀ P → S P → Set
RetType P s =
  {{notret : isRet s ≡ false}} →
  Instr P s (ret-next s)

-- mov --

mov-next : ∀ {P} → Val → Dst → S P → S P
mov-next src dst s = set dst (get src s) s

MovType : ∀ P → S P → Set
MovType P s =
  (src : Val) (dst : Dst)
  {{notret : isRet s ≡ false}} →
  Instr P s (mov-next src dst s)





-- add/sub/imul --

op-next : ∀ {P} → (Exp P → Exp P → Exp P) → Val → Dst → S P → S P
op-next _∙_ src dst s = set dst (getD dst s ∙ get src s) s

OpType : ∀ P → (Exp P → Exp P → Exp P) → S P → Set
OpType P _∙_ s =
  (src : Val) (dst : Dst)
  {{notret : isRet s ≡ false}} →
  Instr P s (op-next _∙_ src dst s)







-- idiv --

DivisionByZero : ∀ {P} → Exp P → Set
DivisionByZero e =
  Obligation "Division by zero" ("Show that " & show e & " is nonzero.")
             {ExpP NonZeroInt e}

idiv-next : ∀ {P} (val : Dst) (s : S P) {{_ : ExpP NonZeroInt (getD val s)}} → S P
idiv-next val s =
  set %rdx (get %rax s modE getD val s) $
  set %rax (get %rax s divE getD val s) s

DivType : ∀ P → S P → Set
DivType P s =
  (val : Dst)
  {{notret : isRet s ≡ false}}
  {{nonz   : DivisionByZero (getD val s)}}
  {{notrdx : val ≠ %rdx}} →
  Instr P s (idiv-next val s)






-- push --

ValidStackPtr : ∀ {P} → Exp P → Set
ValidStackPtr e =
  Obligation "Push" ("Show that " & show e & " is a valid stack pointer.")
             {IsJust (getStackOffs e)}

push-next : ∀ {P} (val : Val) (s : S P) {{_ : IsJust (getStackOffs (get %rsp s))}} → S P
push-next v s {{pre}} =
  record s { stack = storeNth (fromJust pre) undef (get v s) (stack s)
           ; [rsp] = [rsp] s - 8 }

PushType : ∀ P → S P → Set
PushType P s =
  (val : Val)
  {{notret : isRet s ≡ false}}
  {{okrsp  : ValidStackPtr (get %rsp s)}} →
  Instr P s (push-next val s)



-- pop --

ValidStackElem : ∀ {P} → Exp P → List (Exp P) → Set
ValidStackElem e xs =
  Obligation "Pop"
             ("Show that " & show e & " points to an element on the stack " & show xs & ".")
             {IsJust (getStackElem e xs)}

pop-next : ∀ {P} (dst : Dst) (s : S P) {{_ : IsJust (getStackElem (get %rsp s) (stack s))}} → S P
pop-next dst s {{pre}} =
  record (set dst (fromJust pre) s) { [rsp] = [rsp] s + 8 }

PopType : ∀ P → S P → Set
PopType P s =
  (dst : Dst)
  {{notret : isRet s ≡ false}}
  {{okrsp  : ValidStackElem (get %rsp s) (stack s)}} →
  Instr P s (pop-next dst s)


-- label --

PosLoopCounter : ∀ {P} → Exp P → Set
PosLoopCounter e =
  Obligation "Positive loop counter" ("Show that " & show e & " > 0.")
             {ExpP PosInt e}

getLabel : ∀ {P} → S P → Label
getLabel s = length (labels s)

label-next : ∀ {P} (l : Label) (wk : Label → S P → S P) → S P → S P
label-next l wk s = record s₁ { labels = labels s₁ ++ s₁ ∷ [] }
  where
    s₁ = set %rcx (get %rcx s - var l) (wk l s)

LabelType : ∀ P → S P → Set
LabelType P s =
  (wk : Label → S P → S P)
  (let l = getLabel s)
  {{okwk   : substS l 0 (wk l s) ⊑ s}} →
  {{posrcx : PosLoopCounter (get %rcx (wk l s))}} →
  Instr P s (label-next l wk s)




-- loop --

LoopObligation : ∀ {P} → Label → S P → Set
LoopObligation l s =
  case index (labels s) l of λ where
    nothing → Error "Loop" ("Label " & show l & " is not defined.")
    (just s₀) →
      Obligation "Loop" "Show that the loop body preserves the invariant."
                 {substS l (var l ⊕ 1) s₀ ⊑ set %rcx (get %rcx s - 1) s}
                 -- s₀ ⊑ %rcx-- s

loop-next : ∀ {P} → (l : Nat) (s : S P) {{_ : LoopObligation l s}} → S P
loop-next l s with index (labels s) l
loop-next l s {{}} | nothing
loop-next l s      | just s₀ = set %rcx 0 (substS l (get %rcx s₀ + var l) s₀)

LoopType : ∀ P → S P → Set
LoopType P s =
  (l : Label)
  {{notret : isRet s ≡ false}}
  {{okloop : LoopObligation l s}} →
  Instr P s (loop-next l s)

-- The instructions --

data Instr P s where

  ret  : RetType P s
  mov  : MovType P s

  add  : OpType P _+_ s
  sub  : OpType P _-_ s
  imul : OpType P _*_ s

  idiv : DivType P s

  push : PushType P s
  pop  : PopType P s

  label : LabelType P s
  loop  : LoopType P s


X86Code : (P : Env → Set) → S P → S P → Set
X86Code P = Path (Instr P)

-- Forgetting the types --

eraseInstr : ∀ {P i j} → Instr P i j → Untyped.Instr
eraseInstr ret = ret
eraseInstr (mov src dst)  = mov src dst
eraseInstr (add src dst)  = add src dst
eraseInstr (sub src dst)  = sub src dst
eraseInstr (imul val dst) = imul val dst
eraseInstr (idiv val)     = idiv val
eraseInstr (push val)     = push val
eraseInstr (pop dst)      = pop dst
eraseInstr (label _)      = label
eraseInstr (loop l)       = loop l

erase : ∀ {P i j} → X86Code P i j → Untyped.X86Code
erase = foldPath (_∷_ ∘ eraseInstr) []

Precondition : Set₁
Precondition = Int → Int → Set

OnEnv : Precondition → Env → Set
OnEnv P φ = P (φ rdi) (φ rsi)

X86Code' : (P : Precondition) → S (OnEnv P) → S (OnEnv P) → Set
X86Code' P = X86Code (OnEnv P)

funEnv : Int → Reg → Maybe Int
funEnv n rdi = just n
funEnv _ _   = nothing

_isReg_ : ∀ {P} → Exp P → Reg → Set
e isReg r =
  ifYes norm (singleRegEnv r) e == just (0 ∷ 1 ∷ [])
  then ⊤
  else Obligation ("Preservation of " & show r)
                  ("Show that " & show e & " ≡ " & show r & ".")
                  {e ≃ reg r}

mkEnv : (a b c d e f g h : Int) → Reg → Int
mkEnv a b c d e f g h rax = a
mkEnv a b c d e f g h rcx = b
mkEnv a b c d e f g h rdx = c
mkEnv a b c d e f g h rbx = d
mkEnv a b c d e f g h rsp = e
mkEnv a b c d e f g h rbp = f
mkEnv a b c d e f g h rsi = g
mkEnv a b c d e f g h rdi = h

_isFun_ : ∀ {P : Precondition} → Exp (OnEnv P) → (∀ x y {{_ : P x y}} → Int) → Set
_isFun_ {P} e f =
  ∀ {x y vax vcx vdx vbx vsp vbp} {{_ : P x y}} →
    eval (mkEnv vax vcx vdx vbx vsp vbp y x) e ≡ just (f x y)

-- Functions --

data X86Fun (P : Precondition) (f : (x y : Int) {{_ : P x y}} → Int) : Set where
  mkFun : ∀ {s : S (OnEnv P)}
            {{sem  : [rax] s isFun f}} →
            {{prbx : [rbx] s isReg rbx}} →
            {{prsp : [rsp] s isReg rsp}} →
            {{prbp : [rbp] s isReg rbp}} →
            {{isret : Obligation "Return" "Missing return from function."
                                 {isRet s ≡ true}}} →
            X86Code (OnEnv P) initS s → X86Fun P f






data X86Fun! (P : Precondition) : Set where
  mkFun : ∀ {s : S (OnEnv P)}
            {{prbx : [rbx] s isReg rbx}} →
            {{prsp : [rsp] s isReg rsp}} →
            {{prbp : [rbp] s isReg rbp}} →
            {{isret : Obligation "Return" "Missing return from function."
                                 {isRet s ≡ true}}} →
            X86Code (OnEnv P) initS s → X86Fun! P
