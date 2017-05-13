
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

data PosInt : Int → Set where
  instance mkPosInt : ∀ {n} → PosInt (pos (suc n))

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

{-# TERMINATING #-} -- ugh
substS : ∀ {P} → Label → Exp P → S P → S P
[rax] (substS i e s) = subst i e ([rax] s)
[rdx] (substS i e s) = subst i e ([rcx] s)
[rcx] (substS i e s) = subst i e ([rdx] s)
[rbx] (substS i e s) = subst i e ([rbx] s)
[rsp] (substS i e s) = subst i e ([rsp] s)
[rbp] (substS i e s) = subst i e ([rbp] s)
[rsi] (substS i e s) = subst i e ([rsi] s)
[rdi] (substS i e s) = subst i e ([rdi] s)
stack (substS i e s) = map (subst i e) (stack s)
labels (substS i e s) = map (substS i e) (labels s)
isRet (substS i e s) = isRet s

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

data PopPre {P} (s : S P) : Set where
  instance popPre : isRet s ≡ false →
                    IsJust (getStackElem (get %rsp s) (stack s)) →
                    PopPre s

storeNth : {A : Set} → Nat → A → A → List A → List A
storeNth zero _ y []          = y ∷ []
storeNth zero _ y (x ∷ xs)    = y ∷ xs
storeNth (suc n) z y []       = z ∷ storeNth n z y []
storeNth (suc n) z y (x ∷ xs) = x ∷ storeNth n z y xs

store : ∀ {P} (s : S P) → IsJust (getStackOffs (get %rsp s)) → Exp P → List (Exp P)
store s j e = storeNth (fromJust j) undef e (stack s)

ret-next : ∀ {P} → S P → S P
ret-next s = record s { isRet = true }

mov-next : ∀ {P} → Val → Dst → S P → S P
mov-next src dst s = set dst (get src s) s

add-next : ∀ {P} → Val → Dst → S P → S P
add-next src dst s = set dst (getD dst s + get src s) s

sub-next : ∀ {P} → Val → Dst → S P → S P
sub-next src dst s = set dst (getD dst s - get src s) s

imul-next : ∀ {P} → Val → Dst → S P → S P
imul-next src dst s = set dst (getD dst s * get src s) s

NonZeroObligation : ∀ {P} → Exp P → Set
NonZeroObligation e =
  Obligation "Division by zero" ("Show that " & show e & " is nonzero.")
             {ExpP NonZeroInt e}

idiv-next : ∀ {P} (val : Dst) (s : S P) {{_ : ExpP NonZeroInt (getD val s)}} → S P
idiv-next val s =
  set %rdx (get %rax s modE getD val s) $
  set %rax (get %rax s divE getD val s) s

PushObligation : ∀ {P} → Exp P → Set
PushObligation e =
  Obligation "Push"
             ("Show that " & show e & " is a valid stack pointer.")
             {IsJust (getStackOffs e)}

push-next : ∀ {P} (val : Val) (s : S P) {{_ : IsJust (getStackOffs (get %rsp s))}} → S P
push-next v s {{pre}} =
  record s { stack = store s pre (get v s)
           ; [rsp] = [rsp] s - 8 }

PopObligation : ∀ {P} → Exp P → List (Exp P) → Set
PopObligation e xs =
  Obligation "Pop"
             ("Show that " & show e & " points to an element on the stack " & show xs & ".")
             {IsJust (getStackElem e xs)}

pop-next : ∀ {P} (dst : Dst) (s : S P) {{_ : IsJust (getStackElem (get %rsp s) (stack s))}} → S P
pop-next dst s {{pre}} =
  record (set dst (fromJust pre) s) { [rsp] = [rsp] s + 8 }


LabelObligation : ∀ {P} → Exp P → Set
LabelObligation e =
  Obligation "Positive loop counter" ("Show that " & show e & " > 0.")
             {ExpP PosInt e}

label-next : ∀ {P} (wk : S P → S P) → S P → S P
label-next wk s = record s₁ { labels = labels s₁ ++ s₁ ∷ [] }
  where
    l  = length (labels s)
    s₁ = set %rcx (var l) (wk s)

LoopObligation : ∀ {P} → Label → S P → Set
LoopObligation l s =
  case index (labels s) l of λ where
    nothing → Error "Loop" ("Label " & show l & " is not defined.")
    (just s₁) →
      Obligation "Loop" "Show that the loop body preserves the invariant."
                 {s₁ ⊑ s} -- TODO: better message

loop-next : ∀ {P} → (l : Nat) (s : S P) {{_ : LoopObligation l s}} → S P
loop-next l s = set %rcx 0 (substS l (imm 1) s)

Precondition : Set₁
Precondition = Int → Int → Set

EnvPrecondition : Precondition → Env → Set
EnvPrecondition P φ = P (φ rdi) (φ rsi)

data Instr (P : Env → Set) (s : S P) : S P → Set where

  ret  : {{notret : isRet s ≡ false}} →
         Instr P s (ret-next s)

  mov  : (src : Val) (dst : Dst)
         {{notret : isRet s ≡ false}} →
         Instr P s (mov-next src dst s)

  add  : (src : Val) (dst : Dst)
         {{notret : isRet s ≡ false}} →
         Instr P s (add-next src dst s)

  sub  : (src : Val) (dst : Dst)
         {{notret : isRet s ≡ false}} →
         Instr P s (sub-next src dst s)

  imul : (src : Val) (dst : Dst)
         {{notret : isRet s ≡ false}} →
         Instr P s (imul-next src dst s)

  idiv : (val : Dst)
         {{notret : isRet s ≡ false}}
         {{nonz   : NonZeroObligation (getD val s)}}
         {{notrdx : isYes (val == %rdx) ≡ false}} →
         Instr P s (idiv-next val s)

  push : (val : Val)
         {{notret : isRet s ≡ false}} →
         {{okrsp  : PushObligation (get %rsp s)}} →
         Instr P s (push-next val s)

  pop  : (dst : Dst)
         {{notret : isRet s ≡ false}}
         {{okrsp  : PopObligation (get %rsp s) (stack s)}} →
         Instr P s (pop-next dst s)

  label : {{_ : LabelObligation (get %rcx s)}} →
          (wk : S P → S P)
          {{_ : wk s ⊑ s}} →
          Instr P s (label-next wk s)

  loop : (l : Label)
         {{notret : isRet s ≡ false}}
         {{okloop : LoopObligation l s}} →
         Instr P s (loop-next l s)

X86Code : (P : Env → Set) → S P → S P → Set
X86Code P = Path (Instr P)

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

initialState : ∀ {P} → S P
[rax]  initialState = %rax
[rcx]  initialState = %rcx
[rdx]  initialState = %rdx
[rbx]  initialState = %rbx
[rsp]  initialState = %rsp
[rbp]  initialState = %rbp
[rsi]  initialState = %rsi
[rdi]  initialState = %rdi
stack  initialState = []
labels initialState = []
isRet  initialState = false

initS = initialState

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

_isFun_ : ∀ {P : Precondition} → Exp (EnvPrecondition P) → (∀ x y {{_ : P x y}} → Int) → Set
_isFun_ {P} e f =
  ∀ {x y vax vcx vdx vbx vsp vbp} {{_ : P x y}} →
    eval (mkEnv vax vcx vdx vbx vsp vbp y x) e ≡ just (f x y)

data X86Fun (P : Precondition) (f : (x y : Int) {{_ : P x y}} → Int) : Set where
  mkFun : ∀ {s : S (EnvPrecondition P)}
            {{sem  : [rax] s isFun f}} →
            {{prbx : [rbx] s isReg rbx}} →
            {{prsp : [rsp] s isReg rsp}} →
            {{prbp : [rbp] s isReg rbp}} →
            {{isret : Obligation "Return" "Missing return from function."
                                 {isRet s ≡ true}}} →
            X86Code (EnvPrecondition P) initialState s → X86Fun P f

data X86Fun! (P : Precondition) : Set where
  mkFun : ∀ {s : S (EnvPrecondition P)}
            {{prbx : [rbx] s isReg rbx}} →
            {{prsp : [rsp] s isReg rsp}} →
            {{prbp : [rbp] s isReg rbp}} →
            {{isret : Obligation "Return" "Missing return from function."
                                 {isRet s ≡ true}}} →
            X86Code (EnvPrecondition P) initialState s → X86Fun! P
