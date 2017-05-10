
module X86.Typed where

open import Prelude hiding (IsJust; fromJust)
open import Container.Path
open import Numeric.Nat.Divide

open import X86.Common
import X86.Untyped as Untyped
open Untyped using (ret; mov; add; sub; imul; idiv; push; pop)

data IsJust {A : Set} : Maybe A → Set where
  instance just : ∀ x → IsJust (just x)

fromJust : ∀ {A} {m : Maybe A} → IsJust m → A
fromJust (just x) = x

_≃_ : Exp → Exp → Set
e ≃ e₁ = ∀ φ → eval (just ∘ φ) e ≡ eval (just ∘ φ) e₁

record Obligation (t s : String) {P : Set} : Set where
  instance constructor proof
  field {{getProof}} : P

record S : Set where
  field
    [rax] [rcx] [rdx] [rbx] [rsp] [rbp] [rsi] [rdi] : Exp
    stack : List Exp
    isRet : Bool

open S public

get : Val → S → Exp
get %rax s = [rax] s
get %rcx s = [rcx] s
get %rdx s = [rdx] s
get %rbx s = [rbx] s
get %rsp s = [rsp] s
get %rbp s = [rbp] s
get %rsi s = [rsi] s
get %rdi s = [rdi] s
get (imm n) _ = imm n

getD : Dst → S → Exp
getD (reg r) s = get (reg r) s

set : Dst → Exp → S → S
set %rax e s = record s { [rax] = e }
set %rcx e s = record s { [rcx] = e }
set %rdx e s = record s { [rdx] = e }
set %rbx e s = record s { [rbx] = e }
set %rsp e s = record s { [rsp] = e }
set %rbp e s = record s { [rbp] = e }
set %rsi e s = record s { [rsi] = e }
set %rdi e s = record s { [rdi] = e }

getStackOffs : Exp → Maybe Nat
getStackOffs sp =
  case norm (singleRegEnv rsp) sp of λ where
    (just (pos 0 ∷ pos 1 ∷ [])) → just 0
    -- sp = %rsp - n
    (just (negsuc n ∷ pos 1 ∷ [])) →
      case 8 divides? (suc n) of λ where
        (yes (factor q eq)) → just q
        (no  _) → nothing
    _ → nothing

getStackElem : Exp → List Exp → Maybe Exp
getStackElem sp st =
  case getStackOffs sp of λ where
    (just (suc n)) → index st n
    _              → nothing

data PopPre (s : S) : Set where
  instance popPre : isRet s ≡ false →
                    IsJust (getStackElem (get %rsp s) (stack s)) →
                    PopPre s

storeNth : {A : Set} → Nat → A → A → List A → List A
storeNth zero _ y []          = y ∷ []
storeNth zero _ y (x ∷ xs)    = y ∷ xs
storeNth (suc n) z y []       = z ∷ storeNth n z y []
storeNth (suc n) z y (x ∷ xs) = x ∷ storeNth n z y xs

store : (s : S) → IsJust (getStackOffs (get %rsp s)) → Exp → List Exp
store s j e = storeNth (fromJust j) undef e (stack s)

ret-next : S → S
ret-next s = record s { isRet = true }

mov-next : Val → Dst → S → S
mov-next src dst s = set dst (get src s) s

add-next : Val → Dst → S → S
add-next src dst s = set dst (getD dst s + get src s) s

sub-next : Val → Dst → S → S
sub-next src dst s = set dst (getD dst s - get src s) s

imul-next : Val → Dst → S → S
imul-next src dst s = set dst (getD dst s * get src s) s

idiv-next : (val : Dst) (s : S) {{_ : NonZeroE (getD val s)}} → S
idiv-next val s =
  set %rdx (get %rax s modE getD val s) $
  set %rax (get %rax s divE getD val s) s

push-next : (val : Val) (s : S) {{_ : IsJust (getStackOffs (get %rsp s))}} → S
push-next v s {{pre}} =
  record s { stack = store s pre (get v s)
           ; [rsp] = [rsp] s - 8 }

pop-next : (dst : Dst) (s : S) {{_ : IsJust (getStackElem (get %rsp s) (stack s))}} → S
pop-next dst s {{pre}} =
  record (set dst (fromJust pre) s) { [rsp] = [rsp] s + 8 }

NonZeroObligation : Exp → Set
NonZeroObligation e =
  Obligation "Division by zero" ("Show that " & show e & " is nonzero.")
             {NonZeroE e}

PushObligation : Exp → Set
PushObligation e =
  Obligation "Push"
             ("Show that " & show e & " is a valid stack pointer.")
             {IsJust (getStackOffs e)}

PopObligation : Exp → List Exp → Set
PopObligation e xs =
  Obligation "Pop"
             ("Show that " & show e & " points to an element on the stack " & show xs & ".")
             {IsJust (getStackElem e xs)}

data Instr (s : S) : S → Set where

  ret  : {{pre : isRet s ≡ false}} →
         Instr s (ret-next s)

  mov  : (src : Val) (dst : Dst)
         {{pre : isRet s ≡ false}} →
         Instr s (mov-next src dst s)

  add  : (src : Val) (dst : Dst)
         {{pre : isRet s ≡ false}} →
         Instr s (add-next src dst s)

  sub  : (src : Val) (dst : Dst)
         {{pre : isRet s ≡ false}} →
         Instr s (sub-next src dst s)

  imul : (src : Val) (dst : Dst)
         {{pre : isRet s ≡ false}} →
         Instr s (imul-next src dst s)

  idiv : (val : Dst)
         {{notret : isRet s ≡ false}}
         {{nonz   : NonZeroObligation (getD val s)}}
         {{notrdx : isYes (val == %rdx) ≡ false}} →
         Instr s (idiv-next val s)

  push : (val : Val)
         {{notret : isRet s ≡ false}} →
         {{okrsp  : PushObligation (get %rsp s)}} →
         Instr s (push-next val s)

  pop  : (dst : Dst)
         {{notret : isRet s ≡ false}}
         {{okrsp  : PopObligation (get %rsp s) (stack s)}} →
         Instr s (pop-next dst s)

X86Code = Path Instr

eraseInstr : ∀ {i j} → Instr i j → Untyped.Instr
eraseInstr ret = ret
eraseInstr (mov src dst)  = mov src dst
eraseInstr (add src dst)  = add src dst
eraseInstr (sub src dst)  = sub src dst
eraseInstr (imul val dst) = imul val dst
eraseInstr (idiv val)     = idiv val
eraseInstr (push val)     = push val
eraseInstr (pop dst)      = pop dst

erase : ∀ {i j} → X86Code i j → Untyped.X86Code
erase = foldPath (_∷_ ∘ eraseInstr) []

initialState : S
[rax] initialState = %rax
[rcx] initialState = %rcx
[rdx] initialState = %rdx
[rbx] initialState = %rbx
[rsp] initialState = %rsp
[rbp] initialState = %rbp
[rsi] initialState = %rsi
[rdi] initialState = %rdi
stack initialState = []
isRet initialState = false

funEnv : Int → Reg → Maybe Int
funEnv n rdi = just n
funEnv _ _   = nothing

_isReg_ : Exp → Reg → Set
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

_isFun_ : Exp → (Int → Int → Int) → Set
e isFun f =
  ∀ {x y vax vcx vdx vbx vsp vbp} →
    eval (just ∘ mkEnv vax vcx vdx vbx vsp vbp y x) e ≡ just (f x y)

data X86Fun (f : Int → Int → Int) : Set where
  mkFun : ∀ {s : S}
            -- {{sem : ∀ {n} → eval (funEnv n) ([rax] s) ≡ just (f n)}} →
            -- {{sem : ∀ {φ} → eval (just ∘ φ) ([rax] s) ≡ just (f (φ rdi))}} →
            {{sem  : [rax] s isFun f}} →
            {{prbx : [rbx] s isReg rbx}} →
            {{prsp : [rsp] s isReg rsp}} →
            {{prbp : [rbp] s isReg rbp}} →
            X86Code initialState s → X86Fun f
