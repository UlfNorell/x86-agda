
module X86.Typed where

open import Prelude hiding (IsJust; fromJust)
open import Container.Path
open import Numeric.Nat.Divide

open import X86.Common
import X86.Untyped as Untyped
open Untyped using (ret; mov; add; sub; imul; push; pop)

data IsJust {A : Set} : Maybe A → Set where
  instance just : ∀ x → IsJust (just x)

fromJust : ∀ {A} {m : Maybe A} → IsJust m → A
fromJust (just x) = x

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

load : (s : S) → PopPre s → Exp
load s (popPre _ j) = fromJust j

data PushPre (s : S) : Set where
  instance pushPre : isRet s ≡ false →
                     IsJust (getStackOffs (get %rsp s)) →
                     PushPre s

storeNth : {A : Set} → Nat → A → A → List A → List A
storeNth zero _ y []          = y ∷ []
storeNth zero _ y (x ∷ xs)    = y ∷ xs
storeNth (suc n) z y []       = z ∷ storeNth n z y []
storeNth (suc n) z y (x ∷ xs) = x ∷ storeNth n z y xs

store : (s : S) → PushPre s → Exp → List Exp
store s (pushPre _ j) e = storeNth (fromJust j) undef e (stack s)

ret-pre : S → Set
ret-pre s = isRet s ≡ false

ret-next : S → S
ret-next s = record s { isRet = true }

mov-pre : Val → Dst → S → Set
mov-pre _ _ s = isRet s ≡ false

mov-next : Val → Dst → S → S
mov-next src dst s = set dst (get src s) s

add-pre : Val → Dst → S → Set
add-pre _ _ s = isRet s ≡ false

add-next : Val → Dst → S → S
add-next src dst s = set dst (getD dst s + get src s) s

sub-pre : Val → Dst → S → Set
sub-pre _ _ s = isRet s ≡ false

sub-next : Val → Dst → S → S
sub-next src dst s = set dst (getD dst s - get src s) s

imul-pre : Val → Dst → S → Set
imul-pre _ _ s = isRet s ≡ false

imul-next : Val → Dst → S → S
imul-next src dst s = set dst (getD dst s * get src s) s

push-pre : Val → S → Set
push-pre _ s = PushPre s

push-next : (val : Val) (s : S) {{_ : push-pre val s}} → S
push-next v s {{pre}} =
  record s { stack = store s pre (get v s)
           ; [rsp] = [rsp] s - 8 }

pop-pre : Dst → S → Set
pop-pre _ s = PopPre s

pop-next : (dst : Dst) (s : S) {{_ : pop-pre dst s}} → S
pop-next dst s {{pre}} =
  record (set dst (load s pre) s) { [rsp] = [rsp] s + 8 }

data Instr (s : S) : S → Set where
  ret  : {{pre : ret-pre s}} → Instr s (ret-next s)
  mov  : (src : Val) (dst : Dst) {{pre : mov-pre src dst s}} → Instr s (mov-next src dst s)
  add  : (src : Val) (dst : Dst) {{pre : add-pre src dst s}} → Instr s (add-next src dst s)
  sub  : (src : Val) (dst : Dst) {{pre : sub-pre src dst s}} → Instr s (sub-next src dst s)
  imul : (src : Val) (dst : Dst) {{pre : imul-pre src dst s}} → Instr s (imul-next src dst s)
  push : (val : Val) {{pre : push-pre val s}} → Instr s (push-next val s)
  pop  : (dst : Dst) {{pre : pop-pre dst s}} → Instr s (pop-next dst s)

X86Code = Path Instr

eraseInstr : ∀ {i j} → Instr i j → Untyped.Instr
eraseInstr ret = ret
eraseInstr (mov src dst)  = mov src dst
eraseInstr (add src dst)  = add src dst
eraseInstr (sub src dst)  = sub src dst
eraseInstr (imul val dst) = imul val dst
eraseInstr (push val)     = push val
eraseInstr (pop dst)      = pop dst

erase : ∀ {i j} → X86Code i j → Untyped.X86Code
erase = foldPath (_∷_ ∘ eraseInstr) []

initialState : S
[rax] initialState = %rax
[rcx] initialState = undef
[rdx] initialState = undef
[rbx] initialState = %rbx
[rsp] initialState = %rsp
[rbp] initialState = %rbp
[rsi] initialState = undef
[rdi] initialState = %rdi
stack initialState = []
isRet initialState = false

funEnv : Int → Reg → Maybe Int
funEnv n rdi = just n
funEnv _ _   = nothing

_isReg_ : Exp → Reg → Set
e isReg r = norm (singleRegEnv r) e ≡ just (0 ∷ 1 ∷ [])

data X86Fun (f : Int → Int) : Set where
  mkFun : ∀ {s : S}
            {{_ : ∀ {n} → eval (funEnv n) ([rax] s) ≡ just (f n)}} →
            {{_ : [rbx] s isReg rbx}} →
            {{_ : [rsp] s isReg rsp}} →
            {{_ : [rbp] s isReg rbp}} →
            X86Code initialState s → X86Fun f
