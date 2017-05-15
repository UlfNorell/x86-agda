
module X86 where

open import Prelude
open import Text.Printf

open import X86.Common public

import X86.Typed
open X86.Typed public hiding (erase; eraseInstr)
open X86.Typed using (erase)

import X86.Untyped
import X86.Compile as C
open C using (MachineCode) public

compile : ∀ {P i j} → X86Code P i j → MachineCode
compile = C.compile ∘ erase

compileFun : ∀ {P f} → X86Fun P f → MachineCode
compileFun (mkFun code) = compile code

compileFun! : ∀ {P} → X86Fun! P → MachineCode
compileFun! (mkFun code) = compile code

showMachineCode : MachineCode → String
showMachineCode = foldr (printf "%02x %s") ""
