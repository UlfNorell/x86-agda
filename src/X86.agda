
module X86 where

open import Prelude

open import X86.Common public

import X86.Typed
open X86.Typed public hiding (erase; eraseInstr)
open X86.Typed using (erase)

import X86.Untyped
import X86.Compile as C
open C hiding (compile) public

compile : ∀ {i j} → X86Code i j → MachineCode
compile = C.compile ∘ erase
