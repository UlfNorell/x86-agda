
module X86.Compile where

open import Prelude
open import X86.Common
open import X86.Untyped

Byte        = Nat
MachineCode = List Byte

regIx : Reg → Nat
regIx rax = 0
regIx rcx = 1
regIx rdx = 2
regIx rbx = 3
regIx rsp = 4
regIx rbp = 5
regIx rsi = 6
regIx rdi = 7

-- Little endian
bytesNat : Nat → Nat → MachineCode
bytesNat 0       n = []
bytesNat (suc w) n = n mod 256 ∷ bytesNat w (n div 256)

_mod′_ : Nat → Nat → Nat
a mod′ 0     = 0
a mod′ suc b = a mod suc b

bytes : Nat → Int → MachineCode
bytes w       (pos n)    = bytesNat w n
bytes 0       (negsuc n) = []
bytes (suc w) (negsuc n) =
  let max = 256 ^ w * 128 in
  bytesNat (suc w) (2 * max - (n + 1) mod′ max)

compileInstr : Instr → MachineCode

compileInstr ret = 0xc3 ∷ []

compileInstr (mov (reg src) (reg dst)) =
  0x48 ∷ 0x89 ∷ 0xc0 + 8 * regIx src + regIx dst ∷ []
compileInstr (mov (imm val) (reg dst)) =
  0x48 ∷ 0xc7 ∷ 0xc0 + regIx dst ∷ bytes 4 val

compileInstr (add (reg src) (reg dst)) =
  0x48 ∷ 0x01 ∷ 0xc0 + 8 * regIx src + regIx dst ∷ []
compileInstr (add (imm val) (reg dst)) =
  0x48 ∷ 0x81 ∷ 0xc0 + regIx dst ∷ bytes 4 val

compileInstr (sub (reg src) (reg dst)) =
  0x48 ∷ 0x29 ∷ 0xc0 + 8 * regIx src + regIx dst ∷ []
compileInstr (sub (imm val) (reg dst)) =
  0x48 ∷ 0x81 ∷ 0xe8 + regIx dst ∷ bytes 4 val

compileInstr (imul (reg src) (reg dst)) =
  0x48 ∷ 0x0f ∷ 0xaf ∷ 0xc0 + 8 * regIx dst + regIx src ∷ []
compileInstr (imul (imm val) (reg dst)) =
  0x48 ∷ 0x69 ∷ 0xc0 + 8 * regIx dst + regIx dst ∷ bytes 4 val

compileInstr (idiv (reg dst)) =
  0x48 ∷ 0xf7 ∷ 0xf0 + regIx dst ∷ []

compileInstr (push (reg r)) =
  0x50 + regIx r ∷ []
compileInstr (push (imm v)) =
  0x68 ∷ bytes 4 v

compileInstr (pop (reg r)) =
  0x58 + regIx r ∷ []

compile : X86Code → MachineCode
compile = concatMap compileInstr
