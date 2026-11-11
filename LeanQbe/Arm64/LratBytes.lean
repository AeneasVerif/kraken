module

public import LeanQbe.Arm64.Abi
public import LeanQbe.Arm64.Litmus
public import LeanQbe.Examples.LratBytes
public import LeanQbe.Examples.LratBytesLemmas
public import LeanQbe.MainLemmas
public import Kraken.AArch64.Parser
import all Kraken.Separation
import all Kraken.Mem

/-!
# End-to-end untrusted-bytes LRAT proof checker on AArch64 (`lrat_check_bytes`)

Compiles the six-function untrusted-bytes DIMACS + Binary LRAT checker module
`LratBytes.lratBytesFns` through `compileModule Arm64.isa`, verifies all 1,226 emitted AArch64
directives and per-function stack bounds in the kernel (`kernel_rfl`), and links against
`LratBytesLemmas` via `compile_sound`:
- `lrat_bytes_module_fnspec`: closed `FnSpec` for all 6 module functions on `Arm64.target`
- `lrat_check_bytes_arm64_correct`: ABI-preserving end-to-end Kraken-AArch64 theorem over
  arbitrary untrusted `cnfBytes`, `prfBytes`, and `region work_ptr work_len`
- `lrat_check_bytes_arm64_unsat`: trivial-postcondition corollary for encoded valid `CNF Nat`
  (`x0 ∈ {0, 1}` and `x0 = 1 → cnf.Unsat`)
- `lrat_check_bytes_arm64_accepts` / `lrat_check_bytes_arm64_rejects`: concrete machine-level
  non-vacuity witnesses on `lratBytesHost`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Arm64.LratBytes

open LeanQbe LeanQbe.LratBytes Arm64 Arm64.Litmus Kraken.AArch64 Kraken.AArch64.Parser
open Std.Sat

abbrev parseHeaderFn : Fn := ⟨"lb_parse_dimacs_header", lbParseDimacsHeader⟩
abbrev parseBodyFn : Fn := ⟨"lb_parse_dimacs_body", lbParseDimacsBody⟩
abbrev readAddLitsFn : Fn := ⟨"lb_read_add_lits", lbReadAddLits⟩
abbrev rupCheckFn : Fn := ⟨"lb_rup_check", lbRupCheck⟩
abbrev checkPrfFn : Fn := ⟨"lb_check_prf", lbCheckPrf⟩
abbrev lratCheckBytesFn : Fn := ⟨"lrat_check_bytes", lratCheckBytes⟩


def parseHeaderCode : Program := parseAArch64("lb_parse_dimacs_header:
  sub sp, sp, #16
  str x30, [sp]
  add x6, x2, #0
  lb_parse_dimacs_header.L2:
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L3
  ldrb w2, [x0]
  add x3, x0, #1
  subs xzr, x2, #32
  csinc w4, wzr, wzr, ne
  sub x5, x2, #9
  subs xzr, x5, #5
  csinc w5, wzr, wzr, cs
  orr x4, x4, x5
  cbnz w4, lb_parse_dimacs_header.L4
  subs xzr, x2, #99
  b.eq lb_parse_dimacs_header.L5
  b lb_parse_dimacs_header.L1
  lb_parse_dimacs_header.L5:
  add x0, x3, #0
  lb_parse_dimacs_header.L6:
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L7
  ldrb w2, [x0]
  add x0, x0, #1
  subs xzr, x2, #10
  b.eq lb_parse_dimacs_header.L8
  b lb_parse_dimacs_header.L6
  lb_parse_dimacs_header.L8:
  b lb_parse_dimacs_header.L2
  lb_parse_dimacs_header.L7:
  b lb_parse_dimacs_header.L1
  lb_parse_dimacs_header.L4:
  add x0, x3, #0
  b lb_parse_dimacs_header.L2
  lb_parse_dimacs_header.L3:
  lb_parse_dimacs_header.L1:
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L9
  ldrb w2, [x0]
  subs xzr, x2, #112
  b.eq lb_parse_dimacs_header.L10
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L10:
  add x0, x0, #1
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L11
  ldrb w2, [x0]
  subs xzr, x2, #32
  csinc w3, wzr, wzr, ne
  sub x2, x2, #9
  subs xzr, x2, #5
  csinc w2, wzr, wzr, cs
  orr x3, x3, x2
  cbnz w3, lb_parse_dimacs_header.L12
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L12:
  add x0, x0, #1
  lb_parse_dimacs_header.L14:
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L15
  ldrb w2, [x0]
  subs xzr, x2, #32
  csinc w3, wzr, wzr, ne
  sub x2, x2, #9
  subs xzr, x2, #5
  csinc w2, wzr, wzr, cs
  orr x3, x3, x2
  cbnz w3, lb_parse_dimacs_header.L16
  b lb_parse_dimacs_header.L13
  lb_parse_dimacs_header.L16:
  add x0, x0, #1
  b lb_parse_dimacs_header.L14
  lb_parse_dimacs_header.L15:
  lb_parse_dimacs_header.L13:
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L17
  ldrb w2, [x0]
  subs xzr, x2, #99
  b.eq lb_parse_dimacs_header.L18
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L18:
  add x2, x0, #1
  subs xzr, x2, x1
  b.eq lb_parse_dimacs_header.L19
  ldrb w2, [x2]
  subs xzr, x2, #110
  b.eq lb_parse_dimacs_header.L20
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L20:
  add x2, x0, #2
  subs xzr, x2, x1
  b.eq lb_parse_dimacs_header.L21
  ldrb w2, [x2]
  subs xzr, x2, #102
  b.eq lb_parse_dimacs_header.L22
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L22:
  add x0, x0, #3
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L23
  ldrb w2, [x0]
  subs xzr, x2, #32
  csinc w3, wzr, wzr, ne
  sub x2, x2, #9
  subs xzr, x2, #5
  csinc w2, wzr, wzr, cs
  orr x3, x3, x2
  cbnz w3, lb_parse_dimacs_header.L24
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L24:
  add x0, x0, #1
  lb_parse_dimacs_header.L26:
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L27
  ldrb w2, [x0]
  subs xzr, x2, #32
  csinc w3, wzr, wzr, ne
  sub x2, x2, #9
  subs xzr, x2, #5
  csinc w2, wzr, wzr, cs
  orr x3, x3, x2
  cbnz w3, lb_parse_dimacs_header.L28
  b lb_parse_dimacs_header.L25
  lb_parse_dimacs_header.L28:
  add x0, x0, #1
  b lb_parse_dimacs_header.L26
  lb_parse_dimacs_header.L27:
  lb_parse_dimacs_header.L25:
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L29
  ldrb w2, [x0]
  sub x2, x2, #48
  subs xzr, x2, #10
  b.cc lb_parse_dimacs_header.L30
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L30:
  add x0, x0, #1
  lb_parse_dimacs_header.L32:
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L33
  ldrb w3, [x0]
  sub x4, x3, #48
  subs xzr, x4, #10
  b.cc lb_parse_dimacs_header.L34
  subs xzr, x3, #32
  csinc w4, wzr, wzr, ne
  sub x3, x3, #9
  subs xzr, x3, #5
  csinc w3, wzr, wzr, cs
  orr x4, x4, x3
  cbnz w4, lb_parse_dimacs_header.L35
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L35:
  add x7, x2, #0
  b lb_parse_dimacs_header.L31
  lb_parse_dimacs_header.L34:
  ldr x17, =10
  madd x2, x2, x17, xzr
  add x2, x2, x4
  ldr x17, =268435456
  subs xzr, x2, x17
  b.cc lb_parse_dimacs_header.L36
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L36:
  add x0, x0, #1
  b lb_parse_dimacs_header.L32
  lb_parse_dimacs_header.L33:
  add x7, x2, #0
  lb_parse_dimacs_header.L31:
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L37
  ldrb w2, [x0]
  subs xzr, x2, #32
  csinc w3, wzr, wzr, ne
  sub x2, x2, #9
  subs xzr, x2, #5
  csinc w2, wzr, wzr, cs
  orr x3, x3, x2
  cbnz w3, lb_parse_dimacs_header.L38
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L38:
  add x0, x0, #1
  lb_parse_dimacs_header.L40:
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L41
  ldrb w2, [x0]
  subs xzr, x2, #32
  csinc w3, wzr, wzr, ne
  sub x2, x2, #9
  subs xzr, x2, #5
  csinc w2, wzr, wzr, cs
  orr x3, x3, x2
  cbnz w3, lb_parse_dimacs_header.L42
  b lb_parse_dimacs_header.L39
  lb_parse_dimacs_header.L42:
  add x0, x0, #1
  b lb_parse_dimacs_header.L40
  lb_parse_dimacs_header.L41:
  lb_parse_dimacs_header.L39:
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L43
  ldrb w2, [x0]
  sub x2, x2, #48
  subs xzr, x2, #10
  b.cc lb_parse_dimacs_header.L44
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L44:
  add x0, x0, #1
  lb_parse_dimacs_header.L46:
  subs xzr, x0, x1
  b.eq lb_parse_dimacs_header.L47
  ldrb w3, [x0]
  sub x4, x3, #48
  subs xzr, x4, #10
  b.cc lb_parse_dimacs_header.L48
  subs xzr, x3, #32
  csinc w1, wzr, wzr, ne
  sub x3, x3, #9
  subs xzr, x3, #5
  csinc w3, wzr, wzr, cs
  orr x1, x1, x3
  cbnz w1, lb_parse_dimacs_header.L49
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L49:
  b lb_parse_dimacs_header.L45
  lb_parse_dimacs_header.L48:
  ldr x17, =10
  madd x2, x2, x17, xzr
  add x2, x2, x4
  ldr x17, =268435456
  subs xzr, x2, x17
  b.cc lb_parse_dimacs_header.L50
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L50:
  add x0, x0, #1
  b lb_parse_dimacs_header.L46
  lb_parse_dimacs_header.L47:
  lb_parse_dimacs_header.L45:
  str x7, [x6]
  add x1, x6, #8
  str x2, [x1]
  add x6, x6, #72
  str x0, [x6]
  ldr x0, =1
  ldr x30, [sp]
  add sp, sp, #16
  ret
  lb_parse_dimacs_header.L43:
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L37:
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L29:
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L23:
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L21:
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L19:
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L17:
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L11:
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L9:
  lb_parse_dimacs_header.L0:
  ldr x0, =0
  ldr x30, [sp]
  add sp, sp, #16
  ret")

def parseBodyCode : Program := parseAArch64("lb_parse_dimacs_body:
  sub sp, sp, #16
  str x30, [sp]
  ldr x8, [x1]
  add x2, x1, #8
  ldr x10, [x2]
  add x2, x1, #48
  ldr x11, [x2]
  add x2, x1, #56
  ldr x12, [x2]
  add x13, x1, #64
  ldr x6, [x13]
  add x1, x1, #72
  ldr x1, [x1]
  ldr x3, =1
  lb_parse_dimacs_body.L1:
  subs xzr, x10, x3
  b.cc lb_parse_dimacs_body.L2
  add x2, x1, #0
  add x1, x6, #0
  lb_parse_dimacs_body.L3:
  lb_parse_dimacs_body.L5:
  subs xzr, x2, x0
  b.eq lb_parse_dimacs_body.L6
  ldrb w4, [x2]
  add x5, x2, #1
  subs xzr, x4, #32
  csinc w7, wzr, wzr, ne
  sub x9, x4, #9
  subs xzr, x9, #5
  csinc w9, wzr, wzr, cs
  orr x7, x7, x9
  cbnz w7, lb_parse_dimacs_body.L7
  subs xzr, x4, #99
  b.eq lb_parse_dimacs_body.L8
  b lb_parse_dimacs_body.L4
  lb_parse_dimacs_body.L8:
  add x2, x5, #0
  lb_parse_dimacs_body.L9:
  subs xzr, x2, x0
  b.eq lb_parse_dimacs_body.L10
  ldrb w4, [x2]
  add x2, x2, #1
  subs xzr, x4, #10
  b.eq lb_parse_dimacs_body.L11
  b lb_parse_dimacs_body.L9
  lb_parse_dimacs_body.L11:
  b lb_parse_dimacs_body.L5
  lb_parse_dimacs_body.L10:
  b lb_parse_dimacs_body.L4
  lb_parse_dimacs_body.L7:
  add x2, x5, #0
  b lb_parse_dimacs_body.L5
  lb_parse_dimacs_body.L6:
  lb_parse_dimacs_body.L4:
  subs xzr, x2, x0
  csinc w4, wzr, wzr, ne
  cbnz w4, lb_parse_dimacs_body.L12
  subs xzr, x1, x12
  b.eq lb_parse_dimacs_body.L13
  ldrb w5, [x2]
  subs xzr, x5, #45
  b.eq lb_parse_dimacs_body.L14
  cbnz w4, lb_parse_dimacs_body.L15
  ldrb w4, [x2]
  sub x4, x4, #48
  subs xzr, x4, #10
  b.cc lb_parse_dimacs_body.L16
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L16:
  add x2, x2, #1
  lb_parse_dimacs_body.L18:
  subs xzr, x2, x0
  b.eq lb_parse_dimacs_body.L19
  ldrb w5, [x2]
  sub x7, x5, #48
  subs xzr, x7, #10
  b.cc lb_parse_dimacs_body.L20
  subs xzr, x5, #32
  csinc w7, wzr, wzr, ne
  sub x5, x5, #9
  subs xzr, x5, #5
  csinc w5, wzr, wzr, cs
  orr x7, x7, x5
  cbnz w7, lb_parse_dimacs_body.L21
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L21:
  b lb_parse_dimacs_body.L17
  lb_parse_dimacs_body.L20:
  ldr x17, =10
  madd x4, x4, x17, xzr
  add x4, x4, x7
  ldr x17, =268435456
  subs xzr, x4, x17
  b.cc lb_parse_dimacs_body.L22
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L22:
  add x2, x2, #1
  b lb_parse_dimacs_body.L18
  lb_parse_dimacs_body.L19:
  lb_parse_dimacs_body.L17:
  subs xzr, x4, #0
  b.eq lb_parse_dimacs_body.L23
  subs xzr, x8, x4
  b.cc lb_parse_dimacs_body.L24
  str w4, [x1]
  add x1, x1, #4
  b lb_parse_dimacs_body.L3
  lb_parse_dimacs_body.L24:
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L23:
  ldr x17, =0
  str w17, [x1]
  add x1, x1, #4
  ldr x17, =3
  lslv x4, x3, x17
  add x4, x11, x4
  str x6, [x4]
  add x3, x3, #1
  add x6, x1, #0
  add x1, x2, #0
  b lb_parse_dimacs_body.L1
  lb_parse_dimacs_body.L15:
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L14:
  add x2, x2, #1
  subs xzr, x2, x0
  b.eq lb_parse_dimacs_body.L25
  ldrb w4, [x2]
  sub x4, x4, #48
  subs xzr, x4, #10
  b.cc lb_parse_dimacs_body.L26
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L26:
  add x2, x2, #1
  lb_parse_dimacs_body.L28:
  subs xzr, x2, x0
  b.eq lb_parse_dimacs_body.L29
  ldrb w5, [x2]
  sub x7, x5, #48
  subs xzr, x7, #10
  b.cc lb_parse_dimacs_body.L30
  subs xzr, x5, #32
  csinc w7, wzr, wzr, ne
  sub x5, x5, #9
  subs xzr, x5, #5
  csinc w5, wzr, wzr, cs
  orr x7, x7, x5
  cbnz w7, lb_parse_dimacs_body.L31
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L31:
  b lb_parse_dimacs_body.L27
  lb_parse_dimacs_body.L30:
  ldr x17, =10
  madd x4, x4, x17, xzr
  add x4, x4, x7
  ldr x17, =268435456
  subs xzr, x4, x17
  b.cc lb_parse_dimacs_body.L32
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L32:
  add x2, x2, #1
  b lb_parse_dimacs_body.L28
  lb_parse_dimacs_body.L29:
  lb_parse_dimacs_body.L27:
  subs xzr, x4, #0
  b.eq lb_parse_dimacs_body.L33
  subs xzr, x8, x4
  b.cc lb_parse_dimacs_body.L34
  ldr x16, =0
  sub x4, x16, x4
  str w4, [x1]
  add x1, x1, #4
  b lb_parse_dimacs_body.L3
  lb_parse_dimacs_body.L34:
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L33:
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L25:
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L13:
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L12:
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L2:
  lb_parse_dimacs_body.L36:
  subs xzr, x1, x0
  b.eq lb_parse_dimacs_body.L37
  ldrb w2, [x1]
  add x3, x1, #1
  subs xzr, x2, #32
  csinc w4, wzr, wzr, ne
  sub x5, x2, #9
  subs xzr, x5, #5
  csinc w5, wzr, wzr, cs
  orr x4, x4, x5
  cbnz w4, lb_parse_dimacs_body.L38
  subs xzr, x2, #99
  b.eq lb_parse_dimacs_body.L39
  b lb_parse_dimacs_body.L35
  lb_parse_dimacs_body.L39:
  add x1, x3, #0
  lb_parse_dimacs_body.L40:
  subs xzr, x1, x0
  b.eq lb_parse_dimacs_body.L41
  ldrb w2, [x1]
  add x1, x1, #1
  subs xzr, x2, #10
  b.eq lb_parse_dimacs_body.L42
  b lb_parse_dimacs_body.L40
  lb_parse_dimacs_body.L42:
  b lb_parse_dimacs_body.L36
  lb_parse_dimacs_body.L41:
  b lb_parse_dimacs_body.L35
  lb_parse_dimacs_body.L38:
  add x1, x3, #0
  b lb_parse_dimacs_body.L36
  lb_parse_dimacs_body.L37:
  lb_parse_dimacs_body.L35:
  subs xzr, x1, x0
  b.eq lb_parse_dimacs_body.L43
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L43:
  str x6, [x13]
  ldr x0, =1
  ldr x30, [sp]
  add sp, sp, #16
  ret
  lb_parse_dimacs_body.L0:
  ldr x0, =0
  ldr x30, [sp]
  add sp, sp, #16
  ret")

def readAddLitsCode : Program := parseAArch64("lb_read_add_lits:
  sub sp, sp, #16
  str x30, [sp]
  add x9, x1, #0
  add x8, x0, #0
  ldr x10, [x8]
  add x0, x8, #56
  ldr x11, [x0]
  add x6, x8, #64
  ldr x7, [x6]
  add x8, x8, #72
  ldr x1, [x8]
  add x0, x7, #0
  lb_read_add_lits.L1:
  subs xzr, x0, x11
  b.eq lb_read_add_lits.L2
  ldr x4, =0
  ldr x2, =0
  lb_read_add_lits.L4:
  subs xzr, x1, x9
  b.eq lb_read_add_lits.L5
  ldrb w3, [x1]
  add x1, x1, #1
  ldr x17, =127
  and x5, x3, x17
  lslv x5, x5, x2
  orr x4, x4, x5
  ldr x17, =128
  and x3, x3, x17
  subs xzr, x3, #0
  b.ne lb_read_add_lits.L6
  add x3, x1, #0
  add x1, x4, #0
  b lb_read_add_lits.L3
  lb_read_add_lits.L6:
  add x2, x2, #7
  subs xzr, x2, #28
  b.cc lb_read_add_lits.L7
  b lb_read_add_lits.L0
  lb_read_add_lits.L7:
  b lb_read_add_lits.L4
  lb_read_add_lits.L5:
  b lb_read_add_lits.L0
  lb_read_add_lits.L3:
  subs xzr, x1, #0
  b.eq lb_read_add_lits.L8
  ldr x17, =1
  lsrv x2, x1, x17
  subs xzr, x2, #0
  b.eq lb_read_add_lits.L9
  subs xzr, x10, x2
  b.cc lb_read_add_lits.L10
  ldr x17, =1
  and x1, x1, x17
  ldr x16, =0
  sub x1, x16, x1
  eor x2, x2, x1
  sub x2, x2, x1
  str w2, [x0]
  add x0, x0, #4
  add x1, x3, #0
  b lb_read_add_lits.L1
  lb_read_add_lits.L10:
  b lb_read_add_lits.L0
  lb_read_add_lits.L9:
  b lb_read_add_lits.L0
  lb_read_add_lits.L8:
  ldr x17, =0
  str w17, [x0]
  add x1, x0, #4
  str x1, [x6]
  str x3, [x8]
  subs xzr, x0, x7
  b.eq lb_read_add_lits.L11
  ldr x0, =1
  ldr x30, [sp]
  add sp, sp, #16
  ret
  lb_read_add_lits.L11:
  ldr x0, =2
  ldr x30, [sp]
  add sp, sp, #16
  ret
  lb_read_add_lits.L2:
  lb_read_add_lits.L0:
  ldr x0, =0
  ldr x30, [sp]
  add sp, sp, #16
  ret")

def rupCheckCode : Program := parseAArch64("lb_rup_check:
  sub sp, sp, #16
  str x30, [sp, #8]
  str x19, [sp]
  add x10, x3, #0
  add x3, x2, #0
  add x9, x1, #0
  add x19, x0, #0
  add x0, x19, #24
  ldr x5, [x0]
  add x0, x19, #32
  ldr x14, [x0]
  add x0, x19, #40
  ldr x11, [x0]
  add x0, x19, #48
  ldr x12, [x0]
  add x19, x19, #72
  ldr x6, [x19]
  add x0, x14, #0
  lb_rup_check.L3:
  ldrsw x1, [x3]
  cbnz w1, lb_rup_check.L4
  b lb_rup_check.L2
  lb_rup_check.L4:
  ldr x17, =63
  asrv x2, x1, x17
  eor x4, x1, x2
  sub x4, x4, x2
  add x4, x5, x4
  ldrsb x7, [x4]
  eor x7, x7, x2
  sub x2, x7, x2
  add x3, x3, #4
  subs xzr, x2, #0
  b.lt lb_rup_check.L5
  subs xzr, x2, #0
  b.gt lb_rup_check.L6
  ldr x16, =0
  sub x1, x16, x1
  subs xzr, x0, x11
  b.eq lb_rup_check.L7
  ldr x17, =63
  asrv x2, x1, x17
  ldr x17, =1
  orr x2, x2, x17
  strb w2, [x4]
  str w1, [x0]
  add x0, x0, #4
  b lb_rup_check.L3
  lb_rup_check.L7:
  b lb_rup_check.L0
  lb_rup_check.L6:
  add x16, x0, #0
  add x0, x6, #0
  add x6, x16, #0
  b lb_rup_check.L1
  lb_rup_check.L5:
  b lb_rup_check.L3
  lb_rup_check.L2:
  add x4, x0, #0
  add x0, x6, #0
  lb_rup_check.L8:
  ldr x3, =0
  ldr x1, =0
  lb_rup_check.L10:
  subs xzr, x0, x10
  b.eq lb_rup_check.L11
  ldrb w2, [x0]
  add x0, x0, #1
  ldr x17, =127
  and x6, x2, x17
  lslv x6, x6, x1
  orr x3, x3, x6
  ldr x17, =128
  and x2, x2, x17
  subs xzr, x2, #0
  b.ne lb_rup_check.L12
  add x6, x0, #0
  add x0, x3, #0
  b lb_rup_check.L9
  lb_rup_check.L12:
  add x1, x1, #7
  subs xzr, x1, #28
  b.cc lb_rup_check.L13
  b lb_rup_check.L0
  lb_rup_check.L13:
  b lb_rup_check.L10
  lb_rup_check.L11:
  b lb_rup_check.L0
  lb_rup_check.L9:
  subs xzr, x0, #0
  b.eq lb_rup_check.L14
  ldr x17, =1
  and x1, x0, x17
  subs xzr, x1, #0
  b.ne lb_rup_check.L15
  ldr x17, =1
  lsrv x0, x0, x17
  subs xzr, x0, x9
  b.cc lb_rup_check.L16
  b lb_rup_check.L0
  lb_rup_check.L16:
  ldr x17, =3
  lslv x0, x0, x17
  add x0, x12, x0
  ldr x0, [x0]
  subs xzr, x0, #0
  b.ne lb_rup_check.L17
  b lb_rup_check.L0
  lb_rup_check.L17:
  add x1, x4, #0
  add x4, x0, #0
  ldr x2, =0
  lb_rup_check.L19:
  ldrsw x0, [x4]
  cbnz w0, lb_rup_check.L20
  b lb_rup_check.L18
  lb_rup_check.L20:
  ldr x17, =63
  asrv x3, x0, x17
  eor x7, x0, x3
  sub x7, x7, x3
  add x7, x5, x7
  ldrsb x8, [x7]
  eor x8, x8, x3
  sub x8, x8, x3
  add x4, x4, #4
  subs xzr, x8, #0
  b.lt lb_rup_check.L21
  cbnz w2, lb_rup_check.L23
  b lb_rup_check.L22
  lb_rup_check.L23:
  subs xzr, x2, x0
  b.eq lb_rup_check.L24
  b lb_rup_check.L0
  lb_rup_check.L24:
  lb_rup_check.L22:
  subs xzr, x8, #0
  b.eq lb_rup_check.L25
  add x2, x0, #0
  b lb_rup_check.L19
  lb_rup_check.L25:
  subs xzr, x1, x11
  b.eq lb_rup_check.L26
  ldr x17, =1
  orr x3, x3, x17
  strb w3, [x7]
  str w0, [x1]
  add x1, x1, #4
  add x2, x0, #0
  b lb_rup_check.L19
  lb_rup_check.L26:
  b lb_rup_check.L0
  lb_rup_check.L21:
  ldr x16, =0
  sub x0, x16, x0
  subs xzr, x2, x0
  b.eq lb_rup_check.L27
  b lb_rup_check.L19
  lb_rup_check.L27:
  b lb_rup_check.L0
  lb_rup_check.L18:
  cbnz w2, lb_rup_check.L28
  add x0, x6, #0
  add x6, x1, #0
  b lb_rup_check.L1
  lb_rup_check.L28:
  add x0, x6, #0
  add x4, x1, #0
  b lb_rup_check.L8
  lb_rup_check.L15:
  b lb_rup_check.L0
  lb_rup_check.L14:
  b lb_rup_check.L0
  lb_rup_check.L1:
  lb_rup_check.L29:
  ldr x3, =0
  ldr x1, =0
  lb_rup_check.L31:
  subs xzr, x0, x10
  b.eq lb_rup_check.L32
  ldrb w2, [x0]
  add x0, x0, #1
  ldr x17, =127
  and x4, x2, x17
  lslv x4, x4, x1
  orr x3, x3, x4
  ldr x17, =128
  and x2, x2, x17
  subs xzr, x2, #0
  b.ne lb_rup_check.L33
  add x1, x0, #0
  add x0, x3, #0
  b lb_rup_check.L30
  lb_rup_check.L33:
  add x1, x1, #7
  subs xzr, x1, #28
  b.cc lb_rup_check.L34
  b lb_rup_check.L0
  lb_rup_check.L34:
  b lb_rup_check.L31
  lb_rup_check.L32:
  b lb_rup_check.L0
  lb_rup_check.L30:
  subs xzr, x0, #0
  b.eq lb_rup_check.L35
  ldr x17, =1
  and x2, x0, x17
  subs xzr, x2, #0
  b.ne lb_rup_check.L36
  ldr x17, =1
  lsrv x0, x0, x17
  subs xzr, x0, x9
  b.cc lb_rup_check.L37
  b lb_rup_check.L0
  lb_rup_check.L37:
  ldr x17, =3
  lslv x0, x0, x17
  add x0, x12, x0
  ldr x0, [x0]
  subs xzr, x0, #0
  b.ne lb_rup_check.L38
  b lb_rup_check.L0
  lb_rup_check.L38:
  add x0, x1, #0
  b lb_rup_check.L29
  lb_rup_check.L36:
  b lb_rup_check.L0
  lb_rup_check.L35:
  add x0, x14, #0
  lb_rup_check.L39:
  subs xzr, x0, x6
  b.eq lb_rup_check.L40
  ldrsw x2, [x0]
  ldr x17, =63
  asrv x3, x2, x17
  eor x2, x2, x3
  sub x2, x2, x3
  add x2, x5, x2
  ldr x17, =0
  strb w17, [x2]
  add x0, x0, #4
  b lb_rup_check.L39
  lb_rup_check.L40:
  str x1, [x19]
  ldr x0, =1
  ldr x19, [sp]
  ldr x30, [sp, #8]
  add sp, sp, #16
  ret
  lb_rup_check.L0:
  ldr x0, =0
  ldr x19, [sp]
  ldr x30, [sp, #8]
  add sp, sp, #16
  ret")

def checkPrfCode : Program := parseAArch64("lb_check_prf:
  sub sp, sp, #96
  str x30, [sp, #88]
  str x19, [sp]
  str x20, [sp, #8]
  str x21, [sp, #16]
  str x22, [sp, #24]
  str x23, [sp, #32]
  str x24, [sp, #40]
  str x25, [sp, #48]
  str x26, [sp, #56]
  str x27, [sp, #64]
  str x28, [sp, #72]
  str x29, [sp, #80]
  add x19, x1, #0
  add x25, x0, #0
  add x0, x25, #8
  ldr x28, [x0]
  add x0, x25, #16
  ldr x26, [x0]
  add x0, x25, #48
  ldr x27, [x0]
  add x29, x25, #64
  add x21, x25, #72
  lb_check_prf.L1:
  ldr x0, [x21]
  subs xzr, x0, x19
  b.eq lb_check_prf.L2
  ldrb w1, [x0]
  add x0, x0, #1
  subs xzr, x1, #97
  b.eq lb_check_prf.L3
  subs xzr, x1, #100
  b.eq lb_check_prf.L4
  b lb_check_prf.L0
  lb_check_prf.L4:
  lb_check_prf.L5:
  ldr x3, =0
  ldr x1, =0
  lb_check_prf.L7:
  subs xzr, x0, x19
  b.eq lb_check_prf.L8
  ldrb w2, [x0]
  add x0, x0, #1
  ldr x17, =127
  and x4, x2, x17
  lslv x4, x4, x1
  orr x3, x3, x4
  ldr x17, =128
  and x2, x2, x17
  subs xzr, x2, #0
  b.ne lb_check_prf.L9
  add x1, x0, #0
  add x0, x3, #0
  b lb_check_prf.L6
  lb_check_prf.L9:
  add x1, x1, #7
  subs xzr, x1, #28
  b.cc lb_check_prf.L10
  b lb_check_prf.L0
  lb_check_prf.L10:
  b lb_check_prf.L7
  lb_check_prf.L8:
  b lb_check_prf.L0
  lb_check_prf.L6:
  subs xzr, x0, #0
  b.eq lb_check_prf.L11
  ldr x17, =1
  and x2, x0, x17
  subs xzr, x2, #0
  b.ne lb_check_prf.L12
  ldr x17, =1
  lsrv x0, x0, x17
  subs xzr, x0, #0
  b.eq lb_check_prf.L13
  subs xzr, x0, x26
  b.cc lb_check_prf.L14
  b lb_check_prf.L0
  lb_check_prf.L14:
  ldr x17, =3
  lslv x0, x0, x17
  add x0, x27, x0
  ldr x2, [x0]
  subs xzr, x2, #0
  b.ne lb_check_prf.L15
  b lb_check_prf.L0
  lb_check_prf.L15:
  ldr x17, =0
  str x17, [x0]
  add x0, x1, #0
  b lb_check_prf.L5
  lb_check_prf.L13:
  b lb_check_prf.L0
  lb_check_prf.L12:
  b lb_check_prf.L0
  lb_check_prf.L11:
  str x1, [x21]
  b lb_check_prf.L1
  lb_check_prf.L3:
  ldr x3, =0
  ldr x1, =0
  lb_check_prf.L17:
  subs xzr, x0, x19
  b.eq lb_check_prf.L18
  ldrb w2, [x0]
  add x0, x0, #1
  ldr x17, =127
  and x4, x2, x17
  lslv x4, x4, x1
  orr x3, x3, x4
  ldr x17, =128
  and x2, x2, x17
  subs xzr, x2, #0
  b.ne lb_check_prf.L19
  b lb_check_prf.L16
  lb_check_prf.L19:
  add x1, x1, #7
  subs xzr, x1, #28
  b.cc lb_check_prf.L20
  b lb_check_prf.L0
  lb_check_prf.L20:
  b lb_check_prf.L17
  lb_check_prf.L18:
  b lb_check_prf.L0
  lb_check_prf.L16:
  ldr x17, =1
  and x1, x3, x17
  subs xzr, x1, #0
  b.ne lb_check_prf.L21
  ldr x17, =1
  lsrv x20, x3, x17
  subs xzr, x28, x20
  b.cc lb_check_prf.L22
  b lb_check_prf.L0
  lb_check_prf.L22:
  subs xzr, x20, x26
  b.cc lb_check_prf.L23
  b lb_check_prf.L0
  lb_check_prf.L23:
  ldr x17, =3
  lslv x1, x20, x17
  add x22, x27, x1
  ldr x1, [x22]
  subs xzr, x1, #0
  b.ne lb_check_prf.L24
  str x0, [x21]
  ldr x23, [x29]
  add x0, x25, #0
  add x1, x19, #0
  bl lb_read_add_lits
  add x24, x0, #0
  subs xzr, x24, #0
  b.ne lb_check_prf.L25
  b lb_check_prf.L0
  lb_check_prf.L25:
  add x0, x25, #0
  add x1, x20, #0
  add x2, x23, #0
  add x3, x19, #0
  bl lb_rup_check
  subs xzr, x0, #0
  b.ne lb_check_prf.L26
  b lb_check_prf.L0
  lb_check_prf.L26:
  subs xzr, x24, #2
  b.eq lb_check_prf.L27
  str x23, [x22]
  b lb_check_prf.L1
  lb_check_prf.L27:
  ldr x0, =1
  ldr x19, [sp]
  ldr x20, [sp, #8]
  ldr x21, [sp, #16]
  ldr x22, [sp, #24]
  ldr x23, [sp, #32]
  ldr x24, [sp, #40]
  ldr x25, [sp, #48]
  ldr x26, [sp, #56]
  ldr x27, [sp, #64]
  ldr x28, [sp, #72]
  ldr x29, [sp, #80]
  ldr x30, [sp, #88]
  add sp, sp, #96
  ret
  lb_check_prf.L24:
  b lb_check_prf.L0
  lb_check_prf.L21:
  b lb_check_prf.L0
  lb_check_prf.L2:
  lb_check_prf.L0:
  ldr x0, =0
  ldr x19, [sp]
  ldr x20, [sp, #8]
  ldr x21, [sp, #16]
  ldr x22, [sp, #24]
  ldr x23, [sp, #32]
  ldr x24, [sp, #40]
  ldr x25, [sp, #48]
  ldr x26, [sp, #56]
  ldr x27, [sp, #64]
  ldr x28, [sp, #72]
  ldr x29, [sp, #80]
  ldr x30, [sp, #88]
  add sp, sp, #96
  ret")

def lratCheckBytesCode : Program := parseAArch64("lrat_check_bytes:
  sub sp, sp, #64
  str x30, [sp, #48]
  str x19, [sp, #8]
  str x20, [sp, #16]
  str x21, [sp, #24]
  str x22, [sp, #32]
  str x23, [sp, #40]
  add x20, x5, #0
  add x19, x4, #0
  add x22, x3, #0
  add x21, x2, #0
  subs xzr, x20, #128
  b.cc lrat_check_bytes.L0
  add x23, x0, x1
  add x1, x21, x22
  str x1, [sp]
  add x1, x23, #0
  add x2, x19, #0
  bl lb_parse_dimacs_header
  subs xzr, x0, #0
  b.ne lrat_check_bytes.L1
  ldr x0, =0
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x21, [sp, #24]
  ldr x22, [sp, #32]
  ldr x23, [sp, #40]
  ldr x30, [sp, #48]
  add sp, sp, #64
  ret
  lrat_check_bytes.L1:
  ldr x3, [x19]
  add x0, x19, #8
  ldr x0, [x0]
  add x5, x3, #1
  add x1, x3, #8
  ldr x17, =-8
  and x1, x1, x17
  ldr x17, =2
  lslv x5, x5, x17
  add x7, x5, #7
  ldr x17, =-8
  and x7, x7, x17
  add x2, x1, x7
  add x2, x2, #80
  subs xzr, x20, x2
  b.cc lrat_check_bytes.L2
  sub x20, x20, x2
  ldr x17, =4
  lsrv x2, x20, x17
  ldr x17, =268435455
  and x22, x22, x17
  add x4, x0, x22
  add x4, x4, #32
  subs xzr, x2, x4
  b.cc lrat_check_bytes.L4
  add x2, x4, #0
  b lrat_check_bytes.L3
  lrat_check_bytes.L4:
  lrat_check_bytes.L3:
  subs xzr, x2, x0
  b.ls lrat_check_bytes.L5
  add x4, x19, #80
  add x6, x4, x1
  add x8, x6, x5
  add x5, x6, x7
  ldr x17, =3
  lslv x0, x2, x17
  add x7, x5, x0
  sub x20, x20, x0
  ldr x17, =-4
  and x20, x20, x17
  add x9, x7, x20
  ldr x0, =0
  lrat_check_bytes.L7:
  subs xzr, x0, x3
  b.ls lrat_check_bytes.L8
  b lrat_check_bytes.L6
  lrat_check_bytes.L8:
  add x1, x4, x0
  ldr x17, =0
  strb w17, [x1]
  add x0, x0, #1
  b lrat_check_bytes.L7
  lrat_check_bytes.L6:
  ldr x0, =0
  lrat_check_bytes.L10:
  subs xzr, x0, x2
  b.cc lrat_check_bytes.L11
  b lrat_check_bytes.L9
  lrat_check_bytes.L11:
  ldr x17, =3
  lslv x1, x0, x17
  add x1, x5, x1
  ldr x17, =0
  str x17, [x1]
  add x0, x0, #1
  b lrat_check_bytes.L10
  lrat_check_bytes.L9:
  add x0, x19, #16
  str x2, [x0]
  add x0, x19, #24
  str x4, [x0]
  add x0, x19, #32
  str x6, [x0]
  add x0, x19, #40
  str x8, [x0]
  add x0, x19, #48
  str x5, [x0]
  add x0, x19, #56
  str x9, [x0]
  add x0, x19, #64
  str x7, [x0]
  add x0, x23, #0
  add x1, x19, #0
  bl lb_parse_dimacs_body
  subs xzr, x0, #0
  b.ne lrat_check_bytes.L12
  ldr x0, =0
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x21, [sp, #24]
  ldr x22, [sp, #32]
  ldr x23, [sp, #40]
  ldr x30, [sp, #48]
  add sp, sp, #64
  ret
  lrat_check_bytes.L12:
  add x0, x19, #72
  str x21, [x0]
  add x0, x19, #0
  ldr x1, [sp]
  bl lb_check_prf
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x21, [sp, #24]
  ldr x22, [sp, #32]
  ldr x23, [sp, #40]
  ldr x30, [sp, #48]
  add sp, sp, #64
  ret
  lrat_check_bytes.L5:
  ldr x0, =0
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x21, [sp, #24]
  ldr x22, [sp, #32]
  ldr x23, [sp, #40]
  ldr x30, [sp, #48]
  add sp, sp, #64
  ret
  lrat_check_bytes.L2:
  ldr x0, =0
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x21, [sp, #24]
  ldr x22, [sp, #32]
  ldr x23, [sp, #40]
  ldr x30, [sp, #48]
  add sp, sp, #64
  ret
  lrat_check_bytes.L0:
  ldr x0, =0
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x21, [sp, #24]
  ldr x22, [sp, #32]
  ldr x23, [sp, #40]
  ldr x30, [sp, #48]
  add sp, sp, #64
  ret")

def lratBytesCode : Program :=
  parseHeaderCode ++ (parseBodyCode ++ (readAddLitsCode ++
    (rupCheckCode ++ (checkPrfCode ++ lratCheckBytesCode))))

def lratBytesBounds : List (String × Nat) :=
  [("lb_parse_dimacs_header", 16),
   ("lb_parse_dimacs_body", 16),
   ("lb_read_add_lits", 16),
   ("lb_rup_check", 16),
   ("lb_check_prf", 112),
   ("lrat_check_bytes", 176)]

theorem parseHeader_compile : compileFn isa parseHeaderFn = .ok parseHeaderCode := by kernel_rfl
theorem parseBody_compile : compileFn isa parseBodyFn = .ok parseBodyCode := by kernel_rfl
theorem readAddLits_compile : compileFn isa readAddLitsFn = .ok readAddLitsCode := by kernel_rfl
theorem rupCheck_compile : compileFn isa rupCheckFn = .ok rupCheckCode := by kernel_rfl
theorem checkPrf_compile : compileFn isa checkPrfFn = .ok checkPrfCode := by kernel_rfl
theorem lratCheckBytes_compile :
    compileFn isa lratCheckBytesFn = .ok lratCheckBytesCode := by kernel_rfl

theorem lrat_bytes_module_compile :
    compileModule isa 0 [] [] 0 lratBytesFns =
      .ok (lratBytesCode, lratBytesBounds) := by kernel_rfl

/-! ## Generic `compile_sound` linking & closed Arm64 lifting helpers -/

section Generic
variable [hh : Host]

/-- Generic linking helper for `lratBytesFns` on `Arm64.target` via `compile_sound`. -/
theorem lrat_bytes_module_fnspec_of (Γ : Env) (k₀ : Nat)
    (hc : lratBytesCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hwf : ∀ f ∈ lratBytesFns, Func.Wf f.body)
    (hsound : ∀ f ∈ lratBytesFns, ∀ args m Q X, Γ f.name args m Q X → Func.spec Γ f.body args m Q X) :
    ∀ p ∈ lratBytesBounds,
      target.Defined hh p.1 ∧ target.FnSpec hh p.1 (Γ p.1) p.2 0 :=
  compile_sound (T := target) hh Γ [] [] 0 lratBytesFns
    lratBytesCode lratBytesBounds k₀ lrat_bytes_module_compile hc hu hwf hsound
    (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- Lifting any `FnSpec` for `"lrat_check_bytes"` at stack bound `176` and contract
`lratCheckBytesSpec` to the closed Kraken-AArch64 statement. -/
theorem lrat_check_bytes_arm64_of_fnspec
    (hfnspec : target.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec 176 0)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = prf_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 work_len)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 176 ∧ f = bs.At (s.regs.SP.toBitVec - 176#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨ (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 176 ∧
            f = bs.At (s.regs.SP.toBitVec - 176#64)) ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ := by
  let P_mem : Mem 64 → Prop :=
    Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len
  let Q : LeanQbe.Post := fun rets m' =>
    ∃ r : Val, rets = [r] ∧ (r = 0 ∨ r = 1) ∧
      (r = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (P_mem ⋆ Std.ExtHashMap.emp) m'
  let X : XPost := fun _ _ _ => False
  obtain ⟨f_ps, f_r, hu1, hd1, ⟨m, f_e, hu2, hd2, hm_pre, he⟩, hrest⟩ := hmem
  have hm_emp : (P_mem ⋆ Std.ExtHashMap.emp) m := by
    dsimp [P_mem] at hm_pre ⊢
    rw [Std.ExtHashMap.sep_emp]
    exact hm_pre
  have hspec : lratCheckBytesSpec
      [cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len] m Q X :=
    ⟨cnf_ptr, prf_ptr, work_ptr, cnfBytes, prfBytes, work_len, Std.ExtHashMap.emp,
      rfl, hcnf, hprf, hwork, hm_emp,
      fun r m' hr01 hunsat hm' => ⟨r, rfl, hr01, hunsat, hm'⟩⟩
  have hargs : target.ArgsIn
      [cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hx0, hx1, hx2, hx3, hx4, hx5]
  have hsp' : target.spEntry (target.get s target.sp) := by
    simpa [target, get_sp] using hsp
  have hmem' : target.mem s =⋆ Eq m ⋆ target.Entry (target.get s target.sp) ra 176 ⋆ R := by
    refine ⟨f_ps, f_r, hu1, hd1, ⟨m, f_e, hu2, hd2, rfl, ?_⟩, hrest⟩
    simp only [Target.Entry, region_zero, Std.ExtHashMap.sep_emp, get_sp]
    exact he
  have hf := hfnspec
    [cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
     prf_ptr, BitVec.ofNat 64 prfBytes.length,
     work_ptr, BitVec.ofNat 64 work_len] m Q X hspec s ra R hargs hra hsp' hmem'
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨r, rfl, hr01, hunsat, hm'⟩, hrets, ⟨hcs, hsp_out⟩, hdmem⟩ |
    ⟨_, _, _, hx, _⟩)
  · rw [Std.ExtHashMap.sep_emp] at hm'
    have hx0' : (st.data.regs.getXReg .X0).toBitVec = r := by
      simpa [Target.RetsIn, Target.ValsIn, retRegs, get_reg] using hrets
    rw [← hx0'] at hr01 hunsat
    refine ⟨hpc, hr01, hunsat, fun reg hreg => ?_, ?_, ?_⟩
    · have := hcs (.reg reg) (by simp [calleeSaved] at hreg ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp_out
      exact UInt64.toBitVec_inj.mp this
    · simp only [Target.Exit, get_sp, Nat.add_zero] at hdmem
      exact sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hdmem
  · exact hx.elim

/-- Trivial-postcondition lifting helper: given any `cnfBytes` whose parse is `some cnf`,
`lrat_check_bytes` returns to `ra` with `x0 ∈ {0, 1}` and `x0 = 1 → cnf.Unsat`. -/
theorem lrat_check_bytes_arm64_unsat_of_fnspec
    (hfnspec : target.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec 176 0)
    (cnf : CNF Nat) (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hparse : parseDimacs cnfBytes = some cnf)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = prf_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 work_len)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 176 ∧ f = bs.At (s.regs.SP.toBitVec - 176#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨ (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ := by
  refine eventually_weaken _ _ _ _ ?_
    (lrat_check_bytes_arm64_of_fnspec hfnspec cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
      hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 hra hsp hmem)
  rintro st ⟨hpc, hr01, hunsat, -⟩
  refine ⟨hpc, hr01, fun h1 => ?_⟩
  obtain ⟨cnf', hp', hu'⟩ := hunsat h1
  rw [hparse] at hp'
  injection hp' with h_eq
  exact h_eq ▸ hu'

end Generic

/-! ## Concrete host and memory state helpers -/

private theorem sum_map_size_le_four {α : Type} (l : List (Kraken.Sized α))
    (h : ∀ x ∈ l, x.size ≤ 4) : (l.map (·.size)).sum ≤ 4 * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx := h x List.mem_cons_self
    have hxs := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

theorem layoutOf_small (p : Program) (hp : 4 * p.length < 2 ^ 64) :
    ((layoutOf p).apply p).sizeBefore p.length < 2 ^ 64 := by
  unfold Kraken.Executable.sizeBefore
  have hlen : ((layoutOf p).apply p).program.length = p.length := by
    simp [Kraken.Layout.apply]
  rw [List.take_of_length_le (Nat.le_of_eq hlen)]
  have hle := sum_map_size_le_four ((layoutOf p).apply p).program (fun x hx => by
    simp only [Kraken.Layout.apply, List.mem_mapIdx] at hx
    obtain ⟨i, _, rfl⟩ := hx
    change (match p[i]? with | some (.label _) => 0 | _ => 4) ≤ 4
    cases p[i]? with
    | none => simp
    | some d => cases d <;> simp)
  rw [hlen] at hle
  omega

@[instance_reducible] def lratBytesHost : Host :=
  .ofLayout lratBytesCode (layoutOf lratBytesCode) (layoutOf_zero _)
    (layoutOf_small lratBytesCode (of_decide_eq_true (by kernel_rfl)))

attribute [local instance] lratBytesHost

theorem lratBytesHost_prog : Host.prog = lratBytesCode := rfl

theorem lratBytesHost_unique : Host.LabelsUnique :=
  Host.labelsUnique_of_nodup (of_decide_eq_true (by kernel_rfl))

def zeros176 : List UInt8 := List.replicate 176 0
def zeros512 : List UInt8 := List.replicate 512 0

abbrev nvCnfPtr : BitVec 64 := 0x1000#64
abbrev nvPrfPtr (cnfBytes : List UInt8) : BitVec 64 :=
  nvCnfPtr + BitVec.ofNat 64 cnfBytes.length
abbrev nvWorkPtr (cnfBytes prfBytes : List UInt8) : BitVec 64 :=
  nvPrfPtr cnfBytes + BitVec.ofNat 64 prfBytes.length

def lratBytesState (cnfBytes prfBytes : List UInt8) : MachineData :=
  { regs :=
      { X0 := (nvCnfPtr).toNat.toUInt64
        X1 := cnfBytes.length.toUInt64
        X2 := (nvPrfPtr cnfBytes).toNat.toUInt64
        X3 := prfBytes.length.toUInt64
        X4 := (nvWorkPtr cnfBytes prfBytes).toNat.toUInt64
        X5 := 512
        SP := 0x1000
        X30 := (0x1234 : Int64).toUInt64 },
    dmem := (zeros176 ++ ((cnfBytes ++ prfBytes) ++ zeros512)).At 0x0f50#64 }

theorem lratBytesState_mem (cnfBytes prfBytes : List UInt8)
    (hcb : cnfBytes.length ≤ 4096) (hpb : prfBytes.length ≤ 4096) :
    (lratBytesState cnfBytes prfBytes).dmem =⋆
      (Eq (cnfBytes.At nvCnfPtr) ⋆
        Eq (prfBytes.At (nvPrfPtr cnfBytes)) ⋆
        region (nvWorkPtr cnfBytes prfBytes) 512) ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 176 ∧
        f = bs.At ((lratBytesState cnfBytes prfBytes).regs.SP.toBitVec - 176#64)) ⋆
      Std.ExtHashMap.emp := by
  have h176 : zeros176.length = 176 := List.length_replicate
  have h512 : zeros512.length = 512 := List.length_replicate
  have hsp_eq : (lratBytesState cnfBytes prfBytes).regs.SP.toBitVec = 0x1000#64 := rfl
  have hsp_sub : (lratBytesState cnfBytes prfBytes).regs.SP.toBitVec - 176#64 = 0x0f50#64 := by
    rw [hsp_eq]; decide
  rw [hsp_sub, Std.ExtHashMap.sep_emp]
  have h1 := Mem.At_append_sep zeros176 ((cnfBytes ++ prfBytes) ++ zeros512) 0x0f50#64
    (by simp only [List.length_append, h176, h512]; omega)
  have e1 : 0x0f50#64 + BitVec.ofNat 64 zeros176.length = nvCnfPtr := by simp [nvCnfPtr, h176]
  rw [e1] at h1
  have h2 := Mem.At_append_sep (cnfBytes ++ prfBytes) zeros512 nvCnfPtr
    (by simp only [List.length_append, h512]; omega)
  have e2 : nvCnfPtr + BitVec.ofNat 64 (cnfBytes ++ prfBytes).length = nvWorkPtr cnfBytes prfBytes := by
    simp only [nvWorkPtr, nvPrfPtr, nvCnfPtr, List.length_append]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e2] at h2
  have h3 := Mem.At_append_sep cnfBytes prfBytes nvCnfPtr (by omega)
  have h0 : (Eq ((zeros176 ++ ((cnfBytes ++ prfBytes) ++ zeros512)).At 0x0f50#64))
      (lratBytesState cnfBytes prfBytes).dmem := rfl
  rw [h1, Std.ExtHashMap.sep_comm] at h0
  refine sep_mono (fun fL hfL => ?_) (sep_mono_r (fun fS hfS => ⟨zeros176, h176, hfS.symm⟩) h0)
  rw [h2] at hfL
  exact sep_mono (fun fC hfC => by rwa [h3] at hfC)
    (sep_mono_r (fun fW hfW => ⟨zeros512, h512, hfW.symm⟩) hfL)

/-! ## Closed Kraken-AArch64 theorems & concrete instances -/

section Closed

/-- Closed `compile_sound` linking of all 6 functions in `lratBytesFns` on `Arm64.target`
against `lratBytesEnv`. -/
theorem lrat_bytes_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : lratBytesCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∀ p ∈ lratBytesBounds,
      target.Defined hh p.1 ∧ target.FnSpec hh p.1 (lratBytesEnv p.1) p.2 0 :=
  lrat_bytes_module_fnspec_of lratBytesEnv k₀ hc hu lratBytesFns_wf lratBytesEnv_sound

/-- Closed end-to-end AArch64 theorem for `lrat_check_bytes` over arbitrary untrusted
`cnfBytes`, `prfBytes`, and uninitialized scratch `region work_ptr work_len`:
returns to `ra` with `x0 ∈ {0, 1}`, `x0 = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`,
callee-saved `x19`–`x29` and `sp` restored, and all memory frames intact. -/
theorem lrat_check_bytes_arm64_correct [Host] (k₀ : Nat)
    (hc : lratBytesCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = prf_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 work_len)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 176 ∧ f = bs.At (s.regs.SP.toBitVec - 176#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨ (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          (fun f => ∃ bs : List UInt8, bs.length = 176 ∧
            f = bs.At (s.regs.SP.toBitVec - 176#64)) ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_arm64_of_fnspec
    (by simpa [lratBytesEnv_entry] using
      (lrat_bytes_module_fnspec k₀ hc hu ⟨"lrat_check_bytes", 176⟩ (by simp [lratBytesBounds])).2)
    cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
    hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 hra hsp hmem

/-- Trivial-postcondition headline corollary on Kraken-AArch64: for any `ValidDimacsCnf cnf`
encoded at `cnf_ptr` and arbitrary untrusted `prfBytes` and `region work_ptr work_len`,
`lrat_check_bytes` returns to `ra` with `x0 ∈ {0, 1}` and `x0 = 1 → cnf.Unsat`
(with no parser in the postcondition). -/
theorem lrat_check_bytes_arm64_unsat [Host] (k₀ : Nat)
    (hc : lratBytesCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf : CNF Nat) (hvalid : ValidDimacsCnf cnf)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + (encodeDimacs cnf).length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)
    (hx1 : (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 (encodeDimacs cnf).length)
    (hx2 : (s.regs.getXReg .X2).toBitVec = prf_ptr)
    (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length)
    (hx4 : (s.regs.getXReg .X4).toBitVec = work_ptr)
    (hx5 : (s.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 work_len)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 176 ∧ f = bs.At (s.regs.SP.toBitVec - 176#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨ (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_arm64_unsat_of_fnspec
    (by simpa [lratBytesEnv_entry] using
      (lrat_bytes_module_fnspec k₀ hc hu ⟨"lrat_check_bytes", 176⟩ (by simp [lratBytesBounds])).2)
    cnf cnf_ptr prf_ptr work_ptr (encodeDimacs cnf) prfBytes work_len
    (parseDimacs_encodeDimacs hvalid)
    hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 hra hsp hmem

private theorem lratBytesState_call {spec : Spec}
    (hfnspec : target.FnSpec lratBytesHost "lrat_check_bytes" spec 176 0)
    (cnfBytes prfBytes : List UInt8)
    (hcb : cnfBytes.length ≤ 4096) (hpb : prfBytes.length ≤ 4096)
    {Q : LeanQbe.Post}
    (hspec : ∀ m : Mem 64,
      ((Eq (cnfBytes.At nvCnfPtr) ⋆ Eq (prfBytes.At (nvPrfPtr cnfBytes)) ⋆
        region (nvWorkPtr cnfBytes prfBytes) 512) ⋆ Std.ExtHashMap.emp) m →
      spec
        [nvCnfPtr, BitVec.ofNat 64 cnfBytes.length,
         nvPrfPtr cnfBytes, BitVec.ofNat 64 prfBytes.length,
         nvWorkPtr cnfBytes prfBytes, 512#64] m Q (fun _ _ _ => False)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = (0x1234 : Int64) ∧ ∃ rets m', Q rets m' ∧ target.RetsIn rets st.data)
      ⟨lratBytesState cnfBytes prfBytes, Labels.label "lrat_check_bytes"⟩ := by
  let s0 := lratBytesState cnfBytes prfBytes
  obtain ⟨f_ps, f_r, hu1, hd1, ⟨m, f_e, hu2, hd2, hm_pre, he⟩, hrest⟩ :=
    lratBytesState_mem cnfBytes prfBytes hcb hpb
  have hm_emp : ((Eq (cnfBytes.At nvCnfPtr) ⋆ Eq (prfBytes.At (nvPrfPtr cnfBytes)) ⋆
      region (nvWorkPtr cnfBytes prfBytes) 512) ⋆ Std.ExtHashMap.emp) m := by
    rw [Std.ExtHashMap.sep_emp]
    exact hm_pre
  have hx0 : (s0.regs.getXReg .X0).toBitVec = nvCnfPtr := rfl
  have hx1 : (s0.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length := rfl
  have hx2 : (s0.regs.getXReg .X2).toBitVec = nvPrfPtr cnfBytes :=
    BitVec.eq_of_toNat_eq (by
      change (BitVec.ofNat 64 (nvPrfPtr cnfBytes).toNat).toNat = (nvPrfPtr cnfBytes).toNat
      simp)
  have hx3 : (s0.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 prfBytes.length := rfl
  have hx4 : (s0.regs.getXReg .X4).toBitVec = nvWorkPtr cnfBytes prfBytes :=
    BitVec.eq_of_toNat_eq (by
      change (BitVec.ofNat 64 (nvWorkPtr cnfBytes prfBytes).toNat).toNat =
        (nvWorkPtr cnfBytes prfBytes).toNat
      simp)
  have hx5 : (s0.regs.getXReg .X5).toBitVec = 512#64 := rfl
  have hargs : target.ArgsIn
      [nvCnfPtr, BitVec.ofNat 64 cnfBytes.length,
       nvPrfPtr cnfBytes, BitVec.ofNat 64 prfBytes.length,
       nvWorkPtr cnfBytes prfBytes, 512#64] s0 := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hx0, hx1, hx2, hx3, hx4, hx5]
  have hsp' : target.spEntry (target.get s0 target.sp) := by
    change (0x1000 : UInt64).toNat % 16 = 0; decide
  have hmem' : target.mem s0 =⋆ Eq m ⋆ target.Entry (target.get s0 target.sp) 0x1234 176 ⋆
      Std.ExtHashMap.emp := by
    refine ⟨f_ps, f_r, hu1, hd1, ⟨m, f_e, hu2, hd2, rfl, ?_⟩, hrest⟩
    simp only [Target.Entry, region_zero, Std.ExtHashMap.sep_emp, get_sp]
    exact he
  refine eventually_weaken _ _ _ _ ?_
    (hfnspec _ m Q (fun _ _ _ => False) (hspec m hm_emp) s0 0x1234 Std.ExtHashMap.emp
      hargs rfl hsp' hmem')
  rintro st (⟨hpc, rets, m', hQ, hrets, -⟩ | ⟨_, _, _, hx, _⟩)
  · exact ⟨hpc, rets, m', hQ, hrets⟩
  · exact hx.elim

/-- Concrete accepting non-vacuity on `lratBytesHost`: executes `lrat_check_bytes` from
`lratBytesState nvDimacsBytes nvLratAcceptBytes` to `pc = 0x1234` with `x0 = 1` and
`nvBytesCnf.Unsat`. -/
theorem lrat_check_bytes_arm64_accepts :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 1 ∧ nvBytesCnf.Unsat)
      ⟨lratBytesState nvDimacsBytes nvLratAcceptBytes, Labels.label "lrat_check_bytes"⟩ := by
  have hfn := (lrat_bytes_module_fnspec_of lratBytesAcceptEnv 0 (List.prefix_refl _)
    lratBytesHost_unique lratBytesFns_wf lratBytesAcceptEnv_sound
    ⟨"lrat_check_bytes", 176⟩ (by simp [lratBytesBounds])).2
  simp only [lratBytesAcceptEnv_entry] at hfn
  have hf := lratBytesState_call (Q := fun rs _ => rs = [1] ∧ nvBytesCnf.Unsat)
    hfn nvDimacsBytes nvLratAcceptBytes (by simp) (by simp)
    (fun m hm => ⟨nvCnfPtr, nvPrfPtr nvDimacsBytes, nvWorkPtr nvDimacsBytes nvLratAcceptBytes,
      Std.ExtHashMap.emp, rfl,
      by simp only [nvCnfPtr, nvDimacsBytes_length]; decide,
      by simp only [nvPrfPtr, nvCnfPtr, nvDimacsBytes_length, nvLratAcceptBytes_length]; decide,
      by simp only [nvWorkPtr, nvPrfPtr, nvCnfPtr, nvDimacsBytes_length, nvLratAcceptBytes_length]; decide,
      hm, fun _ hu _ => ⟨rfl, hu⟩⟩)
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st ⟨hpc, _, _, ⟨rfl, hu⟩, hrets⟩
  have hx0 : (st.data.regs.getXReg .X0).toBitVec = 1 := by
    simpa [Target.RetsIn, Target.ValsIn, retRegs, get_reg] using hrets
  exact ⟨hpc, hx0, hu⟩

/-- Concrete rejecting non-vacuity on `lratBytesHost`: executes `lrat_check_bytes` from
`lratBytesState nvDimacsBytes nvLratRejectBytes` to `pc = 0x1234` with `x0 = 0`. -/
theorem lrat_check_bytes_arm64_rejects :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 0)
      ⟨lratBytesState nvDimacsBytes nvLratRejectBytes, Labels.label "lrat_check_bytes"⟩ := by
  have hfn := (lrat_bytes_module_fnspec_of lratBytesRejectEnv 0 (List.prefix_refl _)
    lratBytesHost_unique lratBytesFns_wf lratBytesRejectEnv_sound
    ⟨"lrat_check_bytes", 176⟩ (by simp [lratBytesBounds])).2
  simp only [lratBytesRejectEnv_entry] at hfn
  have hf := lratBytesState_call (Q := fun rs _ => rs = [0])
    hfn nvDimacsBytes nvLratRejectBytes (by simp) (by simp)
    (fun m hm => ⟨nvCnfPtr, nvPrfPtr nvDimacsBytes, nvWorkPtr nvDimacsBytes nvLratRejectBytes,
      Std.ExtHashMap.emp, rfl,
      by simp only [nvCnfPtr, nvDimacsBytes_length]; decide,
      by simp only [nvPrfPtr, nvCnfPtr, nvDimacsBytes_length, nvLratRejectBytes_length]; decide,
      by simp only [nvWorkPtr, nvPrfPtr, nvCnfPtr, nvDimacsBytes_length, nvLratRejectBytes_length]; decide,
      hm, fun _ _ => rfl⟩)
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st ⟨hpc, _, _, rfl, hrets⟩
  have hx0 : (st.data.regs.getXReg .X0).toBitVec = 0 := by
    simpa [Target.RetsIn, Target.ValsIn, retRegs, get_reg] using hrets
  exact ⟨hpc, hx0⟩

end Closed

end LeanQbe.Arm64.LratBytes
