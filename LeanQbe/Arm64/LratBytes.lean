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
`LratBytes.lratBytesFns` through `compileModule Arm64.isa`, verifies all 1,579 emitted AArch64
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
  b lb_parse_dimacs_header.L2
  lb_parse_dimacs_header.L2:
  subs xzr, x0, x1
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L3
  ldrb w3, [x0]
  ldr x17, =1
  add x4, x0, x17
  ldr x17, =32
  subs xzr, x3, x17
  csinc w5, wzr, wzr, ne
  ldr x17, =9
  sub x6, x3, x17
  ldr x17, =5
  subs xzr, x6, x17
  csinc w6, wzr, wzr, cs
  orr x5, x5, x6
  cbnz w5, lb_parse_dimacs_header.L4
  ldr x17, =99
  subs xzr, x3, x17
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L5
  b lb_parse_dimacs_header.L1
  lb_parse_dimacs_header.L5:
  add x0, x4, #0
  b lb_parse_dimacs_header.L6
  lb_parse_dimacs_header.L6:
  subs xzr, x0, x1
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L7
  ldrb w3, [x0]
  ldr x17, =1
  add x0, x0, x17
  ldr x17, =10
  subs xzr, x3, x17
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L8
  b lb_parse_dimacs_header.L6
  lb_parse_dimacs_header.L8:
  b lb_parse_dimacs_header.L2
  lb_parse_dimacs_header.L7:
  b lb_parse_dimacs_header.L1
  lb_parse_dimacs_header.L4:
  add x0, x4, #0
  b lb_parse_dimacs_header.L2
  lb_parse_dimacs_header.L3:
  b lb_parse_dimacs_header.L1
  lb_parse_dimacs_header.L1:
  subs xzr, x0, x1
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L9
  ldrb w3, [x0]
  ldr x17, =112
  subs xzr, x3, x17
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L10
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L10:
  ldr x17, =1
  add x0, x0, x17
  subs xzr, x0, x1
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L11
  ldrb w3, [x0]
  ldr x17, =32
  subs xzr, x3, x17
  csinc w4, wzr, wzr, ne
  ldr x17, =9
  sub x3, x3, x17
  ldr x17, =5
  subs xzr, x3, x17
  csinc w3, wzr, wzr, cs
  orr x3, x4, x3
  cbnz w3, lb_parse_dimacs_header.L12
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L12:
  ldr x17, =1
  add x0, x0, x17
  b lb_parse_dimacs_header.L14
  lb_parse_dimacs_header.L14:
  subs xzr, x0, x1
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L15
  ldrb w3, [x0]
  ldr x17, =32
  subs xzr, x3, x17
  csinc w4, wzr, wzr, ne
  ldr x17, =9
  sub x3, x3, x17
  ldr x17, =5
  subs xzr, x3, x17
  csinc w3, wzr, wzr, cs
  orr x3, x4, x3
  cbnz w3, lb_parse_dimacs_header.L16
  b lb_parse_dimacs_header.L13
  lb_parse_dimacs_header.L16:
  ldr x17, =1
  add x0, x0, x17
  b lb_parse_dimacs_header.L14
  lb_parse_dimacs_header.L15:
  b lb_parse_dimacs_header.L13
  lb_parse_dimacs_header.L13:
  subs xzr, x0, x1
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L17
  ldrb w3, [x0]
  ldr x17, =99
  subs xzr, x3, x17
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L18
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L18:
  ldr x17, =1
  add x3, x0, x17
  subs xzr, x3, x1
  csinc w4, wzr, wzr, ne
  cbnz w4, lb_parse_dimacs_header.L19
  ldrb w3, [x3]
  ldr x17, =110
  subs xzr, x3, x17
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L20
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L20:
  ldr x17, =2
  add x3, x0, x17
  subs xzr, x3, x1
  csinc w4, wzr, wzr, ne
  cbnz w4, lb_parse_dimacs_header.L21
  ldrb w3, [x3]
  ldr x17, =102
  subs xzr, x3, x17
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L22
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L22:
  ldr x17, =3
  add x0, x0, x17
  subs xzr, x0, x1
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L23
  ldrb w3, [x0]
  ldr x17, =32
  subs xzr, x3, x17
  csinc w4, wzr, wzr, ne
  ldr x17, =9
  sub x3, x3, x17
  ldr x17, =5
  subs xzr, x3, x17
  csinc w3, wzr, wzr, cs
  orr x3, x4, x3
  cbnz w3, lb_parse_dimacs_header.L24
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L24:
  ldr x17, =1
  add x0, x0, x17
  b lb_parse_dimacs_header.L26
  lb_parse_dimacs_header.L26:
  subs xzr, x0, x1
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L27
  ldrb w3, [x0]
  ldr x17, =32
  subs xzr, x3, x17
  csinc w4, wzr, wzr, ne
  ldr x17, =9
  sub x3, x3, x17
  ldr x17, =5
  subs xzr, x3, x17
  csinc w3, wzr, wzr, cs
  orr x3, x4, x3
  cbnz w3, lb_parse_dimacs_header.L28
  b lb_parse_dimacs_header.L25
  lb_parse_dimacs_header.L28:
  ldr x17, =1
  add x0, x0, x17
  b lb_parse_dimacs_header.L26
  lb_parse_dimacs_header.L27:
  b lb_parse_dimacs_header.L25
  lb_parse_dimacs_header.L25:
  subs xzr, x0, x1
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_parse_dimacs_header.L29
  ldrb w3, [x0]
  ldr x17, =48
  sub x3, x3, x17
  ldr x17, =10
  subs xzr, x3, x17
  csinc w4, wzr, wzr, cs
  cbnz w4, lb_parse_dimacs_header.L30
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L30:
  ldr x17, =1
  add x0, x0, x17
  b lb_parse_dimacs_header.L32
  lb_parse_dimacs_header.L32:
  subs xzr, x0, x1
  csinc w4, wzr, wzr, ne
  cbnz w4, lb_parse_dimacs_header.L33
  ldrb w4, [x0]
  ldr x17, =48
  sub x5, x4, x17
  ldr x17, =10
  subs xzr, x5, x17
  csinc w6, wzr, wzr, cs
  cbnz w6, lb_parse_dimacs_header.L34
  ldr x17, =32
  subs xzr, x4, x17
  csinc w5, wzr, wzr, ne
  ldr x17, =9
  sub x4, x4, x17
  ldr x17, =5
  subs xzr, x4, x17
  csinc w4, wzr, wzr, cs
  orr x4, x5, x4
  cbnz w4, lb_parse_dimacs_header.L35
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L35:
  add x16, x0, #0
  add x0, x3, #0
  add x3, x16, #0
  b lb_parse_dimacs_header.L31
  lb_parse_dimacs_header.L34:
  ldr x17, =10
  madd x3, x3, x17, xzr
  add x3, x3, x5
  ldr x17, =268435456
  subs xzr, x3, x17
  csinc w4, wzr, wzr, cs
  cbnz w4, lb_parse_dimacs_header.L36
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L36:
  ldr x17, =1
  add x0, x0, x17
  b lb_parse_dimacs_header.L32
  lb_parse_dimacs_header.L33:
  add x16, x0, #0
  add x0, x3, #0
  add x3, x16, #0
  b lb_parse_dimacs_header.L31
  lb_parse_dimacs_header.L31:
  subs xzr, x3, x1
  csinc w4, wzr, wzr, ne
  cbnz w4, lb_parse_dimacs_header.L37
  ldrb w4, [x3]
  ldr x17, =32
  subs xzr, x4, x17
  csinc w5, wzr, wzr, ne
  ldr x17, =9
  sub x4, x4, x17
  ldr x17, =5
  subs xzr, x4, x17
  csinc w4, wzr, wzr, cs
  orr x4, x5, x4
  cbnz w4, lb_parse_dimacs_header.L38
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L38:
  ldr x17, =1
  add x3, x3, x17
  b lb_parse_dimacs_header.L40
  lb_parse_dimacs_header.L40:
  subs xzr, x3, x1
  csinc w4, wzr, wzr, ne
  cbnz w4, lb_parse_dimacs_header.L41
  ldrb w4, [x3]
  ldr x17, =32
  subs xzr, x4, x17
  csinc w5, wzr, wzr, ne
  ldr x17, =9
  sub x4, x4, x17
  ldr x17, =5
  subs xzr, x4, x17
  csinc w4, wzr, wzr, cs
  orr x4, x5, x4
  cbnz w4, lb_parse_dimacs_header.L42
  b lb_parse_dimacs_header.L39
  lb_parse_dimacs_header.L42:
  ldr x17, =1
  add x3, x3, x17
  b lb_parse_dimacs_header.L40
  lb_parse_dimacs_header.L41:
  b lb_parse_dimacs_header.L39
  lb_parse_dimacs_header.L39:
  subs xzr, x3, x1
  csinc w4, wzr, wzr, ne
  cbnz w4, lb_parse_dimacs_header.L43
  ldrb w4, [x3]
  ldr x17, =48
  sub x4, x4, x17
  ldr x17, =10
  subs xzr, x4, x17
  csinc w5, wzr, wzr, cs
  cbnz w5, lb_parse_dimacs_header.L44
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L44:
  ldr x17, =1
  add x3, x3, x17
  b lb_parse_dimacs_header.L46
  lb_parse_dimacs_header.L46:
  subs xzr, x3, x1
  csinc w5, wzr, wzr, ne
  cbnz w5, lb_parse_dimacs_header.L47
  ldrb w5, [x3]
  ldr x17, =48
  sub x6, x5, x17
  ldr x17, =10
  subs xzr, x6, x17
  csinc w7, wzr, wzr, cs
  cbnz w7, lb_parse_dimacs_header.L48
  ldr x17, =32
  subs xzr, x5, x17
  csinc w1, wzr, wzr, ne
  ldr x17, =9
  sub x5, x5, x17
  ldr x17, =5
  subs xzr, x5, x17
  csinc w5, wzr, wzr, cs
  orr x1, x1, x5
  cbnz w1, lb_parse_dimacs_header.L49
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L49:
  add x1, x4, #0
  b lb_parse_dimacs_header.L45
  lb_parse_dimacs_header.L48:
  ldr x17, =10
  madd x4, x4, x17, xzr
  add x4, x4, x6
  ldr x17, =268435456
  subs xzr, x4, x17
  csinc w5, wzr, wzr, cs
  cbnz w5, lb_parse_dimacs_header.L50
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L50:
  ldr x17, =1
  add x3, x3, x17
  b lb_parse_dimacs_header.L46
  lb_parse_dimacs_header.L47:
  add x1, x4, #0
  b lb_parse_dimacs_header.L45
  lb_parse_dimacs_header.L45:
  str x0, [x2]
  ldr x17, =8
  add x0, x2, x17
  str x1, [x0]
  ldr x17, =72
  add x0, x2, x17
  str x3, [x0]
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
  b lb_parse_dimacs_header.L0
  lb_parse_dimacs_header.L0:
  ldr x0, =0
  ldr x30, [sp]
  add sp, sp, #16
  ret")

def parseBodyCode : Program := parseAArch64("lb_parse_dimacs_body:
  sub sp, sp, #16
  str x30, [sp]
  ldr x2, [x1]
  ldr x17, =8
  add x3, x1, x17
  ldr x3, [x3]
  ldr x17, =48
  add x4, x1, x17
  ldr x4, [x4]
  ldr x17, =56
  add x5, x1, x17
  ldr x5, [x5]
  ldr x17, =64
  add x6, x1, x17
  ldr x7, [x6]
  ldr x17, =72
  add x1, x1, x17
  ldr x1, [x1]
  add x8, x7, #0
  add x7, x1, #0
  ldr x1, =1
  b lb_parse_dimacs_body.L1
  lb_parse_dimacs_body.L1:
  subs xzr, x3, x1
  csinc w9, wzr, wzr, cs
  cbnz w9, lb_parse_dimacs_body.L2
  add x9, x8, #0
  b lb_parse_dimacs_body.L3
  lb_parse_dimacs_body.L3:
  b lb_parse_dimacs_body.L5
  lb_parse_dimacs_body.L5:
  subs xzr, x7, x0
  csinc w10, wzr, wzr, ne
  cbnz w10, lb_parse_dimacs_body.L6
  ldrb w10, [x7]
  ldr x17, =1
  add x11, x7, x17
  ldr x17, =32
  subs xzr, x10, x17
  csinc w12, wzr, wzr, ne
  ldr x17, =9
  sub x13, x10, x17
  ldr x17, =5
  subs xzr, x13, x17
  csinc w13, wzr, wzr, cs
  orr x12, x12, x13
  cbnz w12, lb_parse_dimacs_body.L7
  ldr x17, =99
  subs xzr, x10, x17
  csinc w10, wzr, wzr, ne
  cbnz w10, lb_parse_dimacs_body.L8
  b lb_parse_dimacs_body.L4
  lb_parse_dimacs_body.L8:
  add x7, x11, #0
  b lb_parse_dimacs_body.L9
  lb_parse_dimacs_body.L9:
  subs xzr, x7, x0
  csinc w10, wzr, wzr, ne
  cbnz w10, lb_parse_dimacs_body.L10
  ldrb w10, [x7]
  ldr x17, =1
  add x7, x7, x17
  ldr x17, =10
  subs xzr, x10, x17
  csinc w10, wzr, wzr, ne
  cbnz w10, lb_parse_dimacs_body.L11
  b lb_parse_dimacs_body.L9
  lb_parse_dimacs_body.L11:
  b lb_parse_dimacs_body.L5
  lb_parse_dimacs_body.L10:
  b lb_parse_dimacs_body.L4
  lb_parse_dimacs_body.L7:
  add x7, x11, #0
  b lb_parse_dimacs_body.L5
  lb_parse_dimacs_body.L6:
  b lb_parse_dimacs_body.L4
  lb_parse_dimacs_body.L4:
  subs xzr, x7, x0
  csinc w10, wzr, wzr, ne
  cbnz w10, lb_parse_dimacs_body.L12
  subs xzr, x9, x5
  csinc w11, wzr, wzr, ne
  cbnz w11, lb_parse_dimacs_body.L13
  ldrb w11, [x7]
  ldr x17, =45
  subs xzr, x11, x17
  csinc w11, wzr, wzr, ne
  cbnz w11, lb_parse_dimacs_body.L14
  cbnz w10, lb_parse_dimacs_body.L15
  ldrb w10, [x7]
  ldr x17, =48
  sub x10, x10, x17
  ldr x17, =10
  subs xzr, x10, x17
  csinc w11, wzr, wzr, cs
  cbnz w11, lb_parse_dimacs_body.L16
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L16:
  ldr x17, =1
  add x7, x7, x17
  b lb_parse_dimacs_body.L18
  lb_parse_dimacs_body.L18:
  subs xzr, x7, x0
  csinc w11, wzr, wzr, ne
  cbnz w11, lb_parse_dimacs_body.L19
  ldrb w11, [x7]
  ldr x17, =48
  sub x12, x11, x17
  ldr x17, =10
  subs xzr, x12, x17
  csinc w13, wzr, wzr, cs
  cbnz w13, lb_parse_dimacs_body.L20
  ldr x17, =32
  subs xzr, x11, x17
  csinc w12, wzr, wzr, ne
  ldr x17, =9
  sub x11, x11, x17
  ldr x17, =5
  subs xzr, x11, x17
  csinc w11, wzr, wzr, cs
  orr x11, x12, x11
  cbnz w11, lb_parse_dimacs_body.L21
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L21:
  add x16, x7, #0
  add x7, x10, #0
  add x10, x16, #0
  b lb_parse_dimacs_body.L17
  lb_parse_dimacs_body.L20:
  ldr x17, =10
  madd x10, x10, x17, xzr
  add x10, x10, x12
  ldr x17, =268435456
  subs xzr, x10, x17
  csinc w11, wzr, wzr, cs
  cbnz w11, lb_parse_dimacs_body.L22
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L22:
  ldr x17, =1
  add x7, x7, x17
  b lb_parse_dimacs_body.L18
  lb_parse_dimacs_body.L19:
  add x16, x7, #0
  add x7, x10, #0
  add x10, x16, #0
  b lb_parse_dimacs_body.L17
  lb_parse_dimacs_body.L17:
  ldr x17, =0
  subs xzr, x7, x17
  csinc w11, wzr, wzr, ne
  cbnz w11, lb_parse_dimacs_body.L23
  subs xzr, x2, x7
  csinc w11, wzr, wzr, cs
  cbnz w11, lb_parse_dimacs_body.L24
  str w7, [x9]
  ldr x17, =4
  add x7, x9, x17
  add x9, x7, #0
  add x7, x10, #0
  b lb_parse_dimacs_body.L3
  lb_parse_dimacs_body.L24:
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L23:
  ldr x17, =0
  str w17, [x9]
  ldr x17, =4
  add x7, x9, x17
  ldr x17, =3
  lslv x9, x1, x17
  add x9, x4, x9
  str x8, [x9]
  ldr x17, =1
  add x1, x1, x17
  add x8, x7, #0
  add x7, x10, #0
  b lb_parse_dimacs_body.L1
  lb_parse_dimacs_body.L15:
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L14:
  ldr x17, =1
  add x7, x7, x17
  subs xzr, x7, x0
  csinc w10, wzr, wzr, ne
  cbnz w10, lb_parse_dimacs_body.L25
  ldrb w10, [x7]
  ldr x17, =48
  sub x10, x10, x17
  ldr x17, =10
  subs xzr, x10, x17
  csinc w11, wzr, wzr, cs
  cbnz w11, lb_parse_dimacs_body.L26
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L26:
  ldr x17, =1
  add x7, x7, x17
  b lb_parse_dimacs_body.L28
  lb_parse_dimacs_body.L28:
  subs xzr, x7, x0
  csinc w11, wzr, wzr, ne
  cbnz w11, lb_parse_dimacs_body.L29
  ldrb w11, [x7]
  ldr x17, =48
  sub x12, x11, x17
  ldr x17, =10
  subs xzr, x12, x17
  csinc w13, wzr, wzr, cs
  cbnz w13, lb_parse_dimacs_body.L30
  ldr x17, =32
  subs xzr, x11, x17
  csinc w12, wzr, wzr, ne
  ldr x17, =9
  sub x11, x11, x17
  ldr x17, =5
  subs xzr, x11, x17
  csinc w11, wzr, wzr, cs
  orr x11, x12, x11
  cbnz w11, lb_parse_dimacs_body.L31
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L31:
  add x16, x7, #0
  add x7, x10, #0
  add x10, x16, #0
  b lb_parse_dimacs_body.L27
  lb_parse_dimacs_body.L30:
  ldr x17, =10
  madd x10, x10, x17, xzr
  add x10, x10, x12
  ldr x17, =268435456
  subs xzr, x10, x17
  csinc w11, wzr, wzr, cs
  cbnz w11, lb_parse_dimacs_body.L32
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L32:
  ldr x17, =1
  add x7, x7, x17
  b lb_parse_dimacs_body.L28
  lb_parse_dimacs_body.L29:
  add x16, x7, #0
  add x7, x10, #0
  add x10, x16, #0
  b lb_parse_dimacs_body.L27
  lb_parse_dimacs_body.L27:
  ldr x17, =0
  subs xzr, x7, x17
  csinc w11, wzr, wzr, ne
  cbnz w11, lb_parse_dimacs_body.L33
  subs xzr, x2, x7
  csinc w11, wzr, wzr, cs
  cbnz w11, lb_parse_dimacs_body.L34
  ldr x16, =0
  sub x7, x16, x7
  str w7, [x9]
  ldr x17, =4
  add x7, x9, x17
  add x9, x7, #0
  add x7, x10, #0
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
  add x1, x7, #0
  b lb_parse_dimacs_body.L36
  lb_parse_dimacs_body.L36:
  subs xzr, x1, x0
  csinc w2, wzr, wzr, ne
  cbnz w2, lb_parse_dimacs_body.L37
  ldrb w2, [x1]
  ldr x17, =1
  add x3, x1, x17
  ldr x17, =32
  subs xzr, x2, x17
  csinc w4, wzr, wzr, ne
  ldr x17, =9
  sub x5, x2, x17
  ldr x17, =5
  subs xzr, x5, x17
  csinc w5, wzr, wzr, cs
  orr x4, x4, x5
  cbnz w4, lb_parse_dimacs_body.L38
  ldr x17, =99
  subs xzr, x2, x17
  csinc w2, wzr, wzr, ne
  cbnz w2, lb_parse_dimacs_body.L39
  b lb_parse_dimacs_body.L35
  lb_parse_dimacs_body.L39:
  add x1, x3, #0
  b lb_parse_dimacs_body.L40
  lb_parse_dimacs_body.L40:
  subs xzr, x1, x0
  csinc w2, wzr, wzr, ne
  cbnz w2, lb_parse_dimacs_body.L41
  ldrb w2, [x1]
  ldr x17, =1
  add x1, x1, x17
  ldr x17, =10
  subs xzr, x2, x17
  csinc w2, wzr, wzr, ne
  cbnz w2, lb_parse_dimacs_body.L42
  b lb_parse_dimacs_body.L40
  lb_parse_dimacs_body.L42:
  b lb_parse_dimacs_body.L36
  lb_parse_dimacs_body.L41:
  b lb_parse_dimacs_body.L35
  lb_parse_dimacs_body.L38:
  add x1, x3, #0
  b lb_parse_dimacs_body.L36
  lb_parse_dimacs_body.L37:
  b lb_parse_dimacs_body.L35
  lb_parse_dimacs_body.L35:
  subs xzr, x1, x0
  csinc w0, wzr, wzr, ne
  cbnz w0, lb_parse_dimacs_body.L43
  b lb_parse_dimacs_body.L0
  lb_parse_dimacs_body.L43:
  str x8, [x6]
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
  ldr x2, [x0]
  ldr x17, =56
  add x3, x0, x17
  ldr x3, [x3]
  ldr x17, =64
  add x4, x0, x17
  ldr x5, [x4]
  ldr x17, =72
  add x0, x0, x17
  ldr x6, [x0]
  add x7, x5, #0
  b lb_read_add_lits.L1
  lb_read_add_lits.L1:
  subs xzr, x7, x3
  csinc w8, wzr, wzr, ne
  cbnz w8, lb_read_add_lits.L2
  ldr x8, =0
  ldr x9, =0
  b lb_read_add_lits.L4
  lb_read_add_lits.L4:
  subs xzr, x6, x1
  csinc w10, wzr, wzr, ne
  cbnz w10, lb_read_add_lits.L5
  ldrb w10, [x6]
  ldr x17, =1
  add x6, x6, x17
  ldr x17, =127
  and x11, x10, x17
  lslv x11, x11, x9
  orr x8, x8, x11
  ldr x17, =128
  and x10, x10, x17
  ldr x17, =0
  subs xzr, x10, x17
  csinc w10, wzr, wzr, eq
  cbnz w10, lb_read_add_lits.L6
  add x16, x6, #0
  add x6, x8, #0
  add x8, x16, #0
  b lb_read_add_lits.L3
  lb_read_add_lits.L6:
  ldr x17, =7
  add x9, x9, x17
  ldr x17, =28
  subs xzr, x9, x17
  csinc w10, wzr, wzr, cs
  cbnz w10, lb_read_add_lits.L7
  b lb_read_add_lits.L0
  lb_read_add_lits.L7:
  b lb_read_add_lits.L4
  lb_read_add_lits.L5:
  b lb_read_add_lits.L0
  lb_read_add_lits.L3:
  ldr x17, =0
  subs xzr, x6, x17
  csinc w9, wzr, wzr, ne
  cbnz w9, lb_read_add_lits.L8
  ldr x17, =1
  lsrv x9, x6, x17
  ldr x17, =0
  subs xzr, x9, x17
  csinc w10, wzr, wzr, ne
  cbnz w10, lb_read_add_lits.L9
  subs xzr, x2, x9
  csinc w10, wzr, wzr, cs
  cbnz w10, lb_read_add_lits.L10
  ldr x17, =1
  and x6, x6, x17
  ldr x16, =0
  sub x6, x16, x6
  eor x9, x9, x6
  sub x6, x9, x6
  str w6, [x7]
  ldr x17, =4
  add x6, x7, x17
  add x7, x6, #0
  add x6, x8, #0
  b lb_read_add_lits.L1
  lb_read_add_lits.L10:
  b lb_read_add_lits.L0
  lb_read_add_lits.L9:
  b lb_read_add_lits.L0
  lb_read_add_lits.L8:
  ldr x17, =0
  str w17, [x7]
  ldr x17, =4
  add x1, x7, x17
  str x1, [x4]
  str x8, [x0]
  subs xzr, x7, x5
  csinc w0, wzr, wzr, ne
  cbnz w0, lb_read_add_lits.L11
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
  b lb_read_add_lits.L0
  lb_read_add_lits.L0:
  ldr x0, =0
  ldr x30, [sp]
  add sp, sp, #16
  ret")

def rupCheckCode : Program := parseAArch64("lb_rup_check:
  sub sp, sp, #48
  str x30, [sp, #32]
  ldr x17, =24
  add x4, x0, x17
  ldr x4, [x4]
  ldr x17, =32
  add x5, x0, x17
  ldr x5, [x5]
  ldr x17, =40
  add x6, x0, x17
  ldr x6, [x6]
  ldr x17, =48
  add x7, x0, x17
  ldr x7, [x7]
  ldr x17, =72
  add x0, x0, x17
  ldr x8, [x0]
  add x9, x5, #0
  b lb_rup_check.L3
  lb_rup_check.L3:
  ldrsw x10, [x2]
  cbnz w10, lb_rup_check.L4
  add x2, x8, #0
  add x8, x9, #0
  b lb_rup_check.L2
  lb_rup_check.L4:
  ldr x17, =63
  asrv x11, x10, x17
  eor x12, x10, x11
  sub x12, x12, x11
  add x12, x4, x12
  ldrsb x13, [x12]
  eor x13, x13, x11
  sub x11, x13, x11
  ldr x17, =4
  add x2, x2, x17
  ldr x17, =0
  subs xzr, x11, x17
  csinc w13, wzr, wzr, ge
  cbnz w13, lb_rup_check.L5
  ldr x16, =0
  subs xzr, x16, x11
  csinc w11, wzr, wzr, ge
  cbnz w11, lb_rup_check.L6
  ldr x16, =0
  sub x10, x16, x10
  subs xzr, x9, x6
  csinc w11, wzr, wzr, ne
  cbnz w11, lb_rup_check.L7
  ldr x17, =63
  asrv x11, x10, x17
  ldr x17, =1
  orr x11, x11, x17
  strb w11, [x12]
  str w10, [x9]
  ldr x17, =4
  add x9, x9, x17
  b lb_rup_check.L3
  lb_rup_check.L7:
  b lb_rup_check.L0
  lb_rup_check.L6:
  add x2, x8, #0
  add x6, x9, #0
  b lb_rup_check.L1
  lb_rup_check.L5:
  b lb_rup_check.L3
  lb_rup_check.L2:
  b lb_rup_check.L8
  lb_rup_check.L8:
  ldr x9, =0
  ldr x10, =0
  b lb_rup_check.L10
  lb_rup_check.L10:
  subs xzr, x2, x3
  csinc w11, wzr, wzr, ne
  cbnz w11, lb_rup_check.L11
  ldrb w11, [x2]
  ldr x17, =1
  add x2, x2, x17
  ldr x17, =127
  and x12, x11, x17
  lslv x12, x12, x10
  orr x9, x9, x12
  ldr x17, =128
  and x11, x11, x17
  ldr x17, =0
  subs xzr, x11, x17
  csinc w11, wzr, wzr, eq
  cbnz w11, lb_rup_check.L12
  add x16, x2, #0
  add x2, x9, #0
  add x9, x16, #0
  b lb_rup_check.L9
  lb_rup_check.L12:
  ldr x17, =7
  add x10, x10, x17
  ldr x17, =28
  subs xzr, x10, x17
  csinc w11, wzr, wzr, cs
  cbnz w11, lb_rup_check.L13
  b lb_rup_check.L0
  lb_rup_check.L13:
  b lb_rup_check.L10
  lb_rup_check.L11:
  b lb_rup_check.L0
  lb_rup_check.L9:
  ldr x17, =0
  subs xzr, x2, x17
  csinc w10, wzr, wzr, ne
  cbnz w10, lb_rup_check.L14
  ldr x17, =1
  and x10, x2, x17
  ldr x17, =0
  subs xzr, x10, x17
  csinc w10, wzr, wzr, eq
  cbnz w10, lb_rup_check.L15
  ldr x17, =1
  lsrv x2, x2, x17
  subs xzr, x2, x1
  csinc w10, wzr, wzr, cs
  cbnz w10, lb_rup_check.L16
  b lb_rup_check.L0
  lb_rup_check.L16:
  ldr x17, =3
  lslv x2, x2, x17
  add x2, x7, x2
  ldr x2, [x2]
  ldr x17, =0
  subs xzr, x2, x17
  csinc w10, wzr, wzr, eq
  cbnz w10, lb_rup_check.L17
  b lb_rup_check.L0
  lb_rup_check.L17:
  add x10, x8, #0
  ldr x8, =0
  b lb_rup_check.L19
  lb_rup_check.L19:
  ldrsw x11, [x2]
  cbnz w11, lb_rup_check.L20
  add x2, x8, #0
  add x8, x10, #0
  b lb_rup_check.L18
  lb_rup_check.L20:
  ldr x17, =63
  asrv x12, x11, x17
  eor x13, x11, x12
  sub x13, x13, x12
  add x13, x4, x13
  ldrsb x14, [x13]
  str x14, [sp]
  eor x14, x14, x12
  str x14, [sp, #8]
  sub x14, x14, x12
  str x14, [sp, #16]
  ldr x17, =4
  add x2, x2, x17
  ldr x14, [sp, #16]
  ldr x17, =0
  subs xzr, x14, x17
  csinc w14, wzr, wzr, ge
  str x14, [sp, #24]
  cbnz w14, lb_rup_check.L21
  cbnz w8, lb_rup_check.L23
  b lb_rup_check.L22
  lb_rup_check.L23:
  subs xzr, x8, x11
  csinc w8, wzr, wzr, ne
  cbnz w8, lb_rup_check.L24
  b lb_rup_check.L0
  lb_rup_check.L24:
  b lb_rup_check.L22
  lb_rup_check.L22:
  ldr x8, [sp, #16]
  ldr x17, =0
  subs xzr, x8, x17
  csinc w8, wzr, wzr, ne
  cbnz w8, lb_rup_check.L25
  add x8, x11, #0
  b lb_rup_check.L19
  lb_rup_check.L25:
  subs xzr, x10, x6
  csinc w8, wzr, wzr, ne
  cbnz w8, lb_rup_check.L26
  ldr x17, =1
  orr x8, x12, x17
  strb w8, [x13]
  str w11, [x10]
  ldr x17, =4
  add x8, x10, x17
  add x10, x8, #0
  add x8, x11, #0
  b lb_rup_check.L19
  lb_rup_check.L26:
  b lb_rup_check.L0
  lb_rup_check.L21:
  ldr x16, =0
  sub x11, x16, x11
  subs xzr, x8, x11
  csinc w11, wzr, wzr, ne
  cbnz w11, lb_rup_check.L27
  b lb_rup_check.L19
  lb_rup_check.L27:
  b lb_rup_check.L0
  lb_rup_check.L18:
  cbnz w2, lb_rup_check.L28
  add x2, x9, #0
  add x6, x8, #0
  b lb_rup_check.L1
  lb_rup_check.L28:
  add x2, x9, #0
  b lb_rup_check.L8
  lb_rup_check.L15:
  b lb_rup_check.L0
  lb_rup_check.L14:
  b lb_rup_check.L0
  lb_rup_check.L1:
  b lb_rup_check.L29
  lb_rup_check.L29:
  ldr x8, =0
  ldr x9, =0
  b lb_rup_check.L31
  lb_rup_check.L31:
  subs xzr, x2, x3
  csinc w10, wzr, wzr, ne
  cbnz w10, lb_rup_check.L32
  ldrb w10, [x2]
  ldr x17, =1
  add x2, x2, x17
  ldr x17, =127
  and x11, x10, x17
  lslv x11, x11, x9
  orr x8, x8, x11
  ldr x17, =128
  and x10, x10, x17
  ldr x17, =0
  subs xzr, x10, x17
  csinc w10, wzr, wzr, eq
  cbnz w10, lb_rup_check.L33
  add x16, x2, #0
  add x2, x8, #0
  add x8, x16, #0
  b lb_rup_check.L30
  lb_rup_check.L33:
  ldr x17, =7
  add x9, x9, x17
  ldr x17, =28
  subs xzr, x9, x17
  csinc w10, wzr, wzr, cs
  cbnz w10, lb_rup_check.L34
  b lb_rup_check.L0
  lb_rup_check.L34:
  b lb_rup_check.L31
  lb_rup_check.L32:
  b lb_rup_check.L0
  lb_rup_check.L30:
  ldr x17, =0
  subs xzr, x2, x17
  csinc w9, wzr, wzr, ne
  cbnz w9, lb_rup_check.L35
  ldr x17, =1
  and x9, x2, x17
  ldr x17, =0
  subs xzr, x9, x17
  csinc w9, wzr, wzr, eq
  cbnz w9, lb_rup_check.L36
  ldr x17, =1
  lsrv x2, x2, x17
  subs xzr, x2, x1
  csinc w9, wzr, wzr, cs
  cbnz w9, lb_rup_check.L37
  b lb_rup_check.L0
  lb_rup_check.L37:
  ldr x17, =3
  lslv x2, x2, x17
  add x2, x7, x2
  ldr x2, [x2]
  ldr x17, =0
  subs xzr, x2, x17
  csinc w2, wzr, wzr, eq
  cbnz w2, lb_rup_check.L38
  b lb_rup_check.L0
  lb_rup_check.L38:
  add x2, x8, #0
  b lb_rup_check.L29
  lb_rup_check.L36:
  b lb_rup_check.L0
  lb_rup_check.L35:
  add x1, x5, #0
  b lb_rup_check.L39
  lb_rup_check.L39:
  subs xzr, x1, x6
  csinc w2, wzr, wzr, ne
  cbnz w2, lb_rup_check.L40
  ldrsw x2, [x1]
  ldr x17, =63
  asrv x3, x2, x17
  eor x2, x2, x3
  sub x2, x2, x3
  add x2, x4, x2
  ldr x17, =0
  strb w17, [x2]
  ldr x17, =4
  add x1, x1, x17
  b lb_rup_check.L39
  lb_rup_check.L40:
  str x8, [x0]
  ldr x0, =1
  ldr x30, [sp, #32]
  add sp, sp, #48
  ret
  lb_rup_check.L0:
  ldr x0, =0
  ldr x30, [sp, #32]
  add sp, sp, #48
  ret")

def checkPrfCode : Program := parseAArch64("lb_check_prf:
  sub sp, sp, #96
  str x30, [sp, #88]
  str x0, [sp]
  str x1, [sp, #8]
  ldr x17, =8
  add x0, x0, x17
  ldr x0, [x0]
  str x0, [sp, #16]
  ldr x0, [sp]
  ldr x17, =16
  add x0, x0, x17
  ldr x0, [x0]
  str x0, [sp, #24]
  ldr x0, [sp]
  ldr x17, =48
  add x0, x0, x17
  ldr x0, [x0]
  str x0, [sp, #32]
  ldr x0, [sp]
  ldr x17, =64
  add x0, x0, x17
  str x0, [sp, #40]
  ldr x0, [sp]
  ldr x17, =72
  add x0, x0, x17
  str x0, [sp, #48]
  b lb_check_prf.L1
  lb_check_prf.L1:
  ldr x0, [sp, #48]
  ldr x0, [x0]
  ldr x1, [sp, #8]
  subs xzr, x0, x1
  csinc w1, wzr, wzr, ne
  cbnz w1, lb_check_prf.L2
  ldrb w1, [x0]
  ldr x17, =1
  add x0, x0, x17
  ldr x17, =97
  subs xzr, x1, x17
  csinc w2, wzr, wzr, ne
  cbnz w2, lb_check_prf.L3
  ldr x17, =100
  subs xzr, x1, x17
  csinc w1, wzr, wzr, ne
  cbnz w1, lb_check_prf.L4
  b lb_check_prf.L0
  lb_check_prf.L4:
  b lb_check_prf.L5
  lb_check_prf.L5:
  ldr x1, =0
  ldr x2, =0
  b lb_check_prf.L7
  lb_check_prf.L7:
  ldr x3, [sp, #8]
  subs xzr, x0, x3
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_check_prf.L8
  ldrb w3, [x0]
  ldr x17, =1
  add x0, x0, x17
  ldr x17, =127
  and x4, x3, x17
  lslv x4, x4, x2
  orr x1, x1, x4
  ldr x17, =128
  and x3, x3, x17
  ldr x17, =0
  subs xzr, x3, x17
  csinc w3, wzr, wzr, eq
  cbnz w3, lb_check_prf.L9
  add x16, x0, #0
  add x0, x1, #0
  add x1, x16, #0
  b lb_check_prf.L6
  lb_check_prf.L9:
  ldr x17, =7
  add x2, x2, x17
  ldr x17, =28
  subs xzr, x2, x17
  csinc w3, wzr, wzr, cs
  cbnz w3, lb_check_prf.L10
  b lb_check_prf.L0
  lb_check_prf.L10:
  b lb_check_prf.L7
  lb_check_prf.L8:
  b lb_check_prf.L0
  lb_check_prf.L6:
  ldr x17, =0
  subs xzr, x0, x17
  csinc w2, wzr, wzr, ne
  cbnz w2, lb_check_prf.L11
  ldr x17, =1
  and x2, x0, x17
  ldr x17, =0
  subs xzr, x2, x17
  csinc w2, wzr, wzr, eq
  cbnz w2, lb_check_prf.L12
  ldr x17, =1
  lsrv x0, x0, x17
  ldr x17, =0
  subs xzr, x0, x17
  csinc w2, wzr, wzr, ne
  cbnz w2, lb_check_prf.L13
  ldr x2, [sp, #24]
  subs xzr, x0, x2
  csinc w2, wzr, wzr, cs
  cbnz w2, lb_check_prf.L14
  b lb_check_prf.L0
  lb_check_prf.L14:
  ldr x17, =3
  lslv x0, x0, x17
  ldr x2, [sp, #32]
  add x0, x2, x0
  ldr x2, [x0]
  ldr x17, =0
  subs xzr, x2, x17
  csinc w2, wzr, wzr, eq
  cbnz w2, lb_check_prf.L15
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
  ldr x0, [sp, #48]
  str x1, [x0]
  b lb_check_prf.L1
  lb_check_prf.L3:
  ldr x1, =0
  ldr x2, =0
  b lb_check_prf.L17
  lb_check_prf.L17:
  ldr x3, [sp, #8]
  subs xzr, x0, x3
  csinc w3, wzr, wzr, ne
  cbnz w3, lb_check_prf.L18
  ldrb w3, [x0]
  ldr x17, =1
  add x0, x0, x17
  ldr x17, =127
  and x4, x3, x17
  lslv x4, x4, x2
  orr x1, x1, x4
  ldr x17, =128
  and x3, x3, x17
  ldr x17, =0
  subs xzr, x3, x17
  csinc w3, wzr, wzr, eq
  cbnz w3, lb_check_prf.L19
  add x16, x0, #0
  add x0, x1, #0
  add x1, x16, #0
  b lb_check_prf.L16
  lb_check_prf.L19:
  ldr x17, =7
  add x2, x2, x17
  ldr x17, =28
  subs xzr, x2, x17
  csinc w3, wzr, wzr, cs
  cbnz w3, lb_check_prf.L20
  b lb_check_prf.L0
  lb_check_prf.L20:
  b lb_check_prf.L17
  lb_check_prf.L18:
  b lb_check_prf.L0
  lb_check_prf.L16:
  ldr x17, =1
  and x2, x0, x17
  ldr x17, =0
  subs xzr, x2, x17
  csinc w2, wzr, wzr, eq
  cbnz w2, lb_check_prf.L21
  ldr x17, =1
  lsrv x0, x0, x17
  str x0, [sp, #56]
  ldr x2, [sp, #16]
  subs xzr, x2, x0
  csinc w0, wzr, wzr, cs
  cbnz w0, lb_check_prf.L22
  b lb_check_prf.L0
  lb_check_prf.L22:
  ldr x0, [sp, #56]
  ldr x2, [sp, #24]
  subs xzr, x0, x2
  csinc w0, wzr, wzr, cs
  cbnz w0, lb_check_prf.L23
  b lb_check_prf.L0
  lb_check_prf.L23:
  ldr x0, [sp, #56]
  ldr x17, =3
  lslv x0, x0, x17
  ldr x2, [sp, #32]
  add x0, x2, x0
  str x0, [sp, #64]
  ldr x0, [x0]
  ldr x17, =0
  subs xzr, x0, x17
  csinc w0, wzr, wzr, eq
  cbnz w0, lb_check_prf.L24
  ldr x0, [sp, #48]
  str x1, [x0]
  ldr x0, [sp, #40]
  ldr x0, [x0]
  str x0, [sp, #72]
  ldr x0, [sp]
  ldr x1, [sp, #8]
  bl lb_read_add_lits
  str x0, [sp, #80]
  ldr x17, =0
  subs xzr, x0, x17
  csinc w0, wzr, wzr, eq
  cbnz w0, lb_check_prf.L25
  b lb_check_prf.L0
  lb_check_prf.L25:
  ldr x0, [sp]
  ldr x1, [sp, #56]
  ldr x2, [sp, #72]
  ldr x3, [sp, #8]
  bl lb_rup_check
  ldr x17, =0
  subs xzr, x0, x17
  csinc w0, wzr, wzr, eq
  cbnz w0, lb_check_prf.L26
  b lb_check_prf.L0
  lb_check_prf.L26:
  ldr x0, [sp, #80]
  ldr x17, =2
  subs xzr, x0, x17
  csinc w0, wzr, wzr, ne
  cbnz w0, lb_check_prf.L27
  ldr x0, [sp, #72]
  ldr x1, [sp, #64]
  str x0, [x1]
  b lb_check_prf.L1
  lb_check_prf.L27:
  ldr x0, =1
  ldr x30, [sp, #88]
  add sp, sp, #96
  ret
  lb_check_prf.L24:
  b lb_check_prf.L0
  lb_check_prf.L21:
  b lb_check_prf.L0
  lb_check_prf.L2:
  b lb_check_prf.L0
  lb_check_prf.L0:
  ldr x0, =0
  ldr x30, [sp, #88]
  add sp, sp, #96
  ret")

def lratCheckBytesCode : Program := parseAArch64("lrat_check_bytes:
  sub sp, sp, #64
  str x30, [sp, #48]
  str x2, [sp]
  str x3, [sp, #8]
  str x4, [sp, #16]
  str x5, [sp, #24]
  ldr x17, =128
  subs xzr, x5, x17
  csinc w2, wzr, wzr, cs
  cbnz w2, lrat_check_bytes.L0
  add x1, x0, x1
  str x1, [sp, #32]
  ldr x1, [sp]
  ldr x2, [sp, #8]
  add x1, x1, x2
  str x1, [sp, #40]
  ldr x1, [sp, #32]
  add x2, x4, #0
  bl lb_parse_dimacs_header
  ldr x17, =0
  subs xzr, x0, x17
  csinc w0, wzr, wzr, eq
  cbnz w0, lrat_check_bytes.L1
  ldr x0, =0
  ldr x30, [sp, #48]
  add sp, sp, #64
  ret
  lrat_check_bytes.L1:
  ldr x0, [sp, #16]
  ldr x0, [x0]
  ldr x1, [sp, #16]
  ldr x17, =8
  add x1, x1, x17
  ldr x1, [x1]
  ldr x17, =1
  add x2, x0, x17
  ldr x17, =8
  add x3, x0, x17
  ldr x17, =-8
  and x3, x3, x17
  ldr x17, =2
  lslv x2, x2, x17
  ldr x17, =7
  add x4, x2, x17
  ldr x17, =-8
  and x4, x4, x17
  add x5, x3, x4
  ldr x16, =80
  add x5, x16, x5
  ldr x6, [sp, #24]
  subs xzr, x6, x5
  csinc w6, wzr, wzr, cs
  cbnz w6, lrat_check_bytes.L2
  ldr x6, [sp, #24]
  sub x5, x6, x5
  ldr x17, =4
  lsrv x6, x5, x17
  ldr x7, [sp, #8]
  ldr x17, =268435455
  and x7, x7, x17
  add x7, x1, x7
  ldr x17, =32
  add x7, x7, x17
  subs xzr, x6, x7
  csinc w8, wzr, wzr, cs
  cbnz w8, lrat_check_bytes.L4
  add x6, x7, #0
  b lrat_check_bytes.L3
  lrat_check_bytes.L4:
  b lrat_check_bytes.L3
  lrat_check_bytes.L3:
  subs xzr, x6, x1
  csinc w1, wzr, wzr, hi
  cbnz w1, lrat_check_bytes.L5
  ldr x1, [sp, #16]
  ldr x17, =80
  add x1, x1, x17
  add x3, x1, x3
  add x2, x3, x2
  add x4, x3, x4
  ldr x17, =3
  lslv x7, x6, x17
  add x8, x4, x7
  sub x5, x5, x7
  ldr x17, =-4
  and x5, x5, x17
  add x5, x8, x5
  ldr x7, =0
  b lrat_check_bytes.L7
  lrat_check_bytes.L7:
  subs xzr, x7, x0
  csinc w9, wzr, wzr, hi
  cbnz w9, lrat_check_bytes.L8
  b lrat_check_bytes.L6
  lrat_check_bytes.L8:
  add x9, x1, x7
  ldr x17, =0
  strb w17, [x9]
  ldr x17, =1
  add x7, x7, x17
  b lrat_check_bytes.L7
  lrat_check_bytes.L6:
  ldr x0, =0
  b lrat_check_bytes.L10
  lrat_check_bytes.L10:
  subs xzr, x0, x6
  csinc w7, wzr, wzr, cs
  cbnz w7, lrat_check_bytes.L11
  b lrat_check_bytes.L9
  lrat_check_bytes.L11:
  ldr x17, =3
  lslv x7, x0, x17
  add x7, x4, x7
  ldr x17, =0
  str x17, [x7]
  ldr x17, =1
  add x0, x0, x17
  b lrat_check_bytes.L10
  lrat_check_bytes.L9:
  ldr x0, [sp, #16]
  ldr x17, =16
  add x0, x0, x17
  str x6, [x0]
  ldr x0, [sp, #16]
  ldr x17, =24
  add x0, x0, x17
  str x1, [x0]
  ldr x0, [sp, #16]
  ldr x17, =32
  add x0, x0, x17
  str x3, [x0]
  ldr x0, [sp, #16]
  ldr x17, =40
  add x0, x0, x17
  str x2, [x0]
  ldr x0, [sp, #16]
  ldr x17, =48
  add x0, x0, x17
  str x4, [x0]
  ldr x0, [sp, #16]
  ldr x17, =56
  add x0, x0, x17
  str x5, [x0]
  ldr x0, [sp, #16]
  ldr x17, =64
  add x0, x0, x17
  str x8, [x0]
  ldr x0, [sp, #32]
  ldr x1, [sp, #16]
  bl lb_parse_dimacs_body
  ldr x17, =0
  subs xzr, x0, x17
  csinc w0, wzr, wzr, eq
  cbnz w0, lrat_check_bytes.L12
  ldr x0, =0
  ldr x30, [sp, #48]
  add sp, sp, #64
  ret
  lrat_check_bytes.L12:
  ldr x0, [sp, #16]
  ldr x17, =72
  add x0, x0, x17
  ldr x1, [sp]
  str x1, [x0]
  ldr x0, [sp, #16]
  ldr x1, [sp, #40]
  bl lb_check_prf
  ldr x30, [sp, #48]
  add sp, sp, #64
  ret
  lrat_check_bytes.L5:
  ldr x0, =0
  ldr x30, [sp, #48]
  add sp, sp, #64
  ret
  lrat_check_bytes.L2:
  ldr x0, =0
  ldr x30, [sp, #48]
  add sp, sp, #64
  ret
  lrat_check_bytes.L0:
  ldr x0, =0
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
   ("lb_rup_check", 48),
   ("lb_check_prf", 144),
   ("lrat_check_bytes", 208)]

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

/-- Lifting any `FnSpec` for `"lrat_check_bytes"` at stack bound `208` and contract
`lratCheckBytesSpec` to the closed Kraken-AArch64 statement. -/
theorem lrat_check_bytes_arm64_of_fnspec
    (hfnspec : target.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec 208 0)
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
      (fun f => ∃ bs : List UInt8, bs.length = 208 ∧ f = bs.At (s.regs.SP.toBitVec - 208#64)) ⋆ R) :
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
          (fun f => ∃ bs : List UInt8, bs.length = 208 ∧
            f = bs.At (s.regs.SP.toBitVec - 208#64)) ⋆ R))
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
  have hmem' : target.mem s =⋆ Eq m ⋆ target.Entry (target.get s target.sp) ra 208 ⋆ R := by
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
    (hfnspec : target.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec 208 0)
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
      (fun f => ∃ bs : List UInt8, bs.length = 208 ∧ f = bs.At (s.regs.SP.toBitVec - 208#64)) ⋆ R) :
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

def zeros208 : List UInt8 := List.replicate 208 0
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
    dmem := (zeros208 ++ ((cnfBytes ++ prfBytes) ++ zeros512)).At 0x0f30#64 }

theorem lratBytesState_mem (cnfBytes prfBytes : List UInt8)
    (hcb : cnfBytes.length ≤ 4096) (hpb : prfBytes.length ≤ 4096) :
    (lratBytesState cnfBytes prfBytes).dmem =⋆
      (Eq (cnfBytes.At nvCnfPtr) ⋆
        Eq (prfBytes.At (nvPrfPtr cnfBytes)) ⋆
        region (nvWorkPtr cnfBytes prfBytes) 512) ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 208 ∧
        f = bs.At ((lratBytesState cnfBytes prfBytes).regs.SP.toBitVec - 208#64)) ⋆
      Std.ExtHashMap.emp := by
  have h208 : zeros208.length = 208 := List.length_replicate
  have h512 : zeros512.length = 512 := List.length_replicate
  have hsp_eq : (lratBytesState cnfBytes prfBytes).regs.SP.toBitVec = 0x1000#64 := rfl
  have hsp_sub : (lratBytesState cnfBytes prfBytes).regs.SP.toBitVec - 208#64 = 0x0f30#64 := by
    rw [hsp_eq]; decide
  rw [hsp_sub, Std.ExtHashMap.sep_emp]
  have h1 := Mem.At_append_sep zeros208 ((cnfBytes ++ prfBytes) ++ zeros512) 0x0f30#64
    (by simp only [List.length_append, h208, h512]; omega)
  have e1 : 0x0f30#64 + BitVec.ofNat 64 zeros208.length = nvCnfPtr := by simp [nvCnfPtr, h208]
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
  have h0 : (Eq ((zeros208 ++ ((cnfBytes ++ prfBytes) ++ zeros512)).At 0x0f30#64))
      (lratBytesState cnfBytes prfBytes).dmem := rfl
  rw [h1, Std.ExtHashMap.sep_comm] at h0
  refine sep_mono (fun fL hfL => ?_) (sep_mono_r (fun fS hfS => ⟨zeros208, h208, hfS.symm⟩) h0)
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
      (fun f => ∃ bs : List UInt8, bs.length = 208 ∧ f = bs.At (s.regs.SP.toBitVec - 208#64)) ⋆ R) :
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
          (fun f => ∃ bs : List UInt8, bs.length = 208 ∧
            f = bs.At (s.regs.SP.toBitVec - 208#64)) ⋆ R))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_arm64_of_fnspec
    (by simpa [lratBytesEnv_entry] using
      (lrat_bytes_module_fnspec k₀ hc hu ⟨"lrat_check_bytes", 208⟩ (by simp [lratBytesBounds])).2)
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
      (fun f => ∃ bs : List UInt8, bs.length = 208 ∧ f = bs.At (s.regs.SP.toBitVec - 208#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        ((st.data.regs.getXReg .X0).toBitVec = 0 ∨ (st.data.regs.getXReg .X0).toBitVec = 1) ∧
        ((st.data.regs.getXReg .X0).toBitVec = 1 → cnf.Unsat))
      ⟨s, Labels.label "lrat_check_bytes"⟩ :=
  lrat_check_bytes_arm64_unsat_of_fnspec
    (by simpa [lratBytesEnv_entry] using
      (lrat_bytes_module_fnspec k₀ hc hu ⟨"lrat_check_bytes", 208⟩ (by simp [lratBytesBounds])).2)
    cnf cnf_ptr prf_ptr work_ptr (encodeDimacs cnf) prfBytes work_len
    (parseDimacs_encodeDimacs hvalid)
    hcnf hprf hwork s ra R hx0 hx1 hx2 hx3 hx4 hx5 hra hsp hmem

private theorem lratBytesState_call {spec : Spec}
    (hfnspec : target.FnSpec lratBytesHost "lrat_check_bytes" spec 208 0)
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
  have hmem' : target.mem s0 =⋆ Eq m ⋆ target.Entry (target.get s0 target.sp) 0x1234 208 ⋆
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
    ⟨"lrat_check_bytes", 208⟩ (by simp [lratBytesBounds])).2
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
    ⟨"lrat_check_bytes", 208⟩ (by simp [lratBytesBounds])).2
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
