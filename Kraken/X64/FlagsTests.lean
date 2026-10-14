module

/-
  Concrete-evaluation tests of the flag helpers, for behaviour the hardware asm tests cannot
  observe on their own.
-/

import Kraken.X64.Parser
meta import Kraken.X64.Parser
import Kraken.X64.Semantics
meta import Kraken.X64.Semantics

/-- Runs `e` to completion, granting every access check and resolving every `undefined` choice
with `h`; `none` if it does not finish. -/
private partial def finish (h : UInt64) : Effects → Option MachineData
  | .done (s, _) => some s
  | .require_read_access _ _ ok | .require_write_access _ _ ok | .require_exec_access _ ok => finish h (ok ())
  | @Effects.undefined _ t cont => finish h (cont (t.from_hash h))
  | _ => none

/-- The status flags after the single instruction `asm` runs from `status` with all registers
zero. -/
private def statusAfter (asm : String) (status : StatusFlags) (h : UInt64 := 0) : Option StatusFlags := do
  let exe := (← (Kraken.X64.Parser.parse asm).toOption).fakeLayout
  let := exe.labels
  let (pc, dir, sz) ← exe.withAddresses.head?
  let p : Std.Rco Int64 := .mk pc (pc + .ofNat sz)
  let s ← finish h (dir.interp { status } p (fun s => .done (s, p.upper)) (fun _ _ => .unimplemented "jump"))
  return s.status

private def dfSet : StatusFlags := { cf := false, pf := false, af := false, zf := false, sf := false, of := false, df := true }

/-- `asm` keeps DF set, under both resolutions of its `undefined` choices. -/
private def keepsDf (asm : String) : Bool :=
  (statusAfter asm dfSet).map (·.df) == some true && (statusAfter asm dfSet (h := -1)).map (·.df) == some true

-- Instructions that compute status flags keep DF; only cld, std and popf change it.
#guard keepsDf "addq $1, %rax"
#guard keepsDf "subq $1, %rax"
#guard keepsDf "incq %rax"
#guard keepsDf "decq %rax"
#guard keepsDf "negq %rax"
#guard keepsDf "testq $1, %rax"
#guard keepsDf "andq $1, %rax"
#guard keepsDf "xorq $1, %rax"
#guard keepsDf "imulq %rcx, %rax"
#guard keepsDf "shlq $1, %rax"
#guard keepsDf "shrq $1, %rax"
#guard keepsDf "sarq $1, %rax"
#guard keepsDf "shrdq $1, %rcx, %rax"
#guard keepsDf "shldq $1, %rcx, %rax"
-- A count above the operand size leaves every status flag undefined, but DF is not one.
#guard keepsDf "shrdw $17, %cx, %ax"
#guard keepsDf "shldw $17, %cx, %ax"
-- The flags that `from_result` does derive from the result are still computed.
#guard (statusAfter "addq $0, %rax" dfSet).map (·.zf) == some true
#guard (statusAfter "shlq $1, %rax" dfSet).map (·.zf) == some true
