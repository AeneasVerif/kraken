module

public import LeanQbe.T.Main
public import LeanQbe.T.DebugAsmCommon
public import LeanQbe.T.Arm64.Frame
public import Kraken.AArch64.Print
import Std.Data.HashSet

/-!
# AAPCS64 Arm64 Debug Assembly & CFI Unwind Emitter

Transforms verified `List Kraken.AArch64.Directive` output from `LeanQbe.T.compile` into
ELF-clean AArch64 assembly with **zero** instruction changes in normal frames:
* ELF function metadata: `.p2align 2`, `.globl fn`, `.type fn, %function`, `.size fn, .-fn`,
  and `.ltorg` strictly after `.size` so literal pools never fall inside `.size` or FDE bounds.
* Local label scrubbing: rewrites `{fn}.L{i}` definitions and branch/literal references to
  `.L{fn}.L{i}` so zero `NOTYPE LOCAL` block symbols leak into `.symtab`.
* Exact static-frame DWARF CFI: `.cfi_startproc`, `.cfi_def_cfa_offset`, `.cfi_offset x30`,
  `.cfi_offset` for `saveCs`, `.cfi_restore`, `.cfi_def_cfa_offset 0`, and
  `.cfi_remember_state` / `.cfi_restore_state` across multi-exit `ret` and tail-call `b`
  boundaries, closed by `.cfi_endproc`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open Std
open LeanQbe.T LeanQbe.T.DebugAsmCommon Kraken Kraken.AArch64

/-- Frame hints specialization for AAPCS64 Arm64 (`armTarget`). -/
abbrev Arm64Hints : Type := Hints Reg Empty ArmCond

private def dirLabel? : Directive → Option Sym | .label l => some l | _ => none

private def scrubConst (fn : Sym) (nonLocal : HashSet Sym) : ConstExpr → ConstExpr
  | .label l => .label (scrubSym fn nonLocal l)
  | .add a b => .add (scrubConst fn nonLocal a) (scrubConst fn nonLocal b)
  | .sub a b => .sub (scrubConst fn nonLocal a) (scrubConst fn nonLocal b)
  | .pg_hi21 a => .pg_hi21 (scrubConst fn nonLocal a)
  | .lo12 a => .lo12 (scrubConst fn nonLocal a)
  | e => e

private def scrubAddr (fn : Sym) (nonLocal : HashSet Sym) (a : AddrExpr) : AddrExpr :=
  { a with off := match a.off with
      | .imm ie => .imm { ie with imm := scrubConst fn nonLocal ie.imm }
      | .reg r => .reg r }

private def scrubUAddr (fn : Sym) (nonLocal : HashSet Sym)
    (a : UnscaledAddrExpr) : UnscaledAddrExpr :=
  { a with imm := scrubConst fn nonLocal a.imm }

private def scrubAddrOrLit (fn : Sym) (nonLocal : HashSet Sym) : AddrOrLit → AddrOrLit
  | .addr a => .addr (scrubAddr fn nonLocal a)
  | .lit (.addr la) => .lit (.addr { label := scrubSym fn nonLocal la.label })
  | .lit (.pool lp) => .lit (.pool { expr := scrubConst fn nonLocal lp.expr })

private def scrubOp {w : RegWidth} (fn : Sym) (nonLocal : HashSet Sym) :
    Operation w → Operation w := fun op =>
  let sa := scrubAddr fn nonLocal; let su := scrubUAddr fn nonLocal
  let sal := scrubAddrOrLit fn nonLocal; let kc := scrubConst fn nonLocal
  match op with
  | .LDR r al => .LDR r (sal al) | .STR r a => .STR r (sa a) | .LDUR r u => .LDUR r (su u)
  | .STUR r u => .STUR r (su u) | .LDP r1 r2 a => .LDP r1 r2 (sa a)
  | .STP r1 r2 a => .STP r1 r2 (sa a) | .LDRB r a => .LDRB r (sa a)
  | .LDURB r u => .LDURB r (su u) | .STRB r a => .STRB r (sa a) | .STURB r u => .STURB r (su u)
  | .LDRSB r a => .LDRSB r (sa a) | .LDURSB r u => .LDURSB r (su u)
  | .LDRH r a => .LDRH r (sa a) | .LDURH r u => .LDURH r (su u)
  | .STRH r a => .STRH r (sa a) | .STURH r u => .STURH r (su u)
  | .LDRSH r a => .LDRSH r (sa a) | .LDURSH r u => .LDURSH r (su u)
  | .LDRSW r al => .LDRSW r (sal al) | .LDURSW r u => .LDURSW r (su u)
  | .LDPSW r1 r2 a => .LDPSW r1 r2 (sa a) | .AND_i d s c => .AND_i d s (kc c)
  | .ANDS_i d s c => .ANDS_i d s (kc c) | .ORR_i d s c => .ORR_i d s (kc c)
  | .EOR_i d s c => .EOR_i d s (kc c) | .MOVZ d c ms => .MOVZ d (kc c) ms
  | .MOVK d c ms => .MOVK d (kc c) ms | .MOVN d c ms => .MOVN d (kc c) ms
  | .ADR d c => .ADR d (kc c) | .ADRP d c => .ADRP d (kc c) | .B c => .B (kc c)
  | .B_cond cc c => .B_cond cc (kc c) | .BL c => .BL (kc c)
  | .CBZ r c => .CBZ r (kc c) | .CBNZ r c => .CBNZ r (kc c)
  | .TBZ r b c => .TBZ r b (kc c) | .TBNZ r b c => .TBNZ r b (kc c)
  | op => op

private def scrubDir (fn : Sym) (nonLocal : HashSet Sym) : Directive → Directive
  | .instr i => .instr ⟨i.operation_size, scrubOp fn nonLocal i.operation⟩
  | .label l => .label (scrubSym fn nonLocal l)
  | .byteArray bs => .byteArray bs | .word n e => .word n (scrubConst fn nonLocal e)

private def cfiReg : Reg → String
  | .reg x => Print.xreg .W64 x | .SP => "sp"

private def isTailDir (fn : Sym) (nonLocal : HashSet Sym) : Directive → Option String
  | .instr ⟨.W64, .RET (.low (.reg .X30) .W64)⟩ => some "ret"
  | .instr ⟨.W64, .B (.label sym)⟩ =>
    if isLocalFnLabel fn nonLocal sym then none else some s!"b {sym}"
  | _ => none

private def csReg? (x : XReg) : Option Reg :=
  let r : Reg := .reg x; if armFrame.calleeSaved.contains r then some r else none

private def matchArmSubSp (body : List Directive) : Option (Nat × List Directive) :=
  match body with
  | .instr ⟨.W64, .SUB_e (.low .SP .W64) (.low .SP .W64) (.imm ⟨.int64 c, .S0⟩)⟩ :: rest =>
    let sz := c.toInt.toNat
    if c.toInt >= 16 && body.take 1 == emitClean (armSubSpIns sz) then some (sz, rest) else none
  | .instr ⟨.W64, .LDR (.low (.reg .X16) .W64) (.lit (.pool ⟨.int64 c⟩))⟩ ::
    .instr ⟨.W64, .SUB_e (.low .SP .W64) (.low .SP .W64) (.ext _)⟩ :: rest =>
    let sz := c.toUInt64.toNat
    if sz >= 16 && sz % 16 == 0 && body.take 2 == emitClean (armSubSpIns sz) then
      some (sz, rest) else none
  | _ => none

private def matchArmStSpX (ds : List Directive) : Option (Nat × XReg × List Directive) :=
  match ds with
  | .instr ⟨.W64,
      .STR (.low (.reg r) .W64) ⟨.low .SP .W64, .imm ⟨.int64 c, none⟩⟩⟩ :: rest =>
    let off := c.toInt.toNat
    if c.toInt >= 0 && c.toInt % 8 == 0 && ds.take 1 == emitClean (armStSpXRegIns r off) then
      some (off, r, rest) else none
  | .instr ⟨.W64, .LDR (.low (.reg .X16) .W64) (.lit (.pool ⟨.int64 c⟩))⟩ ::
    .instr ⟨.W64, .STR (.low (.reg r) .W64) ⟨.low .SP .W64, .reg _⟩⟩ :: rest =>
    let off := c.toUInt64.toNat
    if off % 8 == 0 && ds.take 2 == emitClean (armStSpXRegIns r off) then
      some (off, r, rest) else none
  | _ => none

private def matchArmSaveStep (ds : List Directive) : Option (Nat × List Reg × List Directive) :=
  match ds with
  | .instr ⟨.W64, .STP (.low (.reg x1) .W64) (.low (.reg x2) .W64)
      ⟨.low .SP .W64, .imm ⟨.int64 c, none⟩⟩⟩ :: rest => do
    let r1 ← csReg? x1; let r2 ← csReg? x2; let off := c.toInt.toNat
    if c.toInt >= 0 && c.toInt % 8 == 0 && armFitsPairOff off && r1 != r2 &&
        ds.take 1 == emitClean (armStpSpXRegIns x1 x2 off) then
      some (off / 8, [r1, r2], rest) else none
  | _ => match matchArmStSpX ds with
    | some (off, x, rest) => (csReg? x).map fun r => (off / 8, [r], rest)
    | none => none

private def matchArmRestoreStepRev (dsRev : List Directive) :
    Option (Nat × List Reg × List Directive) :=
  match dsRev with
  | .instr ⟨.W64, .LDP (.low (.reg x1) .W64) (.low (.reg x2) .W64)
      ⟨.low .SP .W64, .imm ⟨.int64 c, none⟩⟩⟩ :: prev => do
    let r1 ← csReg? x1; let r2 ← csReg? x2; let off := c.toInt.toNat
    if c.toInt >= 0 && c.toInt % 8 == 0 && r1 != r2 && armFitsPairOff off &&
        dsRev.take 1 == emitClean (armLdpSpXRegIns x1 x2 off) then
      some (off / 8, [r1, r2], prev) else none
  | .instr ⟨.W64, .LDR (.low (.reg x) .W64)
      (.addr ⟨.low .SP .W64, .imm ⟨.int64 c, none⟩⟩)⟩ :: prev => do
    let r ← csReg? x; let slot := c.toInt.toNat / 8
    if c.toInt >= 0 && c.toInt % 8 == 0 && (armSlotLd r slot).length == 1 &&
        dsRev.take 1 == armSlotLd r slot then some (slot, [r], prev) else none
  | .instr ⟨.W64, .LDR (.low (.reg x) .W64) (.addr ⟨.low .SP .W64, .reg _⟩)⟩ ::
    .instr ⟨.W64, .LDR (.low (.reg .X16) .W64) (.lit (.pool ⟨.int64 c⟩))⟩ :: prev => do
    let r ← csReg? x; let off := c.toUInt64.toNat; let slot := off / 8
    if off % 8 == 0 && dsRev.take 2 == (armSlotLd r slot).reverse then
      some (slot, [r], prev) else none
  | _ => none

private def regOrSpIsSp {w : RegWidth} : RegOrSp w → Bool | .low .SP _ => true | _ => false
private def spOrX30 {w : RegWidth} : RegOrSp w → Bool
  | .low .SP _ | .low (.reg .X30) _ => true | _ => false
private def isX30 {w : RegWidth} : RegOrZr w → Bool | .low (.reg .X30) _ => true | _ => false

private def opIsNonLeafOrFrame {w : RegWidth} : Operation w → Bool
  | .LDR dst (.addr a) | .LDRSW dst (.addr a) | .LDRB dst a | .LDRSB dst a
  | .LDRH dst a | .LDRSH dst a => isX30 dst || regOrSpIsSp a.base
  | .LDR dst (.lit _) | .LDRSW dst (.lit _) => isX30 dst
  | .STR src dst | .STRB src dst | .STRH src dst => isX30 src || regOrSpIsSp dst.base
  | .LDUR dst u | .LDURB dst u | .LDURSB dst u | .LDURH dst u | .LDURSH dst u
  | .LDURSW dst u | .STUR dst u | .STURB dst u | .STURH dst u => isX30 dst || regOrSpIsSp u.base
  | .LDP d1 d2 a | .STP d1 d2 a | .LDPSW d1 d2 a => isX30 d1 || isX30 d2 || regOrSpIsSp a.base
  | .ADD_e dst s1 _ | .SUB_e dst s1 _ => spOrX30 dst || regOrSpIsSp s1
  | .ADDS_e dst s1 _ | .SUBS_e dst s1 _ => isX30 dst || regOrSpIsSp s1
  | .AND_i dst _ _ | .ORR_i dst _ _ | .EOR_i dst _ _ => spOrX30 dst
  | .ADD_s dst _ _ | .ADDS_s dst _ _ | .SUB_s dst _ _ | .SUBS_s dst _ _
  | .ADC dst _ _ | .ADCS dst _ _ | .SBC dst _ _ | .SBCS dst _ _ | .SDIV dst _ _ | .UDIV dst _ _
  | .MADD dst _ _ _ | .MSUB dst _ _ _ | .SMULH dst _ _ | .UMULH dst _ _ | .SMADDL dst _ _ _
  | .UMADDL dst _ _ _ | .SMSUBL dst _ _ _ | .UMSUBL dst _ _ _ | .AND_s dst _ _ | .ANDS_i dst _ _
  | .ANDS_s dst _ _ | .ORR_s dst _ _ | .ORN_s dst _ _ | .EOR_s dst _ _ | .EON_s dst _ _
  | .BIC_s dst _ _ | .BICS_s dst _ _ | .BFM dst _ _ _ | .SBFM dst _ _ _ | .UBFM dst _ _ _
  | .CLZ dst _ | .CLS dst _ | .RBIT dst _ | .REV dst _ | .REV16 dst _ | .REV32 dst _
  | .EXTR dst _ _ _ | .MOVZ dst _ _ | .MOVK dst _ _ | .MOVN dst _ _ | .LSLV dst _ _
  | .LSRV dst _ _ | .ASRV dst _ _ | .RORV dst _ _ | .CSEL dst _ _ _ | .CSINC dst _ _ _
  | .CSINV dst _ _ _ | .CSNEG dst _ _ _ | .ADR dst _ | .ADRP dst _ => isX30 dst
  | .BL _ | .BLR _ | .BR _ => true
  | _ => false

private def isNonLeafOrFrameDir : Directive → Bool
  | .instr i => opIsNonLeafOrFrame i.operation | _ => false

private def inferFnFrame (fn : Sym) (nonLocal : HashSet Sym) (body : List Directive) :
    Except String (FnFrameInfo Reg) :=
  match matchArmSubSp body with
  | none =>
    if armFrame.leafZeroFrame && !body.any isNonLeafOrFrameDir then .ok ⟨true, 0, []⟩
    else .error s!"function '{fn}': unrecognized Arm64 prologue sub sp"
  | some (sz, afterSub) => match matchArmStSpX afterSub with
    | some (raOff, .X30, afterRa) =>
      let ns := raOff / 8
      if armFrameSize ns != sz then
        .error s!"function '{fn}': frame size {sz} mismatches x30 slot {ns}"
      else
        let cands := collectSavePrefix matchArmSaveStep (fun slot regs => slot + regs.length <= ns)
          afterRa.length none [] afterRa
        let tails := collectTailRestores matchArmRestoreStepRev (isTailDir fn nonLocal)
          (emitClean (armEpilogueIns ns)) [] afterRa []
        match inferSavedSlice cands tails ns (fun base len => base + len == ns) with
        | some (nslots, saved) => .ok ⟨false, nslots, saved⟩
        | none => .error s!"function '{fn}': could not infer Arm64 callee-saved slots"
    | _ => .error s!"function '{fn}': unrecognized Arm64 prologue x30 save"

private def armRestoreChunks : Nat → List Reg → List (List Reg × List Directive)
  | _, [] => []
  | i, [r] => [([r], armSlotLd r i)]
  | i, .reg r1 :: .reg r2 :: rs =>
    ([.reg r1, .reg r2], emitClean (armLdpSpXRegIns r1 r2 (8 * i))) ::
      armRestoreChunks (i + 2) rs
  | i, r :: rs => ([r], armSlotLd r i) :: armRestoreChunks (i + 1) rs

private def armCfg (fn : Sym) (nonLocal : HashSet Sym) : DebugAsmCfg Directive Reg where
  commentPfx := "//"; p2align? := some "\t.p2align 2"; emitLtorg := true
  cfaDesc sz := s!"sp+{sz}"; frameSize := armFrameSize; cfaBase sz := sz
  proSteps fn ns sz :=
    [(emitClean (armSubSpIns sz), [s!"\t.cfi_def_cfa_offset {sz}"],
      s!"function '{fn}': Arm64 prologue sub sp mismatch (totalSlots={ns})"),
     (emitClean (armStSpXRegIns .X30 (8 * ns)), [s!"\t.cfi_offset x30, -{sz - 8 * ns}"],
      s!"function '{fn}': Arm64 prologue x30 save mismatch (totalSlots={ns})")]
  nextSave idx rs := match rs with
    | [] => none | [r] => some ([r], armSlotSt idx r, [])
    | .reg r1 :: .reg r2 :: rest =>
      some ([.reg r1, .reg r2], emitClean (armStpSpXRegIns r1 r2 (8 * idx)), rest)
    | r :: rest => some ([r], armSlotSt idx r, rest)
  mkRestoreChunks := armRestoreChunks
  epiSections ns sz :=
    [(emitClean (armLdSpXRegIns .X30 (8 * ns)), ["\t.cfi_restore x30"]),
     (emitClean (armAddSpIns sz), ["\t.cfi_def_cfa_offset 0"])]
  isTailDir := isTailDir fn nonLocal; printDir d := Print.directive (scrubDir fn nonLocal d)
  cfiReg := cfiReg

/-- Emit ELF + DWARF CFI + `.L`-scrubbed AAPCS64 assembly from compiled `fs` and `code`.
When `hints?` is supplied, exact `(nslots, saved)` values are enforced against `code`; otherwise
they are inferred from prologue `str x30` + `saveCs` and cross-checked across all exit tails. -/
def emitArm64DebugAsmChecked (fs : List Fn) (code : List Directive)
    (hints? : Option (List Arm64Hints) := none) (exits : List Sym := [])
    (comments : Bool := false) : Except String String :=
  let pro0 := emitClean (armSubSpIns (armFrameSize 0)) ++ emitClean (armStSpXRegIns .X30 0)
  emitDebugAsmChecked dirLabel? Print.directive
    (fun fn body h => fnInfoOfHints armFrame.leafZeroFrame pro0 isNonLeafOrFrameDir
      s!"function '{fn}': Arm64 prologue mismatch (totalSlots=0)" h.nslots h.saved body)
    inferFnFrame (fun fn info nonLocal body out =>
      emitFnWithCfi (armCfg fn nonLocal) fn info comments body out)
    fs code hints? exits

/-- Infallible wrapper around `emitArm64DebugAsmChecked` for CLI assembly emission. -/
def emitArm64DebugAsm (fs : List Fn) (code : List Directive)
    (hints? : Option (List Arm64Hints) := none) (exits : List Sym := [])
    (comments : Bool := false) : String :=
  match emitArm64DebugAsmChecked fs code hints? exits comments with
  | .ok s => s | .error e => panic! s!"emitArm64DebugAsm: {e}"

end LeanQbe.T.Arm64
