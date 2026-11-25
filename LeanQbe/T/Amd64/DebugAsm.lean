module

public import LeanQbe.T.Main
public import LeanQbe.T.DebugAsmCommon
public import LeanQbe.T.Amd64.Frame
public import LeanQbe.T.Amd64.PrintATTAlign
public import Kraken.X64.PrintATT
import Std.Data.HashSet

/-!
# SysV x64 Debug Assembly & CFI Unwind Emitter

Transforms verified `List Kraken.X64.Directive` output from `LeanQbe.T.compile` into ELF-clean
AT&T assembly with **zero** machine-code changes in `.text`:
* ELF function metadata: `.globl fn`, `.type fn, %function`, `.size fn, .-fn`.
* Local label scrubbing: rewrites `{fn}.L{i}` definitions and internal branch/const-expr
  references to `.L{fn}.L{i}` so zero `NOTYPE LOCAL` block symbols leak into `.symtab`.
* Exact static-frame DWARF CFI: `.cfi_startproc`, `.cfi_def_cfa_offset`, `.cfi_offset` for
  `saveCs`, `.cfi_restore`, `.cfi_def_cfa_offset 8`, and `.cfi_remember_state` /
  `.cfi_restore_state` across multi-exit `ret` and tail-call `jmp` boundaries, closed by
  `.cfi_endproc`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Std
open LeanQbe.T LeanQbe.T.DebugAsmCommon Kraken Kraken.X64

/-- Frame hints specialization for SysV x64 (`x64Target`). -/
abbrev X64Hints : Type := Hints Reg64 RegMm CondCode

private def dirLabel? : Directive → Option Sym | .label l => some l | _ => none

private def scrubConst (fn : Sym) (nonLocal : HashSet Sym) : ConstExpr → ConstExpr
  | .label l => .label (scrubSym fn nonLocal l)
  | .add a b => .add (scrubConst fn nonLocal a) (scrubConst fn nonLocal b)
  | .sub a b => .sub (scrubConst fn nonLocal a) (scrubConst fn nonLocal b)
  | e => e

private def scrubAddr (fn : Sym) (nonLocal : HashSet Sym) (a : AddrExpr) : AddrExpr :=
  { a with disp := scrubConst fn nonLocal a.disp }

private def scrubRM {w : Width} (fn : Sym) (nonLocal : HashSet Sym) : RegOrMem w → RegOrMem w
  | .reg r => .reg r | .mem a => .mem (scrubAddr fn nonLocal a)

private def scrubOpd {w : Width} (fn : Sym) (nonLocal : HashSet Sym) : Operand w → Operand w
  | .regOrMem rm => .regOrMem (scrubRM fn nonLocal rm) | .imm c => .imm (scrubConst fn nonLocal c)

private def scrubRelRM (fn : Sym) (nonLocal : HashSet Sym) : RelRegOrMem → RelRegOrMem
  | .rel c => .rel (scrubConst fn nonLocal c) | .reg r => .reg r
  | .mem a => .mem (scrubAddr fn nonLocal a)

private def scrubSC (fn : Sym) (nonLocal : HashSet Sym) : ShiftCountExpr → ShiftCountExpr
  | .cl => .cl | .imm8 c => .imm8 (scrubConst fn nonLocal c)

private def scrubAvxRM {w : AvxWidth} (fn : Sym) (nonLocal : HashSet Sym) :
    AvxRegOrMem w → AvxRegOrMem w
  | .avx r => .avx r | .mem a => .mem (scrubAddr fn nonLocal a)

private def scrubOp {w : Width} (fn : Sym) (nonLocal : HashSet Sym) :
    Operation w → Operation w := fun op =>
  let sr := scrubRM fn nonLocal; let so := scrubOpd fn nonLocal
  let sc := scrubSC fn nonLocal; let kc := scrubConst fn nonLocal
  match op with
  | .mov d p => .mov (sr d) (so p)
  | .movsx d rm => .movsx (sr d) (scrubRM fn nonLocal rm)
  | .movzx d rm => .movzx (sr d) (scrubRM fn nonLocal rm)
  | .push p => .push (so p) | .pop d => .pop (sr d) | .setcc cc d => .setcc cc (sr d)
  | .cmovcc cc r rm => .cmovcc cc r (sr rm) | .lea r a => .lea r (scrubAddr fn nonLocal a)
  | .add d p => .add (sr d) (so p) | .adc d p => .adc (sr d) (so p)
  | .adcx r rm => .adcx r (sr rm) | .adox r rm => .adox r (sr rm)
  | .inc rm => .inc (sr rm) | .dec rm => .dec (sr rm) | .neg rm => .neg (sr rm)
  | .sub d p => .sub (sr d) (so p) | .sbb d p => .sbb (sr d) (so p)
  | .cmp rm p => .cmp (sr rm) (so p) | .mul rm => .mul (sr rm)
  | .mulx r1 r2 rm => .mulx r1 r2 (sr rm) | .imul1 rm => .imul1 (sr rm)
  | .imul d rm p => .imul (d.map sr) (sr rm) (so p) | .div rm => .div (sr rm)
  | .idiv rm => .idiv (sr rm) | .test rm p => .test (sr rm) (so p)
  | .and d p => .and (sr d) (so p) | .not d => .not (sr d) | .or d p => .or (sr d) (so p)
  | .xor d p => .xor (sr d) (so p) | .shl d s => .shl (sr d) (sc s)
  | .shr d s => .shr (sr d) (sc s) | .sar d s => .sar (sr d) (sc s)
  | .shld d r s => .shld (sr d) r (sc s) | .shrd d r s => .shrd (sr d) r (sc s)
  | .rol d s => .rol (sr d) (sc s) | .ror d s => .ror (sr d) (sc s)
  | .rcl d s => .rcl (sr d) (sc s) | .rcr d s => .rcr (sr d) (sc s)
  | .lzcnt r rm => .lzcnt r (sr rm) | .tzcnt r rm => .tzcnt r (sr rm)
  | .popcnt r rm => .popcnt r (sr rm) | .shlx r rm r2 => .shlx r (sr rm) r2
  | .shrx r rm r2 => .shrx r (sr rm) r2 | .sarx r rm r2 => .sarx r (sr rm) r2
  | .rorx r rm ce => .rorx r (sr rm) (kc ce) | .jcc cc l => .jcc cc (scrubSym fn nonLocal l)
  | .jmp rrm => .jmp (scrubRelRM fn nonLocal rrm) | .call rrm => .call (scrubRelRM fn nonLocal rrm)
  | op => op

private def scrubAvx {w : AvxWidth} (fn : Sym) (nonLocal : HashSet Sym) :
    AvxOperation w → AvxOperation w := fun op =>
  let sa := scrubAvxRM fn nonLocal; let kc := scrubConst fn nonLocal
  match op with
  | .movups d s => .movups (sa d) (sa s) | .vmovups d s => .vmovups (sa d) (sa s)
  | .movaps d s => .movaps (sa d) (sa s) | .subps d s => .subps (sa d) (sa s)
  | .addps d s => .addps (sa d) (sa s) | .movdqu d s => .movdqu (sa d) (sa s)
  | .movdqa d s => .movdqa (sa d) (sa s) | .paddd d s => .paddd (sa d) (sa s)
  | .pshufb d s => .pshufb (sa d) (sa s) | .pshufd d s c => .pshufd (sa d) (sa s) (kc c)
  | .palignr d s c => .palignr (sa d) (sa s) (kc c)
  | .pblendw d s c => .pblendw (sa d) (sa s) (kc c)
  | .vmovdqu d s => .vmovdqu (sa d) (sa s) | .vmovIn n d s => .vmovIn n d (scrubRM fn nonLocal s)
  | .vmovOut n d s => .vmovOut n (scrubRM fn nonLocal d) s
  | .sha256rnds2 d s => .sha256rnds2 (sa d) (sa s)
  | .sha256msg1 d s => .sha256msg1 (sa d) (sa s)
  | .sha256msg2 d s => .sha256msg2 (sa d) (sa s)
  | .vmovdqu32 d s => .vmovdqu32 (sa d) (sa s) | .vmovdqa32 d s => .vmovdqa32 (sa d) (sa s)
  | .vpaddd d s1 s2 => .vpaddd (sa d) (sa s1) (sa s2)
  | .vprord d s c => .vprord (sa d) (sa s) (kc c) | .vpsrld d s c => .vpsrld (sa d) (sa s) (kc c)
  | .vpternlogd d s1 s2 c => .vpternlogd (sa d) (sa s1) (sa s2) (kc c)
  | op => op

private def scrubDir (fn : Sym) (nonLocal : HashSet Sym) : Directive → Directive
  | .instr (.regular w ow op) => .instr (.regular w ow (scrubOp fn nonLocal op))
  | .instr (.avx w ow op) => .instr (.avx w ow (scrubAvx fn nonLocal op))
  | .label l => .label (scrubSym fn nonLocal l)
  | .byteArray bs => .byteArray bs | .word n e => .word n (scrubConst fn nonLocal e)

private def cfiReg : Reg64 → String
  | .rax => "%rax" | .rbx => "%rbx" | .rcx => "%rcx" | .rdx => "%rdx"
  | .rsi => "%rsi" | .rdi => "%rdi" | .rsp => "%rsp" | .rbp => "%rbp"
  | .r8  => "%r8"  | .r9  => "%r9"  | .r10 => "%r10" | .r11 => "%r11"
  | .r12 => "%r12" | .r13 => "%r13" | .r14 => "%r14" | .r15 => "%r15"

private def isTailDir (fn : Sym) (nonLocal : HashSet Sym) : Directive → Option String
  | .instr (.regular .W64 .W64 .ret) => some "ret"
  | .instr (.regular .W64 .W64
      (.jmp (.rel (.sub (.label sym) .after_current_instruction)))) =>
    if isLocalFnLabel fn nonLocal sym then none else some s!"jmp {sym}"
  | _ => none

private def matchPrologueSz (body : List Directive) : Option (Nat × List Directive) :=
  match body with
  | .instr (.regular .W64 .W64 (.sub (.reg (.low .rsp .W64)) (.imm (.int64 c)))) :: rest =>
    let sz := c.toInt.toNat
    if c.toInt >= 8 && body.take 1 == emitClean (x64PrologueIns (sz / 8)) then some (sz, rest)
    else none
  | .instr (.regular .W64 .W64 (.mov (.reg (.low .r10 .W64)) (.imm (.int64 c)))) ::
    .instr (.regular .W64 .W64 (.sub (.reg (.low .rsp .W64)) (.reg (.low .r10 .W64)))) :: rest =>
    let sz := c.toUInt64.toNat
    if sz >= 8 && sz % 16 == 8 && body.take 2 == emitClean (x64PrologueIns (sz / 8)) then
      some (sz, rest) else none
  | _ => none

private def matchSlotSt (ds : List Directive) : Option (Nat × List Reg64 × List Directive) :=
  match ds with
  | .instr (.regular .W64 .W64
      (.mov (.mem ⟨some (.reg .rsp), none, .int64 c⟩) (.reg (.low r .W64)))) :: rest =>
    let slot := c.toInt.toNat / 8
    if c.toInt >= 0 && c.toInt % 8 == 0 && x64Frame.calleeSaved.contains r &&
        ds.take 1 == x64SlotSt slot r then some (slot, [r], rest) else none
  | .instr (.regular .W64 .W64 (.mov (.reg (.low .r10 .W64)) (.imm (.int64 c)))) ::
    .instr (.regular .W64 .W64 (.mov (.mem _) (.reg (.low r .W64)))) :: rest =>
    let off := c.toUInt64.toNat; let slot := off / 8
    if off % 8 == 0 && x64Frame.calleeSaved.contains r && ds.take 2 == x64SlotSt slot r then
      some (slot, [r], rest) else none
  | _ => none

private def matchSlotLdRev (dsRev : List Directive) : Option (Nat × List Reg64 × List Directive) :=
  match dsRev with
  | .instr (.regular .W64 .W64
      (.mov (.reg (.low r .W64)) (.mem ⟨some (.reg .rsp), none, .int64 c⟩))) :: prev =>
    let slot := c.toInt.toNat / 8; let exp := x64SlotLd r slot
    if c.toInt >= 0 && c.toInt % 8 == 0 && x64Frame.calleeSaved.contains r &&
        exp.length == 1 && dsRev.take 1 == exp then some (slot, [r], prev) else none
  | .instr (.regular .W64 .W64 (.mov (.reg (.low r .W64)) (.mem _))) ::
    .instr (.regular .W64 .W64 (.mov (.reg (.low .r10 .W64)) (.imm (.int64 c)))) :: prev =>
    let off := c.toUInt64.toNat; let slot := off / 8; let exp := x64SlotLd r slot
    if off % 8 == 0 && x64Frame.calleeSaved.contains r &&
        dsRev.take 2 == exp.reverse then some (slot, [r], prev) else none
  | _ => none

private def addrUsesRsp (a : AddrExpr) : Bool :=
  a.base == some (.reg .rsp) || match a.idx with | some i => i.reg == .rsp | none => false

private def rmUsesRsp {w : Width} : RegOrMem w → Bool
  | .reg (.low .rsp _) => true | .mem a => addrUsesRsp a | _ => false

private def avxRmUsesRsp {w : AvxWidth} : AvxRegOrMem w → Bool
  | .mem a => addrUsesRsp a | _ => false

private def isNonLeafOrFrameDir : Directive → Bool
  | .instr (.regular _ _ (.call _)) | .instr (.regular _ _ (.push _))
  | .instr (.regular _ _ (.pop _)) | .instr (.regular _ _ (.lea (.low .rsp _) _)) => true
  | .instr (.regular _ _ (.sub d _)) | .instr (.regular _ _ (.add d _)) => rmUsesRsp d
  | .instr (.regular _ _ (.mov d op)) =>
    rmUsesRsp d || match op with | .regOrMem rm => rmUsesRsp rm | .imm _ => false
  | .instr (.avx _ _ (.vmovdqu32 d s)) | .instr (.avx _ _ (.vmovdqu d s))
  | .instr (.avx _ _ (.vmovups d s)) => avxRmUsesRsp d || avxRmUsesRsp s
  | .instr (.avx _ _ (.vmovIn _ _ s)) => rmUsesRsp s
  | .instr (.avx _ _ (.vmovOut _ d _)) => rmUsesRsp d
  | _ => false

private def inferFnFrame (fn : Sym) (nonLocal : HashSet Sym) (body : List Directive) :
    Except String (FnFrameInfo Reg64) :=
  match matchPrologueSz body with
  | none =>
    if x64Frame.leafZeroFrame && !body.any isNonLeafOrFrameDir then .ok ⟨true, 0, []⟩
    else .error s!"function '{fn}': unrecognized x64 prologue"
  | some (sz, afterPro) =>
    let epi := emitClean (x64EpilogueIns (sz / 8))
    let cands := collectSavePrefix matchSlotSt
      (fun slot regs => x64FrameSize (slot + regs.length) <= sz) afterPro.length none [] afterPro
    let tails := collectTailRestores matchSlotLdRev (isTailDir fn nonLocal) epi [] afterPro []
    let lo := sz / 8 - 1; let hi := sz / 8
    match inferSavedSlice cands tails (sz / 8) (fun base len =>
        let tot := base + len; (tot == lo || tot == hi) && x64FrameSize tot == sz) with
    | some (nslots, saved) => .ok ⟨false, nslots, saved⟩
    | none => .error s!"function '{fn}': could not infer x64 callee-saved slots"

private def x64Cfg (fn : Sym) (nonLocal : HashSet Sym) (loopHdrs : HashSet Sym)
    (loopAlign : Bool) : DebugAsmCfg Directive Reg64 where
  commentPfx := "#"; p2align? := none; emitLtorg := false
  cfaDesc sz := s!"rsp+{8 + sz}"; frameSize := x64FrameSize; cfaBase sz := 8 + sz
  proSteps fn ns sz := [(emitClean (x64PrologueIns ns), [s!"\t.cfi_def_cfa_offset {8 + sz}"],
    s!"function '{fn}': prologue mismatch for totalSlots={ns}")]
  nextSave idx rs := match rs with | [] => none | r :: rest => some ([r], x64SlotSt idx r, rest)
  mkRestoreChunks base saved :=
    (List.range saved.length).zip saved |>.map fun (k, r) => ([r], x64SlotLd r (base + k))
  epiSections ns _ := [(emitClean (x64EpilogueIns ns), ["\t.cfi_def_cfa_offset 8"])]
  isTailDir := isTailDir fn nonLocal; printDir d := ATT.directive (scrubDir fn nonLocal d)
  cfiReg := cfiReg
  preBodyDir d := match d with
    | .label l => if loopAlign && loopHdrs.contains l then some loopAlignDirective else none
    | _ => none

/-- Emit ELF + DWARF CFI + `.L`-scrubbed x64 assembly from compiled `fs` and `code`.
When `hints?` is supplied, exact `(nslots, saved)` values are enforced against `code`; otherwise
they are inferred and cross-checked across prologue and all exit tails. -/
def emitX64DebugAsmChecked (fs : List Fn) (code : List Directive)
    (hints? : Option (List X64Hints) := none) (exits : List Sym := [])
    (comments : Bool := false) (loopAlign : Bool := true) : Except String String :=
  emitDebugAsmChecked dirLabel? ATT.directive
    (fun fn body h => fnInfoOfHints x64Frame.leafZeroFrame (emitClean (x64PrologueIns 0))
      isNonLeafOrFrameDir s!"function '{fn}': prologue mismatch for totalSlots=0"
      h.nslots h.saved body)
    inferFnFrame (fun fn info nonLocal body out =>
      let loopHdrs : HashSet Sym :=
        if loopAlign then (detectLoopHeaders body).foldl (fun s l => s.insert l) {} else {}
      emitFnWithCfi (x64Cfg fn nonLocal loopHdrs loopAlign) fn info comments body out)
    fs code hints? exits

/-- Infallible wrapper around `emitX64DebugAsmChecked` for CLI assembly emission. -/
def emitX64DebugAsm (fs : List Fn) (code : List Directive)
    (hints? : Option (List X64Hints) := none) (exits : List Sym := [])
    (comments : Bool := false) (loopAlign : Bool := true) : String :=
  match emitX64DebugAsmChecked fs code hints? exits comments loopAlign with
  | .ok s => s | .error e => panic! s!"emitX64DebugAsm: {e}"

end LeanQbe.T.Amd64
