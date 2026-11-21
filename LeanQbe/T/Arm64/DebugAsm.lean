module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Frame
public import Kraken.AArch64.Print
import Std.Data.HashSet

/-!
# AAPCS64 Arm64 Debug Assembly & CFI Unwind Emitter (`P0 + P1`)

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
open LeanQbe.T Kraken Kraken.AArch64

/-- Frame hints specialization for AAPCS64 Arm64 (`armTarget`). -/
abbrev Arm64Hints : Type := Hints Reg Empty ArmCond

private def isNatDigits (s : String) : Bool :=
  !s.isEmpty && s.toList.all Char.isDigit

private def isLocalFnLabel (fn : Sym) (nonLocal : HashSet Sym) (s : Sym) : Bool :=
  let pfx := fn ++ ".L"
  !nonLocal.contains s && s.startsWith pfx &&
    isNatDigits (String.ofList (s.toList.drop pfx.length))

private def scrubSym (fn : Sym) (nonLocal : HashSet Sym) (s : Sym) : Sym :=
  if isLocalFnLabel fn nonLocal s then ".L" ++ s else s

private def scrubConst (fn : Sym) (nonLocal : HashSet Sym) : ConstExpr → ConstExpr
  | .label l => .label (scrubSym fn nonLocal l)
  | .add a b => .add (scrubConst fn nonLocal a) (scrubConst fn nonLocal b)
  | .sub a b => .sub (scrubConst fn nonLocal a) (scrubConst fn nonLocal b)
  | .pg_hi21 a => .pg_hi21 (scrubConst fn nonLocal a)
  | .lo12 a => .lo12 (scrubConst fn nonLocal a)
  | e => e

private def scrubAddrOff (fn : Sym) (nonLocal : HashSet Sym) : AddrOff → AddrOff
  | .imm ie => .imm { ie with imm := scrubConst fn nonLocal ie.imm }
  | .reg r => .reg r

private def scrubAddr (fn : Sym) (nonLocal : HashSet Sym) (a : AddrExpr) : AddrExpr :=
  { a with off := scrubAddrOff fn nonLocal a.off }

private def scrubUAddr (fn : Sym) (nonLocal : HashSet Sym)
    (a : UnscaledAddrExpr) : UnscaledAddrExpr :=
  { a with imm := scrubConst fn nonLocal a.imm }

private def scrubAddrOrLit (fn : Sym) (nonLocal : HashSet Sym) : AddrOrLit → AddrOrLit
  | .addr a => .addr (scrubAddr fn nonLocal a)
  | .lit (.addr la) => .lit (.addr { label := scrubSym fn nonLocal la.label })
  | .lit (.pool lp) => .lit (.pool { expr := scrubConst fn nonLocal lp.expr })

private def scrubOp {w : RegWidth} (fn : Sym) (nonLocal : HashSet Sym) :
    Operation w → Operation w
  | .LDR r al => .LDR r (scrubAddrOrLit fn nonLocal al)
  | .STR r a => .STR r (scrubAddr fn nonLocal a)
  | .LDUR r u => .LDUR r (scrubUAddr fn nonLocal u)
  | .STUR r u => .STUR r (scrubUAddr fn nonLocal u)
  | .LDP r1 r2 a => .LDP r1 r2 (scrubAddr fn nonLocal a)
  | .STP r1 r2 a => .STP r1 r2 (scrubAddr fn nonLocal a)
  | .LDRB r a => .LDRB r (scrubAddr fn nonLocal a)
  | .LDURB r u => .LDURB r (scrubUAddr fn nonLocal u)
  | .STRB r a => .STRB r (scrubAddr fn nonLocal a)
  | .STURB r u => .STURB r (scrubUAddr fn nonLocal u)
  | .LDRSB r a => .LDRSB r (scrubAddr fn nonLocal a)
  | .LDURSB r u => .LDURSB r (scrubUAddr fn nonLocal u)
  | .LDRH r a => .LDRH r (scrubAddr fn nonLocal a)
  | .LDURH r u => .LDURH r (scrubUAddr fn nonLocal u)
  | .STRH r a => .STRH r (scrubAddr fn nonLocal a)
  | .STURH r u => .STURH r (scrubUAddr fn nonLocal u)
  | .LDRSH r a => .LDRSH r (scrubAddr fn nonLocal a)
  | .LDURSH r u => .LDURSH r (scrubUAddr fn nonLocal u)
  | .LDRSW r al => .LDRSW r (scrubAddrOrLit fn nonLocal al)
  | .LDURSW r u => .LDURSW r (scrubUAddr fn nonLocal u)
  | .LDPSW r1 r2 a => .LDPSW r1 r2 (scrubAddr fn nonLocal a)
  | .AND_i d s c => .AND_i d s (scrubConst fn nonLocal c)
  | .ANDS_i d s c => .ANDS_i d s (scrubConst fn nonLocal c)
  | .ORR_i d s c => .ORR_i d s (scrubConst fn nonLocal c)
  | .EOR_i d s c => .EOR_i d s (scrubConst fn nonLocal c)
  | .MOVZ d c ms => .MOVZ d (scrubConst fn nonLocal c) ms
  | .MOVK d c ms => .MOVK d (scrubConst fn nonLocal c) ms
  | .MOVN d c ms => .MOVN d (scrubConst fn nonLocal c) ms
  | .ADR d c => .ADR d (scrubConst fn nonLocal c)
  | .ADRP d c => .ADRP d (scrubConst fn nonLocal c)
  | .B c => .B (scrubConst fn nonLocal c)
  | .B_cond cc c => .B_cond cc (scrubConst fn nonLocal c)
  | .BL c => .BL (scrubConst fn nonLocal c)
  | .CBZ r c => .CBZ r (scrubConst fn nonLocal c)
  | .CBNZ r c => .CBNZ r (scrubConst fn nonLocal c)
  | .TBZ r b c => .TBZ r b (scrubConst fn nonLocal c)
  | .TBNZ r b c => .TBNZ r b (scrubConst fn nonLocal c)
  | op => op

private def scrubDir (fn : Sym) (nonLocal : HashSet Sym) : Directive → Directive
  | .instr i => .instr ⟨i.operation_size, scrubOp fn nonLocal i.operation⟩
  | .label l => .label (scrubSym fn nonLocal l)
  | .byteArray bs => .byteArray bs
  | .word n e => .word n (scrubConst fn nonLocal e)

private def cfiXReg (r : XReg) : String :=
  Print.xreg .W64 r

private def cfiReg : Reg → String
  | .reg x => cfiXReg x
  | .SP => "sp"

private def isTailDir (fn : Sym) (nonLocal : HashSet Sym) : Directive → Option String
  | .instr ⟨.W64, .RET (.low (.reg .X30) .W64)⟩ => some "ret"
  | .instr ⟨.W64, .B (.label sym)⟩ =>
    if isLocalFnLabel fn nonLocal sym then none else some s!"b {sym}"
  | _ => none

private def dropPrefix? {α : Type} [BEq α] : List α → List α → Option (List α)
  | [], ys => some ys
  | x :: xs, y :: ys => if x == y then dropPrefix? xs ys else none
  | _ :: _, [] => none

private def takeUntilLabelAcc (target : Sym) (acc : List Directive) :
    List Directive → List Directive × List Directive
  | [] => (acc.reverse, [])
  | d :: ds =>
    match d with
    | .label l =>
      if l == target then (acc.reverse, d :: ds)
      else takeUntilLabelAcc target (d :: acc) ds
    | _ => takeUntilLabelAcc target (d :: acc) ds

private def splitFnSlices : List Sym → List Directive → Except String (List (Sym × List Directive))
  | [], [] => .ok []
  | [], d :: _ =>
    .error s!"unexpected trailing directives after functions: {Print.directive d}"
  | nm :: rest, dirs =>
    match dirs with
    | .label l :: body =>
      if l != nm then
        .error s!"expected function label '{nm}', found '{l}'"
      else
        match rest with
        | [] => .ok [(nm, body)]
        | g :: _ =>
          let (fnBody, rem) := takeUntilLabelAcc g [] body
          match splitFnSlices rest rem with
          | .ok more => .ok ((nm, fnBody) :: more)
          | .error e => .error e
    | d :: _ => .error s!"expected function label '{nm}', found '{Print.directive d}'"
    | [] => .error s!"unexpected EOF before function '{nm}'"

private def matchArmSubSp (body : List Directive) : Option (Nat × List Directive) :=
  match body with
  | .instr ⟨.W64, .SUB_e (.low .SP .W64) (.low .SP .W64) (.imm ⟨.int64 c, .S0⟩)⟩ :: rest =>
    if c.toInt >= 16 then
      let sz := c.toInt.toNat
      if body.take 1 == emitClean (armSubSpIns sz) then some (sz, rest) else none
    else none
  | .instr ⟨.W64, .LDR (.low (.reg .X16) .W64) (.lit (.pool ⟨.int64 c⟩))⟩ ::
    .instr ⟨.W64, .SUB_e (.low .SP .W64) (.low .SP .W64) (.ext _)⟩ :: rest =>
    let sz := c.toUInt64.toNat
    if sz >= 16 && sz % 16 == 0 && body.take 2 == emitClean (armSubSpIns sz) then
      some (sz, rest)
    else none
  | _ => none

private def matchArmStSpX (ds : List Directive) :
    Option (Nat × XReg × List Directive × List Directive) :=
  match ds with
  | .instr ⟨.W64,
      .STR (.low (.reg r) .W64) ⟨.low .SP .W64, .imm ⟨.int64 c, none⟩⟩⟩ :: rest =>
    if c.toInt >= 0 && c.toInt % 8 == 0 then
      let off := c.toInt.toNat
      if ds.take 1 == emitClean (armStSpXRegIns r off) then some (off, r, ds.take 1, rest)
      else none
    else none
  | .instr ⟨.W64, .LDR (.low (.reg .X16) .W64) (.lit (.pool ⟨.int64 c⟩))⟩ ::
    .instr ⟨.W64, .STR (.low (.reg r) .W64) ⟨.low .SP .W64, .reg _⟩⟩ :: rest =>
    let off := c.toUInt64.toNat
    if off % 8 == 0 && ds.take 2 == emitClean (armStSpXRegIns r off) then
      some (off, r, ds.take 2, rest)
    else none
  | _ => none

private def collectSavePrefix (ns : Nat) :
    Nat → Option Nat → List Reg → List Directive → List (Nat × Reg)
  | 0, _, _, _ => []
  | fuel + 1, expSlot, seen, ds =>
    match matchArmStSpX ds with
    | some (off, x, _, rest) =>
      let r : Reg := .reg x
      let slot := off / 8
      let contiguous := match expSlot with | none => true | some exp => slot == exp
      if contiguous && slot < ns && armFrame.calleeSaved.contains r && !seen.contains r then
        (slot, r) :: collectSavePrefix ns fuel (some (slot + 1)) (r :: seen) rest
      else []
    | none => []

private def matchArmLdSpXRev (dsRev : List Directive) :
    Option (Nat × Reg × List Directive) :=
  match dsRev with
  | .instr ⟨.W64, .LDR (.low (.reg x) .W64)
      (.addr ⟨.low .SP .W64, .imm ⟨.int64 c, none⟩⟩)⟩ :: prev =>
    let r : Reg := .reg x
    if c.toInt >= 0 && c.toInt % 8 == 0 && armFrame.calleeSaved.contains r then
      let slot := c.toInt.toNat / 8
      let expected := armSlotLd r slot
      if expected.length == 1 && dsRev.take 1 == expected.reverse then some (slot, r, prev)
      else none
    else none
  | .instr ⟨.W64, .LDR (.low (.reg x) .W64) (.addr ⟨.low .SP .W64, .reg _⟩)⟩ ::
    .instr ⟨.W64, .LDR (.low (.reg .X16) .W64) (.lit (.pool ⟨.int64 c⟩))⟩ :: prev =>
    let r : Reg := .reg x
    let off := c.toUInt64.toNat
    if off % 8 == 0 && armFrame.calleeSaved.contains r then
      let slot := off / 8
      let expected := armSlotLd r slot
      if expected.length == 2 && dsRev.take 2 == expected.reverse then some (slot, r, prev)
      else none
    else none
  | _ => none

private def collectRestoreRev :
    Nat → Option Nat → List Reg → List Directive → List (Nat × Reg)
  | 0, _, _, _ => []
  | fuel + 1, expSlot?, seen, dsRev =>
    match matchArmLdSpXRev dsRev with
    | some (slot, r, prev) =>
      let contiguous := match expSlot? with | none => true | some exp => slot == exp
      if contiguous && !seen.contains r && slot > 0 then
        (slot, r) :: collectRestoreRev fuel (some (slot - 1)) (r :: seen) prev
      else if contiguous && !seen.contains r && slot == 0 then
        [(slot, r)]
      else []
    | none => []

private def collectTailRestores (fn : Sym) (nonLocal : HashSet Sym) (epi : List Directive) :
    List Directive → List Directive → List (List (Nat × Reg)) → List (List (Nat × Reg))
  | _revSeen, [], acc => acc
  | revSeen, ds@(d :: rest), acc =>
    match dropPrefix? epi ds with
    | some (tailD :: _) =>
      match isTailDir fn nonLocal tailD with
      | some _ =>
        let loadsFwd := (collectRestoreRev revSeen.length none [] revSeen).reverse
        collectTailRestores fn nonLocal epi (d :: revSeen) rest (loadsFwd :: acc)
      | none => collectTailRestores fn nonLocal epi (d :: revSeen) rest acc
    | _ => collectTailRestores fn nonLocal epi (d :: revSeen) rest acc

private def isSuffixOf {α : Type} [BEq α] (suf xs : List α) : Bool :=
  suf.length <= xs.length && xs.drop (xs.length - suf.length) == suf

private def inferFnSaved (fn : Sym) (nonLocal : HashSet Sym) (body : List Directive) :
    Except String (Nat × List Reg) :=
  match matchArmSubSp body with
  | none => .error s!"function '{fn}': unrecognized Arm64 prologue sub sp"
  | some (sz, afterSub) =>
    match matchArmStSpX afterSub with
    | some (raOff, .X30, _, afterRa) =>
      let ns := raOff / 8
      if armFrameSize ns != sz then
        .error s!"function '{fn}': frame size {sz} mismatches x30 slot {ns}"
      else
        let epi := emitClean (armEpilogueIns ns)
        let cands := collectSavePrefix ns afterRa.length none [] afterRa
        let tails := collectTailRestores fn nonLocal epi [] afterRa []
        let rec tryLen : Nat → Option (Nat × List Reg)
          | 0 => some (ns, [])
          | m + 1 =>
            let slice := cands.take (m + 1)
            match slice with
            | [] => some (ns, [])
            | (base, _) :: _ =>
              if base + slice.length == ns && tails.all (isSuffixOf slice) then
                some (base, slice.map Prod.snd)
              else
                tryLen m
        match tryLen cands.length with
        | some res => .ok res
        | none => .error s!"function '{fn}': could not infer Arm64 callee-saved slots"
    | _ => .error s!"function '{fn}': unrecognized Arm64 prologue x30 save"

private def pushDirLines (fn : Sym) (nonLocal : HashSet Sym) (ds : List Directive)
    (out : Array String) : Array String :=
  ds.foldl (fun acc d => acc.push (Print.directive (scrubDir fn nonLocal d))) out

private def emitBodyTails (fn : Sym) (nonLocal : HashSet Sym) (comments : Bool)
    (restoreChunks : List (Reg × List Directive)) (restoreFlat : List Directive)
    (ldX30 addSp : List Directive) : Nat → List Directive → Array String → Array String
  | 0, rem, out => pushDirLines fn nonLocal rem out
  | _ + 1, [], out => out
  | fuel + 1, rem@(d :: ds), out =>
    match dropPrefix? restoreFlat rem with
    | some afterRest =>
      match dropPrefix? ldX30 afterRest with
      | some afterLdX30 =>
        match dropPrefix? addSp afterLdX30 with
        | some (tailD :: afterTail) =>
          match isTailDir fn nonLocal tailD with
          | some kind =>
            let needState := !afterTail.isEmpty
            let out := if comments then out.push s!"\t// epilogue ({kind})" else out
            let out := if needState then out.push "\t.cfi_remember_state" else out
            let out := restoreChunks.foldl (fun acc (r, lds) =>
              (pushDirLines fn nonLocal lds acc).push s!"\t.cfi_restore {cfiReg r}") out
            let out := (pushDirLines fn nonLocal ldX30 out).push "\t.cfi_restore x30"
            let out := (pushDirLines fn nonLocal addSp out).push "\t.cfi_def_cfa_offset 0"
            let out := out.push (Print.directive (scrubDir fn nonLocal tailD))
            let out := if needState then out.push "\t.cfi_restore_state" else out
            emitBodyTails fn nonLocal comments restoreChunks restoreFlat ldX30 addSp
              fuel afterTail out
          | none =>
            emitBodyTails fn nonLocal comments restoreChunks restoreFlat ldX30 addSp fuel ds
              (out.push (Print.directive (scrubDir fn nonLocal d)))
        | _ =>
          emitBodyTails fn nonLocal comments restoreChunks restoreFlat ldX30 addSp fuel ds
            (out.push (Print.directive (scrubDir fn nonLocal d)))
      | none =>
        emitBodyTails fn nonLocal comments restoreChunks restoreFlat ldX30 addSp fuel ds
          (out.push (Print.directive (scrubDir fn nonLocal d)))
    | none =>
      emitBodyTails fn nonLocal comments restoreChunks restoreFlat ldX30 addSp fuel ds
        (out.push (Print.directive (scrubDir fn nonLocal d)))

private def emitArm64Fn (fn : Sym) (nslots : Nat) (saved : List Reg) (nonLocal : HashSet Sym)
    (comments : Bool) (body : List Directive) (out : Array String) :
    Except String (Array String) :=
  let ns := nslots + saved.length
  let sz := armFrameSize ns
  let subSp := emitClean (armSubSpIns sz)
  let stX30 := emitClean (armStSpXRegIns .X30 (8 * ns))
  match dropPrefix? subSp body with
  | none => .error s!"function '{fn}': Arm64 prologue sub sp mismatch (totalSlots={ns})"
  | some afterSub =>
    match dropPrefix? stX30 afterSub with
    | none => .error s!"function '{fn}': Arm64 prologue x30 save mismatch (totalSlots={ns})"
    | some afterRa =>
      let rec consumeSaves (idx : Nat) (ds : List Directive) (acc : Array String) :
          List Reg → Except String (Array String × List Directive)
        | [] => .ok (acc, ds)
        | r :: rs =>
          let st := armSlotSt idx r
          match dropPrefix? st ds with
          | none =>
            .error s!"function '{fn}': saveCs mismatch for {cfiReg r} at slot {idx}"
          | some rest =>
            let cfaOff := sz - 8 * idx
            let acc := (pushDirLines fn nonLocal st acc).push
              s!"\t.cfi_offset {cfiReg r}, -{cfaOff}"
            consumeSaves (idx + 1) rest acc rs
      let savedNames := String.intercalate "," (saved.map cfiReg)
      let out :=
        if comments then
          out.push s!"// fn {fn}: frame={sz}B cfa=sp+{sz} saved=[{savedNames}]"
        else out
      let out := out
        |>.push "\t.p2align 2"
        |>.push s!"\t.globl {fn}"
        |>.push s!"\t.type {fn}, %function"
        |>.push s!"{fn}:"
        |>.push "\t.cfi_startproc"
      let out := (pushDirLines fn nonLocal subSp out).push s!"\t.cfi_def_cfa_offset {sz}"
      let raCfaOff := sz - 8 * ns
      let out := (pushDirLines fn nonLocal stX30 out).push s!"\t.cfi_offset x30, -{raCfaOff}"
      match consumeSaves nslots afterRa out saved with
      | .error e => .error e
      | .ok (out, restBody) =>
        let restoreChunks := (List.range saved.length).zip saved |>.map fun (k, r) =>
          (r, armSlotLd r (nslots + k))
        let restoreFlat := restoreChunks.flatMap Prod.snd
        let ldX30 := emitClean (armLdSpXRegIns .X30 (8 * ns))
        let addSp := emitClean (armAddSpIns sz)
        let out := emitBodyTails fn nonLocal comments restoreChunks restoreFlat
          ldX30 addSp restBody.length restBody out
        let out := out.push "\t.cfi_endproc" |>.push s!"\t.size {fn}, .-{fn}"
        .ok (out.push "\t.ltorg")

/-- Emit ELF + DWARF CFI + `.L`-scrubbed AAPCS64 assembly from compiled `fs` and `code`.
When `hints?` is supplied, exact `(nslots, saved)` values are enforced against `code`; otherwise
they are inferred from prologue `str x30` + `saveCs` and cross-checked across all exit tails. -/
def emitArm64DebugAsmChecked (fs : List Fn) (code : List Directive)
    (hints? : Option (List Arm64Hints) := none) (exits : List Sym := [])
    (comments : Bool := false) : Except String String := do
  let names := fs.map (·.name)
  let slices ← splitFnSlices names code
  let nonLocal := (names ++ exits).foldl (fun s k => s.insert k) ({} : HashSet Sym)
  let pairs : List ((Sym × List Directive) × (Nat × List Reg)) ←
    match hints? with
    | some hs =>
      if hs.length != fs.length then
        .error s!"hints length {hs.length} != functions length {fs.length}"
      else
        .ok (slices.zip (hs.map fun h => (h.nslots, h.saved)))
    | none =>
      slices.mapM fun (fn, body) => do
        let info ← inferFnSaved fn nonLocal body
        .ok ((fn, body), info)
  let mut out : Array String := #[".text"]
  for ((fn, body), (nslots, saved)) in pairs do
    out ← emitArm64Fn fn nslots saved nonLocal comments body out
  return String.intercalate "\n" out.toList ++ "\n"

/-- Infallible wrapper around `emitArm64DebugAsmChecked` for CLI assembly emission. -/
def emitArm64DebugAsm (fs : List Fn) (code : List Directive)
    (hints? : Option (List Arm64Hints) := none) (exits : List Sym := [])
    (comments : Bool := false) : String :=
  match emitArm64DebugAsmChecked fs code hints? exits comments with
  | .ok s => s
  | .error e => panic! s!"emitArm64DebugAsm: {e}"

end LeanQbe.T.Arm64
