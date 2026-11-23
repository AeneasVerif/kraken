module

public import LeanQbe.T.Main
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
open LeanQbe.T Kraken Kraken.X64

/-- Frame hints specialization for SysV x64 (`x64Target`). -/
abbrev X64Hints : Type := Hints Reg64 RegMm CondCode

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
  | e => e

private def scrubAddr (fn : Sym) (nonLocal : HashSet Sym) (a : AddrExpr) : AddrExpr :=
  { a with disp := scrubConst fn nonLocal a.disp }

private def scrubRM {w : Width} (fn : Sym) (nonLocal : HashSet Sym) :
    RegOrMem w → RegOrMem w
  | .reg r => .reg r
  | .mem a => .mem (scrubAddr fn nonLocal a)

private def scrubOpd {w : Width} (fn : Sym) (nonLocal : HashSet Sym) :
    Operand w → Operand w
  | .regOrMem rm => .regOrMem (scrubRM fn nonLocal rm)
  | .imm c => .imm (scrubConst fn nonLocal c)

private def scrubRelRM (fn : Sym) (nonLocal : HashSet Sym) : RelRegOrMem → RelRegOrMem
  | .rel c => .rel (scrubConst fn nonLocal c)
  | .reg r => .reg r
  | .mem a => .mem (scrubAddr fn nonLocal a)

private def scrubSC (fn : Sym) (nonLocal : HashSet Sym) : ShiftCountExpr → ShiftCountExpr
  | .cl => .cl
  | .imm8 c => .imm8 (scrubConst fn nonLocal c)

private def scrubAvxRM {w : AvxWidth} (fn : Sym) (nonLocal : HashSet Sym) :
    AvxRegOrMem w → AvxRegOrMem w
  | .avx r => .avx r
  | .mem a => .mem (scrubAddr fn nonLocal a)

private def scrubOp {w : Width} (fn : Sym) (nonLocal : HashSet Sym) :
    Operation w → Operation w
  | .mov d op => .mov (scrubRM fn nonLocal d) (scrubOpd fn nonLocal op)
  | .movsx d rm => .movsx (scrubRM fn nonLocal d) (scrubRM fn nonLocal rm)
  | .movzx d rm => .movzx (scrubRM fn nonLocal d) (scrubRM fn nonLocal rm)
  | .push op => .push (scrubOpd fn nonLocal op)
  | .pop d => .pop (scrubRM fn nonLocal d)
  | .setcc cc d => .setcc cc (scrubRM fn nonLocal d)
  | .cmovcc cc r rm => .cmovcc cc r (scrubRM fn nonLocal rm)
  | .movs b => .movs b
  | .stos b => .stos b
  | .lea r a => .lea r (scrubAddr fn nonLocal a)
  | .add d op => .add (scrubRM fn nonLocal d) (scrubOpd fn nonLocal op)
  | .adc d op => .adc (scrubRM fn nonLocal d) (scrubOpd fn nonLocal op)
  | .adcx r rm => .adcx r (scrubRM fn nonLocal rm)
  | .adox r rm => .adox r (scrubRM fn nonLocal rm)
  | .inc rm => .inc (scrubRM fn nonLocal rm)
  | .dec rm => .dec (scrubRM fn nonLocal rm)
  | .neg rm => .neg (scrubRM fn nonLocal rm)
  | .sub d op => .sub (scrubRM fn nonLocal d) (scrubOpd fn nonLocal op)
  | .sbb d op => .sbb (scrubRM fn nonLocal d) (scrubOpd fn nonLocal op)
  | .cmp rm op => .cmp (scrubRM fn nonLocal rm) (scrubOpd fn nonLocal op)
  | .mul rm => .mul (scrubRM fn nonLocal rm)
  | .mulx r1 r2 rm => .mulx r1 r2 (scrubRM fn nonLocal rm)
  | .imul1 rm => .imul1 (scrubRM fn nonLocal rm)
  | .imul d rm op => .imul (d.map (scrubRM fn nonLocal)) (scrubRM fn nonLocal rm)
      (scrubOpd fn nonLocal op)
  | .div rm => .div (scrubRM fn nonLocal rm)
  | .idiv rm => .idiv (scrubRM fn nonLocal rm)
  | .test rm op => .test (scrubRM fn nonLocal rm) (scrubOpd fn nonLocal op)
  | .and d op => .and (scrubRM fn nonLocal d) (scrubOpd fn nonLocal op)
  | .not d => .not (scrubRM fn nonLocal d)
  | .or d op => .or (scrubRM fn nonLocal d) (scrubOpd fn nonLocal op)
  | .xor d op => .xor (scrubRM fn nonLocal d) (scrubOpd fn nonLocal op)
  | .shl d sc => .shl (scrubRM fn nonLocal d) (scrubSC fn nonLocal sc)
  | .shr d sc => .shr (scrubRM fn nonLocal d) (scrubSC fn nonLocal sc)
  | .sar d sc => .sar (scrubRM fn nonLocal d) (scrubSC fn nonLocal sc)
  | .shld d r sc => .shld (scrubRM fn nonLocal d) r (scrubSC fn nonLocal sc)
  | .shrd d r sc => .shrd (scrubRM fn nonLocal d) r (scrubSC fn nonLocal sc)
  | .rol d sc => .rol (scrubRM fn nonLocal d) (scrubSC fn nonLocal sc)
  | .ror d sc => .ror (scrubRM fn nonLocal d) (scrubSC fn nonLocal sc)
  | .rcl d sc => .rcl (scrubRM fn nonLocal d) (scrubSC fn nonLocal sc)
  | .rcr d sc => .rcr (scrubRM fn nonLocal d) (scrubSC fn nonLocal sc)
  | .bswap r => .bswap r
  | .lzcnt r rm => .lzcnt r (scrubRM fn nonLocal rm)
  | .tzcnt r rm => .tzcnt r (scrubRM fn nonLocal rm)
  | .popcnt r rm => .popcnt r (scrubRM fn nonLocal rm)
  | .shlx r rm r2 => .shlx r (scrubRM fn nonLocal rm) r2
  | .shrx r rm r2 => .shrx r (scrubRM fn nonLocal rm) r2
  | .sarx r rm r2 => .sarx r (scrubRM fn nonLocal rm) r2
  | .rorx r rm ce => .rorx r (scrubRM fn nonLocal rm) (scrubConst fn nonLocal ce)
  | .cld => .cld
  | .std => .std
  | .jcc cc l => .jcc cc (scrubSym fn nonLocal l)
  | .jmp rrm => .jmp (scrubRelRM fn nonLocal rrm)
  | .call rrm => .call (scrubRelRM fn nonLocal rrm)
  | .ret => .ret
  | .nop n => .nop n
  | .nopalign a b => .nopalign a b

private def scrubAvx {w : AvxWidth} (fn : Sym) (nonLocal : HashSet Sym) :
    AvxOperation w → AvxOperation w
  | .movups d s => .movups (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .vmovups d s => .vmovups (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .movaps d s => .movaps (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .subps d s => .subps (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .addps d s => .addps (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .movdqu d s => .movdqu (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .movdqa d s => .movdqa (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .paddd d s => .paddd (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .pshufb d s => .pshufb (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .pshufd d s c => .pshufd (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
      (scrubConst fn nonLocal c)
  | .palignr d s c => .palignr (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
      (scrubConst fn nonLocal c)
  | .pblendw d s c => .pblendw (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
      (scrubConst fn nonLocal c)
  | .vmovdqu d s => .vmovdqu (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .vmovIn n d s => .vmovIn n d (scrubRM fn nonLocal s)
  | .vmovOut n d s => .vmovOut n (scrubRM fn nonLocal d) s
  | .vmovq d s => .vmovq d s
  | .vzeroupper => .vzeroupper
  | .sha256rnds2 d s => .sha256rnds2 (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .sha256msg1 d s => .sha256msg1 (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .sha256msg2 d s => .sha256msg2 (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .vmovdqu32 d s => .vmovdqu32 (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .vmovdqa32 d s => .vmovdqa32 (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
  | .vpaddd d s1 s2 => .vpaddd (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s1)
      (scrubAvxRM fn nonLocal s2)
  | .vprord d s c => .vprord (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
      (scrubConst fn nonLocal c)
  | .vpsrld d s c => .vpsrld (scrubAvxRM fn nonLocal d) (scrubAvxRM fn nonLocal s)
      (scrubConst fn nonLocal c)
  | .vpternlogd d s1 s2 c => .vpternlogd (scrubAvxRM fn nonLocal d)
      (scrubAvxRM fn nonLocal s1) (scrubAvxRM fn nonLocal s2) (scrubConst fn nonLocal c)

private def scrubDir (fn : Sym) (nonLocal : HashSet Sym) : Directive → Directive
  | .instr (.regular w ow op) => .instr (.regular w ow (scrubOp fn nonLocal op))
  | .instr (.avx w ow op) => .instr (.avx w ow (scrubAvx fn nonLocal op))
  | .label l => .label (scrubSym fn nonLocal l)
  | .byteArray bs => .byteArray bs
  | .word n e => .word n (scrubConst fn nonLocal e)

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
  | [], d :: _ => .error s!"unexpected trailing directives after functions: {ATT.directive d}"
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
    | d :: _ => .error s!"expected function label '{nm}', found '{ATT.directive d}'"
    | [] => .error s!"unexpected EOF before function '{nm}'"

private def matchPrologueSz (body : List Directive) : Option (Nat × List Directive) :=
  match body with
  | .instr (.regular .W64 .W64
      (.sub (.reg (.low .rsp .W64)) (.imm (.int64 c)))) :: rest =>
    if c.toInt >= 8 then
      let sz := c.toInt.toNat
      if body.take 1 == emitClean (x64PrologueIns (sz / 8)) then some (sz, rest) else none
    else none
  | .instr (.regular .W64 .W64
      (.mov (.reg (.low .r10 .W64)) (.imm (.int64 c)))) ::
    .instr (.regular .W64 .W64
      (.sub (.reg (.low .rsp .W64)) (.reg (.low .r10 .W64)))) :: rest =>
    let sz := c.toUInt64.toNat
    if sz >= 8 && sz % 16 == 8 && body.take 2 == emitClean (x64PrologueIns (sz / 8)) then
      some (sz, rest)
    else none
  | _ => none

private def matchSlotSt (ds : List Directive) :
    Option (Nat × Reg64 × List Directive × List Directive) :=
  match ds with
  | .instr (.regular .W64 .W64
      (.mov (.mem ⟨some (.reg .rsp), none, .int64 c⟩) (.reg (.low r .W64)))) :: rest =>
    if c.toInt >= 0 && c.toInt % 8 == 0 && x64Frame.calleeSaved.contains r then
      let slot := c.toInt.toNat / 8
      if ds.take 1 == x64SlotSt slot r then some (slot, r, ds.take 1, rest) else none
    else none
  | .instr (.regular .W64 .W64 (.mov (.reg (.low .r10 .W64)) (.imm (.int64 c)))) ::
    .instr (.regular .W64 .W64 (.mov (.mem _) (.reg (.low r .W64)))) :: rest =>
    let off := c.toUInt64.toNat
    if off % 8 == 0 && x64Frame.calleeSaved.contains r then
      let slot := off / 8
      if ds.take 2 == x64SlotSt slot r then some (slot, r, ds.take 2, rest) else none
    else none
  | _ => none

private def collectSavePrefix (sz : Nat) :
    Nat → Option Nat → List Reg64 → List Directive → List (Nat × Reg64)
  | 0, _, _, _ => []
  | fuel + 1, expSlot, seen, ds =>
    match matchSlotSt ds with
    | some (slot, r, _, rest) =>
      let contiguous := match expSlot with | none => true | some exp => slot == exp
      if contiguous && !seen.contains r && x64FrameSize (slot + 1) <= sz then
        (slot, r) :: collectSavePrefix sz fuel (some (slot + 1)) (r :: seen) rest
      else []
    | none => []

private def matchSlotLdRev (dsRev : List Directive) :
    Option (Nat × Reg64 × List Directive) :=
  match dsRev with
  | .instr (.regular .W64 .W64
      (.mov (.reg (.low r .W64)) (.mem ⟨some (.reg .rsp), none, .int64 c⟩))) :: prev =>
    if c.toInt >= 0 && c.toInt % 8 == 0 && x64Frame.calleeSaved.contains r then
      let slot := c.toInt.toNat / 8
      let expected := x64SlotLd r slot
      if expected.length == 1 && dsRev.take 1 == expected.reverse then some (slot, r, prev)
      else none
    else none
  | .instr (.regular .W64 .W64 (.mov (.reg (.low r .W64)) (.mem _))) ::
    .instr (.regular .W64 .W64 (.mov (.reg (.low .r10 .W64)) (.imm (.int64 c)))) :: prev =>
    let off := c.toUInt64.toNat
    if off % 8 == 0 && x64Frame.calleeSaved.contains r then
      let slot := off / 8
      let expected := x64SlotLd r slot
      if expected.length == 2 && dsRev.take 2 == expected.reverse then some (slot, r, prev)
      else none
    else none
  | _ => none

private def collectRestoreRev :
    Nat → Option Nat → List Reg64 → List Directive → List (Nat × Reg64)
  | 0, _, _, _ => []
  | fuel + 1, expectedSlot?, seen, dsRev =>
    match matchSlotLdRev dsRev with
    | some (slot, r, prev) =>
      let contiguous := match expectedSlot? with | none => true | some exp => slot == exp
      if contiguous && !seen.contains r && slot > 0 then
        (slot, r) :: collectRestoreRev fuel (some (slot - 1)) (r :: seen) prev
      else if contiguous && !seen.contains r && slot == 0 then
        [(slot, r)]
      else []
    | none => []

private def collectTailRestores (fn : Sym) (nonLocal : HashSet Sym) (epi : List Directive) :
    List Directive → List Directive → List (List (Nat × Reg64)) → List (List (Nat × Reg64))
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

private structure FnFrameInfo where
  zeroFrame : Bool
  nslots : Nat
  saved : List Reg64

private def addrUsesRsp (a : AddrExpr) : Bool :=
  a.base == some (.reg .rsp) ||
    match a.idx with | some i => i.reg == .rsp | none => false

private def rmUsesRsp {w : Width} : RegOrMem w → Bool
  | .reg (.low .rsp _) => true
  | .mem a => addrUsesRsp a
  | _ => false

private def avxRmUsesRsp {w : AvxWidth} : AvxRegOrMem w → Bool
  | .mem a => addrUsesRsp a
  | _ => false

private def isNonLeafOrFrameDir : Directive → Bool
  | .instr (.regular _ _ (.call _)) => true
  | .instr (.regular _ _ (.push _)) => true
  | .instr (.regular _ _ (.pop _)) => true
  | .instr (.regular _ _ (.sub d _)) => rmUsesRsp d
  | .instr (.regular _ _ (.add d _)) => rmUsesRsp d
  | .instr (.regular _ _ (.lea (.low .rsp _) _)) => true
  | .instr (.regular _ _ (.mov d op)) =>
    rmUsesRsp d || match op with | .regOrMem rm => rmUsesRsp rm | .imm _ => false
  | .instr (.avx _ _ (.vmovdqu32 d s)) => avxRmUsesRsp d || avxRmUsesRsp s
  | .instr (.avx _ _ (.vmovdqu d s)) => avxRmUsesRsp d || avxRmUsesRsp s
  | .instr (.avx _ _ (.vmovups d s)) => avxRmUsesRsp d || avxRmUsesRsp s
  | .instr (.avx _ _ (.vmovIn _ _ s)) => rmUsesRsp s
  | .instr (.avx _ _ (.vmovOut _ d _)) => rmUsesRsp d
  | _ => false

private def inferFnFrame (fn : Sym) (nonLocal : HashSet Sym) (body : List Directive) :
    Except String FnFrameInfo :=
  match matchPrologueSz body with
  | none =>
    if x64Frame.leafZeroFrame && !body.any isNonLeafOrFrameDir then
      .ok ⟨true, 0, []⟩
    else
      .error s!"function '{fn}': unrecognized x64 prologue"
  | some (sz, afterPro) =>
    let epi := emitClean (x64EpilogueIns (sz / 8))
    let cands := collectSavePrefix sz afterPro.length none [] afterPro
    let tails := collectTailRestores fn nonLocal epi [] afterPro []
    let lo := sz / 8 - 1
    let hi := sz / 8
    let rec tryLen : Nat → Option (Nat × List Reg64)
      | 0 => some (sz / 8, [])
      | m + 1 =>
        let slice := cands.take (m + 1)
        match slice with
        | [] => some (sz / 8, [])
        | (base, _) :: _ =>
          let tot := base + slice.length
          let totalOk := (tot == lo || tot == hi) && x64FrameSize tot == sz
          if totalOk && tails.all (isSuffixOf slice) then
            some (base, slice.map Prod.snd)
          else
            tryLen m
    match tryLen cands.length with
    | some (nslots, saved) => .ok ⟨false, nslots, saved⟩
    | none => .error s!"function '{fn}': could not infer x64 callee-saved slots"

private def pushDirLine (fn : Sym) (nonLocal : HashSet Sym) (loopHdrs : HashSet Sym)
    (loopAlign : Bool) (d : Directive) (out : Array String) : Array String :=
  let out := match d with
    | .label l => if loopAlign && loopHdrs.contains l then out.push loopAlignDirective else out
    | _ => out
  out.push (ATT.directive (scrubDir fn nonLocal d))

private def pushDirLines (fn : Sym) (nonLocal : HashSet Sym) (ds : List Directive)
    (out : Array String) : Array String :=
  ds.foldl (fun acc d => acc.push (ATT.directive (scrubDir fn nonLocal d))) out

private def emitBodyTails (fn : Sym) (nonLocal : HashSet Sym) (loopHdrs : HashSet Sym)
    (loopAlign comments : Bool) (restoreChunks : List (Reg64 × List Directive))
    (restoreFlat epi : List Directive) : Nat → List Directive → Array String → Array String
  | 0, rem, out => rem.foldl (fun acc d => pushDirLine fn nonLocal loopHdrs loopAlign d acc) out
  | _ + 1, [], out => out
  | fuel + 1, rem@(d :: ds), out =>
    match dropPrefix? restoreFlat rem with
    | some afterRest =>
      match dropPrefix? epi afterRest with
      | some (tailD :: afterTail) =>
        match isTailDir fn nonLocal tailD with
        | some kind =>
          let needState := !afterTail.isEmpty
          let out := if comments then out.push s!"\t# epilogue ({kind})" else out
          let out := if needState then out.push "\t.cfi_remember_state" else out
          let out := restoreChunks.foldl (fun acc (r, lds) =>
            (pushDirLines fn nonLocal lds acc).push s!"\t.cfi_restore {cfiReg r}") out
          let out := (pushDirLines fn nonLocal epi out).push "\t.cfi_def_cfa_offset 8"
          let out := out.push (ATT.directive (scrubDir fn nonLocal tailD))
          let out := if needState then out.push "\t.cfi_restore_state" else out
          emitBodyTails fn nonLocal loopHdrs loopAlign comments restoreChunks restoreFlat epi
            fuel afterTail out
        | none =>
          emitBodyTails fn nonLocal loopHdrs loopAlign comments restoreChunks restoreFlat epi
            fuel ds (pushDirLine fn nonLocal loopHdrs loopAlign d out)
      | _ =>
        emitBodyTails fn nonLocal loopHdrs loopAlign comments restoreChunks restoreFlat epi
          fuel ds (pushDirLine fn nonLocal loopHdrs loopAlign d out)
    | none =>
      emitBodyTails fn nonLocal loopHdrs loopAlign comments restoreChunks restoreFlat epi
        fuel ds (pushDirLine fn nonLocal loopHdrs loopAlign d out)

private def emitX64Header (fn : Sym) (sz : Nat) (saved : List Reg64) (comments : Bool)
    (out : Array String) : Array String :=
  let savedNames := String.intercalate "," (saved.map cfiReg)
  let out :=
    if comments then
      out.push s!"# fn {fn}: frame={sz}B cfa=rsp+{8 + sz} saved=[{savedNames}]"
    else out
  out
    |>.push s!"\t.globl {fn}"
    |>.push s!"\t.type {fn}, %function"
    |>.push s!"{fn}:"
    |>.push "\t.cfi_startproc"

private def emitX64Fn (fn : Sym) (info : FnFrameInfo) (nonLocal : HashSet Sym)
    (loopAlign comments : Bool) (body : List Directive) (out : Array String) :
    Except String (Array String) :=
  let loopHdrs : HashSet Sym :=
    if loopAlign then (detectLoopHeaders body).foldl (fun s l => s.insert l) {} else {}
  if info.zeroFrame then
    let out := emitX64Header fn 0 [] comments out
    let out := body.foldl (fun acc d => pushDirLine fn nonLocal loopHdrs loopAlign d acc) out
    .ok (out |>.push "\t.cfi_endproc" |>.push s!"\t.size {fn}, .-{fn}")
  else
    let ns := info.nslots + info.saved.length
    let sz := x64FrameSize ns
    let pro := emitClean (x64PrologueIns ns)
    match dropPrefix? pro body with
    | none => .error s!"function '{fn}': prologue mismatch for totalSlots={ns}"
    | some afterPro =>
      let rec consumeSaves (idx : Nat) (ds : List Directive) (acc : Array String) :
          List Reg64 → Except String (Array String × List Directive)
        | [] => .ok (acc, ds)
        | r :: rs =>
          let st := x64SlotSt idx r
          match dropPrefix? st ds with
          | none => .error s!"function '{fn}': saveCs mismatch for {cfiReg r} at slot {idx}"
          | some rest =>
            let cfaOff := 8 + sz - 8 * idx
            let acc := (pushDirLines fn nonLocal st acc).push
              s!"\t.cfi_offset {cfiReg r}, -{cfaOff}"
            consumeSaves (idx + 1) rest acc rs
      let out := emitX64Header fn sz info.saved comments out
      let out := (pushDirLines fn nonLocal pro out).push s!"\t.cfi_def_cfa_offset {8 + sz}"
      match consumeSaves info.nslots afterPro out info.saved with
      | .error e => .error e
      | .ok (out, restBody) =>
        let restoreChunks := (List.range info.saved.length).zip info.saved |>.map fun (k, r) =>
          (r, x64SlotLd r (info.nslots + k))
        let restoreFlat := restoreChunks.flatMap Prod.snd
        let epi := emitClean (x64EpilogueIns ns)
        let out := emitBodyTails fn nonLocal loopHdrs loopAlign comments restoreChunks
          restoreFlat epi restBody.length restBody out
        .ok (out |>.push "\t.cfi_endproc" |>.push s!"\t.size {fn}, .-{fn}")

/-- Emit ELF + DWARF CFI + `.L`-scrubbed x64 assembly from compiled `fs` and `code`.
When `hints?` is supplied, exact `(nslots, saved)` values are enforced against `code`; otherwise
they are inferred and cross-checked across prologue and all exit tails. -/
def emitX64DebugAsmChecked (fs : List Fn) (code : List Directive)
    (hints? : Option (List X64Hints) := none) (exits : List Sym := [])
    (comments : Bool := false) (loopAlign : Bool := true) : Except String String := do
  let names := fs.map (·.name)
  let slices ← splitFnSlices names code
  let nonLocal := (names ++ exits).foldl (fun s k => s.insert k) ({} : HashSet Sym)
  let pairs : List ((Sym × List Directive) × FnFrameInfo) ←
    match hints? with
    | some hs =>
      if hs.length != fs.length then
        .error s!"hints length {hs.length} != functions length {fs.length}"
      else
        (slices.zip hs).mapM fun ((fn, body), h) => do
          let ns := h.nslots + h.saved.length
          if ns == 0 && x64Frame.leafZeroFrame then
            let pro := emitClean (x64PrologueIns 0)
            match dropPrefix? pro body with
            | some _ => .ok ((fn, body), ⟨false, 0, []⟩)
            | none =>
              if !body.any isNonLeafOrFrameDir then
                .ok ((fn, body), ⟨true, 0, []⟩)
              else
                .error s!"function '{fn}': prologue mismatch for totalSlots=0"
          else
            .ok ((fn, body), ⟨false, h.nslots, h.saved⟩)
    | none =>
      slices.mapM fun (fn, body) => do
        let info ← inferFnFrame fn nonLocal body
        .ok ((fn, body), info)
  let mut out : Array String := #[".text"]
  for ((fn, body), info) in pairs do
    out ← emitX64Fn fn info nonLocal loopAlign comments body out
  return String.intercalate "\n" out.toList ++ "\n"

/-- Infallible wrapper around `emitX64DebugAsmChecked` for CLI assembly emission. -/
def emitX64DebugAsm (fs : List Fn) (code : List Directive)
    (hints? : Option (List X64Hints) := none) (exits : List Sym := [])
    (comments : Bool := false) (loopAlign : Bool := true) : String :=
  match emitX64DebugAsmChecked fs code hints? exits comments loopAlign with
  | .ok s => s
  | .error e => panic! s!"emitX64DebugAsm: {e}"

end LeanQbe.T.Amd64
