module

public import LeanQbe.T.Amd64.Isa
public import LeanQbe.T.SnippetCheck
public import LeanQbe.T.SpillSnippet
public import Kraken.X64.Parser
public import Kraken.X64.PrintATT

/-!
# SysV x86-64 Snippet Budget Profiler, `AsmIso`, and Untrusted Lifter (`Amd64.Snippet`)

Purely additive Class `L` backend adapter under `LeanQbe.T.Amd64`:

* `profileDirsX64`, `stripPrologueEpilogueX64`: x86-64 assembly profiler counting body insns,
  body spills (`%rsp`-relative ops), bool `movzx`, `cmovcc`, compares/tests, branches, and calls.
* `checkAsmIsoX64`: CFG alpha-isomorphism checker (`IsoVerdict.tier1` / `tier2` / `fail`).
* `liftSnippetU`, `liftSnippetX64`: untrusted x86-64 assembly lifter (`List x64Isa.Directive` ->
  `LiftedSnippet Reg64 CondCode rs` -> solved `x64Isa.Hints` + lowered fixpoint check +
  `IsoVerdict`).
* `checkRegaAndBudgetX64`: end-to-end `Rega.lowerFn` + `@predictable` static `SnippetBudget`
  verification inside an outer function.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.SnippetCheck LeanQbe.T.SpillSnippet Kraken.X64

local instance : Inhabited Reg64 := ⟨.rax⟩

abbrev XDir := x64Isa.Directive

/-! ## 1. Prologue/Epilogue Stripping & `BudgetMetrics` Profiler -/

def stripNops (ds : List XDir) : List XDir :=
  ds.filter fun
    | .instr (.regular _ _ (.nop _)) => false
    | .instr (.regular _ _ (.nopalign _ _)) => false
    | _ => true

def isRspAddr (a : AddrExpr) : Bool :=
  a.base == some (.reg .rsp)

def isBodySpillInstr : Instr → Bool
  | .regular _ _ (.mov (.reg _) (.mem a)) | .regular _ _ (.mov (.mem a) _)
  | .regular _ _ (.movzx (.reg _) (.mem a)) | .regular _ _ (.movsx (.reg _) (.mem a))
  | .regular _ _ (.cmp (.mem a) _) | .regular _ _ (.test (.mem a) _)
  | .regular _ _ (.add (.reg _) (.regOrMem (.mem a)))
  | .regular _ _ (.sub (.reg _) (.regOrMem (.mem a)))
  | .regular _ _ (.and (.reg _) (.regOrMem (.mem a)))
  | .regular _ _ (.or (.reg _) (.regOrMem (.mem a)))
  | .regular _ _ (.xor (.reg _) (.regOrMem (.mem a))) => isRspAddr a
  | _ => false

def isEpilogueInstr : Instr → Bool
  | .regular _ .W64 (.add (.reg (.low .rsp .W64)) (.imm _)) => true
  | .regular _ .W64 (.pop _) => true
  | .regular _ .W64 (.mov (.reg (.low r .W64)) (.mem a)) =>
    isRspAddr a && x64Frame.calleeSaved.contains r
  | _ => false

def stripPrologueEpilogue (ds : List XDir) : List XDir × Nat × List Reg64 :=
  let rec peelPro (saved : List Reg64) (frameSz : Nat) : List XDir → List XDir × Nat × List Reg64
    | .instr i :: rest =>
      match i with
      | .regular _ .W64 (.sub (.reg (.low .rsp .W64)) (.imm (.int64 sz))) =>
        peelPro saved sz.toNatClampNeg rest
      | .regular _ .W64 (.push (.regOrMem (.reg (.low r .W64)))) =>
        peelPro (if saved.contains r then saved else saved ++ [r]) frameSz rest
      | .regular _ .W64 (.mov (.mem a) (.reg (.low r .W64))) =>
        if isRspAddr a && x64Frame.calleeSaved.contains r then
          peelPro (if saved.contains r then saved else saved ++ [r]) frameSz rest
        else (.instr i :: rest, frameSz, saved)
      | _ => (.instr i :: rest, frameSz, saved)
    | other => (other, frameSz, saved)
  let labelOf? : XDir → Option String | .label l => some l | _ => none
  let isRet : XDir → Bool | .instr (.regular _ _ .ret) => true | _ => false
  let peelEpi := peelRevWhile (fun | .instr i => isEpilogueInstr i | _ => false)
  stripPrologueEpilogueGen stripNops labelOf? peelPro isRet peelEpi ds

/-- Profile x86-64 directives into target-generic `BudgetMetrics`. -/
def profileDirs (ds : List XDir) (stripFrame : Bool := true) : BudgetMetrics :=
  let instrOf? : XDir → Option Instr | .instr i => some i | _ => none
  let stepBody (i : Instr) (prevSetcc : Bool) (m : BudgetMetrics) : Bool × BudgetMetrics :=
    match i with
    | .regular _ _ (.mov (.reg _) (.regOrMem (.reg _))) =>
      (false, { m with regMoves := m.regMoves + 1 })
    | .regular _ _ (.movzx (.reg _) (.reg _)) =>
      let bInc := if prevSetcc then 1 else 0
      (false, { m with boolChains := m.boolChains + bInc, regMoves := m.regMoves + 1 })
    | .regular _ _ (.setcc _ _) => (true, m)
    | .regular _ _ (.cmovcc _ _ _) => (false, { m with selectOps := m.selectOps + 1 })
    | .regular _ _ (.cmp _ _) | .regular _ _ (.test _ _) =>
      (false, { m with cmpsTests := m.cmpsTests + 1 })
    | .regular _ _ (.jcc _ _) => (false, { m with branches := m.branches + 1 })
    | .regular _ _ (.jmp _) => (false, { m with jmps := m.jmps + 1 })
    | .regular _ _ (.lea _ _) => (false, { m with leas := m.leas + 1 })
    | .regular _ _ (.call _) => (false, { m with calls := m.calls + 1 })
    | _ => (false, m)
  profileDirsGen stripNops (fun x => (stripPrologueEpilogue x).1)
    instrOf? isBodySpillInstr false stepBody ds stripFrame

/-! ## 2. `AsmIso` (Tier 1 & Tier 2) CFG Alpha-Isomorphism Checker -/

abbrev CfgBlock := GenCfgBlock Instr CondCode

namespace SnippetImpl

def labelOf? : XDir → Option String | .label l => some l | _ => none
def instrOf? : XDir → Option Instr | .instr i => some i | _ => none

def isTerm : Instr → Bool
  | .regular _ _ .ret | .regular _ _ (.jmp _) | .regular _ _ (.jcc _ _) => true
  | _ => false

def extractBranch? : Instr → Option (CondCode × String)
  | .regular _ _ (.jcc cc tgt) => some (cc, tgt)
  | _ => none

def parseTerm (i : Instr) (nextLbl? : Option String) : Option (CfgTerm CondCode) :=
  match i with
  | .regular _ _ .ret => some .ret
  | .regular _ _ (.jmp (.rel (.label t))) => some (.jmp t)
  | .regular _ _ (.jmp (.rel (.sub (.label t) .after_current_instruction))) => some (.jmp t)
  | .regular _ _ (.jmp (.rel t)) => some (.exit (toString (repr t)))
  | .regular _ _ (.jcc cc tgt) => some (.jcc cc tgt (nextLbl?.getD "__end"))
  | _ => none

end SnippetImpl

def toCfgBlocks (ds : List XDir) (stripFrame : Bool := true) : List CfgBlock :=
  toCfgBlocksGen stripNops (fun x => (stripPrologueEpilogue x).1)
    SnippetImpl.labelOf? SnippetImpl.instrOf? SnippetImpl.isTerm
    SnippetImpl.parseTerm SnippetImpl.extractBranch? ds stripFrame

abbrev IsoState := GenIsoState Reg64

def matchReg64 (fixedRegs : List Reg64) (r1 r2 : Reg64) (st : IsoState) : Option IsoState :=
  matchFixedReg fixedRegs r1 r2 st

def matchReg {w : Width} (fixed : List Reg64) (r1 r2 : Reg w) (st : IsoState) :
    Option IsoState :=
  match r1, r2 with
  | .low a _, .low b _ => matchReg64 fixed a b st
  | .ah, .ah | .bh, .bh | .ch, .ch | .dh, .dh => some st
  | _, _ => none

def matchConstExpr (c1 c2 : ConstExpr) (st : IsoState) : Option IsoState :=
  matchConstExprGen (fun | .label l => some l | _ => none) c1 c2 st

def matchAddr (fixed : List Reg64) (a1 a2 : AddrExpr) (st : IsoState) : Option IsoState := do
  let st ← match a1.base, a2.base with
    | some (.reg r1), some (.reg r2) => matchReg64 fixed r1 r2 st
    | some .rip, some .rip => some st
    | none, none => some st
    | _, _ => none
  let st ← match a1.idx, a2.idx with
    | some i1, some i2 =>
      if i1.scale == i2.scale then matchReg64 fixed i1.reg i2.reg st else none
    | none, none => some st
    | _, _ => none
  if a1.base == some (.reg .rsp) && a1.idx.isNone && a2.idx.isNone then
    match a1.disp, a2.disp with
    | .int64 d1, .int64 d2 =>
      (bindBijection d1 d2 st.slotMap).map fun sm => { st with slotMap := sm }
    | _, _ => matchConstExpr a1.disp a2.disp st
  else
    matchConstExpr a1.disp a2.disp st

def matchRegOrMem {w : Width} (fixed : List Reg64) (x1 x2 : RegOrMem w) (st : IsoState) :
    Option IsoState :=
  match x1, x2 with
  | .reg r1, .reg r2 => matchReg fixed r1 r2 st
  | .mem a1, .mem a2 => matchAddr fixed a1 a2 st
  | _, _ => none

def matchOperand {w : Width} (fixed : List Reg64) (o1 o2 : Operand w) (st : IsoState) :
    Option IsoState :=
  match o1, o2 with
  | .regOrMem x1, .regOrMem x2 => matchRegOrMem fixed x1 x2 st
  | .imm c1, .imm c2 => matchConstExpr c1 c2 st
  | _, _ => none

def matchShiftCount (c1 c2 : ShiftCountExpr) (st : IsoState) : Option IsoState :=
  match c1, c2 with
  | .cl, .cl => some st
  | .imm8 a, .imm8 b => matchConstExpr a b st
  | _, _ => none

def matchOperation {w : Width} (fixed : List Reg64) (op1 op2 : Operation w)
    (st : IsoState) : Option IsoState :=
  let mrm {u} (d1 d2 : RegOrMem u) (s : IsoState) := matchRegOrMem fixed d1 d2 s
  let mop (d1 d2 : RegOrMem w) (s1 s2 : Operand w) :=
    mrm d1 d2 st >>= matchOperand fixed s1 s2
  let msc (d1 d2 : RegOrMem w) (c1 c2 : ShiftCountExpr) :=
    mrm d1 d2 st >>= matchShiftCount c1 c2
  let m3 (d1 d2 : Reg w) (a1 a2 : RegOrMem w) (b1 b2 : Reg w) :=
    matchReg fixed d1 d2 st >>= mrm a1 a2 >>= matchReg fixed b1 b2
  match op1, op2 with
  | .mov d1 s1, .mov d2 s2 | .add d1 s1, .add d2 s2 | .adc d1 s1, .adc d2 s2
  | .sub d1 s1, .sub d2 s2 | .sbb d1 s1, .sbb d2 s2 | .cmp d1 s1, .cmp d2 s2
  | .test d1 s1, .test d2 s2 | .and d1 s1, .and d2 s2 | .or d1 s1, .or d2 s2
  | .xor d1 s1, .xor d2 s2 => mop d1 d2 s1 s2
  | .movzx (w' := w1) d1 s1, .movzx (w' := w2) d2 s2
  | .movsx (w' := w1) d1 s1, .movsx (w' := w2) d2 s2 =>
    if h : w1 = w2 then mrm d1 d2 st >>= mrm s1 (h ▸ s2) else none
  | .setcc c1 d1, .setcc c2 d2 => if c1 == c2 then mrm d1 d2 st else none
  | .cmovcc c1 d1 s1, .cmovcc c2 d2 s2 =>
    if c1 == c2 then matchReg fixed d1 d2 st >>= mrm s1 s2 else none
  | .lea d1 a1, .lea d2 a2 => matchReg fixed d1 d2 st >>= matchAddr fixed a1 a2
  | .adcx d1 s1, .adcx d2 s2 | .adox d1 s1, .adox d2 s2
  | .lzcnt d1 s1, .lzcnt d2 s2 | .tzcnt d1 s1, .tzcnt d2 s2
  | .popcnt d1 s1, .popcnt d2 s2 => matchReg fixed d1 d2 st >>= mrm s1 s2
  | .inc d1, .inc d2 | .dec d1, .dec d2 | .neg d1, .neg d2 | .not d1, .not d2
  | .mul d1, .mul d2 | .imul1 d1, .imul1 d2 | .div d1, .div d2 | .idiv d1, .idiv d2 =>
    mrm d1 d2 st
  | .mulx hi1 lo1 s1, .mulx hi2 lo2 s2 =>
    matchReg fixed hi1 hi2 st >>= matchReg fixed lo1 lo2 >>= mrm s1 s2
  | .imul d1 a1 b1, .imul d2 a2 b2 => do
    let st ← match d1, d2 with
      | some r1, some r2 => mrm r1 r2 st
      | none, none => some st
      | _, _ => none
    matchRegOrMem fixed a1 a2 st >>= matchOperand fixed b1 b2
  | .shl d1 c1, .shl d2 c2 | .shr d1 c1, .shr d2 c2 | .sar d1 c1, .sar d2 c2
  | .rol d1 c1, .rol d2 c2 | .ror d1 c1, .ror d2 c2 => msc d1 d2 c1 c2
  | .shld d1 x1 c1, .shld d2 x2 c2 | .shrd d1 x1 c1, .shrd d2 x2 c2 =>
    mrm d1 d2 st >>= matchReg fixed x1 x2 >>= matchShiftCount c1 c2
  | .shlx d1 a1 b1, .shlx d2 a2 b2 | .shrx d1 a1 b1, .shrx d2 a2 b2
  | .sarx d1 a1 b1, .sarx d2 a2 b2 => m3 d1 d2 a1 a2 b1 b2
  | .rorx d1 a1 c1, .rorx d2 a2 c2 =>
    matchReg fixed d1 d2 st >>= mrm a1 a2 >>= matchConstExpr c1 c2
  | .bswap d1, .bswap d2 => matchReg fixed d1 d2 st
  | .call t1, .call t2 => if t1 == t2 then some st else none
  | .ret, .ret => some st
  | _, _ => none

def matchInstr (fixed : List Reg64) (i1 i2 : Instr) (st : IsoState) : Option IsoState :=
  match i1, i2 with
  | .regular aw1 ow1 op1, .regular aw2 ow2 op2 =>
    if h : ow1 = ow2 then
      if aw1 == aw2 then matchOperation fixed op1 (h ▸ op2) st else none
    else none
  | _, _ => none

def matchTier2Single (fixed : List Reg64) (i1 i2 : Instr) (st : IsoState) :
    Option (IsoState × String) :=
  let mXorMov (a b c : Reg64) (rev : Bool) :=
    if a == b then
      (if rev then matchReg64 fixed c a st else matchReg64 fixed a c st).map
        (·, if rev then "mov0~xor0" else "xor0~mov0")
    else none
  let mIncDec {w} (d1 : RegOrMem w) d2 note :=
    (matchRegOrMem fixed d1 d2 st).map (·, note)
  let mTestCmp {w} (ra rb rc : Reg w) (rev : Bool) :=
    if ra == rb then
      (if rev then matchReg fixed rc ra st else matchReg fixed ra rc st).map
        (·, if rev then "cmp0~test" else "test~cmp0")
    else none
  match i1, i2 with
  | .regular _ .W32 (.xor (.reg (.low a .W32)) (.regOrMem (.reg (.low b .W32)))),
    .regular _ _ (.mov (.reg (.low c _)) (.imm (.int64 0))) => mXorMov a b c false
  | .regular _ _ (.mov (.reg (.low c _)) (.imm (.int64 0))),
    .regular _ .W32 (.xor (.reg (.low a .W32)) (.regOrMem (.reg (.low b .W32)))) =>
    mXorMov a b c true
  | .regular _ w1 (.inc d1), .regular _ w2 (.add d2 (.imm (.int64 1))) =>
    if h : w1 = w2 then mIncDec d1 (h ▸ d2) "inc~add1" else none
  | .regular _ w1 (.add d1 (.imm (.int64 1))), .regular _ w2 (.inc d2) =>
    if h : w1 = w2 then mIncDec d1 (h ▸ d2) "add1~inc" else none
  | .regular _ w1 (.dec d1), .regular _ w2 (.sub d2 (.imm (.int64 1))) =>
    if h : w1 = w2 then mIncDec d1 (h ▸ d2) "dec~sub1" else none
  | .regular _ w1 (.sub d1 (.imm (.int64 1))), .regular _ w2 (.dec d2) =>
    if h : w1 = w2 then mIncDec d1 (h ▸ d2) "sub1~dec" else none
  | .regular _ w1 (.test (.reg ra) (.regOrMem (.reg rb))),
    .regular _ w2 (.cmp (.reg rc) (.imm (.int64 0))) =>
    if h : w1 = w2 then mTestCmp ra rb (h ▸ rc) false else none
  | .regular _ w1 (.cmp (.reg rc) (.imm (.int64 0))),
    .regular _ w2 (.test (.reg ra) (.regOrMem (.reg rb))) =>
    if h : w1 = w2 then mTestCmp (h ▸ ra) (h ▸ rb) rc true else none
  | _, _ => none

def matchLeaIdxPair (fixed : List Reg64) (d rd d' s1 s2 : Reg64) (a : AddrExpr) (rev : Bool)
    (st : IsoState) : Option IsoState :=
  if d == d' && a.idx.isSome && a.disp == .int64 0 then
    match a.base, a.idx with
    | some (.reg rb), some ⟨ri, .W8⟩ =>
      let mr x y s := if rev then matchReg64 fixed y x s else matchReg64 fixed x y s
      mr d rd st >>= mr s1 rb >>= mr s2 ri
    | _, _ => none
  else none

def matchSeq (tier2 : Bool) (fixed : List Reg64) :
    List Instr → List Instr → IsoState → Option IsoState
  | [], [], st => some st
  | i1 :: r1, i2 :: r2, st =>
    (matchInstr fixed i1 i2 st >>= matchSeq tier2 fixed r1 r2) <|>
    if !tier2 then none
    else
      (matchTier2Single fixed i1 i2 st).bind (fun (st', note) =>
        matchSeq tier2 fixed r1 r2 { st' with tier2Notes := note :: st'.tier2Notes }) <|>
      match i1, i2 with
      | .regular _ .W64 (.mov (.reg (.low d1 .W64)) (.regOrMem (.reg (.low s1 .W64)))),
        .regular _ .W64 (.lea (.low rd2 .W64) a2) =>
        match r1 with
        | .regular _ .W64 (.add (.reg (.low d1b .W64)) (.regOrMem (.reg (.low s2 .W64)))) :: r1' =>
          (matchLeaIdxPair fixed d1 rd2 d1b s1 s2 a2 false st).bind fun st' =>
            matchSeq tier2 fixed r1' r2 { st' with tier2Notes := "mov+add~lea" :: st'.tier2Notes }
        | _ => none
      | .regular _ .W64 (.lea (.low rd1 .W64) a1),
        .regular _ .W64 (.mov (.reg (.low d2 .W64)) (.regOrMem (.reg (.low s2a .W64)))) =>
        match r2 with
        | .regular _ .W64 (.add (.reg (.low d2b .W64)) (.regOrMem (.reg (.low s2b .W64)))) :: r2' =>
          (matchLeaIdxPair fixed d2 rd1 d2b s2a s2b a1 true st).bind fun st' =>
            matchSeq tier2 fixed r1 r2' { st' with tier2Notes := "lea~mov+add" :: st'.tier2Notes }
        | _ => none
      | _, _ => none
  | _, _, _ => none

def classifyMismatch (ref cand : List CfgBlock) (refB candB : BudgetMetrics) :
    String × String :=
  classifyMismatchGen "ifconv_cmov" "cmovs" "jccs"
    "bool_movzx_chain" "movzxBool" "cmpsTests" ref cand refB candB

def matchBranchCondX64 (_ : List Reg64) (c1 c2 : CondCode) (st : IsoState) :
    Option IsoState :=
  if c1 == c2 then some st else none

partial def matchCfgFrom (tier2 : Bool) (fixed : List Reg64)
    (bs1 bs2 : List CfgBlock) (l1 l2 : String) (st : IsoState) : Option IsoState :=
  matchCfgFromGen matchSeq matchBranchCondX64 x64NegCond tier2 fixed bs1 bs2 l1 l2 st

/-- Compare two x86-64 directive streams for structural/register alpha-isomorphism (`AsmIso`). -/
def checkAsmIso (ref cand : List XDir) (stripFrame : Bool := true) (allowRegPerm : Bool := true) :
    IsoVerdict :=
  let noPerm := x64Frame.allocatable ++ x64Frame.calleeSaved ++ [.rsp]
  checkAsmIsoGen (fun d s => toCfgBlocks d s) (fun d s => profileDirs d s) matchSeq
    matchBranchCondX64 x64NegCond classifyMismatch [.rsp] noPerm
    { regMap := [(.rsp, .rsp)] } ref cand stripFrame allowRegPerm

/-! ## 3. Untrusted x86-64 Lifter (`liftSnippetU`, `liftSnippet`) -/

def condToCmpOp : CondCode → Option CmpOp
  | .z => some .eq | .nz => some .ne
  | .c => some .ult | .be => some .ule
  | .a => some .ugt | .nc => some .uge
  | .l => some .slt | .le => some .sle
  | .g => some .sgt | .ge => some .sge
  | _ => none

abbrev LiftBlockSt := GenLiftSt Reg64 Reg64 CondCode

def widthBits : Width → Nat
  | .W8 => 8 | .W16 => 16 | .W32 => 32 | .W64 => 64

abbrev freshVar (st : LiftBlockSt) (r? : Option Reg64) : Nat × LiftBlockSt :=
  st.fresh some r? none
abbrev freshVarTy (st : LiftBlockSt) (r? : Option Reg64) (ty : Ty) : Nat × LiftBlockSt :=
  st.fresh some r? (some ty)
abbrev setRegVar := @GenLiftSt.setReg Reg64 Reg64 CondCode Unit _
abbrev getRegVar? := @GenLiftSt.regVar? Reg64 Reg64 CondCode Unit _
abbrev setVarTy := @GenLiftSt.setTy Reg64 Reg64 CondCode Unit
abbrev getVarTy? := @GenLiftSt.ty? Reg64 Reg64 CondCode Unit
abbrev addElides := @GenLiftSt.elide Reg64 Reg64 CondCode Unit
abbrev addClique := @GenLiftSt.clique Reg64 Reg64 CondCode Unit

def emitAddrCalc (a : AddrExpr) (st : LiftBlockSt) :
    Except String (Nat × List LiftedStmt × LiftBlockSt) := do
  let disp : BitVec 64 := match a.disp with | .int64 d => d.toBitVec | _ => 0#64
  let rb? ← match a.base with
    | some (.reg rb) =>
      match getRegVar? rb st with
      | some vb => pure (some vb)
      | none => throw s!"uninit_base_reg {repr rb}"
    | none => pure none
    | some .rip => throw "rip_rel_unsupported"
  let ri? ← match a.idx with
    | some ⟨ri, sc⟩ =>
      match getRegVar? ri st with
      | some vi =>
        let sh := match sc with | .W8 => 0 | .W16 => 1 | .W32 => 2 | .W64 => 3
        pure (some (vi, sh))
      | none => throw s!"uninit_idx_reg {repr ri}"
    | none => pure none
  match rb?, ri? with
  | some vb, none =>
    if disp == 0#64 then pure (vb, [], st)
    else
      let (va, st1) := freshVar st none
      pure (va, [.def1 va i64 (.bin 64 "add" vb none (some disp))], st1)
  | some vb, some (vi, sh) =>
    let (vs, st1, stmts1) :=
      if sh == 0 then (vi, st, [])
      else
        let (v0, s0) := freshVar st none
        (v0, s0, [.def1 v0 i64 (.bin 64 "shl" vi none (some (BitVec.ofNat 64 sh)))])
    let (va, st2) := freshVar st1 none
    let stmts2 := stmts1 ++ [.def1 va i64 (.bin 64 "add" vb (some vs) none)]
    if disp == 0#64 then pure (va, stmts2, st2)
    else
      let (vd, st3) := freshVar st2 none
      pure (vd, stmts2 ++ [.def1 vd i64 (.bin 64 "add" va none (some disp))], st3)
  | none, some (vi, sh) =>
    let (vs, st1, stmts1) :=
      if sh == 0 then (vi, st, [])
      else
        let (v0, s0) := freshVar st none
        (v0, s0, [.def1 v0 i64 (.bin 64 "shl" vi none (some (BitVec.ofNat 64 sh)))])
    if disp == 0#64 then pure (vs, stmts1, st1)
    else
      let (vd, st2) := freshVar st1 none
      pure (vd, stmts1 ++ [.def1 vd i64 (.bin 64 "add" vs none (some disp))], st2)
  | none, none =>
    let (vc, st1) := freshVar st none
    pure (vc, [.def1 vc i64 (.movi 64 disp)], st1)

def liftExt (ow : Width) {ws : Width} (isSext : Bool) (rd : Reg64) (src : RegOrMem ws)
    (cur : LiftBlockSt) : Except String (List LiftedStmt × LiftBlockSt) := do
  let w := widthBits ow
  let wsBits := widthBits ws
  let mk (m n x : Nat) := if isSext then NOp.sext m n x else NOp.zext m n x
  match src with
  | .reg (.low rs _) =>
    let vs ← match getRegVar? rs cur with
      | some v => pure v | none => throw s!"ext_uninit {repr rs}"
    let (vd, st1) := freshVar cur (some rd)
    pure ([.def1 vd (.bits w) (mk wsBits w vs)], setVarTy vd (.bits w) (setRegVar rd vd st1))
  | .mem a =>
    if isRspAddr a then throw "spill_in_body: ext slot"
    let (va, asts, st1) ← emitAddrCalc a cur
    let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
    let (vl, st2) := freshVar (addElides evs st1) (some rd)
    let (vd, st3) := freshVar st2 (some rd)
    let st4 := setVarTy vd (.bits w) (setRegVar rd vd (addClique [vl, vd] st3))
    pure (asts ++ [.def1 vl (.bits wsBits) (.load wsBits va),
                   .def1 vd (.bits w) (mk wsBits w vl)], st4)
  | _ => throw "ext_high_byte"

def liftRmwBin {ow : Width} (op : String) (setsCmp eqNe allowMem : Bool) (rd : Reg64)
    (rhs : Operand ow) (cur : LiftBlockSt) : Except String (List LiftedStmt × LiftBlockSt) := do
  let w := widthBits ow
  let va ← match getRegVar? rd cur with
    | some v => pure v | none => throw s!"{op}_uninit {repr rd}"
  let finish (vb? : Option Nat) (imm? : Option (BitVec 64)) (pre : List LiftedStmt)
      (sPre : LiftBlockSt) :=
    let (vd, st1) := freshVarTy sPre (some rd) (.bits w)
    let st2 := setRegVar rd vd (addClique [va, vd] st1)
    let st3 := if setsCmp then
        { st2 with lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := eqNe }
      else { st2 with lastCmp? := none, lastCmpEqNe := false }
    (pre ++ [.def1 vd (.bits w) (.bin w op va vb? imm?)], st3)
  match rhs with
  | .regOrMem (.reg (.low rs _)) =>
    let vb ← match getRegVar? rs cur with
      | some v => pure v | none => throw s!"{op}_rhs_uninit {repr rs}"
    pure (finish (some vb) none [] cur)
  | .imm (.int64 c) => pure (finish none (some c.toBitVec) [] cur)
  | .regOrMem (.mem a) =>
    if !allowMem then throw s!"unsupported_{op}_mem"
    if isRspAddr a then throw s!"spill_in_body: {op} slot"
    let (vaddr, asts, st1) ← emitAddrCalc a cur
    let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
    let (vld, st2) := freshVarTy (addElides evs st1) (some rd) (.bits w)
    pure (finish (some vld) none (asts ++ [.def1 vld (.bits w) (.load w vaddr)]) st2)
  | _ => throw s!"{op}_high_byte"

def liftShift (op : String) (allowCl : Bool) (w : Nat) (rd : Reg64)
    (sc : ShiftCountExpr) (cur : LiftBlockSt) : Except String (List LiftedStmt × LiftBlockSt) := do
  let va ← match getRegVar? rd cur with | some v => pure v | none => throw s!"{op}_uninit"
  let (vb?, imm?) ← match sc with
    | .imm8 (.int64 c) => pure (none, some c.toBitVec)
    | .cl =>
      if !allowCl then throw s!"unsupported_{op}_cl"
      let vc ← match getRegVar? .rcx cur with
        | some v => pure v | none => throw s!"{op}_cl_uninit"
      pure (some vc, none)
    | _ => throw s!"unsupported_{op}_sc"
  let (vd, st1) := freshVarTy cur (some rd) (.bits w)
  let st2 := { setRegVar rd vd (addClique [va, vd] st1) with
               lastCmp? := none, lastCmpEqNe := false }
  pure ([.def1 vd (.bits w) (.bin w op va vb? imm?)], st2)

def resolveX64Flag (tag : String) (cc : CondCode) (st : LiftBlockSt)
    (tyBool : Bool := true) : Except String (Nat × LiftedStmt × LiftBlockSt) := do
  let (la, lb?, lci?, lw) ← match st.lastCmp? with
    | some p => pure p | none => throw s!"{tag}_without_cmp"
  if st.lastCmpEqNe && !(cc == .z || cc == .nz) then
    throw s!"{tag}_flag_eq_ne_only {repr cc}"
  let co ← match condToCmpOp cc with
    | some p => pure p | none => throw s!"unsupported_cond {repr cc}"
  let (vc, s1) := if tyBool then freshVarTy st none .bool else freshVar st none
  pure (vc, .def1 vc .bool (.cmp co lw la lb? lci?), { s1 with flags := (vc, cc) :: s1.flags })

def liftAdcxAdox (vh : VariantHint) (flag : CondCode) (w : Nat) (rd rs : Reg64)
    (cur : LiftBlockSt) : Except String (List LiftedStmt × LiftBlockSt) := do
  let va ← match getRegVar? rd cur with | some v => pure v | none => throw "adcx_adox_uninit"
  let vb ← match getRegVar? rs cur with | some v => pure v | none => throw "adcx_adox_rhs_uninit"
  let (vd, st1) := freshVar cur (some rd)
  let (vc, st2) := freshVar st1 none
  let st3 := setRegVar rd vd (addClique [va, vd]
    { st2 with flags := (vc, flag) :: st2.flags, varHints := (vd, vh) :: st2.varHints,
               lastCarry? := some vc, lastCmp? := none, lastCmpEqNe := false })
  pure ([.def2 vd vc (.bits w) .bool (.addc w va (some vb) none cur.lastCarry? false)], st3)

def liftOneInstr (ins : Instr) (cur : LiftBlockSt) :
    Except String (List LiftedStmt × LiftBlockSt) := do
  match ins with
  | .regular _ ow op =>
    let w := widthBits ow
    match op with
    | .mov (.reg (.low rd _)) (.regOrMem (.reg (.low rs _))) =>
      match getRegVar? rs cur with
      | some vs =>
        let (vd, st1) := freshVar cur (some rd)
        let st2 := setVarTy vd (.bits w) (setRegVar rd vd st1)
        let stmt := match getVarTy? vs cur with
          | some (.bits m) =>
            if w < m then LiftedStmt.def1 vd (.bits w) (.trunc m w vs)
            else if w > m then LiftedStmt.def1 vd (.bits w) (.zext m w vs)
            else LiftedStmt.def1 vd (.bits w) (.copy w vs)
          | _ => LiftedStmt.def1 vd (.bits w) (.copy w vs)
        pure ([stmt], st2)
      | none => throw s!"mov_uninit {repr rs}"
    | .mov (.reg (.low rd _)) (.imm (.int64 c)) =>
      let (vd, st1) := freshVar cur (some rd)
      pure ([.def1 vd (.bits w) (.movi w c.toBitVec)], setVarTy vd (.bits w) (setRegVar rd vd st1))
    | .mov (.reg (.low rd _)) (.regOrMem (.mem a)) =>
      if isRspAddr a then throw "spill_in_body: stack slot load"
      let (va, asts, st1) ← emitAddrCalc a cur
      let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
      let (vd, st2) := freshVar (addElides evs st1) (some rd)
      pure (asts ++ [.def1 vd (.bits w) (.load w va)], setVarTy vd (.bits w) (setRegVar rd vd st2))
    | .mov (.mem a) (.regOrMem (.reg (.low rs _))) =>
      if isRspAddr a then throw "spill_in_body: stack slot store"
      let vs ← match getRegVar? rs cur with
        | some v => pure v | none => throw s!"store_uninit {repr rs}"
      let (va, asts, st1) ← emitAddrCalc a cur
      let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
      pure (asts ++ [.def1 0 (.bits w) (.store w vs va)], addElides evs st1)
    | .mov (.mem a) (.imm (.int64 c)) =>
      if isRspAddr a then throw "spill_in_body: stack slot store imm"
      let (va, asts, st1) ← emitAddrCalc a cur
      let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
      let (vc, st2) := freshVar (addElides evs st1) none
      pure (asts ++ [.def1 vc (.bits w) (.movi w c.toBitVec), .def1 0 (.bits w) (.store w vc va)],
            st2)
    | .movzx (.reg (.low rd _)) src => liftExt ow false rd src cur
    | .movsx (.reg (.low rd _)) src => liftExt ow true rd src cur
    | .lea (.low rd _) a =>
      let (va, asts, st1) ← emitAddrCalc a cur
      if asts.isEmpty then
        let (vd, s2) := freshVarTy st1 (some rd) (.bits w)
        pure ([.def1 vd (.bits w) (.copy w va)], setRegVar rd vd s2)
      else
        pure (asts, setRegVar rd va
          { st1 with softRegs := (va, rd) :: st1.softRegs,
                     varTys := (va, .bits w) :: st1.varTys })
    | .add (.reg (.low rd _)) rhs => liftRmwBin "add" true true true rd rhs cur
    | .sub (.reg (.low rd _)) rhs => liftRmwBin "sub" true true true rd rhs cur
    | .and (.reg (.low rd _)) rhs => liftRmwBin "and" true false false rd rhs cur
    | .or (.reg (.low rd _)) rhs => liftRmwBin "or" true false false rd rhs cur
    | .imul none (.reg (.low rd _)) rhs => liftRmwBin "mul" false false false rd rhs cur
    | .xor (.reg (.low rd _)) rhs =>
      match rhs with
      | .regOrMem (.reg (.low rs _)) =>
        if rd == rs then
          let (vd, st1) := freshVarTy cur (some rd) (.bits w)
          pure ([.def1 vd (.bits w) (.movi w 0#64)],
                { setRegVar rd vd st1 with
                  lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := false })
        else liftRmwBin "xor" true false false rd rhs cur
      | _ => liftRmwBin "xor" true false false rd rhs cur
    | .mul (.reg (.low rs _)) =>
      let va ← match getRegVar? .rax cur with
        | some v => pure v | none => throw "mul_rax_uninit"
      let vb ← match getRegVar? rs cur with
        | some v => pure v | none => throw "mul_rhs_uninit"
      let (vlo, st1) := freshVarTy cur (some .rax) (.bits w)
      let (vhi, st2) := freshVarTy st1 (some .rdx) (.bits w)
      pure ([.def2 vlo vhi (.bits w) (.bits w) (.umulw w va vb)],
            { setRegVar .rdx vhi (setRegVar .rax vlo st2) with
              lastCmp? := none, lastCmpEqNe := false })
    | .inc (.reg (.low rd _)) =>
      let va ← match getRegVar? rd cur with | some v => pure v | none => throw "inc_uninit"
      let (vd, st1) := freshVarTy cur (some rd) (.bits w)
      let st2 := setRegVar rd vd (addClique [va, vd] st1)
      pure ([.def1 vd (.bits w) (.bin w "add" va none (some 1#64))],
            { st2 with varHints := (vd, .decInc) :: st2.varHints,
                       lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := true })
    | .dec (.reg (.low rd _)) =>
      let va ← match getRegVar? rd cur with | some v => pure v | none => throw "dec_uninit"
      let (vd, st1) := freshVarTy cur (some rd) (.bits w)
      let st2 := setRegVar rd vd (addClique [va, vd] st1)
      pure ([.def1 vd (.bits w) (.bin w "sub" va none (some 1#64))],
            { st2 with varHints := (vd, .decInc) :: st2.varHints,
                       lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := true })
    | .neg (.reg (.low rd _)) =>
      let va ← match getRegVar? rd cur with | some v => pure v | none => throw "neg_uninit"
      let (vd, st1) := freshVarTy cur (some rd) (.bits w)
      pure ([.def1 vd (.bits w) (.un w "neg" va)],
            { setRegVar rd vd (addClique [va, vd] st1) with
              lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := true })
    | .not (.reg (.low rd _)) =>
      let va ← match getRegVar? rd cur with | some v => pure v | none => throw "not_uninit"
      let (vd, st1) := freshVarTy cur (some rd) (.bits w)
      pure ([.def1 vd (.bits w) (.un w "not" va)], setRegVar rd vd (addClique [va, vd] st1))
    | .shl (.reg (.low rd _)) sc => liftShift "shl" true w rd sc cur
    | .shr (.reg (.low rd _)) sc => liftShift "lshr" true w rd sc cur
    | .sar (.reg (.low rd _)) sc => liftShift "ashr" false w rd sc cur
    | .cmp lhs rhs =>
      let (la, pre, st1) ← match lhs with
        | .reg (.low ra _) =>
          let va ← match getRegVar? ra cur with
            | some v => pure v | none => throw s!"cmp_uninit {repr ra}"
          pure (va, [], cur)
        | .mem a =>
          if isRspAddr a then throw "spill_in_body: cmp slot"
          let (vaddr, asts, s1) ← emitAddrCalc a cur
          let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
          let (vld, s2) := freshVarTy (addElides evs s1) none (.bits w)
          pure (vld, asts ++ [.def1 vld (.bits w) (.load w vaddr)], s2)
        | _ => throw "cmp_high_byte"
      match rhs with
      | .regOrMem (.reg (.low rb _)) =>
        let vb ← match getRegVar? rb st1 with | some v => pure v | none => throw "cmp_rhs_uninit"
        pure (pre, { st1 with lastCmp? := some (la, some vb, none, w), lastCmpEqNe := false })
      | .imm (.int64 c) =>
        pure (pre, { st1 with lastCmp? := some (la, none, some c.toBitVec, w),
                              lastCmpEqNe := false })
      | _ => throw "unsupported_cmp_mem"
    | .test (.reg (.low ra _)) (.regOrMem (.reg (.low rb _))) =>
      let va ← match getRegVar? ra cur with
        | some v => pure v | none => throw s!"test_uninit {repr ra}"
      if ra == rb then
        pure ([], { cur with lastCmp? := some (va, none, some 0#64, w), lastCmpEqNe := false })
      else
        let vb ← match getRegVar? rb cur with
          | some v => pure v | none => throw "test_rhs_uninit"
        let (vt, st1) := freshVarTy cur none (.bits w)
        pure ([.def1 vt (.bits w) (.bin w "and" va (some vb) none)],
              { st1 with lastCmp? := some (vt, none, some 0#64, w), lastCmpEqNe := false })
    | .test (.reg (.low ra _)) (.imm (.int64 c)) =>
      let va ← match getRegVar? ra cur with
        | some v => pure v | none => throw "test_imm_uninit"
      let (vt, st1) := freshVarTy cur none (.bits w)
      pure ([.def1 vt (.bits w) (.bin w "and" va none (some c.toBitVec))],
            { st1 with lastCmp? := some (vt, none, some 0#64, w), lastCmpEqNe := false })
    | .test (.mem a) (.imm (.int64 c)) =>
      if isRspAddr a then throw "spill_in_body: test slot"
      let (vaddr, asts, st1) ← emitAddrCalc a cur
      let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
      let (vld, st2) := freshVarTy (addElides evs st1) none (.bits w)
      let (vt, st3) := freshVarTy st2 none (.bits w)
      pure (asts ++ [.def1 vld (.bits w) (.load w vaddr),
                     .def1 vt (.bits w) (.bin w "and" vld none (some c.toBitVec))],
            { st3 with lastCmp? := some (vt, none, some 0#64, w), lastCmpEqNe := false })
    | .setcc cc (.reg (.low rd _)) =>
      let (vc, cst, st2) ← resolveX64Flag "setcc" cc cur
      let (vd, st3) := freshVarTy st2 (some rd) (.bits 8)
      pure ([cst, LiftedStmt.def1 vd (.bits 8) (.ofBool 8 vc)], setRegVar rd vd st3)
    | .cmovcc cc (.low rd _) (.reg (.low rs _)) =>
      let vb ← match getRegVar? rd cur with | some v => pure v | none => throw "cmov_dst_uninit"
      let va ← match getRegVar? rs cur with | some v => pure v | none => throw "cmov_src_uninit"
      let (vc, cst, st2) ← resolveX64Flag "cmovcc" cc cur
      let (vd, st3) := freshVarTy st2 (some rd) (.bits w)
      pure ([cst, LiftedStmt.def1 vd (.bits w) (.select w vc va vb)],
            setRegVar rd vd (addClique [vb, vd] st3))
    | .adc (.reg (.low rd _)) rhs =>
      let va ← match getRegVar? rd cur with | some v => pure v | none => throw "adc_uninit"
      let (vd, st1) := freshVarTy cur (some rd) (.bits w)
      let (vc, st2) := freshVarTy st1 none .bool
      let st3 := setRegVar rd vd (addClique [va, vd]
        { st2 with flags := (vc, .c) :: st2.flags, lastCarry? := some vc,
                   lastCmp? := none, lastCmpEqNe := false })
      let (rhs1, rhs2) ← match rhs with
        | .regOrMem (.reg (.low rs _)) =>
          let vb ← match getRegVar? rs cur with
            | some v => pure v | none => throw "adc_rhs_uninit"
          pure (some vb, none)
        | .imm (.int64 c) => pure (none, some c.toBitVec)
        | _ => throw "adc_mem"
      pure ([.def2 vd vc (.bits w) .bool (.addc w va rhs1 rhs2 cur.lastCarry? false)], st3)
    | .adcx (.low rd _) (.reg (.low rs _)) => liftAdcxAdox .adcx .c w rd rs cur
    | .adox (.low rd _) (.reg (.low rs _)) => liftAdcxAdox .adox .o w rd rs cur
    | _ => throw s!"unsupported_instr: {ATT.instr ins}"
  | .avx _ _ _ => throw "unsupported_avx"

def liftInstrs (insns : List Instr) (st : LiftBlockSt) :
    Except String (List LiftedStmt × LiftBlockSt) := do
  let mut cur := st
  let mut out : List LiftedStmt := []
  for ins in insns do
    let (sts, cur') ← liftOneInstr ins cur
    out := out ++ sts
    cur := cur'
  pure (out, cur)

def addrRegs (a : AddrExpr) : List Reg64 :=
  (match a.base with | some (.reg r) => [r] | _ => []) ++
  (match a.idx with | some ⟨r, _⟩ => [r] | none => [])

def opRegs {w : Width} : Operand w → List Reg64
  | .regOrMem (.reg (.low r _)) => [r]
  | .regOrMem (.mem a) => addrRegs a
  | .regOrMem (.reg _) => []
  | .imm _ => []

def instrRegsReadWritten : Instr → List Reg64 × List Reg64
  | .regular _ _ op =>
    match op with
    | .mov (.reg (.low rd _)) (.regOrMem (.reg (.low rs _))) => ([rs], [rd])
    | .mov (.reg (.low rd _)) (.imm _) => ([], [rd])
    | .mov (.reg (.low rd _)) (.regOrMem (.mem a)) => (addrRegs a, [rd])
    | .mov (.mem a) (.regOrMem (.reg (.low rs _))) => (rs :: addrRegs a, [])
    | .mov (.mem a) (.imm _) => (addrRegs a, [])
    | .movzx (.reg (.low rd _)) (.reg (.low rs _)) => ([rs], [rd])
    | .movzx (.reg (.low rd _)) (.mem a) => (addrRegs a, [rd])
    | .movsx (.reg (.low rd _)) (.reg (.low rs _)) => ([rs], [rd])
    | .movsx (.reg (.low rd _)) (.mem a) => (addrRegs a, [rd])
    | .lea (.low rd _) a => (addrRegs a, [rd])
    | .add (.reg (.low rd _)) rhs | .sub (.reg (.low rd _)) rhs
    | .and (.reg (.low rd _)) rhs | .or (.reg (.low rd _)) rhs
    | .imul none (.reg (.low rd _)) rhs => (rd :: opRegs rhs, [rd])
    | .mul (.reg (.low rs _)) => ([.rax, rs], [.rax, .rdx])
    | .xor (.reg (.low rd _)) (.regOrMem (.reg (.low rs _))) =>
      if rd == rs then ([], [rd]) else ([rd, rs], [rd])
    | .xor (.reg (.low rd _)) rhs => (rd :: opRegs rhs, [rd])
    | .inc (.reg (.low rd _)) | .dec (.reg (.low rd _))
    | .neg (.reg (.low rd _)) | .not (.reg (.low rd _)) => ([rd], [rd])
    | .shl (.reg (.low rd _)) .cl | .shr (.reg (.low rd _)) .cl | .sar (.reg (.low rd _)) .cl =>
      ([rd, .rcx], [rd])
    | .shl (.reg (.low rd _)) _ | .shr (.reg (.low rd _)) _ | .sar (.reg (.low rd _)) _ =>
      ([rd], [rd])
    | .cmp (.reg (.low ra _)) rhs => (ra :: opRegs rhs, [])
    | .cmp (.mem a) rhs => (addrRegs a ++ opRegs rhs, [])
    | .test (.reg (.low ra _)) rhs => (ra :: opRegs rhs, [])
    | .test (.mem a) rhs => (addrRegs a ++ opRegs rhs, [])
    | .setcc _ (.reg (.low rd _)) => ([], [rd])
    | .cmovcc _ (.low rd _) (.reg (.low rs _)) => ([rd, rs], [rd])
    | .cmovcc _ (.low rd _) (.mem a) => (rd :: addrRegs a, [rd])
    | .adc (.reg (.low rd _)) rhs => (rd :: opRegs rhs, [rd])
    | .adcx (.low rd _) (.reg (.low rs _))
    | .adox (.low rd _) (.reg (.low rs _)) => ([rd, rs], [rd])
    | _ => ([], [])
  | _ => ([], [])

def computeLiveInRegs (blocks : List CfgBlock) (retRegs : List Reg64) :
    List (String × List Reg64) :=
  computeLiveInRegsGen (fun _ => []) instrRegsReadWritten (fun _ => false) blocks retRegs

def x64LowerJcc (cc : CondCode) (stAfter : LiftBlockSt) :
    Except String (List LiftedStmt × Nat × LiftBlockSt) := do
  let (vc, cst, s1) ← resolveX64Flag "jcc" cc stAfter false
  pure ([cst], vc, s1)

def x64LiftHooks : LiftHooks x64Isa XDir Reg64 Instr CondCode :=
  { preCheck := fun dirs =>
      if !dirs.all (fun | .instr (.avx _ _ _) => false | _ => true) then
        throw "avx_unsupported"
      else pure ()
    stripFrame := fun dirs => stripPrologueEpilogue dirs
    toCfg := fun d s => toCfgBlocks d s
    argLiveRegs := fun n => x64Frame.argRegs.take n
    retLiveRegs := fun n => x64Frame.retRegs.take n
    toIsaReg := id
    instrRW := instrRegsReadWritten
    reprLR := fun r => toString (repr r)
    liftBlock := fun b st => liftInstrs b.instrs st
    lowerJcc := x64LowerJcc }

/-- Lift x86-64 directives into a `LiftedSnippet Reg64 CondCode rs` plus mapped `RelHints`. -/
def liftSnippetU (name : Sym) (as rs : List Ty) (dirs : List XDir) :
    Except String (LiftedSnippet Reg64 CondCode rs) :=
  liftSnippetUGen x64LiftHooks name as rs dirs

/-- Output of end-to-end `liftSnippet` including solved hints, standalone lowered code, and
self round-trip `AsmIso` verdict (`LiftResultX64.fn` projects the `Fn`). -/
abbrev LiftResultX64 := LiftResult x64Isa

/-- Materialize the `Fn` of a `LiftResultX64`. -/
def LiftResultX64.fn (r : LiftResultX64) : Fn := LiftResult.fn r

/-- Full untrusted x86-64 directive lifting + `solveRelHints` + standalone `Rega.lowerFn` +
`checkAsmIso` round-trip check. -/
def liftSnippet (name : Sym) (as rs : List Ty) (dirs : List XDir)
    (avoidRegs : List Reg64 := []) : Except String LiftResultX64 :=
  liftSnippetGen x64LiftHooks (fun a b s p => checkAsmIso a b s p)
    name as rs dirs avoidRegs

/-- Parse AT&T x86-64 assembly text and lift via `liftSnippet` (`IO` convenience wrapper). -/
def liftSnippetAsm (name : Sym) (as rs : List Ty) (asmText : String)
    (avoidRegs : List Reg64 := []) : IO (Except String LiftResultX64) := do
  let dirs ← Kraken.X64.Parser.parse asmText
  pure (liftSnippet name as rs dirs avoidRegs)

/-- Combined `Rega.lowerFn` + `@predictable` static `SnippetBudget` audit on x86-64. -/
def checkRegaAndBudget (sDirect outerLate : Fn) (hOuter : x64Isa.Hints)
    (budget : SnippetBudget := {}) : Except (List SnippetDiag) (List XDir × BudgetReport) :=
  lowerAndCheckBudget x64Isa sDirect outerLate hOuter budget
    (some fun ds => (profileDirs ds true).bodyInsns)

end LeanQbe.T.Amd64
