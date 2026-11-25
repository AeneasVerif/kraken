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
  `LiftedSnippet Reg64 CondCode rs` -> solved `x64Isa.Hints` + lowered fixpoint check + `IsoVerdict`).
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
  | .regular _ _ (.mov (.reg _) (.mem a)) => isRspAddr a
  | .regular _ _ (.mov (.mem a) _) => isRspAddr a
  | .regular _ _ (.movzx (.reg _) (.mem a)) => isRspAddr a
  | .regular _ _ (.movsx (.reg _) (.mem a)) => isRspAddr a
  | .regular _ _ (.cmp (.mem a) _) => isRspAddr a
  | .regular _ _ (.test (.mem a) _) => isRspAddr a
  | .regular _ _ (.add (.reg _) (.regOrMem (.mem a))) => isRspAddr a
  | .regular _ _ (.sub (.reg _) (.regOrMem (.mem a))) => isRspAddr a
  | .regular _ _ (.and (.reg _) (.regOrMem (.mem a))) => isRspAddr a
  | .regular _ _ (.or (.reg _) (.regOrMem (.mem a))) => isRspAddr a
  | .regular _ _ (.xor (.reg _) (.regOrMem (.mem a))) => isRspAddr a
  | _ => false

def isEpilogueInstr : Instr → Bool
  | .regular _ .W64 (.add (.reg (.low .rsp .W64)) (.imm _)) => true
  | .regular _ .W64 (.pop _) => true
  | .regular _ .W64 (.mov (.reg (.low r .W64)) (.mem a)) =>
    isRspAddr a && x64Frame.calleeSaved.contains r
  | _ => false

def stripPrologueEpilogue (ds : List XDir) : List XDir × Nat × List Reg64 :=
  let ds0 := stripNops ds
  let ds1 := match ds0 with
    | .label l :: rest => if !isLocalLabel l then rest else ds0
    | _ => ds0
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
  let (ds2, frameSz, saved) := peelPro [] 0 ds1
  let rec peelEpiRev : List XDir → List XDir
    | .instr i :: rest =>
      if isEpilogueInstr i then peelEpiRev rest else .instr i :: rest
    | other => other
  let rec stripBeforeRet : List XDir → List XDir → List XDir
    | [], acc => acc.reverse
    | .instr (.regular aw ow .ret) :: rest, acc =>
      let acc' := peelEpiRev acc
      stripBeforeRet rest (.instr (.regular aw ow .ret) :: acc')
    | d :: rest, acc => stripBeforeRet rest (d :: acc)
  (stripBeforeRet ds2 [], frameSz, saved)

/-- Profile x86-64 directives into target-generic `BudgetMetrics`. -/
def profileDirs (ds : List XDir) (stripFrame : Bool := true) : BudgetMetrics :=
  let allInsns := (stripNops ds).filterMap fun | .instr i => some i | _ => none
  let body := if stripFrame then (stripPrologueEpilogue ds).1 else stripNops ds
  let bodyIns := body.filterMap fun | .instr i => some i | _ => none
  let rec countBody (prevSetcc : Bool) : List Instr → BudgetMetrics → BudgetMetrics
    | [], m => m
    | i :: rest, m =>
      let m := { m with bodyInsns := m.bodyInsns + 1 }
      let m := if isBodySpillInstr i then { m with spills := m.spills + 1 } else m
      let (m, isSetcc) := match i with
        | .regular _ _ (.mov (.reg _) (.regOrMem (.reg _))) =>
          ({ m with regMoves := m.regMoves + 1 }, false)
        | .regular _ _ (.movzx (.reg _) (.reg _)) =>
          ({ m with boolChains := m.boolChains + (if prevSetcc then 1 else 0),
                    regMoves := m.regMoves + 1 }, false)
        | .regular _ _ (.setcc _ _) => (m, true)
        | .regular _ _ (.cmovcc _ _ _) => ({ m with selectOps := m.selectOps + 1 }, false)
        | .regular _ _ (.cmp _ _) | .regular _ _ (.test _ _) =>
          ({ m with cmpsTests := m.cmpsTests + 1 }, false)
        | .regular _ _ (.jcc _ _) => ({ m with branches := m.branches + 1 }, false)
        | .regular _ _ (.jmp _) => ({ m with jmps := m.jmps + 1 }, false)
        | .regular _ _ (.lea _ _) => ({ m with leas := m.leas + 1 }, false)
        | .regular _ _ (.call _) => ({ m with calls := m.calls + 1 }, false)
        | _ => (m, false)
      countBody isSetcc rest m
  let bm := countBody false bodyIns {}
  { bm with totalInsns := allInsns.length }

/-! ## 2. `AsmIso` (Tier 1 & Tier 2) CFG Alpha-Isomorphism Checker -/

structure CfgBlock where
  label  : String
  instrs : List Instr
  term   : CfgTerm CondCode
  deriving Repr, Inhabited

def toCfgBlocks (ds : List XDir) (stripFrame : Bool := true) : List CfgBlock :=
  let body := if stripFrame then (stripPrologueEpilogue ds).1 else stripNops ds
  let rec splitRaw (curLbl : String) (curIns : List Instr) (idx : Nat) (justClosed : Bool) :
      List XDir → List (String × List Instr)
    | [] => if justClosed && curIns.isEmpty then [] else [(curLbl, curIns.reverse)]
    | .label l :: rest =>
      if curIns.isEmpty && (justClosed || (curLbl == "__entry" && idx == 0)) then
        splitRaw l [] (idx + 1) false rest
      else
        (curLbl, curIns.reverse) :: splitRaw l [] (idx + 1) false rest
    | .instr i :: rest =>
      let isTerm : Bool := match i with
        | .regular _ _ .ret | .regular _ _ (.jmp _) | .regular _ _ (.jcc _ _) => true
        | _ => false
      if isTerm then
        let blk := (curLbl, (i :: curIns).reverse)
        match rest with
        | [] => [blk]
        | .label _ :: _ => blk :: splitRaw "__closed" [] (idx + 1) true rest
        | _ => blk :: splitRaw s!"__fall_{idx}" [] (idx + 1) false rest
      else
        splitRaw curLbl (i :: curIns) (idx + 1) false rest
    | _ :: rest => splitRaw curLbl curIns (idx + 1) justClosed rest
  let raw0 := splitRaw "__entry" [] 0 false body
  let raw := match raw0.reverse with
    | (l, ins) :: rest =>
      if raw0.length > 1 && l == "__entry" && ins.isEmpty then rest.reverse else raw0
    | [] => []
  let rec finalize : List (String × List Instr) → List CfgBlock
    | [] => []
    | (lbl, ins) :: rest =>
      let nextLbl? := rest.head?.map Prod.fst
      let (core, term) : List Instr × CfgTerm CondCode := match ins.reverse with
        | .regular _ _ .ret :: revPre => (revPre.reverse, .ret)
        | .regular _ _ (.jmp (.rel (.label t))) :: revPre => (revPre.reverse, .jmp t)
        | .regular _ _ (.jmp (.rel (.sub (.label t) .after_current_instruction))) :: revPre =>
          (revPre.reverse, .jmp t)
        | .regular _ _ (.jmp (.rel t)) :: revPre => (revPre.reverse, .exit (toString (repr t)))
        | .regular _ _ (.jcc cc tgt) :: revPre =>
          match nextLbl? with
          | some nxt => (revPre.reverse, .jcc cc tgt nxt)
          | none => (revPre.reverse, .jcc cc tgt "__end")
        | _ =>
          match nextLbl? with
          | some nxt => (ins, .fall nxt)
          | none => (ins, .endMark)
      let (core', term') : List Instr × CfgTerm CondCode := match term with
        | .jmp fallLbl =>
          match core.reverse with
          | .regular _ _ (.jcc cc tgt) :: revPre2 => (revPre2.reverse, .jcc cc tgt fallLbl)
          | _ => (core, term)
        | _ => (core, term)
      { label := lbl, instrs := core', term := term' } :: finalize rest
  let bs0 := finalize raw
  let lbls := bs0.map (·.label)
  bs0.map fun b =>
    match b.term with
    | .jmp t => if lbls.contains t then b else { b with term := .exit t }
    | _ => b

structure IsoState where
  regMap     : List (Reg64 × Reg64) := [(.rsp, .rsp)]
  lblMap     : List (String × String) := []
  slotMap    : List (Int64 × Int64) := []
  visited    : List (String × String) := []
  tier2Notes : List String := []
  deriving Repr

def matchReg64 (fixedRegs : List Reg64) (r1 r2 : Reg64) (st : IsoState) : Option IsoState :=
  if fixedRegs.contains r1 || fixedRegs.contains r2 then
    if r1 == r2 then some st else none
  else
    (bindBijection r1 r2 st.regMap).map fun rm => { st with regMap := rm }

def matchReg {w : Width} (fixed : List Reg64) (r1 r2 : Reg w) (st : IsoState) :
    Option IsoState :=
  match r1, r2 with
  | .low a _, .low b _ => matchReg64 fixed a b st
  | .ah, .ah | .bh, .bh | .ch, .ch | .dh, .dh => some st
  | _, _ => none

def matchConstExpr (c1 c2 : ConstExpr) (st : IsoState) : Option IsoState :=
  if c1 == c2 then some st
  else match c1, c2 with
    | .label l1, .label l2 => (bindBijection l1 l2 st.lblMap).map fun lm => { st with lblMap := lm }
    | _, _ => none

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
  match op1, op2 with
  | .mov d1 s1, .mov d2 s2 => matchRegOrMem fixed d1 d2 st >>= matchOperand fixed s1 s2
  | .movzx (w' := w1) d1 s1, .movzx (w' := w2) d2 s2 =>
    if h : w1 = w2 then matchRegOrMem fixed d1 d2 st >>= matchRegOrMem fixed s1 (h ▸ s2) else none
  | .movsx (w' := w1) d1 s1, .movsx (w' := w2) d2 s2 =>
    if h : w1 = w2 then matchRegOrMem fixed d1 d2 st >>= matchRegOrMem fixed s1 (h ▸ s2) else none
  | .setcc c1 d1, .setcc c2 d2 => if c1 == c2 then matchRegOrMem fixed d1 d2 st else none
  | .cmovcc c1 d1 s1, .cmovcc c2 d2 s2 =>
    if c1 == c2 then matchReg fixed d1 d2 st >>= matchRegOrMem fixed s1 s2 else none
  | .lea d1 a1, .lea d2 a2 => matchReg fixed d1 d2 st >>= matchAddr fixed a1 a2
  | .add d1 s1, .add d2 s2 => matchRegOrMem fixed d1 d2 st >>= matchOperand fixed s1 s2
  | .adc d1 s1, .adc d2 s2 => matchRegOrMem fixed d1 d2 st >>= matchOperand fixed s1 s2
  | .adcx d1 s1, .adcx d2 s2 => matchReg fixed d1 d2 st >>= matchRegOrMem fixed s1 s2
  | .adox d1 s1, .adox d2 s2 => matchReg fixed d1 d2 st >>= matchRegOrMem fixed s1 s2
  | .inc d1, .inc d2 => matchRegOrMem fixed d1 d2 st
  | .dec d1, .dec d2 => matchRegOrMem fixed d1 d2 st
  | .neg d1, .neg d2 => matchRegOrMem fixed d1 d2 st
  | .sub d1 s1, .sub d2 s2 => matchRegOrMem fixed d1 d2 st >>= matchOperand fixed s1 s2
  | .sbb d1 s1, .sbb d2 s2 => matchRegOrMem fixed d1 d2 st >>= matchOperand fixed s1 s2
  | .cmp a1 b1, .cmp a2 b2 => matchRegOrMem fixed a1 a2 st >>= matchOperand fixed b1 b2
  | .mul s1, .mul s2 => matchRegOrMem fixed s1 s2 st
  | .mulx hi1 lo1 s1, .mulx hi2 lo2 s2 =>
    matchReg fixed hi1 hi2 st >>= matchReg fixed lo1 lo2 >>= matchRegOrMem fixed s1 s2
  | .imul1 s1, .imul1 s2 => matchRegOrMem fixed s1 s2 st
  | .imul d1 a1 b1, .imul d2 a2 b2 => do
    let st ← match d1, d2 with
      | some r1, some r2 => matchRegOrMem fixed r1 r2 st
      | none, none => some st
      | _, _ => none
    matchRegOrMem fixed a1 a2 st >>= matchOperand fixed b1 b2
  | .div s1, .div s2 => matchRegOrMem fixed s1 s2 st
  | .idiv s1, .idiv s2 => matchRegOrMem fixed s1 s2 st
  | .test a1 b1, .test a2 b2 => matchRegOrMem fixed a1 a2 st >>= matchOperand fixed b1 b2
  | .and d1 s1, .and d2 s2 => matchRegOrMem fixed d1 d2 st >>= matchOperand fixed s1 s2
  | .not d1, .not d2 => matchRegOrMem fixed d1 d2 st
  | .or d1 s1, .or d2 s2 => matchRegOrMem fixed d1 d2 st >>= matchOperand fixed s1 s2
  | .xor d1 s1, .xor d2 s2 => matchRegOrMem fixed d1 d2 st >>= matchOperand fixed s1 s2
  | .shl d1 c1, .shl d2 c2 => matchRegOrMem fixed d1 d2 st >>= matchShiftCount c1 c2
  | .shr d1 c1, .shr d2 c2 => matchRegOrMem fixed d1 d2 st >>= matchShiftCount c1 c2
  | .sar d1 c1, .sar d2 c2 => matchRegOrMem fixed d1 d2 st >>= matchShiftCount c1 c2
  | .rol d1 c1, .rol d2 c2 => matchRegOrMem fixed d1 d2 st >>= matchShiftCount c1 c2
  | .ror d1 c1, .ror d2 c2 => matchRegOrMem fixed d1 d2 st >>= matchShiftCount c1 c2
  | .shld d1 x1 c1, .shld d2 x2 c2 =>
    matchRegOrMem fixed d1 d2 st >>= matchReg fixed x1 x2 >>= matchShiftCount c1 c2
  | .shrd d1 x1 c1, .shrd d2 x2 c2 =>
    matchRegOrMem fixed d1 d2 st >>= matchReg fixed x1 x2 >>= matchShiftCount c1 c2
  | .shlx d1 a1 b1, .shlx d2 a2 b2 =>
    matchReg fixed d1 d2 st >>= matchRegOrMem fixed a1 a2 >>= matchReg fixed b1 b2
  | .shrx d1 a1 b1, .shrx d2 a2 b2 =>
    matchReg fixed d1 d2 st >>= matchRegOrMem fixed a1 a2 >>= matchReg fixed b1 b2
  | .sarx d1 a1 b1, .sarx d2 a2 b2 =>
    matchReg fixed d1 d2 st >>= matchRegOrMem fixed a1 a2 >>= matchReg fixed b1 b2
  | .rorx d1 a1 c1, .rorx d2 a2 c2 =>
    matchReg fixed d1 d2 st >>= matchRegOrMem fixed a1 a2 >>= matchConstExpr c1 c2
  | .bswap d1, .bswap d2 => matchReg fixed d1 d2 st
  | .lzcnt d1 s1, .lzcnt d2 s2 => matchReg fixed d1 d2 st >>= matchRegOrMem fixed s1 s2
  | .tzcnt d1 s1, .tzcnt d2 s2 => matchReg fixed d1 d2 st >>= matchRegOrMem fixed s1 s2
  | .popcnt d1 s1, .popcnt d2 s2 => matchReg fixed d1 d2 st >>= matchRegOrMem fixed s1 s2
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

def matchSeq (tier2 : Bool) (fixed : List Reg64) :
    List Instr → List Instr → IsoState → Option IsoState
  | [], [], st => some st
  | i1 :: r1, i2 :: r2, st =>
    (matchInstr fixed i1 i2 st >>= matchSeq tier2 fixed r1 r2) <|>
    if !tier2 then none
    else
      match i1, i2 with
      | .regular _ .W32 (.xor (.reg (.low a .W32)) (.regOrMem (.reg (.low b .W32)))),
        .regular _ _ (.mov (.reg (.low c _)) (.imm (.int64 0))) =>
        if a == b then
          (matchReg64 fixed a c st).bind fun st' =>
            matchSeq tier2 fixed r1 r2 { st' with tier2Notes := "xor0~mov0" :: st'.tier2Notes }
        else none
      | .regular _ _ (.mov (.reg (.low c _)) (.imm (.int64 0))),
        .regular _ .W32 (.xor (.reg (.low a .W32)) (.regOrMem (.reg (.low b .W32)))) =>
        if a == b then
          (matchReg64 fixed c a st).bind fun st' =>
            matchSeq tier2 fixed r1 r2 { st' with tier2Notes := "mov0~xor0" :: st'.tier2Notes }
        else none
      | .regular _ w1 (.inc d1), .regular _ w2 (.add d2 (.imm (.int64 1))) =>
        if h : w1 = w2 then
          (matchRegOrMem fixed d1 (h ▸ d2) st).bind fun st' =>
            matchSeq tier2 fixed r1 r2 { st' with tier2Notes := "inc~add1" :: st'.tier2Notes }
        else none
      | .regular _ w1 (.add d1 (.imm (.int64 1))), .regular _ w2 (.inc d2) =>
        if h : w1 = w2 then
          (matchRegOrMem fixed d1 (h ▸ d2) st).bind fun st' =>
            matchSeq tier2 fixed r1 r2 { st' with tier2Notes := "add1~inc" :: st'.tier2Notes }
        else none
      | .regular _ w1 (.dec d1), .regular _ w2 (.sub d2 (.imm (.int64 1))) =>
        if h : w1 = w2 then
          (matchRegOrMem fixed d1 (h ▸ d2) st).bind fun st' =>
            matchSeq tier2 fixed r1 r2 { st' with tier2Notes := "dec~sub1" :: st'.tier2Notes }
        else none
      | .regular _ w1 (.sub d1 (.imm (.int64 1))), .regular _ w2 (.dec d2) =>
        if h : w1 = w2 then
          (matchRegOrMem fixed d1 (h ▸ d2) st).bind fun st' =>
            matchSeq tier2 fixed r1 r2 { st' with tier2Notes := "sub1~dec" :: st'.tier2Notes }
        else none
      | .regular _ w1 (.test (.reg ra) (.regOrMem (.reg rb))),
        .regular _ w2 (.cmp (.reg rc) (.imm (.int64 0))) =>
        if h : w1 = w2 then
          if ra == rb then
            (matchReg fixed ra (h ▸ rc) st).bind fun st' =>
              matchSeq tier2 fixed r1 r2 { st' with tier2Notes := "test~cmp0" :: st'.tier2Notes }
          else none
        else none
      | .regular _ w1 (.cmp (.reg rc) (.imm (.int64 0))),
        .regular _ w2 (.test (.reg ra) (.regOrMem (.reg rb))) =>
        if h : w1 = w2 then
          if ra == rb then
            (matchReg fixed rc (h ▸ ra) st).bind fun st' =>
              matchSeq tier2 fixed r1 r2 { st' with tier2Notes := "cmp0~test" :: st'.tier2Notes }
          else none
        else none
      | .regular _ .W64 (.mov (.reg (.low d1 .W64)) (.regOrMem (.reg (.low s1 .W64)))),
        .regular _ .W64 (.lea (.low rd2 .W64) a2) =>
        match r1 with
        | .regular _ .W64 (.add (.reg (.low d1b .W64)) (.regOrMem (.reg (.low s2 .W64)))) :: r1' =>
          if d1 == d1b && a2.idx.isSome && a2.disp == .int64 0 then
            match a2.base, a2.idx with
            | some (.reg rb2), some ⟨ri2, .W8⟩ =>
              (matchReg64 fixed d1 rd2 st >>= matchReg64 fixed s1 rb2 >>= matchReg64 fixed s2 ri2).bind
                fun st' => matchSeq tier2 fixed r1' r2
                  { st' with tier2Notes := "mov+add~lea" :: st'.tier2Notes }
            | _, _ => none
          else none
        | _ => none
      | .regular _ .W64 (.lea (.low rd1 .W64) a1),
        .regular _ .W64 (.mov (.reg (.low d2 .W64)) (.regOrMem (.reg (.low s2a .W64)))) =>
        match r2 with
        | .regular _ .W64 (.add (.reg (.low d2b .W64)) (.regOrMem (.reg (.low s2b .W64)))) :: r2' =>
          if d2 == d2b && a1.idx.isSome && a1.disp == .int64 0 then
            match a1.base, a1.idx with
            | some (.reg rb1), some ⟨ri1, .W8⟩ =>
              (matchReg64 fixed rd1 d2 st >>= matchReg64 fixed rb1 s2a >>= matchReg64 fixed ri1 s2b).bind
                fun st' => matchSeq tier2 fixed r1 r2'
                  { st' with tier2Notes := "lea~mov+add" :: st'.tier2Notes }
            | _, _ => none
          else none
        | _ => none
      | _, _ => none
  | _, _, _ => none

def classifyMismatch (ref cand : List CfgBlock) (refB candB : BudgetMetrics) :
    String × String :=
  if candB.spills > refB.spills then
    ("spill_in_body", s!"spills {refB.spills}->{candB.spills}, insns {refB.bodyInsns}->{candB.bodyInsns}")
  else if candB.selectOps > refB.selectOps && candB.branches < refB.branches then
    ("ifconv_cmov", s!"cmovs {refB.selectOps}->{candB.selectOps}, jccs {refB.branches}->{candB.branches}")
  else if candB.boolChains > refB.boolChains then
    ("bool_movzx_chain", s!"movzxBool {refB.boolChains}->{candB.boolChains}")
  else if candB.cmpsTests > refB.cmpsTests then
    ("extra_cmp_flag_miss", s!"cmpsTests {refB.cmpsTests}->{candB.cmpsTests}")
  else if candB.regMoves > refB.regMoves then
    ("extra_mov_copy", s!"regMoves {refB.regMoves}->{candB.regMoves}, insns {refB.bodyInsns}->{candB.bodyInsns}")
  else if candB.jmps > refB.jmps then
    ("extra_jmp_edge", s!"jmps {refB.jmps}->{candB.jmps}")
  else
    ("insn_or_cfg_diff", s!"blocks {ref.length}->{cand.length}, insns {refB.bodyInsns}->{candB.bodyInsns}")

partial def matchCfgFrom (tier2 : Bool) (fixed : List Reg64)
    (bs1 bs2 : List CfgBlock) (l1 l2 : String) (st : IsoState) : Option IsoState :=
  if st.visited.any (fun p => p.1 == l1 && p.2 == l2) then some st
  else do
    let lm ← bindBijection l1 l2 st.lblMap
    let b1 ← bs1.find? (·.label == l1)
    let b2 ← bs2.find? (·.label == l2)
    let st0 := { st with lblMap := lm, visited := (l1, l2) :: st.visited }
    let st1 ← matchSeq tier2 fixed b1.instrs b2.instrs st0
    match b1.term, b2.term with
    | .ret, .ret | .endMark, .endMark | .ret, .endMark | .endMark, .ret => some st1
    | .exit s1, .exit s2 => if s1 == s2 then some st1 else none
    | .jmp t1, .jmp t2 | .jmp t1, .fall t2 | .fall t1, .jmp t2 | .fall t1, .fall t2 =>
      matchCfgFrom tier2 fixed bs1 bs2 t1 t2 st1
    | .jcc cc1 t1 f1, .jcc cc2 t2 f2 =>
      if cc1 == cc2 then
        (matchCfgFrom tier2 fixed bs1 bs2 t1 t2 st1 >>= matchCfgFrom tier2 fixed bs1 bs2 f1 f2) <|>
        if x64NegCond cc1 == cc2 then
          matchCfgFrom tier2 fixed bs1 bs2 t1 f2 st1 >>= matchCfgFrom tier2 fixed bs1 bs2 f1 t2
        else none
      else if x64NegCond cc1 == cc2 then
        matchCfgFrom tier2 fixed bs1 bs2 t1 f2 st1 >>= matchCfgFrom tier2 fixed bs1 bs2 f1 t2
      else none
    | _, _ => none

/-- Compare two x86-64 directive streams for structural/register alpha-isomorphism (`AsmIso`). -/
def checkAsmIso (ref cand : List XDir) (stripFrame : Bool := true) (allowRegPerm : Bool := true) :
    IsoVerdict :=
  let bs1 := toCfgBlocks ref stripFrame
  let bs2 := toCfgBlocks cand stripFrame
  let bRef := profileDirs ref stripFrame
  let bCand := profileDirs cand stripFrame
  let fixed := if allowRegPerm then [.rsp] else x64Frame.allocatable ++ x64Frame.calleeSaved ++ [.rsp]
  match bs1.head?, bs2.head? with
  | some h1, some h2 =>
    match matchCfgFrom false fixed bs1 bs2 h1.label h2.label {} with
    | some _ => .tier1 bs1.length bRef.bodyInsns
    | none =>
      match matchCfgFrom true fixed bs1 bs2 h1.label h2.label {} with
      | some st => .tier2 bs1.length bRef.bodyInsns st.tier2Notes.length st.tier2Notes.reverse
      | none =>
        let (rsn, det) := classifyMismatch bs1 bs2 bRef bCand
        .fail rsn det
  | _, _ => .fail "empty_cfg" "missing entry block"

/-! ## 3. Untrusted x86-64 Lifter (`liftSnippetU`, `liftSnippet`) -/

def condToCmpOp : CondCode → Option CmpOp
  | .z => some .eq | .nz => some .ne
  | .c => some .ult | .be => some .ule
  | .a => some .ugt | .nc => some .uge
  | .l => some .slt | .le => some .sle
  | .g => some .sgt | .ge => some .sge
  | _ => none

structure LiftBlockSt where
  nextVar      : Nat := 0
  regVars      : List (Reg64 × Nat) := []
  varTys       : List (Nat × Ty) := []
  lastCmp?     : Option (Nat × Option Nat × Option (BitVec 64) × Nat) := none
  lastCmpEqNe  : Bool := false
  lastCarry?   : Option Nat := none
  cliques   : List (List Nat) := []
  flags     : List (Nat × CondCode) := []
  softRegs  : List (Nat × Reg64) := []
  varHints  : List (Nat × VariantHint) := []
  elideVars : List Nat := []
  deriving Repr

def widthBits : Width → Nat
  | .W8 => 8 | .W16 => 16 | .W32 => 32 | .W64 => 64

def freshVar (st : LiftBlockSt) (r? : Option Reg64) : Nat × LiftBlockSt :=
  let v := st.nextVar
  let sr := match r? with | some r => (v, r) :: st.softRegs | none => st.softRegs
  (v, { st with nextVar := v + 1, softRegs := sr })

def freshVarTy (st : LiftBlockSt) (r? : Option Reg64) (ty : Ty) : Nat × LiftBlockSt :=
  let v := st.nextVar
  let sr := match r? with | some r => (v, r) :: st.softRegs | none => st.softRegs
  (v, { st with nextVar := v + 1, softRegs := sr, varTys := (v, ty) :: st.varTys })

def setRegVar (r : Reg64) (v : Nat) (st : LiftBlockSt) : LiftBlockSt :=
  { st with regVars := (r, v) :: st.regVars.filter (fun p => p.1 != r) }

def getRegVar? (r : Reg64) (st : LiftBlockSt) : Option Nat :=
  (st.regVars.find? (fun p => p.1 == r)).map Prod.snd

def setVarTy (v : Nat) (t : Ty) (st : LiftBlockSt) : LiftBlockSt :=
  { st with varTys := (v, t) :: st.varTys }

def getVarTy? (v : Nat) (st : LiftBlockSt) : Option Ty :=
  (st.varTys.find? (·.1 == v)).map Prod.snd

def addElides (vs : List Nat) (st : LiftBlockSt) : LiftBlockSt :=
  { st with elideVars := vs ++ st.elideVars }

def addClique (vs : List Nat) (st : LiftBlockSt) : LiftBlockSt :=
  { st with cliques := vs :: st.cliques }

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

def liftInstrs (insns : List Instr) (st : LiftBlockSt) :
    Except String (List LiftedStmt × LiftBlockSt) := do
  let mut cur := st
  let mut out : List LiftedStmt := []
  for ins in insns do
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
          out := out ++ [stmt]
          cur := st2
        | none => throw s!"mov_uninit {repr rs}"
      | .mov (.reg (.low rd _)) (.imm (.int64 c)) =>
        let (vd, st1) := freshVar cur (some rd)
        let st2 := setVarTy vd (.bits w) (setRegVar rd vd st1)
        out := out ++ [.def1 vd (.bits w) (.movi w c.toBitVec)]
        cur := st2
      | .mov (.reg (.low rd _)) (.regOrMem (.mem a)) =>
        if isRspAddr a then throw "spill_in_body: stack slot load"
        let (va, asts, st1) ← emitAddrCalc a cur
        let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
        let (vd, st2) := freshVar (addElides evs st1) (some rd)
        let st3 := setVarTy vd (.bits w) (setRegVar rd vd st2)
        out := out ++ asts ++ [.def1 vd (.bits w) (.load w va)]
        cur := st3
      | .mov (.mem a) (.regOrMem (.reg (.low rs _))) =>
        if isRspAddr a then throw "spill_in_body: stack slot store"
        let vs ← match getRegVar? rs cur with
          | some v => pure v | none => throw s!"store_uninit {repr rs}"
        let (va, asts, st1) ← emitAddrCalc a cur
        let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
        out := out ++ asts ++ [.def1 0 (.bits w) (.store w vs va)]
        cur := addElides evs st1
      | .mov (.mem a) (.imm (.int64 c)) =>
        if isRspAddr a then throw "spill_in_body: stack slot store imm"
        let (va, asts, st1) ← emitAddrCalc a cur
        let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
        let (vc, st2) := freshVar (addElides evs st1) none
        out := out ++ asts ++ [.def1 vc (.bits w) (.movi w c.toBitVec), .def1 0 (.bits w) (.store w vc va)]
        cur := st2
      | .movzx (w' := ws) (.reg (.low rd _)) (.reg (.low rs _)) =>
        let vs ← match getRegVar? rs cur with
          | some v => pure v | none => throw s!"movzx_uninit {repr rs}"
        let (vd, st1) := freshVar cur (some rd)
        let st2 := setVarTy vd (.bits w) (setRegVar rd vd st1)
        out := out ++ [.def1 vd (.bits w) (.zext (widthBits ws) w vs)]
        cur := st2
      | .movzx (w' := ws) (.reg (.low rd _)) (.mem a) =>
        if isRspAddr a then throw "spill_in_body: movzx slot"
        let (va, asts, st1) ← emitAddrCalc a cur
        let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
        let (vl, st2) := freshVar (addElides evs st1) (some rd)
        let (vd, st3) := freshVar st2 (some rd)
        let st4 := setVarTy vd (.bits w) (setRegVar rd vd (addClique [vl, vd] st3))
        out := out ++ asts ++ [.def1 vl (.bits (widthBits ws)) (.load (widthBits ws) va),
                               .def1 vd (.bits w) (.zext (widthBits ws) w vl)]
        cur := st4
      | .movsx (w' := ws) (.reg (.low rd _)) (.reg (.low rs _)) =>
        let vs ← match getRegVar? rs cur with
          | some v => pure v | none => throw s!"movsx_uninit {repr rs}"
        let (vd, st1) := freshVar cur (some rd)
        let st2 := setVarTy vd (.bits w) (setRegVar rd vd st1)
        out := out ++ [.def1 vd (.bits w) (.sext (widthBits ws) w vs)]
        cur := st2
      | .movsx (w' := ws) (.reg (.low rd _)) (.mem a) =>
        if isRspAddr a then throw "spill_in_body: movsx slot"
        let (va, asts, st1) ← emitAddrCalc a cur
        let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
        let (vl, st2) := freshVar (addElides evs st1) (some rd)
        let (vd, st3) := freshVar st2 (some rd)
        let st4 := setVarTy vd (.bits w) (setRegVar rd vd (addClique [vl, vd] st3))
        out := out ++ asts ++ [.def1 vl (.bits (widthBits ws)) (.load (widthBits ws) va),
                               .def1 vd (.bits w) (.sext (widthBits ws) w vl)]
        cur := st4
      | .lea (.low rd _) a =>
        let (va, asts, st1) ← emitAddrCalc a cur
        let st2 ← if asts.isEmpty then
            let (vd, s2) := freshVarTy st1 (some rd) (.bits w)
            out := out ++ [.def1 vd (.bits w) (.copy w va)]
            pure (setRegVar rd vd s2)
          else
            let st1' := { st1 with softRegs := (va, rd) :: st1.softRegs,
                                   varTys := (va, .bits w) :: st1.varTys }
            out := out ++ asts
            pure (setRegVar rd va st1')
        cur := st2
      | .add (.reg (.low rd _)) rhs =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw s!"add_uninit {repr rd}"
        match rhs with
        | .regOrMem (.reg (.low rs _)) =>
          let vb ← match getRegVar? rs cur with
            | some v => pure v | none => throw s!"add_rhs_uninit {repr rs}"
          let (vd, st1) := freshVarTy cur (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st1) with
                   lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := true }
          out := out ++ [.def1 vd (.bits w) (.bin w "add" va (some vb) none)]
        | .imm (.int64 c) =>
          let (vd, st1) := freshVarTy cur (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st1) with
                   lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := true }
          out := out ++ [.def1 vd (.bits w) (.bin w "add" va none (some c.toBitVec))]
        | .regOrMem (.mem a) =>
          if isRspAddr a then throw "spill_in_body: add slot"
          let (vaddr, asts, st1) ← emitAddrCalc a cur
          let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
          let (vld, st2) := freshVarTy (addElides evs st1) (some rd) (.bits w)
          let (vd, st3) := freshVarTy st2 (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st3) with
                   lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := true }
          out := out ++ asts ++ [.def1 vld (.bits w) (.load w vaddr),
                                 .def1 vd (.bits w) (.bin w "add" va (some vld) none)]
        | _ => throw "add_high_byte"
      | .sub (.reg (.low rd _)) rhs =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw s!"sub_uninit {repr rd}"
        match rhs with
        | .regOrMem (.reg (.low rs _)) =>
          let vb ← match getRegVar? rs cur with
            | some v => pure v | none => throw s!"sub_rhs_uninit {repr rs}"
          let (vd, st1) := freshVarTy cur (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st1) with
                   lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := true }
          out := out ++ [.def1 vd (.bits w) (.bin w "sub" va (some vb) none)]
        | .imm (.int64 c) =>
          let (vd, st1) := freshVarTy cur (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st1) with
                   lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := true }
          out := out ++ [.def1 vd (.bits w) (.bin w "sub" va none (some c.toBitVec))]
        | .regOrMem (.mem a) =>
          if isRspAddr a then throw "spill_in_body: sub slot"
          let (vaddr, asts, st1) ← emitAddrCalc a cur
          let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
          let (vld, st2) := freshVarTy (addElides evs st1) (some rd) (.bits w)
          let (vd, st3) := freshVarTy st2 (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st3) with
                   lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := true }
          out := out ++ asts ++ [.def1 vld (.bits w) (.load w vaddr),
                                 .def1 vd (.bits w) (.bin w "sub" va (some vld) none)]
        | _ => throw "sub_high_byte"
      | .and (.reg (.low rd _)) rhs =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw s!"and_uninit {repr rd}"
        match rhs with
        | .regOrMem (.reg (.low rs _)) =>
          let vb ← match getRegVar? rs cur with
            | some v => pure v | none => throw s!"and_rhs_uninit"
          let (vd, st1) := freshVarTy cur (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st1) with
                   lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := false }
          out := out ++ [.def1 vd (.bits w) (.bin w "and" va (some vb) none)]
        | .imm (.int64 c) =>
          let (vd, st1) := freshVarTy cur (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st1) with
                   lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := false }
          out := out ++ [.def1 vd (.bits w) (.bin w "and" va none (some c.toBitVec))]
        | _ => throw "unsupported_and_mem"
      | .or (.reg (.low rd _)) rhs =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw s!"or_uninit {repr rd}"
        match rhs with
        | .regOrMem (.reg (.low rs _)) =>
          let vb ← match getRegVar? rs cur with
            | some v => pure v | none => throw s!"or_rhs_uninit"
          let (vd, st1) := freshVarTy cur (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st1) with
                   lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := false }
          out := out ++ [.def1 vd (.bits w) (.bin w "or" va (some vb) none)]
        | .imm (.int64 c) =>
          let (vd, st1) := freshVarTy cur (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st1) with
                   lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := false }
          out := out ++ [.def1 vd (.bits w) (.bin w "or" va none (some c.toBitVec))]
        | _ => throw "unsupported_or_mem"
      | .xor (.reg (.low rd _)) rhs =>
        match rhs with
        | .regOrMem (.reg (.low rs _)) =>
          if rd == rs then
            let (vd, st1) := freshVarTy cur (some rd) (.bits w)
            cur := { setRegVar rd vd st1 with
                     lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := false }
            out := out ++ [.def1 vd (.bits w) (.movi w 0#64)]
          else
            let va ← match getRegVar? rd cur with
              | some v => pure v | none => throw s!"xor_uninit {repr rd}"
            let vb ← match getRegVar? rs cur with
              | some v => pure v | none => throw s!"xor_rhs_uninit"
            let (vd, st1) := freshVarTy cur (some rd) (.bits w)
            cur := { setRegVar rd vd (addClique [va, vd] st1) with
                     lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := false }
            out := out ++ [.def1 vd (.bits w) (.bin w "xor" va (some vb) none)]
        | .imm (.int64 c) =>
          let va ← match getRegVar? rd cur with
            | some v => pure v | none => throw s!"xor_uninit {repr rd}"
          let (vd, st1) := freshVarTy cur (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st1) with
                   lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := false }
          out := out ++ [.def1 vd (.bits w) (.bin w "xor" va none (some c.toBitVec))]
        | _ => throw "unsupported_xor_mem"
      | .imul none (.reg (.low rd _)) rhs =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw s!"imul_uninit {repr rd}"
        match rhs with
        | .regOrMem (.reg (.low rs _)) =>
          let vb ← match getRegVar? rs cur with
            | some v => pure v | none => throw s!"imul_rhs_uninit"
          let (vd, st1) := freshVarTy cur (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st1) with
                   lastCmp? := none, lastCmpEqNe := false }
          out := out ++ [.def1 vd (.bits w) (.bin w "mul" va (some vb) none)]
        | .imm (.int64 c) =>
          let (vd, st1) := freshVarTy cur (some rd) (.bits w)
          cur := { setRegVar rd vd (addClique [va, vd] st1) with
                   lastCmp? := none, lastCmpEqNe := false }
          out := out ++ [.def1 vd (.bits w) (.bin w "mul" va none (some c.toBitVec))]
        | _ => throw "unsupported_imul_mem"
      | .mul (.reg (.low rs _)) =>
        let va ← match getRegVar? .rax cur with
          | some v => pure v | none => throw "mul_rax_uninit"
        let vb ← match getRegVar? rs cur with
          | some v => pure v | none => throw "mul_rhs_uninit"
        let (vlo, st1) := freshVarTy cur (some .rax) (.bits w)
        let (vhi, st2) := freshVarTy st1 (some .rdx) (.bits w)
        let st3 := setRegVar .rdx vhi (setRegVar .rax vlo st2)
        out := out ++ [.def2 vlo vhi (.bits w) (.bits w) (.umulw w va vb)]
        cur := { st3 with lastCmp? := none, lastCmpEqNe := false }
      | .inc (.reg (.low rd _)) =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw "inc_uninit"
        let (vd, st1) := freshVarTy cur (some rd) (.bits w)
        let st2 := setRegVar rd vd (addClique [va, vd] st1)
        cur := { st2 with varHints := (vd, .decInc) :: st2.varHints,
                          lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := true }
        out := out ++ [.def1 vd (.bits w) (.bin w "add" va none (some 1#64))]
      | .dec (.reg (.low rd _)) =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw "dec_uninit"
        let (vd, st1) := freshVarTy cur (some rd) (.bits w)
        let st2 := setRegVar rd vd (addClique [va, vd] st1)
        cur := { st2 with varHints := (vd, .decInc) :: st2.varHints,
                          lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := true }
        out := out ++ [.def1 vd (.bits w) (.bin w "sub" va none (some 1#64))]
      | .neg (.reg (.low rd _)) =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw "neg_uninit"
        let (vd, st1) := freshVarTy cur (some rd) (.bits w)
        cur := { setRegVar rd vd (addClique [va, vd] st1) with
                 lastCmp? := some (vd, none, some 0#64, w), lastCmpEqNe := true }
        out := out ++ [.def1 vd (.bits w) (.un w "neg" va)]
      | .not (.reg (.low rd _)) =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw "not_uninit"
        let (vd, st1) := freshVarTy cur (some rd) (.bits w)
        cur := setRegVar rd vd (addClique [va, vd] st1)
        out := out ++ [.def1 vd (.bits w) (.un w "not" va)]
      | .shl (.reg (.low rd _)) (.imm8 (.int64 c)) =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw "shl_uninit"
        let (vd, st1) := freshVarTy cur (some rd) (.bits w)
        cur := { setRegVar rd vd (addClique [va, vd] st1) with
                 lastCmp? := none, lastCmpEqNe := false }
        out := out ++ [.def1 vd (.bits w) (.bin w "shl" va none (some c.toBitVec))]
      | .shr (.reg (.low rd _)) (.imm8 (.int64 c)) =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw "shr_uninit"
        let (vd, st1) := freshVarTy cur (some rd) (.bits w)
        cur := { setRegVar rd vd (addClique [va, vd] st1) with
                 lastCmp? := none, lastCmpEqNe := false }
        out := out ++ [.def1 vd (.bits w) (.bin w "lshr" va none (some c.toBitVec))]
      | .sar (.reg (.low rd _)) (.imm8 (.int64 c)) =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw "sar_uninit"
        let (vd, st1) := freshVarTy cur (some rd) (.bits w)
        cur := { setRegVar rd vd (addClique [va, vd] st1) with
                 lastCmp? := none, lastCmpEqNe := false }
        out := out ++ [.def1 vd (.bits w) (.bin w "ashr" va none (some c.toBitVec))]
      | .shl (.reg (.low rd _)) .cl =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw "shl_uninit"
        let vc ← match getRegVar? .rcx cur with
          | some v => pure v | none => throw "shl_cl_uninit"
        let (vd, st1) := freshVarTy cur (some rd) (.bits w)
        cur := { setRegVar rd vd (addClique [va, vd] st1) with
                 lastCmp? := none, lastCmpEqNe := false }
        out := out ++ [.def1 vd (.bits w) (.bin w "shl" va (some vc) none)]
      | .shr (.reg (.low rd _)) .cl =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw "shr_uninit"
        let vc ← match getRegVar? .rcx cur with
          | some v => pure v | none => throw "shr_cl_uninit"
        let (vd, st1) := freshVarTy cur (some rd) (.bits w)
        cur := { setRegVar rd vd (addClique [va, vd] st1) with
                 lastCmp? := none, lastCmpEqNe := false }
        out := out ++ [.def1 vd (.bits w) (.bin w "lshr" va (some vc) none)]
      | .cmp (.reg (.low ra _)) rhs =>
        let va ← match getRegVar? ra cur with
          | some v => pure v | none => throw s!"cmp_uninit {repr ra}"
        match rhs with
        | .regOrMem (.reg (.low rb _)) =>
          let vb ← match getRegVar? rb cur with
            | some v => pure v | none => throw "cmp_rhs_uninit"
          cur := { cur with lastCmp? := some (va, some vb, none, w), lastCmpEqNe := false }
        | .imm (.int64 c) =>
          cur := { cur with lastCmp? := some (va, none, some c.toBitVec, w), lastCmpEqNe := false }
        | _ => throw "unsupported_cmp_mem"
      | .cmp (.mem a) rhs =>
        if isRspAddr a then throw "spill_in_body: cmp slot"
        let (vaddr, asts, st1) ← emitAddrCalc a cur
        let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
        let (vld, st2) := freshVarTy (addElides evs st1) none (.bits w)
        out := out ++ asts ++ [.def1 vld (.bits w) (.load w vaddr)]
        match rhs with
        | .regOrMem (.reg (.low rb _)) =>
          let vb ← match getRegVar? rb st2 with
            | some v => pure v | none => throw "cmp_rhs_uninit"
          cur := { st2 with lastCmp? := some (vld, some vb, none, w), lastCmpEqNe := false }
        | .imm (.int64 c) =>
          cur := { st2 with lastCmp? := some (vld, none, some c.toBitVec, w), lastCmpEqNe := false }
        | _ => throw "unsupported_cmp_mem_mem"
      | .test (.reg (.low ra _)) (.regOrMem (.reg (.low rb _))) =>
        let va ← match getRegVar? ra cur with
          | some v => pure v | none => throw s!"test_uninit {repr ra}"
        if ra == rb then
          cur := { cur with lastCmp? := some (va, none, some 0#64, w), lastCmpEqNe := false }
        else
          let vb ← match getRegVar? rb cur with
            | some v => pure v | none => throw "test_rhs_uninit"
          let (vt, st1) := freshVarTy cur none (.bits w)
          out := out ++ [.def1 vt (.bits w) (.bin w "and" va (some vb) none)]
          cur := { st1 with lastCmp? := some (vt, none, some 0#64, w), lastCmpEqNe := false }
      | .test (.reg (.low ra _)) (.imm (.int64 c)) =>
        let va ← match getRegVar? ra cur with
          | some v => pure v | none => throw "test_imm_uninit"
        let (vt, st1) := freshVarTy cur none (.bits w)
        out := out ++ [.def1 vt (.bits w) (.bin w "and" va none (some c.toBitVec))]
        cur := { st1 with lastCmp? := some (vt, none, some 0#64, w), lastCmpEqNe := false }
      | .test (.mem a) (.imm (.int64 c)) =>
        if isRspAddr a then throw "spill_in_body: test slot"
        let (vaddr, asts, st1) ← emitAddrCalc a cur
        let evs := asts.filterMap fun | .def1 vid _ _ => some vid | _ => none
        let (vld, st2) := freshVarTy (addElides evs st1) none (.bits w)
        let (vt, st3) := freshVarTy st2 none (.bits w)
        out := out ++ asts ++ [.def1 vld (.bits w) (.load w vaddr),
                               .def1 vt (.bits w) (.bin w "and" vld none (some c.toBitVec))]
        cur := { st3 with lastCmp? := some (vt, none, some 0#64, w), lastCmpEqNe := false }
      | .setcc cc (.reg (.low rd _)) =>
        let (la, lb?, lci?, lw) ← match cur.lastCmp? with
          | some p => pure p | none => throw "setcc_without_cmp"
        if cur.lastCmpEqNe && !(cc == .z || cc == .nz) then
          throw s!"setcc_flag_eq_ne_only {repr cc}"
        let co ← match condToCmpOp cc with
          | some p => pure p | none => throw s!"unsupported_cond {repr cc}"
        let (vc, st1) := freshVarTy cur none .bool
        let st2 := { st1 with flags := (vc, cc) :: st1.flags }
        let (vd, st3) := freshVarTy st2 (some rd) (.bits 8)
        cur := setRegVar rd vd st3
        out := out ++ [.def1 vc .bool (.cmp co lw la lb? lci?), .def1 vd (.bits 8) (.ofBool 8 vc)]
      | .cmovcc cc (.low rd _) (.reg (.low rs _)) =>
        let (la, lb?, lci?, lw) ← match cur.lastCmp? with
          | some p => pure p | none => throw "cmovcc_without_cmp"
        if cur.lastCmpEqNe && !(cc == .z || cc == .nz) then
          throw s!"cmovcc_flag_eq_ne_only {repr cc}"
        let co ← match condToCmpOp cc with
          | some p => pure p | none => throw s!"unsupported_cond {repr cc}"
        let vb ← match getRegVar? rd cur with
          | some v => pure v | none => throw "cmov_dst_uninit"
        let va ← match getRegVar? rs cur with
          | some v => pure v | none => throw "cmov_src_uninit"
        let (vc, st1) := freshVarTy cur none .bool
        let st2 := { st1 with flags := (vc, cc) :: st1.flags }
        let (vd, st3) := freshVarTy st2 (some rd) (.bits w)
        cur := setRegVar rd vd (addClique [vb, vd] st3)
        out := out ++ [.def1 vc .bool (.cmp co lw la lb? lci?), .def1 vd (.bits w) (.select w vc va vb)]
      | .adc (.reg (.low rd _)) rhs =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw "adc_uninit"
        let (vd, st1) := freshVarTy cur (some rd) (.bits w)
        let (vc, st2) := freshVarTy st1 none .bool
        let st3 := setRegVar rd vd (addClique [va, vd]
          { st2 with flags := (vc, .c) :: st2.flags, lastCarry? := some vc,
                     lastCmp? := none, lastCmpEqNe := false })
        match rhs with
        | .regOrMem (.reg (.low rs _)) =>
          let vb ← match getRegVar? rs cur with
            | some v => pure v | none => throw "adc_rhs_uninit"
          out := out ++ [.def2 vd vc (.bits w) .bool (.addc w va (some vb) none cur.lastCarry? false)]
        | .imm (.int64 c) =>
          out := out ++ [.def2 vd vc (.bits w) .bool (.addc w va none (some c.toBitVec) cur.lastCarry? false)]
        | _ => throw "adc_mem"
        cur := st3
      | .adcx (.low rd _) (.reg (.low rs _)) =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw "adcx_uninit"
        let vb ← match getRegVar? rs cur with
          | some v => pure v | none => throw "adcx_rhs_uninit"
        let (vd, st1) := freshVar cur (some rd)
        let (vc, st2) := freshVar st1 none
        let st3 := setRegVar rd vd (addClique [va, vd]
          { st2 with flags := (vc, .c) :: st2.flags, varHints := (vd, .adcx) :: st2.varHints,
                     lastCarry? := some vc, lastCmp? := none, lastCmpEqNe := false })
        out := out ++ [.def2 vd vc (.bits w) .bool (.addc w va (some vb) none cur.lastCarry? false)]
        cur := st3
      | .adox (.low rd _) (.reg (.low rs _)) =>
        let va ← match getRegVar? rd cur with
          | some v => pure v | none => throw "adox_uninit"
        let vb ← match getRegVar? rs cur with
          | some v => pure v | none => throw "adox_rhs_uninit"
        let (vd, st1) := freshVar cur (some rd)
        let (vc, st2) := freshVar st1 none
        let st3 := setRegVar rd vd (addClique [va, vd]
          { st2 with flags := (vc, .o) :: st2.flags, varHints := (vd, .adox) :: st2.varHints,
                     lastCarry? := some vc, lastCmp? := none, lastCmpEqNe := false })
        out := out ++ [.def2 vd vc (.bits w) .bool (.addc w va (some vb) none cur.lastCarry? false)]
        cur := st3
      | _ => throw s!"unsupported_instr: {ATT.instr ins}"
    | .avx _ _ _ => throw "unsupported_avx"
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
    | .adcx (.low rd _) (.reg (.low rs _)) | .adox (.low rd _) (.reg (.low rs _)) => ([rd, rs], [rd])
    | _ => ([], [])
  | _ => ([], [])

def computeLiveInRegs (blocks : List CfgBlock) (retRegs : List Reg64) :
    List (String × List Reg64) :=
  let succs (t : CfgTerm CondCode) : List String := match t with
    | .jmp l | .fall l => [l]
    | .jcc _ l1 l2 => [l1, l2]
    | _ => []
  let blockUsesDefs (b : CfgBlock) : List Reg64 × List Reg64 :=
    b.instrs.foldl (fun (u, d) ins =>
      let (r, w) := instrRegsReadWritten ins
      let u' := r.foldl (fun acc reg => if d.contains reg || acc.contains reg then acc else acc ++ [reg]) u
      let d' := w.foldl (fun acc reg => if acc.contains reg then acc else acc ++ [reg]) d
      (u', d')) ([], [])
  let rec loop (fuel : Nat) (liveIn : List (String × List Reg64)) : List (String × List Reg64) :=
    match fuel with
    | 0 => liveIn
    | f + 1 =>
      let (changed, next) := blocks.foldr (fun b (chg, acc) =>
        let (uses, defs) := blockUsesDefs b
        let outFromSucc := match b.term with
          | .ret | .endMark => retRegs
          | _ => (succs b.term).foldl (fun (rs : List Reg64) (s : String) =>
              let sLive := (liveIn.find? (fun (p : String × List Reg64) => p.1 == s)).map Prod.snd |>.getD []
              sLive.foldl (fun a r => if a.contains r then a else a ++ [r]) rs) []
        let passThrough := outFromSucc.filter fun r => !defs.contains r
        let newIn := passThrough.foldl (fun a r => if a.contains r then a else a ++ [r]) uses
        let oldIn := (liveIn.find? (fun (p : String × List Reg64) => p.1 == b.label)).map Prod.snd |>.getD []
        let chg' := chg || !(newIn.all oldIn.contains && oldIn.all newIn.contains)
        (chg', (b.label, newIn) :: acc)) (false, [])
      if changed then loop f next else next
  loop (blocks.length * 4 + 4) (blocks.map fun b => (b.label, []))

/-- Lift x86-64 directives into a `LiftedSnippet Reg64 CondCode rs` plus mapped `RelHints`. -/
def liftSnippetU (name : Sym) (as rs : List Ty) (dirs : List XDir) :
    Except String (LiftedSnippet Reg64 CondCode rs) := do
  if !dirs.all (fun | .instr (.avx _ _ _) => false | _ => true) then
    throw "avx_unsupported"
  let (bodyDirs, _frameSz, saved) := stripPrologueEpilogue dirs
  let blocks := toCfgBlocks bodyDirs false
  if blocks.isEmpty then throw "empty_blocks"
  let argRegs := x64Frame.argRegs.take as.length
  let retRegs := x64Frame.retRegs.take rs.length
  let liveInMap := computeLiveInRegs blocks retRegs
  let isSingleStraight := blocks.length == 1 && match blocks[0]!.term with
    | .ret | .endMark => true
    | _ => false
  let env0 := ((List.range as.length).map fun i => (i, as[i]!)).reverse
  let (topNExpr, finalSt, blockParamList) ← if isSingleStraight then do
      let b0 := blocks[0]!
      let initRegs := argRegs.mapIdx fun i r => (r, i)
      let initSoft := argRegs.mapIdx fun i r => (i, r)
      let initTys := as.mapIdx fun i t => (i, t)
      let st0 : LiftBlockSt :=
        { nextVar := as.length, regVars := initRegs, varTys := initTys, softRegs := initSoft }
      let (stmts, stAfter) ← liftInstrs b0.instrs st0
      let rvs ← retRegs.mapM fun rr =>
        match getRegVar? rr stAfter with
        | some vr => pure vr
        | none => throw s!"ret_reg_uninit {repr rr}"
      pure (wrapStmts stmts (NExpr.ret rvs), stAfter, ([] : List (Nat × List Reg64)))
    else do
      let initArgTys := as.mapIdx fun i t => (i, t)
      let mut nextV : Nat := as.length
      let mut blkParamVars : List (String × List (Nat × Reg64)) := []
      for b in blocks do
        let regs := (liveInMap.find? (·.1 == b.label)).map Prod.snd |>.getD []
        let pvars := regs.mapIdx fun i r => (nextV + i, r)
        nextV := nextV + regs.length
        blkParamVars := blkParamVars ++ [(b.label, pvars)]
      let mut blockExprs : List (Nat × List (Nat × Ty) × NExpr) := []
      let blkIdxOf (l : String) : Nat := (blocks.findIdx? (·.label == l)).getD 0
      let getParamArgs (l : String) (st : LiftBlockSt) : Except String (List Nat) := do
        let pvars := (blkParamVars.find? (·.1 == l)).map Prod.snd |>.getD []
        pvars.mapM fun (_, r) =>
          match getRegVar? r st with
          | some v => pure v
          | none => throw s!"missing_live_reg {repr r} at jump to {l}"
      let mut sharedSt : LiftBlockSt := { nextVar := nextV, varTys := initArgTys }
      for i in List.range blocks.length do
        let b := blocks[i]!
        let pvars := (blkParamVars.find? (·.1 == b.label)).map Prod.snd |>.getD []
        let initRegs := pvars.map fun (v, r) => (r, v)
        let initSoft := pvars.map fun (v, r) => (v, r)
        let psTy := pvars.map fun (v, _) => (v, i64)
        let stB : LiftBlockSt := {
          nextVar := sharedSt.nextVar
          regVars := initRegs
          varTys := psTy ++ sharedSt.varTys
          cliques := sharedSt.cliques
          flags := sharedSt.flags
          softRegs := initSoft ++ sharedSt.softRegs
          varHints := sharedSt.varHints
          elideVars := sharedSt.elideVars
        }
        let (stmts, stAfter) ← liftInstrs b.instrs stB
        let (extraStmts, termExpr, stFinal) ← match b.term with
          | .ret | .endMark =>
            let rvs ← retRegs.mapM fun rr =>
              match getRegVar? rr stAfter with
              | some vr => pure vr
              | none => throw s!"ret_reg_uninit {repr rr}"
            pure ([], NExpr.ret rvs, stAfter)
          | .jmp tgt | .fall tgt =>
            let args ← getParamArgs tgt stAfter
            pure ([], NExpr.jump (blkIdxOf tgt) args, stAfter)
          | .jcc cc taken fall =>
            let (la, lb?, lci?, lw) ← match stAfter.lastCmp? with
              | some p => pure p | none => throw "jcc_without_cmp"
            if stAfter.lastCmpEqNe && !(cc == .z || cc == .nz) then
              throw s!"jcc_flag_eq_ne_only {repr cc}"
            let co ← match condToCmpOp cc with
              | some p => pure p | none => throw s!"unsupported_jcc_cond {repr cc}"
            let (vc, s1) := freshVar stAfter none
            let s2 := { s1 with flags := (vc, cc) :: s1.flags }
            let argsT ← getParamArgs taken s2
            let argsF ← getParamArgs fall s2
            pure ([LiftedStmt.def1 vc .bool (.cmp co lw la lb? lci?)],
                  NExpr.jnz vc (.jump (blkIdxOf taken) argsT) (.jump (blkIdxOf fall) argsF), s2)
          | .exit sym => throw s!"exit_unsupported: {sym}"
        sharedSt := stFinal
        blockExprs := blockExprs ++ [(i, psTy, wrapStmts (stmts ++ extraStmts) termExpr)]
      let entryRegs := argRegs.mapIdx fun i r => (r, i)
      let entrySt : LiftBlockSt := { nextVar := sharedSt.nextVar, regVars := entryRegs }
      let entryArgs ← getParamArgs blocks[0]!.label entrySt
      let bpr := blkParamVars.mapIdx (fun idx (_, pvs) => (idx, pvs.map Prod.snd))
      pure (NExpr.group blockExprs (.jump 0 entryArgs), sharedSt, bpr)
  let rawRH : RelHints Reg64 CondCode := {
    sameRegCliques := finalSt.cliques
    flagBindings := finalSt.flags
    variants := finalSt.varHints
    softPrefs := finalSt.softRegs ++ (argRegs.mapIdx fun i r => (i, r))
    elideVars := finalSt.elideVars
    blockParamRegs := blockParamList
    savedRegs := saved
    nslots := 0
  }
  let resL ← lowerNExprGen rs env0 [] as.length 0 0 rawRH.variants rawRH.elideVars topNExpr
  let mapVar (vid : Nat) : Nat := (resL.vmap.find? (·.1 == vid)).map Prod.snd |>.getD vid
  let mappedRH : RelHints Reg64 CondCode := {
    sameRegCliques := rawRH.sameRegCliques.map (·.map mapVar)
    flagBindings := rawRH.flagBindings.map (fun (v, cc) => (mapVar v, cc))
    variants := resL.vhs
    softPrefs := rawRH.softPrefs.map (fun (v, r) => (mapVar v, r))
    elideVars := rawRH.elideVars.map mapVar
    elideIps := resL.elides
    blockParamRegs := rawRH.blockParamRegs
    savedRegs := saved
    nslots := 0
  }
  pure { name := name, as := as, tflat := resL.tflat, relHints := mappedRH,
         ipHintMap := resL.vhs, ipElideMap := resL.elides, varToSoftReg := mappedRH.softPrefs }

/-- Output of end-to-end `liftSnippet` including solved hints, standalone lowered code, and
self round-trip `AsmIso` verdict (`LiftResultX64.fn` projects the `Fn`). -/
structure LiftResultX64 where
  rs     : List Ty
  lifted : LiftedSnippet Reg64 CondCode rs
  hints  : x64Isa.Hints
  code   : List XDir
  iso    : IsoVerdict

/-- Materialize the `Fn` of a `LiftResultX64`. -/
def LiftResultX64.fn (r : LiftResultX64) : Fn := r.lifted.toFn

/-- Full untrusted x86-64 directive lifting + `solveRelHints` + standalone `Rega.lowerFn` +
`checkAsmIso` round-trip check. -/
def liftSnippet (name : Sym) (as rs : List Ty) (dirs : List XDir)
    (avoidRegs : List Reg64 := []) : Except String LiftResultX64 := do
  let lifted ← liftSnippetU name as rs dirs
  let fn := lifted.toFn
  let hints := solveRelHints x64Isa lifted.relHints fn avoidRegs lifted.ipElideMap
  let code ← Rega.lowerFn x64Isa hints fn.ext fn
  let iso := checkAsmIso dirs code
  pure { rs := rs, lifted := lifted, hints := hints, code := code, iso := iso }

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
