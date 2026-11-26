module

public import LeanQbe.T.Arm64.Isa
public import LeanQbe.T.SnippetCheck
public import LeanQbe.T.SpillSnippet
public import Kraken.AArch64.Parser
public import Kraken.AArch64.Print

/-!
# AAPCS64 Arm64 Snippet Budget Profiler, `AsmIso`, and Untrusted Lifter (`Arm64.Snippet`)

Purely additive Class `L` backend adapter under `LeanQbe.T.Arm64`:

* `profileDirs`, `stripPrologueEpilogue`: Arm64 assembly profiler counting body insns, SP-relative
  spills, `cset`/`csel` chains, flag-setting compares, branches, and calls.
* `checkAsmIso`: CFG alpha-isomorphism checker
  (`IsoVerdict.tier1` / `tier2` (`orr0~add0`) / `fail`).
* `liftSnippetU`, `liftSnippet`: untrusted Arm64 assembly lifter (with `peekFlagCond` eager flag
  lookahead, `cbz`/`cbnz`/`tbz`/`tbnz`, `ubfm`/`sbfm`, `csel`/`cset`, `addElides`) ->
  `LiftedSnippet` -> `solveRelHints armIsa` -> `Rega.lowerFn` + `checkAsmIso`.
* `checkRegaAndBudget`: end-to-end `Rega.lowerFn` + `@predictable` static `SnippetBudget` check.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T LeanQbe.T.SnippetCheck LeanQbe.T.SpillSnippet Kraken.AArch64

local instance : Inhabited XReg := ⟨.X0⟩
local instance : Inhabited XRegOrSp := ⟨.reg .X0⟩
local instance : Inhabited Reg := ⟨.reg .X0⟩
local instance : Inhabited Instr := ⟨⟨.W64, .NOP⟩⟩

abbrev ADir := armIsa.Directive

/-! ## 1. Prologue/Epilogue Stripping & `BudgetMetrics` Profiler -/

def stripNops (ds : List ADir) : List ADir :=
  ds.filter fun
    | .instr ⟨_, .NOP⟩ => false
    | _ => true

def isSpAddr (a : AddrExpr) : Bool :=
  a.base == .low .SP .W64

def isSpUAddr (a : UnscaledAddrExpr) : Bool :=
  a.base == .low .SP .W64

def isBodySpillInstr (i : Instr) : Bool :=
  match i with
  | ⟨_, .LDR _ (.addr a)⟩ | ⟨_, .STR _ a⟩ | ⟨.W32, .LDRB _ a⟩ | ⟨.W32, .STRB _ a⟩
  | ⟨.W32, .LDRH _ a⟩ | ⟨.W32, .STRH _ a⟩ | ⟨_, .LDRSB _ a⟩ | ⟨_, .LDRSH _ a⟩
  | ⟨.W64, .LDRSW _ (.addr a)⟩ | ⟨_, .LDP _ _ a⟩ | ⟨_, .STP _ _ a⟩ => isSpAddr a
  | ⟨_, .LDUR _ u⟩ | ⟨_, .STUR _ u⟩ | ⟨.W32, .LDURB _ u⟩ | ⟨.W32, .STURB _ u⟩
  | ⟨.W32, .LDURH _ u⟩ | ⟨.W32, .STURH _ u⟩ | ⟨_, .LDURSB _ u⟩ | ⟨_, .LDURSH _ u⟩
  | ⟨.W64, .LDURSW _ u⟩ => isSpUAddr u
  | ⟨.W64, .ADD_e (.low (.reg .X16) .W64) (.low .SP .W64) _⟩ => true
  | _ => false

def isArmFrameRestoreInstr (i : Instr) : Bool :=
  match i with
  | ⟨.W64, .LDP (.low (.reg r1) .W64) (.low (.reg r2) .W64) a⟩ =>
    isSpAddr a && armFrame.calleeSaved.contains (.reg r1) && armFrame.calleeSaved.contains (.reg r2)
  | ⟨.W64, .LDR (.low (.reg r) .W64) (.addr a)⟩ =>
    isSpAddr a && (armFrame.calleeSaved.contains (.reg r) || r == .X30)
  | ⟨.W64, .ADD_e (.low .SP .W64) (.low .SP .W64) _⟩ => true
  | _ => false

partial def peelEpiRev (dsRev : List ADir) : List ADir :=
  match dsRev with
  | .instr i :: rest =>
    if isArmFrameRestoreInstr i then
      match rest with
      | .instr ⟨.W64, .LDR (.low (.reg .X16) .W64) (.lit (.pool _))⟩ :: rest2 => peelEpiRev rest2
      | _ => peelEpiRev rest
    else .instr i :: rest
  | other => other

def stripPrologueEpilogue (ds : List ADir) : List ADir × Nat × List Reg :=
  let rec peelPro (saved : List Reg) (frameSz : Nat) : List ADir → List ADir × Nat × List Reg
    | .instr ⟨.W64, .SUB_e (.low .SP .W64) (.low .SP .W64) (.imm ie)⟩ :: rest =>
      let sz := match ie.imm with | .int64 c => c.toNatClampNeg | _ => 0
      peelPro saved sz rest
    | .instr ⟨.W64, .LDR (.low (.reg .X16) .W64) (.lit (.pool ⟨.int64 c⟩))⟩ ::
      .instr ⟨.W64, .SUB_e (.low .SP .W64) (.low .SP .W64) (.ext _)⟩ :: rest =>
      peelPro saved c.toNatClampNeg rest
    | .instr ⟨.W64, .STP (.low (.reg r1) .W64) (.low (.reg r2) .W64) a⟩ :: rest =>
      if isSpAddr a && armFrame.calleeSaved.contains (.reg r1) &&
          armFrame.calleeSaved.contains (.reg r2) then
        let s1 := if saved.contains (.reg r1) then saved else saved ++ [.reg r1]
        let s2 := if s1.contains (.reg r2) then s1 else s1 ++ [.reg r2]
        peelPro s2 frameSz rest
      else
        (.instr ⟨.W64, .STP (.low (.reg r1) .W64) (.low (.reg r2) .W64) a⟩ :: rest,
         frameSz, saved)
    | .instr ⟨.W64, .STR (.low (.reg r) .W64) a⟩ :: rest =>
      if isSpAddr a && (armFrame.calleeSaved.contains (.reg r) || r == .X30) then
        let s1 := if saved.contains (.reg r) then saved else saved ++ [.reg r]
        peelPro s1 frameSz rest
      else (.instr ⟨.W64, .STR (.low (.reg r) .W64) a⟩ :: rest, frameSz, saved)
    | .instr ⟨.W64, .LDR (.low (.reg .X16) .W64) (.lit (.pool _))⟩ ::
      .instr ⟨.W64, .STR (.low (.reg r) .W64) a⟩ :: rest =>
      if isSpAddr a && armFrame.calleeSaved.contains (.reg r) then
        let s1 := if saved.contains (.reg r) then saved else saved ++ [.reg r]
        peelPro s1 frameSz rest
      else (.instr ⟨.W64, .STR (.low (.reg r) .W64) a⟩ :: rest, frameSz, saved)
    | other => (other, frameSz, saved)
  let labelOf? : ADir → Option String | .label l => some l | _ => none
  let isRet : ADir → Bool | .instr ⟨.W64, .RET _⟩ => true | _ => false
  stripPrologueEpilogueGen stripNops labelOf? peelPro isRet peelEpiRev ds

def isArmMovReg (i : Instr) : Bool :=
  match i.operation with
  | .ORR_s _ (.low .XZR _) sr => sr.shift == .LSL && sr.amount == 0
  | .ADD_e _ _ (.imm ie) => ie.imm == .int64 0
  | _ => false

def isArmCmp (i : Instr) : Bool :=
  match i.operation with
  | .SUBS_e (.low .XZR _) _ _ | .SUBS_s (.low .XZR _) _ _
  | .ADDS_e (.low .XZR _) _ _ | .ADDS_s (.low .XZR _) _ _
  | .ANDS_i (.low .XZR _) _ _ | .ANDS_s (.low .XZR _) _ _ => true
  | _ => false

def isArmCset (i : Instr) : Bool :=
  match i.operation with
  | .CSINC _ (.low .XZR _) (.low .XZR _) _ => true
  | _ => false

/-- Profile Arm64 directives into target-generic `BudgetMetrics`. -/
def profileDirs (ds : List ADir) (stripFrame : Bool := true) : BudgetMetrics :=
  let instrOf? : ADir → Option Instr | .instr i => some i | _ => none
  let stepBody (i : Instr) (_ : Unit) (m : BudgetMetrics) : Unit × BudgetMetrics :=
    let m' :=
      if isArmMovReg i then { m with regMoves := m.regMoves + 1 }
      else if isArmCset i then { m with boolChains := m.boolChains + 1 }
      else if isArmCmp i then { m with cmpsTests := m.cmpsTests + 1 }
      else match i with
      | ⟨_, .CSEL ..⟩ | ⟨_, .CSINC ..⟩ | ⟨_, .CSINV ..⟩ | ⟨_, .CSNEG ..⟩ =>
        { m with selectOps := m.selectOps + 1 }
      | ⟨.W64, .B_cond ..⟩ | ⟨_, .CBZ ..⟩ | ⟨_, .CBNZ ..⟩ | ⟨_, .TBZ ..⟩ | ⟨_, .TBNZ ..⟩ =>
        { m with branches := m.branches + 1 }
      | ⟨.W64, .B _⟩ => { m with jmps := m.jmps + 1 }
      | ⟨.W64, .BL _⟩ => { m with calls := m.calls + 1 }
      | _ => m
    ((), m')
  profileDirsGen stripNops (fun x => (stripPrologueEpilogue x).1)
    instrOf? isBodySpillInstr () stepBody ds stripFrame

/-! ## 2. `AsmIso` CFG Alpha-Isomorphism Checker (`AArch64`) -/

inductive BranchCond where
  | flags (cc : CondCode)
  | cbz (w : RegWidth) (r : XReg)
  | cbnz (w : RegWidth) (r : XReg)
  | tbz (w : RegWidth) (r : XReg) (bit : Nat)
  | tbnz (w : RegWidth) (r : XReg) (bit : Nat)
  deriving Repr, BEq

def negBranchCond : BranchCond → BranchCond
  | .flags cc => .flags cc.invert
  | .cbz w r => .cbnz w r
  | .cbnz w r => .cbz w r
  | .tbz w r b => .tbnz w r b
  | .tbnz w r b => .tbz w r b

abbrev CfgBlock := GenCfgBlock Instr BranchCond

def isTermInstr (i : Instr) : Bool :=
  match i with
  | ⟨.W64, .RET _⟩ | ⟨.W64, .B _⟩ | ⟨.W64, .B_cond _ _⟩
  | ⟨_, .CBZ _ _⟩ | ⟨_, .CBNZ _ _⟩ | ⟨_, .TBZ _ _ _⟩ | ⟨_, .TBNZ _ _ _⟩ => true
  | _ => false

namespace SnippetImpl

def labelOf? : ADir → Option String | .label l => some l | _ => none
def instrOf? : ADir → Option Instr | .instr i => some i | _ => none

def extractBranch? (i : Instr) : Option (BranchCond × String) :=
  match i.operation_size, i.operation with
  | _, .B_cond cc (.label t) => some (.flags cc, t)
  | w, .CBZ (.low (.reg r) _) (.label t) => some (.cbz w r, t)
  | w, .CBNZ (.low (.reg r) _) (.label t) => some (.cbnz w r, t)
  | w, .TBZ (.low (.reg r) _) b (.label t) => some (.tbz w r b, t)
  | w, .TBNZ (.low (.reg r) _) b (.label t) => some (.tbnz w r b, t)
  | _, _ => none

def parseTerm (i : Instr) (nextLbl? : Option String) : Option (CfgTerm BranchCond) :=
  match i with
  | ⟨.W64, .RET _⟩ => some .ret
  | ⟨_, .B (.label t)⟩ => some (.jmp t)
  | ⟨_, .B c⟩ => some (.exit (toString (repr c)))
  | _ => (extractBranch? i).map fun (bc, tgt) => .jcc bc tgt (nextLbl?.getD "__end")

end SnippetImpl

def toCfgBlocks (ds : List ADir) (stripFrame : Bool := true) : List CfgBlock :=
  toCfgBlocksGen stripNops (fun x => (stripPrologueEpilogue x).1)
    SnippetImpl.labelOf? SnippetImpl.instrOf? isTermInstr
    SnippetImpl.parseTerm SnippetImpl.extractBranch? ds stripFrame

abbrev IsoState := GenIsoState XReg

def matchXReg (fixed : List XReg) (r1 r2 : XReg) (st : IsoState) : Option IsoState :=
  matchFixedReg fixed r1 r2 st

def matchRegOrZr {w : RegWidth} (fixed : List XReg) (a b : RegOrZr w) (st : IsoState) :
    Option IsoState :=
  match a, b with
  | .low (.reg x1) _, .low (.reg x2) _ => matchXReg fixed x1 x2 st
  | .low .XZR _, .low .XZR _ => some st
  | _, _ => none

def matchRegOrSp {w : RegWidth} (fixed : List XReg) (a b : RegOrSp w) (st : IsoState) :
    Option IsoState :=
  match a, b with
  | .low (.reg x1) _, .low (.reg x2) _ => matchXReg fixed x1 x2 st
  | .low .SP _, .low .SP _ => some st
  | _, _ => none

def matchConstExpr (c1 c2 : ConstExpr) (st : IsoState) : Option IsoState :=
  matchConstExprGen (fun | .label l => some l | _ => none) c1 c2 st

def matchImmExpr (i1 i2 : ImmExpr) (st : IsoState) : Option IsoState :=
  if i1.shift == i2.shift then matchConstExpr i1.imm i2.imm st else none

def matchExtOrImmReg (fixed : List XReg) (a b : ExtOrImmReg) (st : IsoState) :
    Option IsoState :=
  match a, b with
  | .imm i1, .imm i2 => matchImmExpr i1 i2 st
  | .ext e1, .ext e2 =>
    if h : e1.reg.1 = e2.reg.1 then
      if e1.ext == e2.ext then matchRegOrZr fixed e1.reg.2 (h ▸ e2.reg.2) st else none
    else none
  | _, _ => none

def matchShiftReg {w : RegWidth} (fixed : List XReg) (a b : ShiftRegExpr w)
    (st : IsoState) : Option IsoState :=
  if a.shift == b.shift && a.amount == b.amount then matchRegOrZr fixed a.reg b.reg st else none

def matchAddr (fixed : List XReg) (a1 a2 : AddrExpr) (st : IsoState) : Option IsoState := do
  let st ← matchRegOrSp fixed a1.base a2.base st
  match a1.off, a2.off with
  | .imm i1, .imm i2 =>
    if i1.index == i2.index then
      if a1.base == .low .SP .W64 then
        match i1.imm, i2.imm with
        | .int64 d1, .int64 d2 =>
          (bindBijection d1 d2 st.slotMap).map fun sm => { st with slotMap := sm }
        | _, _ => matchConstExpr i1.imm i2.imm st
      else matchConstExpr i1.imm i2.imm st
    else none
  | .reg r1, .reg r2 =>
    if h : r1.reg.1 = r2.reg.1 then
      if r1.ext == r2.ext then matchRegOrZr fixed r1.reg.2 (h ▸ r2.reg.2) st else none
    else none
  | _, _ => none

def matchAddrOrLit (fixed : List XReg) (a1 a2 : AddrOrLit) (st : IsoState) :
    Option IsoState :=
  match a1, a2 with
  | .addr x1, .addr x2 => matchAddr fixed x1 x2 st
  | .lit (.pool p1), .lit (.pool p2) => matchConstExpr p1.expr p2.expr st
  | .lit (.addr l1), .lit (.addr l2) =>
    (bindBijection l1.label l2.label st.lblMap).map fun lm => { st with lblMap := lm }
  | _, _ => none

def matchOperation {w : RegWidth} (fixed : List XReg) (op1 op2 : Operation w)
    (st : IsoState) : Option IsoState :=
  let mz {u} (a b : RegOrZr u) (s : IsoState) := matchRegOrZr fixed a b s
  let msp {u} (a b : RegOrSp u) (s : IsoState) := matchRegOrSp fixed a b s
  let m3z {u} (d1 d2 a1 a2 b1 b2 : RegOrZr u) := mz d1 d2 st >>= mz a1 a2 >>= mz b1 b2
  let m4z {u} (d1 d2 a1 a2 b1 b2 c1 c2 : RegOrZr u) := m3z d1 d2 a1 a2 b1 b2 >>= mz c1 c2
  let mSh {u} (d1 d2 a1 a2 : RegOrZr u) (b1 b2 : ShiftRegExpr u) :=
    mz d1 d2 st >>= mz a1 a2 >>= matchShiftReg fixed b1 b2
  let mAd {u} (r1 r2 : RegOrZr u) (a1 a2 : AddrExpr) := mz r1 r2 st >>= matchAddr fixed a1 a2
  match op1, op2 with
  | .ADD_e d1 a1 b1, .ADD_e d2 a2 b2 | .SUB_e d1 a1 b1, .SUB_e d2 a2 b2 =>
    msp d1 d2 st >>= msp a1 a2 >>= matchExtOrImmReg fixed b1 b2
  | .ADDS_e d1 a1 b1, .ADDS_e d2 a2 b2 | .SUBS_e d1 a1 b1, .SUBS_e d2 a2 b2 =>
    mz d1 d2 st >>= msp a1 a2 >>= matchExtOrImmReg fixed b1 b2
  | .ADD_s d1 a1 b1, .ADD_s d2 a2 b2 | .SUB_s d1 a1 b1, .SUB_s d2 a2 b2
  | .ADDS_s d1 a1 b1, .ADDS_s d2 a2 b2 | .SUBS_s d1 a1 b1, .SUBS_s d2 a2 b2
  | .AND_s d1 a1 b1, .AND_s d2 a2 b2 | .ANDS_s d1 a1 b1, .ANDS_s d2 a2 b2
  | .ORR_s d1 a1 b1, .ORR_s d2 a2 b2 | .ORN_s d1 a1 b1, .ORN_s d2 a2 b2
  | .EOR_s d1 a1 b1, .EOR_s d2 a2 b2 => mSh d1 d2 a1 a2 b1 b2
  | .ADC d1 a1 b1, .ADC d2 a2 b2 | .ADCS d1 a1 b1, .ADCS d2 a2 b2
  | .SBC d1 a1 b1, .SBC d2 a2 b2 | .SBCS d1 a1 b1, .SBCS d2 a2 b2
  | .UDIV d1 a1 b1, .UDIV d2 a2 b2 | .SDIV d1 a1 b1, .SDIV d2 a2 b2
  | .SMULH d1 a1 b1, .SMULH d2 a2 b2 | .UMULH d1 a1 b1, .UMULH d2 a2 b2
  | .LSLV d1 a1 b1, .LSLV d2 a2 b2 | .LSRV d1 a1 b1, .LSRV d2 a2 b2
  | .ASRV d1 a1 b1, .ASRV d2 a2 b2 | .RORV d1 a1 b1, .RORV d2 a2 b2 => m3z d1 d2 a1 a2 b1 b2
  | .MADD d1 a1 b1 c1, .MADD d2 a2 b2 c2 | .MSUB d1 a1 b1 c1, .MSUB d2 a2 b2 c2 =>
    m4z d1 d2 a1 a2 b1 b2 c1 c2
  | .SMADDL d1 a1 b1 c1, .SMADDL d2 a2 b2 c2 | .UMADDL d1 a1 b1 c1, .UMADDL d2 a2 b2 c2 =>
    mz d1 d2 st >>= mz a1 a2 >>= mz b1 b2 >>= mz c1 c2
  | .AND_i d1 a1 c1, .AND_i d2 a2 c2 | .ORR_i d1 a1 c1, .ORR_i d2 a2 c2
  | .EOR_i d1 a1 c1, .EOR_i d2 a2 c2 => msp d1 d2 st >>= mz a1 a2 >>= matchConstExpr c1 c2
  | .ANDS_i d1 a1 c1, .ANDS_i d2 a2 c2 => mz d1 d2 st >>= mz a1 a2 >>= matchConstExpr c1 c2
  | .UBFM d1 a1 r1 s1, .UBFM d2 a2 r2 s2 | .SBFM d1 a1 r1 s1, .SBFM d2 a2 r2 s2 =>
    if r1 == r2 && s1 == s2 then mz d1 d2 st >>= mz a1 a2 else none
  | .EXTR d1 a1 b1 l1, .EXTR d2 a2 b2 l2 => if l1 == l2 then m3z d1 d2 a1 a2 b1 b2 else none
  | .MOVZ d1 c1 ms1, .MOVZ d2 c2 ms2 | .MOVK d1 c1 ms1, .MOVK d2 c2 ms2
  | .MOVN d1 c1 ms1, .MOVN d2 c2 ms2 =>
    if ms1 == ms2 then mz d1 d2 st >>= matchConstExpr c1 c2 else none
  | .CSEL d1 a1 b1 cc1, .CSEL d2 a2 b2 cc2 | .CSINC d1 a1 b1 cc1, .CSINC d2 a2 b2 cc2
  | .CSINV d1 a1 b1 cc1, .CSINV d2 a2 b2 cc2
  | .CSNEG d1 a1 b1 cc1, .CSNEG d2 a2 b2 cc2 => if cc1 == cc2 then m3z d1 d2 a1 a2 b1 b2 else none
  | .LDR d1 al1, .LDR d2 al2 | .LDRSW d1 al1, .LDRSW d2 al2 =>
    mz d1 d2 st >>= matchAddrOrLit fixed al1 al2
  | .STR r1 a1, .STR r2 a2 | .LDRB r1 a1, .LDRB r2 a2 | .STRB r1 a1, .STRB r2 a2
  | .LDRH r1 a1, .LDRH r2 a2 | .STRH r1 a1, .STRH r2 a2
  | .LDRSB r1 a1, .LDRSB r2 a2 | .LDRSH r1 a1, .LDRSH r2 a2 => mAd r1 r2 a1 a2
  | .CLZ d1 a1, .CLZ d2 a2 | .CLS d1 a1, .CLS d2 a2
  | .RBIT d1 a1, .RBIT d2 a2 | .REV d1 a1, .REV d2 a2 | .REV16 d1 a1, .REV16 d2 a2 =>
    mz d1 d2 st >>= mz a1 a2
  | .BL t1, .BL t2 => if t1 == t2 then some st else none
  | .RET _, .RET _ => some st
  | _, _ => none

def matchInstr (fixed : List XReg) (i1 i2 : Instr) (st : IsoState) : Option IsoState :=
  if h : i1.operation_size = i2.operation_size then
    matchOperation fixed i1.operation (h ▸ i2.operation) st
  else none

def matchSeq (tier2 : Bool) (fixed : List XReg) :
    List Instr → List Instr → IsoState → Option IsoState
  | [], [], st => some st
  | i1 :: r1, i2 :: r2, st =>
    (matchInstr fixed i1 i2 st >>= matchSeq tier2 fixed r1 r2) <|>
    if !tier2 then none
    else
      let mOrrAdd {w1 w2} (o1 : Operation w1) (o2 : Operation w2) (note : String) (rev : Bool) :=
        match o1, o2 with
        | .ORR_s (.low (.reg d1) _) (.low .XZR _) sr1,
          .ADD_e (.low (.reg d2) _) (.low (.reg s2) _) (.imm ie2) =>
          if sr1.shift == .LSL && sr1.amount == 0 && ie2.imm == .int64 0 then
            match sr1.reg with
            | .low (.reg s1) _ =>
              if _h : i1.operation_size = i2.operation_size then
                let mr x y s := if rev then matchXReg fixed y x s else matchXReg fixed x y s
                (mr d1 d2 st >>= mr s1 s2).bind fun st' =>
                  matchSeq tier2 fixed r1 r2 { st' with tier2Notes := note :: st'.tier2Notes }
              else none
            | _ => none
          else none
        | _, _ => none
      mOrrAdd i1.operation i2.operation "orr0~add0" false <|>
        mOrrAdd i2.operation i1.operation "add0~orr0" true
  | _, _, _ => none

def matchBranchCond (fixed : List XReg) (b1 b2 : BranchCond) (st : IsoState) :
    Option IsoState :=
  match b1, b2 with
  | .flags c1, .flags c2 => if c1 == c2 then some st else none
  | .cbz w1 r1, .cbz w2 r2 | .cbnz w1 r1, .cbnz w2 r2 =>
    if w1 == w2 then matchXReg fixed r1 r2 st else none
  | .tbz w1 r1 k1, .tbz w2 r2 k2 | .tbnz w1 r1 k1, .tbnz w2 r2 k2 =>
    if w1 == w2 && k1 == k2 then matchXReg fixed r1 r2 st else none
  | _, _ => none

def classifyMismatch (ref cand : List CfgBlock) (refB candB : BudgetMetrics) :
    String × String :=
  classifyMismatchGen "ifconv_csel" "csels" "br"
    "bool_cset_chain" "csets" "cmps" ref cand refB candB

partial def matchCfgFrom (tier2 : Bool) (fixed : List XReg)
    (bs1 bs2 : List CfgBlock) (l1 l2 : String) (st : IsoState) : Option IsoState :=
  matchCfgFromGen matchSeq matchBranchCond negBranchCond tier2 fixed bs1 bs2 l1 l2 st

/-- Compare two Arm64 directive streams for structural/register alpha-isomorphism (`AsmIso`). -/
def checkAsmIso (ref cand : List ADir) (stripFrame : Bool := true) (allowRegPerm : Bool := true) :
    IsoVerdict :=
  let fixedPerm := [.X16, .X17, .X30]
  let noPerm := (armFrame.allocatable ++ armFrame.calleeSaved).filterMap
    (fun | .reg x => some x | _ => none) ++ fixedPerm
  let initSt : IsoState := { regMap := [(.X16, .X16), (.X17, .X17), (.X30, .X30)] }
  checkAsmIsoGen (fun d s => toCfgBlocks d s) (fun d s => profileDirs d s) matchSeq
    matchBranchCond negBranchCond classifyMismatch fixedPerm noPerm
    initSt ref cand stripFrame allowRegPerm

/-! ## 3. Untrusted Arm64 Lifter (`liftSnippetU`, `liftSnippet`) -/

def condToCmpOp : CondCode → Option CmpOp
  | .EQ => some .eq | .NE => some .ne
  | .CC => some .ult | .LS => some .ule
  | .HI => some .ugt | .CS => some .uge
  | .LT => some .slt | .LE => some .sle
  | .GT => some .sgt | .GE => some .sge
  | _ => none

def ccToArmCond : CondCode → Option ArmCond
  | .EQ => some .eq | .NE => some .ne
  | .CC => some .cc | .CS => some .cs
  | .HI => some .hi | .LS => some .ls
  | .LT => some .lt | .LE => some .le
  | .GT => some .gt | .GE => some .ge
  | _ => none

abbrev LiftBlockSt := GenLiftSt XReg Reg ArmCond CondCode

def widthBits : RegWidth → Nat
  | .W32 => 32 | .W64 => 64

def isScratchXReg (x : XReg) : Bool := x == .X16 || x == .X17

def toSoftReg? (x : XReg) : Option Reg :=
  if isScratchXReg x then none else some (XRegOrSp.reg x)

abbrev freshVar (st : LiftBlockSt) (r? : Option XReg) : Nat × LiftBlockSt :=
  st.fresh toSoftReg? r? none
abbrev freshVarTy (st : LiftBlockSt) (r? : Option XReg) (ty : Ty) : Nat × LiftBlockSt :=
  st.fresh toSoftReg? r? (some ty)
abbrev setRegVar := @GenLiftSt.setReg XReg Reg ArmCond CondCode _
abbrev setRegImm := @GenLiftSt.setImm XReg Reg ArmCond CondCode _
abbrev getRegVar? := @GenLiftSt.regVar? XReg Reg ArmCond CondCode _
abbrev getRegImm? := @GenLiftSt.regImm? XReg Reg ArmCond CondCode _
abbrev addElides := @GenLiftSt.elide XReg Reg ArmCond CondCode

def movShiftNat {w : RegWidth} : MovShift w → Nat
  | .LSL0 => 0 | .LSL16 => 16 | .LSL32 => 32 | .LSL48 => 48

def memExtShiftAmt : MemExtendAmount → Nat
  | .E0 => 0 | .E1 => 1 | .E2 => 2 | .E3 => 3

def extShiftAmt : ExtendAmount → Nat
  | .E0 => 0 | .E1 => 1 | .E2 => 2 | .E3 => 3 | .E4 => 4

def emitAddrCalc (a : AddrExpr) (st : LiftBlockSt) :
    Except String (Nat × List LiftedStmt × LiftBlockSt) := do
  let vb ← match a.base with
    | .low (.reg rb) _ =>
      match getRegVar? rb st with | some v => pure v | none => throw s!"uninit_base {repr rb}"
    | .low .SP _ => throw "spill_in_body: sp base"
  match a.off with
  | .imm ie =>
    let disp : BitVec 64 := match ie.imm with | .int64 d => d.toBitVec | _ => 0#64
    if disp == 0#64 then pure (vb, [], st)
    else
      let (va, st1) := freshVar st none
      pure (va, [.def1 va i64 (.bin 64 "add" vb none (some disp))], st1)
  | .reg mr =>
    match mr.reg.2 with
    | .low .XZR _ => pure (vb, [], st)
    | .low (.reg ri) _ =>
      let vi ← match getRegVar? ri st with
        | some v => pure v
        | none => throw s!"uninit_idx {repr ri}"
      let sh := memExtShiftAmt mr.ext.amount
      let (vx, st1, stmts1) := match mr.ext.type with
        | .UXTW =>
          let (vz, s0) := freshVar st none
          (vz, s0, [LiftedStmt.def1 vz i64 (.zext 32 64 vi)])
        | .SXTW =>
          let (vz, s0) := freshVar st none
          (vz, s0, [LiftedStmt.def1 vz i64 (.sext 32 64 vi)])
        | _ => (vi, st, [])
      let (vs, st2, stmts2) := if sh == 0 then (vx, st1, stmts1)
        else
          let (vsh, s1) := freshVar st1 none
          let shStmt := LiftedStmt.def1 vsh i64 (.bin 64 "shl" vx none (some (BitVec.ofNat 64 sh)))
          (vsh, s1, stmts1 ++ [shStmt])
      let (va, st3) := freshVar st2 none
      pure (va, stmts2 ++ [LiftedStmt.def1 va i64 (.bin 64 "add" vb (some vs) none)], st3)

def emitUnscaledAddrCalc (u : UnscaledAddrExpr) (st : LiftBlockSt) :
    Except String (Nat × List LiftedStmt × LiftBlockSt) := do
  let vb ← match u.base with
    | .low (.reg rb) _ =>
      match getRegVar? rb st with | some v => pure v | none => throw s!"uninit_ubase {repr rb}"
    | .low .SP _ => throw "spill_in_body: unscaled sp"
  let disp : BitVec 64 := match u.imm with | .int64 d => d.toBitVec | _ => 0#64
  if disp == 0#64 then pure (vb, [], st)
  else
    let (va, st1) := freshVar st none
    pure (va, [.def1 va i64 (.bin 64 "add" vb none (some disp))], st1)

def emitShiftExpr {w : RegWidth} (sr : ShiftRegExpr w) (cur : LiftBlockSt) :
    Except String (Nat × List LiftedStmt × LiftBlockSt) := do
  let n := widthBits w
  let v ← match sr.reg with
    | .low .XZR _ =>
      let (vz, s0) := freshVarTy cur none (.bits n)
      pure (vz, [LiftedStmt.def1 vz (.bits n) (.movi n 0#64)], s0)
    | .low (.reg rx) _ =>
      match getRegVar? rx cur with
      | some vr => pure (vr, [], cur)
      | none => throw s!"shift_src_uninit {repr rx}"
  let (vr, sts, s1) := v
  let amt := sr.amount.toNatClampNeg
  if amt == 0 then pure (vr, sts, s1)
  else
    let nm := match sr.shift with | .LSL => "shl" | .LSR => "lshr" | .ASR => "ashr" | .ROR => "rotr"
    if nm == "rotr" then throw "unsupported_ror_shift"
    else
      let (vs, s2) := freshVarTy s1 none (.bits n)
      let shStmt := LiftedStmt.def1 vs (.bits n) (.bin n nm vr none (some (BitVec.ofNat 64 amt)))
      pure (vs, sts ++ [shStmt], s2)

def emitExtImm {w : RegWidth} (ei : ExtOrImmReg) (cur : LiftBlockSt) :
    Except String (Option Nat × Option (BitVec 64) × List LiftedStmt × LiftBlockSt) := do
  let n := widthBits w
  match ei with
  | .imm ie =>
    let base : BitVec 64 := match ie.imm with | .int64 c => c.toBitVec | _ => 0#64
    let sh := match ie.shift with | .S0 => 0 | .S12 => 12
    pure (none, some (base <<< sh), [], cur)
  | .ext er =>
    match er.reg.2 with
    | .low .XZR _ => pure (none, some 0#64, [], cur)
    | .low (.reg rx) _ =>
      let vx ← match getRegVar? rx cur with
        | some v => pure v
        | none => throw s!"ext_uninit {repr rx}"
      let sh := extShiftAmt er.ext.amount
      let (ve, s1, sts1) := match er.ext.type with
        | .UXTB =>
          let (z, s) := freshVarTy cur none (.bits n)
          (z, s, [LiftedStmt.def1 z (.bits n) (.zext 8 n vx)])
        | .SXTB =>
          let (z, s) := freshVarTy cur none (.bits n)
          (z, s, [LiftedStmt.def1 z (.bits n) (.sext 8 n vx)])
        | .UXTH =>
          let (z, s) := freshVarTy cur none (.bits n)
          (z, s, [LiftedStmt.def1 z (.bits n) (.zext 16 n vx)])
        | .SXTH =>
          let (z, s) := freshVarTy cur none (.bits n)
          (z, s, [LiftedStmt.def1 z (.bits n) (.sext 16 n vx)])
        | .UXTW =>
          if n == 64 then
            let (z, s) := freshVarTy cur none (.bits 64)
            (z, s, [LiftedStmt.def1 z (.bits 64) (.zext 32 64 vx)])
          else (vx, cur, [])
        | .SXTW =>
          if n == 64 then
            let (z, s) := freshVarTy cur none (.bits 64)
            (z, s, [LiftedStmt.def1 z (.bits 64) (.sext 32 64 vx)])
          else (vx, cur, [])
        | .UXTX | .SXTX => (vx, cur, [])
      if sh == 0 then pure (some ve, none, sts1, s1)
      else
        let (vs, s2) := freshVarTy s1 none (.bits n)
        let rhs := LiftedStmt.def1 vs (.bits n) (.bin n "shl" ve none (some (BitVec.ofNat 64 sh)))
        pure (some vs, none, sts1 ++ [rhs], s2)

def peekFlagCond (rest : List Instr) (termCond? : Option CondCode) : Option CondCode :=
  let rec go : List Instr → Option CondCode
    | [] => termCond?
    | ins :: tl =>
      match ins with
      | ⟨_, .CSINC _ (.low .XZR _) (.low .XZR _) cc⟩ => some cc.invert
      | ⟨_, .CSEL _ _ _ cc⟩ | ⟨_, .CSINC _ _ _ cc⟩
      | ⟨_, .CSINV _ _ _ cc⟩ | ⟨_, .CSNEG _ _ _ cc⟩ => some cc
      | ⟨_, .SUBS_e ..⟩ | ⟨_, .SUBS_s ..⟩ | ⟨_, .ADDS_e ..⟩ | ⟨_, .ADDS_s ..⟩
      | ⟨_, .ANDS_i ..⟩ | ⟨_, .ANDS_s ..⟩ | ⟨_, .ADCS ..⟩ | ⟨_, .SBCS ..⟩ => none
      | _ => go tl
  go rest

def resolveArmFlag (tag : String) (cc : CondCode) (st : LiftBlockSt)
    (tyBool : Bool := true) : Except String (Nat × List LiftedStmt × LiftBlockSt) := do
  match st.lastCmpBool? with
  | some (vPrev, ccPrev) =>
    if ccPrev == cc then return (vPrev, [], st)
  | none => pure ()
  let (la, lb?, lci?, lw) ← match st.lastCmp? with
    | some p => pure p | none => throw s!"{tag}_without_cmp"
  let co ← match condToCmpOp cc with
    | some p => pure p | none => throw s!"unsupported_{tag}_cc {repr cc}"
  let ac ← match ccToArmCond cc with
    | some a => pure a | none => throw s!"unsupported_{tag}_armcc {repr cc}"
  let (vc, s1) := if tyBool then freshVarTy st none .bool else freshVar st none
  pure (vc, [.def1 vc .bool (.cmp co lw la lb? lci?)], { s1 with flags := (vc, ac) :: s1.flags })

def liftArmBinReg (op : String) (w : Nat) (rd rn rm : XReg) (cur : LiftBlockSt) :
    Except String (List LiftedStmt × LiftBlockSt) := do
  let vn ← match getRegVar? rn cur with | some v => pure v | none => throw s!"{op}_rn"
  let vm ← match getRegVar? rm cur with | some v => pure v | none => throw s!"{op}_rm"
  let (vd, st1) := freshVarTy cur (some rd) (.bits w)
  pure ([.def1 vd (.bits w) (.bin w op vn (some vm) none)], setRegVar rd vd st1)

def liftArmBinImm (op : String) (w : Nat) (rd rn : XReg) (c : Int64) (cur : LiftBlockSt) :
    Except String (List LiftedStmt × LiftBlockSt) := do
  let va ← match getRegVar? rn cur with
    | some v => pure v | none => throw s!"{op}_i_uninit {repr rn}"
  let (vd, st1) := freshVarTy cur (some rd) (.bits w)
  pure ([.def1 vd (.bits w) (.bin w op va none (some c.toBitVec))], setRegVar rd vd st1)

def liftArmShiftBin {rw : RegWidth} (op : String) (w : Nat) (rd rn : XReg) (sr : ShiftRegExpr rw)
    (cur : LiftBlockSt) : Except String (List LiftedStmt × LiftBlockSt) := do
  let va ← match getRegVar? rn cur with
    | some v => pure v | none => throw s!"{op}_s_uninit {repr rn}"
  let (vb, sts, st1) ← emitShiftExpr sr cur
  let (vd, st2) := freshVarTy st1 (some rd) (.bits w)
  pure (sts ++ [.def1 vd (.bits w) (.bin w op va (some vb) none)], setRegVar rd vd st2)

def liftArmExtLoad (sw w : Nat) (isSext : Bool) (rd : XReg) (a : AddrExpr)
    (cur : LiftBlockSt) : Except String (List LiftedStmt × LiftBlockSt) := do
  if isSpAddr a then throw "spill_in_body: sp ext load"
  let (va, asts, st1) ← emitAddrCalc a cur
  let (vl, st2) := freshVarTy st1 (some rd) (.bits sw)
  let (vd, st3) := freshVarTy st2 (some rd) (.bits w)
  let extOp := if isSext then NOp.sext sw w vl else NOp.zext sw w vl
  pure (asts ++ [.def1 vl (.bits sw) (.load sw va), .def1 vd (.bits w) extOp],
        setRegVar rd vd (addElides [vl] st3))

def liftArmEagerFlag (rest : List Instr) (termCond? : Option CondCode) (la : Nat)
    (lb? : Option Nat) (lci? : Option (BitVec 64)) (lw : Nat) (st0 : LiftBlockSt) :
    Except String (List LiftedStmt × LiftBlockSt) := do
  match peekFlagCond rest termCond? with
  | some cc =>
    match condToCmpOp cc, ccToArmCond cc with
    | some co, some ac =>
      let (vc, st1) := freshVarTy st0 none .bool
      let st2 := { st1 with flags := (vc, ac) :: st1.flags,
                            lastCmp? := some (la, lb?, lci?, lw),
                            lastCmpBool? := some (vc, cc) }
      pure ([LiftedStmt.def1 vc .bool (.cmp co lw la lb? lci?)], st2)
    | _, _ => pure ([], { st0 with lastCmp? := some (la, lb?, lci?, lw), lastCmpBool? := none })
  | none => pure ([], { st0 with lastCmp? := some (la, lb?, lci?, lw), lastCmpBool? := none })

def liftArmAdds (rest : List Instr) (termCond? : Option CondCode) (w : Nat)
    (rd : XRegOrXzr) (va : Nat) (vb? : Option Nat) (imm? : Option (BitVec 64))
    (sts : List LiftedStmt) (st1 : LiftBlockSt) :
    Except String (List LiftedStmt × LiftBlockSt) := do
  match rd with
  | .XZR =>
    let (vd, st2) := freshVarTy st1 none (.bits w)
    let (fst, st3) ← liftArmEagerFlag rest termCond? vd none (some 0#64) w st2
    pure (sts ++ [LiftedStmt.def1 vd (.bits w) (.bin w "add" va vb? imm?)] ++ fst, st3)
  | .reg rx =>
    let (vd, st2) := freshVarTy st1 (some rx) (.bits w)
    let (vc, st3) := freshVarTy st2 none .bool
    pure (sts ++ [.def2 vd vc (.bits w) .bool (.addc w va vb? imm? none false)],
          setRegVar rx vd { st3 with lastCarry? := some vc, flags := (vc, .cs) :: st3.flags,
                                     lastCmp? := some (vd, none, some 0#64, w) })

def liftOneInstr (restIns : List Instr) (termCond? : Option CondCode) (ins : Instr)
    (cur : LiftBlockSt) : Except String (List LiftedStmt × LiftBlockSt) := do
  let ow := ins.operation_size
  let w := widthBits ow
  let eager := fun la lb? lci? lw s => liftArmEagerFlag restIns termCond? la lb? lci? lw s
  match ins with
  | ⟨_, .MOVZ (.low (.reg rd) _) (.int64 c) ms⟩ =>
    let val : BitVec 64 := (c.toBitVec &&& 0xFFFF#64) <<< movShiftNat ms
    let (vd, st1) := freshVarTy cur (some rd) (.bits w)
    pure ([.def1 vd (.bits w) (.movi w val)], setRegImm rd vd val st1)
  | ⟨_, .MOVN (.low (.reg rd) _) (.int64 c) ms⟩ =>
    let mask : BitVec 64 := if w == 32 then 0xFFFFFFFF#64 else 0xFFFFFFFFFFFFFFFF#64
    let val : BitVec 64 := (~~~((c.toBitVec &&& 0xFFFF#64) <<< movShiftNat ms)) &&& mask
    let (vd, st1) := freshVarTy cur (some rd) (.bits w)
    pure ([.def1 vd (.bits w) (.movi w val)], setRegImm rd vd val st1)
  | ⟨_, .MOVK (.low (.reg rd) _) (.int64 c) ms⟩ =>
    let sh := movShiftNat ms
    let prev := getRegImm? rd cur |>.getD 0#64
    let lo := (c.toBitVec &&& 0xFFFF#64) <<< sh
    let val : BitVec 64 := (prev &&& ~~~(0xFFFF#64 <<< sh)) ||| lo
    let (vd, st1) := freshVarTy cur (some rd) (.bits w)
    pure ([.def1 vd (.bits w) (.movi w val)], setRegImm rd vd val st1)
  | ⟨_, .LDR (.low (.reg rd) _) (.lit (.pool ⟨.int64 c⟩))⟩ =>
    let val := c.toBitVec
    let (vd, st1) := freshVarTy cur (some rd) (.bits w)
    pure ([.def1 vd (.bits w) (.movi w val)], setRegImm rd vd val st1)
  | ⟨_, .ADD_e (.low (.reg rd) _) (.low (.reg rn) _) ei⟩ =>
    let va ← match getRegVar? rn cur with
      | some v => pure v | none => throw s!"add_e_uninit {repr rn}"
    let (vb?, imm?, sts, st1) ← emitExtImm (w := ow) ei cur
    let (vd, st2) := freshVarTy st1 (some rd) (.bits w)
    let stmt := if imm? == some 0#64 && vb?.isNone then LiftedStmt.def1 vd (.bits w) (.copy w va)
                else .def1 vd (.bits w) (.bin w "add" va vb? imm?)
    pure (sts ++ [stmt], setRegVar rd vd st2)
  | ⟨_, .SUB_e (.low (.reg rd) _) (.low (.reg rn) _) ei⟩ =>
    let va ← match getRegVar? rn cur with
      | some v => pure v | none => throw s!"sub_e_uninit {repr rn}"
    let (vb?, imm?, sts, st1) ← emitExtImm (w := ow) ei cur
    let (vd, st2) := freshVarTy st1 (some rd) (.bits w)
    pure (sts ++ [.def1 vd (.bits w) (.bin w "sub" va vb? imm?)], setRegVar rd vd st2)
  | ⟨_, .ADD_s (.low (.reg rd) _) (.low rn _) sr⟩ =>
    let (vb, sts, st1) ← emitShiftExpr sr cur
    let (vd, st2) := freshVarTy st1 (some rd) (.bits w)
    match rn with
    | .XZR => pure (sts ++ [.def1 vd (.bits w) (.copy w vb)], setRegVar rd vd st2)
    | .reg rx =>
      let va ← match getRegVar? rx cur with
        | some v => pure v | none => throw s!"add_s_uninit {repr rx}"
      pure (sts ++ [.def1 vd (.bits w) (.bin w "add" va (some vb) none)], setRegVar rd vd st2)
  | ⟨_, .SUB_s (.low (.reg rd) _) (.low rn _) sr⟩ =>
    let (vb, sts, st1) ← emitShiftExpr sr cur
    let (vd, st2) := freshVarTy st1 (some rd) (.bits w)
    match rn with
    | .XZR => pure (sts ++ [.def1 vd (.bits w) (.un w "neg" vb)], setRegVar rd vd st2)
    | .reg rx =>
      let va ← match getRegVar? rx cur with
        | some v => pure v | none => throw s!"sub_s_uninit {repr rx}"
      pure (sts ++ [.def1 vd (.bits w) (.bin w "sub" va (some vb) none)], setRegVar rd vd st2)
  | ⟨_, .ADDS_e (.low rd _) (.low (.reg rn) _) ei⟩ =>
    let va ← match getRegVar? rn cur with
      | some v => pure v | none => throw s!"adds_e_uninit {repr rn}"
    let (vb?, imm?, sts, st1) ← emitExtImm (w := ow) ei cur
    liftArmAdds restIns termCond? w rd va vb? imm? sts st1
  | ⟨_, .ADDS_s (.low rd _) (.low rn _) sr⟩ =>
    let (vb, sts, st1) ← emitShiftExpr sr cur
    let va ← match rn with
      | .reg rx => match getRegVar? rx cur with | some v => pure v | none => throw "adds_s_uninit"
      | .XZR => throw "adds_s_xzr"
    liftArmAdds restIns termCond? w rd va (some vb) none sts st1
  | ⟨_, .SUBS_e (.low rd _) (.low (.reg rn) _) ei⟩ =>
    let va ← match getRegVar? rn cur with
      | some v => pure v | none => throw s!"cmp_e_uninit {repr rn}"
    let (vb?, imm?, sts, st1) ← emitExtImm (w := ow) ei cur
    match rd with
    | .XZR =>
      let (fst, st2) ← eager va vb? imm? w st1
      pure (sts ++ fst, st2)
    | .reg rx =>
      let (vd, st2) := freshVarTy st1 (some rx) (.bits w)
      let (fst, st3) ← eager vd none (some 0#64) w st2
      pure (sts ++ [LiftedStmt.def1 vd (.bits w) (.bin w "sub" va vb? imm?)] ++ fst,
            setRegVar rx vd st3)
  | ⟨_, .SUBS_s (.low rd _) (.low rn _) sr⟩ =>
    let (vb, sts, st1) ← emitShiftExpr sr cur
    match rn with
    | .XZR =>
      match rd with
      | .XZR =>
        let (fst, st2) ← eager vb none (some 0#64) w st1
        pure (sts ++ fst, st2)
      | .reg rx =>
        let (vd, st2) := freshVarTy st1 (some rx) (.bits w)
        let (fst, st3) ← eager vd none (some 0#64) w st2
        pure (sts ++ [LiftedStmt.def1 vd (.bits w) (.un w "neg" vb)] ++ fst,
              setRegVar rx vd st3)
    | .reg rxn =>
      let va ← match getRegVar? rxn cur with
        | some v => pure v | none => throw s!"cmp_s_uninit {repr rxn}"
      match rd with
      | .XZR =>
        let (fst, st2) ← eager va (some vb) none w st1
        pure (sts ++ fst, st2)
      | .reg rx =>
        let (vd, st2) := freshVarTy st1 (some rx) (.bits w)
        let (fst, st3) ← eager vd none (some 0#64) w st2
        pure (sts ++ [LiftedStmt.def1 vd (.bits w) (.bin w "sub" va (some vb) none)] ++ fst,
              setRegVar rx vd st3)
  | ⟨_, .ADC (.low (.reg rd) _) (.low (.reg rn) _) (.low (.reg rm) _)⟩ =>
    let va ← match getRegVar? rn cur with | some v => pure v | none => throw "adc_uninit"
    let vb ← match getRegVar? rm cur with | some v => pure v | none => throw "adc_rhs_uninit"
    let (vd, st1) := freshVarTy cur (some rd) (.bits w)
    let (vc, st2) := freshVarTy st1 none .bool
    pure ([.def2 vd vc (.bits w) .bool (.addc w va (some vb) none cur.lastCarry? false)],
          setRegVar rd vd { st2 with lastCarry? := some vc })
  | ⟨_, .ORR_s (.low (.reg rd) _) (.low rn _) sr⟩ =>
    let (vb, sts, st1) ← emitShiftExpr sr cur
    let (vd, st2) := freshVarTy st1 (some rd) (.bits w)
    match rn with
    | .XZR => pure (sts ++ [.def1 vd (.bits w) (.copy w vb)], setRegVar rd vd st2)
    | .reg rx =>
      let va ← match getRegVar? rx cur with
        | some v => pure v | none => throw s!"orr_uninit {repr rx}"
      pure (sts ++ [.def1 vd (.bits w) (.bin w "or" va (some vb) none)], setRegVar rd vd st2)
  | ⟨_, .ORN_s (.low (.reg rd) _) (.low .XZR _) sr⟩ =>
    let (vb, sts, st1) ← emitShiftExpr sr cur
    let (vd, st2) := freshVarTy st1 (some rd) (.bits w)
    pure (sts ++ [.def1 vd (.bits w) (.un w "not" vb)], setRegVar rd vd st2)
  | ⟨_, .AND_s (.low (.reg rd) _) (.low (.reg rn) _) sr⟩ => liftArmShiftBin "and" w rd rn sr cur
  | ⟨_, .EOR_s (.low (.reg rd) _) (.low (.reg rn) _) sr⟩ => liftArmShiftBin "xor" w rd rn sr cur
  | ⟨_, .ANDS_s (.low rd _) (.low (.reg rn) _) sr⟩ =>
    let va ← match getRegVar? rn cur with
      | some v => pure v | none => throw s!"tst_s_uninit {repr rn}"
    let (vb, sts, st1) ← emitShiftExpr sr cur
    let (vt, st2) := freshVarTy st1 none (.bits w)
    let (fst, st3) ← eager vt none (some 0#64) w st2
    pure (sts ++ [.def1 vt (.bits w) (.bin w "and" va (some vb) none)] ++ fst,
          match rd with | .XZR => st3 | .reg rx => setRegVar rx vt st3)
  | ⟨_, .AND_i (.low (.reg rd) _) (.low (.reg rn) _) (.int64 c)⟩ =>
    liftArmBinImm "and" w rd rn c cur
  | ⟨_, .EOR_i (.low (.reg rd) _) (.low (.reg rn) _) (.int64 c)⟩ =>
    liftArmBinImm "xor" w rd rn c cur
  | ⟨_, .ORR_i (.low (.reg rd) _) (.low rn _) (.int64 c)⟩ =>
    let (vd, st1) := freshVarTy cur (some rd) (.bits w)
    match rn with
    | .XZR => pure ([.def1 vd (.bits w) (.movi w c.toBitVec)], setRegImm rd vd c.toBitVec st1)
    | .reg rx =>
      let va ← match getRegVar? rx cur with
        | some v => pure v | none => throw s!"orr_i_uninit {repr rx}"
      pure ([.def1 vd (.bits w) (.bin w "or" va none (some c.toBitVec))], setRegVar rd vd st1)
  | ⟨_, .SBCS (.low (.reg rd) _) (.low (.reg rxn) _) (.low (.reg rxm) _)⟩ =>
    let vn ← match getRegVar? rxn cur with | some v => pure v | none => throw "sbcs_rn"
    let vm ← match getRegVar? rxm cur with | some v => pure v | none => throw "sbcs_rm"
    let (vd, st1) := freshVarTy cur (some rd) (.bits w)
    pure ([.def1 vd (.bits w) (.bin w "sub" vn (some vm) none)],
          setRegVar rd vd { st1 with lastCmp? := some (vd, none, some 0#64, w) })
  | ⟨_, .ANDS_i (.low rd _) (.low (.reg rn) _) (.int64 c)⟩ =>
    let va ← match getRegVar? rn cur with
      | some v => pure v | none => throw s!"tst_i_uninit {repr rn}"
    let (vt, st1) := freshVarTy cur none (.bits w)
    let (fst, st2) ← eager vt none (some 0#64) w st1
    pure ([LiftedStmt.def1 vt (.bits w) (.bin w "and" va none (some c.toBitVec))] ++ fst,
          match rd with | .XZR => st2 | .reg rx => setRegVar rx vt st2)
  | ⟨_, .MADD (.low (.reg rd) _) (.low (.reg rn) _) (.low (.reg rm) _) (.low ra _)⟩ =>
    let vn ← match getRegVar? rn cur with | some v => pure v | none => throw "madd_rn"
    let vm ← match getRegVar? rm cur with | some v => pure v | none => throw "madd_rm"
    let (vp, st1) := freshVarTy cur (some rd) (.bits w)
    match ra with
    | .XZR => pure ([.def1 vp (.bits w) (.bin w "mul" vn (some vm) none)], setRegVar rd vp st1)
    | .reg rxa =>
      let va ← match getRegVar? rxa st1 with | some v => pure v | none => throw "madd_ra"
      let (vd, st2) := freshVarTy st1 (some rd) (.bits w)
      pure ([.def1 vp (.bits w) (.bin w "mul" vn (some vm) none),
             .def1 vd (.bits w) (.bin w "add" vp (some va) none)], setRegVar rd vd st2)
  | ⟨_, .MSUB (.low (.reg rd) _) (.low (.reg rn) _) (.low (.reg rm) _) (.low (.reg rxa) _)⟩ =>
    let vn ← match getRegVar? rn cur with | some v => pure v | none => throw "msub_rn"
    let vm ← match getRegVar? rm cur with | some v => pure v | none => throw "msub_rm"
    let va ← match getRegVar? rxa cur with | some v => pure v | none => throw "msub_ra"
    let (vp, st1) := freshVarTy cur none (.bits w)
    let (vd, st2) := freshVarTy st1 (some rd) (.bits w)
    pure ([.def1 vp (.bits w) (.bin w "mul" vn (some vm) none),
           .def1 vd (.bits w) (.bin w "sub" va (some vp) none)], setRegVar rd vd st2)
  | ⟨_, .UDIV (.low (.reg rd) _) (.low (.reg rn) _) (.low (.reg rm) _)⟩ =>
    liftArmBinReg "udiv" w rd rn rm cur
  | ⟨_, .SDIV (.low (.reg rd) _) (.low (.reg rn) _) (.low (.reg rm) _)⟩ =>
    liftArmBinReg "sdiv" w rd rn rm cur
  | ⟨_, .LSLV (.low (.reg rd) _) (.low (.reg rn) _) (.low (.reg rm) _)⟩ =>
    liftArmBinReg "shl" w rd rn rm cur
  | ⟨_, .LSRV (.low (.reg rd) _) (.low (.reg rn) _) (.low (.reg rm) _)⟩ =>
    liftArmBinReg "lshr" w rd rn rm cur
  | ⟨_, .ASRV (.low (.reg rd) _) (.low (.reg rn) _) (.low (.reg rm) _)⟩ =>
    liftArmBinReg "ashr" w rd rn rm cur
  | ⟨_, .UBFM (.low (.reg rd) _) (.low (.reg rn) _) immr imms⟩ =>
    let vn ← match getRegVar? rn cur with
      | some v => pure v | none => throw s!"ubfm_rn {repr rn}"
    let (vd, st1) := freshVarTy cur (some rd) (.bits w)
    if imms == w - 1 then
      let stmt := if immr == 0 then LiftedStmt.def1 vd (.bits w) (.copy w vn)
                  else .def1 vd (.bits w) (.bin w "lshr" vn none (some (BitVec.ofNat 64 immr)))
      pure ([stmt], setRegVar rd vd st1)
    else if immr == 0 && (imms == 7 || imms == 15 || imms == 31) then
      let sw := imms + 1
      let (vt, st0) := freshVarTy cur none (.bits sw)
      let (vd', st1') := freshVarTy st0 (some rd) (.bits w)
      pure ([.def1 vt (.bits sw) (.trunc w sw vn), .def1 vd' (.bits w) (.zext sw w vt)],
            setRegVar rd vd' (addElides [vt] st1'))
    else if imms + 1 < w && immr == imms + 1 then
      pure ([.def1 vd (.bits w) (.bin w "shl" vn none (some (BitVec.ofNat 64 (w - immr))))],
            setRegVar rd vd st1)
    else if imms >= immr then
      let mask := ((1#64 <<< (imms - immr + 1)) - 1#64)
      let (vs, s0, preSts) := if immr == 0 then (vn, cur, [])
        else
          let (t, s) := freshVarTy cur none (.bits w)
          (t, s, [.def1 t (.bits w) (.bin w "lshr" vn none (some (BitVec.ofNat 64 immr)))])
      let (vd', st1') := freshVarTy s0 (some rd) (.bits w)
      pure (preSts ++ [.def1 vd' (.bits w) (.bin w "and" vs none (some mask))],
            setRegVar rd vd' st1')
    else throw s!"unsupported_ubfm {immr} {imms}"
  | ⟨_, .SBFM (.low (.reg rd) _) (.low (.reg rn) _) immr imms⟩ =>
    let vn ← match getRegVar? rn cur with
      | some v => pure v | none => throw s!"sbfm_rn {repr rn}"
    if imms == w - 1 then
      let (vd, st1) := freshVarTy cur (some rd) (.bits w)
      pure ([.def1 vd (.bits w) (.bin w "ashr" vn none (some (BitVec.ofNat 64 immr)))],
            setRegVar rd vd st1)
    else if immr == 0 && (imms == 7 || imms == 15 || imms == 31) then
      let sw := imms + 1
      let (vt, st0) := freshVarTy cur none (.bits sw)
      let (vd, st1) := freshVarTy st0 (some rd) (.bits w)
      pure ([.def1 vt (.bits sw) (.trunc w sw vn), .def1 vd (.bits w) (.sext sw w vt)],
            setRegVar rd vd (addElides [vt] st1))
    else throw s!"unsupported_sbfm {immr} {imms}"
  | ⟨_, .CSINC (.low (.reg rd) _) (.low .XZR _) (.low .XZR _) cc⟩ =>
    let (vc, cmpSts, st2) ← resolveArmFlag "cset" cc.invert cur
    let (vd, st3) := freshVarTy st2 (some rd) (.bits w)
    pure (cmpSts ++ [LiftedStmt.def1 vd (.bits w) (.ofBool w vc)], setRegVar rd vd st3)
  | ⟨_, .CSEL (.low (.reg rd) _) (.low (.reg rn) _) (.low (.reg rm) _) cc⟩ =>
    let vn ← match getRegVar? rn cur with | some v => pure v | none => throw "csel_rn"
    let vm ← match getRegVar? rm cur with | some v => pure v | none => throw "csel_rm"
    let (vc, cmpSts, st2) ← resolveArmFlag "csel" cc cur
    let (vd, st3) := freshVarTy st2 (some rd) (.bits w)
    pure (cmpSts ++ [LiftedStmt.def1 vd (.bits w) (.select w vc vn vm)], setRegVar rd vd st3)
  | ⟨_, .LDR (.low (.reg rd) _) (.addr a)⟩ =>
    if isSpAddr a then throw "spill_in_body: sp ldr"
    let (va, asts, st1) ← emitAddrCalc a cur
    let (vd, st2) := freshVarTy st1 (some rd) (.bits w)
    pure (asts ++ [.def1 vd (.bits w) (.load w va)], setRegVar rd vd st2)
  | ⟨_, .STR (.low (.reg rs) _) a⟩ =>
    if isSpAddr a then throw "spill_in_body: sp str"
    let vs ← match getRegVar? rs cur with | some v => pure v | none => throw "str_uninit"
    let (va, asts, st1) ← emitAddrCalc a cur
    pure (asts ++ [.def1 0 (.bits w) (.store w vs va)], st1)
  | ⟨.W32, .LDRB (.low (.reg rd) _) a⟩ => liftArmExtLoad 8 32 false rd a cur
  | ⟨.W32, .STRB (.low (.reg rs) _) a⟩ =>
    if isSpAddr a then throw "spill_in_body: sp strb"
    let vs ← match getRegVar? rs cur with | some v => pure v | none => throw "strb_uninit"
    let (va, asts, st1) ← emitAddrCalc a cur
    pure (asts ++ [.def1 0 (.bits 8) (.store 8 vs va)], st1)
  | ⟨.W32, .LDRH (.low (.reg rd) _) a⟩ => liftArmExtLoad 16 32 false rd a cur
  | ⟨.W32, .STRH (.low (.reg rs) _) a⟩ =>
    if isSpAddr a then throw "spill_in_body: sp strh"
    let vs ← match getRegVar? rs cur with | some v => pure v | none => throw "strh_uninit"
    let (va, asts, st1) ← emitAddrCalc a cur
    pure (asts ++ [.def1 0 (.bits 16) (.store 16 vs va)], st1)
  | ⟨.W64, .LDRSW (.low (.reg rd) _) (.addr a)⟩ => liftArmExtLoad 32 64 true rd a cur
  | ⟨_, .LDUR (.low (.reg rd) _) u⟩ =>
    let (va, asts, st1) ← emitUnscaledAddrCalc u cur
    let (vd, st2) := freshVarTy st1 (some rd) (.bits w)
    pure (asts ++ [.def1 vd (.bits w) (.load w va)], setRegVar rd vd st2)
  | ⟨_, .STUR (.low (.reg rs) _) u⟩ =>
    let vs ← match getRegVar? rs cur with | some v => pure v | none => throw "stur_uninit"
    let (va, asts, st1) ← emitUnscaledAddrCalc u cur
    pure (asts ++ [.def1 0 (.bits w) (.store w vs va)], st1)
  | ⟨.W64, .UMULH (.low (.reg rd) _) (.low (.reg rn) _) (.low (.reg rm) _)⟩ =>
    let vn ← match getRegVar? rn cur with | some v => pure v | none => throw "umulh_rn"
    let vm ← match getRegVar? rm cur with | some v => pure v | none => throw "umulh_rm"
    let (vlo, st1) := freshVarTy cur none (.bits 64)
    let (vhi, st2) := freshVarTy st1 (some rd) (.bits 64)
    pure ([.def2 vlo vhi (.bits 64) (.bits 64) (.umulw 64 vn vm)], setRegVar rd vhi st2)
  | _ => throw s!"unsupported_instr: {Kraken.AArch64.Print.instr ins}"

def liftInstrs (insns : List Instr) (st : LiftBlockSt) (termCond? : Option CondCode := none) :
    Except String (List LiftedStmt × LiftBlockSt) := do
  let mut cur := st
  let mut out : List LiftedStmt := []
  for idx in List.range insns.length do
    let (sts, cur') ← liftOneInstr (insns.drop (idx + 1)) termCond? insns[idx]! cur
    out := out ++ sts
    cur := cur'
  pure (out, cur)

def addrXRegs (a : AddrExpr) : List XReg :=
  (match a.base with | .low (.reg r) _ => [r] | _ => []) ++
  (match a.off with | .reg mr => (match mr.reg.2 with | .low (.reg r) _ => [r] | _ => []) | _ => [])

def uaddrXRegs (u : UnscaledAddrExpr) : List XReg :=
  match u.base with | .low (.reg r) _ => [r] | _ => []

def instrRegsReadWritten (i : Instr) : List XReg × List XReg :=
  let zrX {w : RegWidth} : RegOrZr w → List XReg | .low (.reg x) _ => [x] | _ => []
  let spX {w : RegWidth} : RegOrSp w → List XReg | .low (.reg x) _ => [x] | _ => []
  let eiX : ExtOrImmReg → List XReg
    | .ext e => (match e.reg.2 with | .low (.reg x) _ => [x] | _ => []) | _ => []
  let shX {w : RegWidth} : ShiftRegExpr w → List XReg | sr => zrX sr.reg
  match i with
  | ⟨_, .ADD_e d a b⟩ | ⟨_, .SUB_e d a b⟩ => (spX a ++ eiX b, spX d)
  | ⟨_, .ADDS_e d a b⟩ | ⟨_, .SUBS_e d a b⟩ => (spX a ++ eiX b, zrX d)
  | ⟨_, .ADD_s d a b⟩ | ⟨_, .SUB_s d a b⟩ | ⟨_, .ADDS_s d a b⟩ | ⟨_, .SUBS_s d a b⟩
  | ⟨_, .ORR_s d a b⟩ | ⟨_, .ORN_s d a b⟩ | ⟨_, .AND_s d a b⟩ | ⟨_, .ANDS_s d a b⟩
  | ⟨_, .EOR_s d a b⟩ =>
    (zrX a ++ shX b, zrX d)
  | ⟨_, .AND_i d a _⟩ | ⟨_, .ORR_i d a _⟩ | ⟨_, .EOR_i d a _⟩ => (zrX a, spX d)
  | ⟨_, .ANDS_i d a _⟩ => (zrX a, zrX d)
  | ⟨_, .ADC d a b⟩ | ⟨_, .ADCS d a b⟩ | ⟨_, .SBC d a b⟩ | ⟨_, .SBCS d a b⟩
  | ⟨_, .UDIV d a b⟩ | ⟨_, .SDIV d a b⟩ | ⟨_, .LSLV d a b⟩
  | ⟨_, .LSRV d a b⟩ | ⟨_, .ASRV d a b⟩ | ⟨_, .RORV d a b⟩
  | ⟨_, .CSEL d a b _⟩ | ⟨_, .CSINC d a b _⟩ | ⟨_, .CSINV d a b _⟩ | ⟨_, .CSNEG d a b _⟩ =>
    (zrX a ++ zrX b, zrX d)
  | ⟨_, .MADD d a b c⟩ | ⟨_, .MSUB d a b c⟩ => (zrX a ++ zrX b ++ zrX c, zrX d)
  | ⟨_, .UBFM d a _ _⟩ | ⟨_, .SBFM d a _ _⟩ | ⟨_, .CLZ d a⟩ | ⟨_, .CLS d a⟩
  | ⟨_, .RBIT d a⟩ | ⟨_, .REV d a⟩ | ⟨_, .REV16 d a⟩ => (zrX a, zrX d)
  | ⟨_, .MOVZ d _ _⟩ | ⟨_, .MOVN d _ _⟩ => ([], zrX d)
  | ⟨_, .MOVK d _ _⟩ => (zrX d, zrX d)
  | ⟨_, .LDR d (.addr a)⟩ | ⟨.W32, .LDRB d a⟩ | ⟨.W32, .LDRH d a⟩
  | ⟨_, .LDRSB d a⟩ | ⟨_, .LDRSH d a⟩ | ⟨.W64, .LDRSW d (.addr a)⟩ => (addrXRegs a, zrX d)
  | ⟨_, .LDR d (.lit _)⟩ | ⟨.W64, .LDRSW d (.lit _)⟩ => ([], zrX d)
  | ⟨_, .STR r a⟩ | ⟨.W32, .STRB r a⟩ | ⟨.W32, .STRH r a⟩ => (zrX r ++ addrXRegs a, [])
  | ⟨_, .LDUR d u⟩ | ⟨.W32, .LDURB d u⟩ | ⟨.W32, .LDURH d u⟩
  | ⟨_, .LDURSB d u⟩ | ⟨_, .LDURSH d u⟩ | ⟨.W64, .LDURSW d u⟩ => (uaddrXRegs u, zrX d)
  | ⟨_, .STUR r u⟩ | ⟨.W32, .STURB r u⟩ | ⟨.W32, .STURH r u⟩ => (zrX r ++ uaddrXRegs u, [])
  | ⟨_, .CBZ (.low (.reg x) _) _⟩ | ⟨_, .CBNZ (.low (.reg x) _) _⟩
  | ⟨_, .TBZ (.low (.reg x) _) _ _⟩ | ⟨_, .TBNZ (.low (.reg x) _) _ _⟩ => ([x], [])
  | ⟨.W64, .UMULH d a b⟩ | ⟨.W64, .SMULH d a b⟩ => (zrX a ++ zrX b, zrX d)
  | _ => ([], [])

def armTermUses : CfgTerm BranchCond → List XReg
  | .jcc (.cbz _ r) _ _ | .jcc (.cbnz _ r) _ _
  | .jcc (.tbz _ r _) _ _ | .jcc (.tbnz _ r _) _ _ => [r]
  | _ => []

def computeLiveInRegs (blocks : List CfgBlock) (retRegs : List XReg) :
    List (String × List XReg) :=
  computeLiveInRegsGen armTermUses instrRegsReadWritten isScratchXReg blocks retRegs

def armLowerJcc (bc : BranchCond) (stAfter : LiftBlockSt) :
    Except String (List LiftedStmt × Nat × LiftBlockSt) := do
  let emitBitTest (co : CmpOp) (tag : String) (rw : RegWidth) (r : XReg) (bit : Nat) :
      Except String (List LiftedStmt × Nat × LiftBlockSt) := do
    let vr ← match getRegVar? r stAfter with
      | some v => pure v | none => throw s!"{tag}_uninit {repr r}"
    let n := widthBits rw
    let (vt, s0) := freshVarTy stAfter none (.bits n)
    let (vc, s1) := freshVar s0 none
    pure ([.def1 vt (.bits n) (.bin n "and" vr none (some (1#64 <<< bit))),
           .def1 vc .bool (.cmp co n vt none (some 0#64))], vc, s1)
  let emitZeroTest (co : CmpOp) (tag : String) (rw : RegWidth) (r : XReg) :
      Except String (List LiftedStmt × Nat × LiftBlockSt) := do
    let vr ← match getRegVar? r stAfter with
      | some v => pure v | none => throw s!"{tag}_uninit {repr r}"
    let (vc, s1) := freshVar stAfter none
    pure ([.def1 vc .bool (.cmp co (widthBits rw) vr none (some 0#64))], vc, s1)
  match bc with
  | .flags cc =>
    let (vc, sts, st1) ← resolveArmFlag "jcc" cc stAfter false
    pure (sts, vc, st1)
  | .cbz rw r => emitZeroTest .eq "cbz" rw r
  | .cbnz rw r => emitZeroTest .ne "cbnz" rw r
  | .tbz rw r bit => emitBitTest .eq "tbz" rw r bit
  | .tbnz rw r bit => emitBitTest .ne "tbnz" rw r bit

def armLiftHooks :
    LiftHooks armIsa ADir XReg Instr BranchCond CondCode :=
  { stripFrame := fun dirs => stripPrologueEpilogue dirs
    toCfg := fun d s => toCfgBlocks d s
    argLiveRegs := fun n =>
      armFrame.argRegs.take n |>.filterMap fun | .reg x => some x | _ => none
    retLiveRegs := fun n =>
      armFrame.retRegs.take n |>.filterMap fun | .reg x => some x | _ => none
    toIsaReg := XRegOrSp.reg
    termUses := armTermUses
    instrRW := instrRegsReadWritten
    skipReg := isScratchXReg
    reprLR := fun r => toString (repr r)
    liftBlock := fun b st =>
      let tCond? := match b.term with | .jcc (.flags cc) _ _ => some cc | _ => none
      liftInstrs b.instrs st tCond?
    lowerJcc := armLowerJcc }

/-- Lift Arm64 directives into a `LiftedSnippet Reg ArmCond rs` plus mapped `RelHints`. -/
def liftSnippetU (name : Sym) (as rs : List Ty) (dirs : List ADir) :
    Except String (LiftedSnippet Reg ArmCond rs) :=
  liftSnippetUGen armLiftHooks name as rs dirs

/-- Output bundle of end-to-end Arm64 lifting + self-round-trip check (`LiftResultArm64.fn` projects
the `Fn`). -/
abbrev LiftResultArm64 := LiftResult armIsa

/-- Materialize the `Fn` of a `LiftResultArm64`. -/
def LiftResultArm64.fn (r : LiftResultArm64) : Fn := LiftResult.fn r

/-- Full untrusted Arm64 directive lifting + `solveRelHints` + standalone `Rega.lowerFn` +
`checkAsmIso` round-trip check. -/
def liftSnippet (name : Sym) (as rs : List Ty) (dirs : List ADir)
    (avoidRegs : List Reg := []) : Except String LiftResultArm64 :=
  liftSnippetGen armLiftHooks (fun a b s p => checkAsmIso a b s p)
    name as rs dirs avoidRegs

/-- Parse Arm64 assembly text and lift via `liftSnippet` (`IO` convenience wrapper). -/
def liftSnippetAsm (name : Sym) (as rs : List Ty) (asmText : String)
    (avoidRegs : List Reg := []) : IO (Except String LiftResultArm64) := do
  let dirs ← Kraken.AArch64.Parser.parse asmText
  pure (liftSnippet name as rs dirs avoidRegs)

/-- Combined `Rega.lowerFn` + `@predictable` static `SnippetBudget` audit on Arm64. -/
def checkRegaAndBudget (sDirect outerLate : Fn) (hOuter : armIsa.Hints)
    (budget : SnippetBudget := {}) : Except (List SnippetDiag) (List ADir × BudgetReport) :=
  lowerAndCheckBudget armIsa sDirect outerLate hOuter budget
    (some fun ds => (profileDirs ds true).bodyInsns)

end LeanQbe.T.Arm64
