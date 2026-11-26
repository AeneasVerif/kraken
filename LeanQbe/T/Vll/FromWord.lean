module

public import LeanQbe.T.Vll.Sem
public import LeanQbe.T.Unified.CfgContify

/-!
# Target-Neutral `BedrockWord` L0 → `BedrockMach` L1 (`Vll.FromWord`)

Architecture-parametric (`A : Arch`) lowering from `BedrockWord` L0 `CodeMap`s (both plain open
`.ijmp` programs and witness-checked Stage-1 `ContifyWitness` regions with `PrivFrameCfg` and
dual-return contification) into `BedrockMach` L1 `VllCodeMap A`:

* `WordRegBind A` / `WordRegBind.Wf`: fixed 6-register L0 binding (`sp, rp, rv, r1, r2, r3`)
  onto distinct non-SP, non-scratch, non-RA GPRs, plus dual-return flag register `altRet`, three
  working temporaries `w0, w1, w2`, optional local temp pool `tmps`, hardware landing-pad kind
  `padKind`, and verified condition mapping `condOfCmp?`.
* `fromWord`: open L0 → `VllCodeMap A` preserving entry addresses (`addrTaken`, `Instr.pad`),
  evaluating scalar/boolean `BlockFlat` expressions into `tmps` + hardware frame slots, breaking
  register permutation cycles cleanly via `parMove`, and terminating with `Term.ijmp` / `Term.halt`.
* `fromWordContify`: Stage-1 contification + `PrivFrameCfg` lowering translating promoted private
  slots (`[sp - 8*(k+1)]`) to hardware `.slotSt`/`.slotLd`, `.contCall` / `.contRet` into native
  hardware `.call` / `.ret` (RAS/CET/PAC-safe without forging `rp` in memory), dual returns into
  `altRet` + `.jnzGpr`, and residual `wRes` / `.bailout` blocks into padded `.ijmp` code.

Zero `Arm64`, `Amd64`, `Kraken.X64`, `Kraken.AArch64`, or `*Lemmas*` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T
open LeanQbe.T.BedrockWord
open LeanQbe.T.Unified

/-! ## §1. Architecture-Parametric Word Register Binding (`WordRegBind`) -/

/-- Target-neutral binding of `BedrockWord` L0's 6 word registers and lowering scratch state
onto an abstract `A : Arch`. -/
structure WordRegBind (A : Arch) : Type where
  sp : A.Reg
  rp : A.Reg
  rv : A.Reg
  r1 : A.Reg
  r2 : A.Reg
  r3 : A.Reg
  /-- GPR carrying boolean alternate-return bit (`0#64`/`1#64`) across dual-return `ret`. -/
  altRet : A.Reg
  /-- Dedicated working GPRs disjoint from `wordRegs`, `altRet`, `tmps`, `sp`, `scratch`, `ra`. -/
  w0 : A.Reg
  w1 : A.Reg
  w2 : A.Reg
  /-- Fast GPR pool allocated to SSA locals before spilling to hardware stack slots. -/
  tmps : List A.Reg := []
  /-- Hardware indirect-branch landing pad emitted at escaped `addrTaken` entries. -/
  padKind : PadKind := .endbr
  /-- Map typed `CmpOp` onto an architectural condition matching `A.cmpFlags`. -/
  condOfCmp? : CmpOp → Option A.Cond

/-- The 6 bound L0 boundary GPRs in canonical order `[sp, rp, rv, r1, r2, r3]`. -/
@[expose] def WordRegBind.wordRegs {A : Arch} (b : WordRegBind A) : List A.Reg :=
  [b.sp, b.rp, b.rv, b.r1, b.r2, b.r3]

/-- The 4 working/ABI GPRs `[altRet, w0, w1, w2]`. -/
@[expose] def WordRegBind.workRegs {A : Arch} (b : WordRegBind A) : List A.Reg :=
  [b.altRet, b.w0, b.w1, b.w2]

/-- All architectural GPRs managed by `b`. -/
@[expose] def WordRegBind.allRegs {A : Arch} (b : WordRegBind A) : List A.Reg :=
  b.wordRegs ++ b.workRegs ++ b.tmps

/-- L0 boundary GPR corresponding to de Bruijn level `lvl < 6`. -/
@[expose] def WordRegBind.regAt {A : Arch} (b : WordRegBind A) : Nat → A.Reg
  | 0 => b.sp
  | 1 => b.rp
  | 2 => b.rv
  | 3 => b.r1
  | 4 => b.r2
  | _ => b.r3

/-- Well-formedness and ABI soundness obligations for `WordRegBind A`. -/
structure WordRegBind.Wf {A : Arch} (b : WordRegBind A) : Prop where
  allRegs_nodup : b.allRegs.Nodup
  no_sp : ∀ r ∈ b.allRegs, r ≠ A.abi.sp
  no_scratch : ∀ r ∈ b.allRegs, r ∉ A.abi.scratch
  no_ra : ∀ r ∈ b.allRegs, r ∉ A.abi.raRegs
  abi_word : ∀ r ∈ b.wordRegs, r ∈ A.abi.argRegs ∨ r ∈ A.abi.calleeSaved
  cond_sound : ∀ (o : CmpOp) (cc : A.Cond) (w : Width) (x y : BitVec w.bits) (f : A.Flags),
    b.condOfCmp? o = some cc → A.evalCond (A.cmpFlags w x y f) cc = o.evalBits x y

/-- Computable boolean check covering the structural disjointness fields of `WordRegBind.Wf`. -/
@[expose] def WordRegBind.checkStruct {A : Arch} (b : WordRegBind A) : Bool :=
  listNodup b.allRegs &&
  b.allRegs.all fun r =>
    (r != A.abi.sp) && (!A.abi.scratch.contains r) && (!A.abi.raRegs.contains r) &&
    (!b.wordRegs.contains r || A.abi.argRegs.contains r || A.abi.calleeSaved.contains r)

/-! ## §2. Storage Allocation, Parallel Register Transfer, and Op Lowering -/

/-- Location assigned to a de Bruijn SSA variable level inside a `BlockFlat`. -/
inductive WordLoc (A : Arch) : Type where
  | gpr (r : A.Reg)
  | slot (k : Nat)
  deriving DecidableEq

/-- Map de Bruijn level `lvl` (`0` = L0 `sp`, ..., `5` = L0 `r3`, `≥ 6` = local) to `WordLoc`. -/
@[expose] def locOf {A : Arch} (b : WordRegBind A) (spillBase : Nat) (lvl : Nat) : WordLoc A :=
  if lvl < 6 then .gpr (b.regAt lvl)
  else
    let i := lvl - 6
    match b.tmps[i]? with
    | some r => .gpr r
    | none => .slot (spillBase + (i - b.tmps.length))

/-- Maximum SSA variable depth `d` reached anywhere inside `bf`, starting from depth `d`. -/
@[expose] def maxBlockDepth : BlockFlat → Nat → Nat
  | .let_ (ts := ts) _ k, d => maxBlockDepth k (d + ts.length)
  | .load _ _ k, d => maxBlockDepth k (d + 1)
  | .store _ _ k, d => maxBlockDepth k d
  | .codeAddr _ k, d => maxBlockDepth k (d + 1)
  | .jnz _ t e, d => Nat.max (maxBlockDepth t d) (maxBlockDepth e d)
  | .ijmp _ _, d => d
  | .halt _, d => d
  | .hlt, d => d

/-- Number of hardware spill slots required for a block reaching depth `dMax`. -/
@[expose] def tempSpillCount {A : Arch} (b : WordRegBind A) (dMax : Nat) : Nat :=
  (dMax - 6) - b.tmps.length

/-- Extract 64-bit word encoding for a typed L0 scalar constant `Val t`. -/
@[expose] def immToBitVec64 : (t : Ty) → Val t → Option (BitVec 64)
  | .bool, c => some (if c then 1#64 else 0#64)
  | .bits n, v => if _ : n ≤ 64 then some (v.setWidth 64) else none
  | _, _ => none

/-- Low `n`-bit mask in 64 bits (`n ∈ {8, 16, 32, 64}`). -/
@[expose] def maskOfBits64 (n : Nat) : BitVec 64 :=
  if n == 64 then 0xFFFFFFFFFFFFFFFF#64 else (1#64 <<< n) - 1#64

/-- Architectural scalar load/store width corresponding to `t : Ty`. -/
@[expose] def tyToWidth? : Ty → Option Width
  | .bool => some .w8
  | .bits n => Width.ofBits? n
  | _ => none

/-- Resolve an L0 `Arg K t` into a GPR (returning instructions + resulting GPR, using `tmp`). -/
@[expose] def loadArgToGpr {A : Arch} (b : WordRegBind A) (spillBase d : Nat) (tmp : A.Reg)
    {t : Ty} : Arg K t → Except String (List (Instr A) × A.Reg)
  | .imm c =>
    match immToBitVec64 t c with
    | some v => .ok ([.movi tmp v], tmp)
    | none => .error "FromWord: unsupported immediate type"
  | .var idx =>
    if idx < d then
      match locOf b spillBase (d - 1 - idx) with
      | .gpr r => .ok ([], r)
      | .slot k => .ok ([.slotLd tmp k], tmp)
    else .error "FromWord: out-of-scope variable index"

/-- Load an L0 `Arg K t` unconditionally into a specific destination register `dst`. -/
@[expose] def loadArgInto {A : Arch} (b : WordRegBind A) (spillBase d : Nat) (dst : A.Reg)
    {t : Ty} : Arg K t → Except String (List (Instr A))
  | .imm c =>
    match immToBitVec64 t c with
    | some v => .ok [.movi dst v]
    | none => .error "FromWord: unsupported immediate type"
  | .var idx =>
    if idx < d then
      match locOf b spillBase (d - 1 - idx) with
      | .gpr r => if r == dst then .ok [] else .ok [.mov .w64 dst r]
      | .slot k => .ok [.slotLd dst k]
    else .error "FromWord: out-of-scope variable index"

/-- Load immutable de Bruijn level `lvl` into `dst`. -/
@[expose] def loadLevelInto {A : Arch} (b : WordRegBind A) (spillBase : Nat) (dst : A.Reg)
    (lvl : Nat) : List (Instr A) :=
  match locOf b spillBase lvl with
  | .gpr r => if r == dst then [] else [.mov .w64 dst r]
  | .slot k => [.slotLd dst k]

/-- Resolve an L0 `Arg K t` as a `Src A` (using `tmp` only if spilled slot, avoiding `movi`). -/
@[expose] def argToSrc {A : Arch} (b : WordRegBind A) (spillBase d : Nat) (tmp : A.Reg)
    {t : Ty} (a : Arg K t) : Except String (List (Instr A) × Src A) :=
  match a with
  | .imm c =>
    match immToBitVec64 t c with
    | some v => .ok ([], .imm v)
    | none => .error "FromWord: unsupported immediate type"
  | .var idx =>
    if idx < d then
      match locOf b spillBase (d - 1 - idx) with
      | .gpr r => .ok ([], .reg r)
      | .slot k => .ok ([.slotLd tmp k], .reg tmp)
    else .error "FromWord: out-of-scope variable index"

/-- Emit instructions whose logical output lands in `dstLoc : WordLoc A`, staging through `w0`
when `dstLoc` is a stack slot. -/
@[expose] def emitToLoc {A : Arch} (w0 : A.Reg) (dstLoc : WordLoc A)
    (build : A.Reg → List (Instr A)) : List (Instr A) :=
  match dstLoc with
  | .gpr r => build r
  | .slot k => build w0 ++ [.slotSt k w0]

/-- Source value for parallel register transfer at block boundaries. -/
inductive ParSrc (A : Arch) : Type where
  | reg (r : A.Reg)
  | slot (k : Nat)
  | imm (v : BitVec 64)

/-- Replace register `old` with `rep` across pending `ParSrc A` items. -/
@[expose] def ParSrc.substReg {A : Arch} [DecidableEq A.Reg] (old rep : A.Reg) :
    ParSrc A → ParSrc A
  | .reg r => if r = old then .reg rep else .reg r
  | s => s

/-- Emit instructions copying `src : ParSrc A` into `dst : A.Reg`. -/
@[expose] def emitParOne {A : Arch} (dst : A.Reg) : ParSrc A → List (Instr A)
  | .reg r => if r = dst then [] else [.mov .w64 dst r]
  | .slot k => [.slotLd dst k]
  | .imm v => [.movi dst v]

/-- Resolve an L0 `Arg K i64` into a `ParSrc A`. -/
@[expose] def argToParSrc {A : Arch} (b : WordRegBind A) (spillBase d : Nat) :
    Arg K i64 → Except String (ParSrc A)
  | .imm c => .ok (.imm c)
  | .var idx =>
    if idx < d then
      match locOf b spillBase (d - 1 - idx) with
      | .gpr r => .ok (.reg r)
      | .slot k => .ok (.slot k)
    else .error "FromWord: out-of-scope variable index in nextRegs"

/-- Check whether register `r` is read as a `.reg r` source in `moves`. -/
@[expose] def isReadIn {A : Arch} [DecidableEq A.Reg] (r : A.Reg)
    (moves : List (A.Reg × ParSrc A)) : Bool :=
  moves.any fun p => match p.2 with | .reg s => s == r | _ => false

/-- Drop trivial self-moves `(d, .reg d)`. -/
@[expose] def dropSelfMoves {A : Arch} [DecidableEq A.Reg]
    (moves : List (A.Reg × ParSrc A)) : List (A.Reg × ParSrc A) :=
  moves.filter fun p => match p.2 with | .reg r => p.1 != r | _ => true

private theorem length_filter_lt_of_mem {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (hx : x ∈ xs) (hpx : p x = false) : (xs.filter p).length < xs.length := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.filter]
    cases hy : p y <;> simp only [List.length_cons]
    · exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · rcases List.mem_cons.mp hx with rfl | hmem
      · rw [hpx] at hy; cases hy
      · exact Nat.succ_lt_succ (ih hmem)

/-- Bounded recursive worker for cycle-breaking parallel move (`fuel` initially `moves.length`). -/
@[expose] def parMoveAux {A : Arch} [DecidableEq A.Reg] (tmp : A.Reg) :
    Nat → List (A.Reg × ParSrc A) → List (Instr A)
  | _, [] => []
  | 0, _ => []
  | fuel + 1, m :: ms =>
    let moves := m :: ms
    match moves.find? (fun p => !isReadIn p.1 moves) with
    | some (d, sv) =>
      emitParOne d sv ++ parMoveAux tmp fuel (dropSelfMoves (moves.filter (fun p => p.1 != d)))
    | none =>
      match m with
      | (d, .reg r) =>
        if d = r then parMoveAux tmp fuel ms
        else
          [.mov .w64 tmp d, .mov .w64 d r] ++
            parMoveAux tmp fuel (dropSelfMoves (ms.map fun p => (p.1, p.2.substReg d tmp)))
      | (d, sv) =>
        emitParOne d sv ++ parMoveAux tmp fuel ms

/-- Cycle-breaking sequentialization of parallel moves using one dedicated scratch `tmp`
disjoint from all destination registers. -/
@[expose] def parMove {A : Arch} [DecidableEq A.Reg] (tmp : A.Reg)
    (moves : List (A.Reg × ParSrc A)) : List (Instr A) :=
  parMoveAux tmp moves.length moves

/-- Emit parallel assignment for the 6 L0 boundary registers `nxt : RegsExpr K`. -/
@[expose] def emitNextRegs {A : Arch} (b : WordRegBind A) (spillBase d : Nat)
    (nxt : RegsExpr K) : Except String (List (Instr A)) := do
  let spS ← argToParSrc b spillBase d nxt.sp
  let rpS ← argToParSrc b spillBase d nxt.rp
  let rvS ← argToParSrc b spillBase d nxt.rv
  let r1S ← argToParSrc b spillBase d nxt.r1
  let r2S ← argToParSrc b spillBase d nxt.r2
  let r3S ← argToParSrc b spillBase d nxt.r3
  let pairs := dropSelfMoves
    [(b.sp, spS), (b.rp, rpS), (b.rv, rvS), (b.r1, r1S), (b.r2, r2S), (b.r3, r3S)]
  .ok (parMove b.w1 pairs)

/-- Normalize boolean `CmpOp` so `0#8`/`1#8` unsigned comparison matches `CmpOp.evalBool`. -/
@[expose] def normBoolCmp : CmpOp → CmpOp
  | .slt => .ugt
  | .sle => .uge
  | .sgt => .ult
  | .sge => .ule
  | o => o

/-- Emit CoreAlu binary operation on typed arguments of width `w`. -/
@[expose] def lowerBinBits {A : Arch} (b : WordRegBind A) (spillBase d : Nat) (dst : WordLoc A)
    (op : CoreAlu) (w : Width) {t : Ty} (lhs rhs : Arg K t) : Except String (List (Instr A)) := do
  let (ca, ra) ← loadArgToGpr b spillBase d b.w1 lhs
  let (cb, sb) ← argToSrc b spillBase d b.w2 rhs
  .ok (ca ++ cb ++ emitToLoc b.w0 dst fun rd => [.alu op w rd ra sb false])

/-- Emit comparison `lhs o rhs` at width `w` setting boolean destination `dst`. -/
@[expose] def lowerCmpBits {A : Arch} (b : WordRegBind A) (spillBase d : Nat) (dst : WordLoc A)
    (o : CmpOp) (w : Width) {t : Ty} (lhs rhs : Arg K t) : Except String (List (Instr A)) := do
  let some cc := b.condOfCmp? o | .error "FromWord: unsupported CmpOp for WordRegBind"
  let (ca, ra) ← loadArgToGpr b spillBase d b.w1 lhs
  let (cb, sb) ← argToSrc b spillBase d b.w2 rhs
  .ok (ca ++ cb ++ [.cmp w ra sb] ++ emitToLoc b.w0 dst fun rd => [.setcc rd cc])

/-- Branchless mask-based `select c a b` supporting `.bool` and `.bits n` (`n ∈ {8,16,32,64}`). -/
@[expose] def lowerSelect {A : Arch} (b : WordRegBind A) (spillBase d : Nat) (dst : WordLoc A)
    {t : Ty} (c : Arg K .bool) (tVal fVal : Arg K t) : Except String (List (Instr A)) := do
  let (cc, rc) ← loadArgToGpr b spillBase d b.w0 c
  let mkMask : List (Instr A) :=
    [.alu .and .w64 b.w0 rc (.imm 1#64) false,
     .movi b.w1 0#64,
     .alu .sub .w64 b.w0 b.w1 (.reg b.w0) false]
  let ct ← loadArgInto b spillBase d b.w1 tVal
  let cf ← loadArgInto b spillBase d b.w2 fVal
  let core (rd : A.Reg) : List (Instr A) :=
    [.alu .and .w64 b.w1 b.w1 (.reg b.w0) false,
     .alu .xor .w64 b.w0 b.w0 (.imm 0xFFFFFFFFFFFFFFFF#64) false,
     .alu .and .w64 b.w2 b.w2 (.reg b.w0) false,
     .alu .or .w64 rd b.w1 (.reg b.w2) false]
  .ok (cc ++ mkMask ++ ct ++ cf ++ emitToLoc b.w0 dst core)

/-- Dispatch `lowerOp` on `OpCode` before args so every constructor arm reduces cleanly. -/
@[expose] def lowerOpCode {A : Arch} (b : WordRegBind A) (spillBase d : Nat) :
    {as ts : List Ty} → OpCode as ts → Tup (Arg K) as → Except String (List (Instr A) × Nat)
  | _, _, .copy .bool, (a, ()) => do
    let (ca, ra) ← loadArgToGpr b spillBase d b.w1 a
    .ok (ca ++ emitToLoc b.w0 (locOf b spillBase d) fun rd => [.mov .w8 rd ra], d + 1)
  | _, _, .copy (.bits n), (a, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported copy width {n}"
    let (ca, ra) ← loadArgToGpr b spillBase d b.w1 a
    .ok (ca ++ emitToLoc b.w0 (locOf b spillBase d) fun rd => [.mov w rd ra], d + 1)
  | _, _, .add (.bits n), (x, y, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported add width {n}"
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .add w x y, d + 1)
  | _, _, .sub (.bits n), (x, y, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported sub width {n}"
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .sub w x y, d + 1)
  | _, _, .mul (.bits n), (x, y, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported mul width {n}"
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .mul w x y, d + 1)
  | _, _, .and (.bits n), (x, y, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported and width {n}"
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .and w x y, d + 1)
  | _, _, .or (.bits n), (x, y, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported or width {n}"
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .or w x y, d + 1)
  | _, _, .xor (.bits n), (x, y, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported xor width {n}"
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .xor w x y, d + 1)
  | _, _, .shl (.bits n), (x, y, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported shl width {n}"
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .shl w x y, d + 1)
  | _, _, .lshr (.bits n), (x, y, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported lshr width {n}"
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .lshr w x y, d + 1)
  | _, _, .ashr (.bits n), (x, y, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported ashr width {n}"
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .ashr w x y, d + 1)
  | _, _, .neg (.bits n), (x, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported neg width {n}"
    let (ca, rx) ← loadArgToGpr b spillBase d b.w2 x
    let dst := locOf b spillBase d
    .ok ([.movi b.w1 0#64] ++ ca ++ emitToLoc b.w0 dst fun rd =>
      [.alu .sub w rd b.w1 (.reg rx) false], d + 1)
  | _, _, .not (.bits n), (x, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported not width {n}"
    let (ca, rx) ← loadArgToGpr b spillBase d b.w1 x
    let dst := locOf b spillBase d
    .ok (ca ++ emitToLoc b.w0 dst fun rd =>
      [.alu .xor w rd rx (.imm (maskOfBits64 n)) false], d + 1)
  | _, _, .and .bool, (x, y, ()) => do
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .and .w8 x y, d + 1)
  | _, _, .or .bool, (x, y, ()) => do
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .or .w8 x y, d + 1)
  | _, _, .xor .bool, (x, y, ()) => do
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .xor .w8 x y, d + 1)
  | _, _, .not .bool, (x, ()) => do
    let (ca, rx) ← loadArgToGpr b spillBase d b.w1 x
    let dst := locOf b spillBase d
    .ok (ca ++ emitToLoc b.w0 dst fun rd => [.alu .xor .w8 rd rx (.imm 1#64) false], d + 1)
  | _, _, .add .bool, (x, y, ()) => do
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .xor .w8 x y, d + 1)
  | _, _, .sub .bool, (x, y, ()) => do
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .xor .w8 x y, d + 1)
  | _, _, .mul .bool, (x, y, ()) => do
    .ok (← lowerBinBits b spillBase d (locOf b spillBase d) .and .w8 x y, d + 1)
  | _, _, .neg .bool, (x, ()) => do
    let (ca, rx) ← loadArgToGpr b spillBase d b.w1 x
    .ok (ca ++ emitToLoc b.w0 (locOf b spillBase d) fun rd => [.mov .w8 rd rx], d + 1)
  | _, _, .cmp o (.bits n) _ _, (x, y, ()) => do
    let some w := Width.ofBits? n | .error s!"FromWord: unsupported cmp width {n}"
    .ok (← lowerCmpBits b spillBase d (locOf b spillBase d) o w x y, d + 1)
  | _, _, .cmp o .bool _ _, (x, y, ()) => do
    .ok (← lowerCmpBits b spillBase d (locOf b spillBase d) (normBoolCmp o) .w8 x y, d + 1)
  | _, _, .select t, (c, x, y, ()) => do
    if (tyToWidth? t).isSome then
      .ok (← lowerSelect b spillBase d (locOf b spillBase d) c x y, d + 1)
    else .error "FromWord: unsupported select type"
  | _, _, .zext m n, (x, ()) => do
    if _ : m ≤ n ∧ (Width.ofBits? m).isSome ∧ (Width.ofBits? n).isSome then
      let (ca, rx) ← loadArgToGpr b spillBase d b.w1 x
      let dst := locOf b spillBase d
      .ok (ca ++ emitToLoc b.w0 dst fun rd =>
        [.alu .and .w64 rd rx (.imm (maskOfBits64 m)) false], d + 1)
    else .error "FromWord: unsupported zext widths"
  | _, _, .sext m n, (x, ()) => do
    if _ : m ≤ n ∧ (Width.ofBits? m).isSome ∧ (Width.ofBits? n).isSome then
      let ca ← loadArgInto b spillBase d b.w1 x
      let shAmt := BitVec.ofNat 64 (64 - m)
      let sextCode : List (Instr A) :=
        if m == 64 then []
        else [.alu .shl .w64 b.w1 b.w1 (.imm shAmt) false,
              .alu .ashr .w64 b.w1 b.w1 (.imm shAmt) false]
      let storeCode := match locOf b spillBase d with
        | .gpr r => [.mov .w64 r b.w1]
        | .slot k => [.slotSt k b.w1]
      .ok (ca ++ sextCode ++ storeCode, d + 1)
    else .error "FromWord: unsupported sext widths"
  | _, _, .trunc m n, (x, ()) => do
    let some wn := Width.ofBits? n | .error s!"FromWord: unsupported trunc dst width {n}"
    if _ : n ≤ m ∧ (Width.ofBits? m).isSome then
      let (ca, rx) ← loadArgToGpr b spillBase d b.w1 x
      .ok (ca ++ emitToLoc b.w0 (locOf b spillBase d) fun rd => [.mov wn rd rx], d + 1)
    else .error "FromWord: unsupported trunc widths"
  | _, _, .ofBool n, (x, ()) => do
    if (Width.ofBits? n).isSome then
      let (ca, rx) ← loadArgToGpr b spillBase d b.w1 x
      let dst := locOf b spillBase d
      .ok (ca ++ emitToLoc b.w0 dst fun rd => [.alu .and .w64 rd rx (.imm 1#64) false], d + 1)
    else .error s!"FromWord: unsupported ofBool width {n}"
  | _, _, _, _ => .error "FromWord: unsupported OpCode"

/-- Lower a single L0 `Op K ts` binding into `(instrs, nextDepth)`. -/
@[expose] def lowerOp {A : Arch} (b : WordRegBind A) (spillBase d : Nat)
    {ts : List Ty} (op : Op K ts) : Except String (List (Instr A) × Nat) :=
  lowerOpCode b spillBase d op.code op.args

/-- Emit L0 memory load `.load t a` into `dstLoc`. -/
@[expose] def lowerMemLoad {A : Arch} (b : WordRegBind A) (spillBase d : Nat) (t : Ty)
    (a : Arg K i64) : Except String (List (Instr A)) := do
  let some w := tyToWidth? t | .error "FromWord: unsupported load type"
  let (ca, ra) ← loadArgToGpr b spillBase d b.w1 a
  .ok (ca ++ emitToLoc b.w0 (locOf b spillBase d) fun rd => [.load w .zx rd (.baseDisp ra 0)])

/-- Emit L0 memory store `.store v a`. -/
@[expose] def lowerMemStore {A : Arch} (b : WordRegBind A) (spillBase d : Nat) {t : Ty}
    (v : Arg K t) (a : Arg K i64) : Except String (List (Instr A)) := do
  let some w := tyToWidth? t | .error "FromWord: unsupported store type"
  let (cv, rv) ← loadArgToGpr b spillBase d b.w1 v
  let (ca, ra) ← loadArgToGpr b spillBase d b.w2 a
  .ok (cv ++ ca ++ [.store w rv (.baseDisp ra 0)])

/-! ## §3. Fresh-Label Block Lowering (`fromWord` and `fromWordContify`) -/

/-- State monad generating fresh collision-free block suffixes for `.jnz` / switch cascades. -/
abbrev LowerM := StateT Nat (Except String)

/-- Allocate a fresh internal block label with prefix `pfx`. -/
@[expose] def freshLabel (pfx : String) : LowerM Sym := do
  let n ← get
  set (n + 1)
  pure s!"{pfx}__aux_{n}"

/-- Lift `Except String α` into `LowerM α`. -/
@[expose] def liftEx {α : Type} (e : Except String α) : LowerM α :=
  StateT.lift e

/-- Lower an uncontified open `BlockFlat` (optional hardware frame `frameSlots?` for temp spills),
starting at block label `curLbl` with landing pad `pad?` and leading `pfx`. -/
@[expose] def lowerPlainBody {A : Arch} (b : WordRegBind A) (cm : CodeMap) (auxPfx : Sym)
    (frameSlots? : Option Nat) :
    Sym → Option PadKind → List (Instr A) → Nat → BlockFlat → LowerM (List (Block A))
  | curLbl, pad?, acc, d, .let_ op k => do
    let (is, d') ← liftEx (lowerOp b 0 d op)
    lowerPlainBody b cm auxPfx frameSlots? curLbl pad? (acc ++ is) d' k
  | curLbl, pad?, acc, d, .load t a k => do
    let is ← liftEx (lowerMemLoad b 0 d t a)
    lowerPlainBody b cm auxPfx frameSlots? curLbl pad? (acc ++ is) (d + 1) k
  | curLbl, pad?, acc, d, .store v a k => do
    let is ← liftEx (lowerMemStore b 0 d v a)
    lowerPlainBody b cm auxPfx frameSlots? curLbl pad? (acc ++ is) d k
  | curLbl, pad?, acc, d, .codeAddr sym k => do
    if (cm.addrOf? sym).isNone then
      liftEx (.error s!"FromWord: unknown codeAddr symbol '{sym}'")
    let is := emitToLoc b.w0 (locOf b 0 d) fun rd => [.symAddr sym rd]
    lowerPlainBody b cm auxPfx frameSlots? curLbl pad? (acc ++ is) (d + 1) k
  | curLbl, pad?, acc, d, .jnz c t e => do
    let (cc, rc) ← liftEx (loadArgToGpr b 0 d b.w0 c)
    let lT ← freshLabel auxPfx
    let lF ← freshLabel auxPfx
    let blk : Block A :=
      { label := curLbl, pad? := pad?, body := acc ++ cc, term := .jnzGpr rc lT lF }
    let bsT ← lowerPlainBody b cm auxPfx frameSlots? lT none [] d t
    let bsF ← lowerPlainBody b cm auxPfx frameSlots? lF none [] d e
    pure (blk :: (bsT ++ bsF))
  | curLbl, pad?, acc, d, .ijmp tgt nxt => do
    let ctgt ← liftEx (loadArgInto b 0 d b.w0 tgt)
    let cnxt ← liftEx (emitNextRegs b 0 d nxt)
    let ep := match frameSlots? with | some ns => [.epilogue ns] | none => []
    pure [{ label := curLbl, pad? := pad?, body := acc ++ ctgt ++ cnxt ++ ep, term := .ijmp b.w0 }]
  | curLbl, pad?, acc, d, .halt code => do
    let ccode ← liftEx (loadArgInto b 0 d b.w0 code)
    let ep := match frameSlots? with | some ns => [.epilogue ns] | none => []
    pure [{ label := curLbl, pad? := pad?, body := acc ++ ccode ++ ep, term := .halt b.w0 }]
  | _, _, _, _, .hlt => liftEx (.error "FromWord: reachable .hlt in BlockFlat")

/-- Lower one `CodeEntry` in plain open mode (adding `.prologue` iff locals overflow `tmps`). -/
@[expose] def lowerPlainEntry {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (e : CodeEntry) : LowerM (List (Block A)) := do
  let spills := tempSpillCount b (maxBlockDepth e.block 6)
  let frameSlots? := if spills > 0 then some spills else none
  let pfx := match frameSlots? with | some ns => [.prologue ns] | none => []
  lowerPlainBody b cm e.name frameSlots? e.name (some b.padKind) pfx 6 e.block

/-- Deterministic fallback address finder returning the first `cand + 8 * idx` not in `used`. -/
@[expose] def findFreshAddrAux (used : List (BitVec 64)) (cand : BitVec 64) : Nat → BitVec 64
  | 0 => cand
  | fuel + 1 => if used.contains cand then findFreshAddrAux used (cand + 8#64) fuel else cand

/-- Association-list lookup over `(Sym × BitVec 64)`. -/
@[expose] def lookupSymAddr : List (Sym × BitVec 64) → Sym → Option (BitVec 64)
  | [], _ => none
  | (s, a) :: rest, k => if s == k then some a else lookupSymAddr rest k

/-- Build total `Sym → BitVec 64` map preserving all L0 symbol addresses `baseEntries` while
assigning distinct aligned fresh addresses to every remaining block label in `blocks`. -/
@[expose] def buildVllSymAddr {A : Arch} (baseEntries : List (Sym × BitVec 64))
    (blocks : List (Block A)) : Sym → BitVec 64 :=
  let usedInit := baseEntries.map Prod.snd
  let maxNat := usedInit.foldl (fun m a => Nat.max m a.toNat) 0
  let startNat := ((maxNat + 64 + 7) / 8) * 8
  let step := blocks.foldl (fun (st : BitVec 64 × List (BitVec 64) × List (Sym × BitVec 64)) blk =>
    let (cand, used, pairs) := st
    match lookupSymAddr baseEntries blk.label with
    | some _ => st
    | none =>
      let a := findFreshAddrAux used cand (used.length + 1)
      (a + 8#64, a :: used, (blk.label, a) :: pairs))
    (BitVec.ofNat 64 startNat, usedInit, [])
  let auxPairs := step.2.2
  fun sym =>
    match lookupSymAddr baseEntries sym with
    | some a => a
    | none => (lookupSymAddr auxPairs sym).getD 0#64

/-- Validate uniqueness and landing-pad invariants of a `VllCodeMap A`. -/
@[expose] def finalizeVllCodeMap {A : Arch} (cm : VllCodeMap A) : Except String (VllCodeMap A) :=
  if !cm.labelsUnique then .error "FromWord: duplicate block labels in VllCodeMap"
  else if !cm.addrsUnique then .error "FromWord: duplicate block addresses in VllCodeMap"
  else if !cm.padsOk then .error "FromWord: missing landing pad on addrTaken label"
  else .ok cm

/-- Lower an open L0 `BedrockWord.CodeMap` into a `VllCodeMap A` preserving entry addresses and
marking every entry label as `addrTaken` with hardware landing pads. -/
@[expose] def fromWord {A : Arch} (b : WordRegBind A) (cm : CodeMap) :
    Except String (VllCodeMap A) := do
  if !cm.checkWf then .error "FromWord: input CodeMap failed checkWf"
  let (blocksList, _) ← (cm.mapM (lowerPlainEntry b cm)).run 0
  let blocks := blocksList.flatten
  let baseEntries := cm.map fun e => (e.name, e.addr)
  let symAddr := buildVllSymAddr baseEntries blocks
  finalizeVllCodeMap { blocks := blocks, symAddr := symAddr, addrTaken := cm.map (·.name) }

/-! ## §4. Stage-1 `ContifyWitness` & `PrivFrameCfg` Lowering (`fromWordContify`) -/

/-- Canonical internal block label for L0 PC `pc` inside region `cr`. -/
@[expose] def innerLabel (cr : ContifyRegion) (pc : BitVec 64) : Sym :=
  s!"{cr.name}__pc_{pc.toNat}"

/-- Check whether `cr` makes any `.contCall` edge. -/
@[expose] def regionHasCalls (cr : ContifyRegion) : Bool :=
  cr.edges.any fun ew => match ew.kind with | .contCall _ _ _ _ _ => true | _ => false

/-- Maximum SSA variable depth across all blocks in `cr.allPcs`. -/
@[expose] def regionMaxDepth (cm : CodeMap) (cr : ContifyRegion) : Nat :=
  cr.allPcs.foldl (fun m pc =>
    match cm.lookupAddr pc with
    | some blk => Nat.max m (maxBlockDepth blk 6)
    | none => m) 6

/-- Hardware spill-slot base above promoted private slots `(slot 0..nPriv-1, sp₀)`. -/
@[expose] def regionSpillBase (cr : ContifyRegion) : Nat :=
  if cr.privFrame.numSlots > 0 then cr.privFrame.numSlots + 1 else 0

/-- Total hardware frame slots `ns` required by region `cr`. -/
@[expose] def regionFrameSlots {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (cr : ContifyRegion) : Nat :=
  regionSpillBase cr + tempSpillCount b (regionMaxDepth cm cr)

/-- True iff region `cr` must allocate/restore a hardware frame (`.prologue`/`.epilogue`). -/
@[expose] def regionNeedFrame {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (cr : ContifyRegion) : Bool :=
  cr.privFrame.numSlots > 0 || tempSpillCount b (regionMaxDepth cm cr) > 0 || regionHasCalls cr

/-- Emit hardware entry initialization for `nPriv > 0` private stack slots (`[wordSp - 8*(k+1)]`),
plus saving `wordSp = sp₀` in hardware slot `nPriv`. -/
@[expose] def emitPrivFrameInitAux {A : Arch} (b : WordRegBind A) (nPriv k : Nat) :
    List (Instr A) :=
  if _ : k < nPriv then
    let off := BitVec.ofNat 64 (8 * (k + 1))
    [.alu .sub .w64 b.w0 b.sp (.imm off) false,
     .load .w64 .zx b.w0 (.baseDisp b.w0 0),
     .slotSt k b.w0] ++ emitPrivFrameInitAux b nPriv (k + 1)
  else []
termination_by nPriv - k

/-- Entry initialization sequence for `nPriv` promoted private slots (no-op if `nPriv = 0`). -/
@[expose] def emitPrivFrameInit {A : Arch} (b : WordRegBind A) (nPriv : Nat) : List (Instr A) :=
  if nPriv == 0 then [] else .slotSt nPriv b.sp :: emitPrivFrameInitAux b nPriv 0

/-- Flush `nPriv` promoted slots from hardware frame `[hwSp + 8*k]` back to L0 stack memory
`[sp₀ - 8*(k+1)]`, preserving `b.w0` intact (using only `b.w1`, `b.w2`). -/
@[expose] def emitPrivFlushAux {A : Arch} (b : WordRegBind A) (nPriv k : Nat) : List (Instr A) :=
  if _ : k < nPriv then
    [.slotLd b.w2 k,
     .alu .sub .w64 b.w1 b.w1 (.imm 8#64) false,
     .store .w64 b.w2 (.baseDisp b.w1 0)] ++ emitPrivFlushAux b nPriv (k + 1)
  else []
termination_by nPriv - k

/-- Flush promoted private slots back to L0 memory before `.bailout` / `.halt` / alias fallback,
leaving `b.w0` untouched. -/
@[expose] def emitPrivFlush {A : Arch} (b : WordRegBind A) (nPriv : Nat) : List (Instr A) :=
  if nPriv == 0 then [] else .slotLd b.w1 nPriv :: emitPrivFlushAux b nPriv 0

/-- Hardware epilogue suffix restoring frame (no-op if `needFrame = false`). -/
@[expose] def regionExitSuffix {A : Arch} (b : WordRegBind A) (nPriv ns : Nat)
    (needFrame : Bool) : List (Instr A) :=
  emitPrivFlush b nPriv ++ (if needFrame then [.epilogue ns] else [])

/-- Emit dynamic alias-disjointness guard testing `8*nPriv ≤ a - lo ∧ a - lo ≤ 2^64 - bytes`,
placing `1#64`/`0#64` boolean result in `b.w0` and using only `b.w0, b.w1, b.w2`. -/
@[expose] def emitDynAliasGuard {A : Arch} (b : WordRegBind A)
    (spillBase d nPriv bytes : Nat) (a : Arg K i64) : Except String (List (Instr A)) := do
  let some ccUge := b.condOfCmp? .uge | .error "FromWord: bind lacks .uge for alias guard"
  let some ccUle := b.condOfCmp? .ule | .error "FromWord: bind lacks .ule for alias guard"
  let ca ← loadArgInto b spillBase d b.w0 a
  let frameBytes := BitVec.ofNat 64 (8 * nPriv)
  let hiBound := BitVec.ofNat 64 (2 ^ 64 - bytes)
  .ok (ca ++
    [.slotLd b.w1 nPriv,
     .alu .sub .w64 b.w1 b.w1 (.imm frameBytes) false,
     .alu .sub .w64 b.w0 b.w0 (.reg b.w1) false,
     .cmp .w64 b.w0 (.imm frameBytes),
     .setcc b.w1 ccUge,
     .cmp .w64 b.w0 (.imm hiBound),
     .setcc b.w2 ccUle,
     .alu .and .w8 b.w0 b.w1 (.reg b.w2) false])

/-- Unpromoted tail lowering after dynamic alias guard flush (`privSlots` already flushed to L0
memory; `spillBase` and hardware epilogue still active until exit). -/
@[expose] def lowerContUnpromoted {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (cr : ContifyRegion) (spillBase ns : Nat) (needFrame : Bool) :
    Sym → List (Instr A) → Nat → BlockFlat → LowerM (List (Block A))
  | curLbl, acc, d, .let_ op k => do
    let (is, d') ← liftEx (lowerOp b spillBase d op)
    lowerContUnpromoted b cm cr spillBase ns needFrame curLbl (acc ++ is) d' k
  | curLbl, acc, d, .load t a k => do
    let is ← liftEx (lowerMemLoad b spillBase d t a)
    lowerContUnpromoted b cm cr spillBase ns needFrame curLbl (acc ++ is) (d + 1) k
  | curLbl, acc, d, .store v a k => do
    let is ← liftEx (lowerMemStore b spillBase d v a)
    lowerContUnpromoted b cm cr spillBase ns needFrame curLbl (acc ++ is) d k
  | curLbl, acc, d, .codeAddr sym k => do
    if (cm.addrOf? sym).isNone then
      liftEx (.error s!"FromWord: unknown codeAddr symbol '{sym}'")
    let is := emitToLoc b.w0 (locOf b spillBase d) fun rd => [.symAddr sym rd]
    lowerContUnpromoted b cm cr spillBase ns needFrame curLbl (acc ++ is) (d + 1) k
  | curLbl, acc, d, .jnz c t e => do
    let (cc, rc) ← liftEx (loadArgToGpr b spillBase d b.w0 c)
    let lT ← freshLabel cr.name
    let lF ← freshLabel cr.name
    let blk : Block A :=
      { label := curLbl, pad? := none, body := acc ++ cc, term := .jnzGpr rc lT lF }
    let bsT ← lowerContUnpromoted b cm cr spillBase ns needFrame lT [] d t
    let bsF ← lowerContUnpromoted b cm cr spillBase ns needFrame lF [] d e
    pure (blk :: (bsT ++ bsF))
  | curLbl, acc, d, .ijmp tgt nxt => do
    let ctgt ← liftEx (loadArgInto b spillBase d b.w0 tgt)
    let cnxt ← liftEx (emitNextRegs b spillBase d nxt)
    let ep := if needFrame then [.epilogue ns] else []
    pure [{ label := curLbl, pad? := none, body := acc ++ ctgt ++ cnxt ++ ep, term := .ijmp b.w0 }]
  | curLbl, acc, d, .halt code => do
    let ccode ← liftEx (loadArgInto b spillBase d b.w0 code)
    let ep := if needFrame then [.epilogue ns] else []
    pure [{ label := curLbl, pad? := none, body := acc ++ ccode ++ ep, term := .halt b.w0 }]
  | _, _, _, .hlt => liftEx (.error "FromWord: reachable .hlt in unpromoted tail")

/-- Emit comparison cascade for `EdgeKind.strideTable`. Expects index value in `b.w2` and (if
`needGuard`) full runtime target in `b.w0` (both untouched by comparisons). -/
@[expose] def lowerStrideCascade {A : Arch} (b : WordRegBind A) (cr : ContifyRegion)
    (nPriv ns : Nat) (needFrame needGuard : Bool) (ccEq : A.Cond) :
    Sym → List (Instr A) → Nat → List (BitVec 64) → LowerM (List (Block A))
  | curLbl, acc, _, [] =>
    pure [{ label := curLbl, pad? := none,
            body := acc ++ regionExitSuffix b nPriv ns needFrame, term := .ijmp b.w0 }]
  | curLbl, acc, idx, [lastPc] =>
    if !needGuard then
      pure [{ label := curLbl, pad? := none, body := acc, term := .jmp (innerLabel cr lastPc) }]
    else do
      let bailLbl ← freshLabel cr.name
      pure [ { label := curLbl, pad? := none,
               body := acc ++ [.cmp .w64 b.w2 (.imm (BitVec.ofNat 64 idx))],
               term := .jcc ccEq (innerLabel cr lastPc) bailLbl },
             { label := bailLbl, pad? := none,
               body := regionExitSuffix b nPriv ns needFrame, term := .ijmp b.w0 } ]
  | curLbl, acc, idx, tPc :: rest => do
    let nextLbl ← freshLabel cr.name
    let head : Block A :=
      { label := curLbl, pad? := none,
        body := acc ++ [.cmp .w64 b.w2 (.imm (BitVec.ofNat 64 idx))],
        term := .jcc ccEq (innerLabel cr tPc) nextLbl }
    let tail ← lowerStrideCascade b cr nPriv ns needFrame needGuard ccEq
      nextLbl [] (idx + 1) rest
    pure (head :: tail)

/-- Emit guarded-target cascade checking `b.w0 == hPc` for each `hPc ∈ hotTargets`, falling
through to flush + epilogue + `.ijmp b.w0`. -/
@[expose] def lowerGuardedTargets {A : Arch} (b : WordRegBind A) (cr : ContifyRegion)
    (nPriv ns : Nat) (needFrame : Bool) (ccEq : A.Cond) :
    Sym → List (Instr A) → List (BitVec 64) → LowerM (List (Block A))
  | curLbl, acc, [] =>
    pure [{ label := curLbl, pad? := none,
            body := acc ++ regionExitSuffix b nPriv ns needFrame, term := .ijmp b.w0 }]
  | curLbl, acc, hPc :: rest => do
    let nextLbl ← freshLabel cr.name
    let head : Block A :=
      { label := curLbl, pad? := none,
        body := acc ++ [.cmp .w64 b.w0 (.imm hPc)],
        term := .jcc ccEq (innerLabel cr hPc) nextLbl }
    let tail ← lowerGuardedTargets b cr nPriv ns needFrame ccEq nextLbl [] rest
    pure (head :: tail)

/-- Lower a Stage-1 block edge `.ijmp tgt nxt` via its checked `EdgeKind`. -/
@[expose] def lowerContEdge {A : Arch} (b : WordRegBind A) (cr : ContifyRegion)
    (spillBase ns : Nat) (needFrame : Bool) (st : ContSymState) (d : Nat)
    (curLbl : Sym) (acc : List (Instr A)) (tgt : Arg K i64) (nxt : RegsExpr K)
    (kind : EdgeKind) : LowerM (List (Block A)) := do
  let nPriv := cr.privFrame.numSlots
  match cr.abi, kind with
  | _, .direct targetPc =>
    let cnxt ← liftEx (emitNextRegs b spillBase d nxt)
    let tgtLbl := innerLabel cr targetPc
    pure [{ label := curLbl, pad? := none, body := acc ++ cnxt, term := .jmp tgtLbl }]
  | _, .select tPc ePc =>
    match st.evalArg tgt with
    | .ite cLvl _ _ =>
      let cc := loadLevelInto b spillBase b.w0 cLvl
      let cnxt ← liftEx (emitNextRegs b spillBase d nxt)
      pure [{ label := curLbl, pad? := none, body := acc ++ cc ++ cnxt,
              term := .jnzGpr b.w0 (innerLabel cr tPc) (innerLabel cr ePc) }]
    | _ => liftEx (.error "FromWord: select edge missing .ite symbolic value")
  | _, .strideTable _ targets needGuard =>
    match st.evalArg tgt with
    | .stride _ idxLvl =>
      let some ccEq := b.condOfCmp? .eq | liftEx (.error "FromWord: bind lacks .eq")
      let cidx := loadLevelInto b spillBase b.w2 idxLvl
      let ctgt ← if needGuard then liftEx (loadArgInto b spillBase d b.w0 tgt) else pure []
      let cnxt ← liftEx (emitNextRegs b spillBase d nxt)
      lowerStrideCascade b cr nPriv ns needFrame needGuard ccEq
        curLbl (acc ++ cidx ++ ctgt ++ cnxt) 0 targets
    | _ => liftEx (.error "FromWord: strideTable edge missing .stride symbolic value")
  | .retEnvelope, .contCall callee _ dualRet retPc altRetPc? =>
    let cnxt ← liftEx (emitNextRegs b spillBase d nxt)
    if dualRet then
      match altRetPc? with
      | some altPc =>
        let dispLbl ← freshLabel cr.name
        pure [ { label := curLbl, pad? := none, body := acc ++ cnxt,
                 term := .call callee dispLbl },
               { label := dispLbl, pad? := none, body := [],
                 term := .jnzGpr b.altRet (innerLabel cr altPc) (innerLabel cr retPc) } ]
      | none => liftEx (.error "FromWord: dualRet contCall missing altRetPc")
    else
      pure [{ label := curLbl, pad? := none, body := acc ++ cnxt,
              term := .call callee (innerLabel cr retPc) }]
  | .contified false, .contRet false =>
    let cnxt ← liftEx (emitNextRegs b spillBase d nxt)
    let ep := if needFrame then [.epilogue ns] else []
    pure [{ label := curLbl, pad? := none, body := acc ++ cnxt ++ ep, term := .ret }]
  | .contified true, .contRet isAlt =>
    let cnxt ← liftEx (emitNextRegs b spillBase d nxt)
    let flagIns : Instr A := .movi b.altRet (if isAlt then 1#64 else 0#64)
    let ep := if needFrame then [.epilogue ns] else []
    pure [{ label := curLbl, pad? := none, body := acc ++ cnxt ++ [flagIns] ++ ep, term := .ret }]
  | .retEnvelope, .guarded hotTargets =>
    let some ccEq := b.condOfCmp? .eq | liftEx (.error "FromWord: bind lacks .eq")
    let ctgt ← liftEx (loadArgInto b spillBase d b.w0 tgt)
    let cnxt ← liftEx (emitNextRegs b spillBase d nxt)
    lowerGuardedTargets b cr nPriv ns needFrame ccEq curLbl (acc ++ ctgt ++ cnxt) hotTargets
  | .retEnvelope, .bailout =>
    let ctgt ← liftEx (loadArgInto b spillBase d b.w0 tgt)
    let cnxt ← liftEx (emitNextRegs b spillBase d nxt)
    let exitOps := regionExitSuffix b nPriv ns needFrame
    pure [{ label := curLbl, pad? := none,
            body := acc ++ ctgt ++ cnxt ++ exitOps, term := .ijmp b.w0 }]
  | _, _ => liftEx (.error "FromWord: incompatible abi/EdgeKind in ContifyRegion")

/-- Lower a `BlockFlat` inside a Stage-1 `ContifyRegion`, promoting private `[sp - 8*(k+1)]` slots
to `.slotLd`/`.slotSt` and discharging checked `.ijmp` edges via `lowerContEdge`. -/
@[expose] def lowerContBlock {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (cr : ContifyRegion) (pc : BitVec 64) (spillBase ns : Nat) (needFrame : Bool) :
    Sym → List (Instr A) → Nat → BranchPath → ContSymState → BlockFlat →
    LowerM (List (Block A))
  | curLbl, acc, d, path, st, .let_ (ts := ts) op k => do
    let (is, d') ← liftEx (lowerOp b spillBase d op)
    lowerContBlock b cm cr pc spillBase ns needFrame curLbl (acc ++ is) d' path
      (st.pushRes ts (evalContOp st op)) k
  | curLbl, acc, d, path, st, bf@(.load t a k) => do
    let nPriv := cr.privFrame.numSlots
    let st' : ContSymState := { st with env := .top :: st.env, ctx := t :: st.ctx }
    let slotIdx? := if nPriv > 0 && t == i64 then spSlotOf? nPriv (st.evalArg a) else none
    match slotIdx? with
    | some slotIdx =>
      let is := emitToLoc b.w0 (locOf b spillBase d) fun rd => [.slotLd rd slotIdx]
      lowerContBlock b cm cr pc spillBase ns needFrame curLbl (acc ++ is) (d + 1) path st' k
    | none =>
      if nPriv == 0 || isStaticOutsideFrame nPriv t.bytes (st.evalArg a) then
        let is ← liftEx (lowerMemLoad b spillBase d t a)
        lowerContBlock b cm cr pc spillBase ns needFrame curLbl (acc ++ is) (d + 1) path st' k
      else
        let cg ← liftEx (emitDynAliasGuard b spillBase d nPriv t.bytes a)
        let safeLbl ← freshLabel cr.name
        let aliasLbl ← freshLabel cr.name
        let head : Block A :=
          { label := curLbl, pad? := none,
            body := acc ++ cg, term := .jnzGpr b.w0 safeLbl aliasLbl }
        let ldSafe ← liftEx (lowerMemLoad b spillBase d t a)
        let bsSafe ← lowerContBlock b cm cr pc spillBase ns needFrame
          safeLbl ldSafe (d + 1) path st' k
        let bsAlias ← lowerContUnpromoted b cm cr spillBase ns needFrame aliasLbl
          (emitPrivFlush b nPriv) d bf
        pure (head :: (bsSafe ++ bsAlias))
  | curLbl, acc, d, path, st, bf@(.store (t := t) v a k) => do
    let nPriv := cr.privFrame.numSlots
    let slotIdx? := if nPriv > 0 && t == i64 then spSlotOf? nPriv (st.evalArg a) else none
    match slotIdx? with
    | some slotIdx =>
      let (cv, rv) ← liftEx (loadArgToGpr b spillBase d b.w1 v)
      lowerContBlock b cm cr pc spillBase ns needFrame curLbl (acc ++ cv ++ [.slotSt slotIdx rv])
        d path st k
    | none =>
      if nPriv == 0 || isStaticOutsideFrame nPriv t.bytes (st.evalArg a) then
        let is ← liftEx (lowerMemStore b spillBase d v a)
        lowerContBlock b cm cr pc spillBase ns needFrame curLbl (acc ++ is) d path st k
      else
        let cg ← liftEx (emitDynAliasGuard b spillBase d nPriv t.bytes a)
        let safeLbl ← freshLabel cr.name
        let aliasLbl ← freshLabel cr.name
        let head : Block A :=
          { label := curLbl, pad? := none,
            body := acc ++ cg, term := .jnzGpr b.w0 safeLbl aliasLbl }
        let stSafe ← liftEx (lowerMemStore b spillBase d v a)
        let bsSafe ← lowerContBlock b cm cr pc spillBase ns needFrame safeLbl stSafe d path st k
        let bsAlias ← lowerContUnpromoted b cm cr spillBase ns needFrame aliasLbl
          (emitPrivFlush b nPriv) d bf
        pure (head :: (bsSafe ++ bsAlias))
  | curLbl, acc, d, path, st, .codeAddr sym k => do
    let some a := cm.addrOf? sym | liftEx (.error s!"FromWord: unknown codeAddr '{sym}'")
    let is := emitToLoc b.w0 (locOf b spillBase d) fun rd => [.symAddr sym rd]
    let sv := if (a &&& 7#64) == 0#64 then ContSymVal.alignedConst a else .const a
    lowerContBlock b cm cr pc spillBase ns needFrame curLbl (acc ++ is) (d + 1) path
      { st with env := sv :: st.env, ctx := i64 :: st.ctx } k
  | curLbl, acc, d, path, st, .jnz c t e => do
    let (cc, rc) ← liftEx (loadArgToGpr b spillBase d b.w0 c)
    let lT ← freshLabel cr.name
    let lF ← freshLabel cr.name
    let head : Block A :=
      { label := curLbl, pad? := none, body := acc ++ cc, term := .jnzGpr rc lT lF }
    let bsT ← lowerContBlock b cm cr pc spillBase ns needFrame lT [] d (path ++ [true])
      (st.pushCondFact c true) t
    let bsF ← lowerContBlock b cm cr pc spillBase ns needFrame lF [] d (path ++ [false])
      (st.pushCondFact c false) e
    pure (head :: (bsT ++ bsF))
  | curLbl, acc, d, path, st, .ijmp tgt nxt =>
    match cr.toRegionWitness.findEdge pc path with
    | some ew => lowerContEdge b cr spillBase ns needFrame st d curLbl acc tgt nxt ew.kind
    | none => liftEx (.error s!"FromWord: missing EdgeWitness at pc {pc}")
  | curLbl, acc, d, _, _, .halt code => do
    let ccode ← liftEx (loadArgInto b spillBase d b.w0 code)
    let exitOps := regionExitSuffix b cr.privFrame.numSlots ns needFrame
    pure [{ label := curLbl, pad? := none, body := acc ++ ccode ++ exitOps, term := .halt b.w0 }]
  | _, _, _, _, _, .hlt => liftEx (.error "FromWord: reachable .hlt in ContifyRegion")

/-- Lower all blocks of one `ContifyRegion` (external entry `cr.name` + internal `allPcs`). -/
@[expose] def lowerContRegion {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (cr : ContifyRegion) : LowerM (List (Block A)) := do
  let nPriv := cr.privFrame.numSlots
  let spillBase := regionSpillBase cr
  let ns := regionFrameSlots b cm cr
  let needFrame := regionNeedFrame b cm cr
  let pfx := (if needFrame then [.prologue ns] else []) ++ emitPrivFrameInit b nPriv
  let entryBlk : Block A :=
    { label := cr.name, pad? := some b.padKind, body := pfx,
      term := .fall (innerLabel cr cr.entryPc) }
  let innerLists ← cr.allPcs.mapM fun pc => do
    let some ceBlock := cm.lookupAddr pc | liftEx (.error s!"FromWord: missing pc {pc}")
    lowerContBlock b cm cr pc spillBase ns needFrame (innerLabel cr pc) [] 6 []
      ContSymState.init ceBlock
  pure (entryBlk :: innerLists.flatten)

/-- Stage-1 contification & `PrivFrameCfg` lowering from `(cm, wit)` into a `VllCodeMap A`. -/
@[expose] def fromWordContify {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (wit : ContifyWitness) : Except String (VllCodeMap A) := do
  if !cm.checkWf then .error "FromWord: input CodeMap failed checkWf"
  if !wit.check cm then .error "FromWord: ContifyWitness failed check"
  let (regBlocksList, st1) ← (wit.regions.mapM (lowerContRegion b cm)).run 0
  let wRes := residualContifyCodeMap cm wit
  let (resBlocksList, _) ← (wRes.mapM (lowerPlainEntry b cm)).run st1
  let blocks := regBlocksList.flatten ++ resBlocksList.flatten
  let cmPairs := cm.map fun e => (e.name, e.addr)
  let regPairs := wit.regions.map fun cr => (cr.name, cr.entryPc)
  let symAddr := buildVllSymAddr (regPairs ++ cmPairs) blocks
  let taken := wit.regions.map (·.name) ++ wRes.map (·.name)
  finalizeVllCodeMap { blocks := blocks, symAddr := symAddr, addrTaken := taken }

/-! ## §5. Semantic State Relations & Stack Budgets (`ValHolds64`, `WordRegsRel`, `EnvRel`) -/

/-- Agreement between a typed scalar L0 `Val t` and its 64-bit register/slot word `g`. -/
@[expose] def ValHolds64 : (t : Ty) → Val t → BitVec 64 → Prop
  | .bool, b, g => g.setWidth 8 = BitVec.ofNat 8 b.toNat
  | .bits n, v, g => n ≤ 64 ∧ g.setWidth n = v
  | _, _, _ => False

/-- Agreement on the 6 persistent L0 word registers `[sp, rp, rv, r1, r2, r3]`. -/
@[expose] def WordRegsRel {A : Arch} (b : WordRegBind A) (r : BedrockWord.Regs)
    (s : MachSt A) : Prop :=
  s.gpr b.sp = r.sp ∧
  s.gpr b.rp = r.rp ∧
  s.gpr b.rv = r.rv ∧
  s.gpr b.r1 = r.r1 ∧
  s.gpr b.r2 = r.r2 ∧
  s.gpr b.r3 = r.r3

/-- Location `loc` holds L0 typed value `(t, v)` in L1 state `s`. -/
@[expose] def LocHolds {A : Arch} (s : MachSt A) (loc : WordLoc A) (t : Ty) (v : Val t) : Prop :=
  match loc with
  | .gpr r => ValHolds64 t v (s.gpr r)
  | .slot k =>
    ∃ g : BitVec 64,
      loadVal s.mem i64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * k)) = some g ∧
      ValHolds64 t v g

/-- Full de Bruijn value stack `bvs` of depth `d` agrees with L1 register/slot storage. -/
@[expose] def EnvRel {A : Arch} (b : WordRegBind A) (spillBase d : Nat)
    (bvs : List ((t : Ty) × Val t)) (s : MachSt A) : Prop :=
  bvs.length = d ∧
  ∀ i, i < d →
    match listGet? bvs i with
    | some item => LocHolds s (locOf b spillBase (d - 1 - i)) item.1 item.2
    | none => False

/-- Hardware stack-memory reservation below `sp` (`budget` bytes + entry return slot). -/
@[expose] def hwStackMem (A : Arch) (sp ra : BitVec 64) (budget : Nat) : Mem 64 → Prop :=
  (vllFramePreds A).RetAddr sp ra ⋆ region (sp - BitVec.ofNat 64 budget) budget

/-- Lifted XCAP halt postcondition preserving caller memory frame `R`. -/
@[expose] def wordHaltPost (A : Arch) (H_L0 : HaltPost) (R : Mem 64 → Prop) :
    Xcap.Halt (MachSt A) :=
  fun c s => ∃ m', H_L0 c m' ∧ (s.mem =⋆ Eq m' ⋆ R)

/-- Stack byte budget required by one uncontified plain `CodeEntry` (`tempSpillCount` frame). -/
@[expose] def plainEntryBudget {A : Arch} (b : WordRegBind A) (bf : BlockFlat) : Nat :=
  let spills := tempSpillCount b (maxBlockDepth bf 6)
  if spills > 0 then A.abi.frameSize spills else 0

/-- Maximum stack byte budget across all blocks in an open `CodeMap`. -/
@[expose] def codeMapMaxBudget {A : Arch} (b : WordRegBind A) (cm : CodeMap) : Nat :=
  cm.foldl (fun m e => Nat.max m (plainEntryBudget b e.block)) 0

/-- Lookup table of hardware stack budgets (in bytes) for every `cr ∈ wit.regions`. -/
@[expose] def witnessBudgets {A : Arch} (b : WordRegBind A) (cm : CodeMap) :
    List ContifyRegion → List (Sym × Nat) → List (Sym × Nat)
  | [], acc => acc
  | cr :: rest, acc =>
    let selfFrame :=
      if regionNeedFrame b cm cr then A.abi.frameSize (regionFrameSlots b cm cr) else 0
    let maxCallee := cr.edges.foldl (fun accB ew =>
      match ew.kind with
      | .contCall callee _ _ _ _ =>
        let cb := (acc.find? fun p => p.1 == callee).map Prod.snd |>.getD 0
        Nat.max accB (A.abi.raBytes + cb)
      | _ => accB) 0
    let need := selfFrame + maxCallee
    witnessBudgets b cm rest ((cr.name, need) :: acc)

/-- Hardware stack budget (in bytes) needed upon entering `cr.name`. -/
@[expose] def regionStackBudget {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (wit : ContifyWitness) (cr : ContifyRegion) : Nat :=
  (witnessBudgets b cm wit.regions []).find? (fun p => p.1 == cr.name) |>.map Prod.snd |>.getD 0

/-- Entry invariant for open `fromWord` execution at L0 `st`. -/
@[expose] def WordPlainEntryRel {A : Arch} (b : WordRegBind A)
    (st : BedrockWord.State) (budget : Nat) (R : Mem 64 → Prop) (s : MachSt A) : Prop :=
  WordRegsRel b st.regs s ∧
  (budget = 0 → s.mem =⋆ Eq st.mem ⋆ R) ∧
  (budget > 0 → A.abi.spEntry (s.gpr A.abi.sp) ∧
    budget + A.abi.raBytes ≤ 2 ^ 64 ∧
    ∃ ra, (vllFramePreds A).raReg s ra ∧
      (s.mem =⋆ Eq st.mem ⋆ hwStackMem A (s.gpr A.abi.sp) ra budget ⋆ R))

/-- Halt predicate for `fromWord` preserving caller's memory frame `R` (and stack budget). -/
@[expose] def plainHaltPost (A : Arch) (H_L0 : HaltPost) (sp0 ra : BitVec 64) (budget : Nat)
    (R : Mem 64 → Prop) : Xcap.Halt (MachSt A) :=
  if budget = 0 then wordHaltPost A H_L0 R
  else wordHaltPost A H_L0 (hwStackMem A sp0 ra budget ⋆ R)

end LeanQbe.T.Vll
