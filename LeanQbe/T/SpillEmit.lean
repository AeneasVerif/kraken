module

public import LeanQbe.T.Live
public import LeanQbe.T.SpillFlags

/-!
# Register Allocation Emission, Parallel Moves, and `Spill` Context (`SpillEmit`, untrusted)

Split from `LeanQbe.T.Spill`: defines `Home`, `Cfg`, `ArmInfo`, `Ctx`, `EmitSt`, `Pend`,
operand-affinity / `VariantHint.disp` helpers, `emitParMoves`, `buildPre`, `allocDefs`,
`pickPlocs`, `pendFromArrivals`, `jumpSlotMoves`, `slotOpNoLoad`, and `emitAlloc`/`emitAllocB`.

Untrusted: `Rega.lowerFn` verifies every hint.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Spill

open Live Rega SpillFlags

inductive Home (Cond : Type) where
  | none | gpr (r : Nat) | vec (v : Nat) | flag (c : Cond) | slot (s : Nat) (w : SlotWidth)
  deriving Inhabited

/-- Root execution-frequency weight (scaled so branch discounting preserves precision). -/
def baseMult : Nat := 16

def regWeight (ps : List (Nat × Nat)) (r : Nat) : Nat :=
  ps.foldl (fun s (r', w) => if Nat.beq r r' then s + w else s) 0

def bestRegPref (xPrefs : List (Nat × Nat)) (xAvoid : List (Nat × Nat) := []) :
    List Nat → Option Nat
  | [] => none
  | r0 :: rs =>
    some (rs.foldl (fun (bestR, bestP, bestA) r =>
      let p := regWeight xPrefs r
      let a := regWeight xAvoid r
      let better := Nat.ble (bestP + 1) p || (Nat.beq p bestP && Nat.ble (a + 1) bestA)
      if better then (r, p, a) else (bestR, bestP, bestA))
      (r0, regWeight xPrefs r0, regWeight xAvoid r0)).1

def abiIdList {I : Isa} (allGpr : List I.Reg) (allVec : List I.VReg) :
    {ts : List Ty} → Tup (AbiReg I.Reg I.VReg) ts → List (Option (Sum Nat Nat))
  | [], () => []
  | _ :: _, (.gpr r, locs) => some (.inl (allGpr.idxOf r)) :: abiIdList allGpr allVec locs
  | _ :: _, (.vec v, locs) => some (.inr (allVec.idxOf v)) :: abiIdList allGpr allVec locs

def tupArgsToList : {ts : List Ty} → Tup (Arg VNat) ts → List (Option Nat)
  | [], () => []
  | _ :: _, (.var x, as) => some x :: tupArgsToList as
  | _ :: _, (.imm _, as) => none :: tupArgsToList as

def tupSymArgs (I : Isa) : {ts : List Ty} → Tup (Arg VNat) ts → List (Option SymArg)
  | [], () => []
  | t :: _, (a, as) => toSymArg I t a :: tupSymArgs I as

/-! ## Operand Affinity & `VariantHint.disp` Probing -/

def firstOpVar {ts : List Ty} (op : Op VNat ts) : Option Nat × Bool :=
  let { sig := _, code, args } := op
  match code, args with
  | .copy _, (.var a, ()) | .zext _ _, (.var a, ()) | .sext _ _, (.var a, ())
  | .trunc _ _, (.var a, ()) | .bitcast _ _ _, (.var a, ()) => (some a, true)
  | .add _, (.var a, _, ()) | .sub _, (.var a, _, ()) | .mul _, (.var a, _, ())
  | .and _, (.var a, _, ()) | .or _, (.var a, _, ()) | .xor _, (.var a, _, ())
  | .shl _, (.var a, _, ()) | .lshr _, (.var a, _, ()) | .ashr _, (.var a, _, ())
  | .rotl _, (.var a, _, ()) | .rotr _, (.var a, _, ())
  | .addc _, (.var a, _, _, ()) | .subb _, (.var a, _, _, ()) => (some a, false)
  | _, _ => (none, false)

/-- Affinity candidates `(srcVar, weightFactor)` for `op`'s primary output `d0`, giving priority
to dying first operands on 2-address ops and dying commutative/`select` operands. -/
def opAffVars {ts : List Ty} (op : Op VNat ts) (la : List Nat) : List (Nat × Nat) :=
  let { sig := _, code, args } := op
  let addDead {t : Ty} (a : Arg VNat t) (w : Nat) (acc : List (Nat × Nat)) :=
    match a with | .var x => if !natMem x la then (x, w) :: acc else acc | .imm _ => acc
  match code, args with
  | .copy _, (.var a, ()) | .zext _ _, (.var a, ()) | .sext _ _, (.var a, ())
  | .trunc _ _, (.var a, ()) | .bitcast _ _ _, (.var a, ()) =>
    if !natMem a la then [(a, 12)] else [(a, 6)]
  | .neg _, (a, ()) | .not _, (a, ()) | .bswap _, (a, ()) => addDead a 8 []
  | .add _, (a, b, ()) | .mul _, (a, b, ()) | .and _, (a, b, ())
  | .or _, (a, b, ()) | .xor _, (a, b, ()) => addDead a 8 (addDead b 6 [])
  | .sub _, (a, _, ()) | .shl _, (a, _, ()) | .lshr _, (a, _, ())
  | .ashr _, (a, _, ()) | .rotl _, (a, _, ()) | .rotr _, (a, _, ()) => addDead a 8 []
  | .addc _, (a, b, _, ()) => addDead a 8 (addDead b 6 [])
  | .subb _, (a, _, _, ()) => addDead a 8 []
  | .select _, (_, a, b, ()) => addDead a 6 (addDead b 6 [])
  | _, _ => []

/-- Preferred source var for `allocDefs` (first dead operand in `opAffVars`, or `firstOpVar`). -/
def prefOpVar {ts : List Ty} (op : Op VNat ts) (la : List Nat) : Option Nat :=
  (opAffVars op la).head?.map Prod.fst <|> (firstOpVar op).1

/-- Variant of `prefOpVar` skipping slot operands kept directly in memory (`noLoadOps`). -/
def prefOpVarSkip {ts : List Ty} (op : Op VNat ts) (la skip : List Nat) : Option Nat :=
  let vs := (opAffVars op la).filterMap fun (x, _) => if natMem x skip then none else some x
  vs.head? <|> ((firstOpVar op).1.filter (!natMem · skip))

/-- Probe whether `VariantHint.disp` produces strictly fewer directives than `.default` for an
`add`/`sub` immediate with distinct src/dst registers (e.g. x64 `lea` vs `mov; add`). -/
def tryDispHint (I : Isa) (r0 r1 : I.Reg) {ts : List Ty} (op : Op VNat ts)
    (rd : I.Reg) (ra? : Option I.Reg) : Option VariantHint :=
  if ra? == some rd then none
  else
    let { sig := _, code, args } := op
    let probe {w : Nat} (c : OpCode [.bits w, .bits w] [.bits w])
        (pas : Tup (PArg I.Reg I.VReg I.Cond) [.bits w, .bits w]) (off : Int64) :
        Option VariantHint :=
      match I.gpr.op c pas (.gpr r1, ()) (.disp off), I.gpr.op c pas (.gpr r1, ()) .default with
      | some (c1, _), some (c0, _) => if Nat.blt c1.length c0.length then some (.disp off) else none
      | _, _ => none
    match ts, code, args with
    | [.bits w], .add (.bits _), (.var _, .imm cb, ()) =>
      if Nat.beq w 64 || Nat.beq w 32 then
        probe (.add (.bits w)) (.gpr r0, .imm cb, ()) (Int64.ofBitVec (cb.signExtend 64))
      else none
    | [.bits w], .add (.bits _), (.imm ca, .var _, ()) =>
      if Nat.beq w 64 || Nat.beq w 32 then
        probe (.add (.bits w)) (.imm ca, .gpr r0, ()) (Int64.ofBitVec (ca.signExtend 64))
      else none
    | [.bits w], .sub (.bits _), (.var _, .imm cb, ()) =>
      if Nat.beq w 64 || Nat.beq w 32 then
        probe (.sub (.bits w)) (.gpr r0, .imm cb, ()) (Int64.ofBitVec (-(cb.signExtend 64)))
      else none
    | _, _, _ => none

def opImmSrcVar {ts : List Ty} (op : Op VNat ts) : Option Nat :=
  let { sig := _, code, args } := op
  match code, args with
  | .add (.bits _), (.var a, .imm _, ()) | .add (.bits _), (.imm _, .var a, ())
  | .sub (.bits _), (.var a, .imm _, ()) => some a
  | _, _ => none

/-! ## Spill Configuration and Allocation Context -/

/-- `Spill.Cfg` heuristic switches (untrusted: `Rega.lowerFn` re-checks every hint). `sink` defers
slot-home spill stores past straight-line code and into `jnz` arms; `joinGuard` keeps hot join
parameters out of slot-direct `Entry.ploc`; `cacheHint` gives a spilled variable a soft register
that later-colored interfering variables avoid; `regEntry` lets a block take a spilled live-in
in the register its predecessors hold it in; `armEvict` lets a variable that would be spilled keep
a register outside `jnz` arms (and, with `armLoops`, loops) where it is unused, evicting it on
entry (`armX`, on by default, extends this to call-crossing variables, which are then also split
around their calls). -/
structure Cfg where
  (sink joinGuard cacheHint regEntry : Bool := true)
  (armEvict armLoops : Bool := true)
  (armX : Bool := true)
  (backEdgeCoal immMoviDedup : Bool := true)

/-- Baseline configuration (all `Spill.Cfg` switches off), for ablation and regression tests. -/
def Cfg.legacy : Cfg :=
  { sink := false, joinGuard := false, cacheHint := false, regEntry := false, armEvict := false,
    backEdgeCoal := false, immMoviDedup := false }

/-- A non-trivial `jnz` arm (`key = 2 * ip + 1` for the then-arm, `2 * ip` for the else-arm):
its ip interval `[lo, hi)` (arms are contiguous in `Tree.ofFn` numbering), entry weight `w`,
live-in variables, labels declared inside it, and the jumps leaving it as
`(ip, target, weight, args)`. -/
structure ArmInfo where
  (key lo hi w : Nat)
  (liveIn blocks : List Nat)
  (exits : List (Nat × Nat × Nat × List Nat))
  deriving Inhabited

/-- Allocation context. Besides the target and liveness tables: `brW` maps a `jnz` to its
`(mult, multThen, multElse)` weights, `jmpW` a jump to its weight and `inW` a label to the summed
weight of its incoming jumps (all from `gather`); `hintT` maps a slot-homed variable to its
`(cache register, weight)` hint (from coloring); `regIn` lists, per label, the slot-homed
live-ins taken in a register as `(var, reg, alsoInSlot)`; `opt` selects the optimistic emission
pass that only gathers the predecessor statistics for `regIn`. -/
structure Ctx (I : Isa) where
  (allGpr : List I.Reg) (allVec : List I.VReg) (gReg : Trie I.Reg) (vReg : Trie I.VReg)
  (nGpr nVec : Nat) (gAlloc csIds vAlloc : List Nat) (gScr vScr : Option Nat)
  (cross loops : Trie Bool) (loopReach : Trie (List Nat)) (banks : Trie Bank)
  (flagHome : Trie I.Cond) (bparams lTrie : Trie (List Nat))
  (addrDeps : Trie (List Nat) := .empty)
  (isLeaf : Bool := false)
  (rmwDeps : Trie (List Nat) := .empty)
  (regionReused : Trie (List Nat) := .empty)
  (cfg : Cfg := {})
  (csCost : Nat := 2 * baseMult)
  (brW : Trie (Nat × Nat × Nat) := .empty)
  (hintT : Trie (Nat × Nat) := .empty)
  (jmpW inW : Trie Nat := .empty)
  (regIn : Trie (List (Nat × Nat × Bool)) := .empty)
  (evIn : Trie (List Nat) := .empty)
  (opt : Bool := false)
  (r0? : Option I.Reg := none)
  (zextElide : Trie Nat := .empty)
  (blkUses varBlks forceEv : Trie (List Nat) := .empty)
  (blkEdges : List (Nat × Nat × Nat × List Nat) := [])
  (armList : List ArmInfo := [])
  (armT : Trie ArmInfo := .empty)
  (varExt : Trie (Nat × Nat) := .empty)
  (useIps armEvAt : Trie (List Nat) := .empty)
  (ipW : Trie Nat := .empty)
  (foldIps : Trie Unit := .empty)
  (latchIps : Trie Bool := .empty)
  (latchPrefs : Trie (List (Nat × Nat)) := .empty)
  (blkLoops : Trie (List Nat) := .empty)

def isEagerBk (bk : Trie (Nat × SlotWidth × Bool)) (x : Nat) : Bool :=
  match bk.find? x with | some (_, _, e) => e | none => false

end Spill
end LeanQbe.T
end

/-! ## Parallel Moves, Slot-Direct Block Params, and Hint Emission

Nothing reduces the untrusted emission code in the kernel, so from here on declarations are
`public` but not `@[expose]`: their bodies stay out of the public `.olean`. -/

public section

namespace LeanQbe.T
namespace Spill

open Live Rega SpillFlags

def emitParMovesAux {α β : Type} (mkMov : α → α → β) (toR : Nat → α) (scrOpt : Option Nat) :
    Nat → List (Nat × Nat) → List β → List β
  | 0, _, acc | _, [], acc => acc.reverse
  | fuel + 1, pend, acc =>
    match pend.find? fun (d, _) => pend.all fun (_, s) => !Nat.beq s d with
    | some (d, s) =>
      let pend' := pend.filter fun p => !(Nat.beq p.1 d && Nat.beq p.2 s)
      emitParMovesAux mkMov toR scrOpt fuel pend'
        (if Nat.beq d s then acc else mkMov (toR d) (toR s) :: acc)
    | none =>
      match pend, scrOpt with
      | (d, s) :: rest, some tmp =>
        if Nat.beq d s then emitParMovesAux mkMov toR scrOpt fuel rest acc
        else
          let rest' := rest.map fun (d', s') => (d', if Nat.beq s' d then tmp else s')
          emitParMovesAux mkMov toR scrOpt fuel ((d, s) :: rest') (mkMov (toR tmp) (toR d) :: acc)
      | pend, none => acc.reverseAux (pend.map fun (d, s) => mkMov (toR d) (toR s))
      | [], _ => acc.reverse

def emitParMoves {α β : Type} (mkMov : α → α → β) (toR : Nat → α) (scrOpt : Option Nat)
    (pend : List (Nat × Nat)) : List β :=
  let pend := pend.filter fun (d, s) => !Nat.beq d s
  emitParMovesAux mkMov toR scrOpt (2 * pend.length + 2) pend []

def gprHomes {C : Type} (home : Trie (Home C)) (xs : List Nat) : List Nat :=
  xs.filterMap fun x => match home.getD x .none with | .gpr r => some r | _ => none
def vecHomes {C : Type} (home : Trie (Home C)) (xs : List Nat) : List Nat :=
  xs.filterMap fun x => match home.getD x .none with | .vec v => some v | _ => none
def freshReg (cands busy : List Nat) : Option Nat := cands.find? (!natMem · busy)

/-- Pick a free register, preferring registers not currently caching a spilled variable, then
registers not holding a deferred spill store (`keep`). -/
def freshRegAvoid (cands busy cached : List Nat) (keep : List Nat := []) : Option Nat :=
  freshReg (cands.filter (!natMem · cached)) busy <|>
    freshReg (cands.filter (!natMem · keep)) busy <|> freshReg cands busy

/-- Emitted hints; `cin` collects, in an optimistic pass, one `(label, var, reg, deferred,
weight)` record per jump and slot-homed variable that reaches the target cached in `reg`. -/
structure EmitSt (I : Isa) where
  (dest : Trie I.Loc := .empty) (entry : Trie (Entry I.Reg I.VReg I.Cond) := .empty)
  (pre : Trie (PreStep I.Reg I.VReg I.Cond) := .empty)
  (variant : Trie VariantHint := .empty) (usedCs : List Nat := [])
  (cin : List (Nat × Nat × Nat × Bool × Nat) := [])
  (evArr : List (Nat × Nat × Bool × Bool × Nat) := [])
  (latchArr : List (Nat × Nat × Nat) := [])

/-- Moves pending from the previous node: stores of slot-homed or eager-split arrivals
`(x, slot, reg)` and register-to-register arrival moves `(x, home, arrival)`, per bank; `gDf`
holds deferred slot-home stores `(x, slot, reg)` whose value still sits unclobbered in `reg`. -/
structure Pend where
  gSt : List (Nat × Nat × Nat) := []
  gDf : List (Nat × Nat × Nat) := []
  vSt : List (Nat × Nat × SlotWidth × Nat) := []
  gRg : List (Nat × Nat × Nat) := []
  vRg : List (Nat × Nat × Nat) := []

def recordPre {I : Isa} (ip : Nat) (clr : Bool) (mvs : List I.Move)
    (pre : Trie (PreStep I.Reg I.VReg I.Cond)) : Trie (PreStep I.Reg I.VReg I.Cond) :=
  if !clr && mvs.isEmpty then pre else pre.insert ip ⟨clr, mvs⟩

/-- Split-variable moves: backup stores (`save`) or reloads of `xs` between home and backup. -/
def splitMoves {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond))
    (bk : Trie (Nat × SlotWidth × Bool)) (save : Bool) (xs : List Nat) : List I.Move :=
  xs.filterMap fun x => (bk.find? x).bind fun (b, w, _) =>
    match home.getD x .none with
    | .gpr r => let g := c.gReg.getD r I.frame.sp; some (if save then .st b g else .ld g b)
    | .vec v => (c.vReg.find? v).map fun vr => if save then .vst w b vr else .vld w vr b
    | _ => none

/-- Registers overwritten by `splitMoves ... false xs` (reloads). -/
def splitReloadRegs {C : Type} (home : Trie (Home C)) (xs : List Nat) : List Nat × List Nat :=
  xs.foldl (fun (gs, vs) x =>
    match home.getD x .none with
    | .gpr r => (r :: gs, vs)
    | .vec v => (gs, v :: vs)
    | _ => (gs, vs)) ([], [])

/-- Estimated weighted cost (spill stores plus edge-block jumps) of deferring the slot store of
`x` into a tree of execution weight `w`; `arm` marks a direct `jnz` arm. Register clobbers are
ignored: a clobber only moves the store, it never adds one. -/
def sinkCost {I : Isa} (c : Ctx I) (x : Nat) : Nat → Bool → Tree → Nat
  | w, _, .let_ _ _ _ _ _ k | w, _, .load _ _ _ _ _ k | w, _, .store _ _ _ _ _ k
  | w, _, .skip _ _ k => if natMem x k.lv then sinkCost c x w false k else 0
  | w, _, .call _ _ _ _ _ _ _ k => if natMem x k.lv then w else 0
  | w, _, .jnz _ ip _ _ t e =>
    let (_, mT, mE) := c.brW.getD ip (w, w, w)
    let cT := if natMem x t.lv then sinkCost c x mT true t else 0
    let cE := if natMem x e.lv then sinkCost c x mE true e else 0
    cT + cE
  | w, _, .jump _ _ j _ _ =>
    if natMem x (c.lTrie.getD j []) &&
        !((c.regIn.getD j []).any fun (y, _, inS) => Nat.beq y x && !inS) then 2 * w
    else 0
  | w, arm, .group _ _ k => sinkCost c x w arm k
  | _, _, .ret .. | _, _, .exit .. | _, _, .stop _ => 0

/-- Sink the deferred store of `x` into the arms of `jnz ip` iff that is estimated strictly
cheaper than storing before the branch. -/
private def sinkOk {I : Isa} (c : Ctx I) (ip : Nat) (t e : Tree) (x : Nat) : Bool :=
  c.opt || match c.brW.find? ip with
  | some (m, mT, mE) =>
    let cT := if natMem x t.lv then sinkCost c x mT true t else 0
    let cE := if natMem x e.lv then sinkCost c x mE true e else 0
    let pen := match e with | .jump .. => if Nat.ble 1 cE then mT else 0 | _ => 0
    Nat.blt (cT + cE + pen) m
  | none => false

/-- Emit (prepend) the deferred stores selected by `p`; return the moves and the rest. All
deferred registers are intact at `PreStep` entry, so prepending is always sound. -/
private def flushDf {I : Isa} (c : Ctx I) (p : Nat × Nat × Nat → Bool) (mvs : List I.Move)
    (df : List (Nat × Nat × Nat)) : List I.Move × List (Nat × Nat × Nat) :=
  match df.filter p with
  | [] => (mvs, df)
  | fl =>
    let srEq (a b : Nat × Nat × Nat) := Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2 b.2.2
    let uniq := fl.foldl (fun acc e => if acc.any (srEq e) then acc else e :: acc) []
    ((uniq.reverse.map fun (_, s, r) => .st s (c.gReg.getD r I.frame.sp)) ++ mvs,
     df.filter fun e => !fl.any (srEq e))

/-- `PreStep` moves + updated straight-line spilled-operand register caches `(gCache', vCache')`
+ deferred slot-home stores. Elides `.st`/`.vst` for pending values that die at this instruction
and are not clobbered by arrival moves or split reloads, reusing cached regs for spilled
operands. With `cfg.sink`, a live slot-home GPR store stays deferred (`Pend.gDf`) for as long
as its register survives in `gCache'`; otherwise it is emitted here. -/
def buildPre {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (usedCs : List Nat)
    (ipLive liveAfter ops : List Nat) (pd : Pend) (extra : List I.Move)
    (extraWG extraWV : List Nat) (gCache vCache : List (Nat × Nat))
    (noLoadOps : List Nat := []) (evAfter : List Nat := []) :
    List I.Move × List (Nat × Nat) × List (Nat × Nat) × List (Nat × Nat × Nat) :=
  let gOf (r : Nat) := c.gReg.getD r I.frame.sp
  let wG := pd.gRg.map fun (_, d, _) => d
  let wV := pd.vRg.map fun (_, d, _) => d
  let clobG := wG ++ extraWG
  let clobV := wV ++ extraWV
  let isSlotHome (x : Nat) : Bool :=
    match home.getD x .none with | .slot _ _ => true | _ => false
  let cand := if c.cfg.sink then (pd.gSt.filter fun (x, _, _) => isSlotHome x) ++ pd.gDf else []
  let pdG := if c.cfg.sink then pd.gSt.filter fun (x, _, _) => !isSlotHome x else pd.gSt
  let candDf := cand.filter fun (x, _, r) => natMem x liveAfter && !natMem r clobG
  let keepGSt := (pdG.filter fun (x, _, r) => natMem x liveAfter || natMem r clobG) ++
    cand.filter fun (x, _, r) => natMem x ipLive && natMem r clobG
  let inCache (gc : List (Nat × Nat)) (e : Nat × Nat × Nat) : Bool :=
    gc.any fun (y, r') => Nat.beq y e.1 && Nat.beq r' e.2.2
  let keepVSt := pd.vSt.filter fun (x, _, _, v) => natMem x liveAfter || natMem v clobV
  let gStMvs : List I.Move := keepGSt.map fun (_, s, r) => .st s (gOf r)
  let vStMvs : List I.Move :=
    keepVSt.filterMap fun (_, s, w, v) => (c.vReg.find? v).map (.vst w s)
  let gRegMvs : List I.Move := emitParMoves Move.mov gOf c.gScr (pd.gRg.map fun (_, d, s) => (d, s))
  let vW := pd.vRg.foldl (fun w (x, _, _) => maxSlotWidth w (c.banks.getD x .gpr).slotWidth) .w64
  let vRegMvs : List I.Move := match c.vReg.find? 0 with
    | none => []
    | some v0 =>
      emitParMoves (Move.vmov vW) (fun i => c.vReg.getD i v0) c.vScr
        (pd.vRg.map fun (_, d, s) => (d, s))
  let baseMvs := gStMvs ++ vStMvs ++ gRegMvs ++ vRegMvs ++ extra
  let gCache0 := gCache.filter fun (x, r) => natMem x ipLive && !natMem r clobG
  let vCache0 := vCache.filter fun (x, v) => natMem x ipLive && !natMem v clobV
  let gCache1 := pd.gSt.foldl (fun gc (x, _, r) =>
    if isSlotHome x && natMem x ipLive && !natMem r clobG then
      (x, r) :: gc.filter fun (_, r') => !Nat.beq r' r
    else gc) gCache0
  let vCache1 := pd.vSt.foldl (fun vc (x, _, _, v) =>
    if isSlotHome x && natMem x ipLive && !natMem v clobV then
      (x, v) :: vc.filter fun (_, v') => !Nat.beq v' v
    else vc) vCache0
  let needOps := ops.filter (!natMem · noLoadOps)
  if !(needOps.any isSlotHome) then
    let (mvs, kept) := flushDf c (!inCache gCache1 ·) baseMvs candDf
    (mvs, gCache1, vCache1, kept)
  else
    let ipNotEv := if evAfter.isEmpty then ipLive else ipLive.filter (!natMem · evAfter)
    let initGB := gprHomes home ipNotEv ++
      gCache1.filterMap fun (x, r) => if natMem x ops then some r else none
    let initVB := vecHomes home ipNotEv ++
      vCache1.filterMap fun (x, v) => if natMem x ops then some v else none
    let (_, _, gc', vc', ldRev) := ops.foldl (fun (gb, vb, gc, vc, mvs) x =>
      match home.getD x .none with
      | .slot s w =>
        if (c.banks.getD x .gpr).isVec then
          if vc.any (fun (y, _) => Nat.beq y x) then (gb, vb, gc, vc, mvs)
          else
            let cachedV := vc.map Prod.snd
            match (freshRegAvoid c.vAlloc vb cachedV).bind fun v => (c.vReg.find? v).map (v, ·) with
            | some (v, vr) =>
              let vc1 := (x, v) :: vc.filter fun (_, v') => !Nat.beq v' v
              (gb, v :: vb, gc, vc1, .vld w vr s :: mvs)
            | none => (gb, vb, gc, vc, mvs)
        else
          if gc.any (fun (y, _) => Nat.beq y x) then (gb, vb, gc, vc, mvs)
          else if natMem x noLoadOps then (gb, vb, gc, vc, mvs)
          else
            let cachedG := gc.map Prod.snd
            let hReg? := (c.hintT.find? x).bind fun (rh, _) =>
              if (Nat.ble (rh + 1) c.nGpr || natMem rh usedCs) &&
                  !natMem rh gb && !natMem rh cachedG then some rh else none
            let rCand := hReg? <|>
              freshRegAvoid (c.gAlloc ++ usedCs) gb cachedG (candDf.map (·.2.2))
            match rCand with
            | some r =>
              let gc1 := (x, r) :: gc.filter fun (_, r') => !Nat.beq r' r
              (r :: gb, vb, gc1, vc, .ld (gOf r) s :: mvs)
            | none => (gb, vb, gc, vc, mvs)
      | _ => (gb, vb, gc, vc, mvs)) (initGB, initVB, gCache1, vCache1, [])
    let (mvs, kept) := flushDf c (!inCache gc' ·) (baseMvs ++ ldRev.reverse) candDf
    (mvs, gc', vc', kept)

def allocDefs {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond))
    (bk : Trie (Nat × SlotWidth × Bool)) (usedCs : List Nat) (defs la : List Nat)
    (prefVar? : Option Nat) (cachedGPairs : List (Nat × Nat)) (cachedV : List Nat)
    (dest : Trie I.Loc) (evAfter : List Nat := []) :
    Trie I.Loc × List (Nat × Nat × Nat) × List (Nat × Nat × SlotWidth × Nat) ×
      List Nat × List Nat :=
  let gOf (r : Nat) := c.gReg.getD r I.frame.sp
  let cachedG := cachedGPairs.filterMap fun (y, r) => if natMem y la then some r else none
  let pickG (gb sibG : List Nat) (pref : Option Nat) :=
    pref.filter (!natMem · sibG) <|> freshRegAvoid (c.gAlloc ++ usedCs) gb cachedG <|>
      c.gAlloc.find? (!natMem · sibG) <|> c.gAlloc.head?
  let pickV (vb sibV : List Nat) (pref : Option Nat) :=
    pref.filter (!natMem · sibV) <|> freshRegAvoid c.vAlloc vb cachedV <|>
      c.vAlloc.find? (!natMem · sibV) <|> c.vAlloc.head?
  let laNotEv := if evAfter.isEmpty then la else la.filter (!natMem · evAfter)
  let initGb := gprHomes home (union defs laNotEv)
  let initVb := vecHomes home (union defs laNotEv)
  let initSibG := gprHomes home defs
  let initSibV := vecHomes home defs
  let (dest', _, _, _, _, gSt, vSt, wG, wV) := defs.foldl
    (fun (dT, gb, vb, sibG, sibV, gS, vS, wg, wv) x => match home.getD x .none with
      | .flag cc => (dT.insert x (.flag cc), gb, vb, sibG, sibV, gS, vS, wg, wv)
      | .gpr r =>
        let gS' := match bk.find? x with
          | some (b, _, true) => (x, b, r) :: gS | _ => gS
        (dT.insert x (.gpr (gOf r)), r :: gb, vb, r :: sibG, sibV, gS', vS, r :: wg, wv)
      | .vec v =>
        match c.vReg.find? v with
        | some vr =>
          let vS' := match bk.find? x with
            | some (b, w, true) => (x, b, w, v) :: vS | _ => vS
          (dT.insert x (.vec vr), gb, v :: vb, sibG, v :: sibV, gS, vS', wg, v :: wv)
        | none => (dT, gb, vb, sibG, sibV, gS, vS, wg, wv)
      | h =>
        let spill? := match h with | .slot s w => some (s, w) | _ => none
        if (c.banks.getD x .gpr).isVec then
          let pref :=
            if spill?.isSome then prefVar?.bind fun a => match home.getD a .none with
              | .vec va => if Nat.ble (va + 1) c.nVec && !natMem va vb then some va else none
              | _ => none
            else none
          match (pickV vb sibV pref).bind fun v => (c.vReg.find? v).map (v, ·) with
          | some (v, vr) =>
            let vS' := match spill? with | some (s, w) => (x, s, w, v) :: vS | none => vS
            (dT.insert x (.vec vr), gb, v :: vb, sibG, v :: sibV, gS, vS', wg, v :: wv)
          | none => (dT, gb, vb, sibG, sibV, gS, vS, wg, wv)
        else
          let pref :=
            if spill?.isSome then prefVar?.bind fun a =>
              let ra? : Option Nat := match home.getD a .none with
                | .gpr ra => some ra
                | _ =>
                  if natMem a la then none
                  else (cachedGPairs.find? fun (y, _) => Nat.beq y a).map Prod.snd
              ra?.filter fun ra =>
                (Nat.ble (ra + 1) c.nGpr || natMem ra usedCs) && !natMem ra gb &&
                  !(cachedGPairs.any fun (y, r) => Nat.beq r ra && natMem y la)
            else none
          let hintR :=
            if spill?.isSome then (c.hintT.find? x).bind fun (rh, _) =>
              if (Nat.ble (rh + 1) c.nGpr || natMem rh usedCs) && !natMem rh gb &&
                  !(cachedGPairs.any fun (y, r) => Nat.beq r rh && natMem y la) then some rh
              else none
            else none
          match pickG gb sibG (pref <|> hintR) with
          | some r =>
            let gS' := match spill? with | some (s, _) => (x, s, r) :: gS | none => gS
            (dT.insert x (.gpr (gOf r)), r :: gb, vb, r :: sibG, sibV, gS', vS, r :: wg, wv)
          | none => (dT, gb, vb, sibG, sibV, gS, vS, wg, wv))
    (dest, initGb, initVb, initSibG, initSibV, [], [], [], [])
  (dest', gSt, vSt, wG, wV)

def pickPlocs {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (slotOk : Trie Bool)
    (liveL ps usedCs : List Nat) (inRegs : List Nat := []) :
    List I.Loc × List (Option (Sum Nat Nat)) × List Nat :=
  let gOf (r : Nat) := c.gReg.getD r I.frame.sp
  let (locsRev, idsRev, _, _, cs') := ps.foldl (fun (ls, ids, gb, vb, cs) p =>
    let pickGpr (hr : Option Nat) :=
      let lp := c.latchPrefs.getD p []
      let lr := if lp.isEmpty then none
        else bestRegPref lp [] ((c.gAlloc ++ cs).filter (!natMem · gb))
      match lr <|> hr <|> freshReg (c.gAlloc ++ cs) gb with
      | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
      | none => match c.csIds.find? (fun r => !natMem r gb && !natMem r cs) with
        | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs ++ [r])
        | none => match c.gAlloc.head? with
          | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
          | none => (ls, none :: ids, gb, vb, cs)
    match home.getD p .none with
    | .flag cc => (.flag cc :: ls, none :: ids, gb, vb, cs)
    | .gpr r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
    | .vec v => match c.vReg.find? v with
      | some vr => (.vec vr :: ls, some (.inr v) :: ids, gb, v :: vb, cs)
      | none => (ls, none :: ids, gb, vb, cs)
    | .slot s .w64 =>
      if slotOk.getD p false then (.slot s .w64 :: ls, none :: ids, gb, vb, cs)
      else
        let hr := (c.hintT.find? p).bind fun (rh, _) =>
          if (Nat.ble (rh + 1) c.nGpr || natMem rh cs) && !natMem rh gb then some rh else none
        pickGpr hr
    | _ =>
      if (c.banks.getD p .gpr).isVec then
        match (freshReg c.vAlloc vb <|> c.vAlloc.head?).bind fun v =>
            (c.vReg.find? v).map (v, ·) with
        | some (v, vr) => (.vec vr :: ls, some (.inr v) :: ids, gb, v :: vb, cs)
        | none => (ls, none :: ids, gb, vb, cs)
      else pickGpr none)
    ([], [], inRegs ++ gprHomes home liveL ++ gprHomes home ps,
      vecHomes home liveL ++ vecHomes home ps, usedCs)
  (locsRev.reverse, idsRev.reverse, cs')

def pendFromArrivals {C : Type} (home : Trie (Home C)) (bk : Trie (Nat × SlotWidth × Bool))
    (ps : List Nat) (arr : List (Option (Sum Nat Nat))) : Pend :=
  (ps.zip arr).foldl (fun pd (x, ao) =>
    match ao, home.getD x .none with
    | some (.inl rA), .gpr rH =>
      let pd := match bk.find? x with
        | some (b, _, true) => { pd with gSt := (x, b, rA) :: pd.gSt }
        | _ => pd
      if Nat.beq rH rA then pd else { pd with gRg := (x, rH, rA) :: pd.gRg }
    | some (.inl rA), .slot s _ => { pd with gSt := (x, s, rA) :: pd.gSt }
    | some (.inr vA), .vec vH =>
      let pd := match bk.find? x with
        | some (b, w, true) => { pd with vSt := (x, b, w, vA) :: pd.vSt }
        | _ => pd
      if Nat.beq vH vA then pd else { pd with vRg := (x, vH, vA) :: pd.vRg }
    | some (.inr vA), .slot s w => { pd with vSt := (x, s, w, vA) :: pd.vSt }
    | _, _ => pd) {}

/-- Emit `PreStep` moves for jump arguments targeting slot-direct block parameters (`.slot s .w64`).
Identity/coalesced slot args emit zero moves; GPR/cached args emit `.st s r`; immediates and
other-slot args materialize through one free non-scratch GPR. -/
def jumpSlotMoves {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (slotOk : Trie Bool)
    (usedCs : List Nat) (lv : List Nat) (j : Nat) {ts : List Ty} (args : Tup (Arg VNat) ts)
    (gCache : List (Nat × Nat)) : List I.Move :=
  let ps := c.bparams.getD j []
  let sas := tupSymArgs I args
  let gOf (r : Nat) := c.gReg.getD r I.frame.sp
  let busy := gprHomes home lv ++ gCache.map Prod.snd
  let cands := c.gAlloc ++ usedCs
  let tmp? := freshReg cands busy <|> freshReg cands (gprHomes home lv)
  let emitImm (mvs : List I.Move) (immRegs : List (BitVec 64 × Nat))
      (s : Nat) (k64 : BitVec 64) : List I.Move × List (BitVec 64 × Nat) :=
    if c.cfg.immMoviDedup then
      match immRegs.find? fun (k', _) => k' == k64 with
      | some (_, r) => (mvs ++ [.st s (gOf r)], immRegs)
      | none =>
        let r? := freshReg cands (busy ++ immRegs.map Prod.snd) <|> tmp?
        match r? with
        | some tmp =>
          let ir' := (k64, tmp) :: immRegs.filter fun (_, r) => !Nat.beq r tmp
          (mvs ++ [.movi (gOf tmp) k64, .st s (gOf tmp)], ir')
        | none => (mvs, immRegs)
    else
      match tmp? with
      | some tmp => (mvs ++ [.movi (gOf tmp) k64, .st s (gOf tmp)], immRegs)
      | none => (mvs, immRegs)
  ((sas.zip ps).foldl (fun (mvs, immRegs) (sao, p) =>
    if !slotOk.getD p false then (mvs, immRegs)
    else match home.getD p .none with
      | .slot s .w64 =>
        match sao with
        | some (.var x) =>
          match home.getD x .none with
          | .slot s' .w64 =>
            if Nat.beq s s' then (mvs, immRegs)
            else match gCache.find? (fun (y, _) => Nat.beq y x) with
              | some (_, r) => (mvs ++ [.st s (gOf r)], immRegs)
              | none => match tmp? with
                | some tmp =>
                  (mvs ++ [.ld (gOf tmp) s', .st s (gOf tmp)],
                    immRegs.filter fun (_, r) => !Nat.beq r tmp)
                | none => (mvs, immRegs)
          | .gpr r => (mvs ++ [.st s (gOf r)], immRegs)
          | .flag cc =>
            match tmp? with
            | some tmp =>
              (mvs ++ [.setcc (gOf tmp) cc, .st s (gOf tmp)],
                immRegs.filter fun (_, r) => !Nat.beq r tmp)
            | none => (mvs, immRegs)
          | _ => (mvs, immRegs)
        | some (.immBits _ k) => emitImm mvs immRegs s (k.setWidth 64)
        | some (.immBool b) => emitImm mvs immRegs s (if b then 1#64 else 0#64)
        | _ => (mvs, immRegs)
      | _ => (mvs, immRegs)) ([], [])).1

/-- Slot-homed uncached operands that `Rega.trySlotOp` can keep in `[%rsp+off]` directly. -/
private def slotOpNoLoad {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (r0? : Option I.Reg)
    (lv _la : List Nat) (pd : Pend) (rl : List Nat) (gC : List (Nat × Nat))
    (ip nv0 : Nat) {ts : List Ty} (op : Op VNat ts) : List Nat :=
  if (c.addrDeps.find? ip).isSome then []
  else
    let (rlWG, _) := splitReloadRegs home rl
    let clobG := (pd.gRg.map fun (_, d, _) => d) ++ rlWG
    let isSlot (x : Nat) : Bool :=
      match home.getD x .none with | .slot _ .w64 => true | _ => false
    let inCache (x : Nat) : Bool :=
      gC.any (fun (y, r) => Nat.beq y x && natMem x lv && !natMem r clobG) ||
      pd.gSt.any fun (y, _, r) => Nat.beq y x && isSlot y && natMem x lv && !natMem r clobG
    let isUncachedSlot (x : Nat) : Bool := isSlot x && !inCache x
    let hasGprAt (x : Nat) : Bool :=
      (match home.getD x .none with | .gpr _ => true | _ => false) || inCache x
    let tryAlu {n : Nat} (isAddSub : Bool) (code : OpCode [.bits n, .bits n] [.bits n])
        (a b : Arg VNat (.bits n)) : List Nat :=
      let aluOk (memRhs : Bool) : Bool := isStdBitWidth n &&
        (r0?.map fun r => (I.gpr.aluMem n code memRhs (.baseDisp I.frame.sp 0) (.gpr r) r).isSome
          ).getD false
      let sameReg (src : Nat) : Bool :=
        match home.getD nv0 .none, home.getD src .none with
        | .gpr rd, .gpr rs => Nat.beq rd rs
        | _, _ => false
      match a, b with
      | .var x, .var y =>
        if isUncachedSlot y && hasGprAt x && aluOk true && (!natMem x _la || sameReg x) then [y]
        else if isUncachedSlot x && hasGprAt y && aluOk false && (!natMem y _la || sameReg y)
          then [x]
        else []
      | .var x, .imm _ =>
        if isUncachedSlot x && aluOk false && (!isAddSub || !natMem x _la) then [x] else []
      | .imm _, .var y =>
        if isUncachedSlot y && aluOk true && (!isAddSub || !natMem y _la) then [y] else []
      | _, _ => []
    let { sig := _, code, args } := op
    match code, args with
    | .cmp co (.bits n) .bool _, (a, b, ()) =>
      let pdProbe? (r : I.Reg) : PDst I.Reg I.VReg I.Cond .bool :=
        match home.getD nv0 .none with | .flag cc => .flag cc | _ => .gpr r
      let cmpOk (co' : CmpOp) : Bool := I.supportsCmpMem (.bits n) && isStdBitWidth n &&
        (r0?.map fun r => (I.gpr.cmpMem co' n (.baseDisp I.frame.sp 0) (.imm 0#n)
          (pdProbe? r)).isSome).getD false
      match a, b with
      | .var x, .var y =>
        if Nat.beq x y then []
        else if isUncachedSlot x && cmpOk co && (!natMem x _la || !isUncachedSlot y) then [x]
        else if isUncachedSlot y && cmpOk co.swap then [y]
        else []
      | .var x, .imm _ => if isUncachedSlot x && cmpOk co then [x] else []
      | .imm _, .var y => if isUncachedSlot y && cmpOk co.swap then [y] else []
      | _, _ => []
    | .add (.bits n), (a, b, ()) => tryAlu true (.add (.bits n)) a b
    | .sub (.bits n), (a, b, ()) => tryAlu true (.sub (.bits n)) a b
    | .mul (.bits n), (a, b, ()) => tryAlu false (.mul (.bits n)) a b
    | .and (.bits n), (a, b, ()) => tryAlu false (.and (.bits n)) a b
    | .or  (.bits n), (a, b, ()) => tryAlu false (.or  (.bits n)) a b
    | .xor (.bits n), (a, b, ()) => tryAlu false (.xor (.bits n)) a b
    | _, _ => []

/-! Hint emission. Besides pending arrival moves, each path threads `ev` (split variables currently
only in their backup slot), `sv` (split variables whose backup slot holds their value), and
`(gCache, vCache)` (spilled variables whose values remain untouched in registers). -/
mutual
def emitAlloc {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond))
    (bk : Trie (Nat × SlotWidth × Bool)) (slotOk clrAt : Trie Bool) (r0 r1 : Option I.Reg) :
    Tree → Pend → List Nat → List Nat → List (Nat × Nat) → List (Nat × Nat) →
    EmitSt I → EmitSt I
  | .let_ lv ip nv0 ts op k, pd, ev, sv, gC, vC, st =>
    let ops := c.addrDeps.getD ip (opVarIds op)
    let rl := ops.filter (natMem · ev)
    let evAfter := eraseMany rl ev
    let (rlWG, rlWV) := splitReloadRegs home rl
    let defs := (List.range ts.length).map (nv0 + ·)
    let laAfter := eraseMany defs k.lv
    let (mvs0, gC1, vC1, df1) := buildPre c home st.usedCs lv laAfter ops pd
      (splitMoves c home bk false rl) rlWG rlWV gC vC [] evAfter
    let zextShare? : Option (Nat × Option Nat) :=
      (c.zextElide.find? ip).bind fun zx =>
        match home.getD zx .none, home.getD nv0 .none with
        | .gpr rx, .gpr ry =>
          if Nat.beq rx ry && (bk.find? zx).isNone && (bk.find? nv0).isNone then some (rx, none)
          else none
        | .slot sx .w64, .slot sy .w64 =>
          if Nat.beq sx sy then
            (gC1.find? fun (u, _) => Nat.beq u zx).map fun (_, rx) => (rx, some sy)
          else none
        | _, _ => none
    match zextShare? with
    | some (rx, slotOpt) =>
      let dest := st.dest.insert nv0 (.gpr (c.gReg.getD rx I.frame.sp))
      let (gSt', df2, gC2) :
          List (Nat × Nat × Nat) × List (Nat × Nat × Nat) × List (Nat × Nat) :=
        match slotOpt with
        | none => ([], df1, gC1.filter fun (x, _) => natMem x k.lv)
        | some sy =>
          if c.cfg.sink then
            let df' := if natMem nv0 k.lv then (nv0, sy, rx) :: df1 else df1
            let gc' := (if natMem nv0 k.lv then [(nv0, rx)] else []) ++
              gC1.filter fun (x, _) => natMem x k.lv
            ([], df', gc')
          else
            let gS := if natMem nv0 k.lv then [(nv0, sy, rx)] else []
            (gS, df1, gC1.filter fun (x, _) => natMem x k.lv)
      let vC2 := vC1.filter fun (x, _) => natMem x k.lv
      emitAlloc c home bk slotOk clrAt r0 r1 k { gSt := gSt', gDf := df2 }
        evAfter sv gC2 vC2
        { st with dest := dest, pre := recordPre ip (clrAt.getD ip false) mvs0 st.pre }
    | none =>
      let noLoad := (slotOpNoLoad c home r0 lv laAfter pd rl gC ip nv0 op).filter
        (!natMem · (c.regionReused.getD ip []))
      let (mvs0, gC1, vC1, df1) :=
        if noLoad.isEmpty then (mvs0, gC1, vC1, df1)
        else buildPre c home st.usedCs lv laAfter ops pd
          (splitMoves c home bk false rl) rlWG rlWV gC vC noLoad evAfter
      let (dest, gSt', vSt', wG, wV) := allocDefs c home bk st.usedCs defs k.lv
        (prefOpVarSkip op k.lv noLoad) gC1 (vC1.map Prod.snd) st.dest evAfter
      let (mvs, df2) := flushDf c (natMem ·.2.2 wG) mvs0 df1
      let var' := match r0, r1, st.variant.find? ip, dest.find? nv0 with
        | some a0, some a1, none, some (.gpr rd) =>
          let ra? := (opImmSrcVar op).bind fun a =>
            match home.getD a .none with
            | .gpr ra => some (c.gReg.getD ra I.frame.sp)
            | _ =>
              (gC1.find? (fun (y, _) => Nat.beq y a)).map fun (_, ra) => c.gReg.getD ra I.frame.sp
          match tryDispHint I a0 a1 op rd ra? with
          | some vh => st.variant.insert ip vh
          | none => st.variant
        | _, _, _, _ => st.variant
      let gC2 := gC1.filter fun (x, r) => natMem x k.lv && !natMem r wG
      let vC2 := vC1.filter fun (x, v) => natMem x k.lv && !natMem v wV
      let sv' := union sv (defs.filter (isEagerBk bk))
      emitAlloc c home bk slotOk clrAt r0 r1 k { gSt := gSt', vSt := vSt', gDf := df2 }
        evAfter sv' gC2 vC2
        { st with dest := dest, pre := recordPre ip (clrAt.getD ip false) mvs st.pre,
                  variant := var' }
  | .load lv ip x _ a k, pd, ev, sv, gC, vC, st =>
    let ops := c.addrDeps.getD ip (argVarIds a)
    let rl := ops.filter (natMem · ev)
    let evAfter := eraseMany rl ev
    let (rlWG, rlWV) := splitReloadRegs home rl
    let laAfter := erase x k.lv
    let (mvs0, gC1, vC1, df1) := buildPre c home st.usedCs lv laAfter ops pd
      (splitMoves c home bk false rl) rlWG rlWV gC vC [] evAfter
    let (dest, gSt', vSt', wG, wV) := allocDefs c home bk st.usedCs [x] k.lv none
      gC1 (vC1.map Prod.snd) st.dest evAfter
    let (mvs, df2) := flushDf c (natMem ·.2.2 wG) mvs0 df1
    let gC2 := gC1.filter fun (y, r) => natMem y k.lv && !natMem r wG
    let vC2 := vC1.filter fun (y, v) => natMem y k.lv && !natMem v wV
    let sv' := if isEagerBk bk x then union sv [x] else sv
    emitAlloc c home bk slotOk clrAt r0 r1 k { gSt := gSt', vSt := vSt', gDf := df2 }
      evAfter sv' gC2 vC2
      { st with dest := dest, pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .store lv ip _ v a k, pd, ev, sv, gC, vC, st =>
    let ops := storeVarIds c.addrDeps c.rmwDeps ip v a
    let rl := ops.filter (natMem · ev)
    let evAfter := eraseMany rl ev
    let (rlWG, rlWV) := splitReloadRegs home rl
    let (mvs, gC1, vC1, df1) := buildPre c home st.usedCs lv k.lv ops pd
      (splitMoves c home bk false rl) rlWG rlWV gC vC [] evAfter
    emitAlloc c home bk slotOk clrAt r0 r1 k { gDf := df1 } evAfter sv
      (gC1.filter fun (y, _) => natMem y k.lv) (vC1.filter fun (y, _) => natMem y k.lv)
      { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .call lv ip nv0 _ _ bs _ k, pd, ev, sv, gC, vC, st =>
    let defs := (List.range bs.length).map (nv0 + ·)
    let laAfter := eraseMany defs k.lv
    -- Callee-saved GPRs in `st.usedCs` survive `.call` without backup save/eviction.
    let isCallClob (x : Nat) : Bool :=
      match home.getD x .none with
      | .gpr r => Nat.blt r c.nGpr || !natMem r st.usedCs
      | .vec _ => true
      | _ => false
    let la := laAfter.filter fun x => (bk.find? x).isSome && isCallClob x
    let sav := la.filter fun x => !natMem x ev && !natMem x sv
    let (mvs0, gC1, _, df1) := buildPre c home st.usedCs lv laAfter [] pd
      (splitMoves c home bk true sav) [] [] gC vC
    let (mvs, _) := flushDf c (fun _ => true) mvs0 df1
    let arr := match I.assignRets bs with
      | some locs => abiIdList c.allGpr c.allVec locs | none => []
    let sv' := union (union sv sav) (defs.filter (isEagerBk bk))
    let defG := gprHomes home defs
    let gC' := gC1.filter fun (y, r) =>
      natMem y laAfter && natMem r st.usedCs && !natMem r defG
    emitAlloc c home bk slotOk clrAt r0 r1 k (pendFromArrivals home bk defs arr)
      (union ev la) sv' gC' []
      { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .jnz lv ip cx _ t e, pd, ev, sv, gC, vC, st =>
    let rl := if natMem cx ev then [cx] else []
    let ev' := eraseMany rl ev
    let (rlWG, rlWV) := splitReloadRegs home rl
    let laAfter := union t.lv e.lv
    let noLoad := match home.getD cx .none with
      | .slot _ .w64 =>
        if (I.gpr.jnzMem (.baseDisp I.frame.sp 0) false "").isSome then [cx] else []
      | _ => []
    let (mvs0, gC1, vC1, df1) := buildPre c home st.usedCs lv laAfter [cx] pd
      (splitMoves c home bk false rl) rlWG rlWV gC vC noLoad ev'
    let (mvs, df2) := flushDf c (fun d => !sinkOk c ip t e d.1) mvs0 df1
    -- Arm-scoped eviction: `x` leaves its register on arm entry (stored unless already saved).
    let armEvict (key : Nat) (a : Tree) : List Nat × List (Nat × Nat × Nat) :=
      let xs := (c.armEvAt.getD key []).filter fun x => natMem x a.lv && !natMem x ev'
      (xs, xs.filterMap fun x =>
        if natMem x sv then none
        else match home.getD x .none, bk.find? x with
          | .gpr r, some (b, _, _) => some (x, b, r)
          | _, _ => none)
    let (xsE, stE) := armEvict (2 * ip) e
    let (xsT, stT) := armEvict (2 * ip + 1) t
    let st1 := emitAlloc c home bk slotOk clrAt r0 r1 e
      { gDf := df2.filter fun (y, _, _) => natMem y e.lv, gSt := stE } (union ev' xsE)
      (union sv xsE)
      (gC1.filter fun (y, _) => natMem y e.lv) (vC1.filter fun (y, _) => natMem y e.lv)
      { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
    emitAlloc c home bk slotOk clrAt r0 r1 t
      { gDf := df2.filter fun (y, _, _) => natMem y t.lv, gSt := stT } (union ev' xsT)
      (union sv xsT)
      (gC1.filter fun (y, _) => natMem y t.lv) (vC1.filter fun (y, _) => natMem y t.lv) st1
  | .skip lv ip k, pd, ev, sv, gC, vC, st =>
    let (mvs, gC1, vC1, df1) := buildPre c home st.usedCs lv k.lv [] pd [] [] [] gC vC
    emitAlloc c home bk slotOk clrAt r0 r1 k { gDf := df1 } ev sv gC1 vC1
      { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .jump lv ip j _ args, pd, ev, sv, gC, vC, st =>
    let evJ := c.evIn.getD j []
    let lvJ := c.lTrie.getD j []
    let argIds := tupVarIds args
    let rl := lv.filter fun x =>
      natMem x ev && (natMem x argIds || !natMem x evJ)
    let evAfter := eraseMany rl ev
    let lvNotEv := if evAfter.isEmpty then lv else lv.filter (!natMem · evAfter)
    let savJ := lvJ.filter fun x =>
      (bk.find? x).isSome && natMem x evJ && !natMem x ev && !natMem x sv
    let (rlWG, rlWV) := splitReloadRegs home rl
    let extraMvs := splitMoves c home bk true savJ ++ splitMoves c home bk false rl
    let ps := c.bparams.getD j []
    let as := tupArgsToList args
    let needSlotSt := (as.zip ps).filterMap fun (ao, p) =>
      if !slotOk.getD p false then none
      else match ao, home.getD p .none with
        | some x, .slot s .w64 =>
          match home.getD x .none with
          | .slot s' .w64 => if Nat.beq s s' then some x else none
          | _ => none
        | _, _ => none
    let laAfter := union lvJ needSlotSt
    let (mvs1, gC1, _, df1) := buildPre c home st.usedCs lv laAfter [] pd
      extraMvs rlWG rlWV gC vC [] evAfter
    -- A deferred store survives the jump iff the target takes the variable in a register and
    -- no slot-direct argument move can steal that register as its temporary.
    let tmpSafe := !(ps.any (slotOk.getD · false)) ||
      (freshReg (c.gAlloc ++ st.usedCs) (gprHomes home lvNotEv ++ gC1.map Prod.snd)).isSome
    let rin := c.regIn.getD j []
    let keep (d : Nat × Nat × Nat) : Bool :=
      tmpSafe && !natMem d.1 needSlotSt &&
        rin.any fun (y, _, inS) => Nat.beq y d.1 && !inS
    let (mvs0, _) := flushDf c (fun d => !keep d) mvs1 df1
    let smvs := jumpSlotMoves c home slotOk st.usedCs lvNotEv j args gC1
    let cin := if c.opt then gC1.foldl (fun a (y, r) =>
        match home.getD y .none with
        | .slot _ .w64 =>
          if natMem y lvJ then
            (j, y, r, df1.any (fun d => Nat.beq d.1 y), c.jmpW.getD ip 0) :: a
          else a
        | _ => a) st.cin else st.cin
    let jw := c.jmpW.getD ip 0
    let evArr := if c.opt then lv.foldl (fun a x =>
        if (bk.find? x).isSome && natMem x lvJ then
          (j, x, natMem x ev, !natMem x ev && !natMem x sv, jw) :: a
        else a) st.evArr else st.evArr
    let latchArr := if !c.opt then st.latchArr else
      let lw := (if c.latchIps.getD ip false then 8 else 1) * jw
      (as.zip ps).foldl (fun a (ao, p) => match ao with
        | some x =>
          if Nat.beq x p then a
          else
            let r? := match home.getD x .none with
              | .gpr r => some r
              | .slot _ _ => (gC1.find? fun (y, _) => Nat.beq y x).map Prod.snd
              | _ => none
            match r? with | some r => (p, r, lw) :: a | none => a
        | none => a) st.latchArr
    { st with
      pre := recordPre ip (clrAt.getD ip false) (mvs0 ++ smvs) st.pre,
      cin := cin, evArr := evArr, latchArr := latchArr }
  | .ret lv ip _ _, pd, _, _, gC, vC, st | .exit lv ip _ _ _, pd, _, _, gC, vC, st =>
    let (mvs, _, _, _) := buildPre c home st.usedCs lv [] [] pd [] [] [] gC vC
    { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .stop _, _, _, _, _, _, st => st
  | .group _ bs k, pd, ev, sv, gC, vC, st =>
    emitAllocB c home bk slotOk clrAt r0 r1 bs
      (emitAlloc c home bk slotOk clrAt r0 r1 k pd ev sv gC vC st)

def emitAllocB {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond))
    (bk : Trie (Nat × SlotWidth × Bool)) (slotOk clrAt : Trie Bool) (r0 r1 : Option I.Reg) :
    TreeBlocks → EmitSt I → EmitSt I
  | .nil, st => st
  | .cons l ps b bs, st =>
    let lv := c.lTrie.getD l []
    let pvars := ps.map Prod.fst
    let rin := c.regIn.getD l []
    let evL := c.evIn.getD l []
    let lvNotEv := if evL.isEmpty then lv else lv.filter (!natMem · evL)
    let (plocs, pids, cs') := pickPlocs c home slotOk lvNotEv pvars st.usedCs (rin.map (·.2.1))
    let liveL : List (SymArg × I.Loc) := lv.foldr (fun x acc =>
      match home.getD x .none with
      | .gpr r =>
        if natMem x evL then
          match bk.find? x with
          | some (sb, sw, _) => (.var x, .slot sb sw) :: acc
          | none => (.var x, .gpr (c.gReg.getD r I.frame.sp)) :: acc
        else
          let acc := match bk.find? x with
            | some (sb, sw, true) => (.var x, .slot sb sw) :: acc | _ => acc
          (.var x, .gpr (c.gReg.getD r I.frame.sp)) :: acc
      | .vec v =>
        match c.vReg.find? v with
        | some vr =>
          let acc := match bk.find? x with
            | some (sb, sw, true) => (.var x, .slot sb sw) :: acc | _ => acc
          (.var x, .vec vr) :: acc
        | none => acc
      | .flag cc => (.var x, .flag cc) :: acc
      | .slot s w =>
        match rin.find? fun (y, _, _) => Nat.beq y x with
        | some (_, r, inS) =>
          let acc := if inS then (.var x, .slot s w) :: acc else acc
          (.var x, .gpr (c.gReg.getD r I.frame.sp)) :: acc
        | none => (.var x, .slot s w) :: acc
      | .none => acc) []
    let initSv := union (lv.filter (isEagerBk bk)) evL
    let inDf := rin.filterMap fun (x, r, inS) =>
      match inS, home.getD x .none with
      | false, .slot s _ => some (x, s, r)
      | _, _ => none
    let st1 := emitAlloc c home bk slotOk clrAt r0 r1 b
      { pendFromArrivals home bk pvars pids with gDf := inDf }
      evL initSv (rin.map fun (x, r, _) => (x, r)) []
      { st with entry := st.entry.insert l ⟨liveL, plocs⟩, usedCs := cs' }
    emitAllocB c home bk slotOk clrAt r0 r1 bs st1
end

end Spill
end LeanQbe.T
end
