module

public import LeanQbe.T.SpillEmit
public import LeanQbe.T.LiveW62

/-!
# Wave 6.2-A Unverified Spill/Hint Passes (`SpillW62`, untrusted)

Heuristic post-coloring / CFG passes feeding verified `Rega` checkers:
* `OPT-10c`: `computeMulHiIps` marks dead-low `umulw`/`smulw` instructions for `Hints.mulHiIps`.
* `OPT-10a`: `computeBlockInZ32` and `computeZextEntries` propagate canonical zero-extended
  `.bits 8/16/32` facts across block edges into `Entry.liveZ` / `Entry.plocZ` and block-entry
  `gather` `isZ32` seeds.
* `OPT-7b`: `hoistLoopConsts` hoists repeated/multi-instruction large constants out of natural
  loops into unused loop GPRs via `Entry.live`.

Untrusted: `Rega.lowerFn` verifies every hint.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Spill

open Live Rega SpillFlags

/-- Build worst-case dummy `PArg`s (all GPR inputs mapped to `r0`, matching `rd = r0`) for probing
`I.gpr.zeroUpper32Op` independently of register assignment. -/
def dummyPArgsZ32 {I : Isa} (r0 : I.Reg) :
    {sig : List Ty} → Tup (Arg VNat) sig → Option (Tup (PArg I.Reg I.VReg I.Cond) sig)
  | [], () => some ()
  | .bool :: _, (.var _, as) => (dummyPArgsZ32 r0 as).map (.gpr r0, ·)
  | .bool :: _, (.imm b, as) => (dummyPArgsZ32 r0 as).map (.imm b, ·)
  | .bits _ :: _, (.var _, as) => (dummyPArgsZ32 r0 as).map (.gpr r0, ·)
  | .bits _ :: _, (.imm c, as) => (dummyPArgsZ32 r0 as).map (.imm c, ·)
  | _, _ => none

def isSextCode {sig ts : List Ty} : OpCode sig ts → Bool
  | .sext _ _ => true
  | _ => false

/-- True when `op` writes `[.bits 32]` to a GPR with bits `32..63` guaranteed zero regardless of
register assignment (excluding `.sext`, which may lower via `tryLoadSext`). -/
def opProducesZ32Static (I : Isa) (r0? : Option I.Reg) {ts : List Ty} (op : Op VNat ts) : Bool :=
  match r0?, ts with
  | some r0, [.bits 32] =>
    let { sig := _, code, args } := op
    if isSextCode code then false
    else
      match dummyPArgsZ32 r0 args with
      | some pas => I.gpr.zeroUpper32Op code pas (.gpr r0, ())
      | none => false
  | _, _ => false

/-! ## Dead-Low Widening Multiply (`OPT-10c`) -/

mutual
private def collectMulHiTree (I : Isa) (elide : Trie Bool) (dest : Trie I.Loc)
    (saved : List I.Reg) : Tree → Trie Bool → Trie Bool
  | .let_ _ ip nv0 ts op k, acc =>
    let acc1 :=
      if I.gpr.mulHi?.isSome && !elide.getD ip false && !natMem nv0 k.lv then
        let { sig := _, code, args := _ } := op
        match ts, code with
        | [.bits _, .bits _], .umulw n | [.bits _, .bits _], .smulw n =>
          if isGprTy I (.bits n) then
            match dest.find? (nv0 + 1) with
            | some (.gpr dhi) => if isAllocGpr I saved dhi then acc.insert ip true else acc
            | _ => acc
          else acc
        | _, _ => acc
      else acc
    collectMulHiTree I elide dest saved k acc1
  | .load _ _ _ _ _ k, acc | .store _ _ _ _ _ k, acc | .call _ _ _ _ _ _ _ k, acc
  | .skip _ _ k, acc =>
    collectMulHiTree I elide dest saved k acc
  | .jnz _ _ _ _ t e, acc =>
    collectMulHiTree I elide dest saved t (collectMulHiTree I elide dest saved e acc)
  | .group _ bs k, acc =>
    collectMulHiBlocks I elide dest saved bs (collectMulHiTree I elide dest saved k acc)
  | _, acc => acc

private def collectMulHiBlocks (I : Isa) (elide : Trie Bool) (dest : Trie I.Loc)
    (saved : List I.Reg) : TreeBlocks → Trie Bool → Trie Bool
  | .nil, acc => acc
  | .cons _ _ b bs, acc =>
    collectMulHiBlocks I elide dest saved bs (collectMulHiTree I elide dest saved b acc)
end

/-- Mark dead-low `umulw`/`smulw` ops (`nv0 ∉ k.lv`, `nv0+1` allocated in GPR) in `mulHiIps`. -/
def computeMulHiIps (I : Isa) (elide : Trie Bool) (dest : Trie I.Loc) (saved : List I.Reg)
    (t : Tree) : Trie Bool :=
  if I.gpr.mulHi?.isSome then collectMulHiTree I elide dest saved t .empty else .empty

/-! ## Cross-Block Canonical `.gprZ` Entry Propagation (`OPT-10a`) -/

private def isSmallBitsTy : Ty → Bool
  | .bits n => Nat.beq n 8 || Nat.beq n 16 || Nat.beq n 32
  | _ => false

/-- True when `op` writes a single GPR output guaranteed to hold canonical `AbiGprHolds` via
`I.gpr.zeroExtOp` (using dummy `r0` operands). -/
def opZeroExtStatic (I : Isa) (r0? : Option I.Reg) {ts : List Ty} (op : Op VNat ts) : Bool :=
  match r0?, ts with
  | some r0, [_] =>
    let { sig := _, code, args } := op
    match dummyPArgsZ32 r0 args with
    | some pas => I.gpr.zeroExtOp code pas (.gpr r0, ())
    | none => false
  | _, _ => false

/-- Conservative predicate: `op` produces a canonical `.gprZ` value at `nv0` when not elided
and not deferred (`tryLoadSext` / `elideRegOp?` edge cases explicitly excluded). -/
private def opProducesCanonZ (I : Isa) (r0? : Option I.Reg) (elide deferJnz deferLea : Trie Bool)
    (ip : Nat) (ts : List Ty) (op : Op VNat ts) : Bool :=
  if elide.getD ip false || deferJnz.getD ip false || deferLea.getD ip false then false
  else if !opZeroExtStatic I r0? op then false
  else
    let { sig := _, code, args := _ } := op
    match ts, code with
    | [.bits n], .sext _ _ =>
      let _ := n
      false
    | [.bits n], .bitcast (.bits m) (.bits _) _ =>
      Nat.beq m 32 && Nat.beq n 32 && I.gpr.zeroUpper32Load && opProducesZ32Static I r0? op
    | [.bits n], .zext m _ =>
      Nat.blt m n && Nat.ble n 64 && (Nat.beq n 16 || Nat.beq n 32 || Nat.beq n 64)
    | [.bits n], .ofBool _ =>
      Nat.blt 0 n && Nat.ble n 64 && (Nat.beq n 8 || Nat.beq n 16 || Nat.beq n 32)
    | [.bits 32], _ => I.gpr.zeroUpper32Load && opProducesZ32Static I r0? op
    | _, _ => false

private def isSmallNonFlagLoc {R V C : Type} : Loc R V C → Bool
  | .gpr _ => true
  | .slot _ w => slotWidthEq w .w64
  | _ => false

private def collectJumpArgsZ (zCur : Trie Bool) :
    {ts : List Ty} → Tup (Arg VNat) ts → List Bool
  | [], () => []
  | t :: _, (.var x, as) => (isSmallBitsTy t && zCur.getD x false) :: collectJumpArgsZ zCur as
  | _ :: _, (.imm _, as) => false :: collectJumpArgsZ zCur as

private def meetBoolList : List Bool → List Bool → List Bool
  | [], _ | _, [] => []
  | a :: xs, b :: ys => (a && b) :: meetBoolList xs ys

mutual
private def scanOutEdgesZ (I : Isa) (r0? : Option I.Reg) (elide deferJnz deferLea : Trie Bool)
    (zCur : Trie Bool) :
    Tree → List (Nat × Trie Bool × List Bool) → List (Nat × Trie Bool × List Bool)
  | .let_ _ ip nv0 ts op k, acc =>
    let zNext :=
      if opProducesCanonZ I r0? elide deferJnz deferLea ip ts op then zCur.insert nv0 true
      else zCur
    scanOutEdgesZ I r0? elide deferJnz deferLea zNext k acc
  | .load _ ip x t _ k, acc =>
    let zNext :=
      if !elide.getD ip false && isSmallBitsTy t &&
          ((I.gpr.zeroExtLoad && isGprTy I t) || (I.gpr.zeroUpper32Load && tyEq t (.bits 32)))
      then zCur.insert x true
      else zCur
    scanOutEdgesZ I r0? elide deferJnz deferLea zNext k acc
  | .store _ _ _ _ _ k, acc | .call _ _ _ _ _ _ _ k, acc | .skip _ _ k, acc =>
    scanOutEdgesZ I r0? elide deferJnz deferLea zCur k acc
  | .jnz _ _ _ _ t e, acc =>
    scanOutEdgesZ I r0? elide deferJnz deferLea zCur t
      (scanOutEdgesZ I r0? elide deferJnz deferLea zCur e acc)
  | .group _ _ k, acc =>
    scanOutEdgesZ I r0? elide deferJnz deferLea zCur k acc
  | .jump _ _ j _ args, acc =>
    (j, zCur, collectJumpArgsZ zCur args) :: acc
  | _, acc => acc
end

private def seedBlockZ (tys : Trie Ty) (lv : List Nat) (ps : List (Nat × Ty)) :
    Trie Bool × List Bool :=
  let z0 := lv.foldl (fun m x =>
    if isSmallBitsTy (tys.getD x i64) then m.insert x true else m) .empty
  let p0 := ps.map fun (_, t) => isSmallBitsTy t
  (z0, p0)

private def edgeToStateZ (lv : List Nat) (srcZ : Trie Bool) (argZ : List Bool)
    (ps : List (Nat × Ty)) : Trie Bool × List Bool :=
  let zLive := lv.foldl (fun m x => if srcZ.getD x false then m.insert x true else m) .empty
  (zLive, argZ.take ps.length)

private def zMapEq (vars : List Nat) (a b : Trie Bool) : Bool :=
  vars.all fun x => a.getD x false == b.getD x false

/-- Greatest-fixpoint dataflow for canonical `.gprZ` facts at every block entry, returning
`(blockInZVars, blockInParamZFlags)` over `tBlocks`. -/
def computeBlockInZ32 (I : Isa) (r0? : Option I.Reg) (tys : Trie Ty)
    (fnPs : List (Nat × Ty)) (elide deferJnz deferLea : Trie Bool) (lTrie : Trie (List Nat))
    (t : Tree) (tBlocks : List (Nat × List (Nat × Ty) × Tree)) :
    Trie (Trie Bool) × Trie (List Bool) :=
  if !(I.gpr.zeroExtLoad && I.gpr.zeroUpper32Load) || tBlocks.isEmpty then (.empty, .empty)
  else
    let rootZ0 := fnPs.foldl (fun m (p, ty) =>
      if isSmallBitsTy ty then m.insert p true else m) .empty
    let initZ : Trie (Trie Bool) := tBlocks.foldl (fun m (l, ps, _) =>
      m.insert l (seedBlockZ tys (lTrie.getD l []) ps).1) .empty
    let initP : Trie (List Bool) := tBlocks.foldl (fun m (l, ps, _) =>
      m.insert l (seedBlockZ tys (lTrie.getD l []) ps).2) .empty
    let rootEdges := scanOutEdgesZ I r0? elide deferJnz deferLea rootZ0 t []
    let rec iter : Nat → Trie (Trie Bool) → Trie (List Bool) → Trie (Trie Bool) × Trie (List Bool)
      | 0, curZ, curP => (curZ, curP)
      | fuel + 1, curZ, curP =>
        let allEdges := tBlocks.foldl (fun es (l, ps, body) =>
          let z0 := (ps.zip (curP.getD l [])).foldl (fun m ((p, _), zp) =>
            if zp then m.insert p true else m) (curZ.getD l .empty)
          scanOutEdgesZ I r0? elide deferJnz deferLea z0 body es) rootEdges
        let byDst : Std.HashMap Nat (List (Trie Bool × List Bool)) :=
          allEdges.foldl (fun m (j, zOut, aOut) => m.insert j ((zOut, aOut) :: m.getD j [])) {}
        let (nextZ, nextP, changed) := tBlocks.foldl (fun (mz, mp, ch) (l, ps, _) =>
          let lv := lTrie.getD l []
          match byDst.getD l [] with
          | [] => (mz.insert l .empty, mp.insert l (ps.map fun _ => false), ch)
          | e0 :: rest =>
            let s0 := edgeToStateZ lv e0.1 e0.2 ps
            let met := rest.foldl (fun (za, pa) e =>
              let s := edgeToStateZ lv e.1 e.2 ps
              let zM := lv.foldl (fun m x =>
                if za.getD x false && s.1.getD x false then m.insert x true else m) .empty
              (zM, meetBoolList pa s.2)) s0
            let ch' := ch || !zMapEq lv (curZ.getD l .empty) met.1 ||
              !(curP.getD l [] == met.2)
            (mz.insert l met.1, mp.insert l met.2, ch')) (.empty, .empty, false)
        if !changed then (nextZ, nextP) else iter fuel nextZ nextP
    iter (tBlocks.length + 4) initZ initP

/-- Populate `Entry.liveZ` and `Entry.plocZ` across `entry` from `computeBlockInZ32`. -/
def computeZextEntries (I : Isa) (r0? : Option I.Reg) (tys : Trie Ty) (fnPs : List (Nat × Ty))
    (elide deferJnz deferLea : Trie Bool) (lTrie : Trie (List Nat))
    (entry : Trie (Entry I.Reg I.VReg I.Cond)) (t : Tree)
    (tBlocks : List (Nat × List (Nat × Ty) × Tree)) :
    Trie (Entry I.Reg I.VReg I.Cond) :=
  let (inZ, inP) := computeBlockInZ32 I r0? tys fnPs elide deferJnz deferLea lTrie t tBlocks
  tBlocks.foldl (fun m (l, ps, _) =>
    match m.find? l with
    | none => m
    | some en =>
      let zl := inZ.getD l .empty
      let zp := inP.getD l []
      let liveZ := en.live.map fun (sa, loc) =>
        match sa with
        | .var x => isSmallNonFlagLoc loc && zl.getD x false
        | _ => false
      let plocZ := (en.ploc.zip (ps.zip zp)).map fun (loc, (_, z)) =>
        isSmallNonFlagLoc loc && z
      m.insert l { en with liveZ := liveZ, plocZ := plocZ }) entry

/-! ## Natural-Loop Large Constant Hoisting (`OPT-7b`) -/

private def regOfLoc? {R V C : Type} : Loc R V C → Option R
  | .gpr r => some r
  | _ => none

private def regsOfMove {I : Isa} : I.Move → List I.Reg
  | .mov d s => [d, s]
  | .movi d _ => [d]
  | .ld d _ => [d]
  | .st _ s => [s]
  | .setcc d _ => [d]
  | _ => []

private def regsOfPreStep {I : Isa} (ps : PreStep I.Reg I.VReg I.Cond) : List I.Reg :=
  ps.moves.flatMap regsOfMove

mutual
private def scanLoopTree (I : Isa) (elide : Trie Bool) (dest : Trie I.Loc)
    (pre : Trie (PreStep I.Reg I.VReg I.Cond)) (blkUsed : List I.Reg) (calls : Bool)
    (cands : List (BitVec 64 × Nat)) :
    Tree → List I.Reg × Bool × List (BitVec 64 × Nat)
  | .let_ _ ip nv0 ts op k =>
    let blkUsed1 := (List.range ts.length).foldl (fun rs i =>
      match dest.find? (nv0 + i) with
      | some (.gpr r) => r :: rs | _ => rs) (regsOfPreStep (pre.getD ip {}) ++ blkUsed)
    let cands1 :=
      if elide.getD ip false then cands
      else
        let { sig := _, code, args } := op
        let rec addImm : {ss : List Ty} → Tup (Arg VNat) ss →
            List (BitVec 64 × Nat) → List (BitVec 64 × Nat)
          | [], _, cs => cs
          | .bits w :: _, (.imm c, rest), cs =>
            let c64 := c.setWidth 64
            let cs' :=
              if Nat.ble w 64 && c64 != 0#64 &&
                  (match I.gpr.preferRegImm? with | some f => f code w c64 | none => false) then
                let cost := match I.frame.allocatable.head? with
                  | some r0 => (I.gpr.movi r0 c64).length
                  | none => 1
                (c64, cost) :: cs
              else cs
            addImm rest cs'
          | _ :: _, (_, rest), cs => addImm rest cs
        addImm args cands
    scanLoopTree I elide dest pre blkUsed1 calls cands1 k
  | .load _ ip x _ _ k =>
    let blkUsed1 := match dest.find? x with
      | some (.gpr r) => r :: (regsOfPreStep (pre.getD ip {}) ++ blkUsed)
      | _ => regsOfPreStep (pre.getD ip {}) ++ blkUsed
    scanLoopTree I elide dest pre blkUsed1 calls cands k
  | .store _ ip _ _ _ k =>
    scanLoopTree I elide dest pre (regsOfPreStep (pre.getD ip {}) ++ blkUsed) calls cands k
  | .call _ ip nv0 _ _ bs _ k =>
    let blkUsed1 := (List.range bs.length).foldl (fun rs i =>
      match dest.find? (nv0 + i) with
      | some (.gpr r) => r :: rs | _ => rs) (regsOfPreStep (pre.getD ip {}) ++ blkUsed)
    scanLoopTree I elide dest pre blkUsed1 true cands k
  | .skip _ ip k =>
    scanLoopTree I elide dest pre (regsOfPreStep (pre.getD ip {}) ++ blkUsed) calls cands k
  | .jnz _ ip _ _ t e =>
    let (u1, c1, k1) := scanLoopTree I elide dest pre
      (regsOfPreStep (pre.getD ip {}) ++ blkUsed) calls cands t
    scanLoopTree I elide dest pre u1 c1 k1 e
  | .jump _ ip _ _ _ | .ret _ ip _ _ | .exit _ ip _ _ _ =>
    (regsOfPreStep (pre.getD ip {}) ++ blkUsed, calls, cands)
  | .stop _ => (blkUsed, calls, cands)
  | .group _ _ k =>
    scanLoopTree I elide dest pre blkUsed calls cands k
end

private def insertConstCount (m : List (BitVec 64 × Nat)) (c : BitVec 64) (w : Nat) :
    List (BitVec 64 × Nat) :=
  match m with
  | [] => [(c, w)]
  | (c', w') :: rest =>
    if c == c' then (c', w' + w) :: rest else (c', w') :: insertConstCount rest c w

/-- Hoist multi-use or multi-instruction loop constants into unused GPRs via `Entry.live`. -/
def hoistLoopConsts (I : Isa) (gReg : Trie I.Reg) (gAlloc usedCs : List Nat)
    (loops : Trie Bool) (loopReach : Trie (List Nat)) (elide : Trie Bool)
    (dest : Trie I.Loc) (pre : Trie (PreStep I.Reg I.VReg I.Cond))
    (entry : Trie (Entry I.Reg I.VReg I.Cond))
    (tBlocks : List (Nat × List (Nat × Ty) × Tree)) : Trie (Entry I.Reg I.VReg I.Cond) :=
  if tBlocks.isEmpty || usedCs.isEmpty && gAlloc.isEmpty then entry
  else
    let blkMap : Std.HashMap Nat Tree :=
      tBlocks.foldl (fun m (l, _, body) => m.insert l body) {}
    let loopHdrs0 := tBlocks.filterMap fun (l, _, _) =>
      if loops.getD l false then
        let lbs := union [l] (loopReach.getD l [])
        some (lbs.length, l, lbs)
      else none
    -- Outermost first so outer loops claim shared constants over larger regions cleanly.
    let loopHdrs := loopHdrs0.mergeSort fun a b => Nat.ble b.1 a.1
    let gprPool := (gAlloc ++ usedCs).filterMap fun rid => gReg.find? rid
    let csPool := usedCs.filterMap fun rid => gReg.find? rid
    loopHdrs.foldl (fun curEntry (_, _, loopBlks) =>
      if !(loopBlks.all fun b => (curEntry.find? b).isSome) then curEntry
      else
        let (usedRegs, hasCall, rawCands) := loopBlks.foldl (fun (us, hc, cs) b =>
          let usEn := match curEntry.find? b with
            | some en => (en.live.filterMap fun (_, loc) => regOfLoc? loc) ++
                (en.ploc.filterMap regOfLoc?) ++ us
            | none => us
          match blkMap.get? b with
          | some body => scanLoopTree I elide dest pre usEn hc cs body
          | none => (usEn, hc, cs)) ([], false, [])
        let pool := (if hasCall then csPool else gprPool).filter fun r =>
          !(usedRegs.contains r) && !(I.frame.scratch.contains r)
        if pool.isEmpty || rawCands.isEmpty then curEntry
        else
          let agg := rawCands.foldl (fun acc (c, cost) => insertConstCount acc c cost) []
          let worthy := (agg.filter fun (_, totCost) => Nat.ble 2 totCost).mergeSort
            fun a b => Nat.ble b.2 a.2
          let rec assign : List (BitVec 64 × Nat) → List I.Reg → List (BitVec 64 × I.Reg)
            | [], _ | _, [] => []
            | (c, _) :: cs, r :: rs => (c, r) :: assign cs rs
          -- Keep at most 2 hoisted constants per loop and leave headroom if pool is tight.
          let budget := if Nat.ble 3 pool.length then min 2 (pool.length - 1) else 0
          let chosen := assign (worthy.take budget) pool
          if chosen.isEmpty then curEntry
          else
            loopBlks.foldl (fun m b =>
              match m.find? b with
              | none => m
              | some en =>
                let addLive := chosen.map fun (c, r) => (.immBits 64 c, .gpr r)
                let addLiveZ := if en.liveZ.isEmpty then [] else chosen.map fun _ => false
                m.insert b { en with
                  live := en.live ++ addLive
                  liveZ := en.liveZ ++ addLiveZ })
              (curEntry : Trie (Entry I.Reg I.VReg I.Cond))) entry

end Spill
end LeanQbe.T
