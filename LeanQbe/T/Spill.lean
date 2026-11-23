module

public import LeanQbe.T.Live
public import LeanQbe.T.SpillFlags

/-!
# Priority Graph-Coloring Register Allocator & Spilling Oracle (`T7a`, `L-E1.2`, untrusted)

Full port of E1's priority graph-coloring allocator extended to typed banks (`GPR` + `Vec` + local
flag hints): scoped loop-depth & branch-discounted weights, exact dual reload/def pressure points
with callee-saved/flag credit, identity self-jump filtering, dying-operand 2-address + block-edge
coalescing with parallel-move conflict avoidance, per-call live-range splitting (lazy for cold
calls inside or outside loops, eager-backed for loop-crossing invariants), straight-line dead
spill-store elision and spilled-operand register caching, slot-direct block parameters,
`VariantHint.disp` (`lea`) probing, and GPR/Vec parallel-move cycle breaking.

Train B5-1 (`Cfg`) adds four spill-placement refinements: slot-home stores are deferred past
straight-line code and sunk into `jnz` arms (`sink`), hot join parameters stay out of
slot-direct `Entry.ploc` (`joinGuard`), a spilled variable keeps a soft cache register that
later-colored interfering variables avoid (`cacheHint`), and a block may take a spilled live-in
in the register its predecessors hold it in (`regEntry`).

Untrusted: `Rega.lowerFn` checks every hint, so any heuristic bug can only fail lowering.
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

/-! ## Scoped Loop Detection (PHOAS Lexical Nesting) -/

mutual
def blocksWithMin : Tree → List (Nat × Nat × Tree)
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k
  | .call _ _ _ _ _ _ _ k | .skip _ _ k => blocksWithMin k
  | .jnz _ _ _ _ t e => blocksWithMin t ++ blocksWithMin e
  | .group _ bs k =>
    let gMin := match bs with | .cons l _ _ _ => l | .nil => 0
    blocksWithMinB gMin bs ++ blocksWithMin k
  | .jump .. | .ret .. | .exit .. | .stop _ => []

def blocksWithMinB (gMin : Nat) : TreeBlocks → List (Nat × Nat × Tree)
  | .nil => []
  | .cons l _ b bs => (l, gMin, b) :: blocksWithMin b ++ blocksWithMinB gMin bs
end

/-- Identify true loop headers and their scoped loop-body reachability sets (`x ≥ gMin` reaching
header `l`) in a single reverse DFS per block, avoiding false loops on inner `if`/`else` joins. -/
def loopBlocksScoped (bs : List (Nat × Nat × Tree)) : Trie Bool × Trie (List Nat) :=
  let rev := bs.foldl (fun r (l, _, tb) =>
    (allJumps tb).foldl (fun r dst => r.insert dst (l :: r.getD dst [])) r)
    (.empty : Trie (List Nat))
  let maxFuel := bs.length * bs.length + bs.length + 1
  let revReach (target gMin : Nat) : List Nat :=
    let rec dfs : Nat → List Nat → Trie Unit → List Nat → List Nat
      | 0, _, _, acc | _, [], _, acc => acc
      | fuel + 1, x :: xs, vis, acc =>
        if !Nat.ble gMin x || trieMem vis x then dfs fuel xs vis acc
        else dfs fuel (rev.getD x [] ++ xs) (vis.insert x ()) (x :: acc)
    dfs maxFuel (rev.getD target []) .empty []
  bs.foldl (fun (lps, rch) (l, gMin, _) =>
    let reach := revReach l gMin
    if natMem l reach then (lps.insert l true, rch.insert l reach) else (lps, rch))
    (.empty, .empty)

/-! ## Sorting, Intervals, and Preferences -/

def mergeSorted : Nat → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat) →
    List (Nat × Nat)
  | 0, _, _, acc => acc.reverse
  | _, [], ys, acc => acc.reverseAux ys
  | _, xs, [], acc => acc.reverseAux xs
  | fuel + 1, x :: xs, y :: ys, acc =>
    if Nat.ble (y.1 + 1) x.1 || (Nat.beq x.1 y.1 && Nat.ble (x.2 + 1) y.2) then
      mergeSorted fuel xs (y :: ys) (x :: acc)
    else mergeSorted fuel (x :: xs) ys (y :: acc)

def sortByWeight (nv : Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  let rec pass : List (List (Nat × Nat)) → List (List (Nat × Nat))
    | a :: b :: rest => mergeSorted (nv + 2) a b [] :: pass rest
    | xss => xss
  let rec go : Nat → List (List (Nat × Nat)) → List (Nat × Nat)
    | _, [xs] => xs
    | fuel + 1, xss@(_ :: _ :: _) => go fuel (pass xss)
    | _, xss => xss.headD []
  go (nv + 2) (xs.map (· :: []))

def firstFreeSlotRange (k : Nat) (forb : List (Nat × Nat)) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, s => s
    | f + 1, s => if forb.any fun (s', k') => rangesOverlap s k s' k' then go f (s + 1) else s
  go (forb.length * 8 + 2) 0

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

def addAbiArgs (as : List (Option Nat)) (ids : List (Option (Sum Nat Nat))) (mult : Nat)
    (gAcc vAcc : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) × List (Nat × Nat × Nat) :=
  (as.zip ids).foldl (fun (ga, va) (ao, ido) =>
    match ao, ido with
    | some x, some (.inl r) => ((x, r, mult) :: ga, va)
    | some x, some (.inr v) => (ga, (x, v, mult) :: va)
    | _, _ => (ga, va)) (gAcc, vAcc)

def addAffZip (as : List (Option Nat)) (ps : List Nat) (mult : Nat)
    (acc : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  (as.zip ps).foldl (fun a (ao, p) => match ao with | some x => (x, p, mult) :: a | none => a) acc

def addAntiZip (as : List (Option Nat)) (ps : List Nat) (mult : Nat)
    (acc : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  (as.zip ps).foldl (fun a (ao, p) =>
    match ao with
    | some x =>
      ps.foldl (fun a p' =>
        if Nat.beq p' p || Nat.beq x p' then a else (x, p', mult) :: a) a
    | none => a) acc

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

/-- Extract `(m, n, srcVar)` when `op` is `.zext m n (.var x)`. -/
def zextVarSrc? {ts : List Ty} (op : Op VNat ts) : Option (Nat × Nat × Nat) :=
  let { sig := _, code, args } := op
  match code, args with
  | .zext m n, (.var x, ()) => some (m, n, x)
  | _, _ => none

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

/-! ## Interference, Weights, Pressure Points, and Priority Coloring -/

/-- Train B5-1 heuristic switches (untrusted: `Rega.lowerFn` re-checks every hint). `sink` defers
slot-home spill stores past straight-line code and into `jnz` arms; `joinGuard` keeps hot join
parameters out of slot-direct `Entry.ploc`; `cacheHint` gives a spilled variable a soft register
that later-colored interfering variables avoid; `regEntry` lets a block take a spilled live-in
in the register its predecessors hold it in. -/
structure Cfg where
  (sink joinGuard cacheHint regEntry : Bool := true)

/-- Pre-B5-1 behaviour (all switches off), for ablation and regression tests. -/
def Cfg.legacy : Cfg :=
  { sink := false, joinGuard := false, cacheHint := false, regEntry := false }

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

/-- Gathered weights; `gprPts` records `(budget, liveThrough, creditVars)` where coloring any
`u ∈ creditVars` with a callee-saved register credits `+1` back to that point's caller-saved
budget; `callW` records `(mult, vars live across a call)`; `loopCall` marks vars crossing a call
inside a loop; `defWT` records each var's definition weight; `isBP` marks block parameters;
`brW` records `(mult, multThen, multElse)` of every `jnz`. -/
structure GatherAcc where
  (weights defInterf callW : List (Nat × List Nat) := [])
  (gprPts : List (Nat × List Nat × List Nat) := [])
  (gprPtBlks : List (Option Nat) := [])
  (vecPts : List (Nat × List Nat) := [])
  (abiGpr abiVec affEdges antiEdges : List (Nat × Nat × Nat) := [])
  (loopCall : Trie Bool := .empty)
  (defWT : Trie Nat := .empty)
  (isBP : Trie Bool := .empty)
  (brW : Trie (Nat × Nat × Nat) := .empty)
  (jmpW inW : Trie Nat := .empty)
  (zextElide : Trie Nat := .empty)
  (zextEdges : List (Nat × Nat) := [])

def addWeight (mult : Nat) (uses : List Nat) (ws : List (Nat × List Nat)) :
    List (Nat × List Nat) :=
  if uses.isEmpty then ws else (mult, uses) :: ws

/-- GPR pressure point: at most `nGpr - |creditVars|` of `vars` (`live \ creditVars`) may sit in
caller-saved registers initially; each var in `creditVars` assigned a CS register credits `+1` back
to this budget, guaranteeing `|non-CS creditVars|` free caller-saved registers for reload/def. -/
def addGprPtBlk (blk? : Option Nat) (allocLen : Nat) (creditVars vars : List Nat)
    (pts : List (Nat × List Nat × List Nat)) (blks : List (Option Nat)) :
    List (Nat × List Nat × List Nat) × List (Option Nat) :=
  let need := creditVars.length
  let b := allocLen - need
  if Nat.ble 1 need && Nat.ble (b + 1) vars.length then
    ((b, vars, creditVars) :: pts, blk? :: blks)
  else (pts, blks)

def addVecPt (allocLen need : Nat) (vars : List Nat) (pts : List (Nat × List Nat)) :
    List (Nat × List Nat) :=
  let b := allocLen - need
  if Nat.ble 1 need && Nat.ble (b + 1) vars.length then
    match pts with
    | (b0, vs0) :: pts' =>
      if vars == vs0 then (if Nat.ble (b + 1) b0 then (b, vs0) :: pts' else pts)
      else (b, vars) :: pts
    | [] => [(b, vars)]
  else pts

def splitBank {C : Type} (banks : Trie Bank) (flagHome : Trie C) (vs : List Nat) :
    List Nat × List Nat :=
  vs.foldl (fun (gs, vcs) x =>
    if (flagHome.find? x).isSome then (gs, vcs)
    else if (banks.getD x .gpr).isVec then (gs, x :: vcs)
    else (x :: gs, vcs)) ([], [])

mutual
def hasLoopTree (loops : Trie Bool) : Tree → Bool
  | .group _ bs k => hasLoopTreeB loops bs || hasLoopTree loops k
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k
  | .call _ _ _ _ _ _ _ k | .skip _ _ k => hasLoopTree loops k
  | .jnz _ _ _ _ t e => hasLoopTree loops t || hasLoopTree loops e
  | .jump .. | .ret .. | .exit .. | .stop _ => false

def hasLoopTreeB (loops : Trie Bool) : TreeBlocks → Bool
  | .nil => false
  | .cons l _ b bs => loops.getD l false || hasLoopTree loops b || hasLoopTreeB loops bs
end

mutual
def hasCallTree : Tree → Bool
  | .call .. => true
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k | .skip _ _ k => hasCallTree k
  | .jnz _ _ _ _ t e => hasCallTree t || hasCallTree e
  | .group _ bs k => hasCallTree k || hasCallTreeB bs
  | .jump .. | .ret .. | .exit .. | .stop _ => false

def hasCallTreeB : TreeBlocks → Bool
  | .nil => false
  | .cons _ _ b bs => hasCallTree b || hasCallTreeB bs
end

mutual
def countRets : Tree → Nat
  | .ret .. => 1
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k
  | .call _ _ _ _ _ _ _ k | .skip _ _ k => countRets k
  | .jnz _ _ _ _ t e => countRets t + countRets e
  | .group _ bs k => countRetsB bs + countRets k
  | .jump .. | .exit .. | .stop _ => 0

def countRetsB : TreeBlocks → Nat
  | .nil => 0
  | .cons _ _ b bs => countRets b + countRetsB bs
end

mutual
def jumpsToAny (targets : List Nat) : Tree → Bool
  | .jump _ _ j _ _ => natMem j targets
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k
  | .call _ _ _ _ _ _ _ k | .skip _ _ k => jumpsToAny targets k
  | .jnz _ _ _ _ t e => jumpsToAny targets t || jumpsToAny targets e
  | .group _ bs k => jumpsToAny targets k || jumpsToAnyB targets bs
  | .ret .. | .exit .. | .stop _ => false

def jumpsToAnyB (targets : List Nat) : TreeBlocks → Bool
  | .nil => false
  | .cons _ _ b bs => jumpsToAny targets b || jumpsToAnyB targets bs
end

def isTrivialTerm : Tree → Bool
  | .jump .. | .ret .. | .exit .. | .stop _ => true
  | _ => false

mutual
def gatherAt {I : Isa} (c : Ctx I) (blk? : Option Nat) :
    List Nat → List Nat → Nat → Trie Bool → Tree → GatherAcc → GatherAcc
  | lps, lr, mult, isZ32, .let_ lv ip nv0 ts op k, acc =>
    let la := k.lv
    let defs := (List.range ts.length).map (nv0 + ·)
    let uses := dedup (c.addrDeps.getD ip (opVarIds op))
    let zextSrc? :=
      if I.gpr.elideZext32 then
        match zextVarSrc? op with
        | some (_, n, x) =>
          if Nat.ble n 64 && isZ32.getD x false && !natMem x defs then some x else none
        | none => none
      else none
    let aff0 := match defs with
      | d0 :: _ =>
        (opAffVars op la).foldl (fun a (src, wf) => (d0, src, wf * mult) :: a) acc.affEdges
      | [] => acc.affEdges
    let aff := match zextSrc? with
      | some zx => (nv0, zx, 16 * mult) :: aff0
      | none => aff0
    let laFor (x : Nat) := match zextSrc? with
      | some zx => if Nat.beq x nv0 then erase zx la else la
      | none => la
    let di := defs.foldl (fun d x =>
      if natMem x la || Nat.ble 2 defs.length then (x, union defs (laFor x)) :: d else d)
      acc.defInterf
    let (gLv, vLv) := splitBank c.banks c.flagHome lv
    let (gLa, vLa) := splitBank c.banks c.flagHome la
    let (gUse, vUse) := splitBank c.banks c.flagHome uses
    let (gDef, vDef) := splitBank c.banks c.flagHome defs
    let (gPts1, gBlks1) := addGprPtBlk blk? c.nGpr gUse (eraseMany gUse gLv)
      acc.gprPts acc.gprPtBlks
    let (gPts, gBlks) := addGprPtBlk blk? c.nGpr gDef (eraseMany gDef gLa) gPts1 gBlks1
    let vPts := addVecPt c.nVec vDef.length (eraseMany vDef vLa)
      (addVecPt c.nVec vUse.length (eraseMany vUse vLv) acc.vecPts)
    let dw := defs.foldl (fun t x => t.insert x mult) acc.defWT
    let (ze, zed) := match zextSrc? with
      | some zx => (acc.zextElide.insert ip zx, (nv0, zx) :: acc.zextEdges)
      | none => (acc.zextElide, acc.zextEdges)
    let isZ32' :=
      if opProducesZ32Static I c.r0? op then isZ32.insert nv0 true else isZ32
    gatherAt c blk? lps lr mult isZ32' k { acc with
      weights := (mult, defs ++ uses) :: acc.weights, defInterf := di, affEdges := aff,
      gprPts := gPts, gprPtBlks := gBlks, vecPts := vPts, defWT := dw, zextElide := ze,
      zextEdges := zed }
  | lps, lr, mult, isZ32, .load lv ip x t a k, acc =>
    let la := k.lv
    let uses := dedup (c.addrDeps.getD ip (argVarIds a))
    let di := if natMem x la then (x, la) :: acc.defInterf else acc.defInterf
    let (gLv, _) := splitBank c.banks c.flagHome lv
    let (gLa, vLa) := splitBank c.banks c.flagHome la
    let (gUse, _) := splitBank c.banks c.flagHome uses
    let (gDef, vDef) := splitBank c.banks c.flagHome [x]
    let (gPts1, gBlks1) := addGprPtBlk blk? c.nGpr gUse (eraseMany gUse gLv)
      acc.gprPts acc.gprPtBlks
    let (gPts, gBlks) := addGprPtBlk blk? c.nGpr gDef (eraseMany gDef gLa) gPts1 gBlks1
    let vPts := addVecPt c.nVec vDef.length (eraseMany vDef vLa) acc.vecPts
    let isZ32' :=
      if (I.gpr.zeroExtLoad && isGprTy I t) || (I.gpr.zeroUpper32Load && tyEq t (.bits 32)) then
        isZ32.insert x true
      else isZ32
    gatherAt c blk? lps lr mult isZ32' k { acc with
      weights := (mult, x :: uses) :: acc.weights, defInterf := di,
      gprPts := gPts, gprPtBlks := gBlks, vecPts := vPts, defWT := acc.defWT.insert x mult }
  | lps, lr, mult, isZ32, .store lv ip _ v a k, acc =>
    let uses := storeVarIds c.addrDeps c.rmwDeps ip v a
    let (gLv, vLv) := splitBank c.banks c.flagHome lv
    let (gUse, vUse) := splitBank c.banks c.flagHome uses
    let (gPts, gBlks) := addGprPtBlk blk? c.nGpr gUse (eraseMany gUse gLv)
      acc.gprPts acc.gprPtBlks
    gatherAt c blk? lps lr mult isZ32 k { acc with
      weights := addWeight mult uses acc.weights, gprPts := gPts, gprPtBlks := gBlks,
      vecPts := addVecPt c.nVec vUse.length (eraseMany vUse vLv) acc.vecPts }
  | lps, lr, mult, isZ32, .call _ _ nv0 _ as bs args k, acc =>
    let defs := (List.range bs.length).map (nv0 + ·)
    let la := k.lv
    let across := eraseMany defs la
    let di := defs.foldl (fun d x =>
      if natMem x la then (x, union defs la) :: d else d) acc.defInterf
    let (ag1, av1) := match I.assignArgs as with
      | some locs =>
        addAbiArgs (tupArgsToList args) (abiIdList c.allGpr c.allVec locs) (4 * mult)
          acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    let (ag2, av2) := match I.assignRets bs with
      | some locs =>
        addAbiArgs (defs.map some) (abiIdList c.allGpr c.allVec locs) (4 * mult) ag1 av1
      | none => (ag1, av1)
    let dw := defs.foldl (fun t x => t.insert x mult) acc.defWT
    let lc := if lps.isEmpty then acc.loopCall
      else across.foldl (fun t x => t.insert x true) acc.loopCall
    let isZ32' := (defs.zip bs).foldl (fun z (d, t) =>
      if isGprTy I t then z.insert d true else z) isZ32
    gatherAt c blk? lps lr mult isZ32' k { acc with
      weights := addWeight mult (defs ++ tupVarIds args) acc.weights, defInterf := di,
      abiGpr := ag2, abiVec := av2, callW := addWeight mult across acc.callW,
      loopCall := lc, defWT := dw }
  | lps, lr, mult, isZ32, .jnz lv ip cx _ t e, acc =>
    let (gLv, _) := splitBank c.banks c.flagHome lv
    let (gUse, _) := splitBank c.banks c.flagHome [cx]
    let inLoop := !lps.isEmpty
    let halfM := max 1 (mult / 2)
    let remHalf := max 1 (mult - halfM)
    let exitM := max 1 (mult / 10)
    let keepM := max 1 (mult - exitM)
    let guardM := max 1 (mult / 8)
    let contM := max 1 (mult - guardM)
    let asymM := max 1 (mult / 4)
    let mainM := max 1 (mult - asymM)
    let tt := isTrivialTerm t; let te := isTrivialTerm e
    let (mT, mE) :=
      if inLoop then
        let stT := jumpsToAny lps t; let stE := jumpsToAny lps e
        if stT && !stE then (keepM, exitM)
        else if stE && !stT then (exitM, keepM)
        else
          let rT := jumpsToAny lr t; let rE := jumpsToAny lr e
          if rT && !rE then (keepM, exitM)
          else if rE && !rT then (exitM, keepM)
          else if tt && !te then (guardM, contM)
          else if te && !tt then (contM, guardM)
          else (halfM, remHalf)
      else
        let lt := hasLoopTree c.loops t; let le := hasLoopTree c.loops e
        let ct := hasCallTree t; let ce := hasCallTree e
        if lt && !le then (if te then (contM, guardM) else (mainM, asymM))
        else if le && !lt then (if tt then (guardM, contM) else (asymM, mainM))
        else if ct && !ce then (if te then (contM, guardM) else (asymM, mainM))
        else if ce && !ct then (if tt then (guardM, contM) else (mainM, asymM))
        else if tt && !te then (guardM, contM)
        else if te && !tt then (contM, guardM)
        else (halfM, remHalf)
    let (gPts, gBlks) := addGprPtBlk blk? c.nGpr gUse (eraseMany gUse gLv)
      acc.gprPts acc.gprPtBlks
    let acc1 := gatherAt c blk? lps lr mE isZ32 e { acc with
      weights := (mult, [cx]) :: acc.weights, gprPts := gPts, gprPtBlks := gBlks,
      brW := acc.brW.insert ip (mult, mT, mE) }
    gatherAt c blk? lps lr mT isZ32 t acc1
  | lps, lr, mult, isZ32, .skip _ _ k, acc => gatherAt c blk? lps lr mult isZ32 k acc
  | _, _, mult, _, .jump _ ip j _ args, acc =>
    let acc := { acc with
      jmpW := acc.jmpW.insert ip mult, inW := acc.inW.insert j (acc.inW.getD j 0 + mult) }
    let as := tupArgsToList args
    let ps := c.bparams.getD j []
    let nonSelf := if ps.isEmpty then tupVarIds args else
      dedup ((as.zip ps).foldl (fun a (ao, p) =>
        match ao with
        | some x => if Nat.beq x p then a else x :: p :: a
        | none => p :: a) [])
    { acc with weights := addWeight mult nonSelf acc.weights,
               affEdges := addAffZip as ps (8 * mult) acc.affEdges,
               antiEdges := addAntiZip as ps (2 * mult) acc.antiEdges }
  | _, _, mult, _, .ret _ _ rs vs, acc =>
    let (ag, av) := match I.assignRets rs with
      | some locs =>
        addAbiArgs (tupArgsToList vs) (abiIdList c.allGpr c.allVec locs) (4 * mult)
          acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    { acc with weights := addWeight mult (tupVarIds vs) acc.weights, abiGpr := ag, abiVec := av }
  | _, _, mult, _, .exit _ _ _ as args, acc =>
    let (ag, av) := match I.assignArgs as with
      | some locs =>
        addAbiArgs (tupArgsToList args) (abiIdList c.allGpr c.allVec locs) (4 * mult)
          acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    { acc with weights := addWeight mult (tupVarIds args) acc.weights, abiGpr := ag, abiVec := av }
  | _, _, _, _, .stop _, acc => acc
  | lps, lr, mult, isZ32, .group _ bs k, acc =>
    gatherAtB c lps lr mult bs (gatherAt c blk? lps lr mult isZ32 k acc)

def gatherAtB {I : Isa} (c : Ctx I) :
    List Nat → List Nat → Nat → TreeBlocks → GatherAcc → GatherAcc
  | _, _, _, .nil, acc => acc
  | lps, lr, mult, .cons l ps b bs, acc =>
    let pvars := ps.map Prod.fst
    let le := b.lv
    let di := pvars.foldl (fun d p =>
      if natMem p le then (p, union pvars le) :: d else d) acc.defInterf
    let isLoop := c.loops.getD l false
    let mB :=
      if isLoop then
        let scaled := if lps.isEmpty then max (10 * mult) (10 * baseMult) else 10 * max mult 1
        min scaled 160000
      else mult
    let lps' := if isLoop then l :: lps else lps
    let lr' := if isLoop then union (c.loopReach.getD l []) lr else lr
    let dw := pvars.foldl (fun t p => t.insert p mB) acc.defWT
    let bp := pvars.foldl (fun t p => t.insert p true) acc.isBP
    gatherAtB c lps lr mult bs
      (gatherAt c (some l) lps' lr' mB .empty b { acc with
        weights := addWeight (baseMult / 4) pvars acc.weights,
        defInterf := di, defWT := dw, isBP := bp })
end

def gather {I : Isa} (c : Ctx I) (lps lr : List Nat) (mult : Nat) (isZ32 : Trie Bool)
    (t : Tree) (acc : GatherAcc) : GatherAcc :=
  gatherAt c none lps lr mult isZ32 t acc

def triePush {α : Type} (t : Trie (List α)) (k : Nat) (v : α) : Trie (List α) :=
  t.insert k (v :: t.getD k [])

def sumWeights (ws : List (Nat × List Nat)) : Trie Nat :=
  ws.foldl (fun t (w, vs) => vs.foldl (fun t x => t.insert x (t.getD x 0 + w)) t) .empty

def decPts (pids : List Nat) (pb : Trie Nat) : Trie Nat :=
  pids.foldl (fun pb p => pb.insert p (pb.getD p 0 - 1)) pb

def incPts (pids : List Nat) (pb : Trie Nat) : Trie Nat :=
  pids.foldl (fun pb p => pb.insert p (pb.getD p 0 + 1)) pb

/-- Coloring state: homes, used callee-saved ids, slot count, pressure budgets, and the backup
`(slot, width, eager)` of every split (call-crossing, caller-saved-homed) variable. -/
structure ColorSt (C : Type) where
  hT : Trie (Home C)
  usedCs : List Nat := []
  nslots : Nat := 0
  gPb : Trie Nat := .empty
  vPb : Trie Nat := .empty
  bk : Trie (Nat × SlotWidth × Bool) := .empty
  hint : Trie (Nat × Nat) := .empty
  forceEv : Trie (List Nat) := .empty

def isEagerBk (bk : Trie (Nat × SlotWidth × Bool)) (x : Nat) : Bool :=
  match bk.find? x with | some (_, _, e) => e | none => false

/-- Split a spilled GPR variable into a register outside `evBlks` (a high-pressure sub-region where
`x` is unused) by forcing `evIn` eviction on entry and reloading on exit when profitable. -/
def tryEvictSplit {I : Isa} (c : Ctx I) (x : Nat) (xI peers pids : List Nat)
    (ptBlks : Array (Option Nat)) (forbBkSlots : List (Nat × Nat))
    (prefs avoid : List (Nat × Nat)) (isBp : Bool) (dw cw wx slotCost : Nat)
    (s : ColorSt I.Cond) : Option (ColorSt I.Cond) :=
  if !(c.cfg.regEntry && c.cfg.sink) || !Nat.ble (10 * baseMult) wx then none
  else
    let zeroPids := pids.filter fun p => !Nat.ble 1 (s.gPb.getD p 0)
    if zeroPids.isEmpty then none
    else
      let badBlksOpt := zeroPids.foldl (fun (acc : Option (List Nat)) p =>
        match acc, ptBlks[p]? with
        | some bs, some (some b) => some (if natMem b bs then bs else b :: bs)
        | _, _ => none) (some [])
      match badBlksOpt with
      | none => none
      | some badBlks0 =>
        let evBlks := badBlks0.foldl (fun acc b =>
          let acc := if natMem b acc then acc else b :: acc
          if c.loops.getD b false then
            (c.loopReach.getD b []).foldl (fun a b2 =>
              if !natMem b2 a && natMem x (c.lTrie.getD b2 []) &&
                  !natMem x (c.blkUses.getD b2 []) &&
                  !(isBp && natMem x (c.bparams.getD b2 [])) then b2 :: a
              else a) acc
          else acc) []
        let okEv := evBlks.all fun b =>
          !natMem x (c.blkUses.getD b []) && !(isBp && natMem x (c.bparams.getD b []))
        if !okEv then none
        else
          let inEvBlk (p : Nat) : Bool := match ptBlks[p]? with
            | some (some b) => natMem b evBlks | _ => false
          let pidsOut := pids.filter (!inEvBlk ·)
          if !pidsOut.all (fun p => Nat.ble 1 (s.gPb.getD p 0)) then none
          else
            let wEnter := c.blkEdges.foldl (fun a (src, dst, w, _) =>
              if !natMem src evBlks && natMem dst evBlks &&
                  natMem x (c.lTrie.getD dst []) then a + w else a) 0
            let wExit := c.blkEdges.foldl (fun a (src, dst, w, _) =>
              if natMem src evBlks && !natMem dst evBlks &&
                  natMem x (c.lTrie.getD dst []) then a + w else a) 0
            let canEagerEv := !isBp && Nat.ble 1 cw && Nat.ble (dw + 1) (cw + wEnter)
            let evCost := (if canEagerEv then dw + cw else 2 * cw + wEnter) + min wEnter wExit
            let nEnter := c.blkEdges.foldl (fun a (src, dst, _, _) =>
              if !natMem src evBlks && natMem dst evBlks &&
                  natMem x (c.lTrie.getD dst []) then a + 1 else a) 0
            let nExit := c.blkEdges.foldl (fun a (src, dst, _, args) =>
              if natMem src evBlks && !natMem dst evBlks &&
                  (natMem x (c.lTrie.getD dst []) || natMem x args) then a + 1 else a) 0
            let usesOut := (c.varBlks.getD x []).foldl (fun a b =>
              if natMem b evBlks then a
              else (c.blkUses.getD b []).foldl (fun n y => if Nat.beq y x then n + 1 else n) a) 0
            let splitOps := (if canEagerEv then 1 else nEnter) + nExit
            let baseOps := (if isBp then 0 else 1) + usesOut
            let outPbOk := pidsOut.all (fun p => Nat.ble 2 (s.gPb.getD p 0)) || Nat.ble 8 usesOut
            if !outPbOk || !Nat.ble 1 wEnter || !Nat.ble (evCost + baseMult) slotCost ||
                !Nat.ble nExit 1 || !Nat.ble 8 usesOut ||
                !Nat.blt (2 * splitOps) baseOps then
              none
            else
              let exitArgs := c.blkEdges.foldl (fun a (src, dst, _, args) =>
                if natMem src evBlks && !natMem dst evBlks then args ++ a else a) []
              let isInterior (y : Nat) : Bool :=
                !natMem y exitArgs && (c.varBlks.getD y []).all (natMem · evBlks)
              let forbOut := xI.foldl (fun rs y =>
                if isInterior y then rs
                else match s.hT.getD y .none with
                  | .gpr r => if natMem r rs then rs else r :: rs | _ => rs) []
              let forbOutCaller := peers.foldl (fun rs z =>
                match s.hT.getD z .none with
                | .gpr r =>
                  if Nat.ble (r + 1) c.nGpr && !natMem r rs then r :: rs else rs
                | _ => rs) forbOut
              let evCaller := c.gAlloc.filter (!natMem · forbOutCaller)
              match bestRegPref prefs avoid evCaller with
              | none => none
              | some r =>
                let bSlot := firstFreeSlotRange 1 forbBkSlots
                let fe := evBlks.foldl (fun t b => triePush t b x) s.forceEv
                some { s with
                  hT := s.hT.insert x (.gpr r), gPb := decPts pidsOut s.gPb,
                  bk := s.bk.insert x (bSlot, .w64, canEagerEv),
                  nslots := max s.nslots (bSlot + 1), forceEv := fe }

/-- Color one variable `x` of weight `wx` and call-crossing weight `cw`. A call-crossing GPR
prefers an already-saved CS register; if splitting beats both saving a new CS register and spilling
(`cheapSplit`), it splits into a caller-saved register (cold-branch shrink-wrapping); otherwise it
tries a fresh CS register, then falls back to splitting (`splitOk`, using eager def-site backup
when `defW < cw` so loop-invariant vars pay zero stores inside loops) before spilling to a slot. -/
def colorOne {I : Isa} (c : Ctx I) (interf : Trie (List Nat)) (gVp gCp vVp : Trie (List Nat))
    (abiGT abiVT affT antiT : Trie (List (Nat × Nat))) (cwT defWT : Trie Nat)
    (loopCall isBP : Trie Bool) (zextPeers : Trie (List Nat)) (fnParams : List Nat)
    (ptBlks : Array (Option Nat)) (s : ColorSt I.Cond) (wx x : Nat) : ColorSt I.Cond :=
  let xI := interf.getD x []
  let peers := zextPeers.getD x []
  let forbSlots0 := xI.foldl (fun ss y =>
    let ss := match s.hT.getD y .none with | .slot b w => (b, w.slots) :: ss | _ => ss
    match s.bk.find? y with | some (b, w, _) => (b, w.slots) :: ss | none => ss) []
  let forbSlots := peers.foldl (fun ss y =>
    match s.bk.find? y with | some (b, w, _) => (b, w.slots) :: ss | none => ss) forbSlots0
  let forbBkSlots := peers.foldl (fun ss y =>
    match s.hT.getD y .none with | .slot b w => (b, w.slots) :: ss | _ => ss) forbSlots
  let isX := c.cross.getD x false
  let cw := cwT.getD x 0
  let dw := defWT.getD x baseMult
  let canEager := isX && !isBP.getD x false && Nat.ble (dw + 1) cw
  let splitCost := if canEager then dw + cw else 2 * cw
  let slotCost := wx + if natMem x fnParams then baseMult else 0
  let splitOk := Nat.ble (splitCost + 1) slotCost
  let cheapSplit :=
    isX && !loopCall.getD x false && splitOk && Nat.ble splitCost c.csCost
  let toSlot (w : SlotWidth) : ColorSt I.Cond :=
    let prefB := (affT.getD x []).foldl (fun best (y, wy) =>
      match s.hT.getD y .none with
      | .slot b0 w0 =>
        let ok := slotWidthEq w0 w &&
          !(forbSlots.any fun (bi, ki) => rangesOverlap b0 w.slots bi ki)
        if ok then
          match best with
          | some (_, bw) => if Nat.blt bw wy then some (b0, wy) else best
          | none => some (b0, wy)
        else best
      | _ => best) none
    let b := match prefB with | some (bp, _) => bp | none => firstFreeSlotRange w.slots forbSlots
    { s with hT := s.hT.insert x (.slot b w), nslots := max s.nslots (b + w.slots) }
  let withBk (w : SlotWidth) (s1 : ColorSt I.Cond) : ColorSt I.Cond :=
    let b := firstFreeSlotRange w.slots forbBkSlots
    { s1 with bk := s1.bk.insert x (b, w, canEager), nslots := max s1.nslots (b + w.slots) }
  match c.banks.getD x .gpr with
  | .gpr =>
    let bpSlotPref : Option Nat :=
      if !isBP.getD x false then none
      else
        let xs := affT.getD x []
        let totAff := xs.foldl (fun a (_, w) => a + w) 0 +
          (abiGT.getD x []).foldl (fun a (_, w) => a + w) 0
        let slotWs := xs.foldl (fun (acc : List (Nat × Nat)) (y, wy) =>
          match s.hT.getD y .none with
          | .slot b0 .w64 =>
            if forbSlots.any (fun (bi, ki) => rangesOverlap b0 1 bi ki) then acc
            else if acc.any (fun (b, _) => Nat.beq b b0) then
              acc.map fun (b, w) => if Nat.beq b b0 then (b, w + wy) else (b, w)
            else (b0, wy) :: acc
          | _ => acc) []
        let best := slotWs.foldl (fun (b : Option (Nat × Nat)) (s0, w0) =>
          match b with
          | some (_, bw) => if Nat.blt bw w0 then some (s0, w0) else b
          | none => some (s0, w0)) none
        match best with
        | some (s0, sw) =>
          if Nat.ble 1 sw && Nat.ble totAff (2 * sw) && Nat.ble (3 * wx) sw then some s0 else none
        | none => none
    match bpSlotPref with
    | some s0 => { s with hT := s.hT.insert x (.slot s0 .w64), nslots := max s.nslots (s0 + 1) }
    | none =>
      let forb := xI.foldl (fun rs y => match s.hT.getD y .none with
        | .gpr r => if natMem r rs then rs else r :: rs | _ => rs) []
      -- Never let a zero-copy `zext` peer share a caller-saved split register (`bk` collision).
      let forbCaller := peers.foldl (fun rs z => match s.hT.getD z .none with
        | .gpr r =>
          if ((s.bk.find? z).isSome || isX) && Nat.ble (r + 1) c.nGpr && !natMem r rs then r :: rs
          else rs
        | _ => rs) forb
      let pids := gVp.getD x []
      let cpids := gCp.getD x []
      let sharedPeerReg? : Option (Nat × List Nat) :=
        if isX then none
        else peers.findSome? fun z =>
          match s.hT.getD z .none with
          | .gpr r =>
            if Nat.blt r c.nGpr && (s.bk.find? z).isNone && !natMem r forb then
              let zPids := gVp.getD z []
              let extraPids := pids.filter (!natMem · zPids)
              if extraPids.all (fun p => Nat.ble 1 (s.gPb.getD p 0)) then some (r, extraPids)
              else none
            else none
          | _ => none
      let caller := if pids.all (fun p => Nat.ble 1 (s.gPb.getD p 0)) then
          c.gAlloc.filter (!natMem · forbCaller) else []
      let csFree := s.usedCs.filter (!natMem · forb)
      let baseCsThresh := if Nat.ble c.nGpr 8 then 2 * baseMult + 1 else 3 * baseMult
      let leafExtra := if c.isLeaf && s.usedCs.isEmpty then 2 * baseMult else 0
      let csThresh := max (baseCsThresh + leafExtra) c.csCost
      let newCs := if Nat.ble csThresh wx then
          c.csIds.filter (fun r => !natMem r s.usedCs && !natMem r forb) else []
      let prefs := (affT.getD x []).foldl (fun ps (y, w) =>
        match s.hT.getD y .none with
        | .gpr ry => (ry, w) :: ps
        | .none => (abiGT.getD y []).foldl (fun ps (ry, wy) => (ry, min w wy / 2) :: ps) ps
        | _ => ps) (abiGT.getD x [])
      let avoid0 := (antiT.getD x []).foldl (fun ps (y, w) =>
        match s.hT.getD y .none with | .gpr ry => (ry, w) :: ps | _ => ps) []
      let avoid := xI.foldl (fun ps z =>
        match s.hT.getD z .none with
        | .none => (abiGT.getD z []).foldl (fun a p => p :: a) ps
        | .slot _ _ => match s.hint.find? z with | some h => h :: ps | none => ps
        | _ => ps) avoid0
      let toSlotG : ColorSt I.Cond :=
        let s1 := toSlot .w64
        let best := prefs.foldl (fun (b : Option (Nat × Nat)) (r, _) =>
          let tw := regWeight prefs r
          match b with
          | some (_, bw) => if Nat.blt bw tw then some (r, tw) else b
          | none => if Nat.ble (r + 1) (c.nGpr + c.csIds.length) then some (r, tw) else none) none
        match best with
        | some (r, _) =>
          if c.cfg.cacheHint then { s1 with hint := s1.hint.insert x (r, wx) } else s1
        | none => s1
      let inReg (r : Nat) : ColorSt I.Cond :=
        let gPb1 :=
          if Nat.ble (r + 1) c.nGpr then decPts pids s.gPb else incPts cpids s.gPb
        let s1 := { s with hT := s.hT.insert x (.gpr r), gPb := gPb1 }
        if isX && Nat.ble (r + 1) c.nGpr then withBk .w64 s1 else s1
      let inNewCs (r : Nat) : ColorSt I.Cond :=
        { s with hT := s.hT.insert x (.gpr r), usedCs := s.usedCs ++ [r],
                 gPb := incPts cpids s.gPb }
      let toSlotOrEv : ColorSt I.Cond :=
        match tryEvictSplit c x xI peers pids ptBlks forbBkSlots prefs avoid
            (isBP.getD x false) dw cw wx slotCost s with
        | some sEv => sEv
        | none => toSlotG
      let orSplitOrSlot : ColorSt I.Cond :=
        match (if isX && splitOk then bestRegPref prefs avoid caller else none) with
        | some r => inReg r
        | none => toSlotOrEv
      let orNewCs : ColorSt I.Cond :=
        match bestRegPref prefs avoid newCs with
        | some r => inNewCs r
        | none => orSplitOrSlot
      if !isX then
        match sharedPeerReg? with
        | some (r, extraPids) =>
          { s with hT := s.hT.insert x (.gpr r), gPb := decPts extraPids s.gPb }
        | none =>
          match bestRegPref prefs avoid (caller ++ csFree) with
          | some r => inReg r
          | none => orNewCs
      else
        match bestRegPref prefs avoid csFree with
        | some r => inReg r
        | none =>
          match (if cheapSplit then bestRegPref prefs avoid caller else none) with
          | some r => inReg r
          | none => orNewCs
  | .vec w =>
    let forb := xI.foldl (fun rs y => match s.hT.getD y .none with
      | .vec v => if natMem v rs then rs else v :: rs | _ => rs) []
    let pids := vVp.getD x []
    let cands := if (!isX || splitOk) && pids.all (fun p => Nat.ble 1 (s.vPb.getD p 0)) then
        c.vAlloc.filter (!natMem · forb) else []
    let prefs := (affT.getD x []).foldl (fun ps (y, w) =>
      match s.hT.getD y .none with
      | .vec vy => (vy, w) :: ps
      | .none => (abiVT.getD y []).foldl (fun ps (vy, wy) => (vy, min w wy / 2) :: ps) ps
      | _ => ps) (abiVT.getD x [])
    let avoid0 := (antiT.getD x []).foldl (fun ps (y, w) =>
      match s.hT.getD y .none with | .vec vy => (vy, w) :: ps | _ => ps) []
    let avoid := xI.foldl (fun ps z =>
      match s.hT.getD z .none with
      | .none => (abiVT.getD z []).foldl (fun a p => p :: a) ps
      | _ => ps) avoid0
    match bestRegPref prefs avoid cands with
    | some v =>
      let s1 := { s with hT := s.hT.insert x (.vec v),
                         vPb := if Nat.ble (v + 1) c.nVec then decPts pids s.vPb else s.vPb }
      if isX then withBk w s1 else s1
    | none => toSlot w

def colorVars {I : Isa} (c : Ctx I) (nv : Nat) (flagHome : Trie I.Cond) (acc : GatherAcc)
    (fnParams : List Nat) (fnAbi : List (Option (Sum Nat Nat))) : ColorSt I.Cond :=
  let (abiG, abiV) :=
    addAbiArgs (fnParams.map some) fnAbi (4 * baseMult) acc.abiGpr acc.abiVec
  let wTrie := sumWeights acc.weights
  let cwT := sumWeights acc.callW
  let di0 := fnParams.foldl (fun d p => (p, fnParams) :: d) acc.defInterf
  let order := sortByWeight nv ((dedup (di0.map Prod.fst)).map fun x => (wTrie.getD x 0, x))
  let interf : Trie (List Nat) := di0.foldl (fun t (z, ys) =>
    let (zL, t) := ys.foldl (fun (zAcc, t) y =>
      if Nat.beq y z then (zAcc, t) else (y :: zAcc, triePush t y z)) (t.getD z [], t)
    t.insert z zL) .empty
  let (gPb0, gVp, gCp, _) := acc.gprPts.foldl
    (fun (pb, vp, cp, pid) (b, vs, cvs) =>
      (pb.insert pid b, vs.foldl (fun vp x => triePush vp x pid) vp,
        cvs.foldl (fun cp u => triePush cp u pid) cp, pid + 1))
    (.empty, .empty, .empty, 0)
  let (vPb0, vVp, _) := acc.vecPts.foldl
    (fun (pb, vp, pid) (b, vs) =>
      (pb.insert pid b, vs.foldl (fun vp x => triePush vp x pid) vp, pid + 1))
    (.empty, .empty, 0)
  let abiGT : Trie (List (Nat × Nat)) := abiG.foldl (fun t (u, r, w) => triePush t u (r, w)) .empty
  let abiVT : Trie (List (Nat × Nat)) := abiV.foldl (fun t (u, r, w) => triePush t u (r, w)) .empty
  let affT : Trie (List (Nat × Nat)) := acc.affEdges.foldl (fun t (u, v, w) =>
    if Nat.beq u v then t else triePush (triePush t u (v, w)) v (u, w)) .empty
  let antiT : Trie (List (Nat × Nat)) := acc.antiEdges.foldl (fun t (u, v, w) =>
    if Nat.beq u v then t else triePush (triePush t u (v, w)) v (u, w)) .empty
  let zextPeers : Trie (List Nat) := acc.zextEdges.foldl (fun t (u, v) =>
    if Nat.beq u v then t else triePush (triePush t u v) v u) .empty
  let initHome : Trie (Home I.Cond) := (List.range nv).foldl (fun h x =>
    match flagHome.find? x with | some cc => h.insert x (.flag cc) | none => h) .empty
  let ptBlks := acc.gprPtBlks.toArray
  order.foldl (fun s (wx, x) =>
    match s.hT.find? x with
    | some (.flag _) => s
    | _ =>
      colorOne c interf gVp gCp vVp abiGT abiVT affT antiT cwT acc.defWT acc.loopCall acc.isBP
        zextPeers fnParams ptBlks s wx x)
    { hT := initHome, gPb := gPb0, vPb := vPb0 }

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

mutual
def scanSlotPlocBad {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond))
    (bk : Trie (Nat × SlotWidth × Bool)) (usedCs : List Nat) (bad : Trie Bool) :
    Tree → Trie Bool
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k
  | .call _ _ _ _ _ _ _ k | .skip _ _ k => scanSlotPlocBad c home bk usedCs bad k
  | .jnz _ _ _ _ t1 t2 =>
    scanSlotPlocBad c home bk usedCs (scanSlotPlocBad c home bk usedCs bad t1) t2
  | .group _ bs k =>
    scanSlotPlocBadB c home bk usedCs (scanSlotPlocBad c home bk usedCs bad k) bs
  | .jump lv _ j _ args =>
    let varSlot (x : Nat) : Option (Nat × Nat) :=
      match home.getD x .none with
      | .slot s w => some (s, w.slots)
      | _ => match bk.find? x with | some (s, w, _) => some (s, w.slots) | none => none
    let ps := c.bparams.getD j []
    let as := tupArgsToList args
    let liveSlots := (c.lTrie.getD j []).filterMap varSlot
    let busyG := gprHomes home lv
    let hasFree := (c.gAlloc ++ usedCs).any (!natMem · busyG)
    let argSlots := as.map fun ao => ao.bind varSlot
    ((as.zip ps).zip (List.range ps.length)).foldl (fun b ((ao, p), idx) =>
      match home.getD p .none with
      | .slot s .w64 =>
        let argConf := (argSlots.zip (List.range argSlots.length)).any fun (so, idx') =>
          !Nat.beq idx idx' && match so with
            | some (s', k') => rangesOverlap s 1 s' k' | none => false
        let liveConf := liveSlots.any fun (s', k') => rangesOverlap s 1 s' k'
        let needsTmp := match ao with
          | some x => match home.getD x .none with
            | .slot s' .w64 => !Nat.beq s s'
            | .gpr _ => false
            | _ => true
          | none => true
        if argConf || liveConf || (needsTmp && !hasFree) then b.insert p true else b
      | _ => b) bad
  | _ => bad

def scanSlotPlocBadB {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond))
    (bk : Trie (Nat × SlotWidth × Bool)) (usedCs : List Nat) (bad : Trie Bool) :
    TreeBlocks → Trie Bool
  | .nil => bad
  | .cons _ _ b bs =>
    scanSlotPlocBadB c home bk usedCs (scanSlotPlocBad c home bk usedCs bad b) bs
end

mutual
/-- Block parameters that receive, on some incoming jump, an argument already homed in the
parameter's own slot (a zero-move slot-direct edge). -/
private def scanSlotIdent {C : Type} (bparams : Trie (List Nat)) (home : Trie (Home C))
    (acc : Trie Bool) : Tree → Trie Bool
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k
  | .call _ _ _ _ _ _ _ k | .skip _ _ k => scanSlotIdent bparams home acc k
  | .jnz _ _ _ _ t1 t2 => scanSlotIdent bparams home (scanSlotIdent bparams home acc t1) t2
  | .group _ bs k => scanSlotIdentB bparams home (scanSlotIdent bparams home acc k) bs
  | .jump _ _ j _ args =>
    ((tupArgsToList args).zip (bparams.getD j [])).foldl (fun a (ao, p) =>
      match ao.map (home.getD · .none), home.getD p .none with
      | some (.slot s' _), .slot s _ => if Nat.beq s s' then a.insert p true else a
      | _, _ => a) acc
  | _ => acc

private def scanSlotIdentB {C : Type} (bparams : Trie (List Nat)) (home : Trie (Home C))
    (acc : Trie Bool) : TreeBlocks → Trie Bool
  | .nil => acc
  | .cons _ _ b bs => scanSlotIdentB bparams home (scanSlotIdent bparams home acc b) bs
end

/-- Execution weight with which `p` is first read in a tree of weight `w` before any call or
block boundary, i.e. while a register arrival of `p` would still serve the read. -/
def firstUseW {I : Isa} (c : Ctx I) (p : Nat) : Nat → Tree → Nat
  | w, .let_ _ ip _ _ op k =>
    if natMem p (c.addrDeps.getD ip (opVarIds op)) then w else firstUseW c p w k
  | w, .load _ ip _ _ a k =>
    if natMem p (c.addrDeps.getD ip (argVarIds a)) then w else firstUseW c p w k
  | w, .store _ ip _ v a k =>
    if natMem p (argVarIds v ++ c.addrDeps.getD ip (argVarIds a)) then w else firstUseW c p w k
  | w, .call _ _ _ _ _ _ args _ => if natMem p (tupVarIds args) then w else 0
  | w, .jnz _ ip cx _ t e =>
    if Nat.beq cx p then w
    else
      let (_, mT, mE) := c.brW.getD ip (w, w, w)
      firstUseW c p mT t + firstUseW c p mE e
  | w, .skip _ _ k | w, .group _ _ k => firstUseW c p w k
  | w, .jump _ _ _ _ args => if natMem p (tupVarIds args) then w else 0
  | w, .ret _ _ _ vs => if natMem p (tupVarIds vs) then w else 0
  | w, .exit _ _ _ _ args => if natMem p (tupVarIds args) then w else 0
  | _, .stop _ => 0

/-- Number of distinct GPRs statically homed at entry to block `l` (`liveL` plus `ps`). -/
private def blockUsedGpr {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond))
    (l : Nat) (ps : List (Nat × Ty)) : Nat :=
  (dedup (gprHomes home (c.lTrie.getD l [] ++ ps.map Prod.fst))).length

/-- Number of block parameters `ps` needing a fresh GPR in `pickPlocs`, given `useSlot p` (whether
`.slot _ .w64` keeps its slot directly). -/
def countPlocGprs {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond))
    (useSlot : Nat → Bool) (ps : List (Nat × Ty)) : Nat :=
  ps.foldl (fun n (p, _) =>
    match home.getD p .none with
    | .flag _ | .gpr _ | .vec _ => n
    | .slot _ .w64 => if useSlot p then n else n + 1
    | _ => if (c.banks.getD p .gpr).isVec then n else n + 1) 0

/-- Determine which slot-homed GPR block parameters can safely use `.slot s .w64` directly as their
`Entry.ploc` (avoiding jump-edge reload + block-entry store round-trips): safe when no other
incoming jump arg or block live-in variable occupies slot `s`, and every jump needing a temporary
register to materialize an immediate or copy from another slot has a free non-scratch GPR. With
`cfg.joinGuard`, a parameter without a zero-move (same-slot) incoming edge that is read early
in its block on at least half of the block's weight keeps a register `Entry.ploc` instead (bounded
by the block's total GPR budget `nGpr + csIds.length`): the slot-direct form would store on every
edge and reload at once (a join round-trip). -/
def slotPlocMap {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond))
    (bk : Trie (Nat × SlotWidth × Bool)) (usedCs : List Nat) (defWT : Trie Nat) (t : Tree) :
    Trie Bool :=
  let bad := scanSlotPlocBad c home bk usedCs .empty t
  let ident := if c.cfg.joinGuard then scanSlotIdent c.bparams home .empty t else .empty
  let cap := c.nGpr + c.csIds.length
  let rec markOk (ok : Trie Bool) : List (Nat × List (Nat × Ty) × Tree) → Trie Bool
    | [] => ok
    | (l, ps, b) :: rest =>
      let usedG := blockUsedGpr c home l ps
      let fixedNeed := countPlocGprs c home (fun p => !bad.getD p false) ps
      let (ok', _) := ps.foldl (fun (o, rem) (p, _) =>
        match home.getD p .none with
        | .slot _ .w64 =>
          if bad.getD p false then (o, rem)
          else
            let wB := defWT.getD p baseMult
            let hot := c.cfg.joinGuard && !ident.getD p false &&
              Nat.ble wB (2 * firstUseW c p wB b)
            if hot && Nat.ble 1 rem then (o, rem - 1)
            else (o.insert p true, rem)
        | _ => (o, rem)) (ok, cap - (usedG + fixedNeed))
      markOk ok' rest
  markOk .empty t.blocks

/-- Emitted hints; `cin` collects, in an optimistic pass, one `(label, var, reg, deferred,
weight)` record per jump and slot-homed variable that reaches the target cached in `reg`. -/
structure EmitSt (I : Isa) where
  (dest : Trie I.Loc := .empty) (entry : Trie (Entry I.Reg I.VReg I.Cond) := .empty)
  (pre : Trie (PreStep I.Reg I.VReg I.Cond) := .empty)
  (variant : Trie VariantHint := .empty) (usedCs : List Nat := [])
  (cin : List (Nat × Nat × Nat × Bool × Nat) := [])
  (evArr : List (Nat × Nat × Bool × Bool × Nat) := [])

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
    -- An else-arm edge block is laid out inline: the then-arm then pays a taken branch.
    cT + cE + (match e with | .jump .. => if Nat.ble 1 cE then mT else 0 | _ => 0)
  | w, arm, .jump _ _ j _ _ =>
    if natMem x (c.lTrie.getD j []) &&
        !((c.regIn.getD j []).any fun (y, _, inS) => Nat.beq y x && !inS) then
      (if arm then 2 * w else w)
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
    Nat.blt (cT + cE + (match e with | .jump .. => if Nat.ble 1 cE then mT else 0 | _ => 0)) m
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
            match freshRegAvoid (c.gAlloc ++ usedCs) gb cachedG (candDf.map (·.2.2)) with
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
    match home.getD p .none with
    | .flag cc => (.flag cc :: ls, none :: ids, gb, vb, cs)
    | .gpr r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
    | .vec v => match c.vReg.find? v with
      | some vr => (.vec vr :: ls, some (.inr v) :: ids, gb, v :: vb, cs)
      | none => (ls, none :: ids, gb, vb, cs)
    | .slot s .w64 =>
      let hr := (c.hintT.find? p).bind fun (rh, _) =>
        if (Nat.ble (rh + 1) c.nGpr || natMem rh cs) && !natMem rh gb then some rh else none
      if slotOk.getD p false then (.slot s .w64 :: ls, none :: ids, gb, vb, cs)
      else match hr <|> freshReg (c.gAlloc ++ cs) gb with
        | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
        | none => match c.csIds.find? (fun r => !natMem r gb && !natMem r cs) with
          | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs ++ [r])
          | none => match c.gAlloc.head? with
            | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
            | none => (ls, none :: ids, gb, vb, cs)
    | _ =>
      if (c.banks.getD p .gpr).isVec then
        match (freshReg c.vAlloc vb <|> c.vAlloc.head?).bind fun v =>
            (c.vReg.find? v).map (v, ·) with
        | some (v, vr) => (.vec vr :: ls, some (.inr v) :: ids, gb, v :: vb, cs)
        | none => (ls, none :: ids, gb, vb, cs)
      else match freshReg (c.gAlloc ++ cs) gb with
        | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
        | none => match c.csIds.find? (fun r => !natMem r gb && !natMem r cs) with
          | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs ++ [r])
          | none => match c.gAlloc.head? with
            | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
            | none => (ls, none :: ids, gb, vb, cs))
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
  let tmp? :=
    freshReg (c.gAlloc ++ usedCs) busy <|> freshReg (c.gAlloc ++ usedCs) (gprHomes home lv)
  (sas.zip ps).foldl (fun mvs (sao, p) =>
    if !slotOk.getD p false then mvs
    else match home.getD p .none with
      | .slot s .w64 =>
        match sao with
        | some (.var x) =>
          match home.getD x .none with
          | .slot s' .w64 =>
            if Nat.beq s s' then mvs
            else match gCache.find? (fun (y, _) => Nat.beq y x) with
              | some (_, r) => mvs ++ [.st s (gOf r)]
              | none => match tmp? with
                | some tmp => mvs ++ [.ld (gOf tmp) s', .st s (gOf tmp)]
                | none => mvs
          | .gpr r => mvs ++ [.st s (gOf r)]
          | _ => mvs
        | some (.immBits _ k) =>
          match tmp? with
          | some tmp => mvs ++ [.movi (gOf tmp) k, .st s (gOf tmp)]
          | none => mvs
        | some (.immBool b) =>
          match tmp? with
          | some tmp => mvs ++ [.movi (gOf tmp) (if b then 1#64 else 0#64), .st s (gOf tmp)]
          | none => mvs
        | _ => mvs
      | _ => mvs) []

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

private abbrev RegionVarSet := List Nat × Trie Unit

private def rvsAdd (s : RegionVarSet) (xs : List Nat) : RegionVarSet :=
  xs.foldl (fun (ks, t) x => if trieMem t x then (ks, t) else (x :: ks, t.insert x ())) s

private def rvsUnion (a b : RegionVarSet) : RegionVarSet :=
  if Nat.ble a.1.length b.1.length then rvsAdd b a.1 else rvsAdd a b.1

mutual
/-- Linear bottom-up pass recording, at each `.let_` `ip`, the continuation live-ins reused
within the same extended-basic-block region before `.call`/`.ret`/`.exit`/`.stop`. -/
private def buildRegionReused {I : Isa} (c : Ctx I) :
    Tree → Trie (List Nat) → RegionVarSet × Trie (List Nat)
  | .let_ _ ip _ _ op k, acc =>
    let ((ksK, mK), acc1) := buildRegionReused c k acc
    let both := k.lv.filter (trieMem mK ·)
    let acc2 := if both.isEmpty then acc1 else acc1.insert ip both
    (rvsAdd (ksK, mK) (c.addrDeps.getD ip (opVarIds op)), acc2)
  | .load _ ip _ _ a k, acc =>
    let (vsK, acc1) := buildRegionReused c k acc
    (rvsAdd vsK (c.addrDeps.getD ip (argVarIds a)), acc1)
  | .store _ ip _ v a k, acc =>
    let (vsK, acc1) := buildRegionReused c k acc
    (rvsAdd vsK (storeVarIds c.addrDeps c.rmwDeps ip v a), acc1)
  | .skip _ _ k, acc => buildRegionReused c k acc
  | .group _ bs k, acc =>
    let acc1 := buildRegionReusedB c bs acc
    buildRegionReused c k acc1
  | .jnz _ _ cx _ t e, acc =>
    let (vsT, acc1) := buildRegionReused c t acc
    let (vsE, acc2) := buildRegionReused c e acc1
    (rvsAdd (rvsUnion vsT vsE) [cx], acc2)
  | .jump _ _ j _ args, acc =>
    (rvsAdd (rvsAdd ([], .empty) (tupVarIds args)) (c.lTrie.getD j []), acc)
  | .call _ _ _ _ _ _ args k, acc =>
    let (_, acc1) := buildRegionReused c k acc
    (rvsAdd ([], .empty) (tupVarIds args), acc1)
  | .ret _ _ _ args, acc | .exit _ _ _ _ args, acc =>
    (rvsAdd ([], .empty) (tupVarIds args), acc)
  | .stop _, acc => (([], .empty), acc)

private def buildRegionReusedB {I : Isa} (c : Ctx I) :
    TreeBlocks → Trie (List Nat) → Trie (List Nat)
  | .nil, acc => acc
  | .cons _ _ b bs, acc => buildRegionReusedB c bs (buildRegionReused c b acc).2
end

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
    let la := laAfter.filter fun x => (bk.find? x).isSome
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
    let st1 := emitAlloc c home bk slotOk clrAt r0 r1 e
      { gDf := df2.filter fun (y, _, _) => natMem y e.lv } ev' sv
      (gC1.filter fun (y, _) => natMem y e.lv) (vC1.filter fun (y, _) => natMem y e.lv)
      { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
    emitAlloc c home bk slotOk clrAt r0 r1 t
      { gDf := df2.filter fun (y, _, _) => natMem y t.lv } ev' sv
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
    { st with
      pre := recordPre ip (clrAt.getD ip false) (mvs0 ++ smvs) st.pre,
      cin := cin, evArr := evArr }
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

/-- Register entries for spilled live-ins (`cfg.regEntry`): from the `(label, var, reg,
deferred, weight)` records of an optimistic emission pass, let block `l` take slot-homed `x` in
register `r` when the predecessors mostly hold it there. `(x, r, false)` enters in the register
only (its slot store stays deferred into the block); `(x, r, true)` enters in slot and register
(no reload at the first read). Each choice must beat the slot-only entry on estimated cost. -/
def pickRegIn {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (usedCs : List Nat)
    (slotOk : Trie Bool) (cin : List (Nat × Nat × Nat × Bool × Nat))
    (blocks : List (Nat × List (Nat × Ty) × Tree)) : Trie (List (Nat × Nat × Bool)) :=
  let gprBudget := c.nGpr + usedCs.length
  blocks.foldl (fun acc (l, ps, body) =>
    let es := cin.filter fun e => Nat.beq e.1 l
    if es.isEmpty then acc
    else
      let wj := c.inW.getD l 0
      let busy0 := dedup (gprHomes home (c.lTrie.getD l [] ++ ps.map Prod.fst))
      let needPloc := countPlocGprs c home (fun p => slotOk.getD p false) ps
      let sumW (xs : List (Nat × Nat × Nat × Bool × Nat)) := xs.foldl (fun a e => a + e.2.2.2.2) 0
      let (sel, _) := (dedup (es.map (·.2.1))).foldl (fun (sel, busy) x =>
        if !Nat.blt (busy.length + needPloc) gprBudget then (sel, busy)
        else
          let ex := es.filter fun e => Nat.beq e.2.1 x
          let regs := (dedup (ex.map (·.2.2.1))).filter fun r =>
            !natMem r busy && (Nat.ble (r + 1) c.nGpr || natMem r usedCs)
          let best := regs.foldl (fun (b : Option (Nat × Nat)) r =>
            let wr := sumW (ex.filter fun e => Nat.beq e.2.2.1 r)
            match b with
            | some (_, bw) => if Nat.blt bw wr then some (r, wr) else b
            | none => some (r, wr)) none
          match best with
          | none => (sel, busy)
          | some (r, wc) =>
            let wd := sumW (ex.filter (·.2.2.2.1))
            let miss := wj - wc
            let costS := wd + firstUseW c x wj body
            let costR := sinkCost c x wj false body + miss
            let costSR := wd + miss
            let sharedSlot := match home.getD x .none with
              | .slot sx _ =>
                (c.lTrie.getD l []).any fun y =>
                  !Nat.beq y x && match home.getD y .none with
                    | .slot sy _ => Nat.beq sx sy | _ => false
              | _ => false
            if !sharedSlot && Nat.ble 1 wd && Nat.blt costR costS && Nat.ble costR costSR then
              ((x, r, false) :: sel, r :: busy)
            else if Nat.blt costSR costS then ((x, r, true) :: sel, r :: busy)
            else (sel, busy)) ([], busy0)
      if sel.isEmpty then acc else acc.insert l sel) .empty

/-- Weighted reload `(cost, leafCount)` inside `t` when split var `x` enters evicted (`ev`). -/
def evBodyCost {I : Isa} (c : Ctx I) (x : Nat) (evIn : Trie (List Nat)) :
    Nat → Tree → Nat × Nat
  | w, .let_ _ ip _ _ op k =>
    if natMem x (c.addrDeps.getD ip (opVarIds op)) then (w, 1) else evBodyCost c x evIn w k
  | w, .load _ ip _ _ a k =>
    if natMem x (c.addrDeps.getD ip (argVarIds a)) then (w, 1) else evBodyCost c x evIn w k
  | w, .store _ ip _ v a k =>
    if natMem x (storeVarIds c.addrDeps c.rmwDeps ip v a) then (w, 1)
    else evBodyCost c x evIn w k
  | w, .call _ _ _ _ _ _ args _ => if natMem x (tupVarIds args) then (w, 1) else (0, 0)
  | w, .jnz _ ip cx _ t e =>
    if Nat.beq cx x then (w, 1)
    else
      let (_, mT, mE) := c.brW.getD ip (w, w, w)
      let (cT, lT) := evBodyCost c x evIn mT t
      let (cE, lE) := evBodyCost c x evIn mE e
      let extra := match e with | .jump .. => if Nat.ble 1 cE then mT else 0 | _ => 0
      (cT + cE + extra, lT + lE)
  | w, .skip _ _ k | w, .group _ _ k => evBodyCost c x evIn w k
  | w, .jump _ _ j _ args =>
    if natMem x (tupVarIds args) ||
        (natMem x (c.lTrie.getD j []) && !(evIn.getD j []).any (Nat.beq · x)) then
      (w, 1)
    else (0, 0)
  | w, .ret _ _ _ vs => if natMem x (tupVarIds vs) then (w, 1) else (0, 0)
  | w, .exit _ _ _ _ args => if natMem x (tupVarIds args) then (w, 1) else (0, 0)
  | _, .stop _ => (0, 0)

/-- Choose split variables to enter block `l` in their backup slot (`evIn`) instead of reloading
before every jump into `l`, saving reloads at predecessors that arrive evicted or dead-on-call. -/
def pickEvIn {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond))
    (evArr : List (Nat × Nat × Bool × Bool × Nat))
    (prevEv : Trie (List Nat)) (blocks : List (Nat × List (Nat × Ty) × Tree)) :
    Trie (List Nat) :=
  let sumW (xs : List (Nat × Nat × Bool × Bool × Nat)) :=
    xs.foldl (fun a e => a + e.2.2.2.2) 0
  blocks.foldl (fun acc (l, _, body) =>
    let es := evArr.filter fun e => Nat.beq e.1 l
    if es.isEmpty then acc
    else
      let wj := c.inW.getD l 0
      let sel := (dedup (es.map (·.2.1))).filter fun x =>
        match home.getD x .none with
        | .gpr _ =>
          let ex := exFilter es x
          let evEdges := ex.filter (·.2.2.1)
          let savEdges := ex.filter (·.2.2.2.1)
          let wEv := sumW evEdges
          let wSav := sumW savEdges
          let (cost, leaves) := evBodyCost c x prevEv wj body
          let leafOk := Nat.ble (savEdges.length + leaves) evEdges.length ||
            Nat.ble (2 * (wSav + cost)) wEv
          Nat.ble 1 wEv && ((Nat.blt (wSav + cost) wEv && leafOk) ||
            (Nat.ble (leaves + 1) evEdges.length && Nat.ble (wSav + cost) wEv))
        | _ => false
      let forced := c.forceEv.getD l []
      let sel' := forced.foldl (fun s x => if natMem x s then s else x :: s) sel
      if sel'.isEmpty then acc else acc.insert l sel') .empty
where
  exFilter (es : List (Nat × Nat × Bool × Bool × Nat)) (x : Nat) :=
    es.filter fun e => Nat.beq e.2.1 x

def maxSlotInMoves {I : Isa} (mvs : List I.Move) (acc : Nat) : Nat :=
  mvs.foldl (fun m mv => match mv with
    | .ld _ i | .st i _ => max m (i + 1)
    | .vld w _ i | .vst w i _ => max m (i + w.slots)
    | _ => m) acc

def maxSlotInLocs {I : Isa} (locs : List I.Loc) (acc : Nat) : Nat :=
  locs.foldl (fun m loc => match loc with | .slot i w => max m (i + w.slots) | _ => m) acc

def usedSlotCount {I : Isa} (nip nl : Nat) (st : EmitSt I) : Nat :=
  let m1 := (List.range nip).foldl (fun m ip =>
    match st.pre.find? ip with | some ps => maxSlotInMoves ps.moves m | none => m) 0
  (List.range nl).foldl (fun m l =>
    match st.entry.find? l with
    | some en => maxSlotInLocs (en.live.map Prod.snd) (maxSlotInLocs en.ploc m)
    | none => m) m1

/-- Compute untrusted `Hints` for `Rega.lowerFn` via per-bank priority graph coloring. -/
def hints (I : Isa) (f : Fn)
    (condCands : List I.Cond :=
      I.gpr.zeroFlags ++ I.gpr.zeroFlags.map I.gpr.negCond ++ I.gpr.cmpFlags)
    (cfg : Cfg := {}) : I.Hints :=
  let nGpr := I.frame.allocatable.length
  let nCs := I.frame.calleeSaved.length
  let allGpr := I.frame.allocatable ++ I.frame.calleeSaved ++ I.frame.scratch ++
    I.frame.argRegs ++ I.frame.retRegs
  let nVec := I.vec.vecAllocatable.length
  let allVec := I.vec.vecAllocatable ++ I.vec.vecScratch ++ I.vec.vecArgRegs ++ I.vec.vecRetRegs
  let (t0, fnPs, nv, nl, nip, tys) := Tree.ofFn f
  let (t1a, elideIps0, addrDeps0) := elideAddrTreeDeps I t0
  let (t1b, elideIps1, addrDeps) := elideCmpTreeDeps I t1a elideIps0 addrDeps0
  let (t1, elideIps, rmwDeps) := elideRmwTreeDeps I t1b elideIps1 addrDeps
  let bs0 := t1.blocks
  let lTrie := liveLabels bs0 addrDeps rmwDeps
  let (_, t) := fillLive lTrie addrDeps rmwDeps t1
  let crossList := acrossCalls t
  let crossTrie := crossList.foldl (fun a x => a.insert x true) .empty
  let isLeaf := crossList.isEmpty
  let bparamsTrie := bs0.foldl (fun a (l, ps, _) => a.insert l (ps.map Prod.fst)) .empty
  let fh := match I.frame.allocatable.head? with
    | some r0 =>
      let r1 := I.frame.allocatable[1]?.getD r0
      let v0 := I.vec.vecAllocatable.head?
      let v1 := I.vec.vecAllocatable[1]? <|> v0
      gatherFlags I r0 r1 v0 v1 condCands nv (fnPs.map Prod.fst) crossTrie bparamsTrie tys lTrie t
    | none => {}
  let (loops, loopReach) := loopBlocksScoped (blocksWithMin t1)
  let numRets := max 1 (countRets t1)
  let csCost := (1 + numRets) * baseMult
  let c : Ctx I := {
    allGpr := allGpr, allVec := allVec,
    gReg := (allGpr.foldl (fun (t, i) r => (t.insert i r, i + 1)) (.empty, 0)).1,
    vReg := (allVec.foldl (fun (t, i) v => (t.insert i v, i + 1)) (.empty, 0)).1,
    nGpr := nGpr, nVec := nVec, gAlloc := List.range nGpr,
    csIds := (List.range nCs).map (· + nGpr), vAlloc := List.range nVec,
    gScr := if I.frame.scratch.isEmpty then none else some (nGpr + nCs),
    vScr := if I.vec.vecScratch.isEmpty then none else some nVec,
    cross := crossTrie, loops := loops, loopReach := loopReach,
    banks := (List.range nv).foldl (fun b x => b.insert x (bankOf I (tys.getD x i64))) .empty,
    flagHome := fh.flagHome, bparams := bparamsTrie, lTrie := lTrie, addrDeps := addrDeps,
    rmwDeps := rmwDeps, isLeaf := isLeaf, cfg := cfg, csCost := csCost,
    r0? := I.frame.allocatable.head? }
  let regionReused := (buildRegionReused c t .empty).2
  let initZ32 : Trie Bool := fnPs.foldl (fun z (p, ty) =>
    if isGprTy I ty then z.insert p true else z) .empty
  let directVars : Tree → List Nat :=
    let rec go : Tree → List Nat
      | .let_ _ ip nv0 ts op k =>
        (List.range ts.length).map (nv0 + ·) ++ addrDeps.getD ip (opVarIds op) ++ go k
      | .load _ ip x _ a k => x :: addrDeps.getD ip (argVarIds a) ++ go k
      | .store _ ip _ v a k => storeVarIds addrDeps rmwDeps ip v a ++ go k
      | .call _ _ nv0 _ _ bs args k =>
        (List.range bs.length).map (nv0 + ·) ++ tupVarIds args ++ go k
      | .jnz _ _ cx _ t e => cx :: go t ++ go e
      | .skip _ _ k | .group _ _ k => go k
      | .jump _ _ _ _ args => tupVarIds args
      | .ret _ _ _ vs | .exit _ _ _ _ vs => tupVarIds vs
      | .stop _ => []
    go
  let rec jmpEdges (src : Nat) (w : Nat) : Tree → List (Nat × Nat × Nat × List Nat)
    | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k
    | .call _ _ _ _ _ _ _ k | .skip _ _ k | .group _ _ k => jmpEdges src w k
    | .jnz _ ip _ _ t e =>
      let (_, mT, mE) := c.brW.getD ip (w, w, w)
      jmpEdges src mT t ++ jmpEdges src mE e
    | .jump _ _ j _ args => [(src, j, w, tupVarIds args)]
    | _ => []
  let acc := gather c [] [] baseMult initZ32 t {}
  let rootId := t.blocks.foldl (fun m (l, _, _) => max m (l + 1)) 0
  let blkUses := t.blocks.foldl (fun m (l, _, body) => m.insert l (directVars body))
    (Trie.empty.insert rootId (directVars t))
  let rootVars := union t.lv (blkUses.getD rootId [])
  let varBlks0 := rootVars.foldl (fun m v => triePush m v rootId) .empty
  let varBlks := t.blocks.foldl (fun m (l, ps, _) =>
    let vs := union (lTrie.getD l []) (union (ps.map Prod.fst) (blkUses.getD l []))
    vs.foldl (fun m v => triePush m v l) m) varBlks0
  let c := { c with
    brW := acc.brW, zextElide := acc.zextElide, regionReused := regionReused,
    jmpW := acc.jmpW, inW := acc.inW, blkUses := blkUses, varBlks := varBlks }
  let blkEdges := t.blocks.foldl (fun es (l, _, body) =>
    es ++ jmpEdges l (c.inW.getD l 0) body) (jmpEdges rootId baseMult t)
  let c := { c with blkEdges := blkEdges }
  let fnAbi := match I.assignArgs f.as with
    | some locs => abiIdList allGpr allVec locs | none => []
  let cs := colorVars c nv fh.flagHome acc (fnPs.map Prod.fst) fnAbi
  let c := { c with hintT := cs.hint, forceEv := cs.forceEv, evIn := cs.forceEv }
  let slotOk := slotPlocMap c cs.hT cs.bk cs.usedCs acc.defWT t
  let r0? := I.frame.allocatable.head?
  let r1? := I.frame.allocatable[1]?
  let initSv := (fnPs.map Prod.fst).filter (isEagerBk cs.bk)
  let emit (c : Ctx I) : EmitSt I := emitAlloc c cs.hT cs.bk slotOk fh.clearAt r0? r1? t
    (pendFromArrivals cs.hT cs.bk (fnPs.map Prod.fst) fnAbi) [] initSv [] []
    { variant := fh.variant, usedCs := cs.usedCs }
  let c := { c with jmpW := acc.jmpW, inW := acc.inW }
  let refine (c : Ctx I) : Ctx I :=
    let stO := emit { c with opt := true }
    let rin := pickRegIn c cs.hT cs.usedCs slotOk stO.cin t.blocks
    let evi := pickEvIn c cs.hT stO.evArr c.evIn t.blocks
    { c with regIn := rin, evIn := evi }
  let c := if cfg.regEntry && cfg.sink then refine (refine c) else c
  let st := emit c
  let finalSlots :=
    if I.frame.scratch.isEmpty then cs.nslots else min cs.nslots (usedSlotCount nip nl st)
  { dest := st.dest, entry := st.entry, pre := st.pre, variant := st.variant, elide := elideIps,
    nslots := finalSlots, saved := st.usedCs.map fun r => c.gReg.getD r I.frame.sp }

end Spill
end LeanQbe.T
