module

public import LeanQbe.T.Live
public import LeanQbe.T.SpillFlags
public import LeanQbe.T.SpillEmit
public import LeanQbe.T.SpillCoalesce

/-!
# Priority Graph-Coloring Register Allocator & Spilling Oracle (untrusted)

Priority graph-coloring register allocator over typed banks (`GPR` + `Vec` + local
flag hints): scoped loop-depth & branch-discounted weights, exact dual reload/def pressure points
with callee-saved/flag credit, identity self-jump filtering, dying-operand 2-address + block-edge
coalescing with parallel-move conflict avoidance, per-call live-range splitting (lazy for cold
calls inside or outside loops, eager-backed for loop-crossing invariants), straight-line dead
spill-store elision and spilled-operand register caching, slot-direct block parameters,
`VariantHint.disp` (`lea`) probing, and GPR/Vec parallel-move cycle breaking.

`Spill.Cfg` adds five spill-placement refinements: slot-home stores are deferred past
straight-line code and sunk into `jnz` arms (`sink`), hot join parameters stay out of
slot-direct `Entry.ploc` (`joinGuard`), a spilled variable keeps a soft cache register that
later-colored interfering variables avoid (`cacheHint`), a block may take a spilled live-in
in the register its predecessors hold it in (`regEntry`), and a variable that would be spilled
may instead keep a register outside some `jnz` arms or loops where it is unused, being evicted
to a backup slot on entry and reloaded at their exits (`armEvict`, with `armLoops` for loop
regions and, off by default, `armX` for call-crossing variables).

A spilled operand of a compare / ALU op is read from its slot directly (`Rega.trySlotOp`)
unless it is reused later in the same straight-line region; values that are merely live into a
jump target do not count as reused.

Untrusted: `Rega.lowerFn` checks every hint, so any heuristic bug can only fail lowering.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Spill

open Live Rega SpillFlags

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
  let rev : Std.HashMap Nat (List Nat) := bs.foldl (fun r (l, _, tb) =>
    (allJumps tb).foldl (fun r dst => r.insert dst (l :: r.getD dst [])) r) {}
  let maxFuel := bs.length * bs.length + bs.length + 1
  let revReach (target gMin : Nat) : List Nat × Std.HashSet Nat :=
    let rec dfs : Nat → List Nat → Std.HashSet Nat → List Nat → List Nat × Std.HashSet Nat
      | 0, _, vis, acc | _, [], vis, acc => (acc, vis)
      | fuel + 1, x :: xs, vis, acc =>
        if !Nat.ble gMin x || vis.contains x then dfs fuel xs vis acc
        else dfs fuel (rev.getD x [] ++ xs) (vis.insert x) (x :: acc)
    dfs maxFuel (rev.getD target []) {} []
  bs.foldl (fun (lps, rch) (l, gMin, _) =>
    let (reach, vis) := revReach l gMin
    if vis.contains l then (lps.insert l true, rch.insert l reach) else (lps, rch))
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

/-- Gathered weights; `gprPts` records `(budget, liveThrough, creditVars)` where coloring any
`u ∈ creditVars` with a callee-saved register credits `+1` back to that point's caller-saved
budget; `callW` records `(mult, vars live across a call)`; `loopCall` marks vars crossing a call
inside a loop; `defWT` records each var's definition weight; `isBP` marks block parameters;
`brW` records `(mult, multThen, multElse)` of every `jnz`. -/
structure GatherAcc where
  (weights defInterf callW : List (Nat × List Nat) := [])
  (gprPts : List (Nat × List Nat × List Nat) := [])
  (gprPtBlks : List (Option Nat) := [])
  (gprPtIps : List Nat := [])
  (vecPts : List (Nat × List Nat) := [])
  (abiGpr abiVec affEdges antiEdges : List (Nat × Nat × Nat) := [])
  (loopCall : Trie Bool := .empty)
  (defWT : Trie Nat := .empty)
  (isBP : Trie Bool := .empty)
  (brW : Trie (Nat × Nat × Nat) := .empty)
  (jmpW inW : Trie Nat := .empty)
  (zextElide : Trie Nat := .empty)
  (zextEdges : List (Nat × Nat) := [])
  (invertJnz : Trie Bool := .empty)
  (ipW : Trie Nat := .empty)

def addWeight (mult : Nat) (uses : List Nat) (ws : List (Nat × List Nat)) :
    List (Nat × List Nat) :=
  if uses.isEmpty then ws else (mult, uses) :: ws

/-- GPR pressure point: at most `nGpr - |creditVars|` of `vars` (`live \ creditVars`) may sit in
caller-saved registers initially; each var in `creditVars` assigned a CS register credits `+1` back
to this budget, guaranteeing `|non-CS creditVars|` free caller-saved registers for reload/def. -/
def addGprPtBlk (blk? : Option Nat) (ip : Nat) (allocLen : Nat) (creditVars vars : List Nat)
    (pts : List (Nat × List Nat × List Nat)) (blks : List (Option Nat)) (ips : List Nat) :
    List (Nat × List Nat × List Nat) × List (Option Nat) × List Nat :=
  let need := creditVars.length
  let b := allocLen - need
  if Nat.ble 1 need && Nat.ble (b + 1) vars.length then
    ((b, vars, creditVars) :: pts, blk? :: blks, ip :: ips)
  else (pts, blks, ips)

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

def mapRematVars (rematRoot : Trie Nat) (xs : List Nat) : List Nat :=
  dedup (xs.map fun x => rematRoot.getD x x)

/-- Precomputed per-`jnz` branch properties (`hasLoop`, `hasCall`, jump targets) for O(1) lookup
in `gatherAt`, avoiding repeated O(N) subtree traversals on nested branches. -/
structure JnzInfo where
  hasLoopT : Bool
  hasLoopE : Bool
  hasCallT : Bool
  hasCallE : Bool
  jumpsT : List Nat
  jumpsE : List Nat

mutual
def preScanJnz (loops : Trie Bool) :
    Tree → Std.HashMap Nat JnzInfo → Bool × Bool × List Nat × Std.HashMap Nat JnzInfo
  | .let_ _ _ _ _ _ k, m | .load _ _ _ _ _ k, m | .store _ _ _ _ _ k, m | .skip _ _ k, m =>
    preScanJnz loops k m
  | .call _ _ _ _ _ _ _ k, m =>
    let (hl, _, js, m1) := preScanJnz loops k m
    (hl, true, js, m1)
  | .jnz _ ip _ _ t e, m =>
    let (hlT, hcT, jT, m1) := preScanJnz loops t m
    let (hlE, hcE, jE, m2) := preScanJnz loops e m1
    let m3 := m2.insert ip ⟨hlT, hlE, hcT, hcE, jT, jE⟩
    (hlT || hlE, hcT || hcE, union jT jE, m3)
  | .group _ bs k, m =>
    let (hlB, hcB, jB, m1) := preScanJnzB loops bs m
    let (hlK, hcK, jK, m2) := preScanJnz loops k m1
    (hlB || hlK, hcB || hcK, union jB jK, m2)
  | .jump _ _ j _ _, m => (false, false, [j], m)
  | .ret .., m | .exit .., m | .stop _, m => (false, false, [], m)

def preScanJnzB (loops : Trie Bool) :
    TreeBlocks → Std.HashMap Nat JnzInfo → Bool × Bool × List Nat × Std.HashMap Nat JnzInfo
  | .nil, m => (false, false, [], m)
  | .cons l _ b bs, m =>
    let (hlB, hcB, jB, m1) := preScanJnz loops b m
    let (hlBs, hcBs, jBs, m2) := preScanJnzB loops bs m1
    (loops.getD l false || hlB || hlBs, hcB || hcBs, union jB jBs, m2)
end

def splitBankArr {C : Type} (banks : Trie Bank) (flagHome : Trie C)
    (banksArr : Array Bank) (flagArr : Array Bool) (vs : List Nat) :
    List Nat × List Nat :=
  vs.foldl (fun (gs, vcs) x =>
    let isFl := if h : x < flagArr.size then flagArr[x] else (flagHome.find? x).isSome
    if isFl then (gs, vcs)
    else
      let bk := if h : x < banksArr.size then banksArr[x] else banks.getD x .gpr
      if bk.isVec then (gs, x :: vcs)
      else (x :: gs, vcs)) ([], [])

def defVarsRange (nv0 n : Nat) : List Nat :=
  match n with
  | 0 => []
  | 1 => [nv0]
  | _ => (List.range n).map (nv0 + ·)

mutual
def gatherAtFast {I : Isa} (c : Ctx I) (banksArr : Array Bank) (flagArr : Array Bool)
    (jnzMap : Std.HashMap Nat JnzInfo) (blk? : Option Nat)
    (rematRoot : Trie Nat := .empty) (rematOpIps : Trie Bool := .empty) :
    List Nat → Std.HashSet Nat → List Nat → Std.HashSet Nat → Nat → Trie Bool →
    Tree → GatherAcc → GatherAcc
  | lps, lpsS, lr, lrS, mult, isZ32, .let_ lv ip nv0 ts op k, acc =>
    let la := k.lv
    let defs := defVarsRange nv0 ts.length
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
    let isRemOp := rematOpIps.getD ip false
    let di := defs.foldl (fun d x =>
      if isRemOp then (x, union defs (union (laFor x) uses)) :: d
      else if natMem x la || Nat.ble 2 defs.length then (x, union defs (laFor x)) :: d else d)
      acc.defInterf
    let (gLv, vLv) := splitBankArr c.banks c.flagHome banksArr flagArr lv
    let (gLa, vLa) := splitBankArr c.banks c.flagHome banksArr flagArr la
    let (gUse, vUse) := splitBankArr c.banks c.flagHome banksArr flagArr uses
    let (gDef, vDef) := splitBankArr c.banks c.flagHome banksArr flagArr defs
    let (gPts1, gBlks1, gIps1) := addGprPtBlk blk? ip c.nGpr gUse (eraseMany gUse gLv)
      acc.gprPts acc.gprPtBlks acc.gprPtIps
    let (gPts, gBlks, gIps) :=
      addGprPtBlk blk? ip c.nGpr gDef (eraseMany gDef gLa) gPts1 gBlks1 gIps1
    let vPts := addVecPt c.nVec vDef.length (eraseMany vDef vLa)
      (addVecPt c.nVec vUse.length (eraseMany vUse vLv) acc.vecPts)
    let dw := defs.foldl (fun t x => t.insert x mult) acc.defWT
    let (ze, zed) := match zextSrc? with
      | some zx => (acc.zextElide.insert ip zx, (nv0, zx) :: acc.zextEdges)
      | none => (acc.zextElide, acc.zextEdges)
    let isZ32' :=
      if opProducesZ32Static I c.r0? op then isZ32.insert nv0 true else isZ32
    gatherAtFast c banksArr flagArr jnzMap blk? rematRoot rematOpIps lps lpsS lr lrS mult isZ32' k
      { acc with
        ipW := acc.ipW.insert ip mult,
        weights := (mult, defs ++ uses) :: acc.weights, defInterf := di, affEdges := aff,
        gprPts := gPts, gprPtBlks := gBlks, gprPtIps := gIps, vecPts := vPts, defWT := dw,
        zextElide := ze, zextEdges := zed }
  | lps, lpsS, lr, lrS, mult, isZ32, .load lv ip x t a k, acc =>
    let la := k.lv
    let uses := dedup (c.addrDeps.getD ip (argVarIds a))
    let di := if natMem x la then (x, la) :: acc.defInterf else acc.defInterf
    let (gLv, _) := splitBankArr c.banks c.flagHome banksArr flagArr lv
    let (gLa, vLa) := splitBankArr c.banks c.flagHome banksArr flagArr la
    let (gUse, _) := splitBankArr c.banks c.flagHome banksArr flagArr uses
    let (gDef, vDef) := splitBankArr c.banks c.flagHome banksArr flagArr [x]
    let (gPts1, gBlks1, gIps1) := addGprPtBlk blk? ip c.nGpr gUse (eraseMany gUse gLv)
      acc.gprPts acc.gprPtBlks acc.gprPtIps
    let (gPts, gBlks, gIps) :=
      addGprPtBlk blk? ip c.nGpr gDef (eraseMany gDef gLa) gPts1 gBlks1 gIps1
    let vPts := addVecPt c.nVec vDef.length (eraseMany vDef vLa) acc.vecPts
    let isZ32' :=
      if (I.gpr.zeroExtLoad && isGprTy I t) || (I.gpr.zeroUpper32Load && tyEq t (.bits 32)) then
        isZ32.insert x true
      else isZ32
    gatherAtFast c banksArr flagArr jnzMap blk? rematRoot rematOpIps lps lpsS lr lrS mult isZ32' k
      { acc with
        ipW := acc.ipW.insert ip mult,
        weights := (mult, x :: uses) :: acc.weights, defInterf := di,
        gprPts := gPts, gprPtBlks := gBlks, gprPtIps := gIps, vecPts := vPts,
        defWT := acc.defWT.insert x mult }
  | lps, lpsS, lr, lrS, mult, isZ32, .store lv ip _ v a k, acc =>
    let uses := storeVarIds c.addrDeps c.rmwDeps ip v a
    let (gLv, vLv) := splitBankArr c.banks c.flagHome banksArr flagArr lv
    let (gUse, vUse) := splitBankArr c.banks c.flagHome banksArr flagArr uses
    let (gPts, gBlks, gIps) := addGprPtBlk blk? ip c.nGpr gUse (eraseMany gUse gLv)
      acc.gprPts acc.gprPtBlks acc.gprPtIps
    gatherAtFast c banksArr flagArr jnzMap blk? rematRoot rematOpIps lps lpsS lr lrS mult isZ32 k
      { acc with
        ipW := acc.ipW.insert ip mult,
        weights := addWeight mult uses acc.weights, gprPts := gPts, gprPtBlks := gBlks,
        gprPtIps := gIps,
        vecPts := addVecPt c.nVec vUse.length (eraseMany vUse vLv) acc.vecPts }
  | lps, lpsS, lr, lrS, mult, isZ32, .call _ ip nv0 _ as bs args k, acc =>
    let defs := defVarsRange nv0 bs.length
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
    gatherAtFast c banksArr flagArr jnzMap blk? rematRoot rematOpIps lps lpsS lr lrS mult isZ32' k
      { acc with
        ipW := acc.ipW.insert ip mult,
        weights := addWeight mult (defs ++ mapRematVars rematRoot (tupVarIds args)) acc.weights,
        defInterf := di, abiGpr := ag2, abiVec := av2,
        callW := addWeight mult across acc.callW, loopCall := lc, defWT := dw }
  | lps, lpsS, lr, lrS, mult, isZ32, .jnz lv ip cx _ t e, acc =>
    let (gLv, _) := splitBankArr c.banks c.flagHome banksArr flagArr lv
    let (gUse, _) := splitBankArr c.banks c.flagHome banksArr flagArr [cx]
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
    let info := jnzMap.getD ip ⟨false, false, false, false, [], []⟩
    let (mT, mE) :=
      if inLoop then
        let stT := info.jumpsT.any (lpsS.contains ·)
        let stE := info.jumpsE.any (lpsS.contains ·)
        if stT && !stE then (keepM, exitM)
        else if stE && !stT then (exitM, keepM)
        else
          let rT := info.jumpsT.any (lrS.contains ·)
          let rE := info.jumpsE.any (lrS.contains ·)
          if rT && !rE then (keepM, exitM)
          else if rE && !rT then (exitM, keepM)
          else if tt && !te then (guardM, contM)
          else if te && !tt then (contM, guardM)
          else (halfM, remHalf)
      else
        let lt := info.hasLoopT; let le := info.hasLoopE
        let ct := info.hasCallT; let ce := info.hasCallE
        if lt && !le then (if te then (contM, guardM) else (mainM, asymM))
        else if le && !lt then (if tt then (guardM, contM) else (asymM, mainM))
        else if ct && !ce then (if te then (contM, guardM) else (asymM, mainM))
        else if ce && !ct then (if tt then (guardM, contM) else (mainM, asymM))
        else if tt && !te then (guardM, contM)
        else if te && !tt then (contM, guardM)
        else (halfM, remHalf)
    let (gPts, gBlks, gIps) := addGprPtBlk blk? ip c.nGpr gUse (eraseMany gUse gLv)
      acc.gprPts acc.gprPtBlks acc.gprPtIps
    let acc1 := gatherAtFast c banksArr flagArr jnzMap blk? rematRoot rematOpIps
      lps lpsS lr lrS mE isZ32 e
      { acc with
        weights := (mult, [cx]) :: acc.weights, gprPts := gPts, gprPtBlks := gBlks,
        gprPtIps := gIps, brW := acc.brW.insert ip (mult, mT, mE),
        invertJnz := if Nat.blt mE mT then acc.invertJnz.insert ip true else acc.invertJnz }
    gatherAtFast c banksArr flagArr jnzMap blk? rematRoot rematOpIps
      lps lpsS lr lrS mT isZ32 t acc1
  | lps, lpsS, lr, lrS, mult, isZ32, .skip _ _ k, acc =>
    gatherAtFast c banksArr flagArr jnzMap blk? rematRoot rematOpIps
      lps lpsS lr lrS mult isZ32 k acc
  | lps, lpsS, _, _, mult, _, .jump _ ip j _ args, acc =>
    let acc := { acc with
      jmpW := acc.jmpW.insert ip mult, inW := acc.inW.insert j (acc.inW.getD j 0 + mult) }
    let as := tupArgsToList args
    let ps := c.bparams.getD j []
    let nonSelf := if ps.isEmpty then mapRematVars rematRoot (tupVarIds args) else
      dedup ((as.zip ps).foldl (fun a (ao, p) =>
        match ao with
        | some x =>
          let x' := rematRoot.getD x x
          if Nat.beq x' p then a else x' :: p :: a
        | none => p :: a) [])
    let (aff', anti') :=
      if c.cfg.backEdgeCoal then
        addJumpAffAnti (lpsS.contains j) lps.length as ps mult acc.affEdges acc.antiEdges
      else
        (addAffZip as ps (8 * mult) acc.affEdges, addAntiZip as ps (2 * mult) acc.antiEdges)
    { acc with weights := addWeight mult nonSelf acc.weights,
               affEdges := aff', antiEdges := anti' }
  | _, _, _, _, mult, _, .ret _ ip rs vs, acc =>
    let (ag, av) := match I.assignRets rs with
      | some locs =>
        addAbiArgs (tupArgsToList vs) (abiIdList c.allGpr c.allVec locs) (4 * mult)
          acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    { acc with weights := addWeight mult (mapRematVars rematRoot (tupVarIds vs)) acc.weights,
               abiGpr := ag, abiVec := av, ipW := acc.ipW.insert ip mult }
  | _, _, _, _, mult, _, .exit _ ip _ as args, acc =>
    let (ag, av) := match I.assignArgs as with
      | some locs =>
        addAbiArgs (tupArgsToList args) (abiIdList c.allGpr c.allVec locs) (4 * mult)
          acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    { acc with weights := addWeight mult (mapRematVars rematRoot (tupVarIds args)) acc.weights,
               abiGpr := ag, abiVec := av, ipW := acc.ipW.insert ip mult }
  | _, _, _, _, _, _, .stop _, acc => acc
  | lps, lpsS, lr, lrS, mult, isZ32, .group _ bs k, acc =>
    gatherAtFastB c banksArr flagArr jnzMap rematRoot rematOpIps lps lpsS lr lrS mult bs
      (gatherAtFast c banksArr flagArr jnzMap blk? rematRoot rematOpIps
        lps lpsS lr lrS mult isZ32 k acc)

def gatherAtFastB {I : Isa} (c : Ctx I) (banksArr : Array Bank) (flagArr : Array Bool)
    (jnzMap : Std.HashMap Nat JnzInfo) (rematRoot : Trie Nat := .empty)
    (rematOpIps : Trie Bool := .empty) :
    List Nat → Std.HashSet Nat → List Nat → Std.HashSet Nat → Nat →
    TreeBlocks → GatherAcc → GatherAcc
  | _, _, _, _, _, .nil, acc => acc
  | lps, lpsS, lr, lrS, mult, .cons l ps b bs, acc =>
    let pvars := ps.map Prod.fst
    let le := b.lv
    let di := pvars.foldl (fun d p =>
      if natMem p le then (p, union pvars le) :: d else d) acc.defInterf
    let isLoop := c.loops.getD l false
    let blkLps := if c.cfg.backEdgeCoal then c.blkLoops.getD l [] else []
    let lps' := union blkLps (if isLoop then l :: lps else lps)
    let extraDepth := lps'.length - lps.length
    let pow10 : Nat → Nat
      | 0 => 1 | 1 => 10 | 2 => 100 | 3 => 1000 | _ => 10000
    let mB :=
      if Nat.ble 1 extraDepth then
        let f := pow10 extraDepth
        let scaled := if lps.isEmpty then max (f * mult) (f * baseMult) else f * max mult 1
        min scaled 160000
      else mult
    let lr' := lps'.foldl (fun a lh => union (c.loopReach.getD lh []) a) lr
    let lpsS' := if Nat.ble 1 extraDepth then hashSetOfList lps' else lpsS
    let lrS' := if Nat.ble 1 extraDepth || !lps'.isEmpty then hashSetOfList lr' else lrS
    let dw := pvars.foldl (fun t p => t.insert p mB) acc.defWT
    let bp := pvars.foldl (fun t p => t.insert p true) acc.isBP
    let pW := if !lps'.isEmpty then max (baseMult / 4) (mB / 4) else baseMult / 4
    gatherAtFastB c banksArr flagArr jnzMap rematRoot rematOpIps lps lpsS lr lrS mult bs
      (gatherAtFast c banksArr flagArr jnzMap (some l) rematRoot rematOpIps
        lps' lpsS' lr' lrS' mB .empty b
        { acc with weights := addWeight pW pvars acc.weights,
                   defInterf := di, defWT := dw, isBP := bp })
end

def gather {I : Isa} (c : Ctx I) (lps lr : List Nat) (mult : Nat) (isZ32 : Trie Bool)
    (t : Tree) (acc : GatherAcc) (rematRoot : Trie Nat := .empty)
    (rematOpIps : Trie Bool := .empty) (banksArr : Array Bank := #[])
    (flagArr : Array Bool := #[]) : GatherAcc :=
  let jnzMap := (preScanJnz c.loops t {}).2.2.2
  let bArr := if banksArr.isEmpty then #[] else banksArr
  let fArr := if flagArr.isEmpty then #[] else flagArr
  gatherAtFast c bArr fArr jnzMap none rematRoot rematOpIps
    lps (hashSetOfList lps) lr (hashSetOfList lr) mult isZ32 t acc

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
  armEv : Trie (List Nat) := .empty

/-! ## Arm-Scoped Eviction (`Cfg.armEvict`)

A variable `x` that would otherwise be spilled may take a register that is only held, inside
some `jnz` arms where `x` is live but unused, by variables whose whole live range lies inside
those arms. On entry to such an arm `x` is evicted to a backup slot (stored at its definition
when that is cheaper, `eager`, else at the arm entry) and it is reloaded at the arm's exits. -/

def firstIp : Tree → Nat
  | .let_ _ ip _ _ _ _ | .load _ ip _ _ _ _ | .store _ ip _ _ _ _ | .call _ ip _ _ _ _ _ _
  | .jnz _ ip _ _ _ _ | .skip _ ip _ | .jump _ ip _ _ _ | .ret _ ip _ _ | .exit _ ip _ _ _
  | .stop ip => ip
  | .group _ _ k => firstIp k

mutual
/-- `(max ip, labels declared, jumps (ip, target, args))` of a subtree. -/
def subInfo : Tree → Nat × List Nat × List (Nat × Nat × List Nat)
  | .let_ _ ip _ _ _ k | .load _ ip _ _ _ k | .store _ ip _ _ _ k
  | .call _ ip _ _ _ _ _ k | .skip _ ip k =>
    let (m, ls, js) := subInfo k
    (max ip m, ls, js)
  | .jnz _ ip _ _ t e =>
    let (m1, l1, j1) := subInfo t
    let (m2, l2, j2) := subInfo e
    (max ip (max m1 m2), l1 ++ l2, j1 ++ j2)
  | .group _ bs k =>
    let (m1, l1, j1) := subInfo k
    let (m2, l2, j2) := subInfoB bs
    (max m1 m2, l1 ++ l2, j1 ++ j2)
  | .jump _ ip j _ args => (ip, [], [(ip, j, tupVarIds args)])
  | .ret _ ip _ _ | .exit _ ip _ _ _ | .stop ip => (ip, [], [])

def subInfoB : TreeBlocks → Nat × List Nat × List (Nat × Nat × List Nat)
  | .nil => (0, [], [])
  | .cons l _ b bs =>
    let (m1, l1, j1) := subInfo b
    let (m2, l2, j2) := subInfoB bs
    (max m1 m2, l :: (l1 ++ l2), j1 ++ j2)
end

/-- Region key of block `l` (disjoint from the `jnz` arm keys `2 * ip + {0, 1}`). -/
def blockArmKey (l : Nat) : Nat := 2 ^ 40 + l

mutual
/-- Single-pass bottom-up arm collection returning `(maxIp, labels, jumps, arms)` in exact
`collectArms` order without re-scanning nested subtrees. -/
def collectArmsGo {I : Isa} (c : Ctx I) :
    Tree → Nat × List Nat × List (Nat × Nat × List Nat) × List ArmInfo
  | .let_ _ ip _ _ _ k | .load _ ip _ _ _ k | .store _ ip _ _ _ k
  | .call _ ip _ _ _ _ _ k | .skip _ ip k =>
    let (m, ls, js, arms) := collectArmsGo c k
    (max ip m, ls, js, arms)
  | .jnz _ ip _ _ t e =>
    let (mT, lT, jT, armsT) := collectArmsGo c t
    let (mE, lE, jE, armsE) := collectArmsGo c e
    let (_, wT, wE) := c.brW.getD ip (0, 0, 0)
    let mk (key w m : Nat) (ls : List Nat) (js : List (Nat × Nat × List Nat)) (a : Tree) :
        List ArmInfo :=
      if isTrivialTerm a then []
      else
        let exits :=
          if ls.isEmpty then js.map fun (jip, j, args) => (jip, j, c.jmpW.getD jip 0, args)
          else
            let lsSet := hashSetOfList ls
            js.filterMap fun (jip, j, args) =>
              if lsSet.contains j then none else some (jip, j, c.jmpW.getD jip 0, args)
        [{ key, lo := firstIp a, hi := m + 1, w, liveIn := a.lv, exits, blocks := ls }]
    let mkT := mk (2 * ip + 1) wT mT lT jT t
    let mkE := mk (2 * ip) wE mE lE jE e
    (max ip (max mT mE), lT ++ lE, jT ++ jE, armsT ++ armsE ++ mkT ++ mkE)
  | .group _ bs k =>
    let (mK, lK, jK, armsK) := collectArmsGo c k
    let (mB, lB, jB, armsB) := collectArmsGoB c bs
    (max mK mB, lK ++ lB, jK ++ jB, armsB ++ armsK)
  | .jump _ ip j _ args => (ip, [], [(ip, j, tupVarIds args)], [])
  | .ret _ ip _ _ | .exit _ ip _ _ _ | .stop ip => (ip, [], [], [])

def collectArmsGoB {I : Isa} (c : Ctx I) :
    TreeBlocks → Nat × List Nat × List (Nat × Nat × List Nat) × List ArmInfo
  | .nil => (0, [], [], [])
  | .cons l _ b bs =>
    let (mB, lB, jB, armsB) := collectArmsGo c b
    let (mBs, lBs, jBs, armsBs) := collectArmsGoB c bs
    let blk : List ArmInfo :=
      if !c.cfg.armLoops || isTrivialTerm b || !c.loops.getD l false then []
      else
        let inside := l :: lB
        let insideSet := hashSetOfList inside
        let exits := jB.filterMap fun (jip, j, args) =>
          if insideSet.contains j then none else some (jip, j, c.jmpW.getD jip 0, args)
        let backW := jB.foldl (fun n (jip, j, _) =>
          if Nat.beq j l then n + c.jmpW.getD jip 0 else n) 0
        [{ key := blockArmKey l, lo := firstIp b, hi := mB + 1, w := c.inW.getD l 0 - backW,
           liveIn := c.lTrie.getD l [], exits, blocks := inside }]
    (max mB mBs, l :: (lB ++ lBs), jB ++ jBs, armsBs ++ armsB ++ blk)
end

/-- All non-trivial `jnz` arms and blocks of a tree (see `ArmInfo`). -/
def collectArms {I : Isa} (c : Ctx I) (t : Tree) (acc : List ArmInfo) : List ArmInfo :=
  (collectArmsGo c t).2.2.2 ++ acc

def extendExtArr (e : Array (Option (Nat × Nat))) (x ip : Nat) :
    Array (Option (Nat × Nat)) :=
  if h : x < e.size then
    match e[x] with
    | some (lo, hi) => e.set x (some (min lo ip, max hi ip))
    | none => e.set x (some (ip, ip))
  else e

def scanNodeArr (ip : Nat) (lv defs uses : List Nat)
    (acc : Array (Option (Nat × Nat)) × Array (List Nat)) :
    Array (Option (Nat × Nat)) × Array (List Nat) :=
  let e1 := lv.foldl (fun e x => extendExtArr e x ip) acc.1
  let e2 := defs.foldl (fun e x => extendExtArr e x ip) e1
  let e3 := uses.foldl (fun e x => extendExtArr e x ip) e2
  let u1 := uses.foldl (fun u x =>
    if h : x < u.size then u.set x (ip :: u[x]) else u) acc.2
  (e3, u1)

mutual
/-- Array-backed variable extent and use-ip scan (O(1) per update, zero `Trie` allocation). -/
def varScanArr {I : Isa} (c : Ctx I) :
    Tree → Array (Option (Nat × Nat)) × Array (List Nat) →
    Array (Option (Nat × Nat)) × Array (List Nat)
  | .let_ lv ip nv0 ts op k, acc =>
    varScanArr c k (scanNodeArr ip lv (defVarsRange nv0 ts.length)
      (c.addrDeps.getD ip (opVarIds op)) acc)
  | .load lv ip x _ a k, acc =>
    varScanArr c k (scanNodeArr ip lv [x] (c.addrDeps.getD ip (argVarIds a)) acc)
  | .store lv ip _ v a k, acc =>
    varScanArr c k (scanNodeArr ip lv [] (storeVarIds c.addrDeps c.rmwDeps ip v a) acc)
  | .call lv ip nv0 _ _ bs args k, acc =>
    varScanArr c k (scanNodeArr ip lv (defVarsRange nv0 bs.length) (tupVarIds args) acc)
  | .jnz lv ip cx _ t e, acc => varScanArr c t (varScanArr c e (scanNodeArr ip lv [] [cx] acc))
  | .skip lv ip k, acc => varScanArr c k (scanNodeArr ip lv [] [] acc)
  | .jump lv ip _ _ args, acc => scanNodeArr ip lv [] (tupVarIds args) acc
  | .ret lv ip _ vs, acc => scanNodeArr ip lv [] (tupVarIds vs) acc
  | .exit lv ip _ _ args, acc => scanNodeArr ip lv [] (tupVarIds args) acc
  | .stop _, acc => acc
  | .group _ bs k, acc => varScanArrB c bs (varScanArr c k acc)

def varScanArrB {I : Isa} (c : Ctx I) :
    TreeBlocks → Array (Option (Nat × Nat)) × Array (List Nat) →
    Array (Option (Nat × Nat)) × Array (List Nat)
  | .nil, acc => acc
  | .cons _ ps b bs, acc =>
    let fi := firstIp b
    varScanArrB c bs (varScanArr c b
      (ps.foldl (fun a (p, _) => (extendExtArr a.1 p fi, a.2)) acc))
end

def isCmpBitsCode {sig ts : List Ty} : OpCode sig ts → Bool
  | .cmp _ (.bits _) .bool _ => true
  | _ => false

mutual
def foldIpsSetT : Tree → Std.HashSet Nat → Std.HashSet Nat
  | .let_ _ ip _ _ op k, acc => foldIpsSetT k (if isCmpBitsCode op.code then acc.insert ip else acc)
  | .load _ _ _ _ _ k, acc | .store _ _ _ _ _ k, acc | .call _ _ _ _ _ _ _ k, acc
  | .skip _ _ k, acc => foldIpsSetT k acc
  | .jnz _ ip _ _ t e, acc => foldIpsSetT t (foldIpsSetT e (acc.insert ip))
  | .group _ bs k, acc => foldIpsSetTB bs (foldIpsSetT k acc)
  | .jump .., acc | .ret .., acc | .exit .., acc | .stop _, acc => acc

def foldIpsSetTB : TreeBlocks → Std.HashSet Nat → Std.HashSet Nat
  | .nil, acc => acc
  | .cons _ _ b bs, acc => foldIpsSetTB bs (foldIpsSetT b acc)
end

/-- Pre-indexed arrays and hash maps shared across `colorVars` / eviction / recoloring passes,
eliminating per-variable `Trie` walks and `O(E + Arms)` linear scans. -/
structure ColorPre (I : Isa) where
  nv : Nat
  numG : Nat
  numV : Nat
  banksArr : Array Bank
  crossArr : Array Bool
  isBPArr : Array Bool
  cwArr : Array Nat
  defWArr : Array Nat
  interfDedup : Array (List Nat)
  interfMult : Array (List (Nat × Nat))
  gVpArr : Array (List Nat)
  gCpArr : Array (List Nat)
  vVpArr : Array (List Nat)
  abiGArr : Array (List (Nat × Nat))
  abiVArr : Array (List (Nat × Nat))
  affArr : Array (List (Nat × Nat))
  antiArr : Array (List (Nat × Nat))
  zextArr : Array (List Nat)
  fnParamSet : Std.HashSet Nat
  ptBlks : Array (Option Nat)
  ptIps : Array Nat
  armMap : Std.HashMap Nat ArmInfo
  armsByVar : Array (List ArmInfo)
  armExitArgs : Std.HashMap Nat (Std.HashSet Nat)
  varExtArr : Array (Option (Nat × Nat))
  useIpsArr : Array (List Nat)
  foldIpsSet : Std.HashSet Nat
  lTrieSets : Std.HashMap Nat (Std.HashSet Nat)
  blkUsesSets : Std.HashMap Nat (Std.HashSet Nat)
  bparamsSets : Std.HashMap Nat (Std.HashSet Nat)
  edgesBySrc : Std.HashMap Nat (List (Nat × Nat × Nat × List Nat))
  edgesByDst : Std.HashMap Nat (List (Nat × Nat × Nat × List Nat))
  varBlksArr : Array (List Nat)

/-- Array-backed mutable-style coloring state converted back to `ColorSt` once at the end. -/
structure ColorStArr (C : Type) where
  hArr : Array (Home C)
  usedCs : List Nat := []
  nslots : Nat := 0
  gPbArr : Array Nat
  vPbArr : Array Nat
  bkArr : Array (Option (Nat × SlotWidth × Bool))
  hintArr : Array (Option (Nat × Nat))
  forceEv : Trie (List Nat) := .empty
  armEvArr : Array (List Nat)

def pushArr {α : Type} (arr : Array (List α)) (k : Nat) (v : α) : Array (List α) :=
  if h : k < arr.size then arr.set k (v :: arr[k]) else arr

def addRegW (arr : Array Nat) (r w : Nat) : Array Nat :=
  if h : r < arr.size then arr.set r (arr[r] + w) else arr

def decPtsArr (pids : List Nat) (pb : Array Nat) : Array Nat :=
  pids.foldl (fun a p => if h : p < a.size then a.set p (a[p] - 1) else a) pb

def incPtsArr (pids : List Nat) (pb : Array Nat) : Array Nat :=
  pids.foldl (fun a p => if h : p < a.size then a.set p (a[p] + 1) else a) pb

def bestRegPrefArr (prefArr avoidArr : Array Nat) : List Nat → Option Nat
  | [] => none
  | r0 :: rs =>
    some (rs.foldl (fun (bestR, bestP, bestA) r =>
      let p := prefArr.getD r 0
      let a := avoidArr.getD r 0
      let better := Nat.ble (bestP + 1) p || (Nat.beq p bestP && Nat.ble (a + 1) bestA)
      if better then (r, p, a) else (bestR, bestP, bestA))
      (r0, prefArr.getD r0 0, avoidArr.getD r0 0)).1

def bestRegNetArr (prefArr antiArr avoidArr : Array Nat) : List Nat → Option Nat
  | [] => none
  | r0 :: rs =>
    let score (r : Nat) := (prefArr.getD r 0, antiArr.getD r 0, avoidArr.getD r 0)
    some (rs.foldl (fun (bestR, bestP, bestAn, bestAv) r =>
      let (p, an, av) := score r
      let lhs := p + bestAn
      let rhs := bestP + an
      let better := Nat.ble (rhs + 1) lhs ||
        (Nat.beq lhs rhs && (Nat.ble (an + 1) bestAn ||
          (Nat.beq an bestAn && Nat.ble (av + 1) bestAv)))
      if better then (r, p, an, av) else (bestR, bestP, bestAn, bestAv))
      (r0, score r0)).1

def dedupWithCount (xs : List Nat) : List Nat × List (Nat × Nat) :=
  match xs with
  | [] => ([], [])
  | [x] => ([x], [(x, 1)])
  | _ =>
    let (ordRev, cnts) := xs.foldl (fun (ord, m) y =>
      match m.get? y with
      | some c => (ord, m.insert y (c + 1))
      | none => (y :: ord, m.insert y 1))
      ([], (Std.HashMap.emptyWithCapacity xs.length : Std.HashMap Nat Nat))
    let ded := ordRev.reverse
    (ded, ded.map fun y => (y, cnts.getD y 1))

def armInteriorArr (a : ArmInfo) (exitArgs : Std.HashSet Nat)
    (varExtArr : Array (Option (Nat × Nat))) (y : Nat) : Bool :=
  match varExtArr.getD y none with
  | some (lo, hi) => Nat.ble a.lo lo && Nat.blt hi a.hi && !exitArgs.contains y
  | none => false

def armShareArr {I : Isa} (p : ColorPre I) (armEvArr : Array (List Nat))
    (owner y : Nat) : Bool :=
  match armEvArr.getD owner [] with
  | [] => false
  | ks => ks.any fun k => match p.armMap.get? k with
    | some a => armInteriorArr a (p.armExitArgs.getD k {}) p.varExtArr y
    | none => false

/-- Try to give a non-call-crossing GPR `x` a register by evicting it in the smallest set of
maximal arms that contain every conflicting holder of that register (and every exhausted
caller-saved pressure point). Accepted when the eviction cost (backup store plus weighted exit
reloads) beats spilling. -/
def tryArmEvictFast {I : Isa} (c : Ctx I) (p : ColorPre I) (x : Nat) (xI pids cpids : List Nat)
    (forbBkSlots : List (Nat × Nat)) (isBp isX : Bool) (dw cw csThresh wx : Nat)
    (s : ColorStArr I.Cond) : Option (ColorStArr I.Cond) :=
  if !c.cfg.armEvict || !Nat.ble (2 * baseMult) wx then none
  else
    let uses := p.useIpsArr.getD x []
    let inA (a : ArmInfo) (ip : Nat) : Bool := Nat.ble a.lo ip && Nat.blt ip a.hi
    let cand := (p.armsByVar.getD x []).filter fun a =>
      uses.all fun u => !inA a u || a.exits.any fun (jip, _, _, _) => Nat.beq jip u
    if cand.isEmpty then none
    else
      let pick (pred : ArmInfo → Bool) : Option ArmInfo :=
        cand.foldl (fun best a =>
          if pred a then
            match best with
            | some b => if Nat.blt (b.hi - b.lo) (a.hi - a.lo) then some a else best
            | none => some a
          else best) none
      let addArm (as : List ArmInfo) (a : ArmInfo) : List ArmInfo :=
        if as.any (fun b => Nat.beq b.key a.key) then as else a :: as
      let newCs := if Nat.ble csThresh wx then c.csIds.filter (!natMem · s.usedCs) else []
      let evalReg (r : Nat) : Option (Nat × List ArmInfo × Bool) :=
        let isCaller := Nat.blt r c.nGpr
        let confl := xI.filter fun y => match s.hArr.getD y .none with
          | .gpr ry => Nat.beq ry r && !armShareArr p s.armEvArr y x
          | _ => false
        let zeroPts :=
          if isCaller then pids.filter fun pid => !Nat.ble 1 (s.gPbArr.getD pid 0) else []
        if confl.isEmpty && zeroPts.isEmpty then none
        else
          let need1 := confl.foldl (fun acc y => acc.bind fun as =>
            (pick fun a =>
              armInteriorArr a (p.armExitArgs.getD a.key {}) p.varExtArr y).map
              (addArm as ·)) (some [])
          let need := zeroPts.foldl (fun acc pid => acc.bind fun as =>
            (pick fun a => inA a (p.ptIps[pid]?.getD 0)).map (addArm as ·)) need1
          need.bind fun as0 =>
            let as := as0.filter fun a => !as0.any fun b =>
              !Nat.beq b.key a.key && Nat.ble b.lo a.lo && Nat.ble a.hi b.hi
            if as.isEmpty then none
            else
              let entryW := as.foldl (fun n a => n + a.w) 0
              let exitW := as.foldl (fun n a => a.exits.foldl (fun n2 (_, j, w, args) =>
                if (p.lTrieSets.getD j {}).contains x || natMem x args then n2 + w else n2) n) 0
              let callW := if isX && isCaller then cw else 0
              let eager := !isBp && Nat.ble dw (entryW + callW)
              let loopX := if as.any (fun a => Nat.ble (blockArmKey 0) a.key) then 2 else 1
              some (loopX * min exitW entryW + (if eager then callW else entryW + 2 * callW), as,
                eager)
      let best := (c.gAlloc ++ s.usedCs ++ newCs).foldl
        (fun (b : Option (Nat × Nat × List ArmInfo × Bool)) r =>
          match evalReg r, b with
          | none, _ => b
          | some (cost, as, eg), some (_, bc, _, _) =>
            if Nat.blt cost bc then some (r, cost, as, eg) else b
          | some (cost, as, eg), none => some (r, cost, as, eg)) none
      match best with
      | none => none
      | some (r, cost, as, eager) =>
        let usesOut := uses.foldl (fun n u =>
          if as.any (inA · u) || p.foldIpsSet.contains u then n
          else n + (c.ipW.find? u <|> (c.brW.find? u).map (·.1) <|> c.jmpW.find? u).getD 0) 0
        if !Nat.ble (2 * cost + baseMult) usesOut then none
        else
          let isCaller := Nat.blt r c.nGpr
          let outside := pids.filter fun pid => !as.any fun a => inA a (p.ptIps[pid]?.getD 0)
          let bSlot := firstFreeSlotRange 1 forbBkSlots
          some { s with
            hArr := s.hArr.set! x (.gpr r),
            usedCs := if !isCaller && !natMem r s.usedCs then s.usedCs ++ [r] else s.usedCs,
            gPbArr := if isCaller then decPtsArr outside s.gPbArr else incPtsArr cpids s.gPbArr,
            bkArr := s.bkArr.set! x (some (bSlot, .w64, eager)),
            nslots := max s.nslots (bSlot + 1),
            armEvArr := s.armEvArr.set! x (as.map (·.key)) }

/-- Split a spilled GPR variable into a register outside `evBlks` (a high-pressure sub-region where
`x` is unused) by forcing `evIn` eviction on entry and reloading on exit when profitable. -/
def tryEvictSplitFast {I : Isa} (c : Ctx I) (p : ColorPre I) (x : Nat) (xI peers pids : List Nat)
    (forbBkSlots : List (Nat × Nat)) (prefArr avoidArr : Array Nat) (isBp : Bool)
    (dw cw wx slotCost : Nat) (s : ColorStArr I.Cond) : Option (ColorStArr I.Cond) :=
  if !(c.cfg.regEntry && c.cfg.sink) || !Nat.ble (10 * baseMult) wx then none
  else
    let zeroPids := pids.filter fun pid => !Nat.ble 1 (s.gPbArr.getD pid 0)
    if zeroPids.isEmpty then none
    else
      let badBlksOpt := zeroPids.foldl (fun (acc : Option (List Nat)) pid =>
        match acc, p.ptBlks[pid]? with
        | some bs, some (some b) => some (if natMem b bs then bs else b :: bs)
        | _, _ => none) (some [])
      match badBlksOpt with
      | none => none
      | some badBlks0 =>
        let (evBlks, evBlkSet) : List Nat × Std.HashSet Nat := badBlks0.foldl
          (fun ((acc, evS) : List Nat × Std.HashSet Nat) b =>
            let (acc, evS) := if evS.contains b then (acc, evS) else (b :: acc, evS.insert b)
            let lhdrs :=
              if c.cfg.backEdgeCoal then c.blkLoops.getD b []
              else if c.loops.getD b false then [b] else []
            lhdrs.foldl (fun (acc, evS) lh =>
              (union [lh] (c.loopReach.getD lh [])).foldl (fun (a, evS) b2 =>
                if !evS.contains b2 && (p.lTrieSets.getD b2 {}).contains x &&
                    !(p.blkUsesSets.getD b2 {}).contains x &&
                    !(isBp && (p.bparamsSets.getD b2 {}).contains x) then
                  (b2 :: a, evS.insert b2)
                else (a, evS)) (acc, evS)) (acc, evS)) ([], {})
        let okEv := evBlks.all fun b =>
          !(p.blkUsesSets.getD b {}).contains x &&
            !(isBp && (p.bparamsSets.getD b {}).contains x)
        if !okEv then none
        else
          let inEvBlk (pid : Nat) : Bool := match p.ptBlks[pid]? with
            | some (some b) => evBlkSet.contains b | _ => false
          let pidsOut := pids.filter (!inEvBlk ·)
          if !pidsOut.all (fun pid => Nat.ble 1 (s.gPbArr.getD pid 0)) then none
          else
            let (wEnter, nEnter) := evBlks.foldl (fun (we, ne) b =>
              (p.edgesByDst.getD b []).foldl (fun (we, ne) (src, dst, w, _) =>
                if !evBlkSet.contains src && (p.lTrieSets.getD dst {}).contains x then
                  (we + w, ne + 1)
                else (we, ne)) (we, ne)) (0, 0)
            let (wExit, nExit, exitArgSet) := evBlks.foldl
              (fun ((wx0, nx0, eas) : Nat × Nat × Std.HashSet Nat) b =>
                (p.edgesBySrc.getD b []).foldl
                  (fun ((wx0, nx0, eas) : Nat × Nat × Std.HashSet Nat) (_, dst, w, args) =>
                    if !evBlkSet.contains dst then
                      let inDst := (p.lTrieSets.getD dst {}).contains x
                      let wx1 := if inDst then wx0 + w else wx0
                      let nx1 := if inDst || natMem x args then nx0 + 1 else nx0
                      let eas1 := args.foldl (fun (t : Std.HashSet Nat) v => t.insert v) eas
                      (wx1, nx1, eas1)
                    else (wx0, nx0, eas)) (wx0, nx0, eas)) (0, 0, ({} : Std.HashSet Nat))
            let canEagerEv := !isBp && Nat.ble 1 cw && Nat.ble (dw + 1) (cw + wEnter)
            let evCost := (if canEagerEv then dw + cw else 2 * cw + wEnter) + min wEnter wExit
            let usesOut := (p.varBlksArr.getD x []).foldl (fun a b =>
              if evBlkSet.contains b then a
              else (c.blkUses.getD b []).foldl (fun n y => if Nat.beq y x then n + 1 else n) a) 0
            let splitOps := (if canEagerEv then 1 else nEnter) + nExit
            let baseOps := (if isBp then 0 else 1) + usesOut
            let minUses := 8
            let maxExits := 1
            let outPbOk := pidsOut.all (fun pid => Nat.ble 2 (s.gPbArr.getD pid 0)) ||
              Nat.ble minUses usesOut
            if !outPbOk || !Nat.ble 1 wEnter || !Nat.ble (evCost + baseMult) slotCost ||
                !Nat.ble nExit maxExits || !Nat.ble minUses usesOut ||
                !Nat.blt (2 * splitOps) baseOps then
              none
            else
              let isInterior (y : Nat) : Bool :=
                !exitArgSet.contains y && (p.varBlksArr.getD y []).all (evBlkSet.contains ·)
              let forb0 := xI.foldl (fun (fb : Array Bool) y =>
                if isInterior y then fb
                else match s.hArr.getD y .none with
                  | .gpr r => if h : r < fb.size then fb.set r true else fb
                  | _ => fb) (Array.replicate p.numG false)
              let forb := peers.foldl (fun (fb : Array Bool) z =>
                match s.hArr.getD z .none with
                | .gpr r =>
                  if Nat.ble (r + 1) c.nGpr then
                    if h : r < fb.size then fb.set r true else fb
                  else fb
                | _ => fb) forb0
              let evCaller := c.gAlloc.filter (!forb.getD · false)
              match bestRegPrefArr prefArr avoidArr evCaller with
              | none => none
              | some r =>
                let bSlot := firstFreeSlotRange 1 forbBkSlots
                let fe := evBlks.foldl (fun t b => triePush t b x) s.forceEv
                some { s with
                  hArr := s.hArr.set! x (.gpr r), gPbArr := decPtsArr pidsOut s.gPbArr,
                  bkArr := s.bkArr.set! x (some (bSlot, .w64, canEagerEv)),
                  nslots := max s.nslots (bSlot + 1), forceEv := fe }

/-- Split a spilled GPR variable `x` across multi-block inner loops where `x` is live-in but
completely unused: evict `x` to a backup slot on loop entry and reload on loop exits so `x`
keeps a GPR outside while freeing that GPR for hot inner-loop variables. -/
def tryLoopBoundarySplitFast {I : Isa} (c : Ctx I) (p : ColorPre I) (x : Nat) (xI pids : List Nat)
    (forbBkSlots : List (Nat × Nat)) (prefArr avoidArr : Array Nat) (isBp isX : Bool)
    (dw cw wx _slotCost : Nat) (s : ColorStArr I.Cond) : Option (ColorStArr I.Cond) :=
  if !(c.cfg.regEntry && c.cfg.sink && c.cfg.armEvict && c.cfg.armLoops && c.cfg.backEdgeCoal) ||
      !Nat.ble (2 * baseMult) wx || (isX && !c.cfg.armX) then none
  else
    let unusedLoops := (p.varBlksArr.getD x []).filter fun b =>
      c.loops.getD b false && (p.lTrieSets.getD b {}).contains x &&
        let rch := union [b] (c.loopReach.getD b [])
        rch.all fun b2 =>
          !(p.blkUsesSets.getD b2 {}).contains x &&
            !(isBp && (p.bparamsSets.getD b2 {}).contains x)
    if unusedLoops.isEmpty then none
    else
      let evBlks := unusedLoops.foldl (fun acc lh =>
        union (union [lh] (c.loopReach.getD lh [])) acc) []
      let evBlkSet := hashSetOfList evBlks
      let inEvBlk (pid : Nat) : Bool := match p.ptBlks[pid]? with
        | some (some b) => evBlkSet.contains b | _ => false
      let pidsOut := pids.filter (!inEvBlk ·)
      let callerOk := pidsOut.all fun pid => Nat.ble 1 (s.gPbArr.getD pid 0)
      let (wEnter, nEnter) := evBlks.foldl (fun (we, ne) b =>
        (p.edgesByDst.getD b []).foldl (fun (we, ne) (src, dst, w, _) =>
          if !evBlkSet.contains src && (p.lTrieSets.getD dst {}).contains x then
            (we + w, ne + 1)
          else (we, ne)) (we, ne)) (0, 0)
      let (wExit, nExit, exitArgSet) := evBlks.foldl (fun (wx0, nx0, eas) b =>
        (p.edgesBySrc.getD b []).foldl (fun (wx0, nx0, eas) (_, dst, w, args) =>
          if !evBlkSet.contains dst then
            let liveOrArg := (p.lTrieSets.getD dst {}).contains x || natMem x args
            let wx1 := if liveOrArg then wx0 + w else wx0
            let nx1 := if liveOrArg then nx0 + 1 else nx0
            let eas1 := args.foldl (fun t v => t.insert v) eas
            (wx1, nx1, eas1)
          else (wx0, nx0, eas)) (wx0, nx0, eas)) (0, 0, ({} : Std.HashSet Nat))
      let uses := (p.useIpsArr.getD x []).filter (!p.foldIpsSet.contains ·)
      let usesOut := uses.length
      let usesOutW := uses.foldl (fun n u =>
        n + (c.ipW.find? u <|> (c.brW.find? u).map (·.1) <|> c.jmpW.find? u).getD 0) 0
      let baseOps := (if isBp then 0 else 1) + usesOut
      if !Nat.ble 1 wEnter || !Nat.ble nExit 4 || Nat.beq usesOut 0 then none
      else
        let isInterior (y : Nat) : Bool :=
          let ybs := p.varBlksArr.getD y []
          !ybs.isEmpty && !exitArgSet.contains y && ybs.all (evBlkSet.contains ·)
        let forbOut := xI.foldl (fun fb y =>
          if isInterior y then fb
          else match s.hArr.getD y .none with
            | .gpr r => if h : r < fb.size then fb.set r true else fb
            | _ => fb) (Array.replicate p.numG false)
        let evalReg (r : Nat) : Option Bool :=
          let isCaller := Nat.blt r c.nGpr
          let callW := if isX && isCaller then cw else 0
          let canEagerEv := !isBp && Nat.ble dw (wEnter + callW)
          let evCost := (if canEagerEv then dw + callW else 2 * callW + wEnter) + min wEnter wExit
          let splitOps := (if canEagerEv then 1 else nEnter) + nExit
          if Nat.blt splitOps baseOps && Nat.ble (2 * evCost + baseMult) usesOutW then
            some canEagerEv
          else none
        let cands :=
          (((if callerOk then c.gAlloc else []) ++ s.usedCs).filter (!forbOut.getD · false)).filter
            fun r => (evalReg r).isSome
        match bestRegPrefArr prefArr avoidArr cands with
        | none => none
        | some r =>
          let isCaller := Nat.blt r c.nGpr
          let canEagerEv := (evalReg r).getD false
          let bSlot := firstFreeSlotRange 1 forbBkSlots
          let fe := evBlks.foldl (fun t b => triePush t b x) s.forceEv
          some { s with
            hArr := s.hArr.set! x (.gpr r),
            gPbArr := if isCaller then decPtsArr pidsOut s.gPbArr else s.gPbArr,
            bkArr := s.bkArr.set! x (some (bSlot, .w64, canEagerEv)),
            nslots := max s.nslots (bSlot + 1),
            forceEv := fe }

/-- Color one variable `x` of weight `wx` using pre-indexed `ColorPre` arrays and O(1) register
weight accumulators, producing bit-exact identical decisions to the Trie/list implementation. -/
def colorOneFast {I : Isa} (c : Ctx I) (p : ColorPre I) (s : ColorStArr I.Cond) (wx x : Nat) :
    ColorStArr I.Cond :=
  let xI := p.interfDedup.getD x []
  let peers := p.zextArr.getD x []
  let forbSlots0 := xI.foldl (fun ss y =>
    let ss := match s.hArr.getD y .none with | .slot b w => (b, w.slots) :: ss | _ => ss
    match s.bkArr.getD y none with | some (b, w, _) => (b, w.slots) :: ss | none => ss) []
  let forbSlots := peers.foldl (fun ss y =>
    match s.bkArr.getD y none with | some (b, w, _) => (b, w.slots) :: ss | none => ss) forbSlots0
  let forbBkSlots := peers.foldl (fun ss y =>
    match s.hArr.getD y .none with | .slot b w => (b, w.slots) :: ss | _ => ss) forbSlots
  let isX := p.crossArr.getD x false
  let cw := p.cwArr.getD x 0
  let dw := p.defWArr.getD x baseMult
  let isBp := p.isBPArr.getD x false
  let canEager := isX && !isBp && Nat.ble (dw + 1) cw
  let splitCost := if canEager then dw + cw else 2 * cw
  let slotCost := wx + if p.fnParamSet.contains x then baseMult else 0
  let splitOk := Nat.ble (splitCost + 1) slotCost
  let cheapSplit := isX && splitOk && Nat.ble splitCost c.csCost
  let toSlot (w : SlotWidth) : ColorStArr I.Cond :=
    let prefB := (p.affArr.getD x []).foldl (fun best (y, wy) =>
      match s.hArr.getD y .none with
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
    { s with hArr := s.hArr.set! x (.slot b w), nslots := max s.nslots (b + w.slots) }
  let withBk (w : SlotWidth) (s1 : ColorStArr I.Cond) : ColorStArr I.Cond :=
    let b := firstFreeSlotRange w.slots forbBkSlots
    { s1 with bkArr := s1.bkArr.set! x (some (b, w, canEager)),
              nslots := max s1.nslots (b + w.slots) }
  match p.banksArr.getD x .gpr with
  | .gpr =>
    let bpSlotPref : Option Nat :=
      if !isBp then none
      else
        let xs := p.affArr.getD x []
        let totAff := xs.foldl (fun a (_, w) => a + w) 0 +
          (p.abiGArr.getD x []).foldl (fun a (_, w) => a + w) 0
        let slotWs := xs.foldl (fun (acc : List (Nat × Nat)) (y, wy) =>
          match s.hArr.getD y .none with
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
    | some s0 => { s with hArr := s.hArr.set! x (.slot s0 .w64), nslots := max s.nslots (s0 + 1) }
    | none =>
      let forb := xI.foldl (fun fb y => match s.hArr.getD y .none with
        | .gpr r =>
          if fb.getD r false || armShareArr p s.armEvArr y x then fb
          else if h : r < fb.size then fb.set r true else fb
        | _ => fb) (Array.replicate p.numG false)
      let pids := p.gVpArr.getD x []
      let cpids := p.gCpArr.getD x []
      let sharedPeerReg? : Option (Nat × List Nat) :=
        if isX then none
        else peers.findSome? fun z =>
          match s.hArr.getD z .none with
          | .gpr r =>
            if Nat.blt r c.nGpr && (s.bkArr.getD z none).isNone && !forb.getD r false then
              let zPids := p.gVpArr.getD z []
              let extraPids :=
                if zPids.length > 4 then
                  let zs := hashSetOfList zPids
                  pids.filter (!zs.contains ·)
                else pids.filter (!natMem · zPids)
              if extraPids.all (fun pid => Nat.ble 1 (s.gPbArr.getD pid 0)) then some (r, extraPids)
              else none
            else none
          | _ => none
      match sharedPeerReg? with
      | some (r, extraPids) =>
        { s with hArr := s.hArr.set! x (.gpr r), gPbArr := decPtsArr extraPids s.gPbArr }
      | none =>
        let forbCaller := peers.foldl (fun fb z => match s.hArr.getD z .none with
          | .gpr r =>
            if ((s.bkArr.getD z none).isSome || isX) && Nat.ble (r + 1) c.nGpr then
              if h : r < fb.size then fb.set r true else fb
            else fb
          | _ => fb) forb
        let caller := if pids.all (fun pid => Nat.ble 1 (s.gPbArr.getD pid 0)) then
            c.gAlloc.filter (!forbCaller.getD · false) else []
        let csFree := s.usedCs.filter (!forb.getD · false)
        let baseCsThresh := if Nat.ble c.nGpr 8 then 2 * baseMult else 3 * baseMult
        let csThresh := max baseCsThresh c.csCost
        let newCs := if Nat.ble csThresh wx then
            c.csIds.filter (fun r => !natMem r s.usedCs && !forb.getD r false) else []
        let addNbrPref (u w scale : Nat) (acc : Array Nat × List Nat) :=
          match s.hArr.getD u .none with
          | .gpr ru => (addRegW acc.1 ru (w / scale), ru :: acc.2)
          | .none =>
            (p.abiGArr.getD u []).foldl
              (fun (pa, prs) (ru, wu) => (addRegW pa ru (min w wu / scale), ru :: prs)) acc
          | _ => acc
        let abiX := p.abiGArr.getD x []
        let prefArr0 := abiX.foldl (fun a (r, w) => addRegW a r w) (Array.replicate p.numG 0)
        let (prefArr, prefRegs) := (p.affArr.getD x []).foldl (fun (pa, prs) (y, w) =>
          match s.hArr.getD y .none with
          | .gpr ry => (addRegW pa ry w, ry :: prs)
          | .none =>
            let st1 := (p.abiGArr.getD y []).foldl
              (fun (a, rs) (ry, wy) => (addRegW a ry (min w wy / 2), ry :: rs)) (pa, prs)
            (p.affArr.getD y []).foldl (fun acc (z, wz) =>
              if Nat.beq z x then acc else addNbrPref z (min w wz) 4 acc) st1
          | _ => (pa, prs)) (prefArr0, abiX.map Prod.fst)
        let antiArr := (p.antiArr.getD x []).foldl (fun a (y, w) =>
          match s.hArr.getD y .none with | .gpr ry => addRegW a ry w | _ => a)
          (Array.replicate p.numG 0)
        let avoidArr0 := if c.cfg.backEdgeCoal then Array.replicate p.numG 0 else antiArr
        let avoidArr := (p.interfMult.getD x []).foldl (fun av (z, mult) =>
          match s.hArr.getD z .none with
          | .none =>
            let av1 := (p.abiGArr.getD z []).foldl (fun a (r, w) => addRegW a r (mult * w)) av
            (p.affArr.getD z []).foldl (fun a (u, wu) =>
              if Nat.beq u x then a
              else match s.hArr.getD u .none with
                | .gpr ru => addRegW a ru (mult * (wu / 2))
                | .none =>
                  (p.abiGArr.getD u []).foldl
                    (fun a2 (ru, w_u) => addRegW a2 ru (mult * (min wu w_u / 2))) a
                | _ => a) av1
          | .slot _ _ =>
            match s.hintArr.getD z none with
            | some (rh, wh) => addRegW av rh (mult * wh)
            | none => av
          | _ => av) avoidArr0
        let pickReg (cands : List Nat) : Option Nat :=
          if c.cfg.backEdgeCoal then bestRegNetArr prefArr antiArr avoidArr cands
          else bestRegPrefArr prefArr avoidArr cands
        let toSlotG : ColorStArr I.Cond :=
          let s1 := toSlot .w64
          let best := prefRegs.foldl (fun (b : Option (Nat × Nat)) r =>
            let tw := prefArr.getD r 0
            match b with
            | some (_, bw) => if Nat.blt bw tw then some (r, tw) else b
            | none =>
              if Nat.ble (r + 1) (c.nGpr + c.csIds.length) then some (r, tw) else none) none
          match best with
          | some (r, _) =>
            if c.cfg.cacheHint then { s1 with hintArr := s1.hintArr.set! x (some (r, wx)) } else s1
          | none => s1
        let inReg (r : Nat) : ColorStArr I.Cond :=
          let gPb1 :=
            if Nat.ble (r + 1) c.nGpr then decPtsArr pids s.gPbArr else incPtsArr cpids s.gPbArr
          let s1 := { s with hArr := s.hArr.set! x (.gpr r), gPbArr := gPb1 }
          if isX && Nat.ble (r + 1) c.nGpr then withBk .w64 s1 else s1
        let inNewCs (r : Nat) : ColorStArr I.Cond :=
          { s with hArr := s.hArr.set! x (.gpr r), usedCs := s.usedCs ++ [r],
                   gPbArr := incPtsArr cpids s.gPbArr }
        let toSlotOrEv : ColorStArr I.Cond :=
          match tryEvictSplitFast c p x xI peers pids forbBkSlots prefArr avoidArr
              isBp dw cw wx slotCost s with
          | some sEv => sEv
          | none =>
            let armEv? := if !peers.isEmpty || (isX && !c.cfg.armX) then none
              else tryArmEvictFast c p x xI pids cpids forbBkSlots isBp isX dw cw csThresh wx s
            match armEv? with
            | some sA => sA
            | none =>
              let loopEv? := if !peers.isEmpty then none
                else tryLoopBoundarySplitFast c p x xI pids forbBkSlots prefArr avoidArr
                  isBp isX dw cw wx slotCost s
              match loopEv? with
              | some sL => sL
              | none => toSlotG
        let orSplitOrSlot : ColorStArr I.Cond :=
          match (if isX && splitOk then pickReg caller else none) with
          | some r => inReg r
          | none => toSlotOrEv
        let orNewCs : ColorStArr I.Cond :=
          match pickReg newCs with
          | some r => inNewCs r
          | none => orSplitOrSlot
        if !isX then
          match pickReg (caller ++ csFree) with
          | some r => inReg r
          | none => orNewCs
        else
          match pickReg csFree with
          | some r => inReg r
          | none =>
            match (if cheapSplit then pickReg caller else none) with
            | some r => inReg r
            | none => orNewCs
  | .vec w =>
    let forb := xI.foldl (fun fb y => match s.hArr.getD y .none with
      | .vec v => if h : v < fb.size then fb.set v true else fb
      | _ => fb) (Array.replicate p.numV false)
    let pids := p.vVpArr.getD x []
    let cands := if (!isX || splitOk) && pids.all (fun pid => Nat.ble 1 (s.vPbArr.getD pid 0)) then
        c.vAlloc.filter (!forb.getD · false) else []
    if cands.isEmpty then toSlot w
    else
      let prefArr0 := (p.abiVArr.getD x []).foldl (fun a (v, wv) => addRegW a v wv)
        (Array.replicate p.numV 0)
      let prefArr := (p.affArr.getD x []).foldl (fun pa (y, wy) =>
        match s.hArr.getD y .none with
        | .vec vy => addRegW pa vy wy
        | .none => (p.abiVArr.getD y []).foldl (fun a (vy, wv) => addRegW a vy (min wy wv / 2)) pa
        | _ => pa) prefArr0
      let avoidArr0 := (p.antiArr.getD x []).foldl (fun a (y, wy) =>
        match s.hArr.getD y .none with | .vec vy => addRegW a vy wy | _ => a)
        (Array.replicate p.numV 0)
      let avoidArr := (p.interfMult.getD x []).foldl (fun av (z, mult) =>
        match s.hArr.getD z .none with
        | .none => (p.abiVArr.getD z []).foldl (fun a (vz, wz) => addRegW a vz (mult * wz)) av
        | _ => av) avoidArr0
      match bestRegPrefArr prefArr avoidArr cands with
      | some v =>
        let s1 := { s with hArr := s.hArr.set! x (.vec v),
                           vPbArr := if Nat.ble (v + 1) c.nVec then decPtsArr pids s.vPbArr
                             else s.vPbArr }
        if isX then withBk w s1 else s1
      | none => toSlot w

/-- Array-backed 2-pass iterative recoloring matching `SpillCoalesce.refineColors` bit-exactly. -/
def refineColorsArr {I : Isa} (c : Ctx I) (p : ColorPre I) (order : List (Nat × Nat))
    (bkArr : Array (Option (Nat × SlotWidth × Bool))) (armEvArr : Array (List Nat))
    (forceEv : Trie (List Nat)) (usedCs : List Nat) (hArr0 : Array (Home I.Cond)) :
    Array (Home I.Cond) :=
  let emptyAv : Array Nat := Array.replicate p.numG 0
  let isForced (x : Nat) : Bool :=
    (p.varBlksArr.getD x []).any fun b => natMem x (forceEv.getD b [])
  let stepOne (hArr : Array (Home I.Cond)) (x : Nat) : Array (Home I.Cond) :=
    if !(armEvArr.getD x []).isEmpty || isForced x then hArr
    else match hArr.getD x .none with
      | .gpr rx =>
        let isCaller := Nat.blt rx c.nGpr
        let cands0 := if isCaller then c.gAlloc else usedCs
        let xI := p.interfDedup.getD x []
        let peers := p.zextArr.getD x []
        let isX := p.crossArr.getD x false
        let xSplit := isX || (bkArr.getD x none).isSome
        let forb0 := xI.foldl (fun fb y => match hArr.getD y .none with
          | .gpr ry =>
            if fb.getD ry false || armShareArr p armEvArr y x then fb
            else if h : ry < fb.size then fb.set ry true else fb
          | _ => fb) (Array.replicate p.numG false)
        let forb := if !isCaller then forb0 else
          peers.foldl (fun fb z => match hArr.getD z .none with
            | .gpr rz =>
              if (xSplit || (bkArr.getD z none).isSome || p.crossArr.getD z false) &&
                  Nat.blt rz c.nGpr then
                if h : rz < fb.size then fb.set rz true else fb
              else fb
            | _ => fb) forb0
        let cands := cands0.filter (!forb.getD · false)
        let prefArr0 := (p.abiGArr.getD x []).foldl (fun a (r, w) => addRegW a r w)
          (Array.replicate p.numG 0)
        let prefArr := (p.affArr.getD x []).foldl (fun a (y, w) =>
          match hArr.getD y .none with | .gpr ry => addRegW a ry w | _ => a) prefArr0
        let antiArr := (p.antiArr.getD x []).foldl (fun a (y, w) =>
          match hArr.getD y .none with | .gpr ry => addRegW a ry w | _ => a)
          (Array.replicate p.numG 0)
        match bestRegNetArr prefArr antiArr emptyAv (rx :: cands.filter (!Nat.beq · rx)) with
        | some r =>
          if Nat.beq r rx then hArr
          else
            let pNew := prefArr.getD r 0; let anNew := antiArr.getD r 0
            let pOld := prefArr.getD rx 0; let anOld := antiArr.getD rx 0
            let better := Nat.ble (pOld + anNew + 1) (pNew + anOld) ||
              (Nat.beq (pNew + anOld) (pOld + anNew) && Nat.ble (anNew + 1) anOld)
            if better then hArr.set! x (.gpr r) else hArr
        | none => hArr
      | _ => hArr
  let pass (hArr : Array (Home I.Cond)) := order.foldl (fun h (_, x) => stepOne h x) hArr
  pass (pass hArr0)

def colorVarsFast {I : Isa} (c : Ctx I) (nv : Nat) (banksArr : Array Bank)
    (flagHome : Trie I.Cond) (acc : GatherAcc) (fnParams : List Nat)
    (fnAbi : List (Option (Sum Nat Nat)))
    (arms : List ArmInfo) (varExtArr : Array (Option (Nat × Nat)))
    (useIpsArr : Array (List Nat)) (foldIpsSet : Std.HashSet Nat)
    (lTrieSets blkUsesSets bparamsSets : Std.HashMap Nat (Std.HashSet Nat))
    (edgesBySrc edgesByDst : Std.HashMap Nat (List (Nat × Nat × Nat × List Nat)))
    (varBlksArr : Array (List Nat)) : ColorSt I.Cond × Trie Nat :=
  let (abiG, abiV) :=
    addAbiArgs (fnParams.map some) fnAbi (4 * baseMult) acc.abiGpr acc.abiVec
  let sumWArr (ws : List (Nat × List Nat)) : Array Nat :=
    ws.foldl (fun arr (w, vs) =>
      vs.foldl (fun a x => if h : x < a.size then a.set x (a[x] + w) else a) arr)
      (Array.replicate nv 0)
  let wArr := sumWArr acc.weights
  let cwArr := sumWArr acc.callW
  let di0 := fnParams.foldl (fun d p => (p, fnParams) :: d) acc.defInterf
  let order := sortByWeight nv ((dedup (di0.map Prod.fst)).map fun x => (wArr.getD x 0, x))
  let rawInterf : Array (List Nat) := di0.foldl (fun arr (z, ys) =>
    ys.foldl (fun arr y =>
      if Nat.beq y z then arr else pushArr (pushArr arr z y) y z) arr)
    (Array.replicate nv [])
  let (interfDedup, interfMult) := (List.range nv).foldl (fun (da, ma) x =>
    let (d, m) := dedupWithCount (rawInterf.getD x [])
    (da.push d, ma.push m)) (Array.mkEmpty nv, Array.mkEmpty nv)
  let nGprPts := acc.gprPts.length
  let (gPb0, gVpArr, gCpArr, _) := acc.gprPts.foldl
    (fun (pb, vp, cp, pid) (b, vs, cvs) =>
      (pb.push b, vs.foldl (fun a x => pushArr a x pid) vp,
        cvs.foldl (fun a u => pushArr a u pid) cp, pid + 1))
    (Array.mkEmpty nGprPts, Array.replicate nv [], Array.replicate nv [], 0)
  let nVecPts := acc.vecPts.length
  let (vPb0, vVpArr, _) := acc.vecPts.foldl
    (fun (pb, vp, pid) (b, vs) =>
      (pb.push b, vs.foldl (fun a x => pushArr a x pid) vp, pid + 1))
    (Array.mkEmpty nVecPts, Array.replicate nv [], 0)
  let abiGArr := abiG.foldl (fun a (u, r, w) => pushArr a u (r, w)) (Array.replicate nv [])
  let abiVArr := abiV.foldl (fun a (u, r, w) => pushArr a u (r, w)) (Array.replicate nv [])
  let affArr := acc.affEdges.foldl (fun a (u, v, w) =>
    if Nat.beq u v then a else pushArr (pushArr a u (v, w)) v (u, w)) (Array.replicate nv [])
  let antiArr := acc.antiEdges.foldl (fun a (u, v, w) =>
    if Nat.beq u v then a else pushArr (pushArr a u (v, w)) v (u, w)) (Array.replicate nv [])
  let zextArr := acc.zextEdges.foldl (fun a (u, v) =>
    if Nat.beq u v then a else pushArr (pushArr a u v) v u) (Array.replicate nv [])
  let crossArr := (List.range nv).foldl (fun a x => a.push (c.cross.getD x false))
    (Array.mkEmpty nv)
  let isBPArr := (List.range nv).foldl (fun a x => a.push (acc.isBP.getD x false))
    (Array.mkEmpty nv)
  let defWArr := (List.range nv).foldl (fun a x => a.push (acc.defWT.getD x baseMult))
    (Array.mkEmpty nv)
  let armMap : Std.HashMap Nat ArmInfo := arms.foldl (fun m a => m.insert a.key a) {}
  let armExitArgs : Std.HashMap Nat (Std.HashSet Nat) := arms.foldl (fun m a =>
    let s := a.exits.foldl (fun t (_, _, _, as) => as.foldl (fun t v => t.insert v) t)
      ({} : Std.HashSet Nat)
    m.insert a.key s) {}
  let armsByVar : Array (List ArmInfo) := arms.reverse.foldl (fun arr a =>
    a.liveIn.foldl (fun arr v => pushArr arr v a) arr) (Array.replicate nv [])
  let pre : ColorPre I := {
    nv, numG := c.allGpr.length, numV := c.allVec.length,
    banksArr, crossArr, isBPArr, cwArr, defWArr, interfDedup, interfMult,
    gVpArr, gCpArr, vVpArr, abiGArr, abiVArr, affArr, antiArr, zextArr,
    fnParamSet := hashSetOfList fnParams,
    ptBlks := acc.gprPtBlks.toArray, ptIps := acc.gprPtIps.toArray,
    armMap, armsByVar, armExitArgs, varExtArr, useIpsArr, foldIpsSet,
    lTrieSets, blkUsesSets, bparamsSets, edgesBySrc, edgesByDst, varBlksArr }
  let initHome : Array (Home I.Cond) := (List.range nv).foldl (fun h x =>
    match flagHome.find? x with | some cc => h.push (.flag cc) | none => h.push .none)
    (Array.mkEmpty nv)
  let cs0 : ColorStArr I.Cond := order.foldl (fun (s : ColorStArr I.Cond) (wx, x) =>
    match s.hArr.getD x .none with
    | .flag _ => s
    | _ => colorOneFast c pre s wx x)
    { hArr := initHome, gPbArr := gPb0, vPbArr := vPb0,
      bkArr := Array.replicate nv none, hintArr := Array.replicate nv none,
      armEvArr := Array.replicate nv [] }
  let hArrFinal :=
    if c.cfg.backEdgeCoal then
      refineColorsArr c pre order cs0.bkArr cs0.armEvArr cs0.forceEv cs0.usedCs cs0.hArr
    else cs0.hArr
  let (hT, bkT, hintT, armEvT, wTrie) := (List.range nv).foldl
    (fun (ht, bt, hnt, aet, wt) x =>
      let ht' := match hArrFinal.getD x .none with | .none => ht | h => ht.insert x h
      let bt' := match cs0.bkArr.getD x none with | some b => bt.insert x b | none => bt
      let hnt' := match cs0.hintArr.getD x none with | some h => hnt.insert x h | none => hnt
      let aet' := match cs0.armEvArr.getD x [] with | [] => aet | ks => aet.insert x ks
      let wx := wArr.getD x 0
      let wt' := if Nat.beq wx 0 then wt else wt.insert x wx
      (ht', bt', hnt', aet', wt'))
    (.empty, .empty, .empty, .empty, .empty)
  ({ hT, usedCs := cs0.usedCs, nslots := cs0.nslots, bk := bkT, hint := hintT,
     forceEv := cs0.forceEv, armEv := armEvT }, wTrie)

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
  let evL := c.forceEv.getD l []
  let lv := (c.lTrie.getD l []).filter (!natMem · evL)
  (dedup (gprHomes home (lv ++ ps.map Prod.fst))).length

/-- Number of block parameters `ps` needing a fresh GPR in `pickPlocs`, given `useSlot p` (whether
`.slot _ .w64` keeps its slot directly). -/
def countPlocGprs {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond))
    (useSlot : Nat → Bool) (ps : List (Nat × Ty)) : Nat :=
  ps.foldl (fun n (p, _) =>
    match home.getD p .none with
    | .flag _ | .gpr _ | .vec _ => n
    | .slot _ .w64 => if useSlot p then n else n + 1
    | _ => if (c.banks.getD p .gpr).isVec then n else n + 1) 0

/-- Enforce `usedG + needPloc <= nGpr + csIds.length` at every block entry by forcing
lowest-weight `bk` live-ins into `forceEv` or demoting lowest-weight non-param GPR live-ins
to fresh slots when spilled parameters cannot use slot-direct `ploc`. -/
def fitBlockGprs {I : Isa} (c : Ctx I) (wTrie : Trie Nat) (bk : Trie (Nat × SlotWidth × Bool))
    (usedCs : List Nat) (nslots0 : Nat) (home0 : Trie (Home I.Cond)) (fe0 : Trie (List Nat))
    (t : Tree) (tBlocks : List (Nat × List (Nat × Ty) × Tree) := t.blocks) :
    Trie (Home I.Cond) × Trie (List Nat) × Nat :=
  let cap := c.nGpr + c.csIds.length
  let bad := scanSlotPlocBad c home0 bk usedCs .empty t
  let pickMin (xs : List Nat) : Option Nat := xs.foldl (fun b x => match b with
    | some y => if Nat.blt (wTrie.getD x 0) (wTrie.getD y 0) then some x else b
    | none => some x) none
  let rec fix (h : Trie (Home I.Cond)) (fe : Trie (List Nat)) (ns : Nat) :
      List (Nat × List (Nat × Ty) × Tree) → Trie (Home I.Cond) × Trie (List Nat) × Nat
    | [] => (h, fe, ns)
    | (l, ps, _) :: rest =>
      let lv := c.lTrie.getD l []
      let pvars := ps.map Prod.fst
      let pvarSet := hashSetOfList pvars
      let needPloc := countPlocGprs c h (fun p => !bad.getD p false) ps
      let rec dropVars (h : Trie (Home I.Cond)) (fe : Trie (List Nat)) (ns : Nat) :
          Nat → Trie (Home I.Cond) × Trie (List Nat) × Nat
        | 0 => (h, fe, ns)
        | fuel + 1 =>
          let evL := fe.getD l []
          let lvAct :=
            if evL.isEmpty then lv
            else
              let evS := hashSetOfList evL
              lv.filter (!evS.contains ·)
          let gprCnts : Std.HashMap Nat Nat :=
            (gprHomes h lvAct ++ gprHomes h pvars).foldl
              (fun m r => m.insert r (m.getD r 0 + 1)) {}
          if Nat.ble (gprCnts.size + needPloc) cap then (h, fe, ns)
          else
            let cands := lvAct.filter fun x =>
              !pvarSet.contains x && match h.getD x .none with
                | .gpr rx => Nat.beq (gprCnts.getD rx 0) 1
                | _ => false
            match pickMin (cands.filter fun x => (bk.find? x).isSome) with
            | some x => dropVars h (triePush fe l x) ns fuel
            | none =>
              match pickMin (cands.filter fun x => (bk.find? x).isNone) with
              | some x => dropVars (h.insert x (.slot ns .w64)) fe (ns + 1) fuel
              | none => (h, fe, ns)
      let (h', fe', ns') := dropVars h fe ns (lv.length + 1)
      fix h' fe' ns' rest
  fix home0 fe0 nslots0 tBlocks

/-- Determine which slot-homed GPR block parameters can safely use `.slot s .w64` directly as their
`Entry.ploc` (avoiding jump-edge reload + block-entry store round-trips): safe when no other
incoming jump arg or block live-in variable occupies slot `s`, and every jump needing a temporary
register to materialize an immediate or copy from another slot has a free non-scratch GPR. With
`cfg.joinGuard`, a parameter without a zero-move (same-slot) incoming edge that is read early
in its block on at least half of the block's weight keeps a register `Entry.ploc` instead (bounded
by the block's total GPR budget `nGpr + csIds.length`): the slot-direct form would store on every
edge and reload at once (a join round-trip). -/
def slotPlocMap {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond))
    (bk : Trie (Nat × SlotWidth × Bool)) (usedCs : List Nat) (defWT : Trie Nat) (t : Tree)
    (tBlocks : List (Nat × List (Nat × Ty) × Tree) := t.blocks) :
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
  markOk .empty tBlocks

private abbrev RegionVarSet := List Nat × Std.HashSet Nat

private def rvsAdd (s : RegionVarSet) (xs : List Nat) : RegionVarSet :=
  xs.foldl (fun (ks, t) x => if t.contains x then (ks, t) else (x :: ks, t.insert x)) s

private def rvsInter (a b : RegionVarSet) : RegionVarSet :=
  let (small, bigM) := if Nat.ble a.1.length b.1.length then (a.1, b.2) else (b.1, a.2)
  small.foldl (fun (ks, m) x =>
    if bigM.contains x then (x :: ks, m.insert x) else (ks, m)) ([], {})

mutual
/-- Linear bottom-up pass recording, at each `.let_` `ip`, the continuation live-ins reused
within the same straight-line region (or both arms of a `jnz`) by non-compare ops. -/
private def buildRegionReused {I : Isa} (c : Ctx I) :
    Tree → Trie (List Nat) → RegionVarSet × Trie (List Nat)
  | .let_ _ ip _ _ op k, acc =>
    let ((ksK, mK), acc1) := buildRegionReused c k acc
    let both := k.lv.filter (mK.contains ·)
    let acc2 := if both.isEmpty then acc1 else acc1.insert ip both
    let rvs' :=
      if isCmpBitsCode op.code then (ksK, mK)
      else rvsAdd (ksK, mK) (c.addrDeps.getD ip (opVarIds op))
    (rvs', acc2)
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
    (rvsAdd (rvsInter vsT vsE) [cx], acc2)
  | .jump _ _ _ _ args, acc =>
    (rvsAdd ([], {}) (tupVarIds args), acc)
  | .call _ _ _ _ _ _ args k, acc =>
    let (_, acc1) := buildRegionReused c k acc
    (rvsAdd ([], {}) (tupVarIds args), acc1)
  | .ret _ _ _ args, acc | .exit _ _ _ _ args, acc =>
    (rvsAdd ([], {}) (tupVarIds args), acc)
  | .stop _, acc => (([], {}), acc)

private def buildRegionReusedB {I : Isa} (c : Ctx I) :
    TreeBlocks → Trie (List Nat) → Trie (List Nat)
  | .nil, acc => acc
  | .cons _ _ b bs, acc => buildRegionReusedB c bs (buildRegionReused c b acc).2
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
  let cinByLbl : Std.HashMap Nat (List (Nat × Nat × Bool × Nat)) :=
    cin.reverse.foldl (fun m (l, x, r, d, w) => m.insert l ((x, r, d, w) :: m.getD l [])) {}
  blocks.foldl (fun acc (l, ps, body) =>
    let es := cinByLbl.getD l []
    if es.isEmpty then acc
    else
      let wj := c.inW.getD l 0
      let busy0 := dedup (gprHomes home (c.lTrie.getD l [] ++ ps.map Prod.fst))
      let needPloc := countPlocGprs c home (fun p => slotOk.getD p false) ps
      let byVar : Std.HashMap Nat (List (Nat × Bool × Nat)) :=
        es.reverse.foldl (fun m (x, r, d, w) => m.insert x ((r, d, w) :: m.getD x [])) {}
      let (sel, _) := (dedup (es.map Prod.fst)).foldl (fun (sel, busy) x =>
        if !Nat.blt (busy.length + needPloc) gprBudget then (sel, busy)
        else
          let ex := byVar.getD x []
          let (rWeights, wd) := ex.foldl (fun (rw, dSum) (r, d, w) =>
            (rw.insert r (rw.getD r 0 + w), if d then dSum + w else dSum))
            (({} : Std.HashMap Nat Nat), 0)
          let regs := (dedup (ex.map Prod.fst)).filter fun r =>
            !natMem r busy && (Nat.ble (r + 1) c.nGpr || natMem r usedCs)
          let best := regs.foldl (fun (b : Option (Nat × Nat)) r =>
            let wr := rWeights.getD r 0
            match b with
            | some (_, bw) => if Nat.blt bw wr then some (r, wr) else b
            | none => some (r, wr)) none
          match best with
          | none => (sel, busy)
          | some (r, wc) =>
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
def evBodyCost {I : Isa} (c : Ctx I) (x : Nat) (isCaller : Bool) (evIn : Trie (List Nat)) :
    Nat → Tree → Nat × Nat
  | w, .let_ _ ip _ _ op k =>
    if natMem x (c.addrDeps.getD ip (opVarIds op)) then (w, 1)
    else evBodyCost c x isCaller evIn w k
  | w, .load _ ip _ _ a k =>
    if natMem x (c.addrDeps.getD ip (argVarIds a)) then (w, 1)
    else evBodyCost c x isCaller evIn w k
  | w, .store _ ip _ v a k =>
    if natMem x (storeVarIds c.addrDeps c.rmwDeps ip v a) then (w, 1)
    else evBodyCost c x isCaller evIn w k
  | w, .call _ _ _ _ _ _ args k =>
    if natMem x (tupVarIds args) then (w, 1)
    else if isCaller then (0, 0) else evBodyCost c x isCaller evIn w k
  | w, .jnz _ ip cx _ t e =>
    if Nat.beq cx x then (w, 1)
    else
      let (_, mT, mE) := c.brW.getD ip (w, w, w)
      let (cT, lT) := evBodyCost c x isCaller evIn mT t
      let (cE, lE) := evBodyCost c x isCaller evIn mE e
      let extra := match e with | .jump .. => if Nat.ble 1 cE then mT else 0 | _ => 0
      (cT + cE + extra, lT + lE)
  | w, .skip _ _ k | w, .group _ _ k => evBodyCost c x isCaller evIn w k
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
  let evByLbl : Std.HashMap Nat (List (Nat × Bool × Bool × Nat)) :=
    evArr.reverse.foldl (fun m (l, x, isEv, isSav, w) =>
      m.insert l ((x, isEv, isSav, w) :: m.getD l [])) {}
  blocks.foldl (fun acc (l, _, body) =>
    let es := evByLbl.getD l []
    if es.isEmpty then acc
    else
      let wj := c.inW.getD l 0
      let byVar : Std.HashMap Nat (Nat × Nat × Nat × Nat) :=
        es.foldl (fun m (x, isEv, isSav, w) =>
          let (wEv, nEv, wSav, nSav) := m.getD x (0, 0, 0, 0)
          let (wEv', nEv') := if isEv then (wEv + w, nEv + 1) else (wEv, nEv)
          let (wSav', nSav') := if isSav then (wSav + w, nSav + 1) else (wSav, nSav)
          m.insert x (wEv', nEv', wSav', nSav')) {}
      let sel := (dedup (es.map Prod.fst)).filter fun x =>
        match home.getD x .none with
        | .gpr r =>
          let (wEv, nEv, wSav, nSav) := byVar.getD x (0, 0, 0, 0)
          let (cost, leaves) := evBodyCost c x (Nat.blt r c.nGpr) prevEv wj body
          let leafOk := Nat.ble (nSav + leaves) nEv || Nat.ble (2 * (wSav + cost)) wEv
          Nat.ble 1 wEv && ((Nat.blt (wSav + cost) wEv && leafOk) ||
            (Nat.ble (leaves + 1) nEv && Nat.ble (wSav + cost) wEv))
        | _ => false
      let forced := c.forceEv.getD l []
      let sel' := forced.foldl (fun s x => if natMem x s then s else x :: s) sel
      if sel'.isEmpty then acc else acc.insert l sel') .empty

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

/-! ## `Base + ConstDisp` Rematerialization Oracle (untrusted) -/

/-- `true` when `I` rematerializes `rd := rb + disp` in 1 flag-preserving instruction for both
distinct (`rb ≠ rd`) and in-place (`rb = rd`) GPRs. -/
def remat1InsnOk (I : Isa) (disp : BitVec 64) : Bool :=
  match I.frame.allocatable with
  | r0 :: r1 :: _ =>
    (rematAddImm64 I r0 r1 disp).map (fun c => Nat.beq c.length 1) == some true &&
    (rematAddImm64 I r0 r0 disp).map (fun c => Nat.beq c.length 1) == some true
  | r0 :: [] =>
    (rematAddImm64 I r0 r0 disp).map (fun c => Nat.beq c.length 1) == some true
  | [] => false

structure RematDef where
  x : Nat
  ip : Nat
  base : Nat
  disp : BitVec 64

structure RematUse where
  ip : Nat
  dst? : Option Nat
  otherVars : List Nat
  isCmpEqImm : Bool
  isAdd64 : Bool
  isDirect : Bool
  isSlotOpOk : Bool
  isTerm : Bool
  isAddr : Bool
  addrTy? : Option Ty

structure RematScan where
  cands : List RematDef := []
  uses : Trie (List RematUse) := .empty
  bad : Trie Bool := .empty

def addRematUse (u : Nat) (ru : RematUse) (st : RematScan) : RematScan :=
  { st with uses := st.uses.insert u (ru :: st.uses.getD u []) }

def markRematBad (xs : List Nat) (st : RematScan) : RematScan :=
  { st with bad := xs.foldl (fun b x => b.insert x true) st.bad }

def opIsCmpEqImm64 {ts : List Ty} (op : Op VNat ts) : Bool :=
  let { sig := _, code, args } := op
  match code, args with
  | .cmp co (.bits 64) .bool _, (.var _, .imm _, ())
  | .cmp co (.bits 64) .bool _, (.imm _, .var _, ()) => co == .eq || co == .ne
  | _, _ => false

def opIsAdd64VV {ts : List Ty} (op : Op VNat ts) : Bool :=
  let { sig := _, code, args } := op
  match code, args with
  | .add (.bits 64), (.var _, .var _, ()) => true
  | _, _ => false

def opRematSlotOk (I : Isa) {ts : List Ty} (op : Op VNat ts) : Bool :=
  let { sig := _, code, args } := op
  match I.frame.allocatable.head?, code, args with
  | some r0, .cmp co (.bits 64) .bool _, (.var _, .var _, ()) =>
    I.supportsCmpMem i64 &&
    (I.gpr.cmpMem co 64 (.baseDisp I.frame.sp 0) (.gpr r0) (.gpr r0)).isSome &&
    (I.gpr.cmpMem co.swap 64 (.baseDisp I.frame.sp 0) (.gpr r0) (.gpr r0)).isSome
  | _, _, _ => false

mutual
def scanRematTree (I : Isa) (elideIps : Trie Bool) (addrDeps rmwDeps : Trie (List Nat))
    (defs : Trie DefFact) (st : RematScan) : Tree → RematScan
  | .let_ _ ip nv0 ts op k =>
    let df? := recordDef defs op.code op.args
    let defs1 := match df? with | some df => defs.insert nv0 df | none => defs
    if elideIps.getD ip false then
      scanRematTree I elideIps addrDeps rmwDeps defs1 st k
    else
      let st0 := match ts, df? with
        | [.bits 64], some (.addImm64 base disp) =>
          if remat1InsnOk I disp then
            { st with cands := ⟨nv0, ip, base, disp⟩ :: st.cands }
          else st
        | _, _ => st
      let st1 :=
        if (addrDeps.find? ip).isSome then
          markRematBad (addrDeps.getD ip []) st0
        else
          let vs := dedup (opVarIds op)
          let allGpr := ts.all (isGprTy I) && op.sig.all (isGprTy I)
          if !allGpr || !Nat.beq ts.length 1 then
            markRematBad vs st0
          else
            let isDir := match ts, df? with
              | [.bits 64], some (.addImm64 _ d') => remat1InsnOk I d'
              | _, _ => false
            let isCmpEq := opIsCmpEqImm64 op
            let isAdd := opIsAdd64VV op
            let isSlOk := opRematSlotOk I op
            vs.foldl (fun s u =>
              let oth := vs.filter (!Nat.beq · u)
              addRematUse u
                ⟨ip, some nv0, oth, isCmpEq, isAdd, isDir, isSlOk, false, false, none⟩ s) st0
      scanRematTree I elideIps addrDeps rmwDeps defs1 st1 k
  | .load _ ip _ t a k =>
    let st1 :=
      if elideIps.getD ip false || (addrDeps.find? ip).isSome then
        markRematBad (addrDeps.getD ip (argVarIds a)) st
      else match a with
        | .var u =>
          addRematUse u ⟨ip, none, [], false, false, false, false, false, true, some t⟩ st
        | .imm _ => st
    scanRematTree I elideIps addrDeps rmwDeps defs st1 k
  | .store _ ip t v a k =>
    let st0 := markRematBad (argVarIds v) st
    let st1 :=
      if (rmwDeps.find? ip).isSome || (addrDeps.find? ip).isSome then
        markRematBad (storeVarIds addrDeps rmwDeps ip v a) st0
      else match a with
        | .var u =>
          addRematUse u ⟨ip, none, [], false, false, false, false, false, true, some t⟩ st0
        | .imm _ => st0
    scanRematTree I elideIps addrDeps rmwDeps defs st1 k
  | .call _ ip _ _ _ _ args k =>
    let st1 := (dedup (tupVarIds args)).foldl (fun s u =>
      addRematUse u ⟨ip, none, [], false, false, false, false, true, false, none⟩ s) st
    scanRematTree I elideIps addrDeps rmwDeps defs st1 k
  | .jnz _ _ cx _ t e =>
    let st1 := scanRematTree I elideIps addrDeps rmwDeps defs (markRematBad [cx] st) t
    scanRematTree I elideIps addrDeps rmwDeps defs st1 e
  | .skip _ _ k => scanRematTree I elideIps addrDeps rmwDeps defs st k
  | .jump _ ip _ _ args | .ret _ ip _ args | .exit _ ip _ _ args =>
    (dedup (tupVarIds args)).foldl (fun s u =>
      addRematUse u ⟨ip, none, [], false, false, false, false, true, false, none⟩ s) st
  | .stop _ => st
  | .group _ bs k =>
    scanRematTree I elideIps addrDeps rmwDeps defs
      (scanRematBlocks I elideIps addrDeps rmwDeps defs st bs) k

def scanRematBlocks (I : Isa) (elideIps : Trie Bool) (addrDeps rmwDeps : Trie (List Nat))
    (defs : Trie DefFact) (st : RematScan) : TreeBlocks → RematScan
  | .nil => st
  | .cons _ _ b bs =>
    scanRematBlocks I elideIps addrDeps rmwDeps defs
      (scanRematTree I elideIps addrDeps rmwDeps defs st b) bs
end

def fillLiveRemat (lTrie : Trie (List Nat)) (addrDeps rmwDeps : Trie (List Nat))
    (rematRoot : Trie Nat) (t : Tree) : List Nat × Tree :=
  let (lv, _, t') := fillLiveAux lTrie addrDeps rmwDeps (mapRematVars rematRoot) t
  (lv, t')

def fillLiveRematB (lTrie : Trie (List Nat)) (addrDeps rmwDeps : Trie (List Nat))
    (rematRoot : Trie Nat) (bs : TreeBlocks) : TreeBlocks :=
  fillLiveAuxB lTrie addrDeps rmwDeps (mapRematVars rematRoot) bs

def liveLabelsRemat (bs0 : List (Nat × List (Nat × Ty) × Tree))
    (addrDeps rmwDeps : Trie (List Nat)) (rematRoot : Trie Nat) : Trie (List Nat) :=
  liveLabelsWith bs0 addrDeps rmwDeps (mapRematVars rematRoot)

def isGprHome {C : Type} (hT : Trie (Home C)) (x : Nat) : Bool :=
  match hT.getD x .none with | .gpr _ => true | _ => false

def isSlotHomeT {C : Type} (hT : Trie (Home C)) (x : Nat) : Bool :=
  match hT.getD x .none with | .slot _ _ => true | _ => false

def rematCandValid {I : Isa} (scan : RematScan) (hT : Trie (Home I.Cond))
    (bk : Trie (Nat × SlotWidth × Bool)) (cd : RematDef) : Bool :=
  isGprHome hT cd.base && (bk.find? cd.base).isNone &&
  (scan.uses.getD cd.x []).all fun u =>
    if u.isAddr then
      match u.addrTy? with | some ty => I.supportsAddrDisp ty cd.disp | none => false
    else if u.isTerm || u.isDirect || u.isCmpEqImm || u.isAdd64 || u.otherVars.isEmpty then true
    else if u.isSlotOpOk && u.otherVars.all (isSlotHomeT hT) then true
    else
      (match u.dst? with | some d => isGprHome hT d | none => false) &&
      u.otherVars.all fun ov => isGprHome hT ov || (u.isSlotOpOk && isSlotHomeT hT ov)

def selectRematCands {I : Isa} (scan : RematScan) (hT : Trie (Home I.Cond))
    (bk : Trie (Nat × SlotWidth × Bool)) : List RematDef :=
  let (sel, _) := scan.cands.reverse.foldl (fun (acc, chosen) cd =>
    if !isSlotHomeT hT cd.x || scan.bad.getD cd.x false || Nat.beq cd.x cd.base ||
       !isGprHome hT cd.base || (bk.find? cd.base).isSome || chosen.getD cd.base false then
      (acc, chosen)
    else
      let us := scan.uses.getD cd.x []
      let ok := !us.isEmpty && us.all fun u =>
        if u.isAddr then
          match u.addrTy? with | some ty => I.supportsAddrDisp ty cd.disp | none => false
        else if u.isTerm then true
        else
          !(u.otherVars.any fun ov => chosen.getD ov false) &&
          (u.isDirect || u.isCmpEqImm || u.isAdd64 || u.otherVars.isEmpty ||
            u.otherVars.all fun ov => isGprHome hT ov || (u.isSlotOpOk && isSlotHomeT hT ov))
      if ok then (cd :: acc, chosen.insert cd.x true) else (acc, chosen))
    ([], (.empty : Trie Bool))
  sel.reverse

def emitSlotMetrics {I : Isa} (ipW : Trie Nat) (st : EmitSt I) (nip : Nat) : Nat × Nat :=
  (List.range nip).foldl (fun (wCost, rawCnt) ip =>
    match st.pre.find? ip with
    | none => (wCost, rawCnt)
    | some ps =>
      let n := ps.moves.foldl (fun k mv =>
        match mv with
        | .st .. | .vst .. | .ld .. | .vld .. => k + 1
        | _ => k) 0
      if Nat.beq n 0 then (wCost, rawCnt)
      else (wCost + n * ipW.getD ip 1, rawCnt + n)) (0, 0)

mutual
def rewriteRematAddrDeps (rematRoot : Trie Nat) (addrDeps : Trie (List Nat)) :
    Tree → Trie (List Nat)
  | .let_ _ ip _ _ op k =>
    let ops := addrDeps.getD ip (opVarIds op)
    let ad1 := if ops.any fun u => (rematRoot.find? u).isSome then
        addrDeps.insert ip (mapRematVars rematRoot ops)
      else addrDeps
    rewriteRematAddrDeps rematRoot ad1 k
  | .load _ ip _ _ a k =>
    let ops := addrDeps.getD ip (argVarIds a)
    let ad1 := if ops.any fun u => (rematRoot.find? u).isSome then
        addrDeps.insert ip (mapRematVars rematRoot ops)
      else addrDeps
    rewriteRematAddrDeps rematRoot ad1 k
  | .store _ ip _ _ a k =>
    let ops := addrDeps.getD ip (argVarIds a)
    let ad1 := if ops.any fun u => (rematRoot.find? u).isSome then
        addrDeps.insert ip (mapRematVars rematRoot ops)
      else addrDeps
    rewriteRematAddrDeps rematRoot ad1 k
  | .call _ _ _ _ _ _ _ k | .skip _ _ k => rewriteRematAddrDeps rematRoot addrDeps k
  | .jnz _ _ _ _ t e =>
    rewriteRematAddrDeps rematRoot (rewriteRematAddrDeps rematRoot addrDeps t) e
  | .group _ bs k =>
    rewriteRematAddrDeps rematRoot (rewriteRematAddrDepsB rematRoot addrDeps bs) k
  | .jump .. | .ret .. | .exit .. | .stop _ => addrDeps

def rewriteRematAddrDepsB (rematRoot : Trie Nat) (addrDeps : Trie (List Nat)) :
    TreeBlocks → Trie (List Nat)
  | .nil => addrDeps
  | .cons _ _ b bs =>
    rewriteRematAddrDepsB rematRoot (rewriteRematAddrDeps rematRoot addrDeps b) bs
end

/-- Compute untrusted `Hints` for `Rega.lowerFn` via per-bank priority graph coloring.  -/
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
  let fnAbi := match I.assignArgs f.as with
    | some locs => abiIdList allGpr allVec locs | none => []
  let initZ32 : Trie Bool := fnPs.foldl (fun z (p, ty) =>
    if isGprTy I ty then z.insert p true else z) .empty
  -- Control-flow and bank invariants preserved across `rewriteCmpElide` remat reruns:
  let bsBase := t1.blocks
  let bparamsTrie := bsBase.foldl (fun a (l, ps, _) => a.insert l (ps.map Prod.fst)) .empty
  let bparamsSets : Std.HashMap Nat (Std.HashSet Nat) :=
    bsBase.foldl (fun m (l, ps, _) => m.insert l (hashSetOfList (ps.map Prod.fst))) {}
  let (loops, loopReach) := loopBlocksScoped (blocksWithMin t1)
  let loopHdrs := bsBase.filterMap fun (l, _, _) => if loops.getD l false then some l else none
  let blkLoops := loopHdrs.foldl (fun m lh =>
    (union [lh] (loopReach.getD lh [])).foldl (fun m b =>
      if natMem lh (m.getD b []) then m else triePush m b lh) m)
    (.empty : Trie (List Nat))
  let rec jmpLatch (dsts : Std.HashSet Nat) : Tree → Trie Bool → Trie Bool
    | .let_ _ _ _ _ _ k, m | .load _ _ _ _ _ k, m | .store _ _ _ _ _ k, m
    | .call _ _ _ _ _ _ _ k, m | .skip _ _ k, m | .group _ _ k, m => jmpLatch dsts k m
    | .jnz _ _ _ _ t e, m => jmpLatch dsts t (jmpLatch dsts e m)
    | .jump _ ip j _ _, m =>
      if dsts.contains j then m.insert ip true else m
    | _, m => m
  let latchIps := bsBase.foldl (fun m (l, _, body) =>
    let hdrs := blkLoops.getD l []
    if hdrs.isEmpty then m else jmpLatch (hashSetOfList hdrs) body m) .empty
  let gReg := (allGpr.foldl (fun (t, i) r => (t.insert i r, i + 1)) (.empty, 0)).1
  let vReg := (allVec.foldl (fun (t, i) v => (t.insert i v, i + 1)) (.empty, 0)).1
  let gAlloc := List.range nGpr
  let csIds := (List.range nCs).map (· + nGpr)
  let vAlloc := List.range nVec
  let gScr := if I.frame.scratch.isEmpty then none else some (nGpr + nCs)
  let vScr := if I.vec.vecScratch.isEmpty then none else some nVec
  let banksArr : Array Bank := (List.range nv).foldl
    (fun a x => a.push (bankOf I (tys.getD x i64))) (Array.mkEmpty nv)
  let banks := (List.range nv).foldl (fun b x => b.insert x (banksArr.getD x .gpr)) .empty
  let rootId := bsBase.foldl (fun m (l, _, _) => max m (l + 1)) 0
  let fnParamIds := fnPs.map Prod.fst
  let csCost := 2 * baseMult
  let colorPass (t1p : Tree) (adp : Trie (List Nat)) (useRemat : Bool) (rematRoot : Trie Nat)
      (rematOpIps : Trie Bool) (dropFlags : List Nat) :
      Tree × List (Nat × List (Nat × Ty) × Tree) × Ctx I × GatherAcc × FlagHints I.Cond ×
        ColorSt I.Cond × Trie (Home I.Cond) × Trie (List Nat) × Nat :=
    let bs0 := t1p.blocks
    let lTrie := if !useRemat then liveLabels bs0 adp rmwDeps
      else liveLabelsRemat bs0 adp rmwDeps rematRoot
    let (_, t) := if !useRemat then fillLive lTrie adp rmwDeps t1p
      else fillLiveRemat lTrie adp rmwDeps rematRoot t1p
    let tBlocks := t.blocks
    let crossList := acrossCalls t
    let crossTrie := crossList.foldl (fun a x => a.insert x true) .empty
    let isLeaf := crossList.isEmpty
    let fh0 := match I.frame.allocatable.head? with
      | some r0 =>
        let r1 := I.frame.allocatable[1]?.getD r0
        let v0 := I.vec.vecAllocatable.head?
        let v1 := I.vec.vecAllocatable[1]? <|> v0
        gatherFlags I r0 r1 v0 v1 condCands nv fnParamIds crossTrie bparamsTrie tys lTrie t
      | none => {}
    let fh := { fh0 with flagHome := dropFlags.foldl (fun m x => m.erase x) fh0.flagHome }
    let flagArr : Array Bool := (List.range nv).foldl
      (fun a x => a.push (fh.flagHome.find? x).isSome) (Array.mkEmpty nv)
    let c : Ctx I := {
      allGpr, allVec, gReg, vReg, nGpr, nVec, gAlloc, csIds, vAlloc, gScr, vScr,
      cross := crossTrie, loops, loopReach, blkLoops, banks, flagHome := fh.flagHome,
      bparams := bparamsTrie, lTrie, addrDeps := adp, rmwDeps, isLeaf, cfg, csCost,
      r0? := I.frame.allocatable.head?, latchIps }
    let regionReused := (buildRegionReused c t .empty).2
    let directVars : Tree → List Nat :=
      let rec go : Tree → List Nat → List Nat
        | .let_ _ ip nv0 ts op k, acc =>
          defVarsRange nv0 ts.length ++ (adp.getD ip (opVarIds op) ++ go k acc)
        | .load _ ip x _ a k, acc => x :: (adp.getD ip (argVarIds a) ++ go k acc)
        | .store _ ip _ v a k, acc => storeVarIds adp rmwDeps ip v a ++ go k acc
        | .call _ _ nv0 _ _ bs args k, acc =>
          defVarsRange nv0 bs.length ++ (mapRematVars rematRoot (tupVarIds args) ++ go k acc)
        | .jnz _ _ cx _ t e, acc => cx :: go t (go e acc)
        | .skip _ _ k, acc | .group _ _ k, acc => go k acc
        | .jump _ _ _ _ args, acc => mapRematVars rematRoot (tupVarIds args) ++ acc
        | .ret _ _ _ vs, acc | .exit _ _ _ _ vs, acc =>
          mapRematVars rematRoot (tupVarIds vs) ++ acc
        | .stop _, acc => acc
      (go · [])
    let rec jmpEdges (src : Nat) (w : Nat) : Tree → List (Nat × Nat × Nat × List Nat)
      | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k
      | .call _ _ _ _ _ _ _ k | .skip _ _ k | .group _ _ k => jmpEdges src w k
      | .jnz _ ip _ _ t e =>
        let (_, mT, mE) := c.brW.getD ip (w, w, w)
        jmpEdges src mT t ++ jmpEdges src mE e
      | .jump _ _ j _ args => [(src, j, w, mapRematVars rematRoot (tupVarIds args))]
      | _ => []
    let acc := gather c [] [] baseMult initZ32 t {} rematRoot rematOpIps banksArr flagArr
    let rootUses := directVars t
    let (blkUses, blkUsesSets) := tBlocks.foldl (fun (m, ms) (l, _, body) =>
      let us := directVars body
      (m.insert l us, ms.insert l (hashSetOfList us)))
      (Trie.empty.insert rootId rootUses,
        ({} : Std.HashMap Nat (Std.HashSet Nat)).insert rootId (hashSetOfList rootUses))
    let lTrieSets : Std.HashMap Nat (Std.HashSet Nat) := tBlocks.foldl (fun m (l, _, _) =>
      m.insert l (hashSetOfList (lTrie.getD l []))) {}
    let rootVars := union t.lv rootUses
    let varBlksArr0 := rootVars.foldl (fun a v => pushArr a v rootId) (Array.replicate nv [])
    let varBlksArr := tBlocks.foldl (fun a (l, ps, _) =>
      let vs := union (lTrie.getD l []) (union (ps.map Prod.fst) (blkUses.getD l []))
      vs.foldl (fun a v => pushArr a v l) a) varBlksArr0
    let c := { c with
      brW := acc.brW, zextElide := acc.zextElide, regionReused := regionReused, ipW := acc.ipW,
      jmpW := acc.jmpW, inW := acc.inW, blkUses := blkUses }
    let blkEdges := jmpEdges rootId baseMult t ++
      tBlocks.flatMap fun (l, _, body) => jmpEdges l (c.inW.getD l 0) body
    let (edgesBySrc, edgesByDst) := blkEdges.foldl (fun (bs, bd) e@(src, dst, _, _) =>
      (bs.insert src (e :: bs.getD src []), bd.insert dst (e :: bd.getD dst [])))
      (({} : Std.HashMap Nat (List (Nat × Nat × Nat × List Nat))),
       ({} : Std.HashMap Nat (List (Nat × Nat × Nat × List Nat))))
    let (arms, armT, varExtArr, useIpsArr, foldIpsSet) :=
      if !cfg.armEvict then ([], .empty, Array.replicate nv none, Array.replicate nv [], {})
      else
        let arms := collectArms c t []
        let ext0 := fnPs.foldl (fun e (p, _) => extendExtArr e p (firstIp t))
          (Array.replicate nv none)
        let (vext, uips) := varScanArr c t (ext0, Array.replicate nv [])
        (arms, arms.foldl (fun m a => m.insert a.key a) .empty, vext, uips, foldIpsSetT t {})
    let c := { c with armT := armT }
    let (cs, wTrie) := colorVarsFast c nv banksArr fh.flagHome acc fnParamIds fnAbi
      arms varExtArr useIpsArr foldIpsSet lTrieSets blkUsesSets bparamsSets
      edgesBySrc edgesByDst varBlksArr
    let armVars := (List.range nv).filterMap fun x => (cs.armEv.find? x).map (x, ·)
    let armEvAt : Trie (List Nat) := armVars.foldl (fun m (x, ks) =>
      ks.foldl (fun m k => triePush m k x) m) .empty
    let fe0 := armVars.foldl (fun t (x, ks) => ks.foldl (fun t k =>
      match c.armT.find? k with
      | some a =>
        a.blocks.foldl (fun t b =>
          if (lTrieSets.getD b {}).contains x then triePush t b x else t) t
      | none => t) t) cs.forceEv
    let (hT, fe, nslots1) :=
      fitBlockGprs c wTrie cs.bk cs.usedCs cs.nslots cs.hT fe0 t tBlocks
    let c := { c with hintT := cs.hint, forceEv := fe, evIn := fe, armEvAt := armEvAt }
    (t, tBlocks, c, acc, fh, cs, hT, fe, nslots1)
  let emitWithRefine (res : Tree × List (Nat × List (Nat × Ty) × Tree) × Ctx I × GatherAcc ×
      FlagHints I.Cond × ColorSt I.Cond × Trie (Home I.Cond) × Trie (List Nat) × Nat) :
      EmitSt I × Nat × Ctx I × GatherAcc × FlagHints I.Cond :=
    let (t, tBlocks, c, acc, fh, cs, hT, _, nslots1) := res
    let slotOk := slotPlocMap c hT cs.bk cs.usedCs acc.defWT t tBlocks
    let r0? := I.frame.allocatable.head?
    let r1? := I.frame.allocatable[1]?
    let initSv := fnParamIds.filter (isEagerBk cs.bk)
    let emit (c : Ctx I) : EmitSt I := emitAlloc c hT cs.bk slotOk fh.clearAt r0? r1? t
      (pendFromArrivals hT cs.bk fnParamIds fnAbi) [] initSv [] []
      { variant := fh.variant, usedCs := cs.usedCs }
    let c := { c with jmpW := acc.jmpW, inW := acc.inW, addrDeps := addrDeps }
    let refine (c : Ctx I) : Ctx I :=
      let stO := emit { c with opt := true }
      let rin := pickRegIn c hT cs.usedCs slotOk stO.cin tBlocks
      let evi := pickEvIn c hT stO.evArr c.evIn tBlocks
      let lp := stO.latchArr.foldl (fun t (p, r, w) => triePush t p (r, w)) .empty
      { c with regIn := rin, evIn := evi, latchPrefs := lp }
    let c := if cfg.regEntry && cfg.sink then refine (refine c) else c
    let st := emit c
    let finalSlots :=
      if I.frame.scratch.isEmpty then nslots1 else min nslots1 (usedSlotCount nip nl st)
    (st, finalSlots, c, acc, fh)
  let baseRes := colorPass t1 addrDeps false .empty .empty []
  let (_, _, _, acc1, _, cs1, hT1, _, _) := baseRes
  let scan := scanRematTree I elideIps addrDeps rmwDeps .empty {} t0
  let sel0 := selectRematCands scan hT1 cs1.bk
  let (stBase, slotsBase, cBase, accBase, fhBase) := emitWithRefine baseRes
  let (elideIps, st, finalSlots, c, acc, fh) :=
    if sel0.isEmpty then
      (elideIps, stBase, slotsBase, cBase, accBase, fhBase)
    else
      let (wBase, cntBase) := emitSlotMetrics acc1.ipW stBase nip
      let evalSel (sel : List RematDef) :
          Option (Trie Bool × EmitSt I × Nat × Ctx I × GatherAcc × FlagHints I.Cond × Nat × Nat) :=
        let rec evalLoop : Nat → List RematDef →
            Option (Trie Bool × EmitSt I × Nat × Ctx I × GatherAcc × FlagHints I.Cond × Nat × Nat)
          | 0, _ | _, [] => none
          | fuel + 1, cur =>
            let rRoot := cur.foldl (fun m cd => m.insert cd.x cd.base) (.empty : Trie Nat)
            let elide2 := cur.foldl (fun m cd => m.insert cd.ip true) elideIps
            let t1p := rewriteCmpElide elide2 t1
            let adp := rewriteRematAddrDeps rRoot addrDeps t1p
            let (remOpIps, dropFl) := cur.foldl (fun (oi, df) cd =>
              (scan.uses.getD cd.x []).foldl (fun (oi, df) u =>
                if u.isAddr || u.isTerm then (oi, df)
                else
                  let oi' := if !u.isDirect && !u.isCmpEqImm && !u.isAdd64 && !u.otherVars.isEmpty
                    then oi.insert u.ip true else oi
                  let df' := if !u.isCmpEqImm then
                      match u.dst? with | some d => d :: df | none => df
                    else df
                  (oi', df')) (oi, df)) (.empty, [])
            let res2 := colorPass t1p adp true rRoot remOpIps dropFl
            let (_, _, _, acc2, _, cs2, hT2, _, _) := res2
            let cur' := cur.filter (rematCandValid scan hT2 cs2.bk)
            if Nat.beq cur'.length cur.length then
              let (st2, slots2, c2, acc2', fh2) := emitWithRefine res2
              let (w2, cnt2) := emitSlotMetrics acc2.ipW st2 nip
              let better :=
                (Nat.ble (w2 + 1) wBase || (Nat.beq w2 wBase && Nat.ble (slots2 + 1) slotsBase)) &&
                Nat.ble cnt2 cntBase && Nat.ble slots2 slotsBase
              if better then some (elide2, st2, slots2, c2, acc2', fh2, w2, cnt2) else none
            else evalLoop fuel cur'
        evalLoop 3 sel
      match evalSel sel0 with
      | some (el2, st2, sl2, c2, a2, fh2, _, _) => (el2, st2, sl2, c2, a2, fh2)
      | none =>
        if Nat.ble sel0.length 1 then
          (elideIps, stBase, slotsBase, cBase, accBase, fhBase)
        else
          let best := sel0.foldl (fun accBest cd =>
            match evalSel [cd] with
            | none => accBest
            | some r@(_, _, sl, _, _, _, w, cnt) =>
              match accBest with
              | none => some r
              | some (_, _, bsl, _, _, _, bw, bcnt) =>
                if Nat.ble (w + 1) bw ||
                   (Nat.beq w bw && (Nat.ble (cnt + 1) bcnt ||
                     (Nat.beq cnt bcnt && Nat.ble (sl + 1) bsl))) then
                  some r
                else accBest) none
          match best with
          | some (el2, st2, sl2, c2, a2, fh2, _, _) => (el2, st2, sl2, c2, a2, fh2)
          | none => (elideIps, stBase, slotsBase, cBase, accBase, fhBase)
  let h0 : I.Hints :=
    { dest := st.dest, entry := st.entry, pre := st.pre, variant := st.variant, elide := elideIps,
      invertJnz := acc.invertJnz, deadFlags := fh.deadFlags,
      nslots := finalSlots, saved := st.usedCs.map fun r => c.gReg.getD r I.frame.sp }
  Rega.addDeferHints h0 f

end Spill
end LeanQbe.T
