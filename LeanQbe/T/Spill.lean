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

mutual
def gatherAt {I : Isa} (c : Ctx I) (blk? : Option Nat)
    (rematRoot : Trie Nat := .empty) (rematOpIps : Trie Bool := .empty) :
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
    let isRemOp := rematOpIps.getD ip false
    let di := defs.foldl (fun d x =>
      if isRemOp then (x, union defs (union (laFor x) uses)) :: d
      else if natMem x la || Nat.ble 2 defs.length then (x, union defs (laFor x)) :: d else d)
      acc.defInterf
    let (gLv, vLv) := splitBank c.banks c.flagHome lv
    let (gLa, vLa) := splitBank c.banks c.flagHome la
    let (gUse, vUse) := splitBank c.banks c.flagHome uses
    let (gDef, vDef) := splitBank c.banks c.flagHome defs
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
    gatherAt c blk? rematRoot rematOpIps lps lr mult isZ32' k { acc with
      ipW := acc.ipW.insert ip mult,
      weights := (mult, defs ++ uses) :: acc.weights, defInterf := di, affEdges := aff,
      gprPts := gPts, gprPtBlks := gBlks, gprPtIps := gIps, vecPts := vPts, defWT := dw,
      zextElide := ze,
      zextEdges := zed }
  | lps, lr, mult, isZ32, .load lv ip x t a k, acc =>
    let la := k.lv
    let uses := dedup (c.addrDeps.getD ip (argVarIds a))
    let di := if natMem x la then (x, la) :: acc.defInterf else acc.defInterf
    let (gLv, _) := splitBank c.banks c.flagHome lv
    let (gLa, vLa) := splitBank c.banks c.flagHome la
    let (gUse, _) := splitBank c.banks c.flagHome uses
    let (gDef, vDef) := splitBank c.banks c.flagHome [x]
    let (gPts1, gBlks1, gIps1) := addGprPtBlk blk? ip c.nGpr gUse (eraseMany gUse gLv)
      acc.gprPts acc.gprPtBlks acc.gprPtIps
    let (gPts, gBlks, gIps) :=
      addGprPtBlk blk? ip c.nGpr gDef (eraseMany gDef gLa) gPts1 gBlks1 gIps1
    let vPts := addVecPt c.nVec vDef.length (eraseMany vDef vLa) acc.vecPts
    let isZ32' :=
      if (I.gpr.zeroExtLoad && isGprTy I t) || (I.gpr.zeroUpper32Load && tyEq t (.bits 32)) then
        isZ32.insert x true
      else isZ32
    gatherAt c blk? rematRoot rematOpIps lps lr mult isZ32' k { acc with
      ipW := acc.ipW.insert ip mult,
      weights := (mult, x :: uses) :: acc.weights, defInterf := di,
      gprPts := gPts, gprPtBlks := gBlks, gprPtIps := gIps, vecPts := vPts,
      defWT := acc.defWT.insert x mult }
  | lps, lr, mult, isZ32, .store lv ip _ v a k, acc =>
    let uses := storeVarIds c.addrDeps c.rmwDeps ip v a
    let (gLv, vLv) := splitBank c.banks c.flagHome lv
    let (gUse, vUse) := splitBank c.banks c.flagHome uses
    let (gPts, gBlks, gIps) := addGprPtBlk blk? ip c.nGpr gUse (eraseMany gUse gLv)
      acc.gprPts acc.gprPtBlks acc.gprPtIps
    gatherAt c blk? rematRoot rematOpIps lps lr mult isZ32 k { acc with
      ipW := acc.ipW.insert ip mult,
      weights := addWeight mult uses acc.weights, gprPts := gPts, gprPtBlks := gBlks,
      gprPtIps := gIps,
      vecPts := addVecPt c.nVec vUse.length (eraseMany vUse vLv) acc.vecPts }
  | lps, lr, mult, isZ32, .call _ ip nv0 _ as bs args k, acc =>
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
    gatherAt c blk? rematRoot rematOpIps lps lr mult isZ32' k { acc with
      ipW := acc.ipW.insert ip mult,
      weights := addWeight mult (defs ++ mapRematVars rematRoot (tupVarIds args)) acc.weights,
      defInterf := di,
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
    let (gPts, gBlks, gIps) := addGprPtBlk blk? ip c.nGpr gUse (eraseMany gUse gLv)
      acc.gprPts acc.gprPtBlks acc.gprPtIps
    let acc1 := gatherAt c blk? rematRoot rematOpIps lps lr mE isZ32 e { acc with
      weights := (mult, [cx]) :: acc.weights, gprPts := gPts, gprPtBlks := gBlks,
      gprPtIps := gIps,
      brW := acc.brW.insert ip (mult, mT, mE),
      invertJnz := if Nat.blt mE mT then acc.invertJnz.insert ip true else acc.invertJnz }
    gatherAt c blk? rematRoot rematOpIps lps lr mT isZ32 t acc1
  | lps, lr, mult, isZ32, .skip _ _ k, acc =>
    gatherAt c blk? rematRoot rematOpIps lps lr mult isZ32 k acc
  | lps, _, mult, _, .jump _ ip j _ args, acc =>
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
        addJumpAffAnti (natMem j lps) lps.length as ps mult acc.affEdges acc.antiEdges
      else
        (addAffZip as ps (8 * mult) acc.affEdges, addAntiZip as ps (2 * mult) acc.antiEdges)
    { acc with weights := addWeight mult nonSelf acc.weights,
               affEdges := aff', antiEdges := anti' }
  | _, _, mult, _, .ret _ ip rs vs, acc =>
    let (ag, av) := match I.assignRets rs with
      | some locs =>
        addAbiArgs (tupArgsToList vs) (abiIdList c.allGpr c.allVec locs) (4 * mult)
          acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    { acc with weights := addWeight mult (mapRematVars rematRoot (tupVarIds vs)) acc.weights,
               abiGpr := ag, abiVec := av, ipW := acc.ipW.insert ip mult }
  | _, _, mult, _, .exit _ ip _ as args, acc =>
    let (ag, av) := match I.assignArgs as with
      | some locs =>
        addAbiArgs (tupArgsToList args) (abiIdList c.allGpr c.allVec locs) (4 * mult)
          acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    { acc with weights := addWeight mult (mapRematVars rematRoot (tupVarIds args)) acc.weights,
               abiGpr := ag, abiVec := av, ipW := acc.ipW.insert ip mult }
  | _, _, _, _, .stop _, acc => acc
  | lps, lr, mult, isZ32, .group _ bs k, acc =>
    gatherAtB c rematRoot rematOpIps lps lr mult bs
      (gatherAt c blk? rematRoot rematOpIps lps lr mult isZ32 k acc)

def gatherAtB {I : Isa} (c : Ctx I) (rematRoot : Trie Nat := .empty)
    (rematOpIps : Trie Bool := .empty) :
    List Nat → List Nat → Nat → TreeBlocks → GatherAcc → GatherAcc
  | _, _, _, .nil, acc => acc
  | lps, lr, mult, .cons l ps b bs, acc =>
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
    let dw := pvars.foldl (fun t p => t.insert p mB) acc.defWT
    let bp := pvars.foldl (fun t p => t.insert p true) acc.isBP
    let pW := if !lps'.isEmpty then max (baseMult / 4) (mB / 4) else baseMult / 4
    gatherAtB c rematRoot rematOpIps lps lr mult bs
      (gatherAt c (some l) rematRoot rematOpIps lps' lr' mB .empty b { acc with
        weights := addWeight pW pvars acc.weights,
        defInterf := di, defWT := dw, isBP := bp })
end

def gather {I : Isa} (c : Ctx I) (lps lr : List Nat) (mult : Nat) (isZ32 : Trie Bool)
    (t : Tree) (acc : GatherAcc) (rematRoot : Trie Nat := .empty)
    (rematOpIps : Trie Bool := .empty) : GatherAcc :=
  gatherAt c none rematRoot rematOpIps lps lr mult isZ32 t acc

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
/-- All non-trivial `jnz` arms and blocks of a tree (see `ArmInfo`). -/
def collectArms {I : Isa} (c : Ctx I) : Tree → List ArmInfo → List ArmInfo
  | .let_ _ _ _ _ _ k, acc | .load _ _ _ _ _ k, acc | .store _ _ _ _ _ k, acc
  | .call _ _ _ _ _ _ _ k, acc | .skip _ _ k, acc => collectArms c k acc
  | .jnz _ ip _ _ t e, acc =>
    let (_, mT, mE) := c.brW.getD ip (0, 0, 0)
    let mk (key w : Nat) (a : Tree) : List ArmInfo :=
      if isTrivialTerm a then []
      else
        let (m, ls, js) := subInfo a
        let exits := js.filterMap fun (jip, j, args) =>
          if natMem j ls then none else some (jip, j, c.jmpW.getD jip 0, args)
        [{ key, lo := firstIp a, hi := m + 1, w, liveIn := a.lv, exits, blocks := ls }]
    collectArms c t (collectArms c e (mk (2 * ip + 1) mT t ++ mk (2 * ip) mE e ++ acc))
  | .group _ bs k, acc => collectArmsB c bs (collectArms c k acc)
  | .jump .., acc | .ret .., acc | .exit .., acc | .stop _, acc => acc

def collectArmsB {I : Isa} (c : Ctx I) : TreeBlocks → List ArmInfo → List ArmInfo
  | .nil, acc => acc
  | .cons l _ b bs, acc =>
    -- A loop (header block with the blocks nested in it) is a region too: entered by the
    -- jumps to `l` from outside, left by the jumps to labels declared outside it.
    let blk : List ArmInfo :=
      if !c.cfg.armLoops || isTrivialTerm b || !c.loops.getD l false then []
      else
        let (m, ls, js) := subInfo b
        let inside := l :: ls
        let exits := js.filterMap fun (jip, j, args) =>
          if natMem j inside then none else some (jip, j, c.jmpW.getD jip 0, args)
        let backW := js.foldl (fun n (jip, j, _) =>
          if Nat.beq j l then n + c.jmpW.getD jip 0 else n) 0
        [{ key := blockArmKey l, lo := firstIp b, hi := m + 1, w := c.inW.getD l 0 - backW,
           liveIn := c.lTrie.getD l [], exits, blocks := inside }]
    collectArmsB c bs (collectArms c b (blk ++ acc))
end

def extendExt (e : Trie (Nat × Nat)) (x ip : Nat) : Trie (Nat × Nat) :=
  match e.find? x with
  | some (lo, hi) => e.insert x (min lo ip, max hi ip)
  | none => e.insert x (ip, ip)

def scanNode (ip : Nat) (lv defs uses : List Nat) (acc : Trie (Nat × Nat) × Trie (List Nat)) :
    Trie (Nat × Nat) × Trie (List Nat) :=
  ((lv ++ defs ++ uses).foldl (fun e x => extendExt e x ip) acc.1,
   uses.foldl (fun u x => u.insert x (ip :: u.getD x [])) acc.2)

mutual
/-- Per variable: ip extent `(lo, hi)` of its definition and live range, and the ips that use it. -/
def varScan {I : Isa} (c : Ctx I) :
    Tree → Trie (Nat × Nat) × Trie (List Nat) → Trie (Nat × Nat) × Trie (List Nat)
  | .let_ lv ip nv0 ts op k, acc =>
    varScan c k (scanNode ip lv ((List.range ts.length).map (nv0 + ·))
      (c.addrDeps.getD ip (opVarIds op)) acc)
  | .load lv ip x _ a k, acc =>
    varScan c k (scanNode ip lv [x] (c.addrDeps.getD ip (argVarIds a)) acc)
  | .store lv ip _ v a k, acc =>
    varScan c k (scanNode ip lv [] (storeVarIds c.addrDeps c.rmwDeps ip v a) acc)
  | .call lv ip nv0 _ _ bs args k, acc =>
    varScan c k (scanNode ip lv ((List.range bs.length).map (nv0 + ·)) (tupVarIds args) acc)
  | .jnz lv ip cx _ t e, acc => varScan c t (varScan c e (scanNode ip lv [] [cx] acc))
  | .skip lv ip k, acc => varScan c k (scanNode ip lv [] [] acc)
  | .jump lv ip _ _ args, acc => scanNode ip lv [] (tupVarIds args) acc
  | .ret lv ip _ vs, acc => scanNode ip lv [] (tupVarIds vs) acc
  | .exit lv ip _ _ args, acc => scanNode ip lv [] (tupVarIds args) acc
  | .stop _, acc => acc
  | .group _ bs k, acc => varScanB c bs (varScan c k acc)

def varScanB {I : Isa} (c : Ctx I) :
    TreeBlocks → Trie (Nat × Nat) × Trie (List Nat) → Trie (Nat × Nat) × Trie (List Nat)
  | .nil, acc => acc
  | .cons _ ps b bs, acc =>
    let fi := firstIp b
    varScanB c bs (varScan c b (ps.foldl (fun a (p, _) => (extendExt a.1 p fi, a.2)) acc))
end

def isCmpBitsCode {sig ts : List Ty} : OpCode sig ts → Bool
  | .cmp _ (.bits _) .bool _ => true
  | _ => false

mutual
/-- Ips of compares and branches, whose spilled operands `Rega` reads from the slot directly. -/
def foldIpsT : Tree → Trie Unit → Trie Unit
  | .let_ _ ip _ _ op k, acc => foldIpsT k (if isCmpBitsCode op.code then acc.insert ip () else acc)
  | .load _ _ _ _ _ k, acc | .store _ _ _ _ _ k, acc | .call _ _ _ _ _ _ _ k, acc
  | .skip _ _ k, acc => foldIpsT k acc
  | .jnz _ ip _ _ t e, acc => foldIpsT t (foldIpsT e (acc.insert ip ()))
  | .group _ bs k, acc => foldIpsTB bs (foldIpsT k acc)
  | .jump .., acc | .ret .., acc | .exit .., acc | .stop _, acc => acc

def foldIpsTB : TreeBlocks → Trie Unit → Trie Unit
  | .nil, acc => acc
  | .cons _ _ b bs, acc => foldIpsTB bs (foldIpsT b acc)
end

/-- `y` lives entirely inside arm `a` and is not an argument of a jump leaving it. -/
def armInterior (a : ArmInfo) (ext : Trie (Nat × Nat)) (y : Nat) : Bool :=
  match ext.find? y with
  | some (lo, hi) =>
    Nat.ble a.lo lo && Nat.blt hi a.hi && !(a.exits.any fun (_, _, _, as) => natMem y as)
  | none => false

/-- `owner` is arm-evicted in an arm that `y` lives entirely inside. -/
def armShare {I : Isa} (c : Ctx I) (armEv : Trie (List Nat)) (owner y : Nat) : Bool :=
  match armEv.find? owner with
  | none => false
  | some ks => ks.any fun k => match c.armT.find? k with
    | some a => armInterior a c.varExt y
    | none => false

/-- Try to give a non-call-crossing GPR `x` a register by evicting it in the smallest set of
maximal arms that contain every conflicting holder of that register (and every exhausted
caller-saved pressure point). Accepted when the eviction cost (backup store plus weighted exit
reloads) beats spilling. -/
def tryArmEvict {I : Isa} (c : Ctx I) (x : Nat) (xI pids cpids : List Nat) (ptIps : Array Nat)
    (forbBkSlots : List (Nat × Nat)) (isBp isX : Bool) (dw cw csThresh wx : Nat)
    (s : ColorSt I.Cond) : Option (ColorSt I.Cond) :=
  if !c.cfg.armEvict || !Nat.ble (2 * baseMult) wx then none
  else
    let uses := c.useIps.getD x []
    let inA (a : ArmInfo) (ip : Nat) : Bool := Nat.ble a.lo ip && Nat.blt ip a.hi
    let cand := c.armList.filter fun a =>
      natMem x a.liveIn && uses.all fun u =>
        !inA a u || a.exits.any fun (jip, _, _, _) => Nat.beq jip u
    if cand.isEmpty then none
    else
      let pick (p : ArmInfo → Bool) : Option ArmInfo :=
        cand.foldl (fun best a =>
          if p a then
            match best with
            | some b => if Nat.blt (b.hi - b.lo) (a.hi - a.lo) then some a else best
            | none => some a
          else best) none
      let addArm (as : List ArmInfo) (a : ArmInfo) : List ArmInfo :=
        if as.any (fun b => Nat.beq b.key a.key) then as else a :: as
      let newCs := if Nat.ble csThresh wx then c.csIds.filter (!natMem · s.usedCs) else []
      let evalReg (r : Nat) : Option (Nat × List ArmInfo × Bool) :=
        let isCaller := Nat.blt r c.nGpr
        let confl := xI.filter fun y => match s.hT.getD y .none with
          | .gpr ry => Nat.beq ry r && !armShare c s.armEv y x
          | _ => false
        let zeroPts := if isCaller then pids.filter fun p => !Nat.ble 1 (s.gPb.getD p 0) else []
        if confl.isEmpty && zeroPts.isEmpty then none
        else
          let need1 := confl.foldl (fun acc y => acc.bind fun as =>
            (pick fun a => armInterior a c.varExt y).map (addArm as ·)) (some [])
          let need := zeroPts.foldl (fun acc p => acc.bind fun as =>
            (pick fun a => inA a (ptIps[p]?.getD 0)).map (addArm as ·)) need1
          need.bind fun as0 =>
            let as := as0.filter fun a => !as0.any fun b =>
              !Nat.beq b.key a.key && Nat.ble b.lo a.lo && Nat.ble a.hi b.hi
            if as.isEmpty then none
            else
              let entryW := as.foldl (fun n a => n + a.w) 0
              let exitW := as.foldl (fun n a => a.exits.foldl (fun n2 (_, j, w, args) =>
                if natMem x (c.lTrie.getD j []) || natMem x args then n2 + w else n2) n) 0
              -- A call-crossing `x` in a caller-saved register is also split around its calls.
              let callW := if isX && isCaller then cw else 0
              let eager := !isBp && Nat.ble dw (entryW + callW)
              -- Each arm execution leaves it at most once: cap the (statically inflated) exits.
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
        -- Reloads saved: the weight of the uses of `x` outside the evicted arms.
        let usesOut := uses.foldl (fun n u =>
          if as.any (inA · u) || trieMem c.foldIps u then n
          else n + (c.ipW.find? u <|> (c.brW.find? u).map (·.1) <|> c.jmpW.find? u).getD 0) 0
        if !Nat.ble (2 * cost + baseMult) usesOut then none
        else
          let isCaller := Nat.blt r c.nGpr
          let outside := pids.filter fun p => !as.any fun a => inA a (ptIps[p]?.getD 0)
          let bSlot := firstFreeSlotRange 1 forbBkSlots
          some { s with
            hT := s.hT.insert x (.gpr r),
            usedCs := if !isCaller && !natMem r s.usedCs then s.usedCs ++ [r] else s.usedCs,
            gPb := if isCaller then decPts outside s.gPb else incPts cpids s.gPb,
            bk := s.bk.insert x (bSlot, .w64, eager),
            nslots := max s.nslots (bSlot + 1),
            armEv := s.armEv.insert x (as.map (·.key)) }

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
          let lhdrs :=
            if c.cfg.backEdgeCoal then c.blkLoops.getD b []
            else if c.loops.getD b false then [b] else []
          lhdrs.foldl (fun acc lh =>
            (union [lh] (c.loopReach.getD lh [])).foldl (fun a b2 =>
              if !natMem b2 a && natMem x (c.lTrie.getD b2 []) &&
                  !natMem x (c.blkUses.getD b2 []) &&
                  !(isBp && natMem x (c.bparams.getD b2 [])) then b2 :: a
              else a) acc) acc) []
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
            let minUses := 8
            let maxExits := 1
            let outPbOk := pidsOut.all (fun p => Nat.ble 2 (s.gPb.getD p 0)) ||
              Nat.ble minUses usesOut
            if !outPbOk || !Nat.ble 1 wEnter || !Nat.ble (evCost + baseMult) slotCost ||
                !Nat.ble nExit maxExits || !Nat.ble minUses usesOut ||
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

/-- Split a spilled GPR variable `x` across multi-block inner loops where `x` is live-in but
completely unused: evict `x` to a backup slot on loop entry and reload on loop exits so `x`
keeps a GPR outside while freeing that GPR for hot inner-loop variables. -/
def tryLoopBoundarySplit {I : Isa} (c : Ctx I) (x : Nat) (xI pids : List Nat)
    (ptBlks : Array (Option Nat)) (forbBkSlots : List (Nat × Nat))
    (prefs avoid : List (Nat × Nat)) (isBp isX : Bool) (dw cw wx _slotCost : Nat)
    (s : ColorSt I.Cond) : Option (ColorSt I.Cond) :=
  if !(c.cfg.regEntry && c.cfg.sink && c.cfg.armEvict && c.cfg.armLoops && c.cfg.backEdgeCoal) ||
      !Nat.ble (2 * baseMult) wx || (isX && !c.cfg.armX) then none
  else
    let unusedLoops := (c.varBlks.getD x []).filter fun b =>
      c.loops.getD b false && natMem x (c.lTrie.getD b []) &&
        let rch := union [b] (c.loopReach.getD b [])
        rch.all fun b2 =>
          !natMem x (c.blkUses.getD b2 []) && !(isBp && natMem x (c.bparams.getD b2 []))
    if unusedLoops.isEmpty then none
    else
      let evBlks := unusedLoops.foldl (fun acc lh =>
        union (union [lh] (c.loopReach.getD lh [])) acc) []
      let inEvBlk (p : Nat) : Bool := match ptBlks[p]? with
        | some (some b) => natMem b evBlks | _ => false
      let pidsOut := pids.filter (!inEvBlk ·)
      let callerOk := pidsOut.all fun p => Nat.ble 1 (s.gPb.getD p 0)
      let nEnter := c.blkEdges.foldl (fun a (src, dst, _, _) =>
        if !natMem src evBlks && natMem dst evBlks &&
            natMem x (c.lTrie.getD dst []) then a + 1 else a) 0
      let wEnter := c.blkEdges.foldl (fun a (src, dst, w, _) =>
        if !natMem src evBlks && natMem dst evBlks &&
            natMem x (c.lTrie.getD dst []) then a + w else a) 0
      let wExit := c.blkEdges.foldl (fun a (src, dst, w, args) =>
        if natMem src evBlks && !natMem dst evBlks &&
            (natMem x (c.lTrie.getD dst []) || natMem x args) then a + w else a) 0
      let nExit := c.blkEdges.foldl (fun a (src, dst, _, args) =>
        if natMem src evBlks && !natMem dst evBlks &&
            (natMem x (c.lTrie.getD dst []) || natMem x args) then a + 1 else a) 0
      let uses := (c.useIps.getD x []).filter (!trieMem c.foldIps ·)
      let usesOut := uses.length
      let usesOutW := uses.foldl (fun n u =>
        n + (c.ipW.find? u <|> (c.brW.find? u).map (·.1) <|> c.jmpW.find? u).getD 0) 0
      let baseOps := (if isBp then 0 else 1) + usesOut
      if !Nat.ble 1 wEnter || !Nat.ble nExit 4 || Nat.beq usesOut 0 then none
      else
        let exitArgs := c.blkEdges.foldl (fun a (src, dst, _, args) =>
          if natMem src evBlks && !natMem dst evBlks then args ++ a else a) []
        let isInterior (y : Nat) : Bool :=
          let ybs := c.varBlks.getD y []
          !ybs.isEmpty && !natMem y exitArgs && ybs.all (natMem · evBlks)
        let forbOut := xI.foldl (fun rs y =>
          if isInterior y then rs
          else match s.hT.getD y .none with
            | .gpr r => if natMem r rs then rs else r :: rs | _ => rs) []
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
          (((if callerOk then c.gAlloc else []) ++ s.usedCs).filter (!natMem · forbOut)).filter
            fun r => (evalReg r).isSome
        match bestRegPref prefs avoid cands with
        | none => none
        | some r =>
          let isCaller := Nat.blt r c.nGpr
          let canEagerEv := (evalReg r).getD false
          let bSlot := firstFreeSlotRange 1 forbBkSlots
          let fe := evBlks.foldl (fun t b => triePush t b x) s.forceEv
          some { s with
            hT := s.hT.insert x (.gpr r),
            gPb := if isCaller then decPts pidsOut s.gPb else s.gPb,
            bk := s.bk.insert x (bSlot, .w64, canEagerEv),
            nslots := max s.nslots (bSlot + 1),
            forceEv := fe }

/-- Color one variable `x` of weight `wx` and call-crossing weight `cw`. A call-crossing GPR
prefers an already-saved CS register; if splitting beats both saving a new CS register and spilling
(`cheapSplit`), it splits into a caller-saved register (cold-branch shrink-wrapping); otherwise it
tries a fresh CS register, then falls back to splitting (`splitOk`, using eager def-site backup
when `defW < cw` so loop-invariant vars pay zero stores inside loops) before spilling to a slot. -/
def colorOne {I : Isa} (c : Ctx I) (interf : Trie (List Nat)) (gVp gCp vVp : Trie (List Nat))
    (abiGT abiVT affT antiT : Trie (List (Nat × Nat))) (cwT defWT : Trie Nat)
    (_loopCall isBP : Trie Bool) (zextPeers : Trie (List Nat)) (fnParams : List Nat)
    (ptBlks : Array (Option Nat)) (ptIps : Array Nat) (s : ColorSt I.Cond) (wx x : Nat) :
    ColorSt I.Cond :=
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
  let cheapSplit := isX && splitOk && Nat.ble splitCost c.csCost
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
        | .gpr r => if natMem r rs || armShare c s.armEv y x then rs else r :: rs | _ => rs) []
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
      let baseCsThresh := if Nat.ble c.nGpr 8 then 2 * baseMult else 3 * baseMult
      let csThresh := max baseCsThresh c.csCost
      let newCs := if Nat.ble csThresh wx then
          c.csIds.filter (fun r => !natMem r s.usedCs && !natMem r forb) else []
      let addNbr (u w scale : Nat) (acc : List (Nat × Nat)) :=
        match s.hT.getD u .none with
        | .gpr ru => (ru, w / scale) :: acc
        | .none => (abiGT.getD u []).foldl (fun a (ru, wu) => (ru, min w wu / scale) :: a) acc
        | _ => acc
      let prefs := (affT.getD x []).foldl (fun ps (y, w) =>
        match s.hT.getD y .none with
        | .gpr ry => (ry, w) :: ps
        | .none =>
          let p1 := (abiGT.getD y []).foldl (fun ps (ry, wy) => (ry, min w wy / 2) :: ps) ps
          (affT.getD y []).foldl (fun acc (z, wz) =>
            if Nat.beq z x then acc else addNbr z (min w wz) 4 acc) p1
        | _ => ps) (abiGT.getD x [])
      let avoid0 := (antiT.getD x []).foldl (fun ps (y, w) =>
        match s.hT.getD y .none with | .gpr ry => (ry, w) :: ps | _ => ps) []
      let avoid := xI.foldl (fun ps z =>
        match s.hT.getD z .none with
        | .none =>
          let a1 := (abiGT.getD z []).foldl (fun a p => p :: a) ps
          (affT.getD z []).foldl (fun acc (u, wu) =>
            if Nat.beq u x then acc else addNbr u wu 2 acc) a1
        | .slot _ _ => match s.hint.find? z with | some h => h :: ps | none => ps
        | _ => ps) (if c.cfg.backEdgeCoal then [] else avoid0)
      let pickReg (cands : List Nat) : Option Nat :=
        if c.cfg.backEdgeCoal then bestRegNet prefs avoid0 avoid cands
        else bestRegPref prefs avoid cands
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
        | none =>
          let armEv? := if !peers.isEmpty || (isX && !c.cfg.armX) then none
            else tryArmEvict c x xI pids cpids ptIps forbBkSlots (isBP.getD x false) isX dw cw
              csThresh wx s
          match armEv? with
          | some sA => sA
          | none =>
            let loopEv? := if !peers.isEmpty then none
              else tryLoopBoundarySplit c x xI pids ptBlks forbBkSlots prefs avoid
                (isBP.getD x false) isX dw cw wx slotCost s
            match loopEv? with
            | some sL => sL
            | none => toSlotG
      let orSplitOrSlot : ColorSt I.Cond :=
        match (if isX && splitOk then pickReg caller else none) with
        | some r => inReg r
        | none => toSlotOrEv
      let orNewCs : ColorSt I.Cond :=
        match pickReg newCs with
        | some r => inNewCs r
        | none => orSplitOrSlot
      if !isX then
        match sharedPeerReg? with
        | some (r, extraPids) =>
          { s with hT := s.hT.insert x (.gpr r), gPb := decPts extraPids s.gPb }
        | none =>
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
  let ptIps := acc.gprPtIps.toArray
  let cs0 := order.foldl (fun s (wx, x) =>
    match s.hT.find? x with
    | some (.flag _) => s
    | _ =>
      colorOne c interf gVp gCp vVp abiGT abiVT affT antiT cwT acc.defWT acc.loopCall acc.isBP
        zextPeers fnParams ptBlks ptIps s wx x)
    { hT := initHome, gPb := gPb0, vPb := vPb0 }
  if c.cfg.backEdgeCoal then
    let hT' := refineColors c order interf affT antiT abiGT zextPeers cs0.bk cs0.armEv cs0.forceEv
      cs0.usedCs (armShare c) cs0.hT
    { cs0 with hT := hT' }
  else cs0

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
    (t : Tree) : Trie (Home I.Cond) × Trie (List Nat) × Nat :=
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
      let needPloc := countPlocGprs c h (fun p => !bad.getD p false) ps
      let rec dropVars (h : Trie (Home I.Cond)) (fe : Trie (List Nat)) (ns : Nat) :
          Nat → Trie (Home I.Cond) × Trie (List Nat) × Nat
        | 0 => (h, fe, ns)
        | fuel + 1 =>
          let evL := fe.getD l []
          let lvAct := if evL.isEmpty then lv else lv.filter (!natMem · evL)
          let gprs := dedup (gprHomes h (lvAct ++ pvars))
          if Nat.ble (gprs.length + needPloc) cap then (h, fe, ns)
          else
            let cands := lvAct.filter fun x =>
              !natMem x pvars && match h.getD x .none with | .gpr _ => true | _ => false
            let reduces (x : Nat) :=
              let g' := dedup (gprHomes h (lvAct.filter (!Nat.beq · x) ++ pvars))
              Nat.blt g'.length gprs.length
            match pickMin (cands.filter fun x => (bk.find? x).isSome && reduces x) with
            | some x => dropVars h (triePush fe l x) ns fuel
            | none =>
              match pickMin (cands.filter fun x => (bk.find? x).isNone && reduces x) with
              | some x => dropVars (h.insert x (.slot ns .w64)) fe (ns + 1) fuel
              | none => (h, fe, ns)
      let (h', fe', ns') := dropVars h fe ns (lv.length + 1)
      fix h' fe' ns' rest
  fix home0 fe0 nslots0 t.blocks

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

private abbrev RegionVarSet := List Nat × Trie Unit

private def rvsAdd (s : RegionVarSet) (xs : List Nat) : RegionVarSet :=
  xs.foldl (fun (ks, t) x => if trieMem t x then (ks, t) else (x :: ks, t.insert x ())) s

private def rvsInter (a b : RegionVarSet) : RegionVarSet :=
  let (small, bigM) := if Nat.ble a.1.length b.1.length then (a.1, b.2) else (b.1, a.2)
  small.foldl (fun (ks, m) x =>
    if trieMem bigM x then (x :: ks, m.insert x ()) else (ks, m)) ([], .empty)

mutual
/-- Linear bottom-up pass recording, at each `.let_` `ip`, the continuation live-ins reused
within the same straight-line region (or both arms of a `jnz`) by non-compare ops. -/
private def buildRegionReused {I : Isa} (c : Ctx I) :
    Tree → Trie (List Nat) → RegionVarSet × Trie (List Nat)
  | .let_ _ ip _ _ op k, acc =>
    let ((ksK, mK), acc1) := buildRegionReused c k acc
    let both := k.lv.filter (trieMem mK ·)
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
    (rvsAdd ([], .empty) (tupVarIds args), acc)
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
  let sumW (xs : List (Nat × Nat × Bool × Bool × Nat)) :=
    xs.foldl (fun a e => a + e.2.2.2.2) 0
  blocks.foldl (fun acc (l, _, body) =>
    let es := evArr.filter fun e => Nat.beq e.1 l
    if es.isEmpty then acc
    else
      let wj := c.inW.getD l 0
      let sel := (dedup (es.map (·.2.1))).filter fun x =>
        match home.getD x .none with
        | .gpr r =>
          let ex := exFilter es x
          let evEdges := ex.filter (·.2.2.1)
          let savEdges := ex.filter (·.2.2.2.1)
          let wEv := sumW evEdges
          let wSav := sumW savEdges
          let (cost, leaves) := evBodyCost c x (Nat.blt r c.nGpr) prevEv wj body
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

mutual
def fillLiveRemat (lTrie : Trie (List Nat)) (addrDeps rmwDeps : Trie (List Nat))
    (rematRoot : Trie Nat) : Tree → List Nat × Tree
  | .let_ _ ip nv0 ts op k =>
    let (klv, k) := fillLiveRemat lTrie addrDeps rmwDeps rematRoot k
    let ops := addrDeps.getD ip (opVarIds op)
    let lv := union (eraseMany ((List.range ts.length).map (nv0 + ·)) klv) ops
    (lv, .let_ lv ip nv0 ts op k)
  | .load _ ip x t a k =>
    let (klv, k) := fillLiveRemat lTrie addrDeps rmwDeps rematRoot k
    let aUses := addrDeps.getD ip (argVarIds a)
    let lv := union (erase x klv) aUses
    (lv, .load lv ip x t a k)
  | .store _ ip t v a k =>
    let (klv, k) := fillLiveRemat lTrie addrDeps rmwDeps rematRoot k
    let lv := union klv (storeVarIds addrDeps rmwDeps ip v a)
    (lv, .store lv ip t v a k)
  | .call _ ip nv0 g as bs args k =>
    let (klv, k) := fillLiveRemat lTrie addrDeps rmwDeps rematRoot k
    let lv := union (eraseMany ((List.range bs.length).map (nv0 + ·)) klv)
      (mapRematVars rematRoot (tupVarIds args))
    (lv, .call lv ip nv0 g as bs args k)
  | .jnz _ ip c l t e =>
    let (tlv, t) := fillLiveRemat lTrie addrDeps rmwDeps rematRoot t
    let (elv, e) := fillLiveRemat lTrie addrDeps rmwDeps rematRoot e
    let lv := union (union tlv elv) [c]
    (lv, .jnz lv ip c l t e)
  | .skip _ ip k =>
    let (klv, k) := fillLiveRemat lTrie addrDeps rmwDeps rematRoot k
    (klv, .skip klv ip k)
  | .jump _ ip j ts args =>
    let lv := union (mapRematVars rematRoot (tupVarIds args)) (lTrie.getD j [])
    (lv, .jump lv ip j ts args)
  | .ret _ ip rs vs =>
    let lv := mapRematVars rematRoot (tupVarIds vs); (lv, .ret lv ip rs vs)
  | .exit _ ip g as args =>
    let lv := mapRematVars rematRoot (tupVarIds args); (lv, .exit lv ip g as args)
  | .stop ip => ([], .stop ip)
  | .group _ bs k =>
    let (klv, k) := fillLiveRemat lTrie addrDeps rmwDeps rematRoot k
    (klv, .group klv (fillLiveRematB lTrie addrDeps rmwDeps rematRoot bs) k)

def fillLiveRematB (lTrie : Trie (List Nat)) (addrDeps rmwDeps : Trie (List Nat))
    (rematRoot : Trie Nat) : TreeBlocks → TreeBlocks
  | .nil => .nil
  | .cons l ps b bs =>
    .cons l ps (fillLiveRemat lTrie addrDeps rmwDeps rematRoot b).2
      (fillLiveRematB lTrie addrDeps rmwDeps rematRoot bs)
end

def liveLabelsRemat (bs0 : List (Nat × List (Nat × Ty) × Tree))
    (addrDeps rmwDeps : Trie (List Nat)) (rematRoot : Trie Nat) : Trie (List Nat) :=
  let bs := bs0.map fun (l, ps, tb) => (l, ps.map Prod.fst, tb, allJumps tb)
  let rec go : Nat → Bool → Trie (List Nat) → Trie Bool → Trie (List Nat)
    | 0, _, lt, _ => lt
    | fuel + 1, first, lt, prevCh =>
      let (lt', nextCh, ch) := bs.foldl (fun (lt, nch, ch) (l, pvars, tb, js) =>
        if !(first || js.any (fun j => prevCh.getD j false)) then (lt, nch, ch)
        else
          let lv := eraseMany pvars (fillLiveRemat lt addrDeps rmwDeps rematRoot tb).1
          if Nat.beq lv.length (lt.getD l []).length then (lt, nch, ch)
          else (lt.insert l lv, nch.insert l true, true))
        (lt, .empty, false)
      if ch then go fuel false lt' nextCh else lt
  go (8 * bs.length + 8) true .empty .empty

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
  let colorPass (t1p : Tree) (adp : Trie (List Nat)) (useRemat : Bool) (rematRoot : Trie Nat)
      (rematOpIps : Trie Bool) (dropFlags : List Nat) :
      Tree × Ctx I × GatherAcc × FlagHints I.Cond × ColorSt I.Cond × Trie (Home I.Cond) ×
        Trie (List Nat) × Nat :=
    let bs0 := t1p.blocks
    let lTrie := if !useRemat then liveLabels bs0 adp rmwDeps
      else liveLabelsRemat bs0 adp rmwDeps rematRoot
    let (_, t) := if !useRemat then fillLive lTrie adp rmwDeps t1p
      else fillLiveRemat lTrie adp rmwDeps rematRoot t1p
    let crossList := acrossCalls t
    let crossTrie := crossList.foldl (fun a x => a.insert x true) .empty
    let isLeaf := crossList.isEmpty
    let bparamsTrie := bs0.foldl (fun a (l, ps, _) => a.insert l (ps.map Prod.fst)) .empty
    let fh0 := match I.frame.allocatable.head? with
      | some r0 =>
        let r1 := I.frame.allocatable[1]?.getD r0
        let v0 := I.vec.vecAllocatable.head?
        let v1 := I.vec.vecAllocatable[1]? <|> v0
        gatherFlags I r0 r1 v0 v1 condCands nv (fnPs.map Prod.fst) crossTrie bparamsTrie tys lTrie t
      | none => {}
    let fh := { fh0 with flagHome := dropFlags.foldl (fun m x => m.erase x) fh0.flagHome }
    let (loops, loopReach) := loopBlocksScoped (blocksWithMin t1p)
    let loopHdrs := bs0.filterMap fun (l, _, _) => if loops.getD l false then some l else none
    let blkLoops := loopHdrs.foldl (fun m lh =>
      (union [lh] (loopReach.getD lh [])).foldl (fun m b =>
        if natMem lh (m.getD b []) then m else triePush m b lh) m)
      (.empty : Trie (List Nat))
    let csCost := 2 * baseMult
    let c : Ctx I := {
      allGpr := allGpr, allVec := allVec,
      gReg := (allGpr.foldl (fun (t, i) r => (t.insert i r, i + 1)) (.empty, 0)).1,
      vReg := (allVec.foldl (fun (t, i) v => (t.insert i v, i + 1)) (.empty, 0)).1,
      nGpr := nGpr, nVec := nVec, gAlloc := List.range nGpr,
      csIds := (List.range nCs).map (· + nGpr), vAlloc := List.range nVec,
      gScr := if I.frame.scratch.isEmpty then none else some (nGpr + nCs),
      vScr := if I.vec.vecScratch.isEmpty then none else some nVec,
      cross := crossTrie, loops := loops, loopReach := loopReach, blkLoops := blkLoops,
      banks := (List.range nv).foldl (fun b x => b.insert x (bankOf I (tys.getD x i64))) .empty,
      flagHome := fh.flagHome, bparams := bparamsTrie, lTrie := lTrie, addrDeps := adp,
      rmwDeps := rmwDeps, isLeaf := isLeaf, cfg := cfg, csCost := csCost,
      r0? := I.frame.allocatable.head? }
    let regionReused := (buildRegionReused c t .empty).2
    let directVars : Tree → List Nat :=
      let rec go : Tree → List Nat
        | .let_ _ ip nv0 ts op k =>
          (List.range ts.length).map (nv0 + ·) ++ adp.getD ip (opVarIds op) ++ go k
        | .load _ ip x _ a k => x :: adp.getD ip (argVarIds a) ++ go k
        | .store _ ip _ v a k => storeVarIds adp rmwDeps ip v a ++ go k
        | .call _ _ nv0 _ _ bs args k =>
          (List.range bs.length).map (nv0 + ·) ++
            mapRematVars rematRoot (tupVarIds args) ++ go k
        | .jnz _ _ cx _ t e => cx :: go t ++ go e
        | .skip _ _ k | .group _ _ k => go k
        | .jump _ _ _ _ args => mapRematVars rematRoot (tupVarIds args)
        | .ret _ _ _ vs | .exit _ _ _ _ vs => mapRematVars rematRoot (tupVarIds vs)
        | .stop _ => []
      go
    let rec jmpEdges (src : Nat) (w : Nat) : Tree → List (Nat × Nat × Nat × List Nat)
      | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k
      | .call _ _ _ _ _ _ _ k | .skip _ _ k | .group _ _ k => jmpEdges src w k
      | .jnz _ ip _ _ t e =>
        let (_, mT, mE) := c.brW.getD ip (w, w, w)
        jmpEdges src mT t ++ jmpEdges src mE e
      | .jump _ _ j _ args => [(src, j, w, mapRematVars rematRoot (tupVarIds args))]
      | _ => []
    let acc := gather c [] [] baseMult initZ32 t {} rematRoot rematOpIps
    let rootId := t.blocks.foldl (fun m (l, _, _) => max m (l + 1)) 0
    let blkUses := t.blocks.foldl (fun m (l, _, body) => m.insert l (directVars body))
      (Trie.empty.insert rootId (directVars t))
    let rootVars := union t.lv (blkUses.getD rootId [])
    let varBlks0 := rootVars.foldl (fun m v => triePush m v rootId) .empty
    let varBlks := t.blocks.foldl (fun m (l, ps, _) =>
      let vs := union (lTrie.getD l []) (union (ps.map Prod.fst) (blkUses.getD l []))
      vs.foldl (fun m v => triePush m v l) m) varBlks0
    let c := { c with
      brW := acc.brW, zextElide := acc.zextElide, regionReused := regionReused, ipW := acc.ipW,
      jmpW := acc.jmpW, inW := acc.inW, blkUses := blkUses, varBlks := varBlks }
    let blkEdges := t.blocks.foldl (fun es (l, _, body) =>
      es ++ jmpEdges l (c.inW.getD l 0) body) (jmpEdges rootId baseMult t)
    let rec jmpLatch (dsts : List Nat) : Tree → Trie Bool → Trie Bool
      | .let_ _ _ _ _ _ k, m | .load _ _ _ _ _ k, m | .store _ _ _ _ _ k, m
      | .call _ _ _ _ _ _ _ k, m | .skip _ _ k, m | .group _ _ k, m => jmpLatch dsts k m
      | .jnz _ _ _ _ t e, m => jmpLatch dsts t (jmpLatch dsts e m)
      | .jump _ ip j _ _, m =>
        if loops.getD j false && natMem j dsts then m.insert ip true else m
      | _, m => m
    let latchIps := t.blocks.foldl (fun m (l, _, body) =>
      let hdrs := t.blocks.foldl (fun acc (lh, _, _) =>
        if loops.getD lh false && natMem l (loopReach.getD lh []) then lh :: acc else acc) []
      jmpLatch hdrs body m) .empty
    let c := { c with blkEdges := blkEdges, latchIps := latchIps }
    let c :=
      if !cfg.armEvict then c
      else
        let arms := collectArms c t []
        let ext0 := fnPs.foldl (fun e (p, _) => extendExt e p (firstIp t)) .empty
        let (vext, uips) := varScan c t (ext0, .empty)
        { c with armList := arms, armT := arms.foldl (fun m a => m.insert a.key a) .empty,
                 varExt := vext, useIps := uips, foldIps := foldIpsT t .empty }
    let cs := colorVars c nv fh.flagHome acc (fnPs.map Prod.fst) fnAbi
    let armVars := (List.range nv).filterMap fun x => (cs.armEv.find? x).map (x, ·)
    let armEvAt : Trie (List Nat) := armVars.foldl (fun m (x, ks) =>
      ks.foldl (fun m k => triePush m k x) m) .empty
    let fe0 := armVars.foldl (fun t (x, ks) => ks.foldl (fun t k =>
      match c.armT.find? k with
      | some a =>
        a.blocks.foldl (fun t b => if natMem x (lTrie.getD b []) then triePush t b x else t) t
      | none => t) t) cs.forceEv
    let (hT, fe, nslots1) :=
      fitBlockGprs c (sumWeights acc.weights) cs.bk cs.usedCs cs.nslots cs.hT fe0 t
    let c := { c with hintT := cs.hint, forceEv := fe, evIn := fe, armEvAt := armEvAt }
    (t, c, acc, fh, cs, hT, fe, nslots1)
  let emitWithRefine (res : Tree × Ctx I × GatherAcc × FlagHints I.Cond × ColorSt I.Cond ×
      Trie (Home I.Cond) × Trie (List Nat) × Nat) :
      EmitSt I × Nat × Ctx I × GatherAcc × FlagHints I.Cond :=
    let (t, c, acc, fh, cs, hT, _, nslots1) := res
    let slotOk := slotPlocMap c hT cs.bk cs.usedCs acc.defWT t
    let r0? := I.frame.allocatable.head?
    let r1? := I.frame.allocatable[1]?
    let initSv := (fnPs.map Prod.fst).filter (isEagerBk cs.bk)
    let emit (c : Ctx I) : EmitSt I := emitAlloc c hT cs.bk slotOk fh.clearAt r0? r1? t
      (pendFromArrivals hT cs.bk (fnPs.map Prod.fst) fnAbi) [] initSv [] []
      { variant := fh.variant, usedCs := cs.usedCs }
    let c := { c with jmpW := acc.jmpW, inW := acc.inW, addrDeps := addrDeps }
    let refine (c : Ctx I) : Ctx I :=
      let stO := emit { c with opt := true }
      let rin := pickRegIn c hT cs.usedCs slotOk stO.cin t.blocks
      let evi := pickEvIn c hT stO.evArr c.evIn t.blocks
      let lp := stO.latchArr.foldl (fun t (p, r, w) => triePush t p (r, w)) .empty
      { c with regIn := rin, evIn := evi, latchPrefs := lp }
    let c := if cfg.regEntry && cfg.sink then refine (refine c) else c
    let st := emit c
    let finalSlots :=
      if I.frame.scratch.isEmpty then nslots1 else min nslots1 (usedSlotCount nip nl st)
    (st, finalSlots, c, acc, fh)
  let baseRes := colorPass t1 addrDeps false .empty .empty []
  let (_, _, acc1, _, cs1, hT1, _, _) := baseRes
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
            let (_, _, acc2, _, cs2, hT2, _, _) := res2
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
