module

public import LeanQbe.T.Target
public import LeanQbe.T.Live
public import LeanQbe.T.Spill
public import LeanQbe.T.Rega

/-!
# Snippet-First Register Allocation & Edge Spill Splicing (`SpillSnippet`)

Untrusted (`0` TCB, `0` proof obligation) hint builder and relational-hint solver implementing
the 4 Phase-0 validated invariants (`SpillSnippet.splice_snippet_hints`, `solveRelHints`):

1. **`keepInputRegs` exclusion:** Computes actual outer variables read inside `calleeTree`
   (`outerUsedVars \ calleeNvs`, including ABI parameters via `I.assignArgs` and outer `hOuter.dest`
   plus any outer `Move.ld` reload registers inside `calleeIps`) and excludes those GPRs from the
   snippet register pool so internal snippet defs never clobber live inputs.
2. **`freeRegs`-first coloring + call-free hot-island unpoisoning:** Confirms
   `!treeHasCall calleeTree`, allocates from `freeRegs` (registers unused across the region exit)
   before `evictableRegs`, maps snippet return registers (`I.frame.retRegs`) onto `contRetRegs`
   when available, and preserves any new `I.frame.calleeSaved` registers in `hNew.saved`.
3. **Outer `Move.st` hoisting onto entry:** Hoists outer `Move.st` moves from `calleeIps` onto
   `startIp` while clearing interior snippet spills (and keeping any outer input `Move.ld` moves).
4. **Evict / rewrite / post-exit restore:** For any `evictRegs` borrowed from `contLiveRegs`,
   allocates fresh spill slots (`hOuter.nslots + idx`), emits `Move.st` on `startIp`, rewrites
   `contLid.live` and internal `lid2.live` (`w ∉ calleeNvs`) from `.gpr r` to `.slot sIdx .w64`
   (plus internal snippet `w ∈ calleeNvs` from `dest'`), and restores `Move.ld` on `exitNextIp`.

Everything returned by `SpillSnippet` is plain `I.Hints` verified downstream by `Rega.lowerFn`
and `Rega.lowerFn_correct`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace SpillSnippet

/-! ## Generic `Live.Tree` region inspection & structural `zipTrees` -/

/-- Live variable IDs at the head of a `Live.Tree` node. -/
def treeHeadLive : Live.Tree → List Nat
  | .let_ l .. | .load l .. | .store l .. | .call l .. | .jnz l ..
  | .skip l .. | .jump l .. | .ret l .. | .exit l .. | .group l .. => l
  | .stop _ => []

/-- First instruction pointer (`ip`) executed when entering a `Live.Tree` (matching
`Rega.lowerExpr`, which lowers `.group` continuations before block bodies). -/
def firstIpOf : Live.Tree → Option Nat
  | .let_ _ ip .. | .load _ ip .. | .store _ ip .. | .call _ ip .. | .jnz _ ip ..
  | .skip _ ip .. | .jump _ ip .. | .ret _ ip .. | .exit _ ip .. | .stop ip => some ip
  | .group _ _ k => firstIpOf k

/-- True iff any node inside `t` executes `.call` (`treeHasCall`). -/
def treeHasCall : Live.Tree → Bool
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k | .skip _ _ k => treeHasCall k
  | .call .. => true
  | .jnz _ _ _ _ t1 t2 => treeHasCall t1 || treeHasCall t2
  | .group _ bs k => blocksHasCall bs || treeHasCall k
  | _ => false
where
  blocksHasCall : Live.TreeBlocks → Bool
    | .nil => false
    | .cons _ _ b bs => treeHasCall b || blocksHasCall bs

mutual
/-- Collect `(ips, boundNvs, blockLids)` defined inside a `Live.Tree`. -/
def collectTreeIds : Live.Tree → List Nat × List Nat × List Nat
  | .let_ _ ip nv ts _ k =>
    let (is, ns, ls) := collectTreeIds k
    let newVs := (List.range ts.length).map (nv + ·)
    (ip :: is, newVs ++ ns, ls)
  | .load _ ip nv _ _ k =>
    let (is, ns, ls) := collectTreeIds k
    (ip :: is, nv :: ns, ls)
  | .store _ ip _ _ _ k | .skip _ ip k =>
    let (is, ns, ls) := collectTreeIds k
    (ip :: is, ns, ls)
  | .call _ ip nv _ _ bs _ k =>
    let (is, ns, ls) := collectTreeIds k
    let newVs := (List.range bs.length).map (nv + ·)
    (ip :: is, newVs ++ ns, ls)
  | .jnz _ ip _ _ t1 t2 =>
    let (i1, n1, l1) := collectTreeIds t1
    let (i2, n2, l2) := collectTreeIds t2
    (ip :: (i1 ++ i2), n1 ++ n2, l1 ++ l2)
  | .jump _ ip _ _ _ | .ret _ ip _ _ | .exit _ ip _ _ _ => ([ip], [], [])
  | .stop ip => ([ip], [], [])
  | .group _ bs k =>
    let (ib, nb, lb) := collectBlocksIds bs
    let (ik, nk, lk) := collectTreeIds k
    (ib ++ ik, nb ++ nk, lb ++ lk)

/-- Block-list companion of `collectTreeIds`. -/
def collectBlocksIds : Live.TreeBlocks → List Nat × List Nat × List Nat
  | .nil => ([], [], [])
  | .cons lid ps b bs =>
    let (i1, n1, l1) := collectTreeIds b
    let (i2, n2, l2) := collectBlocksIds bs
    (i1 ++ i2, (ps.map Prod.fst) ++ n1 ++ n2, lid :: (l1 ++ l2))
end

mutual
/-- Collect `(nv, liveAfter)` pairs for every `.let_` and `.load` in a `Live.Tree`. -/
def collectTreeAfterLive : Live.Tree → List (Nat × List Nat)
  | .let_ _ _ nv ts _ k =>
    let lv := treeHeadLive k
    ((List.range ts.length).map fun idx => (nv + idx, lv)) ++ collectTreeAfterLive k
  | .load _ _ nv _ _ k => (nv, treeHeadLive k) :: collectTreeAfterLive k
  | .store _ _ _ _ _ k | .call _ _ _ _ _ _ _ k | .skip _ _ k => collectTreeAfterLive k
  | .jnz _ _ _ _ t e => collectTreeAfterLive t ++ collectTreeAfterLive e
  | .group _ bs k => collectBlocksAfterLive bs ++ collectTreeAfterLive k
  | _ => []

/-- Block-list companion of `collectTreeAfterLive`. -/
def collectBlocksAfterLive : Live.TreeBlocks → List (Nat × List Nat)
  | .nil => []
  | .cons _ _ tb bs => collectTreeAfterLive tb ++ collectBlocksAfterLive bs
end

mutual
/-- Collect `(ip, nv0)` pairs for single-result `.let_` and `.load` bindings. -/
def collectIpDefVars : Live.Tree → List (Nat × List Nat)
  | .let_ _ ip nv ts _ k =>
    (ip, (List.range ts.length).map (nv + ·)) :: collectIpDefVars k
  | .load _ ip nv _ _ k => (ip, [nv]) :: collectIpDefVars k
  | .store _ _ _ _ _ k | .call _ _ _ _ _ _ _ k | .skip _ _ k => collectIpDefVars k
  | .jnz _ _ _ _ t e => collectIpDefVars t ++ collectIpDefVars e
  | .group _ bs k => collectBlocksIpDefVars bs ++ collectIpDefVars k
  | _ => []

/-- Block-list companion of `collectIpDefVars`. -/
def collectBlocksIpDefVars : Live.TreeBlocks → List (Nat × List Nat)
  | .nil => []
  | .cons _ _ tb bs => collectIpDefVars tb ++ collectBlocksIpDefVars bs
end

mutual
/-- Collect `(ip, readVarIds)` pairs across a `Live.Tree`. -/
def collectIpUsedVars : Live.Tree → List (Nat × List Nat)
  | .let_ _ ip _ _ op k => (ip, Live.opVarIds op) :: collectIpUsedVars k
  | .load _ ip _ _ a k => (ip, Live.argVarIds a) :: collectIpUsedVars k
  | .store _ ip _ v a k =>
    (ip, Live.dedup (Live.argVarIds v ++ Live.argVarIds a)) :: collectIpUsedVars k
  | .call _ ip _ _ _ _ args k => (ip, Live.tupVarIds args) :: collectIpUsedVars k
  | .jnz _ ip c _ t e => (ip, [c]) :: collectIpUsedVars t ++ collectIpUsedVars e
  | .skip _ ip k => (ip, []) :: collectIpUsedVars k
  | .jump _ ip _ _ args => [(ip, Live.tupVarIds args)]
  | .ret _ ip _ vs => [(ip, Live.tupVarIds vs)]
  | .exit _ ip _ _ args => [(ip, Live.tupVarIds args)]
  | .stop _ => []
  | .group _ bs k => collectBlocksIpUsedVars bs ++ collectIpUsedVars k

/-- Block-list companion of `collectIpUsedVars`. -/
def collectBlocksIpUsedVars : Live.TreeBlocks → List (Nat × List Nat)
  | .nil => []
  | .cons _ _ b bs => collectIpUsedVars b ++ collectBlocksIpUsedVars bs
end

/-- Deduplicated list of all variable IDs referenced as operands in `t`. -/
def collectTreeUsedVars (t : Live.Tree) : List Nat :=
  Live.dedup ((collectIpUsedVars t).foldl (fun acc p => p.2 ++ acc) [])

/-- Structural AST mapping produced by `zipTrees tSnip tInlined`. -/
structure TreeZip where
  nvMap  : List (Nat × Nat) := []
  ipMap  : List (Nat × Nat) := []
  lidMap : List (Nat × Nat) := []
  deriving Repr, Inhabited

mutual
/-- Structurally match a standalone snippet tree `t1` (`sDirect`) against an inlined region tree
`t2` (allowing `.ret` leaves in `t1` to align with `.jump` leaves into `contLid` in `t2`). -/
def zipTrees (t1 t2 : Live.Tree) (acc : TreeZip := {}) : Option TreeZip :=
  match t1, t2 with
  | .let_ _ ip1 nv1 ts1 _ k1, .let_ _ ip2 nv2 ts2 _ k2 =>
    if ts1.length != ts2.length then none
    else
      let nvPairs := (List.range ts1.length).map fun idx => (nv1 + idx, nv2 + idx)
      zipTrees k1 k2
        { acc with nvMap := nvPairs ++ acc.nvMap, ipMap := (ip1, ip2) :: acc.ipMap }
  | .load _ ip1 nv1 _ _ k1, .load _ ip2 nv2 _ _ k2 =>
    zipTrees k1 k2
      { acc with nvMap := (nv1, nv2) :: acc.nvMap, ipMap := (ip1, ip2) :: acc.ipMap }
  | .store _ ip1 _ _ _ k1, .store _ ip2 _ _ _ k2
  | .skip _ ip1 k1, .skip _ ip2 k2 =>
    zipTrees k1 k2 { acc with ipMap := (ip1, ip2) :: acc.ipMap }
  | .jnz _ ip1 _ _ a1 b1, .jnz _ ip2 _ _ a2 b2 => do
    let z1 ← zipTrees a1 a2 { acc with ipMap := (ip1, ip2) :: acc.ipMap }
    zipTrees b1 b2 z1
  | .call _ ip1 nv1 sym1 _ bs1 _ k1, .call _ ip2 nv2 sym2 _ bs2 _ k2 =>
    if sym1 != sym2 || bs1.length != bs2.length then none
    else
      let nvPairs := (List.range bs1.length).map fun idx => (nv1 + idx, nv2 + idx)
      zipTrees k1 k2
        { acc with nvMap := nvPairs ++ acc.nvMap, ipMap := (ip1, ip2) :: acc.ipMap }
  | .ret _ ip1 _ _, .jump _ ip2 _ _ _ | .jump _ ip1 _ _ _, .jump _ ip2 _ _ _ =>
    some { acc with ipMap := (ip1, ip2) :: acc.ipMap }
  | .group _ bs1 k1, .group _ bs2 k2 => do
    let zb ← zipBlocks bs1 bs2 acc
    zipTrees k1 k2 zb
  | _, _ => none

/-- Block-list companion of `zipTrees`. -/
def zipBlocks (bs1 bs2 : Live.TreeBlocks) (acc : TreeZip) : Option TreeZip :=
  match bs1, bs2 with
  | .nil, .nil => some acc
  | .cons l1 ps1 b1 r1, .cons l2 ps2 b2 r2 =>
    if ps1.length != ps2.length then none
    else do
      let pMaps := (ps1.zip ps2).map fun (p, q) => (p.1, q.1)
      let zb ← zipTrees b1 b2
        { acc with nvMap := pMaps ++ acc.nvMap, lidMap := (l1, l2) :: acc.lidMap }
      zipBlocks r1 r2 zb
  | _, _ => none
end

/-- Located snippet region inside an outer function `outerLate`. -/
structure RegionFind where
  startIp      : Nat
  exitIp       : Option Nat := none
  exitNextIp   : Nat
  calleeTree   : Live.Tree
  contLid      : Nat
  contPlocVars : List Nat
  contLiveOut  : List Nat
  calleeIps    : List Nat
  calleeNvs    : List Nat
  calleeLids   : List Nat
  preExitIps   : List Nat := []
  preExitVars  : List Nat := []
  preExitDefs  : List Nat := []

/-- Default start/exit magic store constants used in Phase-0 stress harnesses. -/
def defaultStartMagics : List (BitVec 64) := [1369899009#64, 0x51A70000#64]
def defaultExitMagics  : List (BitVec 64) := [1369899010#64, 0x51A80000#64]

/-- Locate a marked exit store inside `contTree`, returning
`(exitIp, exitNextIp, liveAfterExit, preExitIps, preExitUsedVars, preExitDefVars)`.
Tracking the pre-exit prefix ensures `splice_snippet_hints` keeps registers needed before
`exitNextIp` un-evicted when `Move.ld` restores run after `exitIp`. -/
def findExitStoreMeta? (exitMagics : List (BitVec 64) := defaultExitMagics) :
    Live.Tree → Option (Nat × Nat × List Nat × List Nat × List Nat × List Nat)
  | .store _ eIp (.bits 64) (.imm ce) a afterExit =>
    if exitMagics.contains ce then
      some (eIp, (firstIpOf afterExit).getD (eIp + 1), treeHeadLive afterExit,
        [eIp], Live.argVarIds a, [])
    else do
      let (rIp, nxt, lv, ips, uvs, dvs) ← findExitStoreMeta? exitMagics afterExit
      some (rIp, nxt, lv, eIp :: ips, Live.argVarIds a ++ uvs, dvs)
  | .store _ eIp _ v a afterExit => do
    let (rIp, nxt, lv, ips, uvs, dvs) ← findExitStoreMeta? exitMagics afterExit
    some (rIp, nxt, lv, eIp :: ips, Live.argVarIds v ++ Live.argVarIds a ++ uvs, dvs)
  | .let_ _ ip nv ts op k => do
    let (rIp, nxt, lv, ips, uvs, dvs) ← findExitStoreMeta? exitMagics k
    let newVs := (List.range ts.length).map (nv + ·)
    some (rIp, nxt, lv, ip :: ips, Live.opVarIds op ++ uvs, newVs ++ dvs)
  | .load _ ip nv _ a k => do
    let (rIp, nxt, lv, ips, uvs, dvs) ← findExitStoreMeta? exitMagics k
    some (rIp, nxt, lv, ip :: ips, Live.argVarIds a ++ uvs, nv :: dvs)
  | .skip _ ip k => do
    let (rIp, nxt, lv, ips, uvs, dvs) ← findExitStoreMeta? exitMagics k
    some (rIp, nxt, lv, ip :: ips, uvs, dvs)
  | _ => none

/-- Locate a marked exit store inside `contTree`. -/
def findExitStore? (exitMagics : List (BitVec 64) := defaultExitMagics) (t : Live.Tree) :
    Option (Nat × Nat × List Nat) :=
  (findExitStoreMeta? exitMagics t).map fun (eIp, nxt, lv, _, _, _) => (eIp, nxt, lv)

mutual
/-- Locate an explicitly marker-bracketed snippet `.group` inside an outer `Live.Tree`. -/
def findMarkedRegion? (startMagics : List (BitVec 64) := defaultStartMagics)
    (exitMagics : List (BitVec 64) := defaultExitMagics) :
    Live.Tree → Option RegionFind
  | .store _ sIp (.bits 64) (.imm c) _
      (.group _ (.cons contLid psCont contTree .nil) calleeTree) =>
    if startMagics.contains c then
      match findExitStoreMeta? exitMagics contTree with
      | some (eIp, nextIp, liveExit, preIps, preUvs, preDvs) =>
        let (cIps, cNvs, cLids) := collectTreeIds calleeTree
        some {
          startIp := sIp
          exitIp := some eIp
          exitNextIp := nextIp
          calleeTree := calleeTree
          contLid := contLid
          contPlocVars := psCont.map Prod.fst
          contLiveOut := liveExit
          calleeIps := cIps
          calleeNvs := cNvs
          calleeLids := cLids
          preExitIps := preIps
          preExitVars := Live.dedup preUvs
          preExitDefs := Live.dedup preDvs
        }
      | none => none
    else findMarkedRegion? startMagics exitMagics
      (.group [] (.cons contLid psCont contTree .nil) calleeTree)
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k
  | .call _ _ _ _ _ _ _ k | .skip _ _ k =>
    findMarkedRegion? startMagics exitMagics k
  | .jnz _ _ _ _ t e =>
    findMarkedRegion? startMagics exitMagics t <|>
      findMarkedRegion? startMagics exitMagics e
  | .group _ bs k =>
    findMarkedBlocks? startMagics exitMagics bs <|>
      findMarkedRegion? startMagics exitMagics k
  | _ => none

/-- Block-list companion of `findMarkedRegion?`. -/
def findMarkedBlocks? (startMagics : List (BitVec 64) := defaultStartMagics)
    (exitMagics : List (BitVec 64) := defaultExitMagics) :
    Live.TreeBlocks → Option RegionFind
  | .nil => none
  | .cons _ _ b bs =>
    findMarkedRegion? startMagics exitMagics b <|>
      findMarkedBlocks? startMagics exitMagics bs
end

mutual
/-- Locate an unmarked `lateInline` join `.group` whose `calleeTree` matches `tSnip` under
`zipTrees`. Searches inner continuations/blocks if the first candidate does not zip. -/
def findInlinedRegionByTree? (tSnip : Live.Tree) : Live.Tree → Option (RegionFind × TreeZip)
  | .group _ (.cons contLid psCont contTree .nil) calleeTree =>
    let direct? :=
      match zipTrees tSnip calleeTree with
      | some z =>
        let (cIps, cNvs, cLids) := collectTreeIds calleeTree
        let maxCalleeIp := cIps.foldl Nat.max 0
        let sIp := (firstIpOf calleeTree).getD 0
        let nextIp := (firstIpOf contTree).getD (maxCalleeIp + 1)
        some ({
          startIp := sIp
          exitIp := none
          exitNextIp := nextIp
          calleeTree := calleeTree
          contLid := contLid
          contPlocVars := psCont.map Prod.fst
          contLiveOut := treeHeadLive contTree
          calleeIps := cIps
          calleeNvs := cNvs
          calleeLids := cLids
        }, z)
      | none => none
    direct? <|>
      findInlinedRegionByTree? tSnip calleeTree <|>
      findInlinedRegionByTree? tSnip contTree
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k
  | .call _ _ _ _ _ _ _ k | .skip _ _ k => findInlinedRegionByTree? tSnip k
  | .jnz _ _ _ _ t e =>
    findInlinedRegionByTree? tSnip t <|> findInlinedRegionByTree? tSnip e
  | .group _ bs k =>
    findInlinedBlocksByTree? tSnip bs <|> findInlinedRegionByTree? tSnip k
  | _ => none

/-- Block-list companion of `findInlinedRegionByTree?`. -/
def findInlinedBlocksByTree? (tSnip : Live.Tree) :
    Live.TreeBlocks → Option (RegionFind × TreeZip)
  | .nil => none
  | .cons _ _ b bs =>
    findInlinedRegionByTree? tSnip b <|> findInlinedBlocksByTree? tSnip bs
end

/-! ## Generic `RelHints` & `solveRelHints` over any `I : Isa` -/

/-- Target-generic relational register/flag/variant hints produced by lifted or hand-tuned snippets
before remapping onto concrete outer register pools. -/
structure RelHints (Reg Cond : Type) where
  sameRegCliques : List (List Nat) := []
  flagBindings   : List (Nat × Cond) := []
  variants       : List (Nat × VariantHint) := []
  softPrefs      : List (Nat × Reg) := []
  elideVars      : List Nat := []
  elideIps       : List (Nat × Bool) := []
  blockParamRegs : List (Nat × List Reg) := []
  savedRegs      : List Reg := []
  nslots         : Nat := 0
  deriving Repr, Inhabited

def dedupList {α : Type} [BEq α] (xs : List α) : List α :=
  (xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).reverse

/-- Generic `RelHints` solver parameterized by `I : Isa`, assigning GPRs without conflicts,
honoring `sameRegCliques`, `flagBindings`, `softPrefs`, `variants`, `elideVars`/`elideIps`,
`blockParamRegs`, and `avoidRegs`. -/
def solveRelHints (I : Isa) (rh : RelHints I.Reg I.Cond) (f : Fn)
    (avoidRegs : List I.Reg := []) (extraIpElides : List (Nat × Bool) := []) : I.Hints :=
  let allPool := dedupList (I.frame.allocatable ++ I.frame.calleeSaved)
  let filtered := allPool.filter (!avoidRegs.contains ·)
  let pool := if filtered.isEmpty then allPool else filtered
  let fallbackReg := pool.head?.getD I.frame.sp
  let usedOriginals :=
    dedupList ((rh.softPrefs.map Prod.snd) ++ rh.blockParamRegs.flatMap Prod.snd)
  let rec buildPhi (used : List I.Reg) : List I.Reg → List (I.Reg × I.Reg)
    | [] => []
    | r :: rs =>
      if pool.contains r && !used.contains r then
        (r, r) :: buildPhi (r :: used) rs
      else
        match pool.find? (!used.contains ·) with
        | some r' => (r, r') :: buildPhi (r' :: used) rs
        | none => (r, fallbackReg) :: buildPhi used rs
  let phi := buildPhi [] usedOriginals
  let mapReg (r : I.Reg) : I.Reg := (phi.find? (·.1 == r)).map Prod.snd |>.getD r
  let (t0, _, nvTotal, _, _, tys) := Live.Tree.ofFn f
  let lTrie := Live.liveLabels t0.blocks .empty .empty
  let (_, tLive) := Live.fillLive lTrie .empty .empty t0
  let afterTrie : Trie (List Nat) :=
    (collectTreeAfterLive tLive).reverse.foldl (fun t (v, lv) => t.insert v lv) .empty
  let ipDefs := collectIpDefVars t0
  let hAuto := Spill.hints I f
  -- Seed `destTrieBase` with `softPrefs` and explicit `flagBindings`.
  let destTrieBase : Trie I.Loc :=
    let t1 := rh.softPrefs.foldl (fun t (nv, r) => t.insert nv (.gpr (mapReg r))) .empty
    rh.flagBindings.foldl (fun t (nv, cc) => t.insert nv (.flag cc)) t1
  -- Pre-index `sameRegCliques` by member variable, preserving exact clique-list order.
  let cliqueTrie : Trie (List Nat) :=
    rh.sameRegCliques.reverse.foldl (fun t cl =>
      (Live.dedup cl).foldl (fun t v => t.insert v (cl ++ t.getD v [])) t) .empty
  let destTrie : Trie I.Loc :=
    (List.range nvTotal).foldl (fun t v =>
      if (t.find? v).isSome then t
      else
        match tys.getD v i64 with
        | .bool =>
          match hAuto.dest.find? v with
          | some loc => t.insert v loc
          | none =>
            match I.gpr.cmpFlags.head? with
            | some cc => t.insert v (.flag cc)
            | none => t.insert v (.gpr fallbackReg)
        | _ =>
          let liveAfter := afterTrie.getD v []
          let busy := liveAfter.filterMap fun w =>
            if w == v then none
            else match t.find? w with | some (.gpr r) => some r | _ => none
          let preferredClique := (cliqueTrie.getD v []).findSome? fun u =>
            match t.find? u with
            | some (.gpr r) => if pool.contains r && !busy.contains r then some r else none
            | _ => none
          let chosen := match preferredClique with
            | some r => r
            | none => pool.find? (!busy.contains ·) |>.getD fallbackReg
          t.insert v (.gpr chosen)) destTrieBase
  let entryTrie : Trie (Entry I.Reg I.VReg I.Cond) :=
    rh.blockParamRegs.foldl (fun t (lid, pregs) =>
      let liveVars := (lTrie.getD lid []).filter fun v => v >= f.as.length
      let liveLocs := liveVars.filterMap fun v =>
        (destTrie.find? v).map fun loc => (SymArg.var v, loc)
      let plocs := pregs.map fun r => Loc.gpr (mapReg r)
      t.insert lid { live := liveLocs, ploc := plocs }) .empty
  let varTrie : Trie VariantHint :=
    rh.variants.foldl (fun t (ip, vh) => t.insert ip vh) .empty
  let elideFromVars : List (Nat × Bool) :=
    if rh.elideVars.isEmpty then []
    else
      let elideSet := Live.trieOfList rh.elideVars
      ipDefs.filterMap fun (ip, vs) =>
        if vs.any (Live.trieMem elideSet ·) then some (ip, true) else none
  let elideTrie : Trie Bool :=
    (elideFromVars ++ rh.elideIps ++ extraIpElides).foldl
      (fun t (ip, b) => t.insert ip b) .empty
  let usedRegsInDest := (List.range nvTotal).filterMap fun v =>
    match destTrie.find? v with | some (.gpr r) => some r | _ => none
  let usedInParams := usedOriginals.map mapReg
  let savedUsed := dedupList
    ((usedInParams ++ usedRegsInDest ++ rh.savedRegs).filter (I.frame.calleeSaved.contains ·))
  let h0 : I.Hints := {
    dest := destTrie
    entry := entryTrie
    variant := varTrie
    elide := elideTrie
    saved := savedUsed
    nslots := Nat.max hAuto.nslots rh.nslots
  }
  Rega.addDeferHints h0 f

/-! ## `splice_snippet_hints`: outer/snippet hint integration -/

/-- Diagnostic summary of `splice_snippet_hints` register/spill decisions. -/
structure SpillSnippetReport (Reg : Type) where
  startIp       : Nat
  exitNextIp    : Nat
  matchedByMark : Bool
  usedRegs      : List Reg := []
  keepInputRegs : List Reg := []
  freeRegs      : List Reg := []
  evictedRegs   : List Reg := []
  hoistedSts    : Nat := 0
  keptOuterLds  : Nat := 0
  nslotsBefore  : Nat := 0
  nslotsAfter   : Nat := 0
  deriving Repr

def abiRegsList {Reg VReg : Type} :
    {ts : List Ty} → Tup (AbiReg Reg VReg) ts → List (Option Reg)
  | [], () => []
  | _ :: _, (.gpr r, rest) => some r :: abiRegsList rest
  | _ :: _, (.vec _, rest) => none :: abiRegsList rest

def collectOuterSlots (I : Isa) (calleeNvs : List Nat) (nvTotal : Nat)
    (hOuter : I.Hints) (enCont? : Option (Entry I.Reg I.VReg I.Cond)) : List Nat :=
  let calleeNvSet := Live.trieOfList calleeNvs
  let fromDest := (List.range nvTotal).filterMap fun v =>
    if Live.trieMem calleeNvSet v then none
    else match hOuter.dest.find? v with | some (.slot s _) => some s | _ => none
  let fromCont := match enCont? with
    | some en => en.live.filterMap fun
      | (.var v, .slot s _) => if Live.trieMem calleeNvSet v then none else some s
      | (_, .slot s _) => some s
      | _ => none
    | none => []
  Live.dedup (fromDest ++ fromCont)

def collectCalleeOnlySlots (I : Isa) (calleeNvs : List Nat) (hOuter : I.Hints)
    (outerSlots : List Nat) : List Nat :=
  let outerSlotSet := Live.trieOfList outerSlots
  let ss := calleeNvs.filterMap fun v =>
    match hOuter.dest.find? v with | some (.slot s _) => some s | _ => none
  Live.dedup (ss.filter (!Live.trieMem outerSlotSet ·))

/-- Splice standalone snippet hints `hSnip` (computed via `Spill.hints I sDirect` unless overridden)
into outer function `outerLate` using `hOuter`, implementing all 4 Phase-0 invariants:
1. Exclude actual outer inputs (`keepInputRegs` + `extraKeepRegs`) from `snipPool`.
2. Verify call-free hot island (`!treeHasCall calleeTree`) and allocate `freeRegs` before
   `evictableRegs`, mapping return registers (`I.frame.retRegs`) onto `contRetRegs` when possible.
3. Hoist outer `Move.st` moves from `calleeIps` onto `startIp` and strip snippet-only spills.
4. Evict `evictRegs` around `[startIp, exitNextIp]`, rewrite `contLid.live` and internal `lid2.live`
   entries, preserve new `calleeSaved` registers in `saved`, and append `Move.ld` restores at
   `exitNextIp`.

Supports BOTH Phase-0 marked regions (`findMarkedRegion?`) AND unmarked post-`mid` `lateInline`
join groups (`findInlinedRegionByTree?`). -/
def splice_snippet_hints (I : Isa) (sDirect outerLate : Fn) (hOuter : I.Hints)
    (extraKeepRegs : List I.Reg := [])
    (hSnipOverride? : Option I.Hints := none) :
    Except String (I.Hints × SpillSnippetReport I.Reg) := do
  let (t0, _, nvTotal, _, _, _) := Live.Tree.ofFn outerLate
  let lTrie := Live.liveLabels t0.blocks .empty .empty
  let (_, tLive) := Live.fillLive lTrie .empty .empty t0
  let (tSnip, _, nvSnip, _, _, _) := Live.Tree.ofFn sDirect
  let (reg, z, byMark) ← match findMarkedRegion? defaultStartMagics defaultExitMagics tLive with
    | some r =>
      if treeHasCall r.calleeTree then throw "snippet_contains_call"
      let z ← match zipTrees tSnip r.calleeTree with
        | some z => pure z
        | none => throw "tree_zip_mismatch"
      pure (r, z, true)
    | none =>
      match findInlinedRegionByTree? tSnip tLive with
      | some (r, z) =>
        if treeHasCall r.calleeTree then throw "snippet_contains_call"
        pure (r, z, false)
      | none => throw "snippet_region_not_found"
  let hSnip := hSnipOverride?.getD (Spill.hints I sDirect)
  if hSnip.nslots > 0 then
    throw s!"snippet '{sDirect.name}' needs {hSnip.nslots} spill slots standalone"
  -- Invariant #1: collect exact `keepInputRegs` from outer variables referenced inside `calleeTree`
  -- plus any outer registers needed in `contTree` before `exitNextIp` (where eviction restores run).
  let outerParamRegs : List (Option I.Reg) := match I.assignArgs outerLate.as with
    | some tup => abiRegsList tup
    | none => []
  let calleeNvSet := Live.trieOfList reg.calleeNvs
  let outerInputVars := (collectTreeUsedVars reg.calleeTree).filter (!Live.trieMem calleeNvSet ·)
  let regOfOuterVar (v : Nat) : Option I.Reg :=
    if v < outerParamRegs.length then outerParamRegs[v]?.join
    else match hOuter.dest.find? v with | some (.gpr r) => some r | _ => none
  let regsFromInputVars := outerInputVars.filterMap regOfOuterVar
  let ipUses := collectIpUsedVars reg.calleeTree
  let outerIps := ipUses.filterMap fun (ip, vs) =>
    if vs.any (!Live.trieMem calleeNvSet ·) then some ip else none
  let loadRegsAt (ips : List Nat) : List I.Reg :=
    ips.flatMap fun ip =>
      match hOuter.pre.find? ip with
      | some ps => ps.moves.filterMap fun | .ld r _ => some r | _ => none
      | none => []
  let regsFromIpLoads := loadRegsAt outerIps
  let enCont? := hOuter.entry.find? reg.contLid
  let preExitVarRegs := reg.preExitVars.filterMap fun v =>
    match enCont? with
    | some en =>
      en.live.findSome? fun
        | (.var w, .gpr r) => if w == v then some r else none
        | _ => none
    | none => regOfOuterVar v
  let preExitDefRegs := reg.preExitDefs.filterMap fun v =>
    match hOuter.dest.find? v with | some (.gpr r) => some r | _ => none
  let preExitLoadRegs := loadRegsAt reg.preExitIps
  let keepInputRegs := dedupList
    (regsFromInputVars ++ regsFromIpLoads ++ preExitVarRegs ++ preExitDefRegs ++
      preExitLoadRegs ++ extraKeepRegs)
  -- Collect exit `contRetRegs`, `contLiveRegs`, and outer live-through regs across internal blocks.
  let contRetRegs : List I.Reg := match enCont? with
    | some en => en.ploc.filterMap fun | .gpr r => some r | _ => none
    | none => []
  let contLiveRegs : List I.Reg := match enCont? with
    | some en => en.live.filterMap fun | (_, .gpr r) => some r | _ => none
    | none => []
  let lid2OuterLiveRegs : List I.Reg := z.lidMap.flatMap fun (_, lid2) =>
    match hOuter.entry.find? lid2 with
    | some enO => enO.live.filterMap fun
      | (.var w, .gpr r) => if Live.trieMem calleeNvSet w then none else some r
      | (_, .gpr r) => some r
      | _ => none
    | none => []
  let allLiveRegs := dedupList (contLiveRegs ++ lid2OuterLiveRegs)
  -- Invariant #2: build `freeRegs`-first pool avoiding `keepInputRegs`.
  let allPool := dedupList (I.frame.allocatable ++ I.frame.calleeSaved) |>.filter
    (!keepInputRegs.contains ·)
  let freeRegs := allPool.filter (!allLiveRegs.contains ·)
  let evictableRegs := allPool.filter (allLiveRegs.contains ·)
  let snipPool := freeRegs ++ evictableRegs
  if snipPool.isEmpty then
    throw s!"snippet '{sDirect.name}' has 0 registers in snipPool (kept={keepInputRegs.length})"
  let origDestRegs := (List.range nvSnip).filterMap fun v =>
    match hSnip.dest.find? v with | some (.gpr r) => some r | _ => none
  let origParamRegs := z.lidMap.flatMap fun (lid1, _) =>
    match hSnip.entry.find? lid1 with
    | some en => en.ploc.filterMap fun | .gpr r => some r | _ => none
    | none => []
  let origRegs := dedupList (origDestRegs ++ origParamRegs)
  if origRegs.length > allPool.length then
    throw s!"snippet '{sDirect.name}' requires {origRegs.length} GPRs > {allPool.length} \
available (kept={keepInputRegs.length})"
  let retPrefPairs : List (I.Reg × I.Reg) :=
    (I.frame.retRegs.take contRetRegs.length).zip contRetRegs
  let rec mapPool (used : List I.Reg) : List I.Reg → List (I.Reg × I.Reg)
    | [] => []
    | r :: rs =>
      let retPref? := match retPrefPairs.find? (·.1 == r) with
        | some (_, cr) =>
          if snipPool.contains cr && !used.contains cr then some cr else none
        | none => none
      let selfFree? := match retPref? with
        | some _ => retPref?
        | none =>
          if freeRegs.contains r && !used.contains r then some r else none
      let chosen := match selfFree? with
        | some pr => pr
        | none => snipPool.find? (!used.contains ·) |>.getD (snipPool.head?.getD I.frame.sp)
      (r, chosen) :: mapPool (if used.contains chosen then used else chosen :: used) rs
  let phiSnip := mapPool [] origRegs
  let mapR (r : I.Reg) : I.Reg := (phiSnip.find? (·.1 == r)).map Prod.snd |>.getD r
  let mapLoc : I.Loc → I.Loc
    | .gpr r => .gpr (mapR r)
    | other => other
  let usedRegs := dedupList (phiSnip.map Prod.snd)
  -- Invariant #4: evict used outer live registers (excluding `contRetRegs`).
  let evictRegs := usedRegs.filter fun r => allLiveRegs.contains r && !contRetRegs.contains r
  let baseSlot := hOuter.nslots
  let evictPairs := evictRegs.zip (List.range' baseSlot evictRegs.length)
  let findEvictSlot (r : I.Reg) : Option Nat := (evictPairs.find? (·.1 == r)).map Prod.snd
  -- Splice `dest`, `elide`, `variant`, `invertJnz` from `hSnip` onto `hOuter`.
  let mut dest' := hOuter.dest
  for (v1, v2) in z.nvMap do
    if let some loc := hSnip.dest.find? v1 then
      dest' := dest'.insert v2 (mapLoc loc)
  let mut elide' := hOuter.elide
  let mut variant' := hOuter.variant
  let mut invJnz' := hOuter.invertJnz
  for (ip1, ip2) in z.ipMap do
    elide' := if let some e := hSnip.elide.find? ip1 then elide'.insert ip2 e else elide'.erase ip2
    variant' :=
      if let some vh := hSnip.variant.find? ip1 then variant'.insert ip2 vh else variant'.erase ip2
    invJnz' :=
      if let some iv := hSnip.invertJnz.find? ip1 then invJnz'.insert ip2 iv else invJnz'.erase ip2
  -- Rewrite `contLid.live` and internal `lid2.live`.
  let mut entry' := hOuter.entry
  if let some enCont := enCont? then
    let live' := enCont.live.map fun (sa, loc) =>
      match loc with
      | .gpr r =>
        match findEvictSlot r with
        | some sIdx => (sa, Loc.slot sIdx .w64)
        | none => (sa, loc)
      | other => (sa, other)
    entry' := entry'.insert reg.contLid { enCont with live := live' }
  for (lid1, lid2) in z.lidMap do
    let ploc' := match hSnip.entry.find? lid1 with
      | some enS => enS.ploc.map mapLoc
      | none => (hOuter.entry.find? lid2).map (·.ploc) |>.getD []
    let (liveOuter, liveZOuter) := match hOuter.entry.find? lid2 with
      | some enO =>
        let rec go : List (SymArg × I.Loc) → List Bool → List (SymArg × I.Loc) × List Bool
          | [], _ => ([], [])
          | (sa, loc) :: rest, zs =>
            let z := zs.headD false
            let (rs, rzs) := go rest zs.tail
            match sa with
            | .var w =>
              if Live.trieMem calleeNvSet w then
                match dest'.find? w with
                | some dl => ((sa, dl) :: rs, false :: rzs)
                | none => (rs, rzs)
              else
                match loc with
                | .gpr r =>
                  match findEvictSlot r with
                  | some sIdx => ((sa, Loc.slot sIdx .w64) :: rs, z :: rzs)
                  | none => ((sa, loc) :: rs, z :: rzs)
                | other => ((sa, other) :: rs, z :: rzs)
            | _ => ((sa, loc) :: rs, z :: rzs)
        go enO.live enO.liveZ
      | none => ([], [])
    entry' := entry'.insert lid2
      { live := liveOuter, ploc := ploc', liveZ := liveZOuter, plocZ := [] }
  -- Update `saved` registers cleanly.
  let extraSaved := usedRegs.filter (I.frame.calleeSaved.contains ·)
  let saved' := dedupList (hOuter.saved ++ extraSaved)
  -- Invariant #3: hoist outer `Move.st`s from `calleeIps` onto `startIp`, keep outer `.ld`s,
  -- and clear snippet interior spill moves.
  let outerSlots := collectOuterSlots I reg.calleeNvs nvTotal hOuter enCont?
  let calleeOnlySlots := collectCalleeOnlySlots I reg.calleeNvs hOuter outerSlots
  let calleeOnlySlotSet := Live.trieOfList calleeOnlySlots
  let hoistedSts : List I.Move := reg.calleeIps.flatMap fun ip =>
    match hOuter.pre.find? ip with
    | some ps =>
      ps.moves.filter fun
        | .st sIdx _ => !Live.trieMem calleeOnlySlotSet sIdx
        | _ => false
    | none => []
  let outerLoadSteps : List (Nat × List I.Move) := outerIps.filterMap fun ip =>
    match hOuter.pre.find? ip with
    | some ps =>
      let lds := ps.moves.filter fun
        | .ld _ _ => true
        | _ => false
      if lds.isEmpty then none else some (ip, lds)
    | none => none
  let mut pre' := reg.calleeIps.foldl (fun p ip => p.erase ip) hOuter.pre
  -- Preserve any `clearFlags` from `hSnip.pre` at mapped `ip2`s, plus outer `Move.ld`s at non-start IPs.
  let mut keptLdCount : Nat := 0
  for (ip1, ip2) in z.ipMap do
    if let some ps1 := hSnip.pre.find? ip1 then
      if ps1.clearFlags then
        let cur := pre'.getD ip2 {}
        pre' := pre'.insert ip2 { cur with clearFlags := true }
  let mut startExtraLds : List I.Move := []
  for (ip, lds) in outerLoadSteps do
    keptLdCount := keptLdCount + lds.length
    if ip == reg.startIp then
      startExtraLds := startExtraLds ++ lds
    else
      let cur := pre'.getD ip {}
      pre' := pre'.insert ip { cur with moves := cur.moves ++ lds }
  let stMoves : List I.Move := evictPairs.map fun (r, sIdx) => .st sIdx r
  let ldMoves : List I.Move := evictPairs.map fun (r, sIdx) => .ld r sIdx
  let preStart := pre'.getD reg.startIp {}
  pre' := pre'.insert reg.startIp
    { preStart with moves := hoistedSts ++ stMoves ++ startExtraLds ++ preStart.moves }
  let preExit := pre'.getD reg.exitNextIp {}
  pre' := pre'.insert reg.exitNextIp
    { preExit with moves := ldMoves ++ preExit.moves }
  let nslots' := baseSlot + evictPairs.length
  let hNew0 : I.Hints := {
    dest := dest'
    entry := entry'
    pre := pre'
    elide := elide'
    variant := variant'
    invertJnz := invJnz'
    saved := saved'
    nslots := nslots'
  }
  let hNew := Rega.addDeferHints hNew0 outerLate
  let report : SpillSnippetReport I.Reg := {
    startIp := reg.startIp
    exitNextIp := reg.exitNextIp
    matchedByMark := byMark
    usedRegs := usedRegs
    keepInputRegs := keepInputRegs
    freeRegs := freeRegs
    evictedRegs := evictRegs
    hoistedSts := hoistedSts.length
    keptOuterLds := keptLdCount
    nslotsBefore := baseSlot
    nslotsAfter := nslots'
  }
  pure (hNew, report)

end SpillSnippet

end LeanQbe.T
