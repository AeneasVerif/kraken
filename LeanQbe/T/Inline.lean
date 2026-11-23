module

public import LeanQbe.T.Module
public import LeanQbe.T.OptUtil

/-!
# Acyclic Small-Callee Inlining (`O-M1`)

Pure 100%-PHOAS module-level small-callee inliner (`Module.inline`) with zero de Bruijn shifting:

* `exprSize` / `Func.size` / `Fn.size`: unit-erased IR node-count size metric.
* `spliceRet`: splices a callee body instantiated at `Arg V` and caller label type `L`, flattening
  two-level operands `Arg (Arg V)` directly to `Arg V` (handling both `.var` and `.imm` call
  arguments with no extra `copy` bindings) and rewriting every `.ret vs` to `.jump joinLbl vs`.
  Internal `.group` labels remain directly bound in `L`.
* `inlineExpr` / `Func.inline` / `Fn.inline`: replaces matching `.call f args k` sites with a
  1-block `.group (sig := [bs])` hosting `fun xs => inlineExpr cands (k xs)` and entering
  `spliceRet joinLbl (callee (Arg V) L args)`.
* `Module.inline`: walks `M.fns` in acyclic callees-first order, accumulating already-inlined
  small safe callees (`size ≤ maxSize` and `checkCallsOk`) while keeping `M.fns` order,
  signatures, `externs`, `exits`, `sigs`, and `namesNodup` unchanged.

Correctness (`LeanQbe/T/InlineLemmas.lean`): `spliceRet_wp`, `inline_wp`, `inline_wf`,
`inline_callsOk`, `Module.inline_ok`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## IR size measurement -/

mutual
/-- Count IR nodes of a unit-erased expression (`0`-cost PHOAS traversal). -/
def exprSize {rs : List Ty} : Expr (fun _ => Unit) (fun _ => Unit) rs → Nat
  | .let_ _ k => 1 + exprSize (k (Tup.units _))
  | .load _ _ k => 1 + exprSize (k ())
  | .store _ _ k => 1 + exprSize k
  | .call _ (bs := bs) _ k => 1 + exprSize (k (Tup.units bs))
  | .jnz _ t e => 1 + exprSize t + exprSize e
  | .jump _ _ => 1
  | .ret _ => 1
  | .exit _ _ => 1
  | .hlt => 1
  | .group (sig := sig) bodies k =>
      1 + blocksSize (bodies (Tup.units sig)) + exprSize (k (Tup.units sig))

/-- Count IR nodes across a block list. -/
def blocksSize {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => exprSize (b (Tup.units _)) + blocksSize bs
end

/-- Body node count of a closed function `Func`. -/
def Func.size {as rs : List Ty} (f : Func as rs) : Nat :=
  exprSize (f (fun _ => Unit) (fun _ => Unit) (Tup.units as))

/-- Body node count of a named function `Fn`. -/
def Fn.size (fn : Fn) : Nat :=
  Func.size fn.body

/-! ## `.ret`-to-`.jump` splicing (using `OptUtil` operand flattening) -/

mutual
/-- Splice a callee body instantiated at `Arg V` and caller label type `L` into a caller
returning `callerRs`, turning every `.ret vs` into `.jump joinLbl (flattenArgs vs)`. -/
def spliceRet {V : Ty → Type} {L : List Ty → Type} {calleeRs callerRs : List Ty}
    (joinLbl : L calleeRs) : Expr (Arg V) L calleeRs → Expr V L callerRs
  | .let_ op k => .let_ (flattenOp op) fun xs => spliceRet joinLbl (k (toArgTup xs))
  | .load t a k => .load t (flattenArg a) fun v => spliceRet joinLbl (k (.var v))
  | .store v a k => .store (flattenArg v) (flattenArg a) (spliceRet joinLbl k)
  | .call f args k => .call f (flattenArgs args) fun xs => spliceRet joinLbl (k (toArgTup xs))
  | .jnz c t e => .jnz (flattenArg c) (spliceRet joinLbl t) (spliceRet joinLbl e)
  | .jump j args => .jump j (flattenArgs args)
  | .ret vs => .jump joinLbl (flattenArgs vs)
  | .exit f args => .exit f (flattenArgs args)
  | .hlt => .hlt
  | .group bodies k =>
      .group (fun Js => spliceRetB joinLbl (bodies Js)) (fun Js => spliceRet joinLbl (k Js))

/-- Block-list companion of `spliceRet`. -/
def spliceRetB {V : Ty → Type} {L : List Ty → Type} {calleeRs callerRs : List Ty}
    (joinLbl : L calleeRs) :
    {sig : List (List Ty)} → Blocks (Arg V) L calleeRs sig → Blocks V L callerRs sig
  | _, .nil => .nil
  | _, .cons b bs =>
      .cons (fun xs => spliceRet joinLbl (b (toArgTup xs))) (spliceRetB joinLbl bs)
end

/-! ## Callee lookup and PHOAS callsite inlining -/

/-- Look up an inlineable callee matching `(f, as, bs)` in `cands`, returning its typed body. -/
def lookupCallee : List Fn → Sym → (as bs : List Ty) → Option (Func as bs)
  | [], _, _, _ => none
  | fn :: rest, f, as, bs =>
      if fn.name == f then
        match listTyDecEq fn.as as, listTyDecEq fn.rs bs with
        | isTrue ha, isTrue hr => some (ha ▸ hr ▸ fn.body)
        | _, _ => lookupCallee rest f as bs
      else lookupCallee rest f as bs

mutual
/-- Inline calls to `cands` in `Expr V L rs`, splicing callee bodies via a 1-block join
`.group` around the call continuation. -/
def inlineExpr (cands : List Fn) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr V L rs → Expr V L rs
  | .let_ op k => .let_ op fun xs => inlineExpr cands (k xs)
  | .load t a k => .load t a fun v => inlineExpr cands (k v)
  | .store v a k => .store v a (inlineExpr cands k)
  | .call f (as := as) (bs := bs) args k =>
      match lookupCallee cands f as bs with
      | some callee =>
          .group (sig := [bs])
            (fun _ => .cons (fun xs => inlineExpr cands (k xs)) .nil)
            (fun Js => spliceRet Js.1 (callee (Arg V) L args))
      | none =>
          .call f args fun xs => inlineExpr cands (k xs)
  | .jnz c t e => .jnz c (inlineExpr cands t) (inlineExpr cands e)
  | .jump j args => .jump j args
  | .ret vs => .ret vs
  | .exit f args => .exit f args
  | .hlt => .hlt
  | .group bodies k =>
      .group (fun Js => inlineBlocks cands (bodies Js)) (fun Js => inlineExpr cands (k Js))

/-- Block-list companion of `inlineExpr`. -/
def inlineBlocks (cands : List Fn) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Blocks V L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons b bs => .cons (fun xs => inlineExpr cands (b xs)) (inlineBlocks cands bs)
end

/-- Inline calls to `cands` inside a closed function `Func`. -/
def Func.inline (cands : List Fn) {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs => inlineExpr cands (f V L xs)

/-- Inline calls to `cands` inside a named function `Fn`, keeping `name`, `as`, and `rs`. -/
def Fn.inline (cands : List Fn) (fn : Fn) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.inline cands fn.body⟩

/-! ## Module-level acyclic small-callee and policy-driven inliner -/

/-- Increment the static call-site count for `sym` in an association list. -/
def incCallSite : List (Sym × Nat) → Sym → List (Sym × Nat)
  | [], s => [(s, 1)]
  | (k, n) :: rest, s =>
      if k == s then (k, n + 1) :: rest else (k, n) :: incCallSite rest s

/-- Look up the static call-site count for `sym` (`0` if absent). -/
def lookupCallSite : List (Sym × Nat) → Sym → Nat
  | [], _ => 0
  | (k, n) :: rest, s => if k == s then n else lookupCallSite rest s

mutual
/-- Count static `.call` occurrences per callee symbol inside `Expr`. -/
def exprCallSites {rs : List Ty} (acc : List (Sym × Nat)) :
    Expr (fun _ => Unit) (fun _ => Unit) rs → List (Sym × Nat)
  | .let_ _ k => exprCallSites acc (k (Tup.units _))
  | .load _ _ k => exprCallSites acc (k ())
  | .store _ _ k => exprCallSites acc k
  | .call f (bs := bs) _ k =>
      exprCallSites (incCallSite acc f) (k (Tup.units bs))
  | .jnz _ t e => exprCallSites (exprCallSites acc t) e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => acc
  | .group (sig := sig) bodies k =>
      exprCallSites (blocksCallSites acc (bodies (Tup.units sig))) (k (Tup.units sig))

/-- Block-list companion of `exprCallSites`. -/
def blocksCallSites {rs : List Ty} (acc : List (Sym × Nat)) :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig →
    List (Sym × Nat)
  | _, .nil => acc
  | _, .cons b bs => blocksCallSites (exprCallSites acc (b (Tup.units _))) bs
end

/-- Count static `.call` occurrences for every callee across a function list. -/
def fnsCallSites (fns : List Fn) : List (Sym × Nat) :=
  fns.foldl
    (fun acc fn =>
      exprCallSites acc (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as)))
    []

mutual
/-- Count `.call` nodes in `Expr`. -/
def exprNumCalls {rs : List Ty} : Expr (fun _ => Unit) (fun _ => Unit) rs → Nat
  | .let_ _ k => exprNumCalls (k (Tup.units _))
  | .load _ _ k => exprNumCalls (k ())
  | .store _ _ k => exprNumCalls k
  | .call _ (bs := bs) _ k => 1 + exprNumCalls (k (Tup.units bs))
  | .jnz _ t e => exprNumCalls t + exprNumCalls e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group (sig := sig) bodies k =>
      blocksNumCalls (bodies (Tup.units sig)) + exprNumCalls (k (Tup.units sig))

/-- Block-list companion of `exprNumCalls`. -/
def blocksNumCalls {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => exprNumCalls (b (Tup.units _)) + blocksNumCalls bs
end

/-- True iff `fn` makes zero `.call`s (a leaf function). -/
def Fn.isLeaf (fn : Fn) : Bool :=
  exprNumCalls (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as)) == 0

/-- Total static `.call` count inside `fn`. -/
def Fn.numCalls (fn : Fn) : Nat :=
  exprNumCalls (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))

mutual
/-- True iff `Expr` contains a `.jump` targeting label ID `target`. -/
def exprJumpsTo (target : Nat) {rs : List Ty} (nl : Nat) :
    Expr (fun _ => Unit) (fun _ => Nat) rs → Bool
  | .let_ _ k => exprJumpsTo target nl (k (Tup.units _))
  | .load _ _ k => exprJumpsTo target nl (k ())
  | .store _ _ k => exprJumpsTo target nl k
  | .call _ (bs := bs) _ k => exprJumpsTo target nl (k (Tup.units bs))
  | .jnz _ t e => exprJumpsTo target nl t || exprJumpsTo target nl e
  | .jump j _ => j == target
  | .ret _ | .exit _ _ | .hlt => false
  | .group (sig := sig) bodies k =>
      let ls := Tup.levels sig nl
      let nl' := nl + sig.length
      blocksJumpsTo target nl' (bodies ls) || exprJumpsTo target nl' (k ls)

/-- Block-list companion of `exprJumpsTo`. -/
def blocksJumpsTo (target : Nat) {rs : List Ty} (nl : Nat) :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Nat) rs sig → Bool
  | _, .nil => false
  | _, .cons b bs => exprJumpsTo target nl (b (Tup.units _)) || blocksJumpsTo target nl bs
end

mutual
/-- Count self-jumping single-block loop `.group`s in `Expr`. -/
def exprLoopsAux {rs : List Ty} (nl : Nat) : Expr (fun _ => Unit) (fun _ => Nat) rs → Nat
  | .let_ _ k => exprLoopsAux nl (k (Tup.units _))
  | .load _ _ k => exprLoopsAux nl (k ())
  | .store _ _ k => exprLoopsAux nl k
  | .call _ (bs := bs) _ k => exprLoopsAux nl (k (Tup.units bs))
  | .jnz _ t e => exprLoopsAux nl t + exprLoopsAux nl e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group (sig := sig) bodies k =>
      let ls := Tup.levels sig nl
      let nl' := nl + sig.length
      let bs := bodies ls
      let lp := match sig with
        | [_] => if blocksJumpsTo nl nl' bs then 1 else 0
        | _ => 0
      lp + blocksLoopsAux nl' bs + exprLoopsAux nl' (k ls)

/-- Block-list companion of `exprLoopsAux`. -/
def blocksLoopsAux {rs : List Ty} (nl : Nat) :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Nat) rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => exprLoopsAux nl (b (Tup.units _)) + blocksLoopsAux nl bs
end

/-- Number of self-jumping loop `.group`s inside `fn`. -/
def Fn.numLoops (fn : Fn) : Nat :=
  exprLoopsAux 0 (fn.body (fun _ => Unit) (fun _ => Nat) (Tup.units fn.as))

mutual
/-- Accumulate static `.call` sites occurring inside self-jumping loop `.group`s. -/
def exprLoopSitesAux {rs : List Ty} (nl : Nat) (inLoop : Bool) (acc : List (Sym × Nat)) :
    Expr (fun _ => Unit) (fun _ => Nat) rs → List (Sym × Nat)
  | .let_ _ k => exprLoopSitesAux nl inLoop acc (k (Tup.units _))
  | .load _ _ k => exprLoopSitesAux nl inLoop acc (k ())
  | .store _ _ k => exprLoopSitesAux nl inLoop acc k
  | .call f (bs := bs) _ k =>
      let acc' := if inLoop then incCallSite acc f else acc
      exprLoopSitesAux nl inLoop acc' (k (Tup.units bs))
  | .jnz _ t e => exprLoopSitesAux nl inLoop (exprLoopSitesAux nl inLoop acc t) e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => acc
  | .group (sig := sig) bodies k =>
      let ls := Tup.levels sig nl
      let nl' := nl + sig.length
      let bs := bodies ls
      let isLp := match sig with
        | [_] => blocksJumpsTo nl nl' bs
        | _ => false
      let acc1 := blocksLoopSitesAux nl' (inLoop || isLp) acc bs
      exprLoopSitesAux nl' inLoop acc1 (k ls)

/-- Block-list companion of `exprLoopSitesAux`. -/
def blocksLoopSitesAux {rs : List Ty} (nl : Nat) (inLoop : Bool) (acc : List (Sym × Nat)) :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Nat) rs sig → List (Sym × Nat)
  | _, .nil => acc
  | _, .cons b bs =>
      blocksLoopSitesAux nl inLoop (exprLoopSitesAux nl inLoop acc (b (Tup.units _))) bs
end

/-- Record the minimum transitive hop distance `d` from a loop-hot call site for `k`. -/
def setMinLoopDepth : List (Sym × Nat) → Sym → Nat → List (Sym × Nat)
  | [], k, d => [(k, d)]
  | (s, n) :: rest, k, d =>
      if s == k then (s, Nat.min n d) :: rest else (s, n) :: setMinLoopDepth rest k d

/-- Look up the minimum transitive hop distance from a loop (`none` if unreachable). -/
def lookupLoopDepth? : List (Sym × Nat) → Sym → Option Nat
  | [], _ => none
  | (s, n) :: rest, k => if s == k then some n else lookupLoopDepth? rest k

/-- Count static `.call` sites inside loops across `fns`, propagating loop-hotness
top-down across caller-before-callee `fns.reverse` up to `maxHops` callee hops. -/
def fnsLoopCallSitesBounded (maxHops : Nat) (fns : List Fn) : List (Sym × Nat) :=
  let step (st : List (Sym × Nat) × List (Sym × Nat)) (fn : Fn) :=
    let (acc, depths) := st
    let bodyLoop := fn.body (fun _ => Unit) (fun _ => Nat) (Tup.units fn.as)
    let direct := exprLoopSitesAux 0 false [] bodyLoop
    let acc1 := exprLoopSitesAux 0 false acc bodyLoop
    let depths1 := direct.foldl (fun dep (s, _) => setMinLoopDepth dep s 0) depths
    match lookupLoopDepth? depths fn.name with
    | some d =>
        if d < maxHops then
          let bodyCalls := fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as)
          let callees := exprCallSites [] bodyCalls
          let acc2 := callees.foldl
            (fun a (s, _) => if lookupCallSite a s > 0 then a else incCallSite a s) acc1
          let depths2 := callees.foldl
            (fun dep (s, _) => setMinLoopDepth dep s (d + 1)) depths1
          (acc2, depths2)
        else (acc1, depths1)
    | none => (acc1, depths1)
  (fns.reverse.foldl step ([], [])).1

/-- Count static `.call` sites occurring inside loops across a function list,
propagating 1 transitive hop to direct callees of loop-hot functions. -/
def fnsLoopCallSites (fns : List Fn) : List (Sym × Nat) :=
  fnsLoopCallSitesBounded 1 fns

/-- Policy controlling per-callee size budgets, leaf/single-site elevation, structural caps,
caller caps, and optional explicit out-of-line exclusions. -/
structure InlinePolicy where
  /-- Base IR node-count budget per callee symbol. -/
  budget : Sym → Nat := fun _ => 40
  /-- Elevated node-count cap for call-free (leaf) callees (`0` off). -/
  leafMax : Nat := 0
  /-- Elevated node-count cap when a callee has exactly 1 static call site (`0` off). -/
  singleSiteMax : Nat := 0
  /-- Maximum post-inline caller IR node count allowed when inlining callees (`0` uncapped). -/
  maxCallerSize : Nat := 0
  /-- Max `.call` count inside a candidate exceeding base `budget` (`0` uncapped). -/
  maxCalleeCalls : Nat := 0
  /-- Max self-jumping loops inside a candidate exceeding base `budget` (`none` uncapped). -/
  maxCalleeLoops : Option Nat := none
  /-- Max total duplicated nodes `sites * fn.size` for candidates `> budget` (`0` uncapped). -/
  maxTotalDup : Nat := 0
  /-- Elevated total duplicated node cap for loop-free leaf callees when site counts are
  collected (`maxTotalDup > 0` or `singleSiteMax > 0`; `0` uses `maxTotalDup`). -/
  leafNoLoopMaxDup : Nat := 0
  /-- Require ≥ 1 loop-nest call site for candidates exceeding base `budget`. -/
  requireLoopSite : Bool := false
  /-- Max `.call` count in a caller allowed to inline elevated callees (`0` uncapped). -/
  maxCallerCalls : Nat := 0
  /-- Loop-free callee size cap allowed even when caller exceeds `maxCallerCalls` (`0` off). -/
  exemptNoLoopMax : Nat := 0
  /-- Max `callsInCaller * callee.numLoops` per `(caller, callee)` pair (`0` uncapped). -/
  maxCallerLoopDup : Nat := 0
  /-- Minimum callee size eligible for cold single-sided guard exclusion. -/
  coldLoopGuardMin : Nat := 20
  /-- In loop-free callers, block loop callees up to this size when all sites sit behind
  trivial `.jump`/`.ret` `.jnz` guards (`0` off). -/
  coldLoopGuardMax : Nat := 0
  /-- Optional caller-supplied callee symbols that stay out-of-line. -/
  keepOutOfLine : List String := []

/-- Constant-budget policy matching the legacy `maxSize : Nat` threshold. -/
def InlinePolicy.const (maxSize : Nat := 40) : InlinePolicy :=
  { budget := fun _ => maxSize }

/-- Tuned general `b5` inline policy: combines loop-free leaf/hot-helper elevation with
multi-call loop duplication and cold single-sided slow-path guard caps under a `660`-node
caller budget. -/
def InlinePolicy.b5 : InlinePolicy :=
  { budget := fun _ => 40
    leafMax := 115
    singleSiteMax := 190
    maxCallerSize := 660
    maxCalleeCalls := 2
    maxCalleeLoops := some 2
    maxTotalDup := 450
    leafNoLoopMaxDup := 800
    requireLoopSite := true
    maxCallerCalls := 6
    exemptNoLoopMax := 190
    maxCallerLoopDup := 4
    coldLoopGuardMax := 50
    keepOutOfLine := [] }

/-- Effective size budget for `sym` given its static call-site count `sites` and leaf flag. -/
def InlinePolicy.effectiveBudget (policy : InlinePolicy) (sites : Nat) (isLeaf : Bool)
    (sym : Sym) : Nat :=
  if policy.keepOutOfLine.contains sym then 0
  else
    let base := policy.budget sym
    let withLeaf := if policy.leafMax > 0 && isLeaf then Nat.max base policy.leafMax else base
    if policy.singleSiteMax > 0 && sites == 1 then
      Nat.max withLeaf policy.singleSiteMax
    else
      withLeaf

/-- True iff `fn` satisfies `policy`'s structural predicates for elevated (`> budget`) callees. -/
def InlinePolicy.structuralOk (policy : InlinePolicy) (sites loopSites sz : Nat)
    (fn : Fn) : Bool :=
  let base := policy.budget fn.name
  if sz ≤ base then true
  else
    let dupCap :=
      if fn.isLeaf && fn.numLoops == 0 then
        Nat.max policy.maxTotalDup policy.leafNoLoopMaxDup
      else policy.maxTotalDup
    (policy.maxCalleeCalls == 0 || fn.numCalls ≤ policy.maxCalleeCalls) &&
    (match policy.maxCalleeLoops with | none => true | some cap => fn.numLoops ≤ cap) &&
    (dupCap == 0 || sites * sz ≤ dupCap) &&
    (!policy.requireLoopSite || loopSites > 0)

/-- True iff `fn` is not in `keepOutOfLine`, satisfies `policy`'s budget and structural gates,
and passes `checkCallsOk`. -/
def inlineCandidateOkPolicy (policy : InlinePolicy) (sites loopSites : Nat)
    (allowed : List SigEntry) (exits : List Sym) (fn : Fn) : Bool :=
  let sz := fn.size
  !policy.keepOutOfLine.contains fn.name &&
  policy.structuralOk sites loopSites sz fn &&
  Nat.ble sz (policy.effectiveBudget sites fn.isLeaf fn.name) &&
  fn.checkCallsOk allowed exits

/-- Keep only candidates actually called in `callerCalls`, caching each candidate's `Fn.size`
once and gating `> budget` candidates by `allowElevated`. -/
def filterRelevantCands (callerCalls : List (Sym × Nat)) (allowElevated : Bool)
    (budget : Sym → Nat) : List Fn → List (Fn × Nat)
  | [] => []
  | c :: cs =>
      let rest := filterRelevantCands callerCalls allowElevated budget cs
      if lookupCallSite callerCalls c.name == 0 then rest
      else
        let sz := c.size
        if allowElevated || sz ≤ budget c.name then (c, sz) :: rest else rest

/-- Insert `(fn, sz)` into a list sorted ascending by cached size `sz`. -/
def insertPairBySize (p : Fn × Nat) : List (Fn × Nat) → List (Fn × Nat)
  | [] => [p]
  | q :: qs => if p.2 ≤ q.2 then p :: q :: qs else q :: insertPairBySize p qs

/-- Sort `(fn, sz)` pairs ascending by cached `sz` so smallest callees fit first. -/
def sortPairsBySize : List (Fn × Nat) → List (Fn × Nat)
  | [] => []
  | p :: ps => insertPairBySize p (sortPairsBySize ps)

/-- Greedily filter cached `(callee, sz)` pairs so `curSz + ∑ (k * sz) ≤ maxSz`. -/
def selectCandsAux (callerCalls : List (Sym × Nat)) (maxSz : Nat) :
    Nat → List (Fn × Nat) → List Fn
  | _, [] => []
  | curSz, (c, csz) :: cs =>
      let k := lookupCallSite callerCalls c.name
      let add := k * csz
      if curSz + add ≤ maxSz then
        c :: selectCandsAux callerCalls maxSz (curSz + add) cs
      else
        selectCandsAux callerCalls maxSz curSz cs

/-- True if a branch arm contains only pure `let_` bindings before `.jump` or `.ret`. -/
def isTrivialArm {L : List Ty → Type} {rs : List Ty} :
    Expr (fun _ => Unit) L rs → Bool
  | .let_ _ k => isTrivialArm (k (Tup.units _))
  | .jump _ _ | .ret _ => true
  | _ => false

mutual
/-- Collect `(callee, inTrivialSiblingGuard)` pairs across all call sites of an `Expr`. -/
def exprTrivGuardCalls {rs : List Ty} (nl : Nat) (inTriv : Bool) :
    Expr (fun _ => Unit) (fun _ => Nat) rs → List (Sym × Bool)
  | .let_ _ k => exprTrivGuardCalls nl inTriv (k (Tup.units _))
  | .load _ _ k => exprTrivGuardCalls nl inTriv (k ())
  | .store _ _ k => exprTrivGuardCalls nl inTriv k
  | .call f (bs := bs) _ k =>
      (f, inTriv) :: exprTrivGuardCalls nl inTriv (k (Tup.units bs))
  | .jnz _ t e =>
      exprTrivGuardCalls nl (inTriv || isTrivialArm e) t ++
        exprTrivGuardCalls nl (inTriv || isTrivialArm t) e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => []
  | .group (sig := sig) bodies k =>
      let ls := Tup.levels sig nl
      let nl' := nl + sig.length
      blocksTrivGuardCalls nl' inTriv (bodies ls) ++
        exprTrivGuardCalls nl' inTriv (k ls)

/-- Collect `(callee, inTrivialSiblingGuard)` pairs across all blocks of a `Blocks`. -/
def blocksTrivGuardCalls {rs : List Ty} (nl : Nat) (inTriv : Bool) :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Nat) rs sig →
    List (Sym × Bool)
  | _, .nil => []
  | _, .cons b bs =>
      exprTrivGuardCalls nl inTriv (b (Tup.units _)) ++
        blocksTrivGuardCalls nl inTriv bs
end

/-- Filter `cands` for caller `fn` according to `policy.maxCallerSize` and
`policy.maxCallerCalls` in linear `O(N)` pass over `cands` (`Fn.size` computed once per called
candidate). -/
def selectCandsForCaller (policy : InlinePolicy) (cands : List Fn) (fn : Fn) : List Fn :=
  if policy.maxCallerSize == 0 && policy.maxCallerCalls == 0 then cands
  else
    let callerCalls :=
      exprCallSites [] (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))
    let callerNCalls := callerCalls.foldl (fun a p => a + p.2) 0
    let allowElevated := policy.maxCallerCalls == 0 || callerNCalls ≤ policy.maxCallerCalls
    let useGates :=
      policy.maxCallerLoopDup > 0 || policy.coldLoopGuardMax > 0 ||
        policy.exemptNoLoopMax > 0
    let effAllow := if useGates then false else allowElevated
    let effBudget : Sym → Nat :=
      if !useGates then policy.budget
      else
        let callerLoops := fn.numLoops
        let trivCalls :=
          if policy.coldLoopGuardMax > 0 && callerLoops == 0 then
            exprTrivGuardCalls 0 false
              (fn.body (fun _ => Unit) (fun _ => Nat) (Tup.units fn.as))
          else []
        fun s =>
          match cands.find? (fun c => c.name == s) with
          | none => policy.budget s
          | some c =>
            let k := lookupCallSite callerCalls s
            let csz := c.size
            let clp := c.numLoops
            let lpDupFail :=
              policy.maxCallerLoopDup > 0 && clp > 0 &&
                k * clp > policy.maxCallerLoopDup
            let coldGuardFail :=
              policy.coldLoopGuardMax > 0 && callerLoops == 0 && clp > 0 &&
                csz ≥ policy.coldLoopGuardMin && csz ≤ policy.coldLoopGuardMax &&
                trivCalls.any (fun p => p.1 == s) &&
                trivCalls.all (fun p => p.1 != s || p.2)
            if lpDupFail || coldGuardFail then 0
            else if allowElevated || (policy.exemptNoLoopMax > 0 && clp == 0 &&
                csz ≤ policy.exemptNoLoopMax) then
              Nat.max (policy.budget s) csz
            else policy.budget s
    let rel := filterRelevantCands callerCalls effAllow effBudget cands
    if policy.maxCallerSize == 0 then rel.map Prod.fst
    else
      let fsz := fn.size
      if fsz > policy.maxCallerSize then []
      else selectCandsAux callerCalls policy.maxCallerSize fsz (sortPairsBySize rel)

/-- Incrementally inline prior eligible callees across a callee-first function list under
`policy` and precomputed `(siteCounts, loopCounts)`, preserving function order and sigs. -/
def inlineFnsPolicy (policy : InlinePolicy) (siteCounts loopCounts : List (Sym × Nat))
    (extSigs : List SigEntry) (exits : List Sym) :
    List SigEntry → List Fn → List Fn → List Fn
  | _, _, [] => []
  | seenSigs, cands, fn :: rest =>
      let candsFn := selectCandsForCaller policy cands fn
      let fn' := fn.inline candsFn
      let allowed := seenSigs ++ extSigs
      let sites := lookupCallSite siteCounts fn'.name
      let loopSites := lookupCallSite loopCounts fn'.name
      let cands' :=
        if inlineCandidateOkPolicy policy sites loopSites allowed exits fn' then
          fn' :: cands
        else
          cands
      fn' :: inlineFnsPolicy policy siteCounts loopCounts extSigs exits
        (seenSigs ++ [fn.sig]) cands' rest

/-- Run acyclic policy-driven inlining on `M`, preserving function order, signatures,
`externs`, `exits`, `sigs`, and `namesNodup`. -/
def Module.inlinePolicy (M : Module) (policy : InlinePolicy := {}) : Module :=
  let needSites := policy.singleSiteMax > 0 || policy.maxTotalDup > 0
  let siteCounts := if needSites then fnsCallSites M.fns else []
  let loopCounts := if policy.requireLoopSite then fnsLoopCallSites M.fns else []
  { M with
    fns := inlineFnsPolicy policy siteCounts loopCounts
      (M.externs.map Extern.sig) M.exits [] [] M.fns }

/-- True iff `fn` has body size `≤ maxSize` and only calls/exits within `(allowed, exits)`. -/
def inlineCandidateOk (maxSize : Nat) (allowed : List SigEntry) (exits : List Sym)
    (fn : Fn) : Bool :=
  Nat.ble fn.size maxSize && fn.checkCallsOk allowed exits

/-- Run acyclic small-callee inlining on `M` with node-size threshold `maxSize` (default `40`),
preserving function order, signatures, `externs`, `exits`, `sigs`, and `namesNodup`. -/
def Module.inline (M : Module) (maxSize : Nat := 40) : Module :=
  M.inlinePolicy (InlinePolicy.const maxSize)

end LeanQbe.T
