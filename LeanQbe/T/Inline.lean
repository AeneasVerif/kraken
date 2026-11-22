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

/-- Policy controlling per-callee size budgets and single-call-site elevation. -/
structure InlinePolicy where
  /-- Base IR node-count budget per callee symbol. -/
  budget : Sym → Nat := fun _ => 40
  /-- Elevated node-count cap when a callee has exactly 1 static call site (`0` off). -/
  singleSiteMax : Nat := 0

/-- Constant-budget policy matching the legacy `maxSize : Nat` threshold. -/
def InlinePolicy.const (maxSize : Nat := 40) : InlinePolicy :=
  { budget := fun _ => maxSize, singleSiteMax := 0 }

/-- Effective size budget for `sym` given its static call-site count `sites`. -/
def InlinePolicy.effectiveBudget (policy : InlinePolicy) (sites : Nat) (sym : Sym) : Nat :=
  if policy.singleSiteMax > 0 && sites == 1 then
    Nat.max (policy.budget sym) policy.singleSiteMax
  else
    policy.budget sym

/-- True iff `fn` satisfies `policy`'s effective size budget and `checkCallsOk`. -/
def inlineCandidateOkPolicy (policy : InlinePolicy) (sites : Nat)
    (allowed : List SigEntry) (exits : List Sym) (fn : Fn) : Bool :=
  Nat.ble fn.size (policy.effectiveBudget sites fn.name) && fn.checkCallsOk allowed exits

/-- Incrementally inline prior eligible callees across a callee-first function list under
`policy` and precomputed `siteCounts`, keeping the original function order and signatures. -/
def inlineFnsPolicy (policy : InlinePolicy) (siteCounts : List (Sym × Nat))
    (extSigs : List SigEntry) (exits : List Sym) :
    List SigEntry → List Fn → List Fn → List Fn
  | _, _, [] => []
  | seenSigs, cands, fn :: rest =>
      let fn' := fn.inline cands
      let allowed := seenSigs ++ extSigs
      let sites := lookupCallSite siteCounts fn'.name
      let cands' :=
        if inlineCandidateOkPolicy policy sites allowed exits fn' then fn' :: cands else cands
      fn' :: inlineFnsPolicy policy siteCounts extSigs exits (seenSigs ++ [fn.sig]) cands' rest

/-- Run acyclic policy-driven inlining on `M`, preserving function order, signatures,
`externs`, `exits`, `sigs`, and `namesNodup`. -/
def Module.inlinePolicy (M : Module) (policy : InlinePolicy := {}) : Module :=
  let siteCounts := if policy.singleSiteMax > 0 then fnsCallSites M.fns else []
  { M with
    fns := inlineFnsPolicy policy siteCounts (M.externs.map Extern.sig) M.exits [] [] M.fns }

/-- True iff `fn` has body size `≤ maxSize` and only calls/exits within `(allowed, exits)`. -/
def inlineCandidateOk (maxSize : Nat) (allowed : List SigEntry) (exits : List Sym)
    (fn : Fn) : Bool :=
  Nat.ble fn.size maxSize && fn.checkCallsOk allowed exits

/-- Incrementally inline prior small safe callees across a callee-first function list, keeping
the original function order and signatures. -/
def inlineFns (maxSize : Nat) (extSigs : List SigEntry) (exits : List Sym) :
    List SigEntry → List Fn → List Fn → List Fn :=
  inlineFnsPolicy (InlinePolicy.const maxSize) [] extSigs exits

/-- Run acyclic small-callee inlining on `M` with node-size threshold `maxSize` (default `40`),
preserving function order, signatures, `externs`, `exits`, `sigs`, and `namesNodup`. -/
def Module.inline (M : Module) (maxSize : Nat := 40) : Module :=
  M.inlinePolicy (InlinePolicy.const maxSize)

end LeanQbe.T
