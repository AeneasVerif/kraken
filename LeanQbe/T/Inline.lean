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
/-- True iff `Expr` contains at least one `.call` node. -/
def exprHasCall {rs : List Ty} : Expr (fun _ => Unit) (fun _ => Unit) rs → Bool
  | .let_ _ k => exprHasCall (k (Tup.units _))
  | .load _ _ k => exprHasCall (k ())
  | .store _ _ k => exprHasCall k
  | .call _ _ _ => true
  | .jnz _ t e => exprHasCall t || exprHasCall e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => false
  | .group (sig := sig) bodies k =>
      blocksHasCall (bodies (Tup.units sig)) || exprHasCall (k (Tup.units sig))

/-- Block-list companion of `exprHasCall`. -/
def blocksHasCall {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → Bool
  | _, .nil => false
  | _, .cons b bs => exprHasCall (b (Tup.units _)) || blocksHasCall bs
end

/-- True iff `fn` makes zero `.call`s (a leaf function). -/
def Fn.isLeaf (fn : Fn) : Bool :=
  !exprHasCall (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))

/-- Policy controlling per-callee size budgets, leaf/single-site elevation, caller size caps,
and explicit out-of-line exclusions. -/
structure InlinePolicy where
  /-- Base IR node-count budget per callee symbol. -/
  budget : Sym → Nat := fun _ => 40
  /-- Elevated node-count cap for call-free (leaf) callees (`0` off). -/
  leafMax : Nat := 0
  /-- Elevated node-count cap when a callee has exactly 1 static call site (`0` off). -/
  singleSiteMax : Nat := 0
  /-- Maximum caller IR node count allowed when inlining callees (`0` uncapped). -/
  maxCallerSize : Nat := 0
  /-- Callee symbols that must always stay out-of-line. -/
  keepOutOfLine : List String := []

/-- Constant-budget policy matching the legacy `maxSize : Nat` threshold. -/
def InlinePolicy.const (maxSize : Nat := 40) : InlinePolicy :=
  { budget := fun _ => maxSize }

/-- Tuned Train B5-4 inline policy: keeps `full_watch_push` and cold/bloating helpers
out-of-line while elevating leaf (`≤ 106`) and single-site (`≤ 190`) hot callees under a
`660`-node caller cap. -/
def InlinePolicy.b5 : InlinePolicy :=
  { budget := fun _ => 40
    leafMax := 106
    singleSiteMax := 190
    maxCallerSize := 660
    keepOutOfLine :=
      [ "full_watch_push", "full_search", "full_extend", "full_init_state", "full_init_arenas",
        "full_init_hdr", "full_init_ptrs", "full_zero_tables1", "full_zero_tables2",
        "full_parse_body", "full_ingest_cl", "kissat_parse_header", "kissat_check_model",
        "kissat_read_nat", "kissat_skip_ws1", "kissat_skip_ws_comments", "full_cong_extract",
        "full_cong_try_xor_ite", "full_compact_bins", "full_compact_vars",
        "full_compact_record_ext", "full_compact_vmtf", "full_compact_arena",
        "full_compact_mark_live", "full_compact_assign_map", "full_compact_sift_q",
        "full_compact_sift_h", "full_compact_flush", "full_subst_elim_vars",
        "full_subst_rewrite_bins", "full_subst_rewrite_ar", "full_lucky_scan", "full_lucky",
        "full_congruence_dense", "full_bve_gates", "full_bve_try_bce", "full_bve_commit_res",
        "full_bve_collect", "full_bve_mark_and", "full_eager_subsume", "full_learn_clause",
        "full_ema_update", "full_tick_rel", "full_rephase", "full_switch_mode", "full_warmup",
        "full_decide", "full_restart", "full_restart_due", "full_simplify", "full_reorder",
        "full_tumble_clauses", "full_sweep_dense", "full_forward_sub", "full_fwd_dedup_bins",
        "full_elim_bve", "full_elim_collect_nbrs", "full_bva_pick_cand", "full_bva_hop3",
        "full_bva_match_large", "full_init_fresh_var", "full_tarjan_pop_scc", "full_kitten_mtf",
        "full_kitten_build_failing", "full_kitten_assign", "full_kitten_watch",
        "full_kitten_backtrack", "full_viv_clause", "full_viv_sort_lits", "full_promote_reasons",
        "full_promote_clause", "full_compute_lbd", "full_mark_reasons", "full_recompute_tiers",
        "full_otfs_subsume", "full_red_sift", "full_heap_down", "full_heap_pop",
        "full_sweep_copy", "full_arena_next", "full_fheap_up", "full_fheap_down",
        "full_wsort_sift", "full_walk_pick_lit", "full_walk_collect", "full_save_target_best",
        "full_bump_decay", "full_queue_renumber", "full_unwatch_large", "full_viv_simplify",
        "full_viv_commit", "full_otfs_bin", "full_one_lit_confl", "full_ternary_collect",
        "full_ternary_resolve_bin", "full_ternary_round", "full_ternary_match_bin",
        "full_ternary", "full_cong_mark_trail", "full_cong_emit_xor", "full_cong_and_match",
        "full_cong_equiv_fold", "full_delete_bin_side", "full_score_sift", "full_has_bin",
        "full_find_repl", "full_extend_push_cl", "full_sweep_refine_kitten",
        "full_reorder_queue", "full_cong_merge", "full_set_inactive", "full_calc_max_v",
        "full_probe_tail", "lb_check_prf" ] }

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

/-- True iff `fn` is not in `keepOutOfLine`, satisfies `policy`'s effective size budget,
and passes `checkCallsOk`. -/
def inlineCandidateOkPolicy (policy : InlinePolicy) (sites : Nat)
    (allowed : List SigEntry) (exits : List Sym) (fn : Fn) : Bool :=
  !policy.keepOutOfLine.contains fn.name &&
  Nat.ble fn.size (policy.effectiveBudget sites fn.isLeaf fn.name) &&
  fn.checkCallsOk allowed exits

/-- Insert `fn` into a `Fn` list sorted ascending by `Fn.size`. -/
def insertBySize (fn : Fn) : List Fn → List Fn
  | [] => [fn]
  | c :: cs => if fn.size ≤ c.size then fn :: c :: cs else c :: insertBySize fn cs

/-- Sort `cands` ascending by `Fn.size` so smallest callees fit first under `maxCallerSize`. -/
def sortCandsBySize : List Fn → List Fn
  | [] => []
  | c :: cs => insertBySize c (sortCandsBySize cs)

/-- Greedily filter `cands` so `curSz + ∑ (sitesInCaller * callee.size) ≤ maxSz`. -/
def selectCandsAux (callerCalls : List (Sym × Nat)) (maxSz : Nat) :
    Nat → List Fn → List Fn
  | _, [] => []
  | curSz, c :: cs =>
      let k := lookupCallSite callerCalls c.name
      if k == 0 then selectCandsAux callerCalls maxSz curSz cs
      else
        let add := k * c.size
        if curSz + add ≤ maxSz then
          c :: selectCandsAux callerCalls maxSz (curSz + add) cs
        else
          selectCandsAux callerCalls maxSz curSz cs

/-- Filter `cands` for caller `fn` according to `policy.maxCallerSize`. -/
def selectCandsForCaller (policy : InlinePolicy) (cands : List Fn) (fn : Fn) : List Fn :=
  if policy.maxCallerSize == 0 then cands
  else if fn.size > policy.maxCallerSize then []
  else
    let callerCalls := exprCallSites [] (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))
    selectCandsAux callerCalls policy.maxCallerSize fn.size (sortCandsBySize cands)

/-- Incrementally inline prior eligible callees across a callee-first function list under
`policy` and precomputed `siteCounts`, keeping the original function order and signatures. -/
def inlineFnsPolicy (policy : InlinePolicy) (siteCounts : List (Sym × Nat))
    (extSigs : List SigEntry) (exits : List Sym) :
    List SigEntry → List Fn → List Fn → List Fn
  | _, _, [] => []
  | seenSigs, cands, fn :: rest =>
      let candsFn := selectCandsForCaller policy cands fn
      let fn' := fn.inline candsFn
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

/-- Run acyclic small-callee inlining on `M` with node-size threshold `maxSize` (default `40`),
preserving function order, signatures, `externs`, `exits`, `sigs`, and `namesNodup`. -/
def Module.inline (M : Module) (maxSize : Nat := 40) : Module :=
  M.inlinePolicy (InlinePolicy.const maxSize)

end LeanQbe.T
