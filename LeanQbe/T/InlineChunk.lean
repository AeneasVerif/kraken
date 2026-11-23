module

public import LeanQbe.T.MainInline

/-!
# Chunked `Module.optInlinePolicy` Decomposition (`InlineChunk`)

Pure definitions and lemmas splitting the sequential policy inliner `inlineFnsPolicy` into
contiguous chunks so that `Module.optInlinePolicy` can be materialized (and kernel-checked) one
slice at a time by `inline_mod_chunk!` (`LeanQbe.T.MainCertInlineChunk`):

* `inlSiteCounts`, `inlLoopCounts`: the global call-site tables computed by `Module.inlinePolicy`.
* `inlineFnsPolicyCands`: the candidate list threaded by `inlineFnsPolicy` after a prefix.
* `inlineFnsPolicy_append`: `inlineFnsPolicy` over `A ++ B` splits cleanly at the state
  (`seenSigs`, `cands`) reached after `A`.
* `inlRest`: renormalized inliner output from position `a` with accumulated `seen` and `cands`.
* `Module.optInlinePolicy_fns_eq_inlRest`, `inlRest_step`, `inlRest_last`: the `O(1)`-per-chunk
  chain that rebuilds `(M.optInlinePolicy policy).fns` from per-chunk equalities without
  re-evaluating earlier chunks.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Placeholder function returned by `fnAt` past the end of a list. -/
def Fn.chunkDflt : Fn := ⟨"", [], [], fun _ _ _ => .hlt⟩

/-- Positional function lookup (`Fn.chunkDflt` when out of range). -/
def fnAt : List Fn → Nat → Fn
  | [], _ => Fn.chunkDflt
  | f :: _, 0 => f
  | _ :: fs, n + 1 => fnAt fs n

/-- Static call-site table computed by `Module.inlinePolicy` for `policy` over `fns`. -/
def inlSiteCounts (policy : InlinePolicy) (fns : List Fn) : List (Sym × Nat) :=
  if policy.singleSiteMax > 0 || policy.maxTotalDup > 0 then fnsCallSites fns else []

/-- Loop call-site table computed by `Module.inlinePolicy` for `policy` over `fns`. -/
def inlLoopCounts (policy : InlinePolicy) (fns : List Fn) : List (Sym × Nat) :=
  if policy.requireLoopSite then fnsLoopCallSites fns else []

/-- Candidate list reached by `inlineFnsPolicy` after processing `fns`. -/
def inlineFnsPolicyCands (policy : InlinePolicy) (siteCounts loopCounts : List (Sym × Nat))
    (extSigs : List SigEntry) (exits : List Sym) :
    List SigEntry → List Fn → List Fn → List Fn
  | _, cands, [] => cands
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
      inlineFnsPolicyCands policy siteCounts loopCounts extSigs exits
        (seenSigs ++ [fn.sig]) cands' rest

/-- `inlineFnsPolicy` over `A ++ B` splits at the state reached after `A`. -/
theorem inlineFnsPolicy_append (policy : InlinePolicy) (siteCounts loopCounts : List (Sym × Nat))
    (extSigs : List SigEntry) (exits : List Sym) :
    ∀ (seenSigs : List SigEntry) (cands A B : List Fn),
    inlineFnsPolicy policy siteCounts loopCounts extSigs exits seenSigs cands (A ++ B) =
      inlineFnsPolicy policy siteCounts loopCounts extSigs exits seenSigs cands A ++
      inlineFnsPolicy policy siteCounts loopCounts extSigs exits (seenSigs ++ A.map Fn.sig)
        (inlineFnsPolicyCands policy siteCounts loopCounts extSigs exits seenSigs cands A) B
  | seenSigs, cands, [], B => by
      simp only [List.nil_append, List.map_nil, List.append_nil, inlineFnsPolicyCands]
      cases B <;> rfl
  | seenSigs, cands, fn :: A, B => by
      simp only [List.cons_append, inlineFnsPolicy, inlineFnsPolicyCands, List.map_cons]
      rw [inlineFnsPolicy_append policy siteCounts loopCounts extSigs exits _ _ A B,
        List.append_assoc, List.singleton_append]

/-- Renormalized `inlineFnsPolicy` output from position `a` with accumulated `seen` and
`cands`. -/
def inlRest (policy : InlinePolicy) (siteCounts loopCounts : List (Sym × Nat))
    (extSigs : List SigEntry) (exits : List Sym) (fns : List Fn) (a : Nat)
    (seen : List SigEntry) (cands : List Fn) : List Fn :=
  (inlineFnsPolicy policy siteCounts loopCounts extSigs exits seen cands
    (fns.drop a)).map Fn.renorm

/-- `Module.inlinePolicy` unfolds to `inlineFnsPolicy` over the global call-site tables. -/
theorem Module.inlinePolicy_fns_eq (M : Module) (policy : InlinePolicy) :
    (M.inlinePolicy policy).fns =
      inlineFnsPolicy policy (inlSiteCounts policy M.fns) (inlLoopCounts policy M.fns)
        (M.externs.map Extern.sig) M.exits [] [] M.fns :=
  rfl

/-- Chain start: `(M.optInlinePolicy policy).fns` is `inlRest` from position `0`. -/
theorem Module.optInlinePolicy_fns_eq_inlRest (M : Module) (policy : InlinePolicy)
    (siteCounts loopCounts : List (Sym × Nat))
    (hsc : inlSiteCounts policy M.fns = siteCounts)
    (hlc : inlLoopCounts policy M.fns = loopCounts) :
    (M.optInlinePolicy policy).fns =
      inlRest policy siteCounts loopCounts (M.externs.map Extern.sig) M.exits M.fns 0 [] [] := by
  subst hsc hlc
  simp only [inlRest, List.drop_zero]
  exact congrArg (List.map Fn.renorm) (Module.inlinePolicy_fns_eq M policy)

/-- Chain step: kernel-checked chunk equalities for `[a, a + n)` peel `lit` off `inlRest`. -/
theorem inlRest_step (policy : InlinePolicy) (siteCounts loopCounts : List (Sym × Nat))
    (extSigs : List SigEntry) (exits : List Sym) (fns : List Fn) (a n b : Nat)
    (seen seen' : List SigEntry) (cands cands' lit : List Fn) (hab : a + n = b)
    (hlit : lit = (inlineFnsPolicy policy siteCounts loopCounts extSigs exits
      seen cands ((fns.drop a).take n)).map Fn.renorm)
    (hseen : seen' = seen ++ ((fns.drop a).take n).map Fn.sig)
    (hcands : cands' = inlineFnsPolicyCands policy siteCounts loopCounts extSigs exits
      seen cands ((fns.drop a).take n)) :
    inlRest policy siteCounts loopCounts extSigs exits fns a seen cands =
      List.append lit (inlRest policy siteCounts loopCounts extSigs exits fns b seen' cands') := by
  subst hab hlit hseen hcands
  unfold inlRest
  have hsplit : fns.drop a = (fns.drop a).take n ++ fns.drop (a + n) := by
    rw [← List.drop_drop, List.take_append_drop]
  rw [hsplit, inlineFnsPolicy_append, List.map_append, ← hsplit]
  rfl

/-- Chain end: the final chunk `[a, a + n)` covering the tail of `fns` closes `inlRest`. -/
theorem inlRest_last (policy : InlinePolicy) (siteCounts loopCounts : List (Sym × Nat))
    (extSigs : List SigEntry) (exits : List Sym) (fns : List Fn) (a n : Nat)
    (seen : List SigEntry) (cands lit : List Fn) (hend : Nat.ble fns.length (a + n) = true)
    (hlit : lit = (inlineFnsPolicy policy siteCounts loopCounts extSigs exits
      seen cands ((fns.drop a).take n)).map Fn.renorm) :
    inlRest policy siteCounts loopCounts extSigs exits fns a seen cands = lit := by
  subst hlit
  unfold inlRest
  have hle : fns.length ≤ a + n := Nat.le_of_ble_eq_true hend
  have htake : (fns.drop a).take n = fns.drop a :=
    List.take_of_length_le (by rw [List.length_drop]; omega)
  rw [htake]

/-- Helper for `inline_mod_join!`: prepend a chunk prefix equality across `List.append`. -/
theorem inlRest_prepend_eq {α : Type _} {lhs pre mid rhs : List α}
    (h1 : lhs = List.append pre mid) (h2 : mid = rhs) : lhs = List.append pre rhs := by
  rw [h1, h2]

/-- Module extensionality from field equalities. -/
theorem Module.eq_of_fields {M N : Module} (hf : M.fns = N.fns) (he : M.externs = N.externs)
    (hx : M.exits = N.exits) : M = N := by
  cases M; cases N
  simp only at hf he hx
  subst hf he hx
  rfl

end LeanQbe.T
