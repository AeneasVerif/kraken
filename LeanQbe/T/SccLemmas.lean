module

public import LeanQbe.T.Scc

/-!
# Soundness of `LeanQbe.T.Scc`

Proves `checkSccOrder_sound` (showing every `fn ∈ scc` satisfies `fn.callsOk (earlier ++ own ++ ext)
exits` plus global name uniqueness) and supporting partition/disjointness/acyclic-embedding lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

theorem checkSccCalls_ok (exits : List Sym) (extSigs : List SigEntry) :
    ∀ (seen rest pre : List (List Fn)) (scc : List Fn) (post : List (List Fn)),
      checkSccCalls exits extSigs (seen.flatten.map Fn.sig) rest = true →
      rest = pre ++ scc :: post →
      !scc.isEmpty = true ∧
      ∀ fn ∈ scc,
        fn.callsOk ((seen ++ pre).flatten.map Fn.sig ++ scc.map Fn.sig ++ extSigs) exits
  | _, [], pre, _, _, _, hsplit => by cases pre <;> simp at hsplit
  | seen, s :: rest, [], scc, post, hchk, hsplit => by
      simp only [List.nil_append, List.cons.injEq] at hsplit
      rcases hsplit with ⟨rfl, _⟩
      simp only [checkSccCalls, Bool.and_eq_true] at hchk
      refine ⟨hchk.1.1, fun fn hfn => ?_⟩
      simpa [List.append_nil] using Fn.callsOk_of_checkCallsOk (List.all_eq_true.mp hchk.1.2 fn hfn)
  | seen, s :: rest, s' :: pre', scc, post, hchk, hsplit => by
      simp only [List.cons_append, List.cons.injEq] at hsplit
      rcases hsplit with ⟨rfl, hrest⟩
      simp only [checkSccCalls, Bool.and_eq_true] at hchk
      have hnext := hchk.2
      rw [show seen.flatten.map Fn.sig ++ s.map Fn.sig = (seen ++ [s]).flatten.map Fn.sig by
        simp [List.flatten_append, List.map_append]] at hnext
      have ih := checkSccCalls_ok exits extSigs (seen ++ [s]) rest pre' scc post hnext hrest
      simpa [List.append_assoc] using ih

/-- Soundness of `checkSccOrder`: when `checkSccOrder sccs extSigs exits = true`, names across
all SCCs and `extSigs` are pairwise distinct, every SCC is non-empty, and every `fn ∈ scc` in
`sccs = pre ++ scc :: post` satisfies `fn.callsOk (earlier ++ own ++ extSigs) exits`. -/
theorem checkSccOrder_sound {sccs : List (List Fn)} {extSigs : List SigEntry}
    {exits : List Sym} (h : checkSccOrder sccs extSigs exits = true) :
    (sccs.flatten.map Fn.name ++ extSigs.map Prod.fst).Nodup ∧
    ∀ (pre : List (List Fn)) (scc : List Fn) (post : List (List Fn)),
      sccs = pre ++ scc :: post →
      !scc.isEmpty = true ∧
      ∀ fn ∈ scc,
        fn.callsOk (pre.flatten.map Fn.sig ++ scc.map Fn.sig ++ extSigs) exits := by
  simp only [checkSccOrder, Bool.and_eq_true] at h
  refine ⟨listNodup_nodup h.1, fun pre scc post hsplit => ?_⟩
  simpa using checkSccCalls_ok exits extSigs [] sccs pre scc post h.2 hsplit

theorem checkSccOrder_nodup {sccs : List (List Fn)} {extSigs : List SigEntry}
    {exits : List Sym} (h : checkSccOrder sccs extSigs exits = true) :
    (sccs.flatten.map Fn.name ++ extSigs.map Prod.fst).Nodup :=
  (checkSccOrder_sound h).1

theorem checkSccOrder_scc_callsOk {sccs : List (List Fn)} {extSigs : List SigEntry}
    {exits : List Sym} (h : checkSccOrder sccs extSigs exits = true)
    {pre : List (List Fn)} {scc : List Fn} {post : List (List Fn)}
    (hsplit : sccs = pre ++ scc :: post) {fn : Fn} (hfn : fn ∈ scc) :
    fn.callsOk (pre.flatten.map Fn.sig ++ scc.map Fn.sig ++ extSigs) exits :=
  ((checkSccOrder_sound h).2 pre scc post hsplit).2 fn hfn

theorem checkSccOrder_scc_namesNodup {sccs : List (List Fn)} {extSigs : List SigEntry}
    {exits : List Sym} (h : checkSccOrder sccs extSigs exits = true)
    {pre : List (List Fn)} {scc : List Fn} {post : List (List Fn)}
    (hsplit : sccs = pre ++ scc :: post) :
    (scc.map Fn.name).Nodup ∧
    (∀ nm ∈ scc.map Fn.name, nm ∉ pre.flatten.map Fn.name) ∧
    (∀ nm ∈ scc.map Fn.name, nm ∉ post.flatten.map Fn.name) ∧
    (∀ nm ∈ scc.map Fn.name, nm ∉ extSigs.map Prod.fst) := by
  have hnd := checkSccOrder_nodup h
  rw [hsplit] at hnd
  simp only [List.flatten_append, List.flatten_cons, List.map_append, List.append_assoc] at hnd
  have h1 := List.nodup_append.mp hnd
  have h2 := List.nodup_append.mp h1.2.1
  have h3 := List.nodup_append.mp h2.2.1
  refine ⟨h2.1, ?_, ?_, ?_⟩
  · intro nm hnm hpre
    exact h1.2.2 nm hpre nm (List.mem_append_left _ hnm) rfl
  · intro nm hnm hpost
    exact h2.2.2 nm hnm nm (List.mem_append_left _ hpost) rfl
  · intro nm hnm hext
    exact h2.2.2 nm hnm nm (List.mem_append_right _ hext) rfl

private theorem flatten_map_singleton {α : Type _} {β : Type _} (g : α → β) :
    ∀ xs : List α, (xs.map fun x => [x]).flatten.map g = xs.map g
  | [] => rfl
  | _ :: xs => congrArg (_ :: ·) (flatten_map_singleton g xs)

private theorem any_sigBeq_mono {a b : List SigEntry} (hsub : ∀ x ∈ a, x ∈ b) {s : SigEntry}
    (ha : a.any (SigEntry.beq s) = true) : b.any (SigEntry.beq s) = true := by
  simp only [List.any_eq_true, SigEntry.beq_iff_eq] at ha ⊢
  obtain ⟨x, hx, heq⟩ := ha
  exact ⟨x, hsub x hx, heq⟩

mutual
private theorem Expr.checkCallsOk_mono {a b : List SigEntry} (hsub : ∀ x ∈ a, x ∈ b)
    {exits : List Sym} {rs : List Ty} :
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    e.checkCallsOk a exits = true → e.checkCallsOk b exits = true
  | .let_ _ k, h => Expr.checkCallsOk_mono hsub (k (Tup.units _)) h
  | .load _ _ k, h => Expr.checkCallsOk_mono hsub (k ()) h
  | .store _ _ k, h => Expr.checkCallsOk_mono hsub k h
  | .call _ _ k, h => by
      simp only [Expr.checkCallsOk, Bool.and_eq_true] at h ⊢
      exact ⟨any_sigBeq_mono hsub h.1, Expr.checkCallsOk_mono hsub (k (Tup.units _)) h.2⟩
  | .jnz _ t e, h => by
      simp only [Expr.checkCallsOk, Bool.and_eq_true] at h ⊢
      exact ⟨Expr.checkCallsOk_mono hsub t h.1, Expr.checkCallsOk_mono hsub e h.2⟩
  | .jump _ _, h | .ret _, h | .hlt, h | .exit _ _, h => h
  | .group (sig := sig) bodies k, h => by
      simp only [Expr.checkCallsOk, Bool.and_eq_true] at h ⊢
      exact ⟨Blocks.checkCallsOk_mono hsub (bodies (Tup.units sig)) h.1,
        Expr.checkCallsOk_mono hsub (k (Tup.units sig)) h.2⟩

private theorem Blocks.checkCallsOk_mono {a b : List SigEntry} (hsub : ∀ x ∈ a, x ∈ b)
    {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    bs.checkCallsOk a exits = true → bs.checkCallsOk b exits = true
  | _, .nil, h => h
  | _, .cons bd bs, h => by
      simp only [Blocks.checkCallsOk, Bool.and_eq_true] at h ⊢
      exact ⟨Expr.checkCallsOk_mono hsub (bd (Tup.units _)) h.1,
        Blocks.checkCallsOk_mono hsub bs h.2⟩
end

private theorem Fn.checkCallsOk_mono {a b : List SigEntry} (hsub : ∀ x ∈ a, x ∈ b)
    {exits : List Sym} {fn : Fn} (h : fn.checkCallsOk a exits = true) :
    fn.checkCallsOk b exits = true :=
  Expr.checkCallsOk_mono hsub _ h

private theorem checkFnsCallsOk_to_checkSccCalls (exits : List Sym) (extSigs : List SigEntry) :
    ∀ (seen rest : List Fn),
      Module.checkFnsCallsOk exits extSigs (seen.map Fn.sig) rest = true →
      checkSccCalls exits extSigs ((seen.map fun f => [f]).flatten.map Fn.sig)
        (rest.map fun f => [f]) = true
  | _, [] => fun _ => rfl
  | seen, f :: rest => fun h => by
      simp only [Module.checkFnsCallsOk, Bool.and_eq_true] at h
      simp only [List.map_cons, checkSccCalls, List.isEmpty_cons, Bool.not_false,
        List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, Bool.and_eq_true]
      have hseen : (seen.map fun x => [x]).flatten.map Fn.sig = seen.map Fn.sig :=
        flatten_map_singleton Fn.sig seen
      constructor
      · rw [hseen]
        refine Fn.checkCallsOk_mono (fun x hx => ?_) h.1
        rcases List.mem_append.mp hx with hl | hr
        · exact List.mem_append_left _ (List.mem_append_left _ hl)
        · exact List.mem_append_right _ hr
      · have h2 := h.2
        rw [show seen.map Fn.sig ++ [f.sig] = (seen ++ [f]).map Fn.sig by simp] at h2
        have ih := checkFnsCallsOk_to_checkSccCalls exits extSigs (seen ++ [f]) rest h2
        simpa [List.map_append, List.flatten_append, flatten_map_singleton, List.append_assoc]
          using ih

/-- Any acyclic `Module` passing `M.checkAcyclic = true` induces a valid singleton-SCC order. -/
theorem checkSccOrder_of_acyclic {M : Module} (h : M.checkAcyclic = true) :
    checkSccOrder (M.fns.map fun f => [f]) (M.externs.map Extern.sig) M.exits = true := by
  simp only [Module.checkAcyclic, Bool.and_eq_true] at h
  simp only [checkSccOrder, Bool.and_eq_true]
  constructor
  · have hnd := M.namesNodup_of_checkNamesNodup h.1
    rw [flatten_map_singleton Fn.name M.fns]
    rw [show (M.externs.map Extern.sig).map Prod.fst = M.externs.map Extern.name by
      simp [List.map_map, Function.comp_def, Extern.sig]]
    exact listNodup_iff.mpr hnd
  · exact checkFnsCallsOk_to_checkSccCalls M.exits (M.externs.map Extern.sig) [] M.fns h.2

end LeanQbe.T
