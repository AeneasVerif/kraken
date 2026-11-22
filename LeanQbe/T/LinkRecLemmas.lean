module

public import LeanQbe.T.LinkRec
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.AbiLemmas
import LeanQbe.T.OptLemmas
import LeanQbe.T.LegalLemmas
import LeanQbe.T.RegaLemmas

/-!
# Soundness of `LeanQbe.T.LinkRec` (`B1.1`)

* **Source/IR cyclic linking**: `callsOkRec_of_checkCyclic`, signature isolation for
  `Env.ofModuleRec`, `Env.sound_rec_at`, `Env.sound_rec`, `Env.unfoldRecAt`,
  `Env.sound_rec_unfold` (by `Nat.strongRecOn`), `moduleRecOk_of_step`, and `Env.sound_rec_measure`.
* **Stack-bound & label uniqueness**: `calleesBoundRec_ge`, `calleesBoundRec_mem`,
  `checkAndBoundRecExt_spec`, `compileModuleRecAux_mem`, `compileModuleRecAux_code_labels`,
  and `compileModuleRec_labelsUnique`.
* **Machine linking (`CompiledRec` & `link_rec_compiled`)**: `compileRecChecked` (+ `WithLabels`),
  `compileRec_sound`, `link_rec_compiled`, `link_rec_compiled_host`, `link_rec_compiled_src`,
  `link_rec_compiled_src_noExit` (by `Nat.strongRecOn`), and `TargetInit.run_rec_*`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LinkRec

open Std Std.ExtHashMap
open LeanQbe.T

/-! ## 1. Cyclic `Module` Checks, Signature Isolation, and `Env.sound_rec` -/

theorem callsOkRec_of_checkCyclic {M : Module}
    (hchk : checkCyclic M = true) (hwf : ∀ fn ∈ M.fns, fn.Wf) : CallsOkRec M := by
  simp only [checkCyclic, Bool.and_eq_true, List.all_eq_true] at hchk
  exact ⟨Module.namesNodup_of_checkNamesNodup hchk.1, fun fn hfn =>
    ⟨hwf fn hfn, Fn.callsOk_of_checkCallsOk (hchk.2 fn hfn)⟩⟩

private theorem sigs_map_fst (M : Module) : M.sigs.map Prod.fst = M.names := by
  simp [Module.sigs, Module.names, List.map_append, List.map_map, Function.comp_def,
    Fn.sig, Extern.sig]

private theorem mem_unique_fst : ∀ {xs : List SigEntry}, (xs.map Prod.fst).Nodup →
    ∀ {f as₁ bs₁ as₂ bs₂}, (f, as₁, bs₁) ∈ xs → (f, as₂, bs₂) ∈ xs → as₁ = as₂ ∧ bs₁ = bs₂
  | [], _, _, _, _, _, _, h, _ => nomatch h
  | (_, _, _) :: _, hnd, _, _, _, _, _, h1, h2 => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rcases List.mem_cons.mp h1 with e1 | h1 <;> rcases List.mem_cons.mp h2 with e2 | h2
    · cases e1; cases e2; exact ⟨rfl, rfl⟩
    · cases e1; exact absurd rfl (hnd.1 _ h2)
    · cases e2; exact absurd rfl (hnd.1 _ h1)
    · exact mem_unique_fst hnd.2 h1 h2

private theorem mem_fns_sig_mem_sigs {M : Module} {e : SigEntry}
    (h : e ∈ M.fns.map Fn.sig) : e ∈ M.sigs :=
  List.mem_append_left _ h

private theorem mem_externs_sig_mem_sigs {M : Module} {e : SigEntry}
    (h : e ∈ M.externs.map Extern.sig) : e ∈ M.sigs :=
  List.mem_append_right _ h

theorem Env.ofModuleRec_empty_off_sig {M : Module} (hnd : M.namesNodup)
    (Γrec : Nat → Env) (Γext : Env) {fn : Fn} (hfn : fn ∈ M.fns)
    {as bs : List Ty} (hne : (as, bs) ≠ (fn.as, fn.rs))
    (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    ¬ Env.ofModuleRec M Γrec Γext fn.name as bs xs m Q X := by
  rintro (⟨hsig, _⟩ | ⟨hsig, _⟩)
  · have ⟨ha, hb⟩ := mem_unique_fst (sigs_map_fst M ▸ hnd)
      (mem_fns_sig_mem_sigs hsig) (mem_fns_sig_mem_sigs (List.mem_map_of_mem hfn))
    exact hne (Prod.ext ha hb)
  · have ⟨ha, hb⟩ := mem_unique_fst (sigs_map_fst M ▸ hnd)
      (mem_externs_sig_mem_sigs hsig) (mem_fns_sig_mem_sigs (List.mem_map_of_mem hfn))
    exact hne (Prod.ext ha hb)

theorem Env.ofModuleRec_empty_off_extern_sig {M : Module} (hnd : M.namesNodup)
    (Γrec : Nat → Env) (Γext : Env) {ex : Extern} (hex : ex ∈ M.externs)
    {as bs : List Ty} (hne : (as, bs) ≠ (ex.as, ex.rs))
    (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    ¬ Env.ofModuleRec M Γrec Γext ex.name as bs xs m Q X := by
  rintro (⟨hsig, _⟩ | ⟨hsig, _⟩)
  · have ⟨ha, hb⟩ := mem_unique_fst (sigs_map_fst M ▸ hnd)
      (mem_fns_sig_mem_sigs hsig) (mem_externs_sig_mem_sigs (List.mem_map_of_mem hex))
    exact hne (Prod.ext ha hb)
  · have ⟨ha, hb⟩ := mem_unique_fst (sigs_map_fst M ▸ hnd)
      (mem_externs_sig_mem_sigs hsig) (mem_externs_sig_mem_sigs (List.mem_map_of_mem hex))
    exact hne (Prod.ext ha hb)

theorem Env.ofModuleRec_empty_undeclared {M : Module} (Γrec : Nat → Env) (Γext : Env)
    {f : Sym} (hf : f ∉ M.names) (as bs : List Ty)
    (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    ¬ Env.ofModuleRec M Γrec Γext f as bs xs m Q X := by
  rintro (⟨hsig, _⟩ | ⟨hsig, _⟩)
  · exact hf (sigs_map_fst M ▸ List.mem_map.mpr ⟨(f, as, bs), mem_fns_sig_mem_sigs hsig, rfl⟩)
  · exact hf (sigs_map_fst M ▸
      List.mem_map.mpr ⟨(f, as, bs), mem_externs_sig_mem_sigs hsig, rfl⟩)

theorem Env.stepRec_le_ofModuleRec {M : Module} {Γrec : Nat → Env} {Γext : Env} {k : Nat}
    {f : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.stepRec (M.fns.map Fn.sig) (M.externs.map Extern.sig) Γrec Γext k
      f as bs xs m Q X) :
    Env.ofModuleRec M Γrec Γext f as bs xs m Q X := by
  rcases h with ⟨hsig, k', _, hΓ⟩ | ⟨hsig, hΓ⟩
  · exact Or.inl ⟨hsig, k', hΓ⟩
  · exact Or.inr ⟨hsig, hΓ⟩

/-- Every measure-`k` spec in a `ModuleRecOk` module satisfies `Func.wp` under the closed
environment `Env.ofModuleRec M Γrec Γext`. -/
theorem Env.sound_rec_at {Γrec : Nat → Env} {Γext : Env} {M : Module}
    (hM : ModuleRecOk Γrec Γext M) :
    ∀ (k : Nat) (fn : Fn), fn ∈ M.fns → ∀ xs m Q X,
      Γrec k fn.name fn.as fn.rs xs m Q X →
      Func.wp (Env.ofModuleRec M Γrec Γext) fn.body xs m Q X := by
  intro k fn hfn xs m Q X hspec
  have ⟨_, _, hstep⟩ := hM.fnsOk fn hfn
  exact wp_env_mono (fun _ _ _ _ _ _ _ hg => Env.stepRec_le_ofModuleRec hg) _ m
    (hstep k xs m Q X hspec)

private theorem fn_name_not_mem_externs {M : Module} (hnd : M.namesNodup)
    {fn : Fn} (hfn : fn ∈ M.fns) {as bs : List Ty} :
    (fn.name, as, bs) ∉ M.externs.map Extern.sig := by
  intro hex
  have hdisj := (List.nodup_append.mp hnd).2.2
  have h1 : fn.name ∈ M.fns.map Fn.name := List.mem_map_of_mem hfn
  obtain ⟨ex, hexm, heq⟩ := List.mem_map.mp hex
  have h2 : ex.name ∈ M.externs.map Extern.name := List.mem_map_of_mem hexm
  exact hdisj fn.name h1 ex.name h2 (congrArg Prod.fst heq).symm

/-- Closed environment satisfaction for `Env.ofModuleRec M Γrec Γext`: every function `fn ∈ M.fns`
respects `Func.wp (Env.ofModuleRec M Γrec Γext)`. -/
theorem Env.sound_rec {Γrec : Nat → Env} {Γext : Env} {M : Module}
    (hM : ModuleRecOk Γrec Γext M) :
    ∀ (fn : Fn), fn ∈ M.fns → ∀ xs m Q X,
      Env.ofModuleRec M Γrec Γext fn.name fn.as fn.rs xs m Q X →
      Func.wp (Env.ofModuleRec M Γrec Γext) fn.body xs m Q X := by
  intro fn hfn xs m Q X hspec
  rcases hspec with ⟨_, k, hΓ⟩ | ⟨hsig, _⟩
  · exact Env.sound_rec_at hM k fn hfn xs m Q X hΓ
  · exact absurd hsig (fn_name_not_mem_externs hM.nodup hfn)

/-- `k`-step semantic unfolding of `M` over fixed external environment `Γext`:
at `k = 0`, only external calls in `M.externs` are permitted; at `k + 1`, cyclic callees
in `M.fns` may invoke steps `≤ k`. -/
@[expose] def Env.unfoldRecBelow (M : Module) (Γext : Env) : Nat → Env
  | 0 => fun f as bs xs m Q X =>
      (f, as, bs) ∈ M.externs.map Extern.sig ∧ Γext f as bs xs m Q X
  | k + 1 => fun f as bs xs m Q X =>
      Env.unfoldRecBelow M Γext k f as bs xs m Q X ∨
      ((f, as, bs) ∈ M.fns.map Fn.sig ∧ ∃ fn ∈ M.fns, fn.name = f ∧
        ∃ (ha : fn.as = as) (hr : fn.rs = bs),
          Func.wp (Env.unfoldRecBelow M Γext k) fn.body (ha ▸ xs) m (hr ▸ Q) X)

/-- Measure-`k` semantic environment for `M`: executes `fn ∈ M.fns` against `k` unrolled steps. -/
@[expose] def Env.unfoldRecAt (M : Module) (Γext : Env) (k : Nat) : Env :=
  Env.unfoldRecBelow M Γext (k + 1)

private theorem unfoldRecBelow_mono {M : Module} {Γext : Env} :
    ∀ {j k : Nat}, j ≤ k → ∀ f as bs xs m Q X,
      Env.unfoldRecBelow M Γext j f as bs xs m Q X →
      Env.unfoldRecBelow M Γext k f as bs xs m Q X
  | _, 0, hjk, f, as, bs, xs, m, Q, X, h => by
    obtain rfl : _ = 0 := Nat.le_zero.mp hjk
    exact h
  | _, k + 1, hjk, f, as, bs, xs, m, Q, X, h => by
    rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
    · exact h
    · exact Or.inl (unfoldRecBelow_mono (Nat.lt_succ_iff.mp hlt) f as bs xs m Q X h)

/-- Strong induction on fuel `k`: every `ModuleRecOk Γrec Γext M` refines the unrolled
semantic environment `Env.unfoldRecAt M Γext k`. -/
theorem Env.sound_rec_unfold {Γrec : Nat → Env} {Γext : Env} {M : Module}
    (hM : ModuleRecOk Γrec Γext M) :
    ∀ (k : Nat) (fn : Fn), fn ∈ M.fns → ∀ xs m Q X,
      Γrec k fn.name fn.as fn.rs xs m Q X →
      Env.unfoldRecAt M Γext k fn.name fn.as fn.rs xs m Q X := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro fn hfn xs m Q X hspec
    have ⟨_, _, hstep⟩ := hM.fnsOk fn hfn
    have hwp := hstep k xs m Q X hspec
    refine Or.inr ⟨List.mem_map_of_mem hfn, fn, hfn, rfl, rfl, rfl, ?_⟩
    refine wp_env_mono (fun g as' bs' xs' m' Q' X' hg => ?_) _ m hwp
    rcases hg with ⟨hsig, j, hj, hΓ⟩ | ⟨hsig, hΓ⟩
    · obtain ⟨gfn, hgfn, hgeq⟩ := List.mem_map.mp hsig
      cases hgeq
      exact unfoldRecBelow_mono hj gfn.name gfn.as gfn.rs xs' m' Q' X'
        (ih j hj gfn hgfn xs' m' Q' X' hΓ)
    · exact unfoldRecBelow_mono (Nat.zero_le k) g as' bs' xs' m' Q' X' ⟨hsig, hΓ⟩

/-- Construct `ModuleRecOk Γrec Γext M` from `checkCyclic M = true`, per-function `Wf`, and
polymorphic-`Γ` step specs (`Γ` validating cyclic callees at `k' < k` and externs at `Γext`). -/
theorem moduleRecOk_of_step {Γrec : Nat → Env} {Γext : Env} {M : Module}
    (hchk : checkCyclic M = true) (hwf : ∀ fn ∈ M.fns, fn.Wf)
    (hstep : ∀ k : Nat, ∀ fn ∈ M.fns, ∀ (Γ : Env),
      (∀ g ∈ M.fns, ∀ k' < k, ∀ xs m Q X,
        Γrec k' g.name g.as g.rs xs m Q X → Γ g.name g.as g.rs xs m Q X) →
      (∀ ex ∈ M.externs, ∀ xs m Q X,
        Γext ex.name ex.as ex.rs xs m Q X → Γ ex.name ex.as ex.rs xs m Q X) →
      ∀ xs m Q X, Γrec k fn.name fn.as fn.rs xs m Q X → Func.wp Γ fn.body xs m Q X) :
    ModuleRecOk Γrec Γext M := by
  obtain ⟨hnd, hok⟩ := callsOkRec_of_checkCyclic hchk hwf
  refine ⟨hnd, fun fn hfn => ?_⟩
  obtain ⟨hfwf, hfc⟩ := hok fn hfn
  refine ⟨hfwf, hfc, fun k xs m Q X hspec => ?_⟩
  refine hstep k fn hfn _ (fun g hg k' hk' xs' m' Q' X' hΓ => ?_)
    (fun ex hex xs' m' Q' X' hΓ => ?_) xs m Q X hspec
  · exact Or.inl ⟨List.mem_map_of_mem hg, k', hk', hΓ⟩
  · exact Or.inr ⟨List.mem_map_of_mem hex, hΓ⟩

private theorem spec_cast_wrap {as₁ as₂ bs₁ bs₂ : List Ty}
    (ha : as₁ = as₂) (hb : bs₁ = bs₂) {Γ : Env} {f : Sym}
    {xs : Tup Val as₁} {m : Mem 64} {Q : Post bs₁} {X : XPost}
    (h : Γ f as₂ bs₂ (ha ▸ xs) m (hb ▸ Q) X) : Γ f as₁ bs₁ xs m Q X := by
  subst ha; subst hb; exact h

private theorem envOfMeasureSpec_intro {as bs : List Ty} {P : Sym → Nat → Spec as bs}
    {k : Nat} {g : Fn} (hga : g.as = as) (hgb : g.rs = bs)
    {xs' : Tup Val as} {m' : Mem 64} {Q' : Post bs} {X' : XPost}
    (hp : P g.name k xs' m' Q' X') :
    envOfMeasureSpec P k g.name g.as g.rs (hga.symm ▸ xs') m' (hgb.symm ▸ Q') X' := by
  refine ⟨hga, hgb, ?_⟩
  subst hga; subst hgb; exact hp

/-- Convenience `Env.sound_rec` wrapper for a single-signature spec family
`P : Sym → Nat → Spec as bs`. -/
theorem Env.sound_rec_measure {as bs : List Ty} (P : Sym → Nat → Spec as bs)
    (Γext : Env) {M : Module} (hchk : checkCyclic M = true)
    (hwf : ∀ fn ∈ M.fns, fn.Wf) (hsig : ∀ fn ∈ M.fns, fn.as = as ∧ fn.rs = bs)
    (hstep : ∀ k : Nat, ∀ fn ∈ M.fns, ∀ (ha : fn.as = as) (hb : fn.rs = bs) (Γ : Env),
      (∀ g ∈ M.fns, ∀ k' < k, ∀ xs m Q X,
        P g.name k' xs m Q X → Γ g.name as bs xs m Q X) →
      (∀ ex ∈ M.externs, ∀ xs m Q X,
        Γext ex.name ex.as ex.rs xs m Q X → Γ ex.name ex.as ex.rs xs m Q X) →
      ∀ xs m Q X, P fn.name k xs m Q X →
        Func.wp Γ fn.body (ha ▸ xs) m (hb ▸ Q) X) :
    ∀ fn ∈ M.fns, ∀ xs m Q X,
      Env.ofModuleRec M (envOfMeasureSpec P) Γext fn.name fn.as fn.rs xs m Q X →
      Func.wp (Env.ofModuleRec M (envOfMeasureSpec P) Γext) fn.body xs m Q X := by
  have hM : ModuleRecOk (envOfMeasureSpec P) Γext M := by
    refine moduleRecOk_of_step hchk hwf fun k fn hfn Γ hrec hext xs m Q X hspec => ?_
    rcases hspec with ⟨ha, hb, hp⟩
    have h1 := hstep k fn hfn ha hb Γ (fun g hg k' hk' xs' m' Q' X' gp => by
      obtain ⟨hga, hgb⟩ := hsig g hg
      have h2 := hrec g hg k' hk' (hga.symm ▸ xs') m' (hgb.symm ▸ Q') X'
        (envOfMeasureSpec_intro hga hgb gp)
      exact spec_cast_wrap hga.symm hgb.symm h2) hext (ha ▸ xs) m (hb ▸ Q) X hp
    clear hp
    subst ha; subst hb; exact h1
  exact Env.sound_rec hM

/-! ## 2. Stack-Bound, Label Uniqueness, and Compiler Helpers -/

theorem calleesBoundRec_ge {F raBytes : Nat} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} :
    ∀ {gs : List SigEntry} {n : Nat},
      calleesBoundRec F raBytes recSigs extCallees gs = some n → F ≤ n
  | [], _, h => by cases h; exact Nat.le_refl _
  | g :: gs, n, h => by
    dsimp only [calleesBoundRec] at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨rest, hrest, rfl⟩ := h
      exact Nat.le_trans (calleesBoundRec_ge hrest) (Nat.le_max_right _ _)
    · split at h
      · cases h; exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
      · cases h

theorem calleesBoundRec_mem {F raBytes : Nat} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} :
    ∀ {gs : List SigEntry} {n : Nat},
      calleesBoundRec F raBytes recSigs extCallees gs = some n →
      ∀ g ∈ gs,
        (g ∈ recSigs ∧ F + raBytes ≤ n) ∨
        (g ∉ recSigs ∧ ∃ bg, lookupBound extCallees g = some bg ∧ F + raBytes + bg ≤ n)
  | [], _, _, _, h => nomatch h
  | _ :: gs, n, h, g, hmem => by
    dsimp only [calleesBoundRec] at h
    split at h
    · rename_i hrec
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨rest, hrest, rfl⟩ := h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · simp only [List.any_eq_true, SigEntry.beq_iff_eq] at hrec
        obtain ⟨s, hs, heq⟩ := hrec
        exact Or.inl ⟨heq ▸ hs, Nat.le_max_left _ _⟩
      · rcases calleesBoundRec_mem hrest g hmem' with ⟨h1, h2⟩ | ⟨h1, bg, h2, h3⟩
        · exact Or.inl ⟨h1, Nat.le_trans h2 (Nat.le_max_right _ _)⟩
        · exact Or.inr ⟨h1, bg, h2, Nat.le_trans h3 (Nat.le_max_right _ _)⟩
    · rename_i hnot
      split at h
      · rename_i bg rest hlk hrest
        cases h
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · have hnr : g ∉ recSigs := fun hg =>
            hnot (List.any_eq_true.mpr ⟨g, hg, SigEntry.beq_iff_eq.mpr rfl⟩)
          exact Or.inr ⟨hnr, bg, hlk, Nat.le_max_left _ _⟩
        · rcases calleesBoundRec_mem hrest g hmem' with ⟨h1, h2⟩ | ⟨h1, bg', h2, h3⟩
          · exact Or.inl ⟨h1, Nat.le_trans h2 (Nat.le_max_right _ _)⟩
          · exact Or.inr ⟨h1, bg', h2, Nat.le_trans h3 (Nat.le_max_right _ _)⟩
      · cases h

theorem checkAndBoundRecExt_spec {I : Isa} {raBytes : Nat} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat} {h : I.Hints}
    {ext : Rega.Ext} {b step : Nat}
    (hc : checkAndBoundRecExt I raBytes recSigs extCallees exits nX h ext = some (b, step)) :
    step = I.frame.frameSize h.totalSlots + raBytes ∧
      I.frame.frameSize h.totalSlots ≤ b ∧
      (∀ g ∈ ext.callees,
        (g ∈ recSigs ∧ I.frame.frameSize h.totalSlots + raBytes ≤ b) ∨
        (g ∉ recSigs ∧ ∃ bg, lookupBound extCallees g = some bg ∧
          I.frame.frameSize h.totalSlots + raBytes + bg ≤ b)) ∧
      (∀ g ∈ ext.exits, g ∈ exits ∧ nX ≤ b) := by
  dsimp only [checkAndBoundRecExt] at hc
  cases hcb : calleesBoundRec (I.frame.frameSize h.totalSlots) raBytes recSigs extCallees
      ext.callees with
  | none => rw [hcb] at hc; cases hc
  | some n₁ =>
    rw [hcb] at hc
    cases hex : ext.exits.all (fun g => exits.contains g) with
    | false => rw [hex] at hc; cases hc
    | true =>
      rw [hex] at hc
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩
      have hge := calleesBoundRec_ge hcb
      have hle_b : n₁ ≤ if ext.exits.isEmpty then n₁ else Nat.max n₁ nX := by
        cases ext.exits.isEmpty <;> simp [Nat.le_max_left]
      refine ⟨rfl, Nat.le_trans hge hle_b, fun g hg => ?_, fun g hg => ?_⟩
      · rcases calleesBoundRec_mem hcb g hg with ⟨h1, h2⟩ | ⟨h1, bg, h2, h3⟩
        · exact Or.inl ⟨h1, Nat.le_trans h2 hle_b⟩
        · exact Or.inr ⟨h1, bg, h2, Nat.le_trans h3 hle_b⟩
      · refine ⟨by simpa using List.all_eq_true.mp hex g hg, ?_⟩
        have hne : ext.exits.isEmpty = false := by
          cases he : ext.exits with | nil => simp [he] at hg | cons _ _ => rfl
        simp [hne, Nat.le_max_right]

theorem compileRec_of_compileModuleRecAux {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym}
    {nX : Nat} :
    ∀ {fs : List Fn} {hints : List I.Hints} {code : List I.Directive} {b s : Nat},
      compileModuleRecAux I lt raBytes recSigs extCallees exits nX fs hints = .ok (code, b, s) →
      compile I lt fs hints = .ok code
  | [], [], _, _, _, h => by
    dsimp only [compileModuleRecAux] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _, _⟩; rfl
  | [], _ :: _, _, _, _, h => by dsimp only [compileModuleRecAux] at h; cases h
  | _ :: _, [], _, _, _, h => by dsimp only [compileModuleRecAux] at h; cases h
  | _ :: _, _ :: _, _, _, _, h => by
    dsimp only [compileModuleRecAux] at h
    split at h
    · rename_i c bf sf hl _
      split at h
      · rename_i cs brest srest hrest
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _, _⟩
        have h1 : compileFn I lt _ _ = .ok c := hl
        have h2 := compileRec_of_compileModuleRecAux hrest
        simp [compile, h1, h2]
      · simp at h
    · simp at h
    · simp at h

theorem compileRec_of_compileModuleRec {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel maxBound : Nat}
    {fs : List Fn} {hints : List I.Hints} {code : List I.Directive} {b s : Nat}
    (h : compileModuleRec I lt raBytes extCallees exits nX fuel maxBound fs hints =
      .ok (code, b, s)) :
    compile I lt fs hints = .ok code := by
  dsimp only [compileModuleRec] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i code' b' s' haux
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _, _⟩
        exact compileRec_of_compileModuleRecAux haux
      · simp at h

theorem compileModuleRecAux_mem {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym}
    {nX : Nat} :
    ∀ {fs : List Fn} {hints : List I.Hints} {code : List I.Directive} {base step : Nat},
      compileModuleRecAux I lt raBytes recSigs extCallees exits nX fs hints =
        .ok (code, base, step) →
      ∀ f ∈ fs, ∃ hint c k_f bf sf,
        Rega.lowerFn I hint (f.mid lt).ext (f.mid lt) = .ok c ∧
        c.IsInfixAt code k_f ∧ k_f ≤ code.length ∧
        checkAndBoundRecExt I raBytes recSigs extCallees exits nX hint (f.mid lt).ext =
          some (bf, sf) ∧
        bf ≤ base ∧ sf ≤ step
  | [], _, _, _, _, _, _, hf => nomatch hf
  | _ :: _, [], _, _, _, h, _, _ => by dsimp only [compileModuleRecAux] at h; cases h
  | g :: fs, hint :: hints, code, base, step, h, f, hf => by
    dsimp only [compileModuleRecAux] at h
    split at h
    · rename_i c bf sf hl hchk
      split at h
      · rename_i cs brest srest hrest
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        rcases List.mem_cons.mp hf with rfl | hf'
        · exact ⟨hint, c, 0, bf, sf, hl, ⟨cs, rfl⟩, Nat.zero_le _, hchk,
            Nat.le_max_left _ _, Nat.le_max_left _ _⟩
        · obtain ⟨hint', c', k', bf', sf', hl', hinf', hklen', hchk', hbf', hsf'⟩ :=
            compileModuleRecAux_mem hrest f hf'
          refine ⟨hint', c', c.length + k', bf', sf', hl', ?_, by simp; exact hklen', hchk',
            Nat.le_trans hbf' (Nat.le_max_right _ _),
            Nat.le_trans hsf' (Nat.le_max_right _ _)⟩
          obtain ⟨tail, htail⟩ := hinf'
          exact ⟨tail, by
            have e : (c ++ cs).drop (c.length + k') = cs.drop k' := by
              rw [← List.drop_drop, List.drop_left' rfl]
            rw [e, htail]⟩
      · simp at h
    · simp at h
    · simp at h

private theorem nodup_getElem?_inj : ∀ {xs : List Sym} {i j : Nat} {x : Sym},
    xs.Nodup → xs[i]? = some x → xs[j]? = some x → i = j
  | [], _, _, _, _, hi, _ => by simp at hi
  | _ :: _, 0, 0, _, _, _, _ => rfl
  | _ :: _, 0, _ + 1, _, hnd, hi, hj => by
    simp only [List.nodup_cons, List.getElem?_cons_zero, Option.some.injEq] at hnd hi
    exact absurd (hi ▸ List.mem_of_getElem? hj) hnd.1
  | _ :: _, _ + 1, 0, _, hnd, hi, hj => by
    simp only [List.nodup_cons, List.getElem?_cons_zero, Option.some.injEq] at hnd hj
    exact absurd (hj ▸ List.mem_of_getElem? hi) hnd.1
  | _ :: _, i + 1, j + 1, _, hnd, hi, hj =>
    congrArg Nat.succ (nodup_getElem?_inj (List.nodup_cons.mp hnd).2 hi hj)

theorem compileModuleRecAux_code_labels {T : Target} (hcl : Rega.LabelClean T.toIsa)
    (lt : LegalTarget) (raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) :
    ∀ {fs : List Fn} {hints : List T.toIsa.Hints}
      {code : List T.Directive} {b s : Nat},
      compileModuleRecAux T.toIsa lt raBytes recSigs extCallees exits nX fs hints =
        .ok (code, b, s) →
      (fs.map Fn.name).Nodup → fs.all (fun f => fnNameOk f.name) = true →
      (∀ (i : Nat) (l : Sym), code[i]? = some (T.frame.label l) →
        ∃ f ∈ fs, l = f.name ∨ ∃ a, l = Rega.lname f.name a) ∧
      (∀ (i j : Nat) (l : Sym), code[i]? = some (T.frame.label l) →
        code[j]? = some (T.frame.label l) → i = j)
  | [], [], _, _, _, hcm, _, _ => by
    dsimp only [compileModuleRecAux] at hcm; simp only [Except.ok.injEq, Prod.mk.injEq] at hcm
    rcases hcm with ⟨rfl, _, _⟩
    exact ⟨fun _ _ hi => by simp at hi, fun _ _ _ hi => by simp at hi⟩
  | [], _ :: _, _, _, _, hcm, _, _ => by dsimp only [compileModuleRecAux] at hcm; cases hcm
  | _ :: _, [], _, _, _, hcm, _, _ => by dsimp only [compileModuleRecAux] at hcm; cases hcm
  | f :: fs, h :: hs, code, b, s, hcm, hnd, hok => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    simp only [List.all_cons, Bool.and_eq_true] at hok
    dsimp only [compileModuleRecAux] at hcm
    split at hcm
    · rename_i c bf sf hl _
      split at hcm
      · rename_i cs brest srest hrest
        simp only [Except.ok.injEq, Prod.mk.injEq] at hcm
        rcases hcm with ⟨rfl, _, _⟩
        obtain ⟨ih_mem, ih_uniq⟩ := compileModuleRecAux_code_labels hcl lt raBytes recSigs
          extCallees exits nX hrest hnd.2 hok.2
        have hc_mem : ∀ (i : Nat) (l : Sym), c[i]? = some (T.frame.label l) →
            l = f.name ∨ ∃ a, l = Rega.lname f.name a :=
          fun i l hi => Rega.lowerFn_label_mem hcl hl hi
        have hc_uniq := Rega.lowerFn_labelsUnique hcl hl
        constructor
        · intro i l hi
          by_cases hlt : i < c.length
          · rw [List.getElem?_append_left hlt] at hi
            exact ⟨f, List.mem_cons_self, hc_mem i l hi⟩
          · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
            obtain ⟨g, hg, hl'⟩ := ih_mem (i - c.length) l hi
            exact ⟨g, List.mem_cons_of_mem f hg, hl'⟩
        · intro i j l hi hj
          have disj : ∀ {i₁ j₁ : Nat}, c[i₁]? = some (T.frame.label l) →
              cs[j₁]? = some (T.frame.label l) → False := by
            intro i₁ j₁ hi₁ hj₁
            obtain ⟨g, hg, hlg⟩ := ih_mem j₁ l hj₁
            have hgok := List.all_eq_true.mp hok.2 g hg
            rcases hc_mem i₁ l hi₁ with rfl | ⟨a, rfl⟩ <;> rcases hlg with hgl | ⟨b, hgl⟩
            · exact hnd.1 g hg hgl.symm
            · exact lname_ne_cross hok.1 hgl.symm
            · exact lname_ne_cross hgok hgl
            · exact hnd.1 g hg (lname_inj_cross hok.1 hgok hgl).1.symm
          by_cases hic : i < c.length <;> by_cases hjc : j < c.length
          · rw [List.getElem?_append_left hic] at hi
            rw [List.getElem?_append_left hjc] at hj
            exact hc_uniq i j l hi hj
          · rw [List.getElem?_append_left hic] at hi
            rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
            exact absurd hi (fun h' => disj h' hj)
          · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
            rw [List.getElem?_append_left hjc] at hj
            exact absurd hj (fun h' => disj h' hi)
          · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
            rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
            have heq := ih_uniq (i - c.length) (j - c.length) l hi hj
            omega
      · simp at hcm
    · simp at hcm
    · simp at hcm

theorem compileModuleRec_labelsUnique {T : Target} (hcl : Rega.LabelClean T.toIsa)
    {lt : LegalTarget} {raBytes : Nat} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX fuel maxBound : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {code : List T.Directive} {base step : Nat}
    (hcm : compileModuleRec T.toIsa lt raBytes extCallees exits nX fuel maxBound fs hints =
      .ok (code, base, step))
    (hnd : (fs.map Fn.name ++ exits).Nodup)
    (hok : (fs.map Fn.name ++ exits).all fnNameOk = true) :
    ∀ (i j : Nat) (l : Sym),
      (code ++ exits.map T.frame.label)[i]? = some (T.frame.label l) →
      (code ++ exits.map T.frame.label)[j]? = some (T.frame.label l) → i = j := by
  dsimp only [compileModuleRec] at hcm
  split at hcm; · simp at hcm
  split at hcm; · simp at hcm
  rename_i code' b' s' haux
  split at hcm
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hcm
    rcases hcm with ⟨rfl, _, _⟩
    have hnd_split := List.nodup_append.mp hnd
    simp only [List.all_append, Bool.and_eq_true, List.all_map] at hok
    obtain ⟨hmem, huniq⟩ := compileModuleRecAux_code_labels hcl lt raBytes _ extCallees exits nX
      haux hnd_split.1 hok.1
    have hEx : ∀ (k : Nat) (l : Sym),
        (exits.map T.frame.label)[k]? = some (T.frame.label l) → exits[k]? = some l := by
      intro k l hk
      rw [List.getElem?_map] at hk
      cases hx : exits[k]? with
      | none => simp [hx] at hk
      | some e =>
        simp only [hx, Option.map_some, Option.some.injEq] at hk
        rw [hcl.label_inj e l hk]
    have hdisj : ∀ (i₁ k₂ : Nat) (l : Sym), code'[i₁]? = some (T.frame.label l) →
        (exits.map T.frame.label)[k₂]? = some (T.frame.label l) → False := by
      intro i₁ k₂ l hi₁ hk₂
      have hmemE : l ∈ exits := List.mem_of_getElem? (hEx k₂ l hk₂)
      have hlok : fnNameOk l = true := List.all_eq_true.mp hok.2 l hmemE
      obtain ⟨f, hf, hlf⟩ := hmem i₁ l hi₁
      rcases hlf with hl_eq | ⟨a, hl_eq⟩
      · exact hnd_split.2.2 l (hl_eq ▸ List.mem_map_of_mem hf) l hmemE rfl
      · exact lname_ne_cross hlok hl_eq.symm
    intro i j l hi hj
    by_cases hic : i < code'.length <;> by_cases hjc : j < code'.length
    · rw [List.getElem?_append_left hic] at hi; rw [List.getElem?_append_left hjc] at hj
      exact huniq i j l hi hj
    · rw [List.getElem?_append_left hic] at hi
      rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
      exact absurd hi (fun h' => hdisj i (j - code'.length) l h' hj)
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
      rw [List.getElem?_append_left hjc] at hj
      exact absurd hj (fun h' => hdisj j (i - code'.length) l h' hi)
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
      rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
      have heq := nodup_getElem?_inj hnd_split.2.1 (hEx _ _ hi) (hEx _ _ hj)
      omega
  · simp at hcm

theorem compileModuleRec_bounds_le {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel maxBound : Nat}
    {fs : List Fn} {hints : List I.Hints} {code : List I.Directive} {base step : Nat}
    (h : compileModuleRec I lt raBytes extCallees exits nX fuel maxBound fs hints =
      .ok (code, base, step)) :
    base + fuel * step ≤ maxBound ∧ maxBound ≤ 2 ^ 64 ∧ base + fuel * step + raBytes ≤ 2 ^ 64 := by
  dsimp only [compileModuleRec] at h
  split at h; · simp at h
  split at h; · simp at h
  split at h
  · rename_i hb
    simp only [Bool.and_eq_true] at hb
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl, rfl⟩
    exact ⟨Nat.le_of_ble_eq_true hb.1.1, Nat.le_of_ble_eq_true hb.1.2,
      Nat.le_of_ble_eq_true hb.2⟩
  · simp at h

theorem checkCompileRecResult_parts {D : Type} {label : Sym → D} {progSmall : List D → Bool}
    {res : Except String (List D × Nat × Nat)} {fnNames exits : List Sym}
    (h : checkCompileRecResult label progSmall res fnNames exits = true) :
    res = .ok (extractRecCode res, extractRecBase res, extractRecStep res) ∧
      fnNames.all fnNameOk = true ∧ exits.all fnNameOk = true ∧
      (fnNames ++ exits).Nodup ∧ progSmall (extractRecCode res ++ exits.map label) = true := by
  cases res with
  | error _ => dsimp only [checkCompileRecResult] at h; cases h
  | ok cbs =>
    rcases cbs with ⟨c, b, s⟩
    dsimp only [checkCompileRecResult] at h; simp only [Bool.and_eq_true] at h
    unfold extractRecCode extractRecBase extractRecStep
    exact ⟨rfl, h.1.1.1, h.1.1.2, stringsNodup_nodup h.1.2, h.2⟩

theorem checkCompileRecWithLabels_parts {D : Type} {label : Sym → D}
    {labelsNodup progSmall : List D → Bool}
    {res : Except String (List D × Nat × Nat)} {exits : List Sym}
    (h : checkCompileRecResultWithLabels label labelsNodup progSmall res exits = true) :
    res = .ok (extractRecCode res, extractRecBase res, extractRecStep res) ∧
      labelsNodup (extractRecCode res ++ exits.map label) = true ∧
      progSmall (extractRecCode res ++ exits.map label) = true := by
  cases res with
  | error _ => simp [checkCompileRecResultWithLabels] at h
  | ok cbs =>
    rcases cbs with ⟨c, b, s⟩
    simp only [checkCompileRecResultWithLabels, Bool.and_eq_true] at h
    unfold extractRecCode extractRecBase extractRecStep
    exact ⟨rfl, h.1, h.2⟩

/-! ## 3. `CompiledRec`, `checkCompileRec`, and `link_rec_compiled` -/

/-- Bundle of a compiled cyclic/mutually-recursive typed module on target `T`, constructed from a
single kernel evaluation of `checkCompileRec` (or `checkCompileRecWithLabels`). -/
structure CompiledRec (T : Target) (lt : LegalTarget) (extCallees : List (SigEntry × Nat))
    (exits : List Sym) (nX fuel : Nat) (fs : List Fn) (hints : List T.toIsa.Hints)
    (maxBound : Nat := 2048) where
  code : List T.Directive
  baseBound : Nat
  stepBound : Nat
  compileModuleRec_eq :
    compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound fs hints =
      .ok (code, baseBound, stepBound)
  compile_eq : compile T.toIsa lt fs hints = .ok code
  bound_le : baseBound + fuel * stepBound ≤ maxBound
  maxBound_le : maxBound ≤ 2 ^ 64
  total_ra_le : baseBound + fuel * stepBound + T.frame.raBytes ≤ 2 ^ 64
  host : T.mach.Host
  prog_host : T.mach.prog host = code ++ exits.map T.frame.label
  labelsUnique : T.LabelsUnique host

namespace CompiledRec

variable {T : Target} {lt : LegalTarget} {extCallees : List (SigEntry × Nat)}
  {exits : List Sym} {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
  {maxBound : Nat}

/-- Stack bound at recursion measure `k`: `baseBound + k * stepBound`. -/
@[expose] def boundAt (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (k : Nat) : Nat :=
  M.baseBound + k * M.stepBound

theorem boundAt_mono (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    {k₁ k₂ : Nat} (hk : k₁ ≤ k₂) : M.boundAt k₁ ≤ M.boundAt k₂ :=
  Nat.add_le_add_left (Nat.mul_le_mul_right M.stepBound hk) M.baseBound

theorem boundAt_le_max (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    {k : Nat} (hk : k ≤ fuel) : M.boundAt k ≤ maxBound :=
  Nat.le_trans (M.boundAt_mono hk) M.bound_le

theorem total_ra_le_at (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    {k : Nat} (hk : k ≤ fuel) : M.boundAt k + T.frame.raBytes ≤ 2 ^ 64 :=
  Nat.le_trans (Nat.add_le_add_right (M.boundAt_mono hk) _) M.total_ra_le

theorem code_infix_host (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound) :
    M.code.IsInfixAt (T.mach.prog M.host) 0 := by
  rw [M.prog_host]; exact ⟨exits.map T.frame.label, rfl⟩

theorem defined_exit_host (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    {g : Sym} (hg : g ∈ exits) : T.Defined M.host g := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  refine ⟨M.code.length + i, ?_⟩
  rw [M.prog_host, List.getElem?_append_right (by omega), List.getElem?_map]; simp [hi]

end CompiledRec

/-- Single boolean predicate checked once by `t_kernel_rfl` for a cyclic/recursive module. -/
@[expose] def checkCompileRec (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX fuel : Nat)
    (fs : List Fn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048) : Bool :=
  checkCompileRecResult T.frame.label L.progSmall
    (compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound fs hints)
    (fs.map Fn.name) exits

/-- Construct `CompiledRec` from `checkCompileRec = true` and `hcl : Rega.LabelClean T.toIsa`. -/
@[expose] def compileRecChecked (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (hcl : Rega.LabelClean T.toIsa) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX fuel : Nat) (fs : List Fn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048)
    (h : checkCompileRec T L lt extCallees exits nX fuel fs hints maxBound = true) :
    CompiledRec T lt extCallees exits nX fuel fs hints maxBound where
  code := extractRecCode
    (compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound fs hints)
  baseBound := extractRecBase
    (compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound fs hints)
  stepBound := extractRecStep
    (compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound fs hints)
  compileModuleRec_eq := (checkCompileRecResult_parts h).1
  compile_eq := compileRec_of_compileModuleRec (checkCompileRecResult_parts h).1
  bound_le := (compileModuleRec_bounds_le (checkCompileRecResult_parts h).1).1
  maxBound_le := (compileModuleRec_bounds_le (checkCompileRecResult_parts h).1).2.1
  total_ra_le := (compileModuleRec_bounds_le (checkCompileRecResult_parts h).1).2.2
  host := L.layoutOf
    (extractRecCode (compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel
        maxBound fs hints) ++ exits.map T.frame.label)
    (checkCompileRecResult_parts h).2.2.2.2
  prog_host := L.prog_layoutOf _ _
  labelsUnique := by
    have hp := checkCompileRecResult_parts h
    intro i j l hi hj; rw [L.prog_layoutOf _ hp.2.2.2.2] at hi hj
    exact compileModuleRec_labelsUnique hcl hp.1 hp.2.2.2.1
      (by simp only [List.all_append, Bool.and_eq_true]; exact ⟨hp.2.1, hp.2.2.1⟩) i j l hi hj

/-- Variant boolean predicate checking label uniqueness via `L.labelsNodup`. -/
@[expose] def checkCompileRecWithLabels (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX fuel : Nat)
    (fs : List Fn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048) : Bool :=
  checkCompileRecResultWithLabels T.frame.label L.labelsNodup L.progSmall
    (compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound fs hints)
    exits

/-- Construct `CompiledRec` via `L.labelsNodup` and `L.labelsUnique_layoutOf`. -/
@[expose] def compileRecCheckedWithLabels (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX fuel : Nat)
    (fs : List Fn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048)
    (h : checkCompileRecWithLabels T L lt extCallees exits nX fuel fs hints maxBound = true) :
    CompiledRec T lt extCallees exits nX fuel fs hints maxBound where
  code := extractRecCode
    (compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound fs hints)
  baseBound := extractRecBase
    (compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound fs hints)
  stepBound := extractRecStep
    (compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound fs hints)
  compileModuleRec_eq := (checkCompileRecWithLabels_parts h).1
  compile_eq := compileRec_of_compileModuleRec (checkCompileRecWithLabels_parts h).1
  bound_le := (compileModuleRec_bounds_le (checkCompileRecWithLabels_parts h).1).1
  maxBound_le := (compileModuleRec_bounds_le (checkCompileRecWithLabels_parts h).1).2.1
  total_ra_le := (compileModuleRec_bounds_le (checkCompileRecWithLabels_parts h).1).2.2
  host := L.layoutOf
    (extractRecCode (compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel
        maxBound fs hints) ++ exits.map T.frame.label)
    (checkCompileRecWithLabels_parts h).2.2
  prog_host := L.prog_layoutOf _ _
  labelsUnique := L.labelsUnique_layoutOf
    (checkCompileRecWithLabels_parts h).2.2 (checkCompileRecWithLabels_parts h).2.1

private theorem defined_of_lowerFn {T : Target} {host : T.mach.Host}
    {hints : T.toIsa.Hints} {E : Rega.Ext} {f : Fn} {code : List T.Directive} {k₀ : Nat}
    (hl : Rega.lowerFn T.toIsa hints E f = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) : T.Defined host f.name := by
  unfold Rega.lowerFn at hl
  split at hl
  · cases hl
  · cases hal : T.toIsa.assignArgs f.as with
    | none => simp [hal] at hl
    | some argLocs =>
      cases hrl : T.toIsa.assignRets f.rs with
      | none => simp [hal, hrl] at hl
      | some _ =>
        simp only [hal, hrl] at hl
        cases hb : Rega.bindAbiParams T.toIsa argLocs 0
            { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } with
        | none => simp [hb] at hl
        | some st0 =>
          simp only [hb] at hl
          cases hle : Rega.lowerExpr T.toIsa hints E f.name
              (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0)) f.as.length 0 0 st0 none with
          | error _ => simp [hle] at hl
          | ok _ =>
            simp only [hle, Except.ok.injEq] at hl
            subst hl
            exact ⟨k₀, (List.IsInfixAt.cons hc).1⟩

private theorem find?_pred {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {x : α}, xs.find? p = some x → p x = true
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    simp only [List.find?] at h
    cases hp : p y with
    | true => simp [hp] at h; subst h; exact hp
    | false => simp [hp] at h; exact find?_pred h

private theorem compileModuleRec_disjoint {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel maxBound : Nat}
    {fs : List Fn} {hints : List I.Hints} {code : List I.Directive} {base step : Nat}
    (h : compileModuleRec I lt raBytes extCallees exits nX fuel maxBound fs hints =
      .ok (code, base, step)) :
    (∀ p ∈ extCallees, p.1.1 ∉ fs.map Fn.name) ∧
      compileModuleRecAux I lt raBytes
        (fs.map (fun f => (f.name, lt.legalSig f.as, lt.legalSig f.rs)))
        extCallees exits nX fs hints = .ok (code, base, step) := by
  dsimp only [compileModuleRec] at h
  split at h
  · simp at h
  · rename_i hno
    split at h
    · simp at h
    · rename_i code' b' s' haux
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        refine ⟨fun p hp hmem => ?_, haux⟩
        obtain ⟨f, hf, hnm⟩ := List.mem_map.mp hmem
        exact hno (List.any_eq_true.mpr ⟨p, hp, List.any_eq_true.mpr ⟨f, hf, beq_iff_eq.mpr hnm⟩⟩)
      · simp at h

/-- Concatenate an acyclic `compileModule` program with a cyclic `compileModuleRec` program
whose function names are pairwise distinct and `fnNameOk`, yielding `T.LabelsUnique`. -/
theorem compileModule_append_rec_labelsUnique {T : Target} (hcl : Rega.LabelClean T.toIsa)
    (host : T.mach.Host) {lt₁ lt₂ : LegalTarget} {raBytes₁ raBytes₂ : Nat}
    {ext₁ ext₂ : List (SigEntry × Nat)} {exits₁ exits₂ : List Sym} {nX₁ nX₂ fuel maxBound : Nat}
    {fs₁ fs₂ : List Fn} {hints₁ hints₂ : List T.toIsa.Hints}
    {code₁ code₂ : List T.Directive} {bounds₁ : List (Sym × Nat)} {base₂ step₂ : Nat}
    (hprog : T.mach.prog host = code₁ ++ code₂)
    (hcm₁ : compileModule T.toIsa lt₁ raBytes₁ ext₁ exits₁ nX₁ fs₁ hints₁ = .ok (code₁, bounds₁))
    (hcm₂ : compileModuleRec T.toIsa lt₂ raBytes₂ ext₂ exits₂ nX₂ fuel maxBound fs₂ hints₂ =
      .ok (code₂, base₂, step₂))
    (hnd : (fs₁.map Fn.name ++ fs₂.map Fn.name).Nodup)
    (hok : (fs₁.map Fn.name ++ fs₂.map Fn.name).all fnNameOk = true) :
    T.LabelsUnique host := by
  have hnd_s := List.nodup_append.mp hnd
  simp only [List.all_append, Bool.and_eq_true, List.all_map] at hok
  obtain ⟨_, haux₂⟩ := compileModuleRec_disjoint hcm₂
  obtain ⟨hmem₁, huniq₁⟩ := compileModule_code_labels hcl lt₁ raBytes₁ exits₁ nX₁ hcm₁ hnd_s.1 hok.1
  obtain ⟨hmem₂, huniq₂⟩ :=
    compileModuleRecAux_code_labels hcl lt₂ raBytes₂ _ ext₂ exits₂ nX₂ haux₂ hnd_s.2.1 hok.2
  have hdisj : ∀ (i₁ j₂ : Nat) (l : Sym), code₁[i₁]? = some (T.frame.label l) →
      code₂[j₂]? = some (T.frame.label l) → False := by
    intro i₁ j₂ l hi₁ hj₂
    obtain ⟨f₁, hf₁, h₁⟩ := hmem₁ i₁ l hi₁; obtain ⟨f₂, hf₂, h₂⟩ := hmem₂ j₂ l hj₂
    have hok₁ := List.all_eq_true.mp hok.1 f₁ hf₁; have hok₂ := List.all_eq_true.mp hok.2 f₂ hf₂
    rcases h₁ with rfl | ⟨a, rfl⟩ <;> rcases h₂ with hnm | ⟨b, hnm⟩
    · exact hnd_s.2.2 f₁.name (List.mem_map_of_mem hf₁) f₂.name (List.mem_map_of_mem hf₂) hnm
    · exact lname_ne_cross hok₁ hnm.symm
    · exact lname_ne_cross hok₂ hnm
    · exact hnd_s.2.2 f₁.name (List.mem_map_of_mem hf₁) f₂.name
        (List.mem_map_of_mem hf₂) (lname_inj_cross hok₁ hok₂ hnm).1
  intro i j l hi hj; rw [hprog] at hi hj
  rcases Nat.lt_or_ge i code₁.length with hiL | hiR <;>
    rcases Nat.lt_or_ge j code₁.length with hjL | hjR
  · rw [List.getElem?_append_left hiL] at hi; rw [List.getElem?_append_left hjL] at hj
    exact huniq₁ i j l hi hj
  · rw [List.getElem?_append_left hiL] at hi; rw [List.getElem?_append_right hjR] at hj
    exact absurd hj (fun h' => hdisj i (j - code₁.length) l hi h')
  · rw [List.getElem?_append_right hiR] at hi; rw [List.getElem?_append_left hjL] at hj
    exact absurd hi (fun h' => hdisj j (i - code₁.length) l hj h')
  · rw [List.getElem?_append_right hiR] at hi; rw [List.getElem?_append_right hjR] at hj
    have heq := huniq₂ (i - code₁.length) (j - code₁.length) l hi hj; omega

private theorem infix_trans {α : Type} {a b c : List α} {k₁ k₂ : Nat}
    (hk1 : k₁ ≤ b.length) (h1 : a.IsInfixAt b k₁) (h2 : b.IsInfixAt c k₂) :
    a.IsInfixAt c (k₂ + k₁) := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  refine ⟨t1 ++ t2, ?_⟩
  have hd : (b ++ t2).drop k₁ = b.drop k₁ ++ t2 := by
    rw [List.drop_append, show k₁ - b.length = 0 by omega, List.drop_zero]
  rw [← List.drop_drop, ← ht2, hd, ← ht1, List.append_assoc]

private theorem fnSpec_of_spec_rec {T : Target} {h : T.mach.Host} {sym : Sym} {as bs : List Ty}
    {spec₁ spec₂ : Spec as bs} {n nX : Nat}
    (him : ∀ args m Q X, spec₂ args m Q X → spec₁ args m Q X)
    (hf : T.FnSpec h sym spec₁ n nX) : T.FnSpec h sym spec₂ n nX :=
  fun args m Q X hs => hf args m Q X (him args m Q X hs)

private theorem legalEnv_onlyFn_elim {lt : LegalTarget} {f : Fn} (Γ : Env)
    {xs' : Tup Val (lt.legalSig f.as)} {m : Mem 64}
    {Q' : Post (lt.legalSig f.rs)} {X' : XPost}
    (h : legalEnv lt (Env.onlyFn f Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs)
      xs' m Q' X') :
    ∃ (xs : Tup Val f.as) (P : Post f.rs) (E' : XPost),
      encodeTup lt f.as xs = xs' ∧ (∀ r m₁, legalPost lt P r m₁ → Q' r m₁) ∧
      (∀ g cs ys m₁, legalXPost lt E' g cs ys m₁ → X' g cs ys m₁) ∧
      Γ f.name f.as f.rs xs m P E' := by
  rcases h with ⟨as, bs, has, hbs, xs, P, E', hxs, hQ, hX, _, ha, hb, hΓ⟩
  subst ha; subst hb
  refine ⟨xs, P, E', ?_, ?_, hX, hΓ⟩
  · simpa only [cast_eq] using hxs
  · intro r m₁ hp; have := hQ r m₁ hp; rwa [cast_eq] at this

private theorem compileFn_stepRec_mid {lt : LegalTarget} {f : Fn} (hwf : f.Wf)
    (hsupp : (f.earlyOpt).body.supportsSource lt = true)
    (recSigs extSigs : List SigEntry) (Γrec : Nat → Env) (Γext : Env) (k : Nat)
    (hsound : ∀ xs m P E', Γrec k f.name f.as f.rs xs m P E' →
      Func.wp (Env.stepRec recSigs extSigs Γrec Γext k) f.body xs m P E') :
    ∀ xs' m Q' X',
      legalEnv lt (Env.onlyFn f (Γrec k)) f.name (lt.legalSig f.as) (lt.legalSig f.rs)
        xs' m Q' X' →
      Func.spec (legalEnv lt (Env.stepRec recSigs extSigs Γrec Γext k))
        (f.mid lt).body xs' m Q' X' := by
  intro xs' m Q' X' h
  have hel := legalEnv_onlyFn_elim (Γrec k) h
  exact @fn_mid_spec lt f hwf hsupp (Env.stepRec recSigs extSigs Γrec Γext k)
    hel.choose xs' hel.choose_spec.choose_spec.choose_spec.1 m
    hel.choose_spec.choose hel.choose_spec.choose_spec.choose Q' X'
    hel.choose_spec.choose_spec.choose_spec.2.1
    hel.choose_spec.choose_spec.choose_spec.2.2.1
    (hsound _ m _ _ hel.choose_spec.choose_spec.choose_spec.2.2.2)

private theorem compileFn_correct_stepRec (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (hints : T.toIsa.Hints) (E : Rega.Ext) (f : Fn)
    (recSigs extSigs : List SigEntry) (Γrec : Nat → Env) (Γext : Env) (k : Nat)
    (n nX : Nat) (bound : Sym → Nat) {code : List T.Directive} {k₀ : Nat}
    (hwf : f.Wf) (hsupp : (f.earlyOpt).body.supportsSource lt = true)
    (hl : Rega.lowerFn T.toIsa hints E (f.mid lt) = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hfr : Rega.frame T hints ≤ n) (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hsound : ∀ xs m P E', Γrec k f.name f.as f.rs xs m P E' →
      Func.wp (Env.stepRec recSigs extSigs Γrec Γext k) f.body xs m P E')
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      T.FnSpec host g
        (legalEnv lt (Env.stepRec recSigs extSigs Γrec Γext k) g as bs) (bound g) nX ∧
      Rega.frame T hints + T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → T.Defined host g ∧ nX ≤ n) :
    T.FnSpec host f.name
      (legalEnv lt (Env.onlyFn f (Γrec k)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      n nX :=
  fnSpec_of_spec_rec
    (compileFn_stepRec_mid hwf hsupp recSigs extSigs Γrec Γext k hsound)
    (Rega.lowerFn_correct T host hints E (f.mid lt)
      (legalEnv lt (Env.stepRec recSigs extSigs Γrec Γext k)) n nX bound
      (fn_mid_wf hwf) hl hc hu (Nat.le_trans (Rega.effFrame_le T.toIsa hints E) hfr) hn
      (fun g as bs hg =>
        let ⟨h1, h2⟩ := hcal g as bs hg
        ⟨h1, Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right
          (Rega.effFrame_le T.toIsa hints E) _) _) h2⟩)
      hex)

private theorem legalEnv_stepRec_nil_empty {lt : LegalTarget} {mod : Module}
    (hnd : mod.namesNodup) {Γrec : Nat → Env} {Γext : Env}
    {g : Sym} (hg : g ∈ mod.fns.map Fn.name) {as bs : List Ty}
    {xs' : Tup Val as} {m : Mem 64} {Q' : Post bs} {X' : XPost} :
    ¬ legalEnv lt (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext 0)
      g as bs xs' m Q' X' := by
  rintro ⟨as₀, bs₀, _, _, xs₀, P₀, E₀, _, _, _, hstep⟩
  rcases hstep with ⟨_, k', hk', _⟩ | ⟨hsig, _⟩
  · omega
  · obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp hg
    exact fn_name_not_mem_externs hnd hfn hsig

private theorem legalEnv_stepRec_succ_mem {lt : LegalTarget} {mod : Module}
    (hnd : mod.namesNodup) {Γrec : Nat → Env} {Γext : Env} {m_k : Nat}
    {gfn : Fn} (hgfn : gfn ∈ mod.fns)
    {xs' : Tup Val (lt.legalSig gfn.as)} {m0 : Mem 64}
    {Q' : Post (lt.legalSig gfn.rs)} {X' : XPost}
    (h : legalEnv lt
      (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext (m_k + 1))
      gfn.name (lt.legalSig gfn.as) (lt.legalSig gfn.rs) xs' m0 Q' X') :
    ∃ k' ≤ m_k,
      legalEnv lt (Env.onlyFn gfn (Γrec k')) gfn.name
        (lt.legalSig gfn.as) (lt.legalSig gfn.rs) xs' m0 Q' X' := by
  rcases h with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hstep⟩
  rcases hstep with ⟨hsig, k', hk', hΓ⟩ | ⟨hsig, _⟩
  · have hfnsNd : (mod.fns.map Fn.name).Nodup := (List.nodup_append.mp hnd).1
    have hmapFst : (mod.fns.map Fn.sig).map Prod.fst = mod.fns.map Fn.name := by
      simp [List.map_map, Function.comp_def, Fn.sig]
    obtain ⟨ha, hb⟩ := mem_unique_fst (hmapFst ▸ hfnsNd) hsig (List.mem_map_of_mem hgfn)
    subst ha; subst hb
    exact ⟨k', Nat.lt_succ_iff.mp hk', gfn.as, gfn.rs, has₀, hbs₀, xs₀, P₀, E₀,
      hxs₀, hQ₀, hX₀, rfl, rfl, rfl, hΓ⟩
  · exact absurd hsig (fn_name_not_mem_externs hnd hgfn)

private theorem legalEnv_stepRec_ext {lt : LegalTarget} {mod : Module}
    {Γrec : Nat → Env} {Γext : Env} {k : Nat} {g : Sym} (hg : g ∉ mod.fns.map Fn.name)
    {as bs : List Ty} {xs' : Tup Val as} {m0 : Mem 64} {Q' : Post bs} {X' : XPost}
    (h : legalEnv lt (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext k)
      g as bs xs' m0 Q' X') :
    legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) g as bs xs' m0 Q' X' := by
  rcases h with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hstep⟩
  rcases hstep with ⟨hsig, _⟩ | ⟨hsig, hΓ⟩
  · obtain ⟨fn, hfn, hfeq⟩ := List.mem_map.mp hsig
    have hnm : fn.name = g := congrArg Prod.fst hfeq
    exact absurd (hnm ▸ List.mem_map_of_mem hfn) hg
  · exact ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hsig, hΓ⟩

private def recCallBound (mod : Module) (extCallees : List (SigEntry × Nat))
    (baseBound stepBound k : Nat) (g : Sym) : Nat :=
  if (mod.fns.map Fn.name).contains g then
    match k with
    | 0 => 0
    | m + 1 => baseBound + m * stepBound
  else
    match extCallees.find? (fun q => q.1.1 == g) with
    | some q => q.2
    | none => 0

/-- Core strong-induction soundness theorem for `compileModuleRec` over any host `h` containing
`code` at `k₀` with `T.LabelsUnique h`. -/
theorem compileRec_sound (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (mod : Module) (Γrec : Nat → Env) (Γext : Env)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX fuel maxBound : Nat)
    (hints : List T.toIsa.Hints) (code : List T.Directive) (baseBound stepBound k₀ : Nat)
    (hcm : compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound
      mod.fns hints = .ok (code, baseBound, stepBound))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hrec : ∀ k ≤ fuel, ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γrec k f.name f.as f.rs xs m Q X →
      Func.wp (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext k)
        f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec host p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined host g) :
    ∀ k ≤ fuel, ∀ f ∈ mod.fns, T.Defined host f.name ∧
      T.FnSpec host f.name
        (legalEnv lt (Env.onlyFn f (Γrec k)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        (baseBound + k * stepBound) nX := by
  have hnd := Module.namesNodup_of_checkNamesNodup
    ((Bool.and_eq_true _ _).mp hcyc).1
  obtain ⟨hdisj, haux⟩ := compileModuleRec_disjoint hcm
  obtain ⟨_, _, htot_ra⟩ := compileModuleRec_bounds_le hcm
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk f hf
    obtain ⟨hint, c, k_f, bf, sf, hl, hinf, hklen, hchk, hbf, hsf⟩ :=
      compileModuleRecAux_mem haux f hf
    have hc_f : c.IsInfixAt (T.mach.prog host) (k₀ + k_f) := infix_trans hklen hinf hc
    have hfdef : T.Defined host f.name := defined_of_lowerFn (f := f.mid lt) hl hc_f
    obtain ⟨hsf_eq, hfr_b, hcal_b, hex_b⟩ := checkAndBoundRecExt_spec hchk
    have hfr : Rega.frame T hint ≤ baseBound + k * stepBound :=
      Nat.le_trans hfr_b (Nat.le_trans hbf (Nat.le_add_right _ _))
    have hn : (baseBound + k * stepBound) + T.frame.raBytes ≤ 2 ^ 64 := by
      have hmul : k * stepBound ≤ fuel * stepBound := Nat.mul_le_mul_right stepBound hk
      omega
    let bound : Sym → Nat := recCallBound mod extCallees baseBound stepBound k
    have hcal : ∀ g as bs, (g, as, bs) ∈ (f.mid lt).ext.callees →
        T.FnSpec host g
          (legalEnv lt (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig)
            Γrec Γext k) g as bs)
          (bound g) nX ∧
        Rega.frame T hint + T.frame.raBytes + bound g ≤ baseBound + k * stepBound := by
      intro g as bs hg
      rcases hcal_b (g, as, bs) hg with ⟨hrec_sig, hstep_b⟩ | ⟨_, bg, hlk, hbg_b⟩
      · obtain ⟨gfn, hgfn, hgeq⟩ := List.mem_map.mp hrec_sig
        rcases Prod.mk.inj hgeq with ⟨rfl, hsig_ab⟩
        rcases Prod.mk.inj hsig_ab with ⟨rfl, rfl⟩
        have hmem_nm : gfn.name ∈ mod.fns.map Fn.name := List.mem_map_of_mem hgfn
        have hcon : (mod.fns.map Fn.name).contains gfn.name = true := by simpa using hmem_nm
        cases k with
        | zero =>
          refine ⟨?_, ?_⟩
          · intro args m0 Q X hleg
            exact absurd hleg (legalEnv_stepRec_nil_empty hnd hmem_nm)
          · dsimp only [bound, recCallBound]
            simp only [hcon, ↓reduceIte, Nat.add_zero, Nat.zero_mul]
            exact Nat.le_trans hstep_b hbf
        | succ m =>
          have hbd : bound gfn.name = baseBound + m * stepBound := by
            dsimp only [bound, recCallBound]
            rw [hcon]
            simp
          rw [hbd]
          refine ⟨?_, ?_⟩
          · intro args m0 Q X hleg s ra R hargs hra hspE hmem
            obtain ⟨k', hk', hleg'⟩ := legalEnv_stepRec_succ_mem hnd hgfn hleg
            have hk'_le : k' ≤ fuel := Nat.le_trans hk' (by omega)
            have hih := (ih k' (Nat.lt_succ_iff.mpr hk') hk'_le gfn hgfn).2
            have hmle : baseBound + k' * stepBound ≤ baseBound + m * stepBound :=
              Nat.add_le_add_left (Nat.mul_le_mul_right stepBound hk') baseBound
            have hbra : (baseBound + m * stepBound) + T.frame.raBytes ≤ 2 ^ 64 := by
              have hmul : m * stepBound ≤ fuel * stepBound :=
                Nat.mul_le_mul_right stepBound (by omega)
              omega
            exact (Target.FnSpec.mono_stack T hih hmle hbra)
              args m0 Q X hleg' s ra R hargs hra hspE hmem
          · have hfr_sf : Rega.frame T hint + T.frame.raBytes ≤ stepBound := by
              rw [← hsf_eq]; exact hsf
            rw [Nat.succ_mul]
            omega
      · have hmem_ext : ((g, as, bs), bg) ∈ extCallees := lookupBound_mem hlk
        have hnot_nm : g ∉ mod.fns.map Fn.name := hdisj ((g, as, bs), bg) hmem_ext
        have hcon : (mod.fns.map Fn.name).contains g = false := by
          simpa [List.contains_eq_mem] using hnot_nm
        have hbd : bound g = bg := by
          dsimp only [bound, recCallBound]; rw [hcon]
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hfnd : extCallees.find? (fun q => q.1.1 == g) with
          | none =>
            exfalso; have hnot := List.find?_eq_none.mp hfnd ((g, as, bs), bg) hmem_ext
            simp at hnot
          | some q =>
            have hqmem : q ∈ extCallees := List.mem_of_find?_eq_some hfnd
            have hpred : q.1.1 = g :=
              beq_iff_eq.mp (find?_pred (p := fun q : SigEntry × Nat => q.1.1 == g) hfnd)
            exact hext_uniq q hqmem ((g, as, bs), bg) hmem_ext hpred
        rw [hbd]
        refine ⟨?_, Nat.le_trans hbg_b (Nat.le_trans hbf (Nat.le_add_right _ _))⟩
        exact Target.FnSpec.of_spec T (hext ((g, as, bs), bg) hmem_ext)
          fun args m0 Q X hleg => legalEnv_stepRec_ext hnot_nm hleg
    have hex : ∀ g, g ∈ (f.mid lt).ext.exits → T.Defined host g ∧ nX ≤ baseBound + k * stepBound :=
      fun g hg => ⟨hexits g (hex_b g hg).1,
        Nat.le_trans (hex_b g hg).2 (Nat.le_trans hbf (Nat.le_add_right _ _))⟩
    exact ⟨hfdef, compileFn_correct_stepRec T host lt hint (f.mid lt).ext f
      (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext k
      (baseBound + k * stepBound) nX bound (hwf f hf) (hsupp f hf) hl hc_f hu
      hfr hn (hrec k hk f hf) hcal hex⟩

/-- Transfer `T.FnSpec` from `legalEnv lt (Env.onlyFn f Γ)` directly to source `Γ` when
`lt.legalSig` fixes `(f.as, f.rs)`. -/
theorem fnSpec_of_legalEnv_onlyFn {T : Target} {host : T.mach.Host} {lt : LegalTarget}
    {f : Fn} {Γ : Env} {n nX : Nat}
    (has : lt.legalSig f.as = f.as) (hbs : lt.legalSig f.rs = f.rs)
    (hf : T.FnSpec host f.name
      (legalEnv lt (Env.onlyFn f Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs)) n nX) :
    T.FnSpec host f.name
      (fun args m Q X => Γ f.name f.as f.rs args m Q
        (fun g cs xs m' => X g (lt.legalSig cs) (encodeTup lt cs xs) m')) n nX := by
  intro args m Q X hΓ s ra R hargs hra hspE hmemS
  let args' : Tup Val (lt.legalSig f.as) := cast (congrArg (Tup Val) has.symm) args
  let Q' : Post (lt.legalSig f.rs) := fun ys m' => Q (cast (congrArg (Tup Val) hbs) ys) m'
  have hleg : legalEnv lt (Env.onlyFn f Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs)
      args' m Q' X := by
    refine ⟨f.as, f.rs, rfl, rfl, args, Q,
      (fun g cs xs m' => X g (lt.legalSig cs) (encodeTup lt cs xs) m'),
      ?_, ?_, ?_, rfl, rfl, rfl, hΓ⟩
    · rw [cast_eq]; exact encodeTup_eq_cast_of_legalSig_eq has args
    · rintro r m₁ ⟨xs, rfl, hq⟩
      dsimp only [Q']
      rw [cast_eq, encodeTup_eq_cast_of_legalSig_eq hbs xs, cast_cast_eq]; exact hq
    · rintro g cs' ys m₁ ⟨cs, hcs, xs, hy, hx⟩
      subst hcs; subst hy; exact hx
  have hargs' : T.ArgsIn args' s := (T.argsIn_cast has.symm args s).mpr hargs
  refine eventually_weaken _ _ _ _ ?_ (hf args' m Q' X hleg s ra R hargs' hra hspE hmemS)
  rintro st (⟨hpc, rets', m', hQ', hrets', hrest, hm'⟩ | hEx)
  · exact Or.inl ⟨hpc, cast (congrArg (Tup Val) hbs) rets', m', hQ',
      (T.retsIn_cast hbs rets' (T.mach.data st)).mpr hrets', hrest, hm'⟩
  · exact Or.inr hEx

/-- **`B1.1` headline theorem:** measure-indexed linking over any `CompiledRec` certificate and
compatible host `h`. -/
theorem link_rec_compiled {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γrec : Nat → Env) (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hrec : ∀ k ≤ fuel, ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γrec k f.name f.as f.rs xs m Q X →
      Func.wp (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext k)
        f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ k ≤ fuel, ∀ f ∈ mod.fns, T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.onlyFn f (Γrec k)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.boundAt k) nX :=
  compileRec_sound T h lt mod Γrec Γext extCallees exits nX fuel maxBound hints
    M.code M.baseBound M.stepBound k₀ (hfs ▸ M.compileModuleRec_eq) hc hu hcyc hwf hsupp hrec
    hext hext_uniq hexits

/-- Specialization of `link_rec_compiled` to `M.host` with `extCallees = []`. -/
theorem link_rec_compiled_host {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {maxBound : Nat}
    (M : CompiledRec T lt [] exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γrec : Nat → Env) (Γext : Env)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hrec : ∀ k ≤ fuel, ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γrec k f.name f.as f.rs xs m Q X →
      Func.wp (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext k)
        f.body xs m Q X) :
    ∀ k ≤ fuel, ∀ f ∈ mod.fns, T.Defined M.host f.name ∧
      T.FnSpec M.host f.name
        (legalEnv lt (Env.onlyFn f (Γrec k)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.boundAt k) nX :=
  link_rec_compiled M mod hfs M.host Γrec Γext 0 M.code_infix_host M.labelsUnique hcyc hwf hsupp
    hrec (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ hg => M.defined_exit_host hg)

/-- Source-level specialization of `link_rec_compiled_host` when `lt.legalSig` fixes
`(f.as, f.rs)`. -/
theorem link_rec_compiled_src {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {maxBound : Nat}
    (M : CompiledRec T lt [] exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γrec : Nat → Env) (Γext : Env)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hrec : ∀ k ≤ fuel, ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γrec k f.name f.as f.rs xs m Q X →
      Func.wp (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext k)
        f.body xs m Q X)
    {k : Nat} (hk : k ≤ fuel) {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hbs : lt.legalSig f.rs = f.rs) :
    T.Defined M.host f.name ∧
      T.FnSpec M.host f.name
        (fun args m Q X => Γrec k f.name f.as f.rs args m Q
          (fun g cs xs m' => X g (lt.legalSig cs) (encodeTup lt cs xs) m'))
        (M.boundAt k) nX :=
  let ⟨hd, hs⟩ := link_rec_compiled_host M mod hfs Γrec Γext hcyc hwf hsupp hrec k hk f hf
  ⟨hd, fnSpec_of_legalEnv_onlyFn has hbs hs⟩

/-- Non-exiting source-level specialization of `link_rec_compiled_host`. -/
theorem link_rec_compiled_src_noExit {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {maxBound : Nat}
    (M : CompiledRec T lt [] exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γrec : Nat → Env) (Γext : Env)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hrec : ∀ k ≤ fuel, ∀ f ∈ mod.fns, ∀ xs m Q X,
      Γrec k f.name f.as f.rs xs m Q X →
      Func.wp (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext k)
        f.body xs m Q X)
    {k : Nat} (hk : k ≤ fuel) {f : Fn} (hf : f ∈ mod.fns)
    (has : lt.legalSig f.as = f.as) (hbs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γrec k f.name f.as f.rs args m Q X →
      Γrec k f.name f.as f.rs args m Q X') :
    T.Defined M.host f.name ∧ T.FnSpec M.host f.name (Γrec k f.name f.as f.rs) (M.boundAt k) nX :=
  let ⟨hd, hs⟩ := link_rec_compiled_src M mod hfs Γrec Γext hcyc hwf hsupp hrec hk hf has hbs
  ⟨hd, Target.FnSpec.of_spec T hs fun args m Q X h => hnoex args m Q X _ h⟩

/-! ## 4. Concrete `TargetInit` Helpers for `CompiledRec` -/

section TargetInitRec

variable {T : Target} {maxStack maxMem : Nat} (I : TargetInit T maxStack maxMem)
  {lt : LegalTarget} {extCallees : List (SigEntry × Nat)} {exits : List Sym}
  {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}

/-- Run a function `nm` in `M.host` at measure `k ≤ fuel` from
`I.initState (M.boundAt k) bsMem args`. -/
theorem run_rec_fnSpec (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    {k : Nat} (hk : k ≤ fuel) {nm : Sym} {as bs : List Ty} {spec : Spec as bs}
    (hf : T.FnSpec M.host nm spec (M.boundAt k) nX)
    (bsMem : List UInt8) (args : Tup Val as) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs as).isSome = true) {Q : Post bs} {X : XPost}
    (hspec : spec args (bsMem.At 0x1000#64) Q X) {post : T.mach.State → Prop}
    (hpost : ∀ st, (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (M.boundAt k) ⋆ Std.ExtHashMap.emp)) ∨
      (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64), X sym' cs xs m' ∧
        T.mach.pc st = T.mach.labelAddr M.host sym' ∧ T.ArgsIn xs (T.mach.data st)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host) post
      (T.mach.mkState (I.initState (M.boundAt k) bsMem args) (T.mach.labelAddr M.host nm)) := by
  have hmem := I.mem_entry (M.boundAt k) bsMem args (Nat.le_trans (M.boundAt_le_max hk) hbound) hbs
  rw [← I.get_sp (M.boundAt k) bsMem args] at hmem
  refine eventually_weaken _ _ _ _ ?_ (hf args (bsMem.At 0x1000#64) Q X hspec
    (I.initState (M.boundAt k) bsMem args) I.ra0 Std.ExtHashMap.emp (I.argsIn _ _ _ hargs)
    (I.raReg _ _ _) (by rw [I.get_sp]; exact I.spEntry) hmem)
  rintro st (⟨hpc, rets, m', hQ, hrets, _, hm'⟩ | ⟨sym', cs, xs, m', hX, _, hpc, has, _⟩)
  · rw [I.get_sp] at hm'; exact hpost st (Or.inl ⟨hpc, rets, m', hQ, hrets, hm'⟩)
  · exact hpost st (Or.inr ⟨sym', cs, xs, m', hX, hpc, has⟩)

/-- Run a non-exiting function in `CompiledRec` returning a singleton `(v, ()) : Tup Val [t]`. -/
theorem run_rec_ret1 (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    {k : Nat} (hk : k ≤ fuel) {nm : Sym} {as : List Ty} {t : Ty} {spec : Spec as [t]}
    (hf : T.FnSpec M.host nm spec (M.boundAt k) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val t) (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [t]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.RetsIn (bs := [t]) (v, ()) (T.mach.data st))
      (T.mach.mkState (I.initState (M.boundAt k) bsMem args) (T.mach.labelAddr M.host nm)) := by
  refine run_rec_fnSpec I M hk hf bsMem args hbs hargs hspec ?_ hbound
  rintro st (⟨hpc, rets, m', hq, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · have hr := hQ rets m' hq; subst hr; exact ⟨hpc, hrets⟩
  · exact hx.elim

/-- Specialization of `run_rec_ret1` to `i64`, projecting the return value to `I.ret0`. -/
theorem run_rec_ret1_i64 (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    {k : Nat} (hk : k ≤ fuel) {nm : Sym} {as : List Ty} {spec : Spec as [i64]}
    (hf : T.FnSpec M.host nm spec (M.boundAt k) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val i64) (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [i64]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState (M.boundAt k) bsMem args) (T.mach.labelAddr M.host nm)) :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, I.retsIn_singleton v _ h.2⟩)
    (run_rec_ret1 I M hk hf bsMem args v hbs hargs hspec hQ hbound)

end TargetInitRec

end LeanQbe.T.LinkRec

