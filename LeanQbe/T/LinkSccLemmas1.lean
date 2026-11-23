module

public import LeanQbe.T.LinkScc
public import LeanQbe.T.LinkRecLemmas
public import LeanQbe.T.SccLemmas
import LeanQbe.T.OptLemmas
import LeanQbe.T.LegalLemmas
import LeanQbe.T.RegaLemmas

/-!
# Soundness of `LeanQbe.T.LinkScc` — Part 1

* **Source/IR well-founded SCC linking**: signature isolation for `Env.ofModuleScc`,
  `Env.stepIdx_le_ofModuleScc`, `Env.sound_scc_at`, `Env.sound_scc`, `moduleSccOk_of_step`, and
  `Env.sound_scc_idx`.
* **Core well-founded machine linking**: `defined_of_compileModuleRecAux` and `compileScc_sound`
  (proved by `WellFounded.induction idx.wf` over `compileModuleRecAux`, supporting both
  `stepBound = 0` loose edges and `stepBound ≠ 0` depth-decreasing edges).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LinkScc

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.LinkRec

/-! ## 1. Signature Isolation and Source/IR `Env.sound_scc` -/

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

private theorem fn_name_not_mem_externs {M : Module} (hnd : M.namesNodup)
    {fn : Fn} (hfn : fn ∈ M.fns) {as bs : List Ty} :
    (fn.name, as, bs) ∉ M.externs.map Extern.sig := by
  intro hex
  have hdisj := (List.nodup_append.mp hnd).2.2
  have h1 : fn.name ∈ M.fns.map Fn.name := List.mem_map_of_mem hfn
  obtain ⟨ex, hexm, heq⟩ := List.mem_map.mp hex
  have h2 : ex.name ∈ M.externs.map Extern.name := List.mem_map_of_mem hexm
  exact hdisj fn.name h1 ex.name h2 (congrArg Prod.fst heq).symm

theorem Env.ofModuleScc_empty_off_sig {ι : Type} {M : Module} (hnd : M.namesNodup)
    (Γrec : ι → Env) (Γext : Env) {fn : Fn} (hfn : fn ∈ M.fns)
    {as bs : List Ty} (hne : (as, bs) ≠ (fn.as, fn.rs))
    (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    ¬ Env.ofModuleScc M Γrec Γext fn.name as bs xs m Q X := by
  rintro (⟨hsig, _⟩ | ⟨hsig, _⟩)
  · have ⟨ha, hb⟩ := mem_unique_fst (sigs_map_fst M ▸ hnd)
      (mem_fns_sig_mem_sigs hsig) (mem_fns_sig_mem_sigs (List.mem_map_of_mem hfn))
    exact hne (Prod.ext ha hb)
  · have ⟨ha, hb⟩ := mem_unique_fst (sigs_map_fst M ▸ hnd)
      (mem_externs_sig_mem_sigs hsig) (mem_fns_sig_mem_sigs (List.mem_map_of_mem hfn))
    exact hne (Prod.ext ha hb)

theorem Env.ofModuleScc_empty_off_extern_sig {ι : Type} {M : Module} (hnd : M.namesNodup)
    (Γrec : ι → Env) (Γext : Env) {ex : Extern} (hex : ex ∈ M.externs)
    {as bs : List Ty} (hne : (as, bs) ≠ (ex.as, ex.rs))
    (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    ¬ Env.ofModuleScc M Γrec Γext ex.name as bs xs m Q X := by
  rintro (⟨hsig, _⟩ | ⟨hsig, _⟩)
  · have ⟨ha, hb⟩ := mem_unique_fst (sigs_map_fst M ▸ hnd)
      (mem_fns_sig_mem_sigs hsig) (mem_externs_sig_mem_sigs (List.mem_map_of_mem hex))
    exact hne (Prod.ext ha hb)
  · have ⟨ha, hb⟩ := mem_unique_fst (sigs_map_fst M ▸ hnd)
      (mem_externs_sig_mem_sigs hsig) (mem_externs_sig_mem_sigs (List.mem_map_of_mem hex))
    exact hne (Prod.ext ha hb)

theorem Env.ofModuleScc_empty_undeclared {ι : Type} {M : Module}
    (Γrec : ι → Env) (Γext : Env) {f : Sym} (hf : f ∉ M.names) (as bs : List Ty)
    (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    ¬ Env.ofModuleScc M Γrec Γext f as bs xs m Q X := by
  rintro (⟨hsig, _⟩ | ⟨hsig, _⟩)
  · exact hf (sigs_map_fst M ▸ List.mem_map.mpr ⟨(f, as, bs), mem_fns_sig_mem_sigs hsig, rfl⟩)
  · exact hf (sigs_map_fst M ▸
      List.mem_map.mpr ⟨(f, as, bs), mem_externs_sig_mem_sigs hsig, rfl⟩)

theorem Env.stepIdx_le_ofModuleScc {ι : Type} {idx : RecIdx ι} {M : Module}
    {Γrec : ι → Env} {Γext : Env} {strict : Bool} {i : ι}
    {f : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.stepIdx idx (M.fns.map Fn.sig) (M.externs.map Extern.sig) Γrec Γext strict i
      f as bs xs m Q X) :
    Env.ofModuleScc M Γrec Γext f as bs xs m Q X := by
  rcases h with ⟨hsig, i', _, _, hΓ⟩ | ⟨hsig, hΓ⟩
  · exact Or.inl ⟨hsig, i', hΓ⟩
  · exact Or.inr ⟨hsig, hΓ⟩

/-- Every index-`i` spec in a `ModuleSccOk` module satisfies `Func.wp` under the closed
environment `Env.ofModuleScc M Γrec Γext`. -/
theorem Env.sound_scc_at {ι : Type} {idx : RecIdx ι} {Γrec : ι → Env} {Γext : Env}
    {strict : Bool} {M : Module} (hM : ModuleSccOk idx Γrec Γext strict M) :
    ∀ (i : ι) (fn : Fn), fn ∈ M.fns → ∀ xs m Q X,
      Γrec i fn.name fn.as fn.rs xs m Q X →
      Func.wp (Env.ofModuleScc M Γrec Γext) fn.body xs m Q X := by
  intro i fn hfn xs m Q X hspec
  have ⟨_, _, hstep⟩ := hM.fnsOk fn hfn
  exact wp_env_mono (fun _ _ _ _ _ _ _ hg => Env.stepIdx_le_ofModuleScc hg) _ m
    (hstep i xs m Q X hspec)

/-- Closed environment satisfaction for `Env.ofModuleScc M Γrec Γext`. -/
theorem Env.sound_scc {ι : Type} {idx : RecIdx ι} {Γrec : ι → Env} {Γext : Env}
    {strict : Bool} {M : Module} (hM : ModuleSccOk idx Γrec Γext strict M) :
    ∀ (fn : Fn), fn ∈ M.fns → ∀ xs m Q X,
      Env.ofModuleScc M Γrec Γext fn.name fn.as fn.rs xs m Q X →
      Func.wp (Env.ofModuleScc M Γrec Γext) fn.body xs m Q X := by
  intro fn hfn xs m Q X hspec
  rcases hspec with ⟨_, i, hΓ⟩ | ⟨hsig, _⟩
  · exact Env.sound_scc_at hM i fn hfn xs m Q X hΓ
  · exact absurd hsig (fn_name_not_mem_externs hM.nodup hfn)

/-- Construct `ModuleSccOk` from `checkCyclic M = true`, per-function `Wf`, and polymorphic-`Γ`
step specs. -/
theorem moduleSccOk_of_step {ι : Type} (idx : RecIdx ι) {Γrec : ι → Env} {Γext : Env}
    {strict : Bool} {M : Module} (hchk : checkCyclic M = true) (hwf : ∀ fn ∈ M.fns, fn.Wf)
    (hstep : ∀ i : ι, ∀ fn ∈ M.fns, ∀ (Γ : Env),
      (∀ g ∈ M.fns, ∀ i', idx.lt i' i → (strict = false ∨ idx.depth i' < idx.depth i) →
        ∀ xs m Q X, Γrec i' g.name g.as g.rs xs m Q X → Γ g.name g.as g.rs xs m Q X) →
      (∀ ex ∈ M.externs, ∀ xs m Q X,
        Γext ex.name ex.as ex.rs xs m Q X → Γ ex.name ex.as ex.rs xs m Q X) →
      ∀ xs m Q X, Γrec i fn.name fn.as fn.rs xs m Q X → Func.wp Γ fn.body xs m Q X) :
    ModuleSccOk idx Γrec Γext strict M := by
  obtain ⟨hnd, hok⟩ := callsOkRec_of_checkCyclic hchk hwf
  refine ⟨hnd, fun fn hfn => ?_⟩
  obtain ⟨hfwf, hfc⟩ := hok fn hfn
  refine ⟨hfwf, hfc, fun i xs m Q X hspec => ?_⟩
  refine hstep i fn hfn _ (fun g hg i' hlt hst xs' m' Q' X' hΓ => ?_)
    (fun ex hex xs' m' Q' X' hΓ => ?_) xs m Q X hspec
  · exact Or.inl ⟨List.mem_map_of_mem hg, i', hlt, hst, hΓ⟩
  · exact Or.inr ⟨List.mem_map_of_mem hex, hΓ⟩

private theorem spec_cast_wrap {as₁ as₂ bs₁ bs₂ : List Ty}
    (ha : as₁ = as₂) (hb : bs₁ = bs₂) {Γ : Env} {f : Sym}
    {xs : Tup Val as₁} {m : Mem 64} {Q : Post bs₁} {X : XPost}
    (h : Γ f as₂ bs₂ (ha ▸ xs) m (hb ▸ Q) X) : Γ f as₁ bs₁ xs m Q X := by
  subst ha; subst hb; exact h

private theorem envOfIdxSpec_intro {ι : Type} {as bs : List Ty} {P : Sym → ι → Spec as bs}
    {i : ι} {g : Fn} (hga : g.as = as) (hgb : g.rs = bs)
    {xs' : Tup Val as} {m' : Mem 64} {Q' : Post bs} {X' : XPost}
    (hp : P g.name i xs' m' Q' X') :
    envOfIdxSpec P i g.name g.as g.rs (hga.symm ▸ xs') m' (hgb.symm ▸ Q') X' := by
  refine ⟨hga, hgb, ?_⟩
  subst hga; subst hgb; exact hp

/-- Convenience `Env.sound_scc` wrapper for a single-signature spec family
`P : Sym → ι → Spec as bs`. -/
theorem Env.sound_scc_idx {ι : Type} (idx : RecIdx ι) {as bs : List Ty}
    (P : Sym → ι → Spec as bs) (Γext : Env) {strict : Bool} {M : Module}
    (hchk : checkCyclic M = true) (hwf : ∀ fn ∈ M.fns, fn.Wf)
    (hsig : ∀ fn ∈ M.fns, fn.as = as ∧ fn.rs = bs)
    (hstep : ∀ i : ι, ∀ fn ∈ M.fns, ∀ (ha : fn.as = as) (hb : fn.rs = bs) (Γ : Env),
      (∀ g ∈ M.fns, ∀ i', idx.lt i' i → (strict = false ∨ idx.depth i' < idx.depth i) →
        ∀ xs m Q X, P g.name i' xs m Q X → Γ g.name as bs xs m Q X) →
      (∀ ex ∈ M.externs, ∀ xs m Q X,
        Γext ex.name ex.as ex.rs xs m Q X → Γ ex.name ex.as ex.rs xs m Q X) →
      ∀ xs m Q X, P fn.name i xs m Q X →
        Func.wp Γ fn.body (ha ▸ xs) m (hb ▸ Q) X) :
    ∀ fn ∈ M.fns, ∀ xs m Q X,
      Env.ofModuleScc M (envOfIdxSpec P) Γext fn.name fn.as fn.rs xs m Q X →
      Func.wp (Env.ofModuleScc M (envOfIdxSpec P) Γext) fn.body xs m Q X := by
  have hM : ModuleSccOk idx (envOfIdxSpec P) Γext strict M := by
    refine moduleSccOk_of_step idx hchk hwf fun i fn hfn Γ hrec hext xs m Q X hspec => ?_
    rcases hspec with ⟨ha, hb, hp⟩
    have h1 := hstep i fn hfn ha hb Γ (fun g hg i' hlt hst xs' m' Q' X' gp => by
      obtain ⟨hga, hgb⟩ := hsig g hg
      have h2 := hrec g hg i' hlt hst (hga.symm ▸ xs') m' (hgb.symm ▸ Q') X'
        (envOfIdxSpec_intro hga hgb gp)
      exact spec_cast_wrap hga.symm hgb.symm h2) hext (ha ▸ xs) m (hb ▸ Q) X hp
    clear hp
    subst ha; subst hb; exact h1
  exact Env.sound_scc hM

/-! ## 2. Core Well-Founded Machine Linking (`compileScc_sound`) -/

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
                    (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0))
                    f.as.length 0 0 st0 none with
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

private theorem infix_trans {α : Type} {a b c : List α} {k₁ k₂ : Nat}
    (hk1 : k₁ ≤ b.length) (h1 : a.IsInfixAt b k₁) (h2 : b.IsInfixAt c k₂) :
    a.IsInfixAt c (k₂ + k₁) := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  refine ⟨t1 ++ t2, ?_⟩
  have hd : (b ++ t2).drop k₁ = b.drop k₁ ++ t2 := by
    rw [List.drop_append, show k₁ - b.length = 0 by omega, List.drop_zero]
  rw [← List.drop_drop, ← ht2, hd, ← ht1, List.append_assoc]

/-- Every function `f ∈ fs` lowered by `compileModuleRecAux` is `T.Defined` in any host
containing `code` at `k₀` (independent of `ι`). -/
theorem defined_of_compileModuleRecAux {T : Target} {host : T.mach.Host} {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym}
    {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {code : List T.Directive} {baseBound stepBound k₀ : Nat}
    (haux : compileModuleRecAux T.toIsa lt T.frame.raBytes recSigs extCallees exits nX
      fs hints = .ok (code, baseBound, stepBound))
    (hc : code.IsInfixAt (T.mach.prog host) k₀)
    {f : Fn} (hf : f ∈ fs) : T.Defined host f.name := by
  obtain ⟨_, _, k_f, _, _, hl, hinf, hklen, _⟩ := compileModuleRecAux_mem haux f hf
  exact defined_of_lowerFn (f := f.mid lt) hl (infix_trans hklen hinf hc)

private theorem fnSpec_of_spec_scc {T : Target} {h : T.mach.Host} {sym : Sym} {as bs : List Ty}
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

private theorem compileFn_stepIdx_mid {ι : Type} {idx : RecIdx ι} {lt : LegalTarget} {f : Fn}
    (hwf : f.Wf) (hsupp : (f.earlyOpt).body.supportsSource lt = true)
    (recSigs extSigs : List SigEntry) (Γrec : ι → Env) (Γext : Env) (strict : Bool) (i : ι)
    (hsound : ∀ xs m P E', Γrec i f.name f.as f.rs xs m P E' →
      Func.wp (Env.stepIdx idx recSigs extSigs Γrec Γext strict i) f.body xs m P E') :
    ∀ xs' m Q' X',
      legalEnv lt (Env.onlyFn f (Γrec i)) f.name (lt.legalSig f.as) (lt.legalSig f.rs)
        xs' m Q' X' →
      Func.spec (legalEnv lt (Env.stepIdx idx recSigs extSigs Γrec Γext strict i))
        (f.mid lt).body xs' m Q' X' := by
  intro xs' m Q' X' h
  have hel := legalEnv_onlyFn_elim (Γrec i) h
  exact @fn_mid_spec lt f hwf hsupp (Env.stepIdx idx recSigs extSigs Γrec Γext strict i)
    hel.choose xs' hel.choose_spec.choose_spec.choose_spec.1 m
    hel.choose_spec.choose hel.choose_spec.choose_spec.choose Q' X'
    hel.choose_spec.choose_spec.choose_spec.2.1
    hel.choose_spec.choose_spec.choose_spec.2.2.1
    (hsound _ m _ _ hel.choose_spec.choose_spec.choose_spec.2.2.2)

private theorem compileFn_correct_stepIdx {ι : Type} (idx : RecIdx ι) (T : Target)
    (host : T.mach.Host) (lt : LegalTarget) (hints : T.toIsa.Hints) (E : Rega.Ext) (f : Fn)
    (recSigs extSigs : List SigEntry) (Γrec : ι → Env) (Γext : Env) (strict : Bool) (i : ι)
    (n nX : Nat) (bound : Sym → Nat) {code : List T.Directive} {k₀ : Nat}
    (hwf : f.Wf) (hsupp : (f.earlyOpt).body.supportsSource lt = true)
    (hl : Rega.lowerFn T.toIsa hints E (f.mid lt) = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hfr : Rega.frame T hints ≤ n) (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hsound : ∀ xs m P E', Γrec i f.name f.as f.rs xs m P E' →
      Func.wp (Env.stepIdx idx recSigs extSigs Γrec Γext strict i) f.body xs m P E')
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      T.FnSpec host g
        (legalEnv lt (Env.stepIdx idx recSigs extSigs Γrec Γext strict i) g as bs) (bound g) nX ∧
      Rega.frame T hints + T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → T.Defined host g ∧ nX ≤ n) :
    T.FnSpec host f.name
      (legalEnv lt (Env.onlyFn f (Γrec i)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      n nX :=
  fnSpec_of_spec_scc
    (compileFn_stepIdx_mid hwf hsupp recSigs extSigs Γrec Γext strict i hsound)
    (Rega.lowerFn_correct T host hints E (f.mid lt)
      (legalEnv lt (Env.stepIdx idx recSigs extSigs Γrec Γext strict i)) n nX bound
      (fn_mid_wf hwf) hl hc hu (Nat.le_trans (Rega.effFrame_le T.toIsa hints E) hfr) hn
      (fun g as bs hg =>
        let ⟨h1, h2⟩ := hcal g as bs hg
        ⟨h1, Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right
          (Rega.effFrame_le T.toIsa hints E) _) _) h2⟩)
      hex)

private theorem legalEnv_stepIdx_zero_empty {ι : Type} {idx : RecIdx ι} {lt : LegalTarget}
    {mod : Module} (hnd : mod.namesNodup) {Γrec : ι → Env} {Γext : Env} {i : ι}
    (hdep : idx.depth i = 0) {g : Sym} (hg : g ∈ mod.fns.map Fn.name) {as bs : List Ty}
    {xs' : Tup Val as} {m : Mem 64} {Q' : Post bs} {X' : XPost} :
    ¬ legalEnv lt
      (Env.stepIdx idx (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext true i)
      g as bs xs' m Q' X' := by
  rintro ⟨as₀, bs₀, _, _, xs₀, P₀, E₀, _, _, _, hstep⟩
  rcases hstep with ⟨_, i', _, hlt, _⟩ | ⟨hsig, _⟩
  · rcases hlt with h | h
    · cases h
    · omega
  · obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp hg
    exact fn_name_not_mem_externs hnd hfn hsig

private theorem legalEnv_stepIdx_rec_mem {ι : Type} {idx : RecIdx ι} {lt : LegalTarget}
    {mod : Module} (hnd : mod.namesNodup) {Γrec : ι → Env} {Γext : Env} {strict : Bool} {i : ι}
    {gfn : Fn} (hgfn : gfn ∈ mod.fns)
    {xs' : Tup Val (lt.legalSig gfn.as)} {m0 : Mem 64}
    {Q' : Post (lt.legalSig gfn.rs)} {X' : XPost}
    (h : legalEnv lt
      (Env.stepIdx idx (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext strict i)
      gfn.name (lt.legalSig gfn.as) (lt.legalSig gfn.rs) xs' m0 Q' X') :
    ∃ i', idx.lt i' i ∧ (strict = false ∨ idx.depth i' < idx.depth i) ∧
      legalEnv lt (Env.onlyFn gfn (Γrec i')) gfn.name
        (lt.legalSig gfn.as) (lt.legalSig gfn.rs) xs' m0 Q' X' := by
  rcases h with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hstep⟩
  rcases hstep with ⟨hsig, i', hlt, hst, hΓ⟩ | ⟨hsig, _⟩
  · have hfnsNd : (mod.fns.map Fn.name).Nodup := (List.nodup_append.mp hnd).1
    have hmapFst : (mod.fns.map Fn.sig).map Prod.fst = mod.fns.map Fn.name := by
      simp [List.map_map, Function.comp_def, Fn.sig]
    obtain ⟨ha, hb⟩ := mem_unique_fst (hmapFst ▸ hfnsNd) hsig (List.mem_map_of_mem hgfn)
    subst ha; subst hb
    exact ⟨i', hlt, hst, gfn.as, gfn.rs, has₀, hbs₀, xs₀, P₀, E₀,
      hxs₀, hQ₀, hX₀, rfl, rfl, rfl, hΓ⟩
  · exact absurd hsig (fn_name_not_mem_externs hnd hgfn)

private theorem legalEnv_stepIdx_ext {ι : Type} {idx : RecIdx ι} {lt : LegalTarget}
    {mod : Module} {Γrec : ι → Env} {Γext : Env} {strict : Bool} {i : ι}
    {g : Sym} (hg : g ∉ mod.fns.map Fn.name)
    {as bs : List Ty} {xs' : Tup Val as} {m0 : Mem 64} {Q' : Post bs} {X' : XPost}
    (h : legalEnv lt
      (Env.stepIdx idx (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext strict i)
      g as bs xs' m0 Q' X') :
    legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) g as bs xs' m0 Q' X' := by
  rcases h with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hstep⟩
  rcases hstep with ⟨hsig, _⟩ | ⟨hsig, hΓ⟩
  · obtain ⟨fn, hfn, hfeq⟩ := List.mem_map.mp hsig
    have hnm : fn.name = g := congrArg Prod.fst hfeq
    exact absurd (hnm ▸ List.mem_map_of_mem hfn) hg
  · exact ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hsig, hΓ⟩

private def sccCallBound (mod : Module) (extCallees : List (SigEntry × Nat))
    (baseBound stepBound depth : Nat) (g : Sym) : Nat :=
  if (mod.fns.map Fn.name).contains g then
    if stepBound == 0 then baseBound
    else match depth with
      | 0 => 0
      | d + 1 => baseBound + d * stepBound
  else
    match extCallees.find? (fun q => q.1.1 == g) with
    | some q => q.2
    | none => 0

/-- Core well-founded induction soundness theorem for `compileModuleRecAux` over `RecIdx ι`:
for any index `i : ι` whose stack budget fits (`baseBound + idx.depth i * stepBound ≤ maxBound`
and `+ T.frame.raBytes ≤ 2 ^ 64`), every `f ∈ mod.fns` is `T.Defined` and satisfies `T.FnSpec` at
`baseBound + idx.depth i * stepBound`. -/
theorem compileScc_sound {ι : Type} (idx : RecIdx ι) (T : Target) (host : T.mach.Host)
    (lt : LegalTarget) (mod : Module) (Γrec : ι → Env) (Γext : Env)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (hints : List T.toIsa.Hints) (code : List T.Directive)
    (baseBound stepBound k₀ maxBound : Nat)
    (haux : compileModuleRecAux T.toIsa lt T.frame.raBytes
      (mod.fns.map (fun f => (f.name, lt.legalSig f.as, lt.legalSig f.rs)))
      extCallees exits nX mod.fns hints = .ok (code, baseBound, stepBound))
    (hdisj : ∀ p ∈ extCallees, p.1.1 ∉ mod.fns.map Fn.name)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hM : ModuleSccOk idx Γrec Γext (stepBound != 0) mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec host p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined host g) :
    ∀ (i : ι),
      baseBound + idx.depth i * stepBound ≤ maxBound →
      baseBound + idx.depth i * stepBound + T.frame.raBytes ≤ 2 ^ 64 →
      ∀ f ∈ mod.fns, T.Defined host f.name ∧
        T.FnSpec host f.name
          (legalEnv lt (Env.onlyFn f (Γrec i)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
          (baseBound + idx.depth i * stepBound) nX := by
  intro i
  induction i using (WellFounded.induction idx.wf) with
  | h i ih =>
    intro hmax hra f hf
    obtain ⟨hint, c, k_f, bf, sf, hl, hinf, hklen, hchk, hbf, hsf⟩ :=
      compileModuleRecAux_mem haux f hf
    have hc_f : c.IsInfixAt (T.mach.prog host) (k₀ + k_f) := infix_trans hklen hinf hc
    have hfdef : T.Defined host f.name := defined_of_lowerFn (f := f.mid lt) hl hc_f
    obtain ⟨hsf_eq, hfr_b, hcal_b, hex_b⟩ := checkAndBoundRecExt_spec hchk
    have hfr : Rega.frame T hint ≤ baseBound + idx.depth i * stepBound :=
      Nat.le_trans hfr_b (Nat.le_trans hbf (Nat.le_add_right _ _))
    let bound : Sym → Nat := sccCallBound mod extCallees baseBound stepBound (idx.depth i)
    have hcal : ∀ g as bs, (g, as, bs) ∈ (f.mid lt).ext.callees →
        T.FnSpec host g
          (legalEnv lt (Env.stepIdx idx (mod.fns.map Fn.sig) (mod.externs.map Extern.sig)
            Γrec Γext (stepBound != 0) i) g as bs)
          (bound g) nX ∧
        Rega.frame T hint + T.frame.raBytes + bound g ≤ baseBound + idx.depth i * stepBound := by
      intro g as bs hg
      rcases hcal_b (g, as, bs) hg with ⟨hrec_sig, hstep_b⟩ | ⟨_, bg, hlk, hbg_b⟩
      · obtain ⟨gfn, hgfn, hgeq⟩ := List.mem_map.mp hrec_sig
        rcases Prod.mk.inj hgeq with ⟨rfl, hsig_ab⟩
        rcases Prod.mk.inj hsig_ab with ⟨rfl, rfl⟩
        have hmem_nm : gfn.name ∈ mod.fns.map Fn.name := List.mem_map_of_mem hgfn
        have hcon : (mod.fns.map Fn.name).contains gfn.name = true := by simpa using hmem_nm
        by_cases hsz : stepBound = 0
        · have hstrict : (stepBound != 0) = false := by simp [hsz]
          have hbd : bound gfn.name = baseBound := by
            dsimp only [bound, sccCallBound]
            rw [hcon]
            simp [hsz]
          rw [hbd]
          refine ⟨?_, ?_⟩
          · intro args m0 Q X hleg s ra R hargs hra0 hspE hmem
            rw [hstrict] at hleg
            obtain ⟨i', hlt', _, hleg'⟩ := legalEnv_stepIdx_rec_mem hM.nodup hgfn hleg
            have hmax' : baseBound + idx.depth i' * stepBound ≤ maxBound := by
              simpa [hsz] using hmax
            have hra' : baseBound + idx.depth i' * stepBound + T.frame.raBytes ≤ 2 ^ 64 := by
              simpa [hsz] using hra
            have hih := (ih i' hlt' hmax' hra' gfn hgfn).2
            simp only [hsz, Nat.mul_zero, Nat.add_zero] at hih
            exact hih args m0 Q X hleg' s ra R hargs hra0 hspE hmem
          · have hfr_sf : Rega.frame T hint + T.frame.raBytes ≤ stepBound := by
              rw [← hsf_eq]; exact hsf
            rw [hsz] at hfr_sf ⊢
            omega
        · have hstrict : (stepBound != 0) = true := by simp [hsz]
          have hbeq : (stepBound == 0) = false := beq_false_of_ne hsz
          cases hdep : idx.depth i with
          | zero =>
              refine ⟨?_, ?_⟩
              · intro args m0 Q X hleg
                rw [hstrict] at hleg
                exact absurd hleg (legalEnv_stepIdx_zero_empty hM.nodup hdep hmem_nm)
              · simp only [bound, sccCallBound, hcon, ↓reduceIte, hbeq, hdep,
                  Nat.zero_mul, Nat.add_zero]
                exact Nat.le_trans hstep_b hbf
          | succ d =>
              have hbd : bound gfn.name = baseBound + d * stepBound := by
                dsimp only [bound, sccCallBound]
                rw [hcon]
                simp [hbeq, hdep]
              rw [hbd]
              refine ⟨?_, ?_⟩
              · intro args m0 Q X hleg s ra R hargs hra0 hspE hmem
                rw [hstrict] at hleg
                obtain ⟨i', hlt', hst', hleg'⟩ := legalEnv_stepIdx_rec_mem hM.nodup hgfn hleg
                have hlt_d : idx.depth i' ≤ d := by
                  rcases hst' with hfalse | hlt_dep
                  · cases hfalse
                  · rw [hdep] at hlt_dep; exact Nat.lt_succ_iff.mp hlt_dep
                have hmle : baseBound + idx.depth i' * stepBound ≤ baseBound + d * stepBound :=
                  Nat.add_le_add_left (Nat.mul_le_mul_right stepBound hlt_d) baseBound
                have hmle_i : baseBound + d * stepBound ≤ baseBound + idx.depth i * stepBound := by
                  rw [hdep]
                  exact Nat.add_le_add_left
                    (Nat.mul_le_mul_right stepBound (Nat.le_succ d)) baseBound
                have hmax' : baseBound + idx.depth i' * stepBound ≤ maxBound :=
                  Nat.le_trans hmle (Nat.le_trans hmle_i hmax)
                have hbra : (baseBound + d * stepBound) + T.frame.raBytes ≤ 2 ^ 64 := by omega
                have hra' : baseBound + idx.depth i' * stepBound + T.frame.raBytes ≤ 2 ^ 64 := by
                  omega
                have hih := (ih i' hlt' hmax' hra' gfn hgfn).2
                exact (Target.FnSpec.mono_stack T hih hmle hbra)
                  args m0 Q X hleg' s ra R hargs hra0 hspE hmem
              · have hfr_sf : Rega.frame T hint + T.frame.raBytes ≤ stepBound := by
                  rw [← hsf_eq]; exact hsf
                rw [Nat.succ_mul]
                omega
      · have hmem_ext : ((g, as, bs), bg) ∈ extCallees := lookupBound_mem hlk
        have hnot_nm : g ∉ mod.fns.map Fn.name := hdisj ((g, as, bs), bg) hmem_ext
        have hcon : (mod.fns.map Fn.name).contains g = false := by
          simpa [List.contains_eq_mem] using hnot_nm
        have hbd : bound g = bg := by
          dsimp only [bound, sccCallBound]; rw [hcon]
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
          fun args m0 Q X hleg => legalEnv_stepIdx_ext hnot_nm hleg
    have hex : ∀ g, g ∈ (f.mid lt).ext.exits →
        T.Defined host g ∧ nX ≤ baseBound + idx.depth i * stepBound :=
      fun g hg => ⟨hexits g (hex_b g hg).1,
        Nat.le_trans (hex_b g hg).2 (Nat.le_trans hbf (Nat.le_add_right _ _))⟩
    have ⟨hfwf, _, hfwp⟩ := hM.fnsOk f hf
    exact ⟨hfdef, compileFn_correct_stepIdx idx T host lt hint (f.mid lt).ext f
      (mod.fns.map Fn.sig) (mod.externs.map Extern.sig) Γrec Γext (stepBound != 0) i
      (baseBound + idx.depth i * stepBound) nX bound hfwf (hsupp f hf) hl hc_f hu
      hfr hra (hfwp i) hcal hex⟩

end LeanQbe.T.LinkScc
