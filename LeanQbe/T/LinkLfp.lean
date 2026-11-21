module

public import LeanQbe.T.LinkSccLemmas2

/-!
# Knaster–Tarski `Env.lfp`, Kleene Approximants, and `link_scc_static` (`R-B` / `Lfp` Follow-Up)

Purely additive semantic fixed-point layer complementing `LinkScc`:
* **Impredicative `Env.lfp`:** `Env.le`, `Env.mono`, `Env.lfp`, `Env.lfp_le`, `Env.lfp_pre`,
  `Env.lfp_post`, `Env.lfp_fix`, and `Env.lfp_wf` (well-founded `(ι, ≺)` introduction).
* **Module operator & reductions:** `Env.sccStep`, `Env.sccOp`, `sccOp_mono`, `Env.semScc`,
  `moduleSccOk_le_semScc` (`strict = false`), and `moduleSccOk_le_unfoldRecAt` (`strict = true`).
* **Static Kleene linking (`link_scc_static`):** proves `T.FnSpec` for `Env.unfoldRecAt mod Γext d`
  at stack bound `base + d * step` by instantiating `LinkRec.link_rec_compiled` (zero new
  induction over compiler internals), plus `link_scc_static_host` and `link_scc_static_of_scc`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

open LeanQbe.T.LinkRec
open LeanQbe.T.LinkScc

/-! ## 1. Pointwise Ordering and Knaster–Tarski `Env.lfp` -/

/-- Pointwise implication ordering on symbol environments. -/
def Env.le (Γ₁ Γ₂ : Env) : Prop :=
  ∀ f as bs xs m Q X, Γ₁ f as bs xs m Q X → Γ₂ f as bs xs m Q X

theorem Env.le_refl (Γ : Env) : Env.le Γ Γ :=
  fun _ _ _ _ _ _ _ h => h

theorem Env.le_trans {Γ₁ Γ₂ Γ₃ : Env} (h₁ : Env.le Γ₁ Γ₂) (h₂ : Env.le Γ₂ Γ₃) :
    Env.le Γ₁ Γ₃ :=
  fun f as bs xs m Q X h => h₂ f as bs xs m Q X (h₁ f as bs xs m Q X h)

/-- Monotonicity of an environment transformer with respect to `Env.le`. -/
def Env.mono (Φ : Env → Env) : Prop :=
  ∀ ⦃Γ₁ Γ₂ : Env⦄, Env.le Γ₁ Γ₂ → Env.le (Φ Γ₁) (Φ Γ₂)

/-- Impredicative Knaster–Tarski least fixed point of `Φ : Env → Env`. -/
def Env.lfp (Φ : Env → Env) : Env :=
  fun f as bs xs m Q X =>
    ∀ Γ : Env, Env.le (Φ Γ) Γ → Γ f as bs xs m Q X

/-- Elimination: `Env.lfp Φ` lies below every pre-fixpoint `G` (`Φ G ≤ G`). -/
theorem Env.lfp_le {Φ : Env → Env} {G : Env} (h : Env.le (Φ G) G) :
    Env.le (Env.lfp Φ) G :=
  fun _ _ _ _ _ _ _ hlfp => hlfp G h

/-- Pre-fixpoint property: when `Φ` is monotone, `Φ (Env.lfp Φ) ≤ Env.lfp Φ`. -/
theorem Env.lfp_pre {Φ : Env → Env} (hm : Env.mono Φ) :
    Env.le (Φ (Env.lfp Φ)) (Env.lfp Φ) := by
  intro f as bs xs m Q X hΦ Γ hΓ
  exact hΓ f as bs xs m Q X (hm (Env.lfp_le hΓ) f as bs xs m Q X hΦ)

/-- Post-fixpoint property: when `Φ` is monotone, `Env.lfp Φ ≤ Φ (Env.lfp Φ)`. -/
theorem Env.lfp_post {Φ : Env → Env} (hm : Env.mono Φ) :
    Env.le (Env.lfp Φ) (Φ (Env.lfp Φ)) :=
  Env.lfp_le (hm (Env.lfp_pre hm))

/-- Fixed-point equation `Env.lfp Φ = Φ (Env.lfp Φ)` for monotone `Φ`. -/
theorem Env.lfp_fix {Φ : Env → Env} (hm : Env.mono Φ) :
    Env.lfp Φ = Φ (Env.lfp Φ) := by
  funext f as bs xs m Q X
  exact propext
    ⟨fun h => Env.lfp_post hm f as bs xs m Q X h,
     fun h => Env.lfp_pre hm f as bs xs m Q X h⟩

/-- Indexed supremum strictly below `i` along relation `lt`. -/
def Env.supBelow {ι : Type} (lt : ι → ι → Prop) (S : ι → Env) (i : ι) : Env :=
  fun f as bs xs m Q X => ∃ j, lt j i ∧ S j f as bs xs m Q X

/-- Well-founded `(ι, lt)` introduction into `Env.lfp Φ`. -/
theorem Env.lfp_wf {ι : Type} {lt : ι → ι → Prop} (hwf : WellFounded lt)
    {Φ : Env → Env} (hm : Env.mono Φ) (S : ι → Env)
    (hstep : ∀ i, Env.le (S i) (Φ (Env.supBelow lt S i))) :
    ∀ i, Env.le (S i) (Env.lfp Φ) := by
  intro i
  induction i using (WellFounded.induction hwf) with
  | h i ih =>
      have hsup : Env.le (Env.supBelow lt S i) (Env.lfp Φ) := by
        rintro f as bs xs m Q X ⟨j, hlt, hj⟩
        exact ih j hlt f as bs xs m Q X hj
      exact Env.le_trans (hstep i) (Env.le_trans (hm hsup) (Env.lfp_pre hm))

/-! ## 2. Module Operator `Env.sccOp`, `Env.semScc`, and `ModuleSccOk` Reductions -/

/-- One-step callee environment offered inside `Env.sccOp`: module functions in `M.fns` take
contracts from `Γ`, and declared externs in `M.externs` take contracts from `Γext`. -/
def Env.sccStep (M : Module) (Γ Γext : Env) : Env :=
  fun f as bs xs m Q X =>
    ((f, as, bs) ∈ M.fns.map Fn.sig ∧ Γ f as bs xs m Q X) ∨
    ((f, as, bs) ∈ M.externs.map Extern.sig ∧ Γext f as bs xs m Q X)

/-- One-step semantic operator for module `M` over external environment `Γext`, matching the
successor arm of `Env.unfoldRecBelow`. -/
def Env.sccOp (M : Module) (Γext : Env) (Γ : Env) : Env :=
  fun f as bs xs m Q X =>
    (f, as, bs) ∈ M.fns.map Fn.sig ∧ ∃ fn ∈ M.fns, fn.name = f ∧
      ∃ (ha : fn.as = as) (hr : fn.rs = bs),
        Func.wp (Env.sccStep M Γ Γext) fn.body (ha ▸ xs) m (hr ▸ Q) X

/-- Monotonicity of `Env.sccOp M Γext` in `Γ` (via `wp_env_mono`). -/
theorem sccOp_mono (M : Module) (Γext : Env) : Env.mono (Env.sccOp M Γext) := by
  rintro Γ₁ Γ₂ hle f as bs xs m Q X ⟨hsig, fn, hfn, hnm, ha, hr, hwp⟩
  refine ⟨hsig, fn, hfn, hnm, ha, hr, wp_env_mono (fun g as' bs' xs' m' Q' X' hg => ?_) _ m hwp⟩
  rcases hg with ⟨hfns, hΓ⟩ | ⟨hext, hΓ⟩
  · exact Or.inl ⟨hfns, hle g as' bs' xs' m' Q' X' hΓ⟩
  · exact Or.inr ⟨hext, hΓ⟩

/-- Canonical least-fixed-point semantics of module `M` over external environment `Γext`. -/
def Env.semScc (M : Module) (Γext : Env) : Env :=
  Env.lfp (Env.sccOp M Γext)

/-- Loose (`strict = false`) `ModuleSccOk` embeds into `Env.semScc M Γext` via `Env.lfp_wf`. -/
theorem moduleSccOk_le_semScc {ι : Type} {idx : RecIdx ι} {Γrec : ι → Env} {Γext : Env}
    {M : Module} (hM : ModuleSccOk idx Γrec Γext false M) :
    ∀ i, Env.le (Env.restrict (Γrec i) (M.fns.map Fn.sig)) (Env.semScc M Γext) := by
  let S : ι → Env := fun i => Env.restrict (Γrec i) (M.fns.map Fn.sig)
  refine Env.lfp_wf idx.wf (sccOp_mono M Γext) S fun i f as bs xs m Q X hS => ?_
  rcases hS with ⟨hsig, hΓ⟩
  obtain ⟨fn, hfn, hfeq⟩ := List.mem_map.mp hsig
  rcases Prod.mk.inj hfeq with ⟨rfl, hsig_ab⟩
  rcases Prod.mk.inj hsig_ab with ⟨rfl, rfl⟩
  have hwp := (hM.fnsOk fn hfn).2.2 i xs m Q X hΓ
  refine ⟨hsig, fn, hfn, rfl, rfl, rfl, wp_env_mono (fun g as' bs' xs' m' Q' X' hg => ?_) _ m hwp⟩
  rcases hg with ⟨hfns, j, hlt, _, hΓ'⟩ | ⟨hext, hΓ'⟩
  · exact Or.inl ⟨hfns, j, hlt, hfns, hΓ'⟩
  · exact Or.inr ⟨hext, hΓ'⟩

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

/-- Strict (`strict = true`) `ModuleSccOk` embeds into `Env.unfoldRecAt M Γext (idx.depth i)` by
strong induction on `idx.depth i`. -/
theorem moduleSccOk_le_unfoldRecAt {ι : Type} {idx : RecIdx ι} {Γrec : ι → Env} {Γext : Env}
    {M : Module} (hM : ModuleSccOk idx Γrec Γext true M) :
    ∀ i, Env.le (Env.restrict (Γrec i) (M.fns.map Fn.sig))
      (Env.unfoldRecAt M Γext (idx.depth i)) := by
  suffices h : ∀ d : Nat, ∀ i : ι, idx.depth i = d →
      Env.le (Env.restrict (Γrec i) (M.fns.map Fn.sig)) (Env.unfoldRecAt M Γext d) from
    fun i => h (idx.depth i) i rfl
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
      intro i hid f as bs xs m Q X hS
      rcases hS with ⟨hsig, hΓ⟩
      obtain ⟨fn, hfn, hfeq⟩ := List.mem_map.mp hsig
      rcases Prod.mk.inj hfeq with ⟨rfl, hsig_ab⟩
      rcases Prod.mk.inj hsig_ab with ⟨rfl, rfl⟩
      have hwp := (hM.fnsOk fn hfn).2.2 i xs m Q X hΓ
      refine Or.inr ⟨hsig, fn, hfn, rfl, rfl, rfl,
        wp_env_mono (fun g as' bs' xs' m' Q' X' hg => ?_) _ m hwp⟩
      rcases hg with ⟨hfns, j, _, hst, hΓ'⟩ | ⟨hext, hΓ'⟩
      · rcases hst with hfalse | hlt_dep
        · cases hfalse
        · rw [hid] at hlt_dep
          have hj := ih (idx.depth j) hlt_dep j rfl g as' bs' xs' m' Q' X' ⟨hfns, hΓ'⟩
          exact unfoldRecBelow_mono hlt_dep g as' bs' xs' m' Q' X' hj
      · exact unfoldRecBelow_mono (Nat.zero_le d) g as' bs' xs' m' Q' X' ⟨hext, hΓ'⟩

/-! ## 3. `link_scc_static` via `LinkRec.link_rec_compiled` -/

private theorem fn_name_not_mem_externs_lfp {M : Module} (hnd : M.namesNodup)
    {fn : Fn} (hfn : fn ∈ M.fns) {as bs : List Ty} :
    (fn.name, as, bs) ∉ M.externs.map Extern.sig := by
  intro hex
  have hdisj := (List.nodup_append.mp hnd).2.2
  have h1 : fn.name ∈ M.fns.map Fn.name := List.mem_map_of_mem hfn
  obtain ⟨ex, hexm, heq⟩ := List.mem_map.mp hex
  have h2 : ex.name ∈ M.externs.map Extern.name := List.mem_map_of_mem hexm
  exact hdisj fn.name h1 ex.name h2 (congrArg Prod.fst heq).symm

private theorem fn_eq_of_name_nodup : ∀ {fns : List Fn}, (fns.map Fn.name).Nodup →
    ∀ {f g : Fn}, f ∈ fns → g ∈ fns → f.name = g.name → f = g
  | [], _, _, _, hf, _, _ => nomatch hf
  | _ :: _, hnd, f, g, hf, hg, hnm => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      rcases List.mem_cons.mp hf with rfl | hf' <;> rcases List.mem_cons.mp hg with rfl | hg'
      · rfl
      · exact absurd hnm.symm (hnd.1 g hg')
      · exact absurd hnm (hnd.1 f hf')
      · exact fn_eq_of_name_nodup hnd.2 hf' hg' hnm

private theorem unfoldRecBelow_succ_to_stepRec (mod : Module) (Γext : Env) :
    ∀ {k : Nat} {g : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64}
      {Q : Post bs} {X : XPost},
      Env.unfoldRecBelow mod Γext k g as bs xs m Q X →
      Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig)
        (fun j => Env.unfoldRecBelow mod Γext (j + 1)) Γext k g as bs xs m Q X
  | 0, _, _, _, _, _, _, _, h => Or.inr h
  | k + 1, _, _, _, _, _, _, _, h => by
      rcases h with hprev | hcur
      · rcases unfoldRecBelow_succ_to_stepRec mod Γext hprev with
          ⟨hs, j, hlt, hj⟩ | ⟨hs, he⟩
        · exact Or.inl ⟨hs, j, Nat.lt_succ_of_lt hlt, hj⟩
        · exact Or.inr ⟨hs, he⟩
      · exact Or.inl ⟨hcur.1, k, Nat.lt_succ_self k, Or.inr hcur⟩

private theorem unfoldRecAt_wp_step (mod : Module) (hnd : mod.namesNodup) (Γext : Env) :
    ∀ k : Nat, ∀ f ∈ mod.fns, ∀ xs m Q X,
      Env.unfoldRecAt mod Γext k f.name f.as f.rs xs m Q X →
      Func.wp (Env.stepRec (mod.fns.map Fn.sig) (mod.externs.map Extern.sig)
        (fun j => Env.unfoldRecBelow mod Γext (j + 1)) Γext k) f.body xs m Q X
  | 0, f, hf, xs, m, Q, X, h => by
      rcases h with h0 | ⟨_, fn, hfn, hnm, ha, hr, hwp⟩
      · exact absurd h0.1 (fn_name_not_mem_externs_lfp hnd hf)
      · have hfnsNd : (mod.fns.map Fn.name).Nodup := (List.nodup_append.mp hnd).1
        obtain rfl := fn_eq_of_name_nodup hfnsNd hfn hf hnm
        exact wp_env_mono (fun _ _ _ _ _ _ _ hg => Or.inr hg) _ m hwp
  | k + 1, f, hf, xs, m, Q, X, h => by
      rcases h with hprev | ⟨_, fn, hfn, hnm, ha, hr, hwp⟩
      · have ih := unfoldRecAt_wp_step mod hnd Γext k f hf xs m Q X hprev
        refine wp_env_mono (fun _ _ _ _ _ _ _ hg => ?_) _ m ih
        rcases hg with ⟨hs, j, hj, hΓ⟩ | ⟨hs, hΓ⟩
        · exact Or.inl ⟨hs, j, Nat.lt_succ_of_lt hj, hΓ⟩
        · exact Or.inr ⟨hs, hΓ⟩
      · have hfnsNd : (mod.fns.map Fn.name).Nodup := (List.nodup_append.mp hnd).1
        obtain rfl := fn_eq_of_name_nodup hfnsNd hfn hf hnm
        exact wp_env_mono (fun _ _ _ _ _ _ _ hg =>
          unfoldRecBelow_succ_to_stepRec mod Γext hg) _ m hwp

/-- **`Lfp` static-bound linking theorem:** every compiled function `f ∈ mod.fns` satisfies
`T.FnSpec` for the `d`-step Kleene approximant `Env.unfoldRecAt mod Γext d` at stack bound
`M.baseBound + d * M.stepBound`, proved by instantiating `LinkRec.link_rec_compiled`. -/
theorem link_scc_static {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ d ≤ fuel, ∀ f ∈ mod.fns, T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.onlyFn f (Env.unfoldRecAt mod Γext d)) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + d * M.stepBound) nX := by
  have hnd := Module.namesNodup_of_checkNamesNodup ((Bool.and_eq_true _ _).mp hcyc).1
  exact link_rec_compiled M mod hfs h (fun k => Env.unfoldRecBelow mod Γext (k + 1)) Γext k₀
    hc hu hcyc hwf hsupp (fun k _ f hf => unfoldRecAt_wp_step mod hnd Γext k f hf)
    hext hext_uniq hexits

/-- Specialization of `link_scc_static` to `M.host` with `extCallees = []`. -/
theorem link_scc_static_host {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {maxBound : Nat}
    (M : CompiledRec T lt [] exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γext : Env)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ d ≤ fuel, ∀ f ∈ mod.fns, T.Defined M.host f.name ∧
      T.FnSpec M.host f.name
        (legalEnv lt (Env.onlyFn f (Env.unfoldRecAt mod Γext d)) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + d * M.stepBound) nX :=
  link_scc_static M mod hfs M.host Γext 0 M.code_infix_host M.labelsUnique hcyc hwf hsupp
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ hg => M.defined_exit_host hg)

/-- Derive `T.FnSpec` for a strict `ModuleSccOk` spec directly from `link_scc_static` +
`moduleSccOk_le_unfoldRecAt` (no `compileScc_sound` induction). -/
theorem link_scc_static_of_scc {ι : Type} {idx : RecIdx ι} {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γrec : ι → Env) (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hcyc : checkCyclic mod = true)
    (hM : ModuleSccOk idx Γrec Γext true mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g)
    {i : ι} (hi : idx.depth i ≤ fuel) {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.onlyFn f (Γrec i)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + idx.depth i * M.stepBound) nX := by
  obtain ⟨hdef, hspec⟩ := link_scc_static M mod hfs h Γext k₀ hc hu hcyc
    (fun g hg => (hM.fnsOk g hg).1) hsupp hext hext_uniq hexits (idx.depth i) hi f hf
  refine ⟨hdef, Target.FnSpec.of_spec T hspec fun args m Q X hleg => ?_⟩
  rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hnm, ha, hb, hΓ⟩
  subst ha; subst hb
  exact ⟨f.as, f.rs, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hnm, rfl, rfl,
    moduleSccOk_le_unfoldRecAt hM i f.name f.as f.rs xs₀ m P₀ E₀
      ⟨List.mem_map_of_mem hf, hΓ⟩⟩

end LeanQbe.T
