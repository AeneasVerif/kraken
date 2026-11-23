module

public import LeanQbe.T.LinkSccLemmas1
import LeanQbe.T.WPLemmas

/-!
# Soundness of `LeanQbe.T.LinkScc` — Part 2

Top-level `CompiledRec`-backed theorems:
* `link_scc_compiled` (+ `link_scc_compiled_le`, `_host`, `_src`, `_src_noExit`): well-founded
  SCC linking for any `i : ι` satisfying `M.baseBound + idx.depth i * M.stepBound ≤ maxBound`.
* `link_scc_export` (+ `_restrict`, `_host`, `_src`, `_src_noExit`): packages `Env.exportScc idx
  Γrec fuel` at uniform static stack bound `M.baseBound + fuel * M.stepBound` (`M.boundAt fuel`).
* `link_rec_of_scc`: recovers `LinkRec.link_rec_compiled` cleanly via `natRecIdx`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LinkScc

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.LinkRec

private theorem compileModuleRec_disjoint' {I : Isa} {lt : LegalTarget} {raBytes : Nat}
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

private theorem mem_unique_fst_sig : ∀ {xs : List SigEntry}, (xs.map Prod.fst).Nodup →
    ∀ {f as₁ bs₁ as₂ bs₂}, (f, as₁, bs₁) ∈ xs → (f, as₂, bs₂) ∈ xs → as₁ = as₂ ∧ bs₁ = bs₂
  | [], _, _, _, _, _, _, h, _ => nomatch h
  | (_, _, _) :: _, hnd, _, _, _, _, _, h1, h2 => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      rcases List.mem_cons.mp h1 with e1 | h1 <;> rcases List.mem_cons.mp h2 with e2 | h2
      · cases e1; cases e2; exact ⟨rfl, rfl⟩
      · cases e1; exact absurd rfl (hnd.1 _ h2)
      · cases e2; exact absurd rfl (hnd.1 _ h1)
      · exact mem_unique_fst_sig hnd.2 h1 h2

-- Extension point: `link_scc_compiled_split` will replace `ModuleSccOk` here with split call/tail
-- obligations, keeping `Env.exportScc` and `link_scc_export` unchanged for downstream SCCs.
/-- **Main SCC-linking theorem:** well-founded index-parameterized linking over any `CompiledRec`
certificate and compatible host `h`, for any `i : ι` whose stack budget fits within `maxBound`
and `2 ^ 64`. -/
theorem link_scc_compiled {ι : Type} (idx : RecIdx ι) {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γrec : ι → Env) (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleSccOk idx Γrec Γext (M.stepBound != 0) mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g)
    (i : ι)
    (hbound : M.baseBound + idx.depth i * M.stepBound ≤ maxBound)
    (hra : M.baseBound + idx.depth i * M.stepBound + T.frame.raBytes ≤ 2 ^ 64) :
    ∀ f ∈ mod.fns, T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.onlyFn f (Γrec i)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + idx.depth i * M.stepBound) nX := by
  obtain ⟨hdisj, haux⟩ :=
    compileModuleRec_disjoint' (show compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits
      nX fuel maxBound mod.fns hints = .ok (M.code, M.baseBound, M.stepBound) from
      by rw [hfs]; exact M.compileModuleRec_eq)
  exact compileScc_sound idx T h lt mod Γrec Γext extCallees exits nX hints
    M.code M.baseBound M.stepBound k₀ maxBound haux hdisj hc hu hM hsupp hext hext_uniq hexits
    i hbound hra

/-- Specialization of `link_scc_compiled` when `idx.depth i ≤ fuel`, automatically discharging
stack bounds from `M : CompiledRec`. -/
theorem link_scc_compiled_le {ι : Type} (idx : RecIdx ι) {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γrec : ι → Env) (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleSccOk idx Γrec Γext (M.stepBound != 0) mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g)
    {i : ι} (hi : idx.depth i ≤ fuel) :
    ∀ f ∈ mod.fns, T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.onlyFn f (Γrec i)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.boundAt (idx.depth i)) nX :=
  link_scc_compiled idx M mod hfs h Γrec Γext k₀ hc hu hM hsupp hext hext_uniq hexits i
    (M.boundAt_le_max hi) (M.total_ra_le_at hi)

/-- Specialization of `link_scc_compiled` to `M.host` with `extCallees = []`. -/
theorem link_scc_compiled_host {ι : Type} (idx : RecIdx ι) {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {maxBound : Nat}
    (M : CompiledRec T lt [] exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γrec : ι → Env) (Γext : Env)
    (hM : ModuleSccOk idx Γrec Γext (M.stepBound != 0) mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (i : ι)
    (hbound : M.baseBound + idx.depth i * M.stepBound ≤ maxBound)
    (hra : M.baseBound + idx.depth i * M.stepBound + T.frame.raBytes ≤ 2 ^ 64) :
    ∀ f ∈ mod.fns, T.Defined M.host f.name ∧
      T.FnSpec M.host f.name
        (legalEnv lt (Env.onlyFn f (Γrec i)) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + idx.depth i * M.stepBound) nX :=
  link_scc_compiled idx M mod hfs M.host Γrec Γext 0 M.code_infix_host M.labelsUnique hM hsupp
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ hg => M.defined_exit_host hg)
    i hbound hra

/-- Source-level specialization of `link_scc_compiled_host` when `lt.legalSig` fixes
`(f.as, f.rs)`. -/
theorem link_scc_compiled_src {ι : Type} (idx : RecIdx ι) {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {maxBound : Nat}
    (M : CompiledRec T lt [] exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γrec : ι → Env) (Γext : Env)
    (hM : ModuleSccOk idx Γrec Γext (M.stepBound != 0) mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (i : ι)
    (hbound : M.baseBound + idx.depth i * M.stepBound ≤ maxBound)
    (hra : M.baseBound + idx.depth i * M.stepBound + T.frame.raBytes ≤ 2 ^ 64)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hbs : lt.legalSig f.rs = f.rs) :
    T.Defined M.host f.name ∧
      T.FnSpec M.host f.name
        (fun args m Q X => Γrec i f.name f.as f.rs args m Q
          (fun g cs xs m' => X g (lt.legalSig cs) (encodeTup lt cs xs) m'))
        (M.baseBound + idx.depth i * M.stepBound) nX :=
  let ⟨hd, hs⟩ := link_scc_compiled_host idx M mod hfs Γrec Γext hM hsupp i hbound hra f hf
  ⟨hd, fnSpec_of_legalEnv_onlyFn has hbs hs⟩

/-- Non-exiting source-level specialization of `link_scc_compiled_src`. -/
theorem link_scc_compiled_src_noExit {ι : Type} (idx : RecIdx ι) {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {maxBound : Nat}
    (M : CompiledRec T lt [] exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γrec : ι → Env) (Γext : Env)
    (hM : ModuleSccOk idx Γrec Γext (M.stepBound != 0) mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (i : ι)
    (hbound : M.baseBound + idx.depth i * M.stepBound ≤ maxBound)
    (hra : M.baseBound + idx.depth i * M.stepBound + T.frame.raBytes ≤ 2 ^ 64)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hbs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γrec i f.name f.as f.rs args m Q X →
      Γrec i f.name f.as f.rs args m Q X') :
    T.Defined M.host f.name ∧
      T.FnSpec M.host f.name (Γrec i f.name f.as f.rs)
        (M.baseBound + idx.depth i * M.stepBound) nX :=
  let ⟨hd, hs⟩ :=
    link_scc_compiled_src idx M mod hfs Γrec Γext hM hsupp i hbound hra hf has hbs
  ⟨hd, Target.FnSpec.of_spec T hs fun args m Q X h => hnoex args m Q X _ h⟩

/-- **Static-budget export theorem:** packages all indices `i : ι` with `idx.depth i ≤ fuel`
into `Env.exportScc idx Γrec fuel` at uniform stack bound `M.baseBound + fuel * M.stepBound`. -/
theorem link_scc_export {ι : Type} (idx : RecIdx ι) {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γrec : ι → Env) (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleSccOk idx Γrec Γext (M.stepBound != 0) mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ f ∈ mod.fns, T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.onlyFn f (Env.exportScc idx Γrec fuel)) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + fuel * M.stepBound) nX := by
  obtain ⟨_, haux⟩ :=
    compileModuleRec_disjoint' (show compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits
      nX fuel maxBound mod.fns hints = .ok (M.code, M.baseBound, M.stepBound) from
      by rw [hfs]; exact M.compileModuleRec_eq)
  intro f hf
  refine ⟨defined_of_compileModuleRecAux haux hc hf, ?_⟩
  intro args m0 Q X hleg s ra R hargs hra hspE hmem
  rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀,
    _, ha, hb, i, hdepth, hΓi⟩
  have hspec_i := (link_scc_compiled_le idx M mod hfs h Γrec Γext k₀ hc hu hM hsupp
    hext hext_uniq hexits hdepth f hf).2
  have hleg_i : legalEnv lt (Env.onlyFn f (Γrec i)) f.name
      (lt.legalSig f.as) (lt.legalSig f.rs) args m0 Q X :=
    ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, rfl, ha, hb, hΓi⟩
  have hlift := Target.FnSpec.mono_stack T hspec_i (M.boundAt_mono hdepth) M.total_ra_le
  exact hlift args m0 Q X hleg_i s ra R hargs hra hspE hmem

/-- `Env.restrict`-shaped variant of `link_scc_export` ready to satisfy `hext` for downstream
outer SCCs or acyclic callers. -/
theorem link_scc_export_restrict {ι : Type} (idx : RecIdx ι) {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γrec : ι → Env) (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hM : ModuleSccOk idx Γrec Γext (M.stepBound != 0) mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g)
    {S : List SigEntry} (hSnd : (S.map Prod.fst).Nodup)
    {f : Fn} (hf : f ∈ mod.fns) (hfS : f.sig ∈ S) :
    T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.restrict (Env.exportScc idx Γrec fuel) S) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + fuel * M.stepBound) nX := by
  obtain ⟨hdef, hspec⟩ := link_scc_export idx M mod hfs h Γrec Γext k₀ hc hu hM hsupp
    hext hext_uniq hexits f hf
  refine ⟨hdef, Target.FnSpec.of_spec T hspec fun args m0 Q X hleg => ?_⟩
  rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hmemS, hΓ⟩
  obtain ⟨rfl, rfl⟩ := mem_unique_fst_sig hSnd hmemS hfS
  exact ⟨f.as, f.rs, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, rfl, rfl, rfl, hΓ⟩

/-- Specialization of `link_scc_export` to `M.host` with `extCallees = []`. -/
theorem link_scc_export_host {ι : Type} (idx : RecIdx ι) {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {maxBound : Nat}
    (M : CompiledRec T lt [] exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γrec : ι → Env) (Γext : Env)
    (hM : ModuleSccOk idx Γrec Γext (M.stepBound != 0) mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ f ∈ mod.fns, T.Defined M.host f.name ∧
      T.FnSpec M.host f.name
        (legalEnv lt (Env.onlyFn f (Env.exportScc idx Γrec fuel)) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + fuel * M.stepBound) nX :=
  link_scc_export idx M mod hfs M.host Γrec Γext 0 M.code_infix_host M.labelsUnique hM hsupp
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ hg => M.defined_exit_host hg)

/-- Source-level specialization of `link_scc_export_host` when `lt.legalSig` fixes
`(f.as, f.rs)` and `Env.exportScc` ignores exit continuations. -/
theorem link_scc_export_src_noExit {ι : Type} (idx : RecIdx ι) {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {maxBound : Nat}
    (M : CompiledRec T lt [] exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γrec : ι → Env) (Γext : Env)
    (hM : ModuleSccOk idx Γrec Γext (M.stepBound != 0) mod)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hbs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Env.exportScc idx Γrec fuel f.name f.as f.rs args m Q X →
      Env.exportScc idx Γrec fuel f.name f.as f.rs args m Q X') :
    T.Defined M.host f.name ∧
      T.FnSpec M.host f.name (Env.exportScc idx Γrec fuel f.name f.as f.rs)
        (M.baseBound + fuel * M.stepBound) nX := by
  obtain ⟨hdef, hspec⟩ := link_scc_export_host idx M mod hfs Γrec Γext hM hsupp f hf
  exact ⟨hdef, Target.FnSpec.of_spec T (fnSpec_of_legalEnv_onlyFn has hbs hspec)
    fun args m Q X h => hnoex args m Q X _ h⟩

/-- Recover `LinkRec.link_rec_compiled` cleanly as the `ι := Nat, lt := (· < ·), depth := id`
(`natRecIdx`) instance of `link_scc_compiled`. -/
theorem link_rec_of_scc {T : Target} {lt : LegalTarget}
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
        (M.boundAt k) nX := by
  let Γtrunc : Nat → Env := fun k =>
    if k ≤ fuel then Γrec k else fun _ _ _ _ _ _ _ => False
  have hM : ModuleSccOk natRecIdx Γtrunc Γext (M.stepBound != 0) mod := by
    refine moduleSccOk_of_step natRecIdx hcyc hwf fun k fn hfn Γ hrec' hext' xs m Q X hspec => ?_
    by_cases hk : k ≤ fuel
    · have hspec' : Γrec k fn.name fn.as fn.rs xs m Q X := by simpa [Γtrunc, hk] using hspec
      refine wp_env_mono (fun g as bs xs' m' Q' X' hg => ?_) _ m
        (hrec k hk fn hfn xs m Q X hspec')
      rcases hg with ⟨hsig, k', hk', hΓ'⟩ | ⟨hsig, hΓ'⟩
      · obtain ⟨gfn, hgfn, hgeq⟩ := List.mem_map.mp hsig
        cases hgeq
        have hk'_le : k' ≤ fuel := Nat.le_trans (Nat.le_of_lt hk') hk
        exact hrec' gfn hgfn k' hk' (Or.inr hk') xs' m' Q' X' (by simpa [Γtrunc, hk'_le] using hΓ')
      · obtain ⟨ex, hex, hexeq⟩ := List.mem_map.mp hsig
        cases hexeq
        exact hext' ex hex xs' m' Q' X' hΓ'
    · simp [Γtrunc, hk] at hspec
  intro k hk f hf
  obtain ⟨hdef, hspec⟩ := link_scc_compiled_le natRecIdx M mod hfs h Γtrunc Γext k₀ hc hu hM hsupp
    hext hext_uniq hexits (i := k) hk f hf
  refine ⟨hdef, Target.FnSpec.of_spec T hspec fun args m0 Q X hleg => ?_⟩
  rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hnm, ha, hb, hΓ⟩
  subst ha; subst hb
  exact ⟨f.as, f.rs, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hnm, rfl, rfl, by
    simpa [Γtrunc, hk] using hΓ⟩

end LeanQbe.T.LinkScc
