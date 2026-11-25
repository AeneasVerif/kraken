module

public import LeanQbe.T.Unified.Driver
public import LeanQbe.T.Bedrock2.FromKraken
public import LeanQbe.T.Main
public import LeanQbe.T.MainLemmas
public import Kraken.Bedrock2.SemanticsLemmas
import LeanQbe.T.Unified.DriverLemmas
import LeanQbe.T.RegaLemmas
import LeanQbe.T.TargetLemmas

/-!
# `Kraken.Bedrock2` Direct Frontend on `LeanQbe.T.Unified` (`Unified.Frontend.Bedrock2`)

Arch-free `LeanQbe.T.Unified.Frontend` adapter for `Kraken.Bedrock2` (`Func.fromKraken`,
`FuncB.toFunc`, `Func.fromKraken_toFunc_wf`, `Func.fromKraken_toFunc_wp_sound`, and
`Env.ofBedrock2Sound`):

* `bedrock2Src` / `bedrock2Lower` / `bedrock2Caps` / `bedrock2Frontend`: pinned direct `Frontend`
  (`caps := {}`, `route (bedrock2Frontend.caps _) = .direct`) with zero architecture imports
  (`Kraken.X64`, `Kraken.AArch64`, `LeanQbe.T.Amd64`, `LeanQbe.T.Arm64`-free).
* `bedrock2Module`, `bedrock2Env`, `bedrock2Module_moduleOk`, and `bedrock2ModMid` (`_eq`, `_wf`,
  `_sound`): whole-module lowering and `ModuleOk` soundness over acyclic `Kraken.Bedrock2.Env`
  lists, including `call`, `stackalloc`, and `interact`.
* `bedrock2TargetBackend`: shared arch-free `Unified.Backend` bridge over any `T : Target`
  (serving both `Amd64` and `Arm64`), plus end-to-end `unified` and `Compiled` / `TargetInit`
  theorems connecting `Kraken.Bedrock2.Exec` / `Kraken.Bedrock2.call` specs through `Fn.mid` to
  `Target.FnSpec` and `TargetInit.run_fnSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T
open LeanQbe.T.Bedrock2

/-! ## 1. `bedrock2Src`, `bedrock2Frontend`, and `B2Spec` -/

/-- A named first-order `Kraken.Bedrock2` function (`Sym × Kraken.Bedrock2.Func`). -/
abbrev B2NamedFunc : Type := Sym × Kraken.Bedrock2.Func

/-- Source-level `Kraken.Bedrock2` contract: external I/O specification `ext`, callee
environment `e`, and pre/post execution predicate `Pre`. -/
structure B2Spec : Type where
  ext : Kraken.Bedrock2.ExtSpec 64
  e : Kraken.Bedrock2.Env
  Pre : Sym → (nArgs nRets : Nat) → List (BitVec 64) → Mem 64 →
    (Kraken.Bedrock2.Trace 64 → Mem 64 → List (BitVec 64) → Prop) → Prop

/-- Empty `Kraken.Bedrock2` external I/O specification (no interactions permitted). -/
@[expose] def bedrock2ExtEmpty : Kraken.Bedrock2.ExtSpec 64 :=
  fun _ _ _ _ _ => False

/-- Source tier for first-order `Kraken.Bedrock2` functions (`B2NamedFunc`) with native
`Kraken.Bedrock2.Exec` operational semantics. -/
@[expose] def bedrock2Src : Tier.{0, 0} where
  Prog := B2NamedFunc
  Ok _ := True
  Spec := B2Spec
  top := ⟨bedrock2ExtEmpty, [], fun _ _ _ _ _ _ => False⟩
  Sat p s :=
    ∀ (xs : List (BitVec 64)) (m : Mem 64)
      (post : Kraken.Bedrock2.Trace 64 → Mem 64 → List (BitVec 64) → Prop),
      s.Pre p.1 p.2.params.length p.2.rets.length xs m post →
      ∃ B : Nat, B < 2 ^ 64 ∧
        Kraken.Bedrock2.Exec s.ext s.e B p.2.body [] m
          ((∅ : Kraken.Bedrock2.Locals 64).insertMany (p.2.params.zip xs))
          (fun t' m' l' =>
            ∃ retvs, Kraken.Bedrock2.getMany l' p.2.rets = some retvs ∧ post t' m' retvs)

/-- Universal `B2Spec` packaging all valid `Kraken.Bedrock2.Exec` runs in `(ext, e)`. -/
@[expose] def B2Spec.ofEnv (ext : Kraken.Bedrock2.ExtSpec 64)
    (e : Kraken.Bedrock2.Env) : B2Spec where
  ext := ext
  e := e
  Pre sym nArgs nRets xs m post :=
    ∃ (B : Nat) (f : Kraken.Bedrock2.Func),
      B < 2 ^ 64 ∧ e.lookup sym = some f ∧
      f.params.length = nArgs ∧ f.rets.length = nRets ∧
      Kraken.Bedrock2.Exec ext e B f.body [] m
        ((∅ : Kraken.Bedrock2.Locals 64).insertMany (f.params.zip xs))
        (fun t' m' l' =>
          ∃ retvs, Kraken.Bedrock2.getMany l' f.rets = some retvs ∧ post t' m' retvs)

private theorem list_lookup_of_nodup {α β : Type} [DecidableEq α] :
    ∀ {xs : List (α × β)}, (xs.map Prod.fst).Nodup →
      ∀ {p : α × β}, p ∈ xs → xs.lookup p.1 = some p.2
  | [], _, _, hp => nomatch hp
  | (k, v) :: rest, hnd, (a, b), hp => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with hhead | htail
    · cases hhead
      simp [List.lookup]
    · have hne : (a == k) = false := beq_false_of_ne fun he => by
        subst he
        exact hnd.1 (List.mem_map.mpr ⟨(a, b), htail, rfl⟩)
      simp only [List.lookup, hne]
      exact list_lookup_of_nodup hnd.2 htail

private theorem exec_of_kraken_call {ext : Kraken.Bedrock2.ExtSpec 64}
    {e : Kraken.Bedrock2.Env} {B : Nat} {p : B2NamedFunc}
    (hlk : e.lookup p.1 = some p.2)
    {t : Kraken.Bedrock2.Trace 64} {m : Mem 64} {xs : List (BitVec 64)}
    {post : Kraken.Bedrock2.Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    (hcall : Kraken.Bedrock2.call ext e B p.1 t m xs post) :
    Kraken.Bedrock2.Exec ext e B p.2.body t m
      ((∅ : Kraken.Bedrock2.Locals 64).insertMany (p.2.params.zip xs))
      (fun t' m' l' =>
        ∃ retvs, Kraken.Bedrock2.getMany l' p.2.rets = some retvs ∧ post t' m' retvs) := by
  rcases hcall with ⟨f, hf, l, hput, hex⟩
  rw [hlk, Option.some.injEq] at hf
  subst hf
  simp only [Kraken.Bedrock2.putManyZip] at hput
  split at hput
  · simp only [Option.some.injEq] at hput
    subst hput
    exact hex
  · cases hput

theorem bedrock2Src_sat_of_call {p : B2NamedFunc} {s : B2Spec}
    (hlk : s.e.lookup p.1 = some p.2)
    (hcall : ∀ (xs : List (BitVec 64)) (m : Mem 64)
      (post : Kraken.Bedrock2.Trace 64 → Mem 64 → List (BitVec 64) → Prop),
      s.Pre p.1 p.2.params.length p.2.rets.length xs m post →
      ∃ B : Nat, B < 2 ^ 64 ∧ Kraken.Bedrock2.call s.ext s.e B p.1 [] m xs post) :
    bedrock2Src.Sat p s := by
  intro xs m post hpre
  obtain ⟨B, hB, hc⟩ := hcall xs m post hpre
  exact ⟨B, hB, exec_of_kraken_call hlk hc⟩

theorem bedrock2Src_sat_ofEnv {ext : Kraken.Bedrock2.ExtSpec 64}
    {e : Kraken.Bedrock2.Env} (hnd : (e.map Prod.fst).Nodup)
    {p : B2NamedFunc} (hp : p ∈ e) :
    bedrock2Src.Sat p (B2Spec.ofEnv ext e) := by
  intro xs m post ⟨B, f, hB, hlk, _, _, hex⟩
  have hlk' := list_lookup_of_nodup hnd hp
  rw [hlk', Option.some.injEq] at hlk
  subst hlk
  exact ⟨B, hB, hex⟩

/-- Lower a named `Kraken.Bedrock2.Func` into a typed `LeanQbe.T.Fn` via `Func.fromKraken` and
`FuncB.toFunc cfg`. -/
@[expose] def b2NamedFuncToFn? (cfg : LowerCfg := LowerCfg.default)
    (p : B2NamedFunc) : Except String Fn :=
  match Func.fromKraken p.2 with
  | some fb =>
    .ok ⟨p.1, List.replicate p.2.params.length i64, List.replicate p.2.rets.length i64,
      fb.toFunc cfg⟩
  | none => .error s!"bedrock2: cannot lower `{p.1}`"

theorem b2NamedFuncToFn?_wf {cfg : LowerCfg} {p : B2NamedFunc} {fn : Fn}
    (h : b2NamedFuncToFn? cfg p = .ok fn) : fn.Wf := by
  unfold b2NamedFuncToFn? at h
  cases hfk : Func.fromKraken p.2 with
  | none => simp [hfk] at h
  | some fb =>
    simp only [hfk, Except.ok.injEq] at h
    subst h
    exact Func.fromKraken_toFunc_wf hfk cfg

/-- Translate a `B2Spec` into a `LeanQbe.T.Unified.SSpec` backed by
`Env.ofBedrock2Sound cfg (extToB s.ext) (EnvB.ofKraken s.ext s.e)`. -/
@[expose] def bedrock2ToSSpec (cfg : LowerCfg) (p : B2NamedFunc) (s : B2Spec) : SSpec where
  Γ := Env.ofBedrock2Sound cfg (extToB s.ext) (EnvB.ofKraken s.ext s.e)
  C as rs args m Q _ :=
    ∃ (h1 : List.replicate p.2.params.length i64 = as)
      (h2 : List.replicate p.2.rets.length i64 = rs)
      (post : Kraken.Bedrock2.Trace 64 → Mem 64 → List (BitVec 64) → Prop),
      s.Pre p.1 p.2.params.length p.2.rets.length
        (tupToList (cast (congrArg (Tup Val) h1.symm) args)) m post ∧
      ∀ (resTup : Tup Val (List.replicate p.2.rets.length i64)) t' m',
        post t' m' (tupToList resTup) → Q (cast (congrArg (Tup Val) h2) resTup) m'

/-- Checked lowering stage from `bedrock2Src` into `ssa` via `b2NamedFuncToFn?`. -/
@[expose] def bedrock2Lower (cfg : LowerCfg := LowerCfg.default) : Stage bedrock2Src ssa where
  run := b2NamedFuncToFn? cfg
  tr := bedrock2ToSSpec cfg
  ok _ _ _ h := b2NamedFuncToFn?_wf h
  sound p q s _ h hs := by
    unfold b2NamedFuncToFn? at h
    cases hfk : Func.fromKraken p.2 with
    | none => simp [hfk] at h
    | some fb =>
      simp only [hfk] at h
      injection h with h
      subst h
      rintro xs m Q X ⟨_, _, post, hpre, hpost⟩
      dsimp only at hpre hpost
      rw [cast_eq] at hpre
      obtain ⟨B, hB, hex⟩ := hs (tupToList xs) m post hpre
      refine Func.fromKraken_toFunc_wp_sound hfk hB X (post := post) ?_ hex cfg
      intro resTup t' m' hp
      simpa only [cast_eq] using hpost resTup t' m' hp

/-- Pinned empty capability summary (`{}`) routing every `Kraken.Bedrock2` function directly. -/
@[expose] def bedrock2Caps (_ : B2NamedFunc) : Caps := {}

/-- Configurable direct `Frontend` for `Kraken.Bedrock2` (`caps := fun _ => {}`). -/
@[expose] def bedrock2FrontendWith (cfg : LowerCfg) : Frontend.{0, 0} :=
  ⟨bedrock2Src, bedrock2Caps, bedrock2Lower cfg⟩

/-- Pinned direct `Frontend` for `Kraken.Bedrock2` (`cfg := LowerCfg.default`,
`caps := fun _ => {}`). -/
@[expose] def bedrock2Frontend : Frontend.{0, 0} :=
  bedrock2FrontendWith LowerCfg.default

theorem bedrock2Frontend_caps (cfg : LowerCfg) (p : B2NamedFunc) :
    (bedrock2FrontendWith cfg).caps p = {} :=
  rfl

theorem bedrock2Frontend_direct (cfg : LowerCfg) (p : B2NamedFunc) :
    route ((bedrock2FrontendWith cfg).caps p) = .direct :=
  rfl

theorem bedrock2Frontend_unified_direct (cfg : LowerCfg) (Bs : Backends.{0})
    (p : B2NamedFunc) :
    pick Bs (route ((bedrock2FrontendWith cfg).caps p)) = Bs.direct :=
  rfl

theorem bedrock2Frontend_unified_eq_legacy (cfg : LowerCfg) (t : LegalTarget) (B : Backend.{0})
    (p : B2NamedFunc) :
    (unified (bedrock2FrontendWith cfg) t B).run p =
      bindE ((bedrock2FrontendWith cfg).lower.run p) fun q => bindE (legacyMid t q) B.lower :=
  rfl

theorem bedrock2Frontend_mapM_wf (cfg : LowerCfg) (fs : List B2NamedFunc) {fns : List Fn}
    (h : (bedrock2FrontendWith cfg).lower.mapM fs = .ok fns) : ∀ fn ∈ fns, fn.Wf := by
  intro fn hfn
  obtain ⟨p, _, hp, _, _⟩ :=
    Stage.mapM_sound (bedrock2FrontendWith cfg).lower (fun _ => bedrock2Src.top)
      fs fns (fun _ _ => trivial)
      (fun _ _ _ _ _ hpre => False.elim hpre) h fn hfn
  exact b2NamedFuncToFn?_wf hp

theorem bedrock2Lower_mapM_spec (cfg : LowerCfg) :
    ∀ (fs : List B2NamedFunc) {fns : List Fn},
      (bedrock2FrontendWith cfg).lower.mapM fs = .ok fns →
      fns.map Fn.name = fs.map Prod.fst ∧
      ∀ p ∈ fs, ∃ fb, Func.fromKraken p.2 = some fb ∧
        (⟨p.1, List.replicate p.2.params.length i64, List.replicate p.2.rets.length i64,
          fb.toFunc cfg⟩ : Fn) ∈ fns
  | [], fns, h => by
    simp only [Stage.mapM] at h
    cases h
    exact ⟨rfl, fun _ hp => nomatch hp⟩
  | p :: rest, fns, h => by
    obtain ⟨q, qs, hq, hqs, rfl⟩ :=
      @Stage.mapM_cons_ok bedrock2Src ssa (bedrock2FrontendWith cfg).lower p rest fns h
    dsimp only [bedrock2FrontendWith, bedrock2Lower, b2NamedFuncToFn?] at hq
    cases hfk : Func.fromKraken p.2 with
    | none => simp [hfk] at hq
    | some fb =>
      simp only [hfk] at hq
      injection hq with hq
      subst hq
      obtain ⟨hnames, hmem⟩ := bedrock2Lower_mapM_spec cfg rest hqs
      refine ⟨congrArg (p.1 :: ·) hnames, fun p' hp' => ?_⟩
      rcases List.mem_cons.mp hp' with rfl | hpRest
      · exact ⟨fb, hfk, List.mem_cons_self⟩
      · obtain ⟨fb', hfk', hm'⟩ := hmem p' hpRest
        exact ⟨fb', hfk', List.mem_cons_of_mem _ hm'⟩

/-! ## 2. `bedrock2Module`, `bedrock2Env`, & `ModuleOk` -/

/-- Extern declarations for `stackalloc` (`cfg.allocSym` and `cfg.freeSym`). -/
@[expose] def bedrock2StackExterns (cfg : LowerCfg := LowerCfg.default) : List Extern :=
  [⟨cfg.allocSym, [i64], [i64]⟩, ⟨cfg.freeSym, [i64, i64], []⟩]

/-- Lower a list of `B2NamedFunc`s via `(bedrock2FrontendWith cfg).lower.mapM` into a
`LeanQbe.T.Module`. -/
@[expose] def bedrock2Module (fs : List B2NamedFunc)
    (externs : List Extern := []) (exits : List Sym := [])
    (cfg : LowerCfg := LowerCfg.default) : Except String Module :=
  bindE ((bedrock2FrontendWith cfg).lower.mapM fs) fun fns =>
    .ok { fns := fns, externs := externs, exits := exits }

theorem bedrock2Module_eq {fs : List B2NamedFunc} {externs : List Extern} {exits : List Sym}
    {cfg : LowerCfg} {M : Module}
    (h : bedrock2Module fs externs exits cfg = .ok M) :
    ∃ fns, (bedrock2FrontendWith cfg).lower.mapM fs = .ok fns ∧
      M = { fns := fns, externs := externs, exits := exits } := by
  dsimp only [bedrock2Module] at h
  obtain ⟨fns, hmap, hok⟩ := bindE_ok h
  cases hok
  exact ⟨fns, hmap, rfl⟩

theorem bedrock2Module_wf {fs : List B2NamedFunc} {externs : List Extern} {exits : List Sym}
    {cfg : LowerCfg} {M : Module}
    (h : bedrock2Module fs externs exits cfg = .ok M) :
    ∀ fn ∈ M.fns, fn.Wf := by
  obtain ⟨fns, hmap, rfl⟩ := bedrock2Module_eq h
  exact bedrock2Frontend_mapM_wf cfg fs hmap

theorem bedrock2Module_names {fs : List B2NamedFunc} {externs : List Extern} {exits : List Sym}
    {cfg : LowerCfg} {M : Module}
    (h : bedrock2Module fs externs exits cfg = .ok M) :
    M.fns.map Fn.name = fs.map Prod.fst := by
  obtain ⟨fns, hmap, rfl⟩ := bedrock2Module_eq h
  exact (bedrock2Lower_mapM_spec cfg fs hmap).1

theorem bedrock2Module_mem {fs : List B2NamedFunc} {externs : List Extern} {exits : List Sym}
    {cfg : LowerCfg} {M : Module}
    (h : bedrock2Module fs externs exits cfg = .ok M) {p : B2NamedFunc} (hp : p ∈ fs) :
    ∃ fb, Func.fromKraken p.2 = some fb ∧
      (⟨p.1, List.replicate p.2.params.length i64, List.replicate p.2.rets.length i64,
        fb.toFunc cfg⟩ : Fn) ∈ M.fns := by
  obtain ⟨fns, hmap, rfl⟩ := bedrock2Module_eq h
  exact (bedrock2Lower_mapM_spec cfg fs hmap).2 p hp

/-- Soundness `LeanQbe.T.Env` for lowered `Kraken.Bedrock2` modules. -/
@[expose] def bedrock2Env (cfg : LowerCfg) (ext : Kraken.Bedrock2.ExtSpec 64)
    (e : Kraken.Bedrock2.Env) : Env :=
  Env.ofBedrock2Sound cfg (extToB ext) (EnvB.ofKraken ext e)

/-- Disjointness between defined function names in `fs` and `LowerCfg` runtime/IO symbols. -/
@[expose] def Bedrock2NamesValid (cfg : LowerCfg) (ext : Kraken.Bedrock2.ExtSpec 64)
    (fs : List B2NamedFunc) : Prop :=
  ∀ p ∈ fs, p.1 ≠ cfg.allocSym ∧ p.1 ≠ cfg.freeSym ∧
    ∀ action, p.1 = cfg.ioSym action →
      ∀ t mGive args mid, ¬ ext t mGive action args mid

theorem bedrock2NamesValid_empty {cfg : LowerCfg} {fs : List B2NamedFunc}
    (h : fs.all (fun p => p.1 != cfg.allocSym && p.1 != cfg.freeSym) = true) :
    Bedrock2NamesValid cfg bedrock2ExtEmpty fs := by
  intro p hp
  have h' := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, bne_iff_ne] at h'
  exact ⟨h'.1, h'.2, fun _ _ _ _ _ _ hF => hF⟩

private theorem bedrock2Lower_mapM_mem_src (cfg : LowerCfg) :
    ∀ {fs : List B2NamedFunc} {fns : List Fn},
      (bedrock2FrontendWith cfg).lower.mapM fs = .ok fns →
      ∀ fn ∈ fns, ∃ p ∈ fs, ∃ fb, Func.fromKraken p.2 = some fb ∧
        fn = ⟨p.1, List.replicate p.2.params.length i64, List.replicate p.2.rets.length i64,
          fb.toFunc cfg⟩
  | [], fns, h, _, hfn => by
    simp only [Stage.mapM] at h
    cases h
    nomatch hfn
  | p :: rest, fns, h, fn, hfn => by
    obtain ⟨q, qs, hq, hqs, rfl⟩ :=
      @Stage.mapM_cons_ok bedrock2Src ssa (bedrock2FrontendWith cfg).lower p rest fns h
    dsimp only [bedrock2FrontendWith, bedrock2Lower, b2NamedFuncToFn?] at hq
    cases hfk : Func.fromKraken p.2 with
    | none => simp [hfk] at hq
    | some fb =>
      simp only [hfk] at hq
      injection hq with hq
      subst hq
      rcases List.mem_cons.mp hfn with rfl | htail
      · exact ⟨p, List.mem_cons_self, fb, hfk, rfl⟩
      · obtain ⟨p', hp', fb', hfk', rfl⟩ := bedrock2Lower_mapM_mem_src cfg hqs fn htail
        exact ⟨p', List.mem_cons_of_mem _ hp', fb', hfk', rfl⟩

/-- Every acyclic `bedrock2Module` satisfies `ModuleOk (bedrock2Env cfg ext fs) M` unconditionally
(covering pure functions, `call`, `stackalloc`, and `interact`). -/
theorem bedrock2Module_moduleOk {cfg : LowerCfg} {fs : List B2NamedFunc}
    {externs : List Extern} {exits : List Sym} {M : Module}
    {ext : Kraken.Bedrock2.ExtSpec 64}
    (hmod : bedrock2Module fs externs exits cfg = .ok M)
    (hacyc : M.checkAcyclic = true)
    (hval : Bedrock2NamesValid cfg ext fs) :
    ModuleOk (bedrock2Env cfg ext fs) M := by
  obtain ⟨fns, hmap, rfl⟩ := bedrock2Module_eq hmod
  have hacyc' := hacyc
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hacyc'
  have hndM : ({ fns := fns, externs := externs, exits := exits } : Module).namesNodup :=
    Module.namesNodup_of_checkNamesNodup hacyc'.1
  have hndFs : (fs.map Prod.fst).Nodup := by
    rw [← (bedrock2Lower_mapM_spec cfg fs hmap).1]
    exact (List.nodup_append.mp hndM).1
  refine Module.moduleOk_of_checkAcyclic hacyc (bedrock2Frontend_mapM_wf cfg fs hmap) ?_
  intro fn hfn xs m Q X hspec
  obtain ⟨p, hp, fb, hfk, rfl⟩ := bedrock2Lower_mapM_mem_src cfg hmap fn hfn
  obtain ⟨hna, hnf, hnio⟩ := hval p hp
  rcases hspec with ⟨_, hdisj⟩
  rcases hdisj with
      ⟨ha, _⟩
    | ⟨hf, _⟩
    | ⟨action, hio, tB, mKeep, mGive, midB, _, hexB, _⟩
    | ⟨B, tB, P', hB, hEnvB, hP'⟩
  · exact absurd ha hna
  · exact absurd hf hnf
  · rcases hexB with ⟨_, _, _, _, _, hex, _⟩
    exact absurd hex (hnio action hio _ _ _ _)
  · rcases hEnvB with ⟨f', t0, argList, lf, mid, hlk, _, hExtArgs, hput, hex, hPost⟩
    have hlk' := list_lookup_of_nodup hndFs hp
    rw [hlk', Option.some.injEq] at hlk
    subst hlk
    rw [extTupToList?_replicate, Option.some.injEq] at hExtArgs
    subst hExtArgs
    simp only [Kraken.Bedrock2.putManyZip] at hput
    split at hput
    · simp only [Option.some.injEq] at hput
      subst hput
      refine Func.fromKraken_toFunc_wp_sound hfk hB X (t := t0)
        (post := fun _ m' retvs =>
          ∀ resTup : Tup Val (List.replicate p.2.rets.length i64),
            tupToList resTup = retvs → Q resTup m')
        (fun resTup _ _ hp' => hp' resTup rfl) ?_ cfg
      refine Exec.weaken_b2 hex fun t' m' st1 hm => ?_
      obtain ⟨retvs, resTup, hget, hExtRet, hP⟩ := hPost t' m' st1 hm
      rw [extTupToList?_replicate, Option.some.injEq] at hExtRet
      refine ⟨retvs, hget, fun resTup' hEq => ?_⟩
      have hinj : resTup' = resTup := tupToList_inj (hEq.trans hExtRet.symm)
      cases hinj
      exact hP' _ (traceToB t') m' hP
    · cases hput
where
  Exec.weaken_b2 {ext : Kraken.Bedrock2.ExtSpec 64} {e : Kraken.Bedrock2.Env}
      {c : Kraken.Bedrock2.Cmd} {B : Nat} {t : Kraken.Bedrock2.Trace 64} {m : Mem 64}
      {l : Kraken.Bedrock2.Locals 64}
      {P Q : Kraken.Bedrock2.Trace 64 → Mem 64 → Kraken.Bedrock2.Locals 64 → Prop}
      (hex : Kraken.Bedrock2.Exec ext e B c t m l P)
      (hPQ : ∀ t' m' l', P t' m' l' → Q t' m' l') :
      Kraken.Bedrock2.Exec ext e B c t m l Q := by
    induction hex generalizing Q with
    | skip _ _ _ _ _ hp => exact .skip _ _ _ _ _ (hPQ _ _ _ hp)
    | set _ _ _ _ _ _ _ _ hv hp => exact .set _ _ _ _ _ _ _ _ hv (hPQ _ _ _ hp)
    | unset _ _ _ _ _ _ hp => exact .unset _ _ _ _ _ _ (hPQ _ _ _ hp)
    | store _ _ _ _ _ _ _ _ _ _ _ ha hv hs hp =>
        exact .store _ _ _ _ _ _ _ _ _ _ _ ha hv hs (hPQ _ _ _ hp)
    | stackalloc _ _ _ _ _ _ _ _ hle _ ih =>
        exact .stackalloc _ _ _ _ _ _ _ _ hle fun a ms mc ha hs =>
          ih a ms mc ha hs fun _ _ _ ⟨m1, m2, h1, h2, hp⟩ => ⟨m1, m2, h1, h2, hPQ _ _ _ hp⟩
    | if_true _ _ _ _ _ _ _ _ _ hv hnz _ ih => exact .if_true _ _ _ _ _ _ _ _ _ hv hnz (ih hPQ)
    | if_false _ _ _ _ _ _ _ _ _ hv hz _ ih => exact .if_false _ _ _ _ _ _ _ _ _ hv hz (ih hPQ)
    | seq _ _ _ _ _ _ _ _ _ _ _ ih2 =>
        exact .seq _ _ _ _ _ _ _ _ (by assumption) fun _ _ _ hm => ih2 _ _ _ hm hPQ
    | while_false _ _ _ _ _ _ _ _ hv hz hp =>
        exact .while_false _ _ _ _ _ _ _ _ hv hz (hPQ _ _ _ hp)
    | while_true _ _ _ _ _ _ _ _ _ hv hnz _ _ _ ihw =>
        exact .while_true _ _ _ _ _ _ _ _ _ hv hnz (by assumption) fun _ _ _ hm => ihw _ _ _ hm hPQ
    | call _ _ _ _ _ _ _ _ _ _ _ _ hf ha hl _ hk =>
        exact .call _ _ _ _ _ _ _ _ _ _ _ _ hf ha hl (by assumption) fun _ _ _ hm =>
          let ⟨rv, h1, l', h2, hp⟩ := hk _ _ _ hm; ⟨rv, h1, l', h2, hPQ _ _ _ hp⟩
    | interact _ _ _ _ _ _ _ _ _ _ _ _ hs ha hx hk =>
        exact .interact _ _ _ _ _ _ _ _ _ _ _ _ hs ha hx fun _ _ hm =>
          let ⟨l', h1, hp⟩ := hk _ _ hm; ⟨l', h1, fun m' hs' => hPQ _ _ _ (hp m' hs')⟩

/-! ## 3. Shared Mid-End Lifting (`bedrock2ModMid`) & Signature Transfer -/

/-- Route `Kraken.Bedrock2` functions through `(bedrock2FrontendWith cfg).lower` and shared
production `midEnd t`. -/
@[expose] def bedrock2ModMid (t : LegalTarget) (fs : List B2NamedFunc)
    (cfg : LowerCfg := LowerCfg.default) : Except String (List Fn) :=
  ((bedrock2FrontendWith cfg).lower ≫ midEnd t).mapM fs

theorem bedrock2ModMid_eq (t : LegalTarget) (cfg : LowerCfg) :
    ∀ (fs : List B2NamedFunc) {qs : List Fn},
      bedrock2ModMid t fs cfg = .ok qs →
      ∃ fns, (bedrock2FrontendWith cfg).lower.mapM fs = .ok fns ∧ qs = fns.map (·.mid t)
  | [], qs, h => by
    simp only [bedrock2ModMid, Stage.mapM] at h
    cases h
    exact ⟨[], rfl, rfl⟩
  | p :: rest, qs, h => by
    dsimp only [bedrock2ModMid] at h
    obtain ⟨q, qs', hq, hqs, rfl⟩ :=
      @Stage.mapM_cons_ok bedrock2Src ssa ((bedrock2FrontendWith cfg).lower ≫ midEnd t) p rest qs h
    dsimp only [Stage.comp, bedrock2FrontendWith, bedrock2Lower, bindE] at hq
    cases hrun : b2NamedFuncToFn? cfg p with
    | error e => simp [hrun] at hq
    | ok fn =>
      simp only [hrun, midEnd] at hq
      by_cases hs : (fn.earlyOpt).body.supportsSource t = true
      · simp only [hs, ↓reduceIte] at hq
        cases hq
        obtain ⟨fns', hmap', hqs'⟩ := bedrock2ModMid_eq t cfg rest hqs
        refine ⟨fn :: fns', ?_, by rw [hqs']; rfl⟩
        change bindE (b2NamedFuncToFn? cfg p)
          (fun fn₀ => bindE ((bedrock2FrontendWith cfg).lower.mapM rest)
            (fun qs₀ => .ok (fn₀ :: qs₀))) = .ok (fn :: fns')
        rw [hrun, bindE, hmap']
        rfl
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hq
        cases hq

theorem bedrock2ModMid_module_eq {t : LegalTarget} {fs : List B2NamedFunc}
    {externs : List Extern} {exits : List Sym} {cfg : LowerCfg} {M : Module} {qs : List Fn}
    (hmod : bedrock2Module fs externs exits cfg = .ok M)
    (hmid : bedrock2ModMid t fs cfg = .ok qs) :
    qs = M.fns.map (·.mid t) := by
  obtain ⟨fns, hmap, rfl⟩ := bedrock2Module_eq hmod
  obtain ⟨fns', hmap', hqs⟩ := bedrock2ModMid_eq t cfg fs hmid
  rw [hmap] at hmap'
  cases hmap'
  exact hqs

theorem bedrock2ModMid_wf (t : LegalTarget) (fs : List B2NamedFunc)
    (cfg : LowerCfg := LowerCfg.default) {qs : List Fn}
    (h : bedrock2ModMid t fs cfg = .ok qs) : ∀ q ∈ qs, q.Wf := by
  intro q hq
  obtain ⟨_, _, _, hok, _⟩ := Stage.mapM_sound ((bedrock2FrontendWith cfg).lower ≫ midEnd t)
    (fun _ => bedrock2Src.top) fs qs (fun _ _ => trivial)
    (fun _ _ _ _ _ hpre => False.elim hpre) h q hq
  exact hok

theorem bedrock2ModMid_sound (t : LegalTarget) (fs : List B2NamedFunc)
    (S : B2NamedFunc → B2Spec) (qs : List Fn)
    (hsat : ∀ p ∈ fs, bedrock2Src.Sat p (S p))
    (cfg : LowerCfg := LowerCfg.default)
    (h : bedrock2ModMid t fs cfg = .ok qs) :
    ∀ q ∈ qs, ∃ p ∈ fs,
      ((bedrock2FrontendWith cfg).lower ≫ midEnd t).run p = .ok q ∧
      ssa.Ok q ∧ ssa.Sat q (((bedrock2FrontendWith cfg).lower ≫ midEnd t).tr p (S p)) :=
  Stage.mapM_sound ((bedrock2FrontendWith cfg).lower ≫ midEnd t) S fs qs
    (fun _ _ => trivial) hsat h

theorem bedrock2ModMid_ofEnv_sound (t : LegalTarget) (ext : Kraken.Bedrock2.ExtSpec 64)
    (fs : List B2NamedFunc) (hnd : (fs.map Prod.fst).Nodup) (qs : List Fn)
    (cfg : LowerCfg := LowerCfg.default)
    (h : bedrock2ModMid t fs cfg = .ok qs) :
    ∀ q ∈ qs, ∃ p ∈ fs,
      ((bedrock2FrontendWith cfg).lower ≫ midEnd t).run p = .ok q ∧
      ssa.Ok q ∧
      ssa.Sat q (((bedrock2FrontendWith cfg).lower ≫ midEnd t).tr p (B2Spec.ofEnv ext fs)) :=
  bedrock2ModMid_sound t fs (fun _ => B2Spec.ofEnv ext fs) qs
    (fun _ hp => bedrock2Src_sat_ofEnv hnd hp) cfg h

private theorem minGe_le (w : Nat) : ∀ (ws : List Nat) {b : Nat}, minGe w ws = some b → w ≤ b
  | [], _, h => by simp [minGe] at h
  | x :: xs, b, h => by
    dsimp only [minGe] at h
    cases hx : minGe w xs with
    | none =>
      rw [hx] at h
      by_cases hwx : w ≤ x
      · simp only [hwx, ↓reduceIte, Option.some.injEq] at h
        omega
      · simp [hwx] at h
    | some best =>
      rw [hx] at h
      by_cases hwb : w ≤ x && x < best
      · simp only [hwb, ↓reduceIte, Option.some.injEq] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hwb
        omega
      · simp only [hwb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        exact h ▸ minGe_le w xs hx

private theorem minGe_eq_self_of_mem :
    ∀ (n : Nat) (ws : List Nat), n ∈ ws → minGe n ws = some n
  | _, [], h => nomatch h
  | n, w :: ws, h => by
    dsimp only [minGe]
    rcases List.mem_cons.mp h with rfl | hrest
    · cases hmg : minGe n ws with
      | none => simp
      | some best =>
        by_cases hlt : n < best
        · simp [hlt]
        · have hge := minGe_le n ws hmg
          have heq : best = n := by omega
          simp [heq]
    · rw [minGe_eq_self_of_mem n ws hrest]
      by_cases hlt : n ≤ w && w < n
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
        omega
      · simp [hlt]

theorem legalSig_replicate_i64 {t : LegalTarget} (h64 : 64 ∈ t.bitWidths) :
    ∀ n : Nat, t.legalSig (List.replicate n i64) = List.replicate n i64
  | 0 => rfl
  | n + 1 => by
    have hw : t.widenWidth 64 = 64 := by
      dsimp only [LegalTarget.widenWidth]
      rw [minGe_eq_self_of_mem 64 t.bitWidths h64]
      rfl
    have ht : t.legalTys i64 = [i64] := by
      change [Ty.bits (t.widenWidth 64)] = [i64]
      rw [hw]
    rw [List.replicate_succ, LegalTarget.legalSig, ht, List.singleton_append,
      legalSig_replicate_i64 h64 n]

/-! ## 4. Shared Arch-Free `Backend` Bridge (`bedrock2TargetBackend`) & `unified` Theorems -/

/-- Host-level `Target.FnSpec` satisfaction for `ds` compiled from `fn : Fn` on `T : Target`
(arch-free: shared across `Amd64` and `Arm64`). -/
@[expose] def bedrock2TargetHostSpec (T : Target) (hints : Fn → T.toIsa.Hints)
    (ds : List T.Directive) (s : SSpec) (fn : Fn) : Prop :=
  ∀ (h : T.mach.Host) (k₀ n nX : Nat) (bound : Sym → Nat),
    ds.IsInfixAt (T.mach.prog h) k₀ →
    T.LabelsUnique h →
    Rega.effFrame T.toIsa (hints fn) fn.ext ≤ n →
    n + T.frame.raBytes ≤ 2 ^ 64 →
    (∀ g as bs, (g, as, bs) ∈ fn.ext.callees →
      T.FnSpec h g (s.Γ g as bs) (bound g) nX ∧
      Rega.effFrame T.toIsa (hints fn) fn.ext + T.frame.raBytes + bound g ≤ n) →
    (∀ g, g ∈ fn.ext.exits → T.Defined h g ∧ nX ≤ n) →
    T.Defined h fn.name ∧ T.FnSpec h fn.name (s.C fn.as fn.rs) n nX

/-- Target-tier `MSat` for `bedrock2TargetBackend T hints`: non-vacuous compilation witness
paired with universal host soundness for every matching `Fn`. -/
@[expose] def bedrock2TargetMSat (T : Target) (hints : Fn → T.toIsa.Hints)
    (ds : List T.Directive) (s : SSpec) : Prop :=
  (∃ fn : Fn, fn.Wf ∧ Rega.lowerFn T.toIsa (hints fn) fn.ext fn = .ok ds ∧
    bedrock2TargetHostSpec T hints ds s fn) ∧
  (∀ fn : Fn, fn.Wf → Rega.lowerFn T.toIsa (hints fn) fn.ext fn = .ok ds →
    ssa.Sat fn s → bedrock2TargetHostSpec T hints ds s fn)

private theorem defined_of_lowerFn_loc {T : Target} {host : T.mach.Host}
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

theorem bedrock2TargetHostSpec_of_lower {T : Target} {hints : Fn → T.toIsa.Hints}
    {fn : Fn} {ds : List T.Directive} {s : SSpec}
    (hwf : fn.Wf) (hl : Rega.lowerFn T.toIsa (hints fn) fn.ext fn = .ok ds)
    (hsat : ssa.Sat fn s) : bedrock2TargetHostSpec T hints ds s fn := by
  intro h k₀ n nX bound hinf hu hfr hn hcal hex
  refine ⟨defined_of_lowerFn_loc hl hinf, ?_⟩
  have hfn := Rega.lowerFn_correct T h (hints fn) fn.ext fn s.Γ n nX bound hwf hl hinf hu
    hfr hn hcal hex
  exact fun args m Q X hC => hfn args m Q X (hsat args m Q X hC)

/-- Shared arch-free `Unified.Backend` bridge over any `T : Target` (applicable to both `Amd64`
and `Arm64` using only arch-free `Target`, `RegaLemmas`, and `DriverLemmas`). -/
@[expose] def bedrock2TargetBackend (T : Target) (hints : Fn → T.toIsa.Hints) : Backend.{0} where
  D := T.Directive
  MSat := bedrock2TargetMSat T hints
  lower fn := Rega.lowerFn T.toIsa (hints fn) fn.ext fn
  correct fn _ _ hwf hl hsat :=
    ⟨⟨fn, hwf, hl, bedrock2TargetHostSpec_of_lower hwf hl hsat⟩,
     fun _ hwf' hl' hsat' => bedrock2TargetHostSpec_of_lower hwf' hl' hsat'⟩

/-- Convenience `Backends` table routing `.direct` to `bedrock2TargetBackend T hints`. -/
@[expose] def bedrock2Backends (T : Target) (hints : Fn → T.toIsa.Hints)
    (designB word : Backend.{0}) : Backends.{0} :=
  ⟨bedrock2TargetBackend T hints, designB, word⟩

theorem bedrock2_unified_sound (cfg : LowerCfg) (t : LegalTarget) (Bs : Backends.{0})
    (p : B2NamedFunc) (s : B2Spec)
    (ds : List (pick Bs (route ((bedrock2FrontendWith cfg).caps p))).D)
    (hrun :
      (unified (bedrock2FrontendWith cfg) t
        (pick Bs (route ((bedrock2FrontendWith cfg).caps p)))).run p = .ok ds)
    (hs : bedrock2Src.Sat p s) :
    Bs.direct.MSat ds ((unified (bedrock2FrontendWith cfg) t Bs.direct).tr p s) :=
  (unified (bedrock2FrontendWith cfg) t Bs.direct).sound p ds s trivial hrun hs

theorem bedrock2_unified_eq_compileFn (cfg : LowerCfg) (T : Target) (t : LegalTarget)
    (hints : Fn → T.toIsa.Hints) {p : B2NamedFunc} {fn : Fn}
    (hlow : (bedrock2FrontendWith cfg).lower.run p = .ok fn)
    (hsupp : (fn.earlyOpt).body.supportsSource t = true) :
    (unified (bedrock2FrontendWith cfg) t (bedrock2TargetBackend T hints)).run p =
      compileFn T.toIsa t (hints (fn.mid t)) fn := by
  rw [unified_eq_legacy]
  dsimp only [bindE, legacyMid, bedrock2TargetBackend]
  rw [hlow]
  simp only [hsupp, ↓reduceIte]
  rfl

theorem bedrock2_unified_target_hostSpec (cfg : LowerCfg) (T : Target) (t : LegalTarget)
    (hints : Fn → T.toIsa.Hints) (p : B2NamedFunc) (s : B2Spec) (ds : List T.Directive)
    (hrun : (unified (bedrock2FrontendWith cfg) t (bedrock2TargetBackend T hints)).run p = .ok ds)
    (hs : bedrock2Src.Sat p s) :
    ∃ fn : Fn,
      (bedrock2FrontendWith cfg).lower.run p = .ok fn ∧
      (fn.earlyOpt).body.supportsSource t = true ∧
      Rega.lowerFn T.toIsa (hints (fn.mid t)) (fn.mid t).ext (fn.mid t) = .ok ds ∧
      bedrock2TargetHostSpec T hints ds (legalTr t fn (bedrock2ToSSpec cfg p s)) (fn.mid t) := by
  have hrun' := hrun
  rw [unified_eq_legacy] at hrun'
  cases hlow : (bedrock2FrontendWith cfg).lower.run p with
  | error e =>
    dsimp only [bindE] at hrun'
    rw [hlow] at hrun'
    cases hrun'
  | ok fn =>
    dsimp only [bindE, legacyMid, bedrock2TargetBackend] at hrun'
    rw [hlow] at hrun'
    by_cases hsupp : (fn.earlyOpt).body.supportsSource t = true
    · simp only [hsupp, ↓reduceIte] at hrun'
      have hmid_run : ((bedrock2FrontendWith cfg).lower ≫ midEnd t).run p = .ok (fn.mid t) := by
        dsimp only [Stage.comp, bindE]
        rw [hlow]
        exact midEnd_run t fn hsupp
      have hmid_tr : ((bedrock2FrontendWith cfg).lower ≫ midEnd t).tr p s =
          legalTr t fn (bedrock2ToSSpec cfg p s) := by
        dsimp only [Stage.comp]
        rw [hlow]
        rfl
      have htr :
          (unified (bedrock2FrontendWith cfg) t (bedrock2TargetBackend T hints)).tr p s =
            legalTr t fn (bedrock2ToSSpec cfg p s) := by
        dsimp only [unified, Stage.comp, Backend.stage]
        rw [hlow]
        dsimp only
        rw [midEnd_run t fn hsupp]
        rfl
      have hmsat :=
        (unified (bedrock2FrontendWith cfg) t (bedrock2TargetBackend T hints)).sound p ds s
          trivial hrun hs
      rw [htr] at hmsat
      have hmid_wf : (fn.mid t).Wf :=
        ((bedrock2FrontendWith cfg).lower ≫ midEnd t).ok p (fn.mid t) trivial hmid_run
      have hmid_sat : ssa.Sat (fn.mid t) (legalTr t fn (bedrock2ToSSpec cfg p s)) := by
        rw [← hmid_tr]
        exact ((bedrock2FrontendWith cfg).lower ≫ midEnd t).sound p (fn.mid t) s trivial
          hmid_run hs
      exact ⟨fn, rfl, hsupp, hrun', hmsat.2 (fn.mid t) hmid_wf hrun' hmid_sat⟩
    · simp only [hsupp, Bool.false_eq_true, ↓reduceIte] at hrun'
      cases hrun'

/-- Source-level `Kraken.Bedrock2` `Spec` induced by `B2Spec.Pre`. -/
@[expose] def B2Spec.toSpec (s : B2Spec) (nm : Sym) (nArgs nRets : Nat) :
    Spec (List.replicate nArgs i64) (List.replicate nRets i64) :=
  fun args m Q _ =>
    ∃ post : Kraken.Bedrock2.Trace 64 → Mem 64 → List (BitVec 64) → Prop,
      s.Pre nm nArgs nRets (tupToList args) m post ∧
      ∀ (resTup : Tup Val (List.replicate nRets i64)) t' m',
        post t' m' (tupToList resTup) → Q resTup m'

private theorem cast_cast_symm {α β : Sort _} (h : α = β) (a : α) :
    cast h.symm (cast h a) = a := by
  subst h; rfl

private theorem eq_cast_of_cast_eq {α β : Sort _} {h : α = β} {a : α} {b : β}
    (he : cast h a = b) : a = cast h.symm b := by
  subst h; exact he

/-- End-to-end `unified bedrock2Frontend` theorem directly connecting `bedrock2Src.Sat p s` to
`T.Defined` and `T.FnSpec` at `s.toSpec` for any `T : Target` and `t : LegalTarget` with
`64 ∈ t.bitWidths` (shared across `Amd64` and `Arm64`). -/
theorem bedrock2_unified_fnSpec (cfg : LowerCfg) (T : Target) (t : LegalTarget)
    (hints : Fn → T.toIsa.Hints) (p : B2NamedFunc) (s : B2Spec) (ds : List T.Directive)
    (hrun : (unified (bedrock2FrontendWith cfg) t (bedrock2TargetBackend T hints)).run p = .ok ds)
    (hs : bedrock2Src.Sat p s) (h64 : 64 ∈ t.bitWidths)
    (h : T.mach.Host) (k₀ n nX : Nat) (bound : Sym → Nat)
    (hinf : ds.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hmid : ∀ fn, (bedrock2FrontendWith cfg).lower.run p = .ok fn →
      Rega.effFrame T.toIsa (hints (fn.mid t)) (fn.mid t).ext ≤ n ∧
      (∀ g as bs, (g, as, bs) ∈ (fn.mid t).ext.callees →
        T.FnSpec h g (legalEnv t (bedrock2Env cfg s.ext s.e) g as bs) (bound g) nX ∧
        Rega.effFrame T.toIsa (hints (fn.mid t)) (fn.mid t).ext +
          T.frame.raBytes + bound g ≤ n) ∧
      (∀ g, g ∈ (fn.mid t).ext.exits → T.Defined h g ∧ nX ≤ n))
    (hn : n + T.frame.raBytes ≤ 2 ^ 64) :
    T.Defined h p.1 ∧
    T.FnSpec h p.1 (s.toSpec p.1 p.2.params.length p.2.rets.length) n nX := by
  obtain ⟨fn, hlow, _, _, hhost⟩ :=
    bedrock2_unified_target_hostSpec cfg T t hints p s ds hrun hs
  obtain ⟨hfr, hcal, hex⟩ := hmid fn hlow
  have hfnEq : fn.name = p.1 ∧
      fn.as = List.replicate p.2.params.length i64 ∧
      fn.rs = List.replicate p.2.rets.length i64 := by
    dsimp only [bedrock2FrontendWith, bedrock2Lower, b2NamedFuncToFn?] at hlow
    cases hfk : Func.fromKraken p.2 with
    | none => simp [hfk] at hlow
    | some fb =>
      simp only [hfk] at hlow
      injection hlow with hlow
      exact ⟨by rw [← hlow], by rw [← hlow], by rw [← hlow]⟩
  rcases hfnEq with ⟨hnm, hasEq, hrsEq⟩
  have has : t.legalSig fn.as = fn.as := by
    rw [hasEq]; exact legalSig_replicate_i64 h64 p.2.params.length
  have hrs : t.legalSig fn.rs = fn.rs := by
    rw [hrsEq]; exact legalSig_replicate_i64 h64 p.2.rets.length
  have hhost' := hhost h k₀ n nX bound hinf hu hfr hn hcal hex
  change T.Defined h fn.name ∧
    T.FnSpec h fn.name
      ((legalTr t fn (bedrock2ToSSpec cfg p s)).C (t.legalSig fn.as) (t.legalSig fn.rs)) n nX
      at hhost'
  rw [hnm] at hhost'
  refine ⟨hhost'.1, fun args m Q X ⟨post, hpre, hpost⟩ st ra R hargs hra hspE hmemS => ?_⟩
  let args₀ : Tup Val fn.as := cast (congrArg (Tup Val) hasEq.symm) args
  let args' : Tup Val (t.legalSig fn.as) := cast (congrArg (Tup Val) has.symm) args₀
  let Q₀ : Post fn.rs := fun ys m' => Q (cast (congrArg (Tup Val) hrsEq) ys) m'
  let Q' : Post (t.legalSig fn.rs) := legalPost t Q₀
  let X' : XPost := legalXPost t (fun _ _ _ _ => False)
  have htr : (legalTr t fn (bedrock2ToSSpec cfg p s)).C
      (t.legalSig fn.as) (t.legalSig fn.rs) args' m Q' X' := by
    refine ⟨rfl, rfl, args₀, Q₀, (fun _ _ _ _ => False), ?_, ?_, rfl, rfl⟩
    · refine ⟨hasEq.symm, hrsEq.symm, post, ?_, ?_⟩
      · change s.Pre p.1 p.2.params.length p.2.rets.length
          (tupToList (cast (congrArg (Tup Val) hasEq) args₀)) m post
        dsimp only [args₀]
        rw [cast_cast_symm]
        exact hpre
      · intro resTup t' m' hp
        dsimp only [Q₀]
        rw [cast_cast_symm]
        exact hpost resTup t' m' hp
    · rw [cast_eq]
      exact encodeTup_eq_cast_of_legalSig_eq has args₀
  have hargs₀ : T.ArgsIn args₀ st := by
    dsimp only [args₀]
    rw [Target.argsIn_cast]
    · exact hargs
    · exact hasEq.symm
  have hargs' : T.ArgsIn args' st := by
    dsimp only [args']
    rw [Target.argsIn_cast]
    · exact hargs₀
    · exact has.symm
  refine eventually_weaken _ _ _ _ ?_
    (hhost'.2 args' m Q' X' htr st ra R hargs' hra hspE hmemS)
  rintro st' (⟨hpc, rets', m', hQ', hrets', hrest, hm'⟩ | ⟨_, _, _, _, ⟨_, _, _, _, hF⟩, _⟩)
  · rcases hQ' with ⟨r₀, hr₀, hQr₀⟩
    have henc : encodeTup t fn.rs r₀ = cast (congrArg (Tup Val) hrs.symm) r₀ :=
      encodeTup_eq_cast_of_legalSig_eq hrs r₀
    rw [henc] at hr₀
    have hreq : r₀ = cast (congrArg (Tup Val) hrs) rets' :=
      eq_cast_of_cast_eq hr₀
    dsimp only [Q₀] at hQr₀
    rw [hreq] at hQr₀
    have hrets₀ : T.RetsIn (cast (congrArg (Tup Val) hrs) rets') (T.mach.data st') :=
      (T.retsIn_cast hrs rets' (T.mach.data st')).mpr hrets'
    have hretsFinal :
        T.RetsIn (cast (congrArg (Tup Val) hrsEq) (cast (congrArg (Tup Val) hrs) rets'))
          (T.mach.data st') :=
      (T.retsIn_cast hrsEq _ (T.mach.data st')).mpr hrets₀
    exact Or.inl ⟨hpc, _, m', hQr₀, hretsFinal, hrest, hm'⟩
  · exact False.elim hF

/-! ## 5. End-to-End `Compiled` & `TargetInit` Theorems (`bedrock2Module`) -/

/-- Whole-module `Compiled` soundness for `bedrock2Module fs externs exits cfg = .ok M`
under `Bedrock2NamesValid` and `extCallees` specs (e.g. `stackalloc` / `interact`). -/
theorem bedrock2Module_compiled_fnSpec {T : Target} {t : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {cfg : LowerCfg} {fs : List B2NamedFunc} {externs : List Extern} {M : Module}
    {hints : List T.toIsa.Hints} {maxBound : Nat}
    (hmod : bedrock2Module fs externs exits cfg = .ok M)
    (C : Compiled T t extCallees exits nX M.fns hints maxBound)
    (ext : Kraken.Bedrock2.ExtSpec 64)
    (hacyc : M.checkAcyclic = true)
    (hval : Bedrock2NamesValid cfg ext fs)
    (hext : ∀ q ∈ extCallees,
      T.FnSpec C.host q.1.1
        (legalEnv t (Env.ofModule M (bedrock2Env cfg ext fs)) q.1.1 q.1.2.1 q.1.2.2) q.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ M.fns.map Fn.name))
    {p : B2NamedFunc} (hp : p ∈ fs) :
    T.Defined C.host p.1 ∧
    T.FnSpec C.host p.1
      (legalEnv t (Env.ofModule M (bedrock2Env cfg ext fs)) p.1
        (t.legalSig (List.replicate p.2.params.length i64))
        (t.legalSig (List.replicate p.2.rets.length i64)))
      (C.bound p.1) nX := by
  have hOk := bedrock2Module_moduleOk hmod hacyc hval
  obtain ⟨_, _, hmem⟩ := bedrock2Module_mem hmod hp
  exact C.fnSpec M rfl C.host (bedrock2Env cfg ext fs) 0 C.code_infix_host C.labelsUnique
    hacyc (bedrock2Module_wf hmod) C.supportsSource
    (fun fn hfn xs m Q X hc =>
      let ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hfn
      (hOk.fnsOk pre fn post hsp).2.2 xs m Q X hc)
    hext hext_uniq (fun _ hg => C.defined_exit_host hg) hmem

/-- Source-signature transfer for `bedrock2Module_compiled_fnSpec` (`64 ∈ t.bitWidths`). -/
theorem bedrock2Module_compiled_fnSpec_src {T : Target} {t : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {cfg : LowerCfg} {fs : List B2NamedFunc} {externs : List Extern} {M : Module}
    {hints : List T.toIsa.Hints} {maxBound : Nat}
    (hmod : bedrock2Module fs externs exits cfg = .ok M)
    (C : Compiled T t extCallees exits nX M.fns hints maxBound)
    (ext : Kraken.Bedrock2.ExtSpec 64)
    (hacyc : M.checkAcyclic = true)
    (hval : Bedrock2NamesValid cfg ext fs)
    (hext : ∀ q ∈ extCallees,
      T.FnSpec C.host q.1.1
        (legalEnv t (Env.ofModule M (bedrock2Env cfg ext fs)) q.1.1 q.1.2.1 q.1.2.2) q.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ M.fns.map Fn.name))
    {p : B2NamedFunc} (hp : p ∈ fs) (h64 : 64 ∈ t.bitWidths) :
    T.Defined C.host p.1 ∧
    T.FnSpec C.host p.1
      (fun args m Q X =>
        bedrock2Env cfg ext fs p.1
          (List.replicate p.2.params.length i64) (List.replicate p.2.rets.length i64)
          args m Q (fun g cs xs m' => X g (t.legalSig cs) (encodeTup t cs xs) m'))
      (C.bound p.1) nX := by
  obtain ⟨hdef, hsp⟩ :=
    bedrock2Module_compiled_fnSpec hmod C ext hacyc hval hext hext_uniq hp
  obtain ⟨fb, _, hmem⟩ := bedrock2Module_mem hmod hp
  have hsig :
      (p.1, List.replicate p.2.params.length i64, List.replicate p.2.rets.length i64) ∈ M.sigs :=
    List.mem_append_left _ (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq
    (legalSig_replicate_i64 h64 p.2.params.length)
    (legalSig_replicate_i64 h64 p.2.rets.length) hsig hsp⟩

/-- End-to-end `TargetInit.run_fnSpec` theorem directly from any `Kraken.Bedrock2.Exec` proof for
`p ∈ fs` compiled through `bedrock2Module` and `Compiled`. -/
theorem bedrock2Module_compiled_run_exec {T : Target} {maxStack maxMem : Nat}
    (I : TargetInit T maxStack maxMem) {t : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {cfg : LowerCfg} {fs : List B2NamedFunc} {externs : List Extern} {M : Module}
    {hints : List T.toIsa.Hints} {maxBound : Nat}
    (hmod : bedrock2Module fs externs exits cfg = .ok M)
    (C : Compiled T t extCallees exits nX M.fns hints maxBound)
    (ext : Kraken.Bedrock2.ExtSpec 64)
    (hacyc : M.checkAcyclic = true)
    (hval : Bedrock2NamesValid cfg ext fs)
    (hext : ∀ q ∈ extCallees,
      T.FnSpec C.host q.1.1
        (legalEnv t (Env.ofModule M (bedrock2Env cfg ext fs)) q.1.1 q.1.2.1 q.1.2.2) q.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ M.fns.map Fn.name))
    {p : B2NamedFunc} (hp : p ∈ fs) (h64 : 64 ∈ t.bitWidths)
    (bsMem : List UInt8) (args : Tup Val (List.replicate p.2.params.length i64))
    (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs (List.replicate p.2.params.length i64)).isSome = true)
    {B : Nat} (hB : B < 2 ^ 64) (t0 : Kraken.Bedrock2.Trace 64)
    {Q : Post (List.replicate p.2.rets.length i64)}
    (hex : Kraken.Bedrock2.Exec ext fs B p.2.body t0 (bsMem.At 0x1000#64)
      ((∅ : Kraken.Bedrock2.Locals 64).insertMany (p.2.params.zip (tupToList args)))
      (fun _ m' l' =>
        ∃ retvs, Kraken.Bedrock2.getMany l' p.2.rets = some retvs ∧
          ∀ resTup : Tup Val (List.replicate p.2.rets.length i64),
            tupToList resTup = retvs → Q resTup m'))
    {post : T.mach.State → Prop}
    (hpost : ∀ st, (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧
        T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (C.bound p.1) ⋆
          Std.ExtHashMap.emp)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step C.host) post
      (T.mach.mkState (I.initState (C.bound p.1) bsMem args)
        (T.mach.labelAddr C.host p.1)) := by
  have hfn := (bedrock2Module_compiled_fnSpec_src hmod C ext hacyc hval hext hext_uniq hp h64).2
  have hacyc' := hacyc
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hacyc'
  obtain ⟨fns, hmap, rfl⟩ := bedrock2Module_eq hmod
  have hndM := Module.namesNodup_of_checkNamesNodup hacyc'.1
  have hndFs : (fs.map Prod.fst).Nodup := by
    rw [← (bedrock2Lower_mapM_spec cfg fs hmap).1]
    exact (List.nodup_append.mp hndM).1
  have hlk := list_lookup_of_nodup hndFs hp
  have hspec :
      bedrock2Env cfg ext fs p.1
        (List.replicate p.2.params.length i64) (List.replicate p.2.rets.length i64)
        args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False) := by
    refine ⟨fun _ _ _ _ hF => hF, Or.inr (Or.inr (Or.inr ⟨B, traceToB t0,
      fun r _ m' => Q r m', hB, ?_, fun _ _ _ h => h⟩))⟩
    refine ⟨p.2, t0, tupToList args, _,
      (fun _ m' l' =>
        ∃ retvs, Kraken.Bedrock2.getMany l' p.2.rets = some retvs ∧
          ∀ resTup : Tup Val (List.replicate p.2.rets.length i64),
            tupToList resTup = retvs → Q resTup m'),
      hlk, traceFromB?_traceToB t0, extTupToList?_replicate args, ?_, hex, ?_⟩
    · simp [Kraken.Bedrock2.putManyZip, tupToList_length]
    · rintro t' m' st1 ⟨retvs, hget, hQ⟩
      have hlen : retvs.length = p.2.rets.length := by
        dsimp only [Kraken.Bedrock2.getMany] at hget
        exact (List.mapM_some_iff hget).symm
      obtain ⟨resTup, hresTup⟩ := exists_listToTup?_of_length hlen
      have hretEq := tupToList_listToTup? hresTup
      exact ⟨retvs, resTup, hget, by simp [hretEq], hQ resTup hretEq⟩
  exact I.run_fnSpec C hfn bsMem args hbs hargs (X := fun _ _ _ _ => False) hspec
    (fun st hst => match hst with
      | .inl h => hpost st h
      | .inr ⟨_, _, _, _, hX, _⟩ => False.elim hX)
    hbound
where
  List.mapM_some_iff {α β : Type} {f : α → Option β} :
      ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.length = ys.length
    | [], ys, h => by simp [List.mapM_nil] at h; subst h; rfl
    | x :: xs, ys, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      rcases h with ⟨y, _, ys', hys', rfl⟩
      exact congrArg Nat.succ (List.mapM_some_iff hys')

/-- End-to-end `TargetInit.run_fnSpec` theorem directly from any `Kraken.Bedrock2.call` proof for
`p ∈ fs` compiled through `bedrock2Module` and `Compiled`. -/
theorem bedrock2Module_compiled_run_call {T : Target} {maxStack maxMem : Nat}
    (I : TargetInit T maxStack maxMem) {t : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {cfg : LowerCfg} {fs : List B2NamedFunc} {externs : List Extern} {M : Module}
    {hints : List T.toIsa.Hints} {maxBound : Nat}
    (hmod : bedrock2Module fs externs exits cfg = .ok M)
    (C : Compiled T t extCallees exits nX M.fns hints maxBound)
    (ext : Kraken.Bedrock2.ExtSpec 64)
    (hacyc : M.checkAcyclic = true)
    (hval : Bedrock2NamesValid cfg ext fs)
    (hext : ∀ q ∈ extCallees,
      T.FnSpec C.host q.1.1
        (legalEnv t (Env.ofModule M (bedrock2Env cfg ext fs)) q.1.1 q.1.2.1 q.1.2.2) q.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ M.fns.map Fn.name))
    {p : B2NamedFunc} (hp : p ∈ fs) (h64 : 64 ∈ t.bitWidths)
    (bsMem : List UInt8) (args : Tup Val (List.replicate p.2.params.length i64))
    (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs (List.replicate p.2.params.length i64)).isSome = true)
    {B : Nat} (hB : B < 2 ^ 64) (t0 : Kraken.Bedrock2.Trace 64)
    {Q : Post (List.replicate p.2.rets.length i64)}
    (hcall : Kraken.Bedrock2.call ext fs B p.1 t0 (bsMem.At 0x1000#64) (tupToList args)
      (fun _ m' retvs =>
        ∀ resTup : Tup Val (List.replicate p.2.rets.length i64),
          tupToList resTup = retvs → Q resTup m'))
    {post : T.mach.State → Prop}
    (hpost : ∀ st, (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧
        T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (C.bound p.1) ⋆
          Std.ExtHashMap.emp)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step C.host) post
      (T.mach.mkState (I.initState (C.bound p.1) bsMem args)
        (T.mach.labelAddr C.host p.1)) := by
  have hacyc' := hacyc
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hacyc'
  obtain ⟨fns, hmap, rfl⟩ := bedrock2Module_eq hmod
  have hndM := Module.namesNodup_of_checkNamesNodup hacyc'.1
  have hndFs : (fs.map Prod.fst).Nodup := by
    rw [← (bedrock2Lower_mapM_spec cfg fs hmap).1]
    exact (List.nodup_append.mp hndM).1
  have hlk := list_lookup_of_nodup hndFs hp
  exact bedrock2Module_compiled_run_exec I hmod C ext hacyc hval hext hext_uniq hp h64
    bsMem args hbs hargs hB t0 (exec_of_kraken_call hlk hcall) hpost hbound

end LeanQbe.T.Unified
