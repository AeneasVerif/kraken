module

public import LeanQbe.T.Xcap.Bridge
public import LeanQbe.T.BedrockWord.Exec
public import LeanQbe.T.Unified.CfgRecovery
public import LeanQbe.T.Unified.CfgContify
public import LeanQbe.T.Main
public import LeanQbe.T.MainCertCore
import LeanQbe.T.Unified.CfgRecoveryLemmas
import LeanQbe.T.Unified.CfgRecoveryProof
import LeanQbe.T.Unified.CfgContifyLemmas
import LeanQbe.T.Unified.CfgContifyProof
import LeanQbe.T.RegaLemmas
import LeanQbe.T.MainLemmas
import LeanQbe.T.TargetLemmas
import LeanQbe.T.MainCertProof

/-!
# Target-Generic CFG Recovery → Concrete `Target.FnSpec` / `Xcap.cptr` Bridge
(`Unified.CfgRecoveryBridge`)

Firewall-clean (`0` arch imports, `0` direct public `*Lemmas*` imports) target-generic bridge
connecting Stage-0 (`checkAndLiftWitness_hybrid_sound` & `checkAndLiftWitness_ro_hybrid_sound`)
and Stage-1 (`checkAndLiftContify_hybrid_sound`) CFG recovery directly to compiled machine-code
verification (`Compiled` + `Rega.lowerFn_correct` + `Xcap.Bridge.fnSpec_to_cptr`) for any
`T : Target` (`x64Target`, `armTarget`, etc.):

* **Option 1A coinductive return-envelope embedding (`embedStep` / `embedTargetSafe`):**
  uniformly handles `.retEnvelope`, single-return `.contified false`, dual-return `.contified true`,
  and `.exit` (`haltSym`) continuations via `cptr (TargetSafe T C host H_mach)`.
* **Compiled region module linking (`compileModule_spec_at`):** discharges `hEntry` directly from
  `Compiled.compileModule_eq`, handling arbitrary acyclic `.contified` callee DAGs inside
  `witEnv` / `witContifyEnv`.
* **Top-level soundness theorems:** `recoverCfg_compiled_sound`,
  `recoverCfg_ro_compiled_sound`, `recoverCfg_contify_compiled_sound`, and their direct
  entry-execution corollaries.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Xcap
open LeanQbe.T.BedrockWord

/-! ## §1. Return-Envelope Decoding & Coinductive `embedTargetSafe` (Option 1A) -/

/-- Extract `(nextPc, nextState)` from the source return tuple of any `RegionAbi`. -/
@[expose] def abiNextPcAndState : (abi : RegionAbi) → BitVec 64 →
    Tup Val abi.retSig → Mem 64 → BitVec 64 × BedrockWord.State
  | .retEnvelope, _, (nextPc, sp, rp, rv, r1, r2, r3, ()), m =>
      (nextPc, ⟨⟨sp, rp, rv, r1, r2, r3⟩, m⟩)
  | .contified false, rp₀, (sp, rp, rv, r1, r2, r3, ()), m =>
      (rp₀, ⟨⟨sp, rp, rv, r1, r2, r3⟩, m⟩)
  | .contified true, rp₀, (isAlt, sp, rp, rv, r1, r2, r3, ()), m =>
      ((if isAlt then rp₀ + 8#64 else rp₀), ⟨⟨sp, rp, rv, r1, r2, r3⟩, m⟩)

/-- Abnormal-exit postcondition specialized to `haltSym` (`[i64]`). -/
@[expose] def haltX (H : HaltPost) : XPost :=
  fun sym' cs xs m' => sym' = haltSym ∧ ∃ (hcs : cs = [i64]), H (hcs ▸ xs).1 m'

/-- Entry-condition predicate connecting abstract `(pc, st)` at a compiled region `sym` with
`T.mach` execution under Option 1A return-envelope `cptr` and `haltSym` exit obligation. -/
@[expose] def RegionEntryCond (T : Target) (C : AddrCodec T) (host : T.mach.Host)
    (lt : LegalTarget) (H : HaltPost) (nX : Nat) (H_mach : T.mach.State → Prop)
    (Ψ : CodeSpec) (sym : Sym) (abi : RegionAbi) (bound : Nat)
    (st : BedrockWord.State) : Prop :=
  ∀ (s : T.mach.MData) (ra : T.mach.Addr) (R : Mem 64 → Prop),
    T.ArgsIn (encodeTup lt regSig st.regs.toRegsV.toTup) s →
    T.frameSpec.raReg s ra →
    T.frameSpec.spEntry (T.mach.getGpr s T.frame.sp) →
    (T.mach.mem s =⋆ Eq st.mem ⋆ T.Entry (T.mach.getGpr s T.frame.sp) ra bound ⋆ R) →
    cptr (TargetSafe T C host H_mach) (C.toBits ra) (fun s' =>
      ∃ (rets : Tup Val (lt.legalSig abi.retSig)) (m' : Mem 64),
        (∃ rets₀ : Tup Val abi.retSig, encodeTup lt abi.retSig rets₀ = rets ∧
          let p := abiNextPcAndState abi st.regs.rp rets₀ m'
          Ψ p.1 p.2) ∧
        T.RetsIn rets s' ∧ T.Restored s s' ∧
        (T.mach.mem s' =⋆ Eq m' ⋆ T.Exit (T.mach.getGpr s T.frame.sp) bound ⋆ R)) →
    (∀ c m' stExit,
      H c m' →
      T.Defined host haltSym →
      T.mach.pc stExit = T.mach.labelAddr host haltSym →
      T.ArgsIn (encodeTup lt [i64] (c, ())) (T.mach.data stExit) →
      T.frameSpec.spEntry (T.mach.getGpr (T.mach.data stExit) T.frame.sp) →
      (∃ ra' n' F, nX ≤ n' ∧ n' + T.frame.raBytes ≤ 2 ^ 64 ∧
        T.frameSpec.raReg (T.mach.data stExit) ra' ∧
        (T.mach.mem (T.mach.data stExit) =⋆
          Eq m' ⋆ T.Entry (T.mach.getGpr (T.mach.data stExit) T.frame.sp) ra' n' ⋆ F ⋆ R)) →
      Eventually (T.mach.step host) H_mach stExit) →
    TargetSafe T C host H_mach (C.toBits (T.mach.labelAddr host sym)) s

/-- Monotone step operator for the greatest fixed point `embedTargetSafe`. -/
@[expose] def embedStep (T : Target) (C : AddrCodec T) (host : T.mach.Host)
    (lt : LegalTarget) (H : HaltPost) (nX : Nat) (H_mach : T.mach.State → Prop)
    (entries : List (BitVec 64 × Sym × RegionAbi × Nat))
    (guard : BitVec 64 → Mem 64 → Prop) (Ψ_res : CodeSpec)
    (Ψ : CodeSpec) : CodeSpec :=
  fun pc st =>
    (∀ e ∈ entries, e.1 = pc →
      guard pc st.mem →
      RegionEntryCond T C host lt H nX H_mach Ψ e.2.1 e.2.2.1 e.2.2.2 st) ∧
    (¬ (entries.any fun e => e.1 == pc) = true → Ψ_res pc st)

/-- Coinductive greatest fixed point `Ψ_cold` connecting verified CFG recovery to
`TargetSafe T C host H_mach` at every compiled region entry and `Ψ_res` on residual blocks. -/
@[expose] def embedTargetSafe (T : Target) (C : AddrCodec T) (host : T.mach.Host)
    (lt : LegalTarget) (H : HaltPost) (nX : Nat) (H_mach : T.mach.State → Prop)
    (entries : List (BitVec 64 × Sym × RegionAbi × Nat))
    (guard : BitVec 64 → Mem 64 → Prop) (Ψ_res : CodeSpec) : CodeSpec :=
  fun pc st => ∃ Ψ, (∀ p s, Ψ p s → embedStep T C host lt H nX H_mach entries guard Ψ_res Ψ p s) ∧
    Ψ pc st

/-- Entry descriptor list for Stage-0 witness `wit` compiled with bound function `bound`. -/
@[expose] def witEntries (wit : CfgWitness) (bound : Sym → Nat) :
    List (BitVec 64 × Sym × RegionAbi × Nat) :=
  wit.regions.map fun rw => (rw.entryPc, rw.name, rw.abi, bound rw.name)

/-- Entry descriptor list for Stage-1 witness `wit` compiled with bound function `bound`. -/
@[expose] def witContifyEntries (wit : ContifyWitness) (bound : Sym → Nat) :
    List (BitVec 64 × Sym × RegionAbi × Nat) :=
  wit.regions.map fun cr => (cr.entryPc, cr.name, cr.abi, bound cr.name)

/-- RO-table memory guard matching `RoPred true wit pc m` using only `CfgRecovery` symbols. -/
@[expose] def roPcGuard (wit : CfgWitness) (pc : BitVec 64) (m : Mem 64) : Prop :=
  ((wit.regions.filter RegionWitness.hasMemTableRo).flatMap RegionWitness.allPcs).contains pc =
    true → WitRoOk wit m

private theorem regionRetPost_iff (abi : RegionAbi) (Ψ : CodeSpec) (rp₀ : BitVec 64)
    (rets : Tup Val abi.retSig) (m : Mem 64) :
    regionRetPost abi Ψ rp₀ rets m ↔
      let p := abiNextPcAndState abi rp₀ rets m
      Ψ p.1 p.2 := by
  cases abi with
  | retEnvelope =>
      rcases rets with ⟨nextPc, sp, rp, rv, r1, r2, r3, ⟨⟩⟩
      exact Iff.rfl
  | contified dualRet =>
      cases dualRet
      · rcases rets with ⟨sp, rp, rv, r1, r2, r3, ⟨⟩⟩
        exact Iff.rfl
      · rcases rets with ⟨isAlt, sp, rp, rv, r1, r2, r3, ⟨⟩⟩
        exact Iff.rfl

private theorem embedStep_mono {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {lt : LegalTarget} {H : HaltPost} {nX : Nat} {H_mach : T.mach.State → Prop}
    {entries : List (BitVec 64 × Sym × RegionAbi × Nat)}
    {guard : BitVec 64 → Mem 64 → Prop} {Ψ_res : CodeSpec}
    {Ψ₁ Ψ₂ : CodeSpec} (hΨ : ∀ p s, Ψ₁ p s → Ψ₂ p s) :
    ∀ pc st, embedStep T C host lt H nX H_mach entries guard Ψ_res Ψ₁ pc st →
      embedStep T C host lt H nX H_mach entries guard Ψ_res Ψ₂ pc st := by
  intro pc st ⟨hEnt, hRes⟩
  refine ⟨fun e he heq hg s ra R ha hra hsp hm hret hexit => ?_, hRes⟩
  refine hEnt e he heq hg s ra R ha hra hsp hm ?_ hexit
  intro s' ⟨rets, m', ⟨rets₀, henc, hp⟩, hrets, hrest, hm'⟩
  exact hret s' ⟨rets, m', ⟨rets₀, henc, hΨ _ _ hp⟩, hrets, hrest, hm'⟩

theorem embedTargetSafe_unfold {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {lt : LegalTarget} {H : HaltPost} {nX : Nat} {H_mach : T.mach.State → Prop}
    {entries : List (BitVec 64 × Sym × RegionAbi × Nat)}
    {guard : BitVec 64 → Mem 64 → Prop} {Ψ_res : CodeSpec}
    {pc : BitVec 64} {st : BedrockWord.State}
    (h : embedTargetSafe T C host lt H nX H_mach entries guard Ψ_res pc st) :
    embedStep T C host lt H nX H_mach entries guard Ψ_res
      (embedTargetSafe T C host lt H nX H_mach entries guard Ψ_res) pc st := by
  rcases h with ⟨Ψ, hΨ, hpc⟩
  exact embedStep_mono (fun p s hp => ⟨Ψ, hΨ, hp⟩) pc st (hΨ pc st hpc)

theorem embedTargetSafe_fold {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {lt : LegalTarget} {H : HaltPost} {nX : Nat} {H_mach : T.mach.State → Prop}
    {entries : List (BitVec 64 × Sym × RegionAbi × Nat)}
    {guard : BitVec 64 → Mem 64 → Prop} {Ψ_res : CodeSpec}
    {pc : BitVec 64} {st : BedrockWord.State}
    (h : embedStep T C host lt H nX H_mach entries guard Ψ_res
      (embedTargetSafe T C host lt H nX H_mach entries guard Ψ_res) pc st) :
    embedTargetSafe T C host lt H nX H_mach entries guard Ψ_res pc st :=
  ⟨fun p s => embedStep T C host lt H nX H_mach entries guard Ψ_res
      (embedTargetSafe T C host lt H nX H_mach entries guard Ψ_res) p s,
   fun p s hp => embedStep_mono (fun _ _ hq => embedTargetSafe_unfold hq) p s hp,
   h⟩

/-- Extract `RegionEntryCond` from `embedTargetSafe` at any compiled entry descriptor. -/
theorem embedTargetSafe_entry {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {lt : LegalTarget} {H : HaltPost} {nX : Nat} {H_mach : T.mach.State → Prop}
    {entries : List (BitVec 64 × Sym × RegionAbi × Nat)}
    {guard : BitVec 64 → Mem 64 → Prop} {Ψ_res : CodeSpec}
    {e : BitVec 64 × Sym × RegionAbi × Nat} (he : e ∈ entries)
    {st : BedrockWord.State}
    (h : embedTargetSafe T C host lt H nX H_mach entries guard Ψ_res e.1 st)
    (hg : guard e.1 st.mem) :
    RegionEntryCond T C host lt H nX H_mach
      (embedTargetSafe T C host lt H nX H_mach entries guard Ψ_res)
      e.2.1 e.2.2.1 e.2.2.2 st :=
  (embedTargetSafe_unfold h).1 e he rfl hg

/-- Extract `Ψ_res` from `embedTargetSafe` at any non-entry residual PC. -/
theorem embedTargetSafe_res {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {lt : LegalTarget} {H : HaltPost} {nX : Nat} {H_mach : T.mach.State → Prop}
    {entries : List (BitVec 64 × Sym × RegionAbi × Nat)}
    {guard : BitVec 64 → Mem 64 → Prop} {Ψ_res : CodeSpec}
    {pc : BitVec 64} {st : BedrockWord.State}
    (hne : ¬ (entries.any fun e => e.1 == pc) = true)
    (h : embedTargetSafe T C host lt H nX H_mach entries guard Ψ_res pc st) :
    Ψ_res pc st :=
  (embedTargetSafe_unfold h).2 hne

/-! ## §2. Compiled Region Module Linking (`compileModule_spec_at`) -/

private theorem find?_pred_bridge {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {x : α}, xs.find? p = some x → p x = true
  | [], _, h => by simp at h
  | y :: ys, x, h => by
      simp only [List.find?] at h
      cases hp : p y with
      | true => simp [hp] at h; subst h; exact hp
      | false => simp [hp] at h; exact find?_pred_bridge h

private theorem defined_of_lowerFn_bridge {T : Target} {host : T.mach.Host}
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

private theorem legalEnv_elim_mid_bridge {lt : LegalTarget} {f : Fn} {Γ_src : Env}
    (hiso : ∀ as bs xs m P E, Γ_src f.name as bs xs m P E → as = f.as ∧ bs = f.rs)
    {xs' : Tup Val (lt.legalSig f.as)} {m : Mem 64} {Q' : Post (lt.legalSig f.rs)} {X' : XPost}
    (h : legalEnv lt Γ_src f.name (lt.legalSig f.as) (lt.legalSig f.rs) xs' m Q' X') :
    ∃ (xs : Tup Val f.as) (P : Post f.rs) (E : XPost),
      encodeTup lt f.as xs = xs' ∧ (∀ r m₁, legalPost lt P r m₁ → Q' r m₁) ∧
      (∀ g cs ys m₁, legalXPost lt E g cs ys m₁ → X' g cs ys m₁) ∧
      Γ_src f.name f.as f.rs xs m P E := by
  rcases h with ⟨as, bs, has, hbs, xs, P, E, hxs, hQ, hX, hΓ⟩
  obtain ⟨rfl, rfl⟩ := hiso as bs xs m P E hΓ
  refine ⟨xs, P, E, ?_, ?_, hX, hΓ⟩
  · simpa only [cast_eq] using hxs
  · intro r m₁ hp; have := hQ r m₁ hp; rwa [cast_eq] at this

private theorem compileFn_mid_spec_bridge {lt : LegalTarget} {f : Fn} (hwf : f.Wf)
    (hsupp : (f.earlyOpt).body.supportsSource lt = true) (Γ_src : Env)
    (hiso : ∀ as bs xs m P E, Γ_src f.name as bs xs m P E → as = f.as ∧ bs = f.rs)
    (hsound : ∀ xs m P E, Γ_src f.name f.as f.rs xs m P E → Func.spec Γ_src f.body xs m P E) :
    ∀ xs' m Q' X',
      legalEnv lt Γ_src f.name (lt.legalSig f.as) (lt.legalSig f.rs) xs' m Q' X' →
      Func.spec (legalEnv lt Γ_src) (f.mid lt).body xs' m Q' X' := by
  intro xs' m Q' X' h
  have hel := legalEnv_elim_mid_bridge hiso h
  exact @fn_mid_spec lt f hwf hsupp Γ_src hel.choose xs'
    hel.choose_spec.choose_spec.choose_spec.1 m
    hel.choose_spec.choose hel.choose_spec.choose_spec.choose Q' X'
    hel.choose_spec.choose_spec.choose_spec.2.1
    hel.choose_spec.choose_spec.choose_spec.2.2.1
    (hsound _ m _ _ hel.choose_spec.choose_spec.choose_spec.2.2.2)

private theorem compileModule_bounds_map_fst {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {exits : List Sym} {nX : Nat} :
    ∀ {extCallees : List (SigEntry × Nat)} {fs : List Fn} {hints : List I.Hints}
      {code : List I.Directive} {bounds : List (Sym × Nat)},
      compileModule I lt raBytes extCallees exits nX fs hints = .ok (code, bounds) →
      bounds.map Prod.fst = fs.map Fn.name
  | _, [], [], _, _, h => by dsimp only [compileModule] at h; cases h; rfl
  | _, [], _ :: _, _, _, h => by dsimp only [compileModule] at h; cases h
  | _, _ :: _, [], _, _, h => by dsimp only [compileModule] at h; cases h
  | extCallees, f :: fs, hint :: hints, _, _, h => by
      have hsupp := compileModule_cons_supportsSource h
      rw [compileModule_cons_mid hsupp] at h
      cases hl : Rega.lowerFn I hint (f.mid lt).ext (f.mid lt) with
      | error _ => simp only [hl] at h; cases h
      | ok c =>
          cases hchk : checkAndBoundExt I raBytes exits nX extCallees hint (f.mid lt).ext with
          | none => simp only [hl, hchk] at h; cases h
          | some b =>
              simp only [hl, hchk] at h
              cases hrest : compileModule I lt raBytes (((f.mid lt).sig, b) :: extCallees)
                  exits nX fs hints with
              | error _ => simp only [hrest] at h; cases h
              | ok res =>
                  rcases res with ⟨cs, bs⟩
                  simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
                  rcases h with ⟨_, rfl⟩
                  simpa using compileModule_bounds_map_fst hrest

private theorem compileModule_spec_at (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (Γ_src : Env) (exits : List Sym) (nX : Nat)
    (hexits : ∀ g ∈ exits, T.Defined host g) :
    ∀ {fs : List Fn} {hints : List T.toIsa.Hints} {extCallees : List (SigEntry × Nat)}
      {code : List T.Directive} {bounds : List (Sym × Nat)} {k₀ : Nat},
      compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints = .ok (code, bounds) →
      code.IsInfixAt (T.mach.prog host) k₀ → T.LabelsUnique host → (fs.map Fn.name).Nodup →
      (∀ f ∈ fs, f.Wf) →
      (∀ p ∈ extCallees,
        T.FnSpec host p.1.1 (legalEnv lt Γ_src p.1.1 p.1.2.1 p.1.2.2) p.2 nX) →
      (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) →
      (∀ p ∈ extCallees, p.1.1 ∉ fs.map Fn.name) →
      (∀ f ∈ fs, ∀ as bs xs m P E, Γ_src f.name as bs xs m P E →
        ∃ (h₁ : as = f.as) (h₂ : bs = f.rs),
          Func.spec Γ_src f.body (h₁ ▸ xs) m (h₂ ▸ P) E) →
      ∀ {f : Fn}, f ∈ fs →
        ∃ b, (f.name, b) ∈ bounds ∧ T.Defined host f.name ∧
          T.FnSpec host f.name (Func.spec (legalEnv lt Γ_src) (f.mid lt).body) b nX
  | [], [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, hf => nomatch hf
  | [], _ :: _, _, _, _, _, hcm, _, _, _, _, _, _, _, _, _, _ => by
      dsimp only [compileModule] at hcm; cases hcm
  | _ :: _, [], _, _, _, _, hcm, _, _, _, _, _, _, _, _, _, _ => by
      dsimp only [compileModule] at hcm; cases hcm
  | f :: fs, hint :: hints, extCallees, code, bounds, k₀, hcm, hc, hu, hfsnd, hwfAll,
      hext, hext_eq, hext_disj, hΓ, g, hg => by
      simp only [List.map_cons, List.nodup_cons] at hfsnd
      have hsupp := compileModule_cons_supportsSource hcm
      rw [compileModule_cons_mid hsupp] at hcm
      cases hl : Rega.lowerFn T.toIsa hint (f.mid lt).ext (f.mid lt) with
      | error _ => simp only [hl] at hcm; cases hcm
      | ok c =>
          cases hchk : checkAndBoundExt T.toIsa T.frame.raBytes exits nX extCallees hint
              (f.mid lt).ext with
          | none => simp only [hl, hchk] at hcm; cases hcm
          | some b =>
              simp only [hl, hchk] at hcm
              cases hrest : compileModule T.toIsa lt T.frame.raBytes
                  (((f.mid lt).sig, b) :: extCallees) exits nX fs hints with
              | error _ => simp only [hrest] at hcm; cases hcm
              | ok res =>
                  rcases res with ⟨cs, bs⟩
                  simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at hcm
                  rcases hcm with ⟨rfl, rfl⟩
                  obtain ⟨hc_inf, hcs_inf⟩ := List.IsInfixAt.append hc
                  obtain ⟨hfr, hn, hcal_b, hex_b⟩ := checkAndBoundExt_spec hchk
                  let bound : Sym → Nat := fun nm =>
                    match extCallees.find? (fun q => q.1.1 == nm) with
                    | some q => q.2
                    | none => 0
                  have hcal : ∀ nm as bs', (nm, as, bs') ∈ (f.mid lt).ext.callees →
                      T.FnSpec host nm (legalEnv lt Γ_src nm as bs') (bound nm) nX ∧
                      Rega.effFrame T.toIsa hint (f.mid lt).ext + T.frame.raBytes +
                        bound nm ≤ b := by
                    intro nm as bs' hnm
                    obtain ⟨bg, hlk, hle⟩ := hcal_b (nm, as, bs') hnm
                    have hmem : ((nm, as, bs'), bg) ∈ extCallees := lookupBound_mem hlk
                    have hbd_eq : bound nm = bg := by
                      dsimp only [bound]
                      cases hfnd : extCallees.find? (fun q => q.1.1 == nm) with
                      | none =>
                          exfalso
                          have hnot := List.find?_eq_none.mp hfnd ((nm, as, bs'), bg) hmem
                          simp at hnot
                      | some q =>
                          have hqmem : q ∈ extCallees := List.mem_of_find?_eq_some hfnd
                          have hpred : q.1.1 = nm := beq_iff_eq.mp
                            (find?_pred_bridge (p := fun q : SigEntry × Nat => q.1.1 == nm) hfnd)
                          exact hext_eq q hqmem ((nm, as, bs'), bg) hmem hpred
                    rw [hbd_eq]; exact ⟨hext ((nm, as, bs'), bg) hmem, hle⟩
                  have hex : ∀ nm, nm ∈ (f.mid lt).ext.exits → T.Defined host nm ∧ nX ≤ b :=
                    fun nm hnm => ⟨hexits nm (hex_b nm hnm).1, (hex_b nm hnm).2⟩
                  have hfdef : T.Defined host f.name :=
                    defined_of_lowerFn_bridge (f := f.mid lt) hl hc_inf
                  have hfspec_mid :
                      T.FnSpec host f.name (Func.spec (legalEnv lt Γ_src) (f.mid lt).body) b nX :=
                    Rega.lowerFn_correct T host hint (f.mid lt).ext (f.mid lt)
                      (legalEnv lt Γ_src) b nX bound (fn_mid_wf (hwfAll f List.mem_cons_self))
                      hl hc_inf hu hfr hn hcal hex
                  rcases List.mem_cons.mp hg with rfl | hg'
                  · exact ⟨b, List.mem_cons_self, hfdef, hfspec_mid⟩
                  · have hf_iso : ∀ as bs xs m P E, Γ_src f.name as bs xs m P E →
                        as = f.as ∧ bs = f.rs := fun as bs xs m P E h =>
                      let ⟨h1, h2, _⟩ := hΓ f List.mem_cons_self as bs xs m P E h; ⟨h1, h2⟩
                    have hf_sound : ∀ xs m P E, Γ_src f.name f.as f.rs xs m P E →
                        Func.spec Γ_src f.body xs m P E := fun xs m P E h => by
                      rcases hΓ f List.mem_cons_self f.as f.rs xs m P E h with ⟨_, _, hSp⟩
                      exact hSp
                    have hfspec_leg : T.FnSpec host f.name
                        (legalEnv lt Γ_src f.name (lt.legalSig f.as) (lt.legalSig f.rs)) b nX :=
                      fun args m Q X hC =>
                        hfspec_mid args m Q X
                          (compileFn_mid_spec_bridge (hwfAll f List.mem_cons_self) hsupp
                            Γ_src hf_iso hf_sound args m Q X hC)
                    have hext' : ∀ q ∈ ((f.mid lt).sig, b) :: extCallees,
                        T.FnSpec host q.1.1
                          (legalEnv lt Γ_src q.1.1 q.1.2.1 q.1.2.2) q.2 nX := by
                      intro q hq
                      rcases List.mem_cons.mp hq with rfl | hq'
                      · exact hfspec_leg
                      · exact hext q hq'
                    have hext_disj' : ∀ q ∈ ((f.mid lt).sig, b) :: extCallees,
                        q.1.1 ∉ fs.map Fn.name := by
                      intro q hq hmem
                      rcases List.mem_cons.mp hq with rfl | hq'
                      · exact hfsnd.1 hmem
                      · exact hext_disj q hq' (List.mem_cons_of_mem f.name hmem)
                    have hext_eq' : ∀ q₁ ∈ ((f.mid lt).sig, b) :: extCallees,
                        ∀ q₂ ∈ ((f.mid lt).sig, b) :: extCallees,
                          q₁.1.1 = q₂.1.1 → q₁.2 = q₂.2 := by
                      intro q₁ hq₁ q₂ hq₂ hsym
                      rcases List.mem_cons.mp hq₁ with rfl | hq₁' <;>
                        rcases List.mem_cons.mp hq₂ with rfl | hq₂'
                      · rfl
                      · exact absurd (hsym.symm ▸ List.mem_cons_self) (hext_disj q₂ hq₂')
                      · exact absurd (hsym ▸ List.mem_cons_self) (hext_disj q₁ hq₁')
                      · exact hext_eq q₁ hq₁' q₂ hq₂' hsym
                    obtain ⟨bg, hbgMem, hgdef, hgspec⟩ :=
                      compileModule_spec_at T host lt Γ_src exits nX hexits hrest hcs_inf hu
                        hfsnd.2 (fun x hx => hwfAll x (List.mem_cons_of_mem f hx))
                        hext' hext_eq' hext_disj' (fun x hx => hΓ x (List.mem_cons_of_mem f hx)) hg'
                    exact ⟨bg, List.mem_cons_of_mem (f.name, b) hbgMem, hgdef, hgspec⟩

private theorem compiled_lift_fnSpec {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T lt [] exits nX fs hints maxBound)
    (Γ_src : Env) (hnd : (fs.map Fn.name).Nodup) (hwf : ∀ f ∈ fs, f.Wf)
    (hΓ : ∀ f ∈ fs, ∀ as bs xs m P E, Γ_src f.name as bs xs m P E →
      ∃ (h₁ : as = f.as) (h₂ : bs = f.rs), Func.spec Γ_src f.body (h₁ ▸ xs) m (h₂ ▸ P) E)
    {f : Fn} (hf : f ∈ fs) :
    T.FnSpec M.host f.name (Func.spec (legalEnv lt Γ_src) (f.mid lt).body) (M.bound f.name) nX := by
  obtain ⟨b, hbMem, _, hspec⟩ := compileModule_spec_at T M.host lt Γ_src exits nX
    (fun _ hg => M.defined_exit_host hg) M.compileModule_eq M.code_infix_host M.labelsUnique
    hnd hwf (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h) hΓ hf
  have hMapFst : M.bounds.map Prod.fst = fs.map Fn.name :=
    compileModule_bounds_map_fst M.compileModule_eq
  have hNdB : (M.bounds.map Prod.fst).Nodup := hMapFst ▸ hnd
  have hBoundEq : M.bound f.name = b := by
    dsimp only [Compiled.bound]
    rw [lookupFnBound_of_mem_nodup hNdB hbMem]
    rfl
  exact hBoundEq ▸ hspec

/-! ## §3. Environment Soundness & Disjointness Helpers -/

private theorem witEnvAux_not_mem (cm : CodeMap) (Γ : Env) :
    ∀ (rws : List RegionWitness) (nm : Sym), nm ∉ rws.map RegionWitness.name →
      ∀ as bs xs m P E, witEnvAux cm Γ rws nm as bs xs m P E → Γ nm as bs xs m P E
  | [], _, _, _, _, _, _, _, _, h => h
  | r :: rs, nm, hnm, as, bs, xs, m, P, E, h => by
      have hne : nm ≠ r.name := fun he => hnm (by simp [he])
      have hnot : nm ∉ rs.map RegionWitness.name := fun hm => hnm (by simp [hm])
      have hg := witEnvAux_not_mem cm _ rs nm hnot as bs xs m P E h
      rcases hg with ⟨_, rfl, _⟩ | hbase
      · exact absurd rfl hne
      · exact hbase

private theorem witEnvAux_mono_right' (cm : CodeMap) (Γ : Env) :
    ∀ rws f as bs xs m P E, Γ f as bs xs m P E → witEnvAux cm Γ rws f as bs xs m P E
  | [], _, _, _, _, _, _, _, h => h
  | _ :: rws, f, as, bs, xs, m, P, E, h =>
      witEnvAux_mono_right' cm _ rws f as bs xs m P E (Or.inr h)

private theorem witEnvAux_elim (cm : CodeMap) :
    ∀ (rws : List RegionWitness) (Γ₀ : Env),
      (rws.map RegionWitness.name).Nodup →
      (∀ rw ∈ rws, ∀ as bs xs m P E, Γ₀ rw.name as bs xs m P E → False) →
      ∀ rw ∈ rws, ∀ as bs xs m P E,
        witEnvAux cm Γ₀ rws rw.name as bs xs m P E →
        ∃ (h₁ : as = (liftRegion cm rw).as) (h₂ : bs = (liftRegion cm rw).rs),
          Func.spec (witEnvAux cm Γ₀ rws) (liftRegion cm rw).body (h₁ ▸ xs) m (h₂ ▸ P) E
  | [], _, _, _, _, hrw, _, _, _, _, _, _, _ => nomatch hrw
  | r :: rs, Γ₀, hnd, hbase, rw, hrw, as, bs, xs, m, P, E, h => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hrw with rfl | hrw'
      · have hg := witEnvAux_not_mem cm _ rs rw.name hnd.1 as bs xs m P E h
        rcases hg with ⟨_, _, h₁, h₂, hSp⟩ | hg0
        · subst h₁; subst h₂
          refine ⟨rfl, rfl, Func.spec_env_mono (fun g cs ds ys m' P' E' hm => ?_) hSp⟩
          exact witEnvAux_mono_right' cm _ rs g cs ds ys m' P' E' (Or.inr hm)
        · exact absurd hg0 (hbase rw List.mem_cons_self as bs xs m P E)
      · have hbase' : ∀ rw' ∈ rs, ∀ as bs xs m P E,
            (fun f as bs xs m P E =>
              ((∃ dualRet, r.abi = .contified dualRet) ∧ f = r.name ∧
                ∃ (h₁ : as = (liftRegion cm r).as) (h₂ : bs = (liftRegion cm r).rs),
                  Func.spec Γ₀ (liftRegion cm r).body (h₁ ▸ xs) m (h₂ ▸ P) E) ∨
              Γ₀ f as bs xs m P E) rw'.name as bs xs m P E → False := by
          intro rw' hrw'' as' bs' xs' m' P' E' hg
          have hne' : rw'.name ≠ r.name := fun he => hnd.1 (he ▸ List.mem_map_of_mem hrw'')
          rcases hg with ⟨_, heqN, _⟩ | hg0
          · exact absurd heqN hne'
          · exact hbase rw' (List.mem_cons_of_mem r hrw'') as' bs' xs' m' P' E' hg0
        exact witEnvAux_elim cm rs _ hnd.2 hbase' rw hrw' as bs xs m P E h

private theorem witContifyEnvAux_not_mem (cm : CodeMap) (Γ : Env) :
    ∀ (crs : List ContifyRegion) (nm : Sym), nm ∉ crs.map ContifyRegion.name →
      ∀ as bs xs m P E, witContifyEnvAux cm Γ crs nm as bs xs m P E → Γ nm as bs xs m P E
  | [], _, _, _, _, _, _, _, _, h => h
  | c :: cs, nm, hnm, as, bs, xs, m, P, E, h => by
      have hne : nm ≠ c.name := fun he => hnm (by simp [he])
      have hnot : nm ∉ cs.map ContifyRegion.name := fun hm => hnm (by simp [hm])
      have hg := witContifyEnvAux_not_mem cm _ cs nm hnot as bs xs m P E h
      rcases hg with ⟨_, rfl, _⟩ | hbase
      · exact absurd rfl hne
      · exact hbase

private theorem witContifyEnvAux_elim (cm : CodeMap) :
    ∀ (crs : List ContifyRegion) (Γ₀ : Env),
      (crs.map ContifyRegion.name).Nodup →
      (∀ cr ∈ crs, ∀ as bs xs m P E, Γ₀ cr.name as bs xs m P E → False) →
      ∀ cr ∈ crs, ∀ as bs xs m P E,
        witContifyEnvAux cm Γ₀ crs cr.name as bs xs m P E →
        ∃ (h₁ : as = (liftContifyRegion cm cr).as) (h₂ : bs = (liftContifyRegion cm cr).rs),
          Func.spec (witContifyEnvAux cm Γ₀ crs) (liftContifyRegion cm cr).body
            (h₁ ▸ xs) m (h₂ ▸ P) E
  | [], _, _, _, _, hcr, _, _, _, _, _, _, _ => nomatch hcr
  | c :: cs, Γ₀, hnd, hbase, cr, hcr, as, bs, xs, m, P, E, h => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hcr with rfl | hcr'
      · have hg := witContifyEnvAux_not_mem cm _ cs cr.name hnd.1 as bs xs m P E h
        rcases hg with ⟨_, _, h₁, h₂, hSp⟩ | hg0
        · subst h₁; subst h₂
          refine ⟨rfl, rfl, Func.spec_env_mono (fun g cs' ds ys m' P' E' hm => ?_) hSp⟩
          exact witContifyEnvAux_mono_right cm _ cs g cs' ds ys m' P' E' (Or.inr hm)
        · exact absurd hg0 (hbase cr List.mem_cons_self as bs xs m P E)
      · have hbase' : ∀ cr' ∈ cs, ∀ as bs xs m P E,
            (fun f as bs xs m P E =>
              ((∃ dualRet, c.abi = .contified dualRet) ∧ f = c.name ∧
                ∃ (h₁ : as = (liftContifyRegion cm c).as) (h₂ : bs = (liftContifyRegion cm c).rs),
                  Func.spec Γ₀ (liftContifyRegion cm c).body (h₁ ▸ xs) m (h₂ ▸ P) E) ∨
              Γ₀ f as bs xs m P E) cr'.name as bs xs m P E → False := by
          intro cr' hcr'' as' bs' xs' m' P' E' hg
          have hne' : cr'.name ≠ c.name := fun he => hnd.1 (he ▸ List.mem_map_of_mem hcr'')
          rcases hg with ⟨_, heqN, _⟩ | hg0
          · exact absurd heqN hne'
          · exact hbase cr' (List.mem_cons_of_mem c hcr'') as' bs' xs' m' P' E' hg0
        exact witContifyEnvAux_elim cm cs _ hnd.2 hbase' cr hcr' as bs xs m P E h

private theorem nodup_flatMap_disjoint {α β : Type} (f : α → List β) :
    ∀ {xs : List α}, (xs.flatMap f).Nodup →
      ∀ {a b}, a ∈ xs → b ∈ xs → a ≠ b → ∀ p, p ∈ f a → p ∉ f b
  | [], _, _, _, ha, _, _, _, _, _ => nomatch ha
  | _ :: xs, hnd, a, b, ha, hb, hne, p, hpa, hpb => by
      rw [List.flatMap_cons, List.nodup_append] at hnd
      rcases hnd with ⟨_, hndXs, hDisj⟩
      rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact hDisj p hpa p (List.mem_flatMap.2 ⟨b, hb', hpb⟩) rfl
      · exact hDisj p hpb p (List.mem_flatMap.2 ⟨a, ha', hpa⟩) rfl
      · exact nodup_flatMap_disjoint f hndXs ha' hb' hne p hpa hpb

private theorem nodup_flatMap_inj {α β : Type} (f : α → List β) (g : α → β)
    {xs : List α} (hg : ∀ a ∈ xs, g a ∈ f a) (hnd : (xs.flatMap f).Nodup)
    {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) (heq : g a = g b) : a = b :=
  Classical.byContradiction fun hne =>
    nodup_flatMap_disjoint f hnd ha hb hne (g a) (hg a ha) (heq ▸ hg b hb)

private theorem groupTree_entryPc_mem_allPcs_stage0 (cm : CodeMap) (rw : RegionWitness)
    (callees : List CalleeMeta) :
    ∀ (pcs : List (BitVec 64)) (g : GroupTree),
      checkGroupNode cm rw callees pcs g = true → g.entryPc ∈ g.allPcs
  | _, .leaf pc, _ => by simp only [GroupTree.entryPc, GroupTree.allPcs]; exact List.mem_cons_self
  | pcs, .loop header nodes, hchk => by
      dsimp only [checkGroupNode] at hchk; simp only [Bool.and_eq_true] at hchk
      have hin : header ∈ nodes.map GroupTree.entryPc := by simpa using hchk.1.2
      rcases List.mem_map.1 hin with ⟨c, hcMem, hcEq⟩
      have hsub := groupTree_entryPc_mem_allPcs_stage0 cm rw callees
        (pushLabelPcs (nodes.map GroupTree.entryPc) pcs) c
        (checkGroupNodes_forall cm rw callees _ nodes hchk.2 c hcMem)
      rw [hcEq] at hsub
      simp only [GroupTree.entryPc, GroupTree.allPcs]
      exact List.mem_flatMap.2 ⟨c, hcMem, hsub⟩

private theorem checkAux_mem_stage0 (cm : CodeMap) :
    ∀ (rws : List RegionWitness) (callees : List CalleeMeta),
      CfgWitness.checkAux cm callees rws = true →
      ∀ rw ∈ rws, rw.entryPc ∈ rw.allPcs
  | [], _, _, _, hrw => nomatch hrw
  | r :: rs, callees, hchk, rw, hrw => by
      dsimp only [CfgWitness.checkAux] at hchk; simp only [Bool.and_eq_true] at hchk
      rcases List.mem_cons.mp hrw with rfl | hrw'
      · have hr := hchk.1
        dsimp only [RegionWitness.check] at hr; simp only [Bool.and_eq_true] at hr
        have hin : rw.entryPc ∈ rw.tree.map GroupTree.entryPc := by simpa using hr.1.1.1.1.2
        rcases List.mem_map.1 hin with ⟨g, hgMem, hgEq⟩
        have hm := groupTree_entryPc_mem_allPcs_stage0 cm rw callees _ g
          (checkGroupNodes_forall cm rw callees _ rw.tree hr.1.1.2 g hgMem)
        rw [hgEq] at hm
        exact List.mem_flatMap.2 ⟨g, hgMem, hm⟩
      · exact checkAux_mem_stage0 cm rs _ hchk.2 rw hrw'

private theorem groupTree_entryPc_mem_allPcs_stage1 (cm : CodeMap) (cr : ContifyRegion)
    (callees : List ContCalleeMeta) :
    ∀ (pcs : List (BitVec 64)) (g : GroupTree),
      checkContGroupNode cm cr callees pcs g = true → g.entryPc ∈ g.allPcs
  | _, .leaf pc, _ => by simp only [GroupTree.entryPc, GroupTree.allPcs]; exact List.mem_cons_self
  | pcs, .loop header nodes, hchk => by
      dsimp only [checkContGroupNode] at hchk; simp only [Bool.and_eq_true] at hchk
      have hin : header ∈ nodes.map GroupTree.entryPc := by simpa using hchk.1.2
      rcases List.mem_map.1 hin with ⟨c, hcMem, hcEq⟩
      have hsub := groupTree_entryPc_mem_allPcs_stage1 cm cr callees
        (pushLabelPcs (nodes.map GroupTree.entryPc) pcs) c
        (checkContGroupNodes_forall cm cr callees _ nodes hchk.2 c hcMem)
      rw [hcEq] at hsub
      simp only [GroupTree.entryPc, GroupTree.allPcs]
      exact List.mem_flatMap.2 ⟨c, hcMem, hsub⟩

private theorem checkAux_mem_stage1 (cm : CodeMap) :
    ∀ (crs : List ContifyRegion) (callees : List ContCalleeMeta),
      ContifyWitness.checkAux cm callees crs = true →
      ∀ cr ∈ crs, cr.entryPc ∈ cr.allPcs
  | [], _, _, _, hcr => nomatch hcr
  | c :: cs, callees, hchk, cr, hcr => by
      dsimp only [ContifyWitness.checkAux] at hchk; simp only [Bool.and_eq_true] at hchk
      rcases List.mem_cons.mp hcr with rfl | hcr'
      · have hc := hchk.1
        dsimp only [ContifyRegion.check] at hc; simp only [Bool.and_eq_true] at hc
        have hin : cr.entryPc ∈ cr.tree.map GroupTree.entryPc := by
          simpa using hc.1.1.1.1.2
        rcases List.mem_map.1 hin with ⟨g, hgMem, hgEq⟩
        have hm := groupTree_entryPc_mem_allPcs_stage1 cm cr callees _ g
          (checkContGroupNodes_forall cm cr callees _ cr.tree hc.1.1.2 g hgMem)
        rw [hgEq] at hm
        exact List.mem_flatMap.2 ⟨g, hgMem, hm⟩
      · exact checkAux_mem_stage1 cm cs _ hchk.2 cr hcr'

private theorem regionEntry_to_targetSafe {T : Target} {C : AddrCodec T}
    {M_host : T.mach.Host} {lt : LegalTarget} {H : HaltPost} {nX : Nat}
    {H_mach : T.mach.State → Prop} {entries : List (BitVec 64 × Sym × RegionAbi × Nat)}
    {guard : BitVec 64 → Mem 64 → Prop} {Ψ_res : CodeSpec}
    {sym : Sym} {abi : RegionAbi} {b : Nat}
    {Γ_legal : Env} {body : Func (lt.legalSig regSig) (lt.legalSig abi.retSig)}
    {Ψ_hyb : CodeSpec} {r₀ : BedrockWord.Regs} {m₀ : Mem 64}
    (hHyb : ∀ pc st, Ψ_hyb pc st →
      embedTargetSafe T C M_host lt H nX H_mach entries guard Ψ_res pc st)
    (hfn : T.FnSpec M_host sym (Func.spec Γ_legal body) b nX)
    (hMid : Func.spec Γ_legal body (encodeTup lt regSig r₀.toRegsV.toTup) m₀
      (legalPost lt (regionRetPost abi Ψ_hyb r₀.rp)) (legalXPost lt (haltX H))) :
    RegionEntryCond T C M_host lt H nX H_mach
      (embedTargetSafe T C M_host lt H nX H_mach entries guard Ψ_res)
      sym abi b ⟨r₀, m₀⟩ := by
  intro s ra R hargs hra hsp hmem hret hexit
  dsimp only [TargetSafe]
  rw [C.of_to]
  apply TargetSafe.bind (C := C)
  refine eventually_weaken (T.mach.step M_host) _ _ _ ?_
    (hfn (encodeTup lt regSig r₀.toRegsV.toTup) m₀
      (legalPost lt (regionRetPost abi Ψ_hyb r₀.rp)) (legalXPost lt (haltX H))
      hMid s ra R hargs hra hsp hmem)
  rintro st (⟨hpc, rets, m', hQ, hrets, hrest, hm'⟩ |
    ⟨sym', cs', xs', m', hX, hdef, hpc, hxs, hsp', ra', n', F, hnX, hbd, hra', hm'⟩)
  · rcases hQ with ⟨rets₀, rfl, hRetP⟩
    have hPsi := (regionRetPost_iff abi Ψ_hyb r₀.rp rets₀ m').1 hRetP
    have hSafeRa := hret (T.mach.data st)
      ⟨encodeTup lt abi.retSig rets₀, m', ⟨rets₀, rfl, hHyb _ _ hPsi⟩, hrets, hrest, hm'⟩
    rw [← hpc] at hSafeRa
    exact hSafeRa
  · rcases hX with ⟨cs, hcs, xs, hxsEq, rfl, hcsEq, hH⟩
    cases hcsEq
    cases hcs
    rcases xs with ⟨c, ⟨⟩⟩
    have hCastEq : encodeTup lt [i64] (c, ()) = xs' := by simpa using hxsEq
    have hEv := hexit c m' st hH hdef hpc (hCastEq ▸ hxs) hsp' ⟨ra', n', F, hnX, hbd, hra', hm'⟩
    dsimp only [TargetSafe]
    rw [C.of_to, T.mach.mk_eta]
    exact hEv

/-! ## §4. Top-Level Stage-0, Stage-0-RO & Stage-1 Compiled Soundness Theorems -/

/-- **Stage-0 End-to-End Compiled Soundness:** connects `checkAndLiftWitness` + `Compiled` on any
`T : Target` to `embedTargetSafe` (and `TargetSafe T C M.host H_mach` at every region entry). -/
theorem recoverCfg_compiled_sound {T : Target} (C : AddrCodec T) {lt : LegalTarget}
    (cm : CodeMap) (wit : CfgWitness) (H : HaltPost) (H_mach : T.mach.State → Prop)
    {exits : List Sym} {nX : Nat} {hints : List T.toIsa.Hints} {maxBound : Nat}
    {fns : List Fn} {wRes : CodeMap}
    (hLift : checkAndLiftWitness cm wit = .ok (fns, wRes))
    (M : Compiled T lt [] exits nX fns hints maxBound)
    (Ψ_res : CodeSpec)
    (hRes : SpecsClosed wRes cm.symEnv
      (embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
        (fun _ _ => True) Ψ_res) H)
    (hDrop : ∀ rw ∈ wit.regions, rw.retainFallbacks = false →
      ∀ pc ∈ rw.allPcs, pc ≠ rw.entryPc → ∀ st, Ψ_res pc st)
    (hNoRo : wit.hasMemTableRo = false := by decide) :
    (∃ Ψ_hyb : CodeSpec, SpecsClosed cm cm.symEnv Ψ_hyb H ∧
      ∀ pc st, Ψ_hyb pc st →
        embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
          (fun _ _ => True) Ψ_res pc st) ∧
      ∀ pc₀ st₀, cm.wp H pc₀ st₀ →
        embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
          (fun _ _ => True) Ψ_res pc₀ st₀ := by
  have hLift' := hLift
  dsimp only [checkAndLiftWitness] at hLift'
  split at hLift'
  · rename_i hChk
    cases hLift'
    have hChk' := hChk
    dsimp only [CfgWitness.check] at hChk'
    simp only [Bool.and_eq_true] at hChk'
    have hNameNd : (wit.regions.map RegionWitness.name).Nodup := listNodup_nodup hChk'.1.1
    have hAllNd : (wit.regions.flatMap RegionWitness.allPcs).Nodup := listNodup_nodup hChk'.1.2
    have hEntMem : ∀ rw ∈ wit.regions, rw.entryPc ∈ rw.allPcs :=
      checkAux_mem_stage0 cm wit.regions [] hChk'.2
    have hFsNd : ((wit.regions.map (liftRegion cm)).map Fn.name).Nodup := by
      rw [List.map_map]; exact hNameNd
    have hWfAll : ∀ f ∈ wit.regions.map (liftRegion cm), f.Wf := by
      intro f hf
      rcases List.mem_map.1 hf with ⟨rw, _, rfl⟩
      exact liftRegion_wf cm rw
    have hΓ : ∀ f ∈ wit.regions.map (liftRegion cm), ∀ as bs xs m P E,
        witEnv cm wit f.name as bs xs m P E →
        ∃ (h₁ : as = f.as) (h₂ : bs = f.rs),
          Func.spec (witEnv cm wit) f.body (h₁ ▸ xs) m (h₂ ▸ P) E := by
      intro f hf as bs xs m P E h
      rcases List.mem_map.1 hf with ⟨rw, hRwMem, rfl⟩
      exact witEnvAux_elim cm wit.regions (fun _ _ _ _ _ _ _ => False) hNameNd
        (fun _ _ _ _ _ _ _ _ hf0 => hf0) rw hRwMem as bs xs m P E h
    let Ψ_cold := embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
      (fun _ _ => True) Ψ_res
    have hHybToCold : ∀ pc st, PsiHyb cm wit Ψ_cold H pc st → Ψ_cold pc st := by
      intro pc st hp
      dsimp only [PsiHyb] at hp
      split at hp
      · exact hp.2
      · exact hp
    obtain ⟨hCl, hWp⟩ := checkAndLiftWitness_hybrid_sound cm wit Ψ_cold H (haltX H) lt hLift
      (fun _ _ hc => ⟨rfl, rfl, hc⟩)
      (fun rw hRwMem => M.supportsSource (liftRegion cm rw) (List.mem_map_of_mem hRwMem))
      hRes
      (fun rw hRwMem r₀ m₀ hMid => by
        apply embedTargetSafe_fold
        refine ⟨fun e he heq _ => ?_, fun hne => ?_⟩
        · rcases List.mem_map.1 he with ⟨rw', hRw'Mem, rfl⟩
          have hEqRw : rw' = rw :=
            nodup_flatMap_inj RegionWitness.allPcs RegionWitness.entryPc hEntMem hAllNd
              hRw'Mem hRwMem heq
          subst hEqRw
          have hfn := compiled_lift_fnSpec M (witEnv cm wit) hFsNd hWfAll hΓ
            (List.mem_map_of_mem hRwMem)
          exact regionEntry_to_targetSafe hHybToCold hfn hMid
        · exfalso
          apply hne
          exact List.any_eq_true.2 ⟨(rw.entryPc, rw.name, rw.abi, M.bound rw.name),
            List.mem_map_of_mem hRwMem, by simp⟩)
      (fun rw hRwMem hRet pc hPcRw hNe st _ => by
        apply embedTargetSafe_fold
        refine ⟨fun e he heq _ => ?_, fun _ => hDrop rw hRwMem hRet pc hPcRw hNe st⟩
        · exfalso
          rcases List.mem_map.1 he with ⟨rw', hRw'Mem, rfl⟩
          by_cases hEqRw : rw' = rw
          · subst hEqRw; exact hNe heq.symm
          · exact nodup_flatMap_disjoint RegionWitness.allPcs hAllNd hRw'Mem hRwMem hEqRw
              rw'.entryPc (hEntMem rw' hRw'Mem)
              (by rw [show rw'.entryPc = pc from heq]; exact hPcRw))
      hNoRo
    exact ⟨⟨PsiHyb cm wit Ψ_cold H, hCl, hHybToCold⟩, hWp⟩
  · cases hLift'

/-- **Stage-0 Read-Only Table Compiled Soundness:** handles `.memTableRo` regions guarded by
`WitRoOk wit st.mem` (e.g. `threadedVM` ELIDED-BOUNDS RO dispatch tables). -/
theorem recoverCfg_ro_compiled_sound {T : Target} (C : AddrCodec T) {lt : LegalTarget}
    (cm : CodeMap) (wit : CfgWitness) (H : HaltPost) (H_mach : T.mach.State → Prop)
    {exits : List Sym} {nX : Nat} {hints : List T.toIsa.Hints} {maxBound : Nat}
    {fns : List Fn} {wRes : CodeMap}
    (hLift : checkAndLiftWitness cm wit = .ok (fns, wRes))
    (M : Compiled T lt [] exits nX fns hints maxBound)
    (Ψ_res : CodeSpec)
    (hRes : SpecsClosed wRes cm.symEnv
      (embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
        (roPcGuard wit) Ψ_res) H)
    (hDrop : ∀ rw ∈ wit.regions, rw.retainFallbacks = false →
      ∀ pc ∈ rw.allPcs, pc ≠ rw.entryPc → ∀ st, Ψ_res pc st) :
    (∃ Ψ_hyb : CodeSpec, SpecsClosed cm cm.symEnv Ψ_hyb H ∧
      ∀ pc st, Ψ_hyb pc st →
        embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
          (roPcGuard wit) Ψ_res pc st) ∧
      ∀ pc₀ st₀, cm.wp H pc₀ st₀ →
        embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
          (roPcGuard wit) Ψ_res pc₀ st₀ := by
  have hLift' := hLift
  dsimp only [checkAndLiftWitness] at hLift'
  split at hLift'
  · rename_i hChk
    cases hLift'
    have hChk' := hChk
    dsimp only [CfgWitness.check] at hChk'
    simp only [Bool.and_eq_true] at hChk'
    have hNameNd : (wit.regions.map RegionWitness.name).Nodup := listNodup_nodup hChk'.1.1
    have hAllNd : (wit.regions.flatMap RegionWitness.allPcs).Nodup := listNodup_nodup hChk'.1.2
    have hEntMem : ∀ rw ∈ wit.regions, rw.entryPc ∈ rw.allPcs :=
      checkAux_mem_stage0 cm wit.regions [] hChk'.2
    have hFsNd : ((wit.regions.map (liftRegion cm)).map Fn.name).Nodup := by
      rw [List.map_map]; exact hNameNd
    have hWfAll : ∀ f ∈ wit.regions.map (liftRegion cm), f.Wf := by
      intro f hf
      rcases List.mem_map.1 hf with ⟨rw, _, rfl⟩
      exact liftRegion_wf cm rw
    have hΓ : ∀ f ∈ wit.regions.map (liftRegion cm), ∀ as bs xs m P E,
        witEnv cm wit f.name as bs xs m P E →
        ∃ (h₁ : as = f.as) (h₂ : bs = f.rs),
          Func.spec (witEnv cm wit) f.body (h₁ ▸ xs) m (h₂ ▸ P) E := by
      intro f hf as bs xs m P E h
      rcases List.mem_map.1 hf with ⟨rw, hRwMem, rfl⟩
      exact witEnvAux_elim cm wit.regions (fun _ _ _ _ _ _ _ => False) hNameNd
        (fun _ _ _ _ _ _ _ _ hf0 => hf0) rw hRwMem as bs xs m P E h
    let Ψ_cold := embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
      (roPcGuard wit) Ψ_res
    have hHybToCold : ∀ pc st, PsiHybG true cm wit Ψ_cold H pc st → Ψ_cold pc st := by
      intro pc st hp
      dsimp only [PsiHybG] at hp
      split at hp
      · exact hp.2
      · exact hp
    obtain ⟨hCl, hWp⟩ := checkAndLiftWitness_ro_hybrid_sound cm wit Ψ_cold H (haltX H) lt hLift
      (fun _ _ hc => ⟨rfl, rfl, hc⟩)
      (fun rw hRwMem => M.supportsSource (liftRegion cm rw) (List.mem_map_of_mem hRwMem))
      hRes
      (fun rw hRwMem r₀ m₀ hMidImp => by
        apply embedTargetSafe_fold
        refine ⟨fun e he heq hGuard => ?_, fun hne => ?_⟩
        · rcases List.mem_map.1 he with ⟨rw', hRw'Mem, rfl⟩
          have hEqRw : rw' = rw :=
            nodup_flatMap_inj RegionWitness.allPcs RegionWitness.entryPc hEntMem hAllNd
              hRw'Mem hRwMem heq
          subst hEqRw
          have hRoPred : RoPred true wit rw'.entryPc m₀ := by
            dsimp only [RoPred]
            split
            · rename_i hCond
              exact hGuard (by simpa [isRoPc] using hCond)
            · trivial
          have hfn := compiled_lift_fnSpec M (witEnv cm wit) hFsNd hWfAll hΓ
            (List.mem_map_of_mem hRwMem)
          exact regionEntry_to_targetSafe hHybToCold hfn (hMidImp hRoPred)
        · exfalso
          apply hne
          exact List.any_eq_true.2 ⟨(rw.entryPc, rw.name, rw.abi, M.bound rw.name),
            List.mem_map_of_mem hRwMem, by simp⟩)
      (fun rw hRwMem hRet pc hPcRw hNe st _ => by
        apply embedTargetSafe_fold
        refine ⟨fun e he heq _ => ?_, fun _ => hDrop rw hRwMem hRet pc hPcRw hNe st⟩
        · exfalso
          rcases List.mem_map.1 he with ⟨rw', hRw'Mem, rfl⟩
          by_cases hEqRw : rw' = rw
          · subst hEqRw; exact hNe heq.symm
          · exact nodup_flatMap_disjoint RegionWitness.allPcs hAllNd hRw'Mem hRwMem hEqRw
              rw'.entryPc (hEntMem rw' hRw'Mem)
              (by rw [show rw'.entryPc = pc from heq]; exact hPcRw))
    exact ⟨⟨PsiHybG true cm wit Ψ_cold H, hCl, hHybToCold⟩, hWp⟩
  · cases hLift'

/-- **Stage-1 End-to-End Compiled Soundness:** connects `checkAndLiftContify` (with private
stack-frame promotion and `ContifyRegion`) + `Compiled` on any `T : Target` to
`embedTargetSafe` (and `TargetSafe T C M.host H_mach` at every region entry). -/
theorem recoverCfg_contify_compiled_sound {T : Target} (C : AddrCodec T) {lt : LegalTarget}
    (cm : CodeMap) (wit : ContifyWitness) (H : HaltPost) (H_mach : T.mach.State → Prop)
    {exits : List Sym} {nX : Nat} {hints : List T.toIsa.Hints} {maxBound : Nat}
    {fns : List Fn} {wRes : CodeMap}
    (hLift : checkAndLiftContify cm wit = .ok (fns, wRes))
    (M : Compiled T lt [] exits nX fns hints maxBound)
    (Ψ_res : CodeSpec)
    (hPriv : ∀ cr ∈ wit.regions, ∀ (r₀ : BedrockWord.Regs) (m₀ : Mem 64),
      (∃ b, cm.lookupAddr cr.entryPc = some b ∧
        b.wp cm.symEnv (fun _ _ => True) H (pushRegsV r₀.toRegsV) m₀) →
      cr.privFrame.numSlots > 0 →
      cr.privFrame.numSlots ≤ 64 ∧ ∀ k < cr.privFrame.numSlots, storeOk m₀ i64 (slotAddr r₀.sp k))
    (hRes : SpecsClosed wRes cm.symEnv
      (embedTargetSafe T C M.host lt H nX H_mach (witContifyEntries wit M.bound)
        (fun _ _ => True) Ψ_res) H)
    (hDrop : ∀ cr ∈ wit.regions, cr.retainFallbacks = false →
      ∀ pc ∈ cr.allPcs, pc ≠ cr.entryPc → ∀ st, Ψ_res pc st) :
    (∃ Ψ_hyb : CodeSpec, SpecsClosed cm cm.symEnv Ψ_hyb H ∧
      ∀ pc st, Ψ_hyb pc st →
        embedTargetSafe T C M.host lt H nX H_mach (witContifyEntries wit M.bound)
          (fun _ _ => True) Ψ_res pc st) ∧
      ∀ pc₀ st₀, cm.wp H pc₀ st₀ →
        embedTargetSafe T C M.host lt H nX H_mach (witContifyEntries wit M.bound)
          (fun _ _ => True) Ψ_res pc₀ st₀ := by
  have hLift' := hLift
  dsimp only [checkAndLiftContify] at hLift'
  split at hLift'
  · rename_i hChk
    cases hLift'
    have hChk' := hChk
    dsimp only [ContifyWitness.check] at hChk'
    simp only [Bool.and_eq_true] at hChk'
    have hNameNd : (wit.regions.map ContifyRegion.name).Nodup := listNodup_nodup hChk'.1.1
    have hAllNd : (wit.regions.flatMap ContifyRegion.allPcs).Nodup := listNodup_nodup hChk'.1.2
    have hEntMem : ∀ cr ∈ wit.regions, cr.entryPc ∈ cr.allPcs :=
      checkAux_mem_stage1 cm wit.regions [] hChk'.2
    have hFsNd : ((wit.regions.map (liftContifyRegion cm)).map Fn.name).Nodup := by
      rw [List.map_map]; exact hNameNd
    have hWfAll : ∀ f ∈ wit.regions.map (liftContifyRegion cm), f.Wf := by
      intro f hf
      rcases List.mem_map.1 hf with ⟨cr, _, rfl⟩
      exact liftContifyRegion_wf cm cr
    have hΓ : ∀ f ∈ wit.regions.map (liftContifyRegion cm), ∀ as bs xs m P E,
        witContifyEnv cm wit f.name as bs xs m P E →
        ∃ (h₁ : as = f.as) (h₂ : bs = f.rs),
          Func.spec (witContifyEnv cm wit) f.body (h₁ ▸ xs) m (h₂ ▸ P) E := by
      intro f hf as bs xs m P E h
      rcases List.mem_map.1 hf with ⟨cr, hCrMem, rfl⟩
      exact witContifyEnvAux_elim cm wit.regions (fun _ _ _ _ _ _ _ => False) hNameNd
        (fun _ _ _ _ _ _ _ _ hf0 => hf0) cr hCrMem as bs xs m P E h
    let Ψ_cold := embedTargetSafe T C M.host lt H nX H_mach (witContifyEntries wit M.bound)
      (fun _ _ => True) Ψ_res
    have hHybToCold : ∀ pc st, PsiContHyb cm wit Ψ_cold H pc st → Ψ_cold pc st := by
      intro pc st hp
      dsimp only [PsiContHyb] at hp
      split at hp
      · exact hp.2
      · exact hp
    obtain ⟨hCl, hWp⟩ := checkAndLiftContify_hybrid_sound cm wit Ψ_cold H (haltX H) lt hLift
      (fun _ _ hc => ⟨rfl, rfl, hc⟩)
      (fun cr hCrMem => M.supportsSource (liftContifyRegion cm cr) (List.mem_map_of_mem hCrMem))
      (fun cr hCrMem r₀ m₀ hReg => by
        have hStep := Xcap.Lfp.lfp_post
          (contifyRegionStep_mono cm wit Ψ_cold H) (cr.entryPc, ⟨r₀, m₀⟩) hReg
        rcases hStep with ⟨b, hlu, hbp⟩
        exact hPriv cr hCrMem r₀ m₀ ⟨b, hlu, blockFlat_wp_mono (fun _ _ _ => trivial) b _ _ hbp⟩)
      hRes
      (fun cr hCrMem r₀ m₀ hMid => by
        apply embedTargetSafe_fold
        refine ⟨fun e he heq _ => ?_, fun hne => ?_⟩
        · rcases List.mem_map.1 he with ⟨cr', hCr'Mem, rfl⟩
          have hEqCr : cr' = cr :=
            nodup_flatMap_inj ContifyRegion.allPcs ContifyRegion.entryPc hEntMem hAllNd
              hCr'Mem hCrMem heq
          subst hEqCr
          have hfn := compiled_lift_fnSpec M (witContifyEnv cm wit) hFsNd hWfAll hΓ
            (List.mem_map_of_mem hCrMem)
          exact regionEntry_to_targetSafe hHybToCold hfn hMid
        · exfalso
          apply hne
          exact List.any_eq_true.2 ⟨(cr.entryPc, cr.name, cr.abi, M.bound cr.name),
            List.mem_map_of_mem hCrMem, by simp⟩)
      (fun cr hCrMem hRet pc hPcCr hNe st _ => by
        apply embedTargetSafe_fold
        refine ⟨fun e he heq _ => ?_, fun _ => hDrop cr hCrMem hRet pc hPcCr hNe st⟩
        · exfalso
          rcases List.mem_map.1 he with ⟨cr', hCr'Mem, rfl⟩
          by_cases hEqCr : cr' = cr
          · subst hEqCr; exact hNe heq.symm
          · exact nodup_flatMap_disjoint ContifyRegion.allPcs hAllNd hCr'Mem hCrMem hEqCr
              cr'.entryPc (hEntMem cr' hCr'Mem)
              (by rw [show cr'.entryPc = pc from heq]; exact hPcCr))
    exact ⟨⟨PsiContHyb cm wit Ψ_cold H, hCl, hHybToCold⟩, hWp⟩
  · cases hLift'

/-- Direct execution corollary for `recoverCfg_compiled_sound`: from `cm.wp H rw.entryPc ⟨r₀, m₀⟩`
and concrete machine entry frame `(s, ra, R)` matching `(r₀, m₀)`, execute `T.mach.step M.host`
from `T.mach.labelAddr M.host rw.name` to `H_mach`. -/
theorem recoverCfg_run_compiled {T : Target} (C : AddrCodec T) {lt : LegalTarget}
    {cm : CodeMap} {wit : CfgWitness} {H : HaltPost} {H_mach : T.mach.State → Prop}
    {exits : List Sym} {nX : Nat} {hints : List T.toIsa.Hints} {maxBound : Nat}
    {fns : List Fn} {wRes : CodeMap}
    (hLift : checkAndLiftWitness cm wit = .ok (fns, wRes))
    (M : Compiled T lt [] exits nX fns hints maxBound)
    (Ψ_res : CodeSpec)
    (hRes : SpecsClosed wRes cm.symEnv
      (embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
        (fun _ _ => True) Ψ_res) H)
    (hDrop : ∀ rw ∈ wit.regions, rw.retainFallbacks = false →
      ∀ pc ∈ rw.allPcs, pc ≠ rw.entryPc → ∀ st, Ψ_res pc st)
    {rw : RegionWitness} (hRw : rw ∈ wit.regions) {r₀ : BedrockWord.Regs} {m₀ : Mem 64}
    (hWp : cm.wp H rw.entryPc ⟨r₀, m₀⟩)
    (s : T.mach.MData) (ra : T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : T.ArgsIn (encodeTup lt regSig r₀.toRegsV.toTup) s)
    (hra : T.frameSpec.raReg s ra)
    (hsp : T.frameSpec.spEntry (T.mach.getGpr s T.frame.sp))
    (hmem : T.mach.mem s =⋆ Eq m₀ ⋆ T.Entry (T.mach.getGpr s T.frame.sp) ra (M.bound rw.name) ⋆ R)
    (hret : cptr (TargetSafe T C M.host H_mach) (C.toBits ra) (fun s' =>
      ∃ (rets : Tup Val (lt.legalSig rw.abi.retSig)) (m' : Mem 64),
        (∃ rets₀ : Tup Val rw.abi.retSig, encodeTup lt rw.abi.retSig rets₀ = rets ∧
          let p := abiNextPcAndState rw.abi r₀.rp rets₀ m'
          embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
            (fun _ _ => True) Ψ_res p.1 p.2) ∧
        T.RetsIn rets s' ∧ T.Restored s s' ∧
        (T.mach.mem s' =⋆ Eq m' ⋆ T.Exit (T.mach.getGpr s T.frame.sp) (M.bound rw.name) ⋆ R)))
    (hexit : ∀ c m' stExit,
      H c m' → T.Defined M.host haltSym →
      T.mach.pc stExit = T.mach.labelAddr M.host haltSym →
      T.ArgsIn (encodeTup lt [i64] (c, ())) (T.mach.data stExit) →
      T.frameSpec.spEntry (T.mach.getGpr (T.mach.data stExit) T.frame.sp) →
      (∃ ra' n' F, nX ≤ n' ∧ n' + T.frame.raBytes ≤ 2 ^ 64 ∧
        T.frameSpec.raReg (T.mach.data stExit) ra' ∧
        (T.mach.mem (T.mach.data stExit) =⋆
          Eq m' ⋆ T.Entry (T.mach.getGpr (T.mach.data stExit) T.frame.sp) ra' n' ⋆ F ⋆ R)) →
      Eventually (T.mach.step M.host) H_mach stExit)
    (hNoRo : wit.hasMemTableRo = false := by decide) :
    Eventually (T.mach.step M.host) H_mach
      (T.mach.mkState s (T.mach.labelAddr M.host rw.name)) := by
  have hMain := (recoverCfg_compiled_sound C cm wit H H_mach hLift M Ψ_res hRes hDrop hNoRo).2
    rw.entryPc ⟨r₀, m₀⟩ hWp
  have hCond := embedTargetSafe_entry
    (List.mem_map.2 ⟨rw, hRw, rfl⟩) hMain trivial
  have hSafe := hCond s ra R hargs hra hsp hmem hret hexit
  dsimp only [TargetSafe] at hSafe
  rwa [C.of_to] at hSafe

/-- Direct execution corollary for `recoverCfg_ro_compiled_sound` (guarding RO-table lookups
with `WitRoOk wit m₀`). -/
theorem recoverCfg_ro_run_compiled {T : Target} (C : AddrCodec T) {lt : LegalTarget}
    {cm : CodeMap} {wit : CfgWitness} {H : HaltPost} {H_mach : T.mach.State → Prop}
    {exits : List Sym} {nX : Nat} {hints : List T.toIsa.Hints} {maxBound : Nat}
    {fns : List Fn} {wRes : CodeMap}
    (hLift : checkAndLiftWitness cm wit = .ok (fns, wRes))
    (M : Compiled T lt [] exits nX fns hints maxBound)
    (Ψ_res : CodeSpec)
    (hRes : SpecsClosed wRes cm.symEnv
      (embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
        (roPcGuard wit) Ψ_res) H)
    (hDrop : ∀ rw ∈ wit.regions, rw.retainFallbacks = false →
      ∀ pc ∈ rw.allPcs, pc ≠ rw.entryPc → ∀ st, Ψ_res pc st)
    {rw : RegionWitness} (hRw : rw ∈ wit.regions) {r₀ : BedrockWord.Regs} {m₀ : Mem 64}
    (hRo : roPcGuard wit rw.entryPc m₀)
    (hWp : cm.wp H rw.entryPc ⟨r₀, m₀⟩)
    (s : T.mach.MData) (ra : T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : T.ArgsIn (encodeTup lt regSig r₀.toRegsV.toTup) s)
    (hra : T.frameSpec.raReg s ra)
    (hsp : T.frameSpec.spEntry (T.mach.getGpr s T.frame.sp))
    (hmem : T.mach.mem s =⋆ Eq m₀ ⋆ T.Entry (T.mach.getGpr s T.frame.sp) ra (M.bound rw.name) ⋆ R)
    (hret : cptr (TargetSafe T C M.host H_mach) (C.toBits ra) (fun s' =>
      ∃ (rets : Tup Val (lt.legalSig rw.abi.retSig)) (m' : Mem 64),
        (∃ rets₀ : Tup Val rw.abi.retSig, encodeTup lt rw.abi.retSig rets₀ = rets ∧
          let p := abiNextPcAndState rw.abi r₀.rp rets₀ m'
          embedTargetSafe T C M.host lt H nX H_mach (witEntries wit M.bound)
            (roPcGuard wit) Ψ_res p.1 p.2) ∧
        T.RetsIn rets s' ∧ T.Restored s s' ∧
        (T.mach.mem s' =⋆ Eq m' ⋆ T.Exit (T.mach.getGpr s T.frame.sp) (M.bound rw.name) ⋆ R)))
    (hexit : ∀ c m' stExit,
      H c m' → T.Defined M.host haltSym →
      T.mach.pc stExit = T.mach.labelAddr M.host haltSym →
      T.ArgsIn (encodeTup lt [i64] (c, ())) (T.mach.data stExit) →
      T.frameSpec.spEntry (T.mach.getGpr (T.mach.data stExit) T.frame.sp) →
      (∃ ra' n' F, nX ≤ n' ∧ n' + T.frame.raBytes ≤ 2 ^ 64 ∧
        T.frameSpec.raReg (T.mach.data stExit) ra' ∧
        (T.mach.mem (T.mach.data stExit) =⋆
          Eq m' ⋆ T.Entry (T.mach.getGpr (T.mach.data stExit) T.frame.sp) ra' n' ⋆ F ⋆ R)) →
      Eventually (T.mach.step M.host) H_mach stExit) :
    Eventually (T.mach.step M.host) H_mach
      (T.mach.mkState s (T.mach.labelAddr M.host rw.name)) := by
  have hMain := (recoverCfg_ro_compiled_sound C cm wit H H_mach hLift M Ψ_res hRes hDrop).2
    rw.entryPc ⟨r₀, m₀⟩ hWp
  have hCond := embedTargetSafe_entry (List.mem_map.2 ⟨rw, hRw, rfl⟩) hMain hRo
  have hSafe := hCond s ra R hargs hra hsp hmem hret hexit
  dsimp only [TargetSafe] at hSafe
  rwa [C.of_to] at hSafe

/-- Direct execution corollary for `recoverCfg_contify_compiled_sound`. -/
theorem recoverCfg_contify_run_compiled {T : Target} (C : AddrCodec T) {lt : LegalTarget}
    {cm : CodeMap} {wit : ContifyWitness} {H : HaltPost} {H_mach : T.mach.State → Prop}
    {exits : List Sym} {nX : Nat} {hints : List T.toIsa.Hints} {maxBound : Nat}
    {fns : List Fn} {wRes : CodeMap}
    (hLift : checkAndLiftContify cm wit = .ok (fns, wRes))
    (M : Compiled T lt [] exits nX fns hints maxBound)
    (Ψ_res : CodeSpec)
    (hPriv : ∀ cr ∈ wit.regions, ∀ (r₀ : BedrockWord.Regs) (m₀ : Mem 64),
      (∃ b, cm.lookupAddr cr.entryPc = some b ∧
        b.wp cm.symEnv (fun _ _ => True) H (pushRegsV r₀.toRegsV) m₀) →
      cr.privFrame.numSlots > 0 →
      cr.privFrame.numSlots ≤ 64 ∧ ∀ k < cr.privFrame.numSlots, storeOk m₀ i64 (slotAddr r₀.sp k))
    (hRes : SpecsClosed wRes cm.symEnv
      (embedTargetSafe T C M.host lt H nX H_mach (witContifyEntries wit M.bound)
        (fun _ _ => True) Ψ_res) H)
    (hDrop : ∀ cr ∈ wit.regions, cr.retainFallbacks = false →
      ∀ pc ∈ cr.allPcs, pc ≠ cr.entryPc → ∀ st, Ψ_res pc st)
    {cr : ContifyRegion} (hCr : cr ∈ wit.regions) {r₀ : BedrockWord.Regs} {m₀ : Mem 64}
    (hWp : cm.wp H cr.entryPc ⟨r₀, m₀⟩)
    (s : T.mach.MData) (ra : T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : T.ArgsIn (encodeTup lt regSig r₀.toRegsV.toTup) s)
    (hra : T.frameSpec.raReg s ra)
    (hsp : T.frameSpec.spEntry (T.mach.getGpr s T.frame.sp))
    (hmem : T.mach.mem s =⋆ Eq m₀ ⋆ T.Entry (T.mach.getGpr s T.frame.sp) ra (M.bound cr.name) ⋆ R)
    (hret : cptr (TargetSafe T C M.host H_mach) (C.toBits ra) (fun s' =>
      ∃ (rets : Tup Val (lt.legalSig cr.abi.retSig)) (m' : Mem 64),
        (∃ rets₀ : Tup Val cr.abi.retSig, encodeTup lt cr.abi.retSig rets₀ = rets ∧
          let p := abiNextPcAndState cr.abi r₀.rp rets₀ m'
          embedTargetSafe T C M.host lt H nX H_mach (witContifyEntries wit M.bound)
            (fun _ _ => True) Ψ_res p.1 p.2) ∧
        T.RetsIn rets s' ∧ T.Restored s s' ∧
        (T.mach.mem s' =⋆ Eq m' ⋆ T.Exit (T.mach.getGpr s T.frame.sp) (M.bound cr.name) ⋆ R)))
    (hexit : ∀ c m' stExit,
      H c m' → T.Defined M.host haltSym →
      T.mach.pc stExit = T.mach.labelAddr M.host haltSym →
      T.ArgsIn (encodeTup lt [i64] (c, ())) (T.mach.data stExit) →
      T.frameSpec.spEntry (T.mach.getGpr (T.mach.data stExit) T.frame.sp) →
      (∃ ra' n' F, nX ≤ n' ∧ n' + T.frame.raBytes ≤ 2 ^ 64 ∧
        T.frameSpec.raReg (T.mach.data stExit) ra' ∧
        (T.mach.mem (T.mach.data stExit) =⋆
          Eq m' ⋆ T.Entry (T.mach.getGpr (T.mach.data stExit) T.frame.sp) ra' n' ⋆ F ⋆ R)) →
      Eventually (T.mach.step M.host) H_mach stExit) :
    Eventually (T.mach.step M.host) H_mach
      (T.mach.mkState s (T.mach.labelAddr M.host cr.name)) := by
  have hMain :=
    (recoverCfg_contify_compiled_sound C cm wit H H_mach hLift M Ψ_res hPriv hRes hDrop).2
      cr.entryPc ⟨r₀, m₀⟩ hWp
  have hCond := embedTargetSafe_entry (List.mem_map.2 ⟨cr, hCr, rfl⟩) hMain trivial
  have hSafe := hCond s ra R hargs hra hsp hmem hret hexit
  dsimp only [TargetSafe] at hSafe
  rwa [C.of_to] at hSafe

end LeanQbe.T.Unified
