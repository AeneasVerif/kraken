/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof0
public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof1a
public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof1b
public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof2a
public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof2
import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullM4VivBceProof1
import LeanQbe.T.Examples.Kissat.FullM6Transport1
public meta import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat M8 XOR / $\mathbb{F}_2$ Gauss-Jordan Driver & Closed `ModuleOk` (`FullM8XorGaussProof`)

Top-level `full_xor_gauss_wp`, `19`-row `m8XorGaussSpecTable`, parametric `m8XorGauss_tableImpl_of`,
closed `m8XorGaussEnv`, `m8XorGaussEnv_noExit`, and `m8XorGauss_moduleOk` (`std3` axioms only).
-/

set_option autoImplicit false

local elab "c0_hstraight" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 2000

public section

namespace LeanQbe.T.Examples.Kissat.FullM8XorGauss

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullAssignAddTactics
open FullAssignAddTactics LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers

/-! ## 1. Framing, Union-Find Closure & Level-0 Propagation Helpers (`private`) -/

@[expose] def fullXorGaussSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private def FullGaussRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pDelayed s.scratch.delayed ⋆ array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
   array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
   array (t := i32) c.pTarjanMark s.scratch.tarjan_mark) ⋆
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆ c.pad

private theorem focus_full_gauss {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
     array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
     array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
     array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
     array (t := i32) c.pWsort s.scratch.wsort ⋆
     (FullGaussRest c s ⋆ R)) m := by
  unfold FullMem FullScratchArrays FullScrWksArrs FullScrDynArrs at hm
  unfold FullGaussRest
  ecancel

private theorem unfocus_full_gauss {c : FullCfg} {s : FullState}
    {scr' par' c2v' vc' cnt' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pScratchBuf scr' ⋆
           array (t := i32) c.pWorkStk1 par' ⋆
           array (t := i32) c.pWorkStk2 c2v' ⋆
           array (t := i32) c.pTarjanReach vc' ⋆
           array (t := i32) c.pWsort cnt' ⋆
           (FullGaussRest c s ⋆ R)) m) :
    (FullMem c { s with scratch :=
      { s.scratch with
        scratch_buf := scr'
        work_stk1 := par'
        work_stk2 := c2v'
        tarjan_reach := vc'
        wsort := cnt' } } ⋆ R) m := by
  change (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
      s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
    (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      (array (t := i32) c.pWsort cnt' ⋆ array (t := i32) c.pWorkStk1 par' ⋆
       array (t := i32) c.pWorkStk2 c2v' ⋆ array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
       array (t := i32) c.pTarjanReach vc') ⋆
      FullScrMetaArrs c s.scratch ⋆
      (array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf scr')) ⋆
    c.pad ⋆ R) m
  unfold FullGaussRest at hm
  ecancel

private theorem fullSparseInvW_upd_gauss {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    {scr' par' c2v' vc' cnt' : List (BitVec 32)}
    (hs : scr'.length = s.scratch.scratch_buf.length)
    (hp : par'.length = s.scratch.work_stk1.length)
    (hc : c2v'.length = s.scratch.work_stk2.length)
    (hv : vc'.length = s.scratch.tarjan_reach.length)
    (hk : cnt'.length = s.scratch.wsort.length) :
    FullSparseInvW c F0 F_cur { s with scratch :=
      { s.scratch with
        scratch_buf := scr'
        work_stk1 := par'
        work_stk2 := c2v'
        tarjan_reach := vc'
        wsort := cnt' } } := by
  have h1 := fullSparseInvW_upd_scratch_buf h hs
  have h2 := fullSparseInvW_upd_work_stk1 h1 hp
  have h3 := fullSparseInvW_upd_work_stk2 h2 hc
  have h4 := fullSparseInvW_upd_tarjan_reach h3 hv
  exact fullSparseInvW_upd_wsort h4 hk

private def UfPoolMerged (par scr : List (BitVec 32)) (cv eq_end bound : Nat) : Prop :=
  ∀ q ∈ poolStarts scr eq_end 0 eq_end, q < bound →
    let hdr := scr[q]?.getD 0#32
    let clen := (hdr &&& 0xFFFF#32).toNat
    0 < clen → ∀ k < clen,
      ufRoot par (scr[q + 1 + k]?.getD 0#32).toNat cv =
      ufRoot par (scr[q + 1]?.getD 0#32).toNat cv

private theorem ufRoot_set_root {par : List (BitVec 32)} {cv big : Nat} {small : BitVec 32}
    (hord : ∀ i < cv, (par[i]?.getD 0#32).toNat ≤ i) (hlen : cv ≤ par.length)
    (hsb : small.toNat < big) (hbig : big < cv)
    (hs_rt : (par[small.toNat]?.getD 0#32).toNat = small.toNat)
    (hb_rt : (par[big]?.getD 0#32).toNat = big) :
    let par' := par.set big small
    (∀ i < cv, (par'[i]?.getD 0#32).toNat ≤ i) ∧
    ∀ x < cv, ∀ fuel, x < fuel →
      ufRoot par' x fuel = if ufRoot par x fuel = big then small.toNat else ufRoot par x fuel := by
  intro par'
  have hbig_len : big < par.length := by omega
  have hord' : ∀ i < cv, (par'[i]?.getD 0#32).toNat ≤ i := by
    intro i hi
    by_cases hib : i = big
    · subst hib
      simp only [par', List.getElem?_set_self hbig_len, Option.getD_some]; omega
    · rw [show par'[i]? = par[i]? from List.getElem?_set_ne (Ne.symm hib)]; exact hord i hi
  refine ⟨hord', fun x hx fuel hxf => ?_⟩
  induction fuel generalizing x with
  | zero => exact absurd hxf (Nat.not_lt_zero _)
  | succ f ih =>
    dsimp only [ufRoot]
    by_cases hxb : x = big
    · subst hxb
      have hnb : ¬ (x ≤ small.toNat) := by omega
      have hge : x ≤ (par[x]?.getD 0#32).toNat := by omega
      simp only [par', List.getElem?_set_self hbig_len, Option.getD_some, hnb, hge, ↓reduceIte]
      have hf_pos : small.toNat < f := by omega
      have hih := ih small.toNat (by omega) hf_pos
      have hs_fix : ufRoot par small.toNat f = small.toNat := by
        cases f with
        | zero => omega
        | succ f' => exact ufRoot_eq_of_self (by omega)
      rw [hih, hs_fix, ite_eq_right (by omega)]
    · have hne : par'[x]? = par[x]? := List.getElem?_set_ne (Ne.symm hxb)
      rw [hne]
      split
      · simp
      · rename_i hlt
        have hpx_lt : (par[x]?.getD 0#32).toNat < x := by have := hord x hx; omega
        exact ih _ (by omega) (by omega)

private theorem ufRoot_set_flat {par : List (BitVec 32)} {cv v : Nat} {rv : BitVec 32}
    (hord : ∀ i < cv, (par[i]?.getD 0#32).toNat ≤ i) (hlen : cv ≤ par.length)
    (hv : v < cv) (hrv : rv.toNat = ufRoot par v cv) :
    let par' := par.set v rv
    (∀ i < cv, (par'[i]?.getD 0#32).toNat ≤ i) ∧
    ∀ x < cv, ∀ fuel, x < fuel → ufRoot par' x fuel = ufRoot par x fuel := by
  intro par'
  have hv_len : v < par.length := by omega
  have hrv_le : rv.toNat ≤ v := by rw [hrv]; exact ufRoot_le hord hv
  have hord' : ∀ i < cv, (par'[i]?.getD 0#32).toNat ≤ i := by
    intro i hi
    by_cases hiv : i = v
    · subst hiv; simp only [par', List.getElem?_set_self hv_len, Option.getD_some]; exact hrv_le
    · rw [show par'[i]? = par[i]? from List.getElem?_set_ne (Ne.symm hiv)]; exact hord i hi
  refine ⟨hord', fun x hx fuel hxf => ?_⟩
  induction fuel generalizing x with
  | zero => exact absurd hxf (Nat.not_lt_zero _)
  | succ f ih =>
    by_cases hxv : x = v
    · subst hxv
      have hidem : ufRoot par x (f + 1) = ufRoot par x cv := ufRoot_idem_of_ord hord hxf hx hx
      rw [hidem]
      conv => lhs; unfold ufRoot; dsimp only
      rw [List.getElem?_set_self hv_len, Option.getD_some]
      split
      · rename_i hge; omega
      · rename_i hlt
        have hih := ih rv.toNat (by omega) (by omega)
        rw [hih]
        have hrt_fix := ufRoot_is_root hord hv hv
        rw [← hrv] at hrt_fix
        cases f with
        | zero => omega
        | succ f' => rw [ufRoot_eq_of_self (by omega), hrv]
    · conv => lhs; unfold ufRoot; dsimp only
      conv => rhs; unfold ufRoot; dsimp only
      rw [List.getElem?_set_ne (Ne.symm hxv)]
      split
      · rfl
      · have hpx_lt : (par[x]?.getD 0#32).toNat < x := by have := hord x hx; omega
        exact ih _ (by omega) (by omega)

private theorem poolStarts_eq_of_ge {scr : List (BitVec 32)} {eq_end : Nat} :
    ∀ {f0 f1 p : Nat}, eq_end - p ≤ f0 → eq_end - p ≤ f1 →
      poolStarts scr eq_end p f0 = poolStarts scr eq_end p f1
  | 0, f1, p, h0, _ => by
    have hp : ¬ (p < eq_end) := by omega
    cases f1 <;> simp [poolStarts, hp]
  | f0 + 1, 0, p, _, h1 => by
    have hp : ¬ (p < eq_end) := by omega
    simp [poolStarts, hp]
  | f0 + 1, f1 + 1, p, h0, h1 => by
    unfold poolStarts
    split
    · rename_i hp
      let p' := p + 1 + (((scr[p]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32).toNat
      have hp0 : eq_end - p' ≤ f0 := by dsimp only [p']; omega
      have hp1 : eq_end - p' ≤ f1 := by dsimp only [p']; omega
      exact congrArg (p :: ·) (poolStarts_eq_of_ge hp0 hp1)
    · rfl

private theorem xorEqPoolOk_starts_prop {F : CNF Nat} {cv : Nat} {scr : List (BitVec 32)}
    {eq_end : Nat} : ∀ {p0 : Nat}, XorEqPoolOk F cv scr eq_end p0 →
      ∀ q ∈ poolStarts scr eq_end p0 (eq_end - p0),
        q < eq_end ∧
        let clen := ((scr[q]?.getD 0#32) &&& 0xFFFF#32).toNat
        (0 < clen → q + 1 + clen ≤ eq_end ∧ ∀ k < clen, (scr[q + 1 + k]?.getD 0#32).toNat < cv)
  | _, .done => by intro q hq; simp [poolStarts] at hq
  | p0, .step (hdr := hdr) (stride := st) (clen := cl) hp hhdr hst hcl hbd hbody hrest => by
    intro q hq
    have hsub : eq_end - p0 = (eq_end - p0 - 1) + 1 := by omega
    rw [hsub, poolStarts_step_iff hp] at hq
    have hst' : (((scr[p0]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32).toNat = st := by
      rw [hhdr, Option.getD_some, ← hst]
    rw [hst'] at hq
    rcases hq with rfl | ⟨_, hrest_q⟩
    · refine ⟨hp, fun hpos => ?_⟩
      have hcl' : ((scr[q]?.getD 0#32) &&& 0xFFFF#32).toNat = cl := by
        rw [hhdr, Option.getD_some, ← hcl]
      rw [hcl'] at hpos ⊢
      rcases hbody with rfl | ⟨_, hle, _, hlt, _⟩
      · omega
      · refine ⟨by omega, fun k hk =>
          hlt _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)⟩
    · have heq := poolStarts_eq_of_ge (scr := scr) (eq_end := eq_end)
        (f0 := eq_end - p0 - 1) (f1 := eq_end - (p0 + 1 + st)) (p := p0 + 1 + st)
        (by omega) (Nat.le_refl _)
      rw [heq] at hrest_q
      exact xorEqPoolOk_starts_prop hrest q hrest_q

private theorem ufPoolMerged_of_same_root {F : CNF Nat} {par1 par2 scr : List (BitVec 32)}
    {cv eq_end b : Nat} (h : UfPoolMerged par1 scr cv eq_end b)
    (hpool : XorEqPoolOk F cv scr eq_end 0)
    (hsame : ∀ x < cv, ufRoot par2 x cv = ufRoot par1 x cv) :
    UfPoolMerged par2 scr cv eq_end b := by
  intro q hq hqb hdr clen hpos k hk
  have ⟨_, hcl_ok⟩ := xorEqPoolOk_starts_prop hpool q (by simpa using hq)
  have ⟨_, hvars_q⟩ := hcl_ok hpos
  rw [hsame _ (hvars_q k hk), hsame _ (hvars_q 0 hpos)]
  exact h q hq hqb hpos k hk

private theorem ufPoolMerged_of_union {par scr : List (BitVec 32)} {F : CNF Nat}
    {cv eq_end b big : Nat} {small : BitVec 32}
    (h : UfPoolMerged par scr cv eq_end b)
    (hpool : XorEqPoolOk F cv scr eq_end 0)
    (hord : ∀ i < cv, (par[i]?.getD 0#32).toNat ≤ i) (hlen : cv ≤ par.length)
    (hsb : small.toNat < big) (hbig : big < cv)
    (hs_rt : (par[small.toNat]?.getD 0#32).toNat = small.toNat)
    (hb_rt : (par[big]?.getD 0#32).toNat = big) :
    UfPoolMerged (par.set big small) scr cv eq_end b := by
  have hsr := (ufRoot_set_root hord hlen hsb hbig hs_rt hb_rt).2
  intro q hq hqb hdr clen hpos k hk
  have ⟨_, hcl_ok⟩ := xorEqPoolOk_starts_prop hpool q (by simpa using hq)
  have ⟨_, hvars_q⟩ := hcl_ok hpos
  have hk_lt := hvars_q k hk
  have h0_lt := hvars_q 0 hpos
  rw [hsr _ hk_lt cv hk_lt, hsr _ h0_lt cv h0_lt, h q hq hqb hpos k hk]

private theorem xorPoolCompClosed_of_flat {par_pre par_flat scr : List (BitVec 32)} {F : CNF Nat}
    {cv eq_end : Nat}
    (hpool : XorEqPoolOk F cv scr eq_end 0)
    (hmerged : UfPoolMerged par_pre scr cv eq_end eq_end)
    (hflat : ∀ i < cv, (par_flat[i]?.getD 0#32).toNat = ufRoot par_pre i cv) :
    XorPoolCompClosed par_flat scr eq_end := by
  intro p hp hdr clen hpos k hk
  have ⟨hp_lt, hcl_ok⟩ := xorEqPoolOk_starts_prop hpool p (by simpa using hp)
  have ⟨_, hvars_p⟩ := hcl_ok hpos
  apply BitVec.eq_of_toNat_eq
  rw [hflat _ (hvars_p k hk), hflat _ (hvars_p 0 hpos)]
  exact hmerged p hp hp_lt hpos k hk

private theorem xorPoolCompClosed_congr {F : CNF Nat} {cv : Nat}
    {par scr1 scr2 : List (BitVec 32)} {eq_end : Nat}
    (h : XorPoolCompClosed par scr1 eq_end)
    (hpool : XorEqPoolOk F cv scr1 eq_end 0)
    (heq : ∀ i < eq_end, scr2[i]? = scr1[i]?) :
    XorPoolCompClosed par scr2 eq_end := by
  have hps : poolStarts scr2 eq_end 0 eq_end = poolStarts scr1 eq_end 0 eq_end :=
    poolStarts_congr fun i _ hi => by rw [heq i hi]
  intro p hp
  rw [hps] at hp
  have ⟨hp_lt, hcl_ok⟩ := xorEqPoolOk_starts_prop hpool p (by simpa using hp)
  have hhdr_eq : scr2[p]?.getD 0#32 = scr1[p]?.getD 0#32 := by rw [heq p hp_lt]
  intro hdr clen hpos k hk
  dsimp only [hdr, clen] at hpos hk ⊢
  rw [hhdr_eq] at hpos hk
  have hle := (hcl_ok hpos).1
  rw [heq (p + 1 + k) (by omega), heq (p + 1) (by omega)]
  exact h p hp hpos k hk

private theorem gauss_cur_unsat {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) :
    (cnfOfClauses F_cur).Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_)
    obtain ⟨i, hi, hieq⟩ :=
      (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

private theorem gauss_conflict_level0_unsat {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) : F0.Unsat :=
  hw.ext_sound.2 (gauss_cur_unsat hw hl0 hc)

private theorem fullSparseInvW_of_prop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hdom : s'.core.dense_mode = 0#64)
    (hext : s'.scratch.extend_len = s.scratch.extend_len) :
    FullSparseInvW c F0 F_cur s' := by
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm.2.1]
    have hp := hperm.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (h.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    h.2.2.2.2.1.1.of_refs_subset hll fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm.2.1]
  have hext' : FullExtScratchOk c s' :=
    ⟨hll', by rw [hext]; exact h.2.2.2.2.1.2⟩
  exact ⟨hlen', hw', fullLitMarksClear_of_eq h.2.2.1 hmrk hlm, hnd', hext', hdom⟩

/-! ## 2. Top-Level XOR Gauss-Jordan Driver (`full_xor_gauss`) -/

theorem full_xor_gauss_wp (Γ : Env)
    (hColAr : ∀ a m Q X, fullXorCollectArenaSpec a m Q X →
      Γ "full_xor_collect_arena" [i64, i64] [i64] a m Q X)
    (hColBin : ∀ a m Q X, fullXorCollectBinsSpec a m Q X →
      Γ "full_xor_collect_bins" [i64, i64] [i64] a m Q X)
    (hChain : ∀ a m Q X, fullXorChainMergeSpec a m Q X →
      Γ "full_xor_chain_merge" [i64, i64] [i64] a m Q X)
    (hEmitSmall : ∀ a m Q X, fullXorEmitPoolSmallSpec a m Q X →
      Γ "full_xor_emit_pool_small" [i64, i64] [i64] a m Q X)
    (hUfFind : ∀ a m Q X, fullXorUfFindSpec a m Q X →
      Γ "full_xor_uf_find" [i64, i32, i64] [i32] a m Q X)
    (hBuildMat : ∀ a m Q X, fullXorBuildMatSpec a m Q X →
      Γ "full_xor_build_mat" [i64, i64, i64, i64] [i64] a m Q X)
    (hRref : ∀ a m Q X, fullXorRrefSpec a m Q X →
      Γ "full_xor_rref" [i64, i64, i64, i64] [] a m Q X)
    (hEmitMat : ∀ a m Q X, fullXorEmitMatSpec a m Q X →
      Γ "full_xor_emit_mat" [i64, i64, i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullXorGaussSpec a m Q X → Func.wp Γ full_xor_gauss_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hsp0_ex, hlvl0, hm0, hQ⟩
  obtain ⟨F_cur, hsp0⟩ := hsp0_ex.exists_witness
  have hcap_lt : c.scratch_cap < 268435456 := by
    have := c.hscr; rw [dimacsBound_val] at this; exact this
  have hmaxv_lt : c.max_vars < 536870912 := by
    have := c.hmaxv; rw [dimacsBound_val] at this; exact this
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hsp0.1.1.cur_vars_le
  have hcv_lt : s0.core.cur_vars < 536870912 := by omega
  unfold full_xor_gauss_body Func.wp; dsimp only
  c0_hstraight
  -- Guard 1: inconsistent != 0
  c0_hsplit
  · c0_hstraight
    have hinc_ne : s0.core.inconsistent ≠ 0#64 := by bv_omega
    exact hQ 20#64 s0 m0 hsp0.toSparse hlvl0 (Nat.le_refl _) (Or.inr rfl)
      (fun _ => unsat_of_sparseW_inconsistent hsp0 (hsp0.2.1.inconsistent_sound hinc_ne)) hm0
  -- Guard 2: cur_level != 0
  · c0_hstraight
    c0_hsplit
    · c0_hstraight
      exact hQ 1#64 s0 m0 hsp0.toSparse hlvl0 (Nat.le_refl _) (Or.inl rfl)
        (fun h => by simp at h) hm0
    -- Guard 3: dense_mode != 0
    · c0_hstraight
      c0_hsplit
      · c0_hstraight
        exact hQ 1#64 s0 m0 hsp0.toSparse hlvl0 (Nat.le_refl _) (Or.inl rfl)
          (fun h => by simp at h) hm0
      -- Guard 4: cur_vars == 0
      · c0_hstraight
        c0_hsplit
        · c0_hstraight
          exact hQ 1#64 s0 m0 hsp0.toSparse hlvl0 (Nat.le_refl _) (Or.inl rfl)
            (fun h => by simp at h) hm0
        -- Guard 5: scratch_cap < 3
        · c0_hstraight
          c0_hsplit
          · c0_hstraight
            exact hQ 1#64 s0 m0 hsp0.toSparse hlvl0 (Nat.le_refl _) (Or.inl rfl)
              (fun h => by simp at h) hm0
          · c0_hstraight
            -- Join after ht_cap computation
            let Jht : Tup Val [i64] → Mem 64 → Prop := fun (ht_cap, ()) m1 =>
              m1 = m0 ∧ (ht_cap ≠ 0#64 → 7 * ht_cap.toNat ≤ c.scratch_cap ∧ ht_cap.toNat < 2 ^ 30)
            refine wp_join_group Jht ?_ ?_
            · rintro _ ⟨ht_cap, _⟩ m1 ⟨rfl, hht_ok⟩
              -- Call 1: full_xor_collect_arena
              c0_hstraight
              apply wp_call_of_spec
              dsimp only [vals, Arg.val]
              refine hColAr _ _ _ _
                ⟨c, F0, F_cur, s0, R, rfl, hsp0, hlvl0, hht_ok, hm0,
                  fun eq1 s1 m1 hsp1 hcv1 hlvl1 hfuel1 _ hfail1 hok1 hm1 => ?_⟩
              dsimp only
              c0_hsplit
              · c0_hstraight
                have hff : eq1 = 0xFFFFFFFFFFFFFFFF#64 := by bv_omega
                exact hQ 20#64 s1 m1 hsp1.toSparse (hlvl1.trans hlvl0)
                  (by rw [hfuel1]; exact Nat.le_refl _) (Or.inr rfl) (fun _ => (hfail1 hff).1) hm1
              · have hne1 : eq1 ≠ 0xFFFFFFFFFFFFFFFF#64 := by bv_omega
                obtain ⟨heq1_le, _, hpool1⟩ := hok1 hne1
                -- Call 2: full_xor_collect_bins
                c0_hstraight
                apply wp_call_of_spec
                dsimp only [vals, Arg.val]
                refine hColBin _ _ _ _
                  ⟨c, F0, F_cur, s1, R, rfl, hsp1, heq1_le, hpool1, hm1,
                    fun eq2 scr2 m2 hlen2 heq2_le hpool2 hm2 => ?_⟩
                dsimp only
                let s2 : FullState := { s1 with scratch := { s1.scratch with scratch_buf := scr2 } }
                have hsp2 : FullSparseInvW c F0 F_cur s2 :=
                  fullSparseInvW_upd_scratch_buf hsp1 hlen2
                c0_hsplit
                · c0_hstraight
                  exact hQ 1#64 s2 m2 hsp2.toSparse (hlvl1.trans hlvl0)
                    (by rw [hfuel1]; exact Nat.le_refl _) (Or.inl rfl) (fun h => by simp at h) hm2
                · -- Call 3: full_xor_chain_merge
                  c0_hstraight
                  apply wp_call_of_spec
                  dsimp only [vals, Arg.val]
                  refine hChain _ _ _ _
                    ⟨c, F0, F_cur, s2, R, rfl, hsp2, heq2_le, hpool2, hm2,
                      fun eq3 s3 m3 hsp3 hcv3 hlvl3 hfuel3 _ hfail3 hok3 hm3 => ?_⟩
                  dsimp only
                  c0_hsplit
                  · c0_hstraight
                    have hff3 : eq3 = 0xFFFFFFFFFFFFFFFF#64 := by bv_omega
                    exact hQ 20#64 s3 m3 hsp3.toSparse (hlvl3.trans (hlvl1.trans hlvl0))
                      (by rw [hfuel3, hfuel1]; exact Nat.le_refl _) (Or.inr rfl)
                      (fun _ => (hfail3 hff3).1) hm3
                  · have hne3 : eq3 ≠ 0xFFFFFFFFFFFFFFFF#64 := by bv_omega
                    obtain ⟨heq3_le, _, hpool3⟩ := hok3 hne3
                    -- Post-main join: final if (propagated < trail_end) full_propagate
                    let Jpost : Mem 64 → Prop := fun mp =>
                      ∃ sp : FullState,
                        FullSparseInvW c F0 F_cur sp ∧ sp.core.cur_level = 0 ∧
                        sp.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sp ⋆ R) mp
                    refine wp_join0 Jpost ?_ ?_
                    · rintro _ mp ⟨sp, hsp_p, hlvl_p, hfuel_p, hmp⟩
                      refine wp_join0 Jpost ?_ ?_
                      · rintro _ mf ⟨sf, hsp_f, hlvl_f, hfuel_f, hmf⟩
                        c0_hstraight
                        exact hQ 1#64 sf mf hsp_f.toSparse hlvl_f hfuel_f (Or.inl rfl)
                          (fun h => by simp at h) hmf
                      · intro _ hJret1
                        c0_hstraight
                        c0_hsplit
                        · c0_hstraight
                          apply wp_call_of_spec
                          dsimp only [vals, Arg.val]
                          refine hProp _ _ _ _
                            ⟨c, F0, F_cur, sp, R, rfl, hsp_p.1, hsp_p.2.1, hsp_p.2.2.2.2.2, hmp,
                              fun pr vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl'
                                wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom'
                                ticks' wsort' phases' m' hlen' hw' _ hperm' hfu' _ _ hr1 _ _ hm' =>
                                ?_⟩
                          dsimp only
                          let sp' : FullState :=
                            { sp with
                              core :=
                                { sp.core with
                                  vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', trail_end := te',
                                  propagated := prop', unassigned := unass', unflushed := unfl',
                                  wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                  wusable := wu', fuel := fuel', confl_type := ctype',
                                  confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                  oom := oom' }
                              scratch :=
                                { sp.scratch with
                                  search_ticks := ticks', wsort := wsort', phases := phases' } }
                          have hsp_p' : FullSparseInvW c F0 F_cur sp' :=
                            fullSparseInvW_of_prop hsp_p hlen' hw' hperm' rfl rfl rfl
                              hsp_p.2.2.2.2.2 rfl
                          c0_hsplit
                          · have hpr1 : pr = 1#64 := by bv_omega
                            have hconfl := (hr1 hpr1).2.2
                            have hunsat : F0.Unsat :=
                              gauss_conflict_level0_unsat hw' hlvl_p hconfl
                            have hcur_unsat : (cnfOfClauses F_cur).Unsat :=
                              gauss_cur_unsat hw' hlvl_p hconfl
                            c0_hstraight
                            have hsp_inc : FullSparseInvW c F0 F_cur
                                { sp' with core := { sp'.core with inconsistent := 1#64 } } :=
                              fullSparseInvW_upd_inc hsp_p' 1#64 (fun _ => hcur_unsat)
                            exact hQ 20#64 _ _ hsp_inc.toSparse hlvl_p
                              (Nat.le_trans hfu' hfuel_p) (Or.inr rfl) (fun _ => hunsat) hm
                          · exact hJret1 m' ⟨sp', hsp_p', hlvl_p, Nat.le_trans hfu' hfuel_p, hm'⟩
                        · exact hJret1 mp ⟨sp, hsp_p, hlvl_p, hfuel_p, hmp⟩
                    · intro _ hJpost
                      c0_hsplit
                      · -- Main branch: eq3 > 0
                        have hlvl3_0 : s3.core.cur_level = 0 := hlvl3.trans (hlvl1.trans hlvl0)
                        have hfuel3_0 : s3.core.fuel = s0.core.fuel := hfuel3.trans hfuel1
                        have hcv3_0 : s3.core.cur_vars = s0.core.cur_vars := hcv3.trans hcv1
                        -- Call 4: full_xor_emit_pool_small
                        c0_hstraight
                        apply wp_call_of_spec
                        dsimp only [vals, Arg.val]
                        refine hEmitSmall _ _ _ _
                          ⟨c, F0, F_cur, s3, R, rfl, hsp3, hlvl3_0, heq3_le, hpool3, hm3,
                            fun er s4 m4 hsp4 hcv4 hlvl4 hfuel4 hscr4 _ her20 hm4 => ?_⟩
                        dsimp only
                        c0_hsplit
                        · c0_hstraight
                          have h20 : er = 20#64 := by bv_omega
                          exact hQ 20#64 s4 m4 hsp4.toSparse hlvl4
                            (by rw [hfuel4, hfuel3_0]; exact Nat.le_refl _)
                            (Or.inr rfl) (fun _ => her20 h20) hm4
                        · have hcv4_0 : s4.core.cur_vars = s0.core.cur_vars := hcv4.trans hcv3_0
                          have hfuel4_0 : s4.core.fuel = s0.core.fuel := hfuel4.trans hfuel3_0
                          have hcv4_le : s4.core.cur_vars ≤ c.max_vars := hsp4.1.1.cur_vars_le
                          have hcv4_lt : s4.core.cur_vars < 536870912 := by omega
                          have hpool4 : XorEqPoolOk (cnfOfClauses F_cur) s4.core.cur_vars
                              s4.scratch.scratch_buf eq3.toNat 0 := by
                            rw [hcv4, hscr4]; exact hpool3
                          let scr_pool := s4.scratch.scratch_buf
                          have hscrp_len : scr_pool.length = c.scratch_cap :=
                            hsp4.1.2.scratch_buf_len
                          -- 6 pointer/scalar loads before UF init loop
                          c0_hstraight
                          have hm4_f := focus_full_gauss hm4
                          -- Loop A: UF init (v = 0 .. cv)
                          let Jinit : Tup Val [i64] → Mem 64 → Prop := fun (v, ()) m5 =>
                            ∃ par vc cnt : List (BitVec 32),
                              v.toNat ≤ s4.core.cur_vars ∧
                              par.length = 2 * c.max_vars ∧ vc.length = 2 * c.max_vars ∧
                              cnt.length = 2 * c.max_vars ∧
                              (∀ i < v.toNat, (par[i]?.getD 0#32).toNat = i) ∧
                              (array (t := i32) c.pScratchBuf scr_pool ⋆
                               array (t := i32) c.pWorkStk1 par ⋆
                               array (t := i32) c.pWorkStk2
                                                    s4.scratch.work_stk2 ⋆
                               array (t := i32) c.pTarjanReach vc ⋆
                               array (t := i32) c.pWsort cnt ⋆
                               (FullGaussRest c s4 ⋆ R)) m5
                          refine wp_loop_inv Jinit (fun (v, ()) _ => s4.core.cur_vars - v.toNat)
                            (fun _ h => by
                              c0_hstraight
                              exact h (0#64, ()) m4 ⟨s4.scratch.work_stk1, s4.scratch.tarjan_reach,
                                s4.scratch.wsort, Nat.zero_le _, hsp4.1.2.work_stk1_len,
                                hsp4.1.2.tarjan_reach_len, hsp4.1.2.wsort_len,
                                fun _ hi => absurd hi (Nat.not_lt_zero _), hm4_f⟩) ?_
                          rintro _ ⟨v, _⟩ m5 ⟨par, vc, cnt, hv_le, hlp, hlv, hlk, hinit, hm5⟩ hJi_ih
                          c0_hsplit
                          · have hv_lt : v.toNat < s4.core.cur_vars := by bv_omega
                            have hvp : v.toNat < par.length := by omega
                            have hvv : v.toNat < vc.length := by omega
                            have hvk : v.toNat < cnt.length := by omega
                            have hv32 : (v.setWidth 32).toNat = v.toNat :=
                              bv64_toNat_setWidth32_lt (by omega)
                            c0_hstraight
                            have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
                            refine hJi_ih (v + 1#64, ()) _ (by dsimp only; omega)
                              ⟨par.set v.toNat (v.setWidth 32), vc.set v.toNat 0xFFFFFFFF#32,
                               cnt.set v.toNat 0#32, by omega, by simp [hlp], by simp [hlv],
                               by simp [hlk], ?_, ?_⟩
                            · intro i hi
                              rw [hv1] at hi
                              by_cases hiv : i = v.toNat
                              · subst hiv
                                rw [List.getElem?_set_self hvp, Option.getD_some, hv32]
                              · rw [List.getElem?_set_ne (Ne.symm hiv)]
                                exact hinit i (by omega)
                            · rw [Std.ExtHashMap.sep_emp] at hm
                              change (array (t := i32) c.pWsort (cnt.set v.toNat 0#32) ⋆
                                (array (t := i32) c.pTarjanReach (vc.set v.toNat 0xFFFFFFFF#32) ⋆
                                  (array (t := i32) c.pWorkStk1 (par.set v.toNat (v.setWidth 32)) ⋆
                                    (array (t := i32) c.pScratchBuf scr_pool ⋆
                                      (array (t := i32) c.pWorkStk2 s4.scratch.work_stk2 ⋆
                                        (FullGaussRest c s4 ⋆ R)))))) m at hm
                              ecancel
                          · -- End of Loop A: par[i] = i for all i < cv
                            have hv_eq : v.toNat = s4.core.cur_vars := by bv_omega
                            have hord_init : ∀ i < s4.core.cur_vars,
                                (par[i]?.getD 0#32).toNat ≤ i := fun i hi => by
                              rw [hinit i (by omega)]; exact Nat.le_refl _
                            -- Loop B: UF union pass (p = 0 .. eq3)
                            let Junion_exit : Tup Val [i64] → Mem 64 → Prop := fun (_p, ()) m6 =>
                              ∃ par_u : List (BitVec 32),
                                par_u.length = 2 * c.max_vars ∧
                                (∀ i < s4.core.cur_vars, (par_u[i]?.getD 0#32).toNat ≤ i) ∧
                                UfPoolMerged par_u scr_pool s4.core.cur_vars eq3.toNat eq3.toNat ∧
                                (array (t := i32) c.pScratchBuf scr_pool ⋆
                                 array (t := i32) c.pWorkStk1 par_u ⋆
                                 array (t := i32) c.pWorkStk2
                                                    s4.scratch.work_stk2 ⋆
                                 array (t := i32) c.pTarjanReach vc ⋆
                                 array (t := i32) c.pWsort cnt ⋆
                                 (FullGaussRest c s4 ⋆ R)) m6
                            refine wp_join_group Junion_exit ?_ ?_
                            · -- After Loop B: Loop C (UF flatten pass)
                              rintro _ ⟨_p, _⟩ m6 ⟨par_u, hlpu, hord_u, hmrg_u, hm6⟩
                              let Jflat : Tup Val [i64] → Mem 64 → Prop := fun (vf, ()) m7 =>
                                ∃ par_f : List (BitVec 32),
                                  vf.toNat ≤ s4.core.cur_vars ∧ par_f.length = 2 * c.max_vars ∧
                                  (∀ i < s4.core.cur_vars, (par_f[i]?.getD 0#32).toNat ≤ i) ∧
                                  (∀ i < s4.core.cur_vars,
                                    ufRoot par_f i s4.core.cur_vars =
                                      ufRoot par_u i s4.core.cur_vars) ∧
                                  (∀ i < vf.toNat,
                                    (par_f[i]?.getD 0#32).toNat =
                                      ufRoot par_u i s4.core.cur_vars) ∧
                                  (array (t := i32) c.pScratchBuf scr_pool ⋆
                                   array (t := i32) c.pWorkStk1 par_f ⋆
                                   array (t := i32) c.pWorkStk2
                                                    s4.scratch.work_stk2 ⋆
                                   array (t := i32) c.pTarjanReach vc ⋆
                                   array (t := i32) c.pWsort cnt ⋆
                                   (FullGaussRest c s4 ⋆ R)) m7
                              refine wp_loop_inv Jflat
                                (fun (vf, ()) _ => s4.core.cur_vars - vf.toNat)
                                (fun _ h => by
                                  c0_hstraight
                                  exact h (0#64, ()) m6 ⟨par_u, Nat.zero_le _, hlpu, hord_u,
                                    fun _ _ => rfl, fun _ hi => absurd hi (Nat.not_lt_zero _), hm6⟩)
                                ?_
                              rintro _ ⟨vf, _⟩ m7
                                ⟨par_f, hvf_le, hlpf, hord_f, hrt_f, hflat_f, hm7⟩ hJf_ih
                              c0_hsplit
                              · have hvf_lt : vf.toNat < s4.core.cur_vars := by bv_omega
                                have hvf32 : (vf.setWidth 32).toNat = vf.toNat :=
                                  bv64_toNat_setWidth32_lt (by omega)
                                have hcv64 : (BitVec.ofNat 64 s4.core.cur_vars).toNat =
                                    s4.core.cur_vars := by
                                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                                c0_hstraight
                                apply wp_call_of_spec
                                dsimp only [vals, Arg.val]
                                refine hUfFind _ _ _ _
                                  ⟨par_f,
                                    array (t := i32) c.pScratchBuf scr_pool ⋆
                                    array (t := i32) c.pWorkStk2
                                                    s4.scratch.work_stk2 ⋆
                                    array (t := i32) c.pTarjanReach vc ⋆
                                    array (t := i32) c.pWsort cnt ⋆ (FullGaussRest c s4 ⋆ R),
                                    by rw [hcv64, hlpf]; omega, by rw [hlpf]; omega,
                                    by rw [hvf32, hcv64]; exact hvf_lt,
                                    by rw [hcv64]; exact hord_f, by ecancel,
                                    fun rv par_f1 m7' hlf1 hrv_eq hrv_lt hord_f1 hrt_f1 hfl_f1
                                      _ hm7' => ?_⟩
                                dsimp only
                                rw [hcv64] at hrv_eq hrv_lt hord_f1 hrt_f1 hfl_f1
                                rw [hvf32] at hrv_eq
                                have hvf_len : vf.toNat < par_f1.length := by omega
                                c0_hstraight
                                have hsf := ufRoot_set_flat hord_f1 (by omega) hvf_lt
                                  (by rw [hrv_eq, hrt_f1 vf.toNat hvf_lt])
                                have hvf1 : (vf + 1#64).toNat = vf.toNat + 1 := by bv_omega
                                refine hJf_ih (vf + 1#64, ()) _ (by dsimp only; omega)
                                  ⟨par_f1.set vf.toNat rv, by omega, by simp [hlf1, hlpf],
                                   hsf.1, ?_, ?_, ?_⟩
                                · intro i hi
                                  rw [hsf.2 i hi s4.core.cur_vars hi, hrt_f1 i hi, hrt_f i hi]
                                · intro i hi
                                  rw [hvf1] at hi
                                  by_cases hiv : i = vf.toNat
                                  · subst hiv
                                    rw [List.getElem?_set_self hvf_len, Option.getD_some,
                                      hrv_eq, hrt_f vf.toNat hvf_lt]
                                  · rw [List.getElem?_set_ne (Ne.symm hiv)]
                                    have hfl0 : (par_f[i]?.getD 0#32).toNat =
                                        ufRoot par_f i s4.core.cur_vars := by
                                      rw [hrt_f i (by omega), hflat_f i (by omega)]
                                    rw [hfl_f1 i (by omega) hfl0, hflat_f i (by omega)]
                                · ecancel
                              · -- End of Loop C: par_f is flattened -> XorPoolCompClosed!
                                have hvf_eq : vf.toNat = s4.core.cur_vars := by bv_omega
                                have hclosed : XorPoolCompClosed par_f scr_pool eq3.toNat :=
                                  xorPoolCompClosed_of_flat hpool4 hmrg_u fun i hi =>
                                    hflat_f i (by omega)
                                -- Loop D: comp_eq_cnt count pass
                                let Jcnt_exit : Tup Val [i64] → Mem 64 → Prop := fun (_p, ()) m8 =>
                                  ∃ cnt_d : List (BitVec 32),
                                    cnt_d.length = 2 * c.max_vars ∧
                                    (array (t := i32) c.pScratchBuf scr_pool ⋆
                                     array (t := i32) c.pWorkStk1 par_f ⋆
                                     array (t := i32) c.pWorkStk2
                                                    s4.scratch.work_stk2 ⋆
                                     array (t := i32) c.pTarjanReach vc ⋆
                                     array (t := i32) c.pWsort cnt_d ⋆
                                     (FullGaussRest c s4 ⋆ R)) m8
                                refine wp_join_group Jcnt_exit ?_ ?_
                                · -- After Loop D: Unfocus & Loop E (component loop)
                                  rintro _ ⟨_p, _⟩ m8 ⟨cnt_d, hlk_d, hm8⟩
                                  have hm8_full := unfocus_full_gauss hm8
                                  let s5 : FullState :=
                                    { s4 with scratch :=
                                      { s4.scratch with
                                        scratch_buf := scr_pool
                                        work_stk1 := par_f
                                        work_stk2 := s4.scratch.work_stk2
                                        tarjan_reach := vc
                                        wsort := cnt_d } }
                                  have hsp5 : FullSparseInvW c F0 F_cur s5 :=
                                    fullSparseInvW_upd_gauss hsp4 rfl
                                      (by rw [hlpf, hsp4.1.2.work_stk1_len]) rfl
                                      (by rw [hlv, hsp4.1.2.tarjan_reach_len])
                                      (by rw [hlk_d, hsp4.1.2.wsort_len])
                                  -- Loop E: while (root < cv && budget < 4000000)
                                  let Jcomp : Tup Val [i64, i64, i64] → Mem 64 → Prop :=
                                    fun (_vc, _bud, root, ()) m9 =>
                                      ∃ sc : FullState,
                                        FullSparseInvW c F0 F_cur sc ∧
                                        sc.core.cur_vars = s4.core.cur_vars ∧
                                        sc.core.cur_level = 0 ∧
                                        sc.core.fuel = s0.core.fuel ∧
                                        root.toNat ≤ s4.core.cur_vars ∧
                                        sc.scratch.work_stk1 = par_f ∧
                                        (∀ i < eq3.toNat,
                                          sc.scratch.scratch_buf[i]? = scr_pool[i]?) ∧
                                        (FullMem c sc ⋆ R) m9
                                  refine wp_loop_inv Jcomp
                                    (fun (_vc, _bud, root, ()) _ => s4.core.cur_vars - root.toNat)
                                    (fun _ h => by
                                      c0_hstraight
                                      exact h (vf, 0#64, 0#64, ()) m8
                                        ⟨s5, hsp5, rfl, hlvl4, hfuel4_0, Nat.zero_le _, rfl,
                                         fun _ _ => rfl, hm8_full⟩) ?_
                                  rintro _ ⟨vc_arg, bud, root, _⟩ m9
                                    ⟨sc, hsp_c, hcv_c, hlvl_c, hfuel_c, hrt_le, hpar_c, hpre_c,
                                     hm9⟩ hJc_ih
                                  c0_hsplit
                                  · c0_hsplit
                                    · have hrt_lt : root.toNat < s4.core.cur_vars := by bv_omega
                                      let Jc_step : Tup Val [i64, i64] → Mem 64 → Prop :=
                                        fun (_vc1, _bud1, ()) m10 =>
                                          ∃ sc1 : FullState,
                                            FullSparseInvW c F0 F_cur sc1 ∧
                                            sc1.core.cur_vars = s4.core.cur_vars ∧
                                            sc1.core.cur_level = 0 ∧
                                            sc1.core.fuel = s0.core.fuel ∧
                                            sc1.scratch.work_stk1 = par_f ∧
                                            (∀ i < eq3.toNat,
                                              sc1.scratch.scratch_buf[i]? = scr_pool[i]?) ∧
                                            (FullMem c sc1 ⋆ R) m10
                                      refine wp_join_group Jc_step ?_ ?_
                                      · rintro _ ⟨vc1, bud1, _⟩ m10
                                          ⟨sc1, hsp10, hcv10, hlvl10, hfuel10, hpar10, hpre10, hm10⟩
                                        c0_hstraight
                                        have hrt1 : (root + 1#64).toNat = root.toNat + 1 := by
                                          bv_omega
                                        exact hJc_ih (vc1, bud1, root + 1#64, ()) m10
                                          (by dsimp only; omega)
                                          ⟨sc1, hsp10, hcv10, hlvl10, hfuel10, by omega, hpar10,
                                           hpre10, hm10⟩
                                      · intro _ hJc_step
                                        have hrt_par :
                                            root.toNat < sc.scratch.work_stk1.length := by
                                          rw [hsp_c.1.2.work_stk1_len]; omega
                                        have hrt_cnt : root.toNat < sc.scratch.wsort.length := by
                                          rw [hsp_c.1.2.wsort_len]; omega
                                        c0_hstraight
                                        c0_hsplit
                                        · c0_hstraight
                                          c0_hsplit
                                          · -- Inner loop: build var_col and c2v
                                            let Jcol : Tup Val [i64, i64] → Mem 64 → Prop :=
                                              fun (vcol, ncols, ()) m10 =>
                                                ∃ vc_i c2v_i : List (BitVec 32),
                                                  vcol.toNat ≤ s4.core.cur_vars ∧
                                                  ncols.toNat ≤ vcol.toNat ∧
                                                  vc_i.length = 2 * c.max_vars ∧
                                                  c2v_i.length = 2 * c.max_vars ∧
                                                  (∀ u < vcol.toNat,
                                                    (par_f[u]?.getD 0#32).toNat = root.toNat →
                                                    (vc_i[u]?.getD 0#32).toNat < ncols.toNat ∧
                                                    (c2v_i[(vc_i[u]?.getD 0#32).toNat]?.getD
                                                      0#32).toNat
                                                      = u) ∧
                                                  (∀ col < ncols.toNat,
                                                    (c2v_i[col]?.getD 0#32).toNat < vcol.toNat) ∧
                                                  (FullMem c { sc with scratch :=
                                                    { sc.scratch with
                                                      tarjan_reach := vc_i
                                                      work_stk2 := c2v_i } } ⋆ R) m10
                                            refine wp_loop_inv Jcol
                                              (fun (vcol, _, ()) _ => s4.core.cur_vars - vcol.toNat)
                                              (fun _ h => by
                                                c0_hstraight
                                                exact h (0#64, 0#64, ()) m9
                                                  ⟨sc.scratch.tarjan_reach, sc.scratch.work_stk2,
                                                   Nat.zero_le _, Nat.le_refl _,
                                                   hsp_c.1.2.tarjan_reach_len,
                                                   hsp_c.1.2.work_stk2_len,
                                                   fun _ hu => absurd hu (Nat.not_lt_zero _),
                                                   fun _ hc => absurd hc (Nat.not_lt_zero _),
                                                   hm9⟩) ?_
                                            rintro _ ⟨vcol, ncols, _⟩ m10
                                              ⟨vc_i, c2v_i, hvcol_le, hnc_le, hlvc, hlc2, hmap,
                                               hc2v_lt, hm10⟩ hJcol_ih
                                            c0_hsplit
                                            · have hvcol_lt : vcol.toNat < s4.core.cur_vars := by
                                                bv_omega
                                              let Jcol_step : Tup Val [i64] → Mem 64 → Prop :=
                                                fun (ncols', ()) m11 =>
                                                  ∃ vc_n c2v_n : List (BitVec 32),
                                                    ncols'.toNat ≤ vcol.toNat + 1 ∧
                                                    vc_n.length = 2 * c.max_vars ∧
                                                    c2v_n.length = 2 * c.max_vars ∧
                                                    (∀ u < vcol.toNat + 1,
                                                      (par_f[u]?.getD 0#32).toNat = root.toNat →
                                                      (vc_n[u]?.getD 0#32).toNat < ncols'.toNat ∧
                                                      (c2v_n[(vc_n[u]?.getD 0#32).toNat]?.getD
                                                        0#32).toNat = u) ∧
                                                    (∀ col < ncols'.toNat,
                                                      (c2v_n[col]?.getD 0#32).toNat <
                                                        vcol.toNat + 1) ∧
                                                    (FullMem c { sc with scratch :=
                                                      { sc.scratch with
                                                        tarjan_reach := vc_n
                                                        work_stk2 := c2v_n } } ⋆ R) m11
                                              refine wp_join_group Jcol_step ?_ ?_
                                              · rintro _ ⟨ncols', _⟩ m11
                                                  ⟨vc_n, c2v_n, hnc_n, hlvc_n, hlc2_n, hmap_n,
                                                   hc2v_n, hm11⟩
                                                c0_hstraight
                                                have hvcol1 : (vcol + 1#64).toNat =
                                                    vcol.toNat + 1 := by bv_omega
                                                exact hJcol_ih (vcol + 1#64, ncols', ()) m11
                                                  (by dsimp only; omega)
                                                  ⟨vc_n, c2v_n, by omega, by omega, hlvc_n, hlc2_n,
                                                   by rw [hvcol1]; exact hmap_n,
                                                   by rw [hvcol1]; exact hc2v_n, hm11⟩
                                              · intro _ hJcol_step
                                                have hvcol_par :
                                                    vcol.toNat < sc.scratch.work_stk1.length := by
                                                  rw [hsp_c.1.2.work_stk1_len]; omega
                                                c0_hstraight
                                                c0_hsplit
                                                · have hpar_eq :
                                                      (par_f[vcol.toNat]?.getD 0#32).toNat =
                                                        root.toNat := by
                                                    rw [← hpar_c,
                                                      List.getElem?_eq_getElem hvcol_par,
                                                      Option.getD_some]
                                                    bv_omega
                                                  have hvcol_vc : vcol.toNat < vc_i.length := by
                                                    omega
                                                  have hnc_c2v : ncols.toNat < c2v_i.length := by
                                                    omega
                                                  have hnc32 : (ncols.setWidth 32).toNat =
                                                      ncols.toNat :=
                                                    bv64_toNat_setWidth32_lt (by omega)
                                                  have hvcol32 : (vcol.setWidth 32).toNat =
                                                      vcol.toNat :=
                                                    bv64_toNat_setWidth32_lt (by omega)
                                                  have hnc1 : (ncols + 1#64).toNat =
                                                      ncols.toNat + 1 := by bv_omega
                                                  c0_hstraight
                                                  refine hJcol_step (ncols + 1#64, ()) _
                                                    ⟨vc_i.set vcol.toNat (ncols.setWidth 32),
                                                     c2v_i.set ncols.toNat (vcol.setWidth 32),
                                                     by omega, by simp [hlvc], by simp [hlc2],
                                                     ?_, ?_, hm⟩
                                                  · intro u hu hpu
                                                    by_cases huv : u = vcol.toNat
                                                    · subst huv
                                                      rw [List.getElem?_set_self hvcol_vc,
                                                        Option.getD_some, hnc32,
                                                        List.getElem?_set_self hnc_c2v,
                                                        Option.getD_some, hvcol32]
                                                      exact ⟨by omega, rfl⟩
                                                    · have hu_lt : u < vcol.toNat := by omega
                                                      have ⟨h1, h2⟩ := hmap u hu_lt hpu
                                                      rw [List.getElem?_set_ne (Ne.symm huv),
                                                        List.getElem?_set_ne (by omega)]
                                                      exact ⟨by omega, h2⟩
                                                  · intro col hcol
                                                    rw [hnc1] at hcol
                                                    by_cases hcn : col = ncols.toNat
                                                    · subst hcn
                                                      rw [List.getElem?_set_self hnc_c2v,
                                                        Option.getD_some, hvcol32]; omega
                                                    · rw [List.getElem?_set_ne (Ne.symm hcn)]
                                                      have := hc2v_lt col (by omega); omega
                                                · have hpar_ne :
                                                      (par_f[vcol.toNat]?.getD 0#32).toNat ≠
                                                        root.toNat := by
                                                    rw [← hpar_c,
                                                      List.getElem?_eq_getElem hvcol_par,
                                                      Option.getD_some]
                                                    bv_omega
                                                  refine hJcol_step (ncols, ()) m10
                                                    ⟨vc_i, c2v_i, by omega, hlvc, hlc2, ?_, ?_,
                                                     hm10⟩
                                                  · intro u hu hpu
                                                    have huv : u ≠ vcol.toNat := fun h =>
                                                      hpar_ne (h ▸ hpu)
                                                    exact hmap u (by omega) hpu
                                                  · intro col hcol
                                                    have := hc2v_lt col hcol; omega
                                            · -- End of inner col loop: ncols, vc_i, c2v_i built!
                                              have hvcol_eq : vcol.toNat = s4.core.cur_vars := by
                                                bv_omega
                                              let sc_b : FullState :=
                                                { sc with scratch :=
                                                  { sc.scratch with
                                                    tarjan_reach := vc_i
                                                    work_stk2 := c2v_i } }
                                              have hsp_cb : FullSparseInvW c F0 F_cur sc_b :=
                                                fullSparseInvW_upd_work_stk2
                                                  (fullSparseInvW_upd_tarjan_reach hsp_c
                                                    (by rw [hlvc, hsp_c.1.2.tarjan_reach_len]))
                                                  (by rw [hlc2, hsp_c.1.2.work_stk2_len])
                                              let Jnc_exit : Tup Val [i64] → Mem 64 → Prop :=
                                                fun (_bud1, ()) m11 =>
                                                  ∃ sc1 : FullState,
                                                    FullSparseInvW c F0 F_cur sc1 ∧
                                                    sc1.core.cur_vars = s4.core.cur_vars ∧
                                                    sc1.core.cur_level = 0 ∧
                                                    sc1.core.fuel = s0.core.fuel ∧
                                                    sc1.scratch.work_stk1 = par_f ∧
                                                    (∀ i < eq3.toNat,
                                                      sc1.scratch.scratch_buf[i]? = scr_pool[i]?) ∧
                                                    (FullMem c sc1 ⋆ R) m11
                                              refine wp_join_group Jnc_exit ?_ ?_
                                              · rintro _ ⟨bud1, _⟩ m11
                                                  ⟨sc1, hsp11, hcv11, hlvl11, hfuel11, hpar11,
                                                   hpre11, hm11⟩
                                                exact hJc_step (vcol, bud1, ()) m11
                                                  ⟨sc1, hsp11, hcv11, hlvl11, hfuel11, hpar11,
                                                   hpre11, hm11⟩
                                              · intro _ hJnc_exit
                                                c0_hsplit
                                                · -- ncols > 0: build_mat -> rref -> emit_mat
                                                  have hnc_pos : 0 < ncols.toNat := by bv_omega
                                                  have hpool_cb : XorEqPoolOk (cnfOfClauses F_cur)
                                                      sc_b.core.cur_vars sc_b.scratch.scratch_buf
                                                      eq3.toNat 0 := by
                                                    rw [show sc_b.core.cur_vars =
                                                      s4.core.cur_vars from hcv_c]
                                                    exact xorEqPoolOk_congr hpool4
                                                      fun i _ hi => hpre_c i hi
                                                  have hclosed_cb : XorPoolCompClosed
                                                      sc_b.scratch.work_stk1
                                                      sc_b.scratch.scratch_buf eq3.toNat := by
                                                    change XorPoolCompClosed sc.scratch.work_stk1
                                                      sc.scratch.scratch_buf eq3.toNat
                                                    rw [hpar_c]
                                                    exact xorPoolCompClosed_congr hclosed hpool4
                                                      hpre_c
                                                  c0_hstraight
                                                  apply wp_call_of_spec
                                                  dsimp only [vals, Arg.val]
                                                  refine hBuildMat _ _ _ _
                                                    ⟨c, F0, F_cur, sc_b, R, rfl, hsp_cb, heq3_le,
                                                     hnc_pos, by rw [hcv_c]; omega, hpool_cb,
                                                     hclosed_cb, ?_, hm10,
                                                     fun nrows scr_m m11 hlm hpre_m hbd_m hmat_m
                                                       hm11 => ?_⟩
                                                  · intro u hu hpu
                                                    change
                                                      (sc.scratch.work_stk1[u]?.getD 0#32).toNat
                                                      = root.toNat at hpu
                                                    rw [hpar_c] at hpu
                                                    exact hmap u
                                                      (by rw [hvcol_eq, ← hcv_c]; exact hu)
                                                      hpu
                                                  · dsimp only
                                                    let sc_m : FullState :=
                                                      { sc_b with scratch :=
                                                        { sc_b.scratch with scratch_buf := scr_m } }
                                                    have hsp_cm : FullSparseInvW c F0 F_cur sc_m :=
                                                      fullSparseInvW_upd_scratch_buf hsp_cb
                                                        (by rw [hlm, hsp_cb.1.2.scratch_buf_len])
                                                    have hpre_m0 : ∀ i < eq3.toNat,
                                                        scr_m[i]? = scr_pool[i]? := fun i hi =>
                                                      (hpre_m i hi).trans (hpre_c i hi)
                                                    let Jnr_exit : Mem 64 → Prop := fun m12 =>
                                                      ∃ sc1 : FullState,
                                                        FullSparseInvW c F0 F_cur sc1 ∧
                                                        sc1.core.cur_vars = s4.core.cur_vars ∧
                                                        sc1.core.cur_level = 0 ∧
                                                        sc1.core.fuel = s0.core.fuel ∧
                                                        sc1.scratch.work_stk1 = par_f ∧
                                                        (∀ i < eq3.toNat,
                                                          sc1.scratch.scratch_buf[i]? =
                                                            scr_pool[i]?) ∧
                                                        (FullMem c sc1 ⋆ R) m12
                                                    refine wp_join0 Jnr_exit ?_ ?_
                                                    · rintro _ m12
                                                        ⟨sc1, hsp12, hcv12, hlvl12, hfuel12,
                                                         hpar12, hpre12, hm12⟩
                                                      exact hJnc_exit (bud + nrows + eq3, ()) m12
                                                        ⟨sc1, hsp12, hcv12, hlvl12, hfuel12,
                                                         hpar12, hpre12, hm12⟩
                                                    · intro _ hJnr_exit
                                                      c0_hsplit
                                                      · -- nrows >= 2: rref -> emit_mat
                                                        have hnr32 : nrows.toNat < 2 ^ 32 := by
                                                          have hw_pos :
                                                              0 < 2 * ((ncols.toNat + 64) / 64) :=
                                                            by
                                                            omega
                                                          have := Nat.mul_le_mul_left nrows.toNat
                                                            hw_pos
                                                          omega
                                                        have hm11_f := focus_full_scr_buf hm11
                                                        c0_hstraight
                                                        apply wp_call_of_spec
                                                        dsimp only [vals, Arg.val]
                                                        refine hRref _ _ _ _
                                                          ⟨cnfOfClauses F_cur, c2v_i, scr_m,
                                                           FullScrBufRest c sc_m ⋆ R,
                                                           by rw [hlm]; exact hbd_m,
                                                           by rw [hlm]; omega, by omega, hnr32,
                                                           hmat_m, hm11_f,
                                                           fun scr_r m12 hlr hpre_r hmat_r hm12 =>
                                                             ?_⟩
                                                        dsimp only
                                                        have hm12_full := unfocus_full_scr_buf hm12
                                                        let sc_r : FullState :=
                                                          { sc_m with scratch :=
                                                            { sc_m.scratch with
                                                              scratch_buf := scr_r } }
                                                        have hsp_cr :
                                                            FullSparseInvW c F0 F_cur sc_r :=
                                                          fullSparseInvW_upd_scratch_buf hsp_cm
                                                            (by
                                                              rw [hlr, hsp_cm.1.2.scratch_buf_len])
                                                        have hpre_r0 : ∀ i < eq3.toNat,
                                                            scr_r[i]? = scr_pool[i]? := fun i hi =>
                                                          (hpre_r i (Or.inl hi)).trans
                                                            (hpre_m0 i hi)
                                                        c0_hstraight
                                                        apply wp_call_of_spec
                                                        dsimp only [vals, Arg.val]
                                                        refine hEmitMat _ _ _ _
                                                          ⟨c, F0, F_cur, sc_r, R, rfl, hsp_cr,
                                                           hlvl_c, hbd_m, by rw [hcv_c]; omega,
                                                           hnr32,
                                                           fun col hcol => by
                                                             have := hc2v_lt col hcol
                                                             rw [hvcol_eq] at this
                                                             simpa [sc_r, sc_m, sc_b, hcv_c] using
                                                               this,
                                                           hmat_r, hm12_full,
                                                           fun erm sc_e m13 hsp_e hcv_e hlvl_e
                                                             hfuel_e hscr_e hws1_e _ _ herm20
                                                             hm13 => ?_⟩
                                                        dsimp only
                                                        c0_hsplit
                                                        · c0_hstraight
                                                          have h20 : erm = 20#64 := by bv_omega
                                                          exact hQ 20#64 sc_e m13 hsp_e.toSparse
                                                            hlvl_e
                                                            (by
                                                              rw [hfuel_e, hfuel_c]
                                                              exact Nat.le_refl _)
                                                            (Or.inr rfl) (fun _ => herm20 h20) hm13
                                                        · exact hJnr_exit m13
                                                            ⟨sc_e, hsp_e, hcv_e.trans hcv_c, hlvl_e,
                                                             hfuel_e.trans hfuel_c,
                                                             hws1_e.trans hpar_c,
                                                             fun i hi => by
                                                               rw [hscr_e]; exact hpre_r0 i hi,
                                                             hm13⟩
                                                      · exact hJnr_exit m11
                                                          ⟨sc_m, hsp_cm, hcv_c, hlvl_c, hfuel_c,
                                                           hpar_c, hpre_m0, hm11⟩
                                                · exact hJnc_exit (bud, ()) m10
                                                    ⟨sc_b, hsp_cb, hcv_c, hlvl_c, hfuel_c, hpar_c,
                                                     hpre_c, hm10⟩
                                          · exact hJc_step (vc_arg, bud, ()) m9
                                              ⟨sc, hsp_c, hcv_c, hlvl_c, hfuel_c, hpar_c, hpre_c,
                                               hm9⟩
                                        · exact hJc_step (vc_arg, bud, ()) m9
                                            ⟨sc, hsp_c, hcv_c, hlvl_c, hfuel_c, hpar_c, hpre_c, hm9⟩
                                    · exact hJpost m9 ⟨sc, hsp_c, hlvl_c,
                                        by rw [hfuel_c]; exact Nat.le_refl _, hm9⟩
                                  · exact hJpost m9 ⟨sc, hsp_c, hlvl_c,
                                      by rw [hfuel_c]; exact Nat.le_refl _, hm9⟩
                                · -- Loop D body: comp_eq_cnt count pass
                                  intro _ hJcnt_exit
                                  let Jcnt : Tup Val [i64] → Mem 64 → Prop := fun (pc, ()) m8 =>
                                    ∃ cnt_c : List (BitVec 32),
                                      pc.toNat ≤ eq3.toNat ∧ cnt_c.length = 2 * c.max_vars ∧
                                      XorEqPoolOk (cnfOfClauses F_cur) s4.core.cur_vars scr_pool
                                        eq3.toNat pc.toNat ∧
                                      (array (t := i32) c.pScratchBuf scr_pool ⋆
                                       array (t := i32) c.pWorkStk1 par_f ⋆
                                       array (t := i32) c.pWorkStk2
                                                    s4.scratch.work_stk2 ⋆
                                       array (t := i32) c.pTarjanReach vc ⋆
                                       array (t := i32) c.pWsort cnt_c ⋆
                                       (FullGaussRest c s4 ⋆ R)) m8
                                  refine wp_loop_inv Jcnt (fun (pc, ()) _ => eq3.toNat - pc.toNat)
                                    (fun _ h => by
                                      c0_hstraight
                                      exact h (0#64, ()) m7 ⟨cnt, Nat.zero_le _, hlk, hpool4, hm7⟩)
                                    ?_
                                  rintro _ ⟨pc, _⟩ m8 ⟨cnt_c, hpc_le, hlk_c, hpool_pc, hm8⟩ hJcnt_ih
                                  c0_hsplit
                                  · have hpc_lt : pc.toNat < eq3.toNat := by bv_omega
                                    generalize hpcn_eq : pc.toNat = pcn at hpool_pc
                                    cases hpool_pc with
                                    | done => omega
                                    | @step _ hdr st cl _ hhdr hst hcl hbd hbody hrest =>
                                      rw [← hpcn_eq] at hhdr hbd hbody hrest
                                      have hpc_scr : pc.toNat < scr_pool.length := by omega
                                      c0_hstraight
                                      have hhdr_eq : scr_pool[pc.toNat]'hpc_scr = hdr := by
                                        have := List.getElem?_eq_getElem hpc_scr
                                        rw [hhdr] at this; exact Option.some.inj this.symm
                                      have hst_c0 :
                                          (BitVec.setWidth 64
                                            (hdr >>> OfNat.ofNat 16 &&&
                                              (32767 : BitVec 32))).toNat =
                                          st := by
                                        rw [bv_zext32_toNat]; exact hst.symm
                                      have hst_nat :
                                          (hdr.toNat / 2 ^ OfNat.ofNat 16 &&& 32767 % 2 ^ 32) =
                                          st := by
                                        have := hst_c0
                                        rwa [bv_zext32_toNat, BitVec.toNat_and,
                                          BitVec.toNat_ushiftRight,
                                          Nat.shiftRight_eq_div_pow] at this
                                      have hst_nat' :
                                          (hdr >>> OfNat.ofNat 16 &&& (32767 : BitVec 32)).toNat =
                                          st := by
                                        rw [BitVec.toNat_and, BitVec.toNat_ushiftRight,
                                          Nat.shiftRight_eq_div_pow]
                                        exact hst_nat
                                      have hcl_c0 :
                                          (BitVec.setWidth 64
                                            (hdr &&& (65535 : BitVec 32))).toNat = cl := by
                                        rw [bv_zext32_toNat]; exact hcl.symm
                                      have hcl_nat : (hdr.toNat &&& 65535 % 2 ^ 32) = cl := by
                                        have := hcl_c0
                                        rwa [bv_zext32_toNat, BitVec.toNat_and] at this
                                      c0_hsplit
                                      · exfalso; rw [hhdr_eq] at hc
                                        have := hst_nat; have := hst_nat'; bv_omega
                                      · let Jcnt_step : Mem 64 → Prop := fun m8' =>
                                          ∃ cnt_n : List (BitVec 32),
                                            cnt_n.length = 2 * c.max_vars ∧
                                            (array (t := i32) c.pScratchBuf scr_pool ⋆
                                             array (t := i32) c.pWorkStk1 par_f ⋆
                                             array (t := i32) c.pWorkStk2
                                                    s4.scratch.work_stk2 ⋆
                                             array (t := i32) c.pTarjanReach vc ⋆
                                             array (t := i32) c.pWsort cnt_n ⋆
                                             (FullGaussRest c s4 ⋆ R)) m8'
                                        refine wp_join0 Jcnt_step ?_ ?_
                                        · rintro _ m8' ⟨cnt_n, hlk_n, hm8'⟩
                                          c0_hstraight
                                          have hpc_next :
                                              (pc + (1 : BitVec 64) +
                                                BitVec.setWidth 64
                                                  ((scr_pool[pc.toNat]'hpc_scr) >>> OfNat.ofNat 16
                                                    &&& (32767 : BitVec 32))).toNat =
                                              pc.toNat + 1 + st := by
                                            rw [hhdr_eq]; have := hst_nat'; bv_omega
                                          refine hJcnt_ih _ m8'
                                            (by dsimp only; rw [hpc_next]; omega)
                                            ⟨cnt_n, by rw [hpc_next]; omega, hlk_n,
                                             by rw [hpc_next]; exact hrest, hm8'⟩
                                        · intro _ hJcnt_step
                                          c0_hsplit
                                          · c0_hsplit
                                            · have hcl_pos : 0 < cl := by
                                                rw [hhdr_eq] at *; have := hcl_nat; bv_omega
                                              have hcl_le : cl ≤ st := by
                                                rw [hhdr_eq] at hc; have := hcl_nat
                                                have := hst_nat; bv_omega
                                              have hp1_nat : (pc + 1#64).toNat = pc.toNat + 1 := by
                                                bv_omega
                                              have hp1_lt :
                                                  (pc + 1#64).toNat < scr_pool.length := by
                                                rw [hp1_nat]; omega
                                              c0_hstraight
                                              refine wp_join0 Jcnt_step
                                                (fun _ m h => hJcnt_step m h)
                                                ?_
                                              intro _ hJcnt1
                                              c0_hsplit
                                              · rcases hbody with rfl | ⟨_, _, _, hvars_lt, _⟩
                                                · exfalso; omega
                                                · have hv0_lt :
                                                      (scr_pool[(pc + 1#64).toNat]'hp1_lt).toNat <
                                                        s4.core.cur_vars := by
                                                    have h0m := hvars_lt _ (List.mem_map.mpr
                                                      ⟨0, List.mem_range.mpr hcl_pos, rfl⟩)
                                                    rwa [Nat.add_zero, List.getElem?_eq_getElem
                                                      (by rw [← hp1_nat]; exact hp1_lt),
                                                      Option.getD_some,
                                                      list_getElem_congr hp1_nat.symm _ _] at h0m
                                                  have hv0_par :
                                                      ((scr_pool[(pc + 1#64).toNat]'hp1_lt).setWidth
                                                        64).toNat < par_f.length := by
                                                    rw [bv_zext32_toNat]; omega
                                                  c0_hstraight
                                                  refine wp_join0 Jcnt_step
                                                    (fun _ m h => hJcnt1 m h) ?_
                                                  intro _ hJcnt2
                                                  c0_hsplit
                                                  · have hrt_c_lt :
                                                        (par_f[((scr_pool[(pc + 1#64).toNat]'
                                                          hp1_lt).setWidth 64).toNat]'
                                                          hv0_par).toNat <
                                                          s4.core.cur_vars := by
                                                      have hord := hord_f _ hv0_lt
                                                      have hv0_p :
                                                          (scr_pool[(pc + 1#64).toNat]'
                                                            hp1_lt).toNat < par_f.length := by
                                                        rw [bv_zext32_toNat] at hv0_par
                                                        exact hv0_par
                                                      have hpeq :
                                                          par_f[((scr_pool[(pc + 1#64).toNat]'
                                                            hp1_lt).setWidth 64).toNat]'hv0_par =
                                                          par_f[(scr_pool[(pc + 1#64).toNat]'
                                                            hp1_lt).toNat]'hv0_p :=
                                                        list_getElem_congr (bv_zext32_toNat _)
                                                          hv0_par hv0_p
                                                      rw [hpeq]
                                                      rw [List.getElem?_eq_getElem hv0_p,
                                                        Option.getD_some] at hord
                                                      omega
                                                    have hrt_cnt_lt :
                                                        ((par_f[((scr_pool[(pc + 1#64).toNat]'
                                                          hp1_lt).setWidth 64).toNat]'
                                                            hv0_par).setWidth 64).toNat <
                                                          cnt_c.length := by
                                                      have hv_lt_c := hord_f _ hv0_lt
                                                      have hv0_p :
                                                          (scr_pool[(pc + 1#64).toNat]'
                                                            hp1_lt).toNat < par_f.length := by
                                                        rw [bv_zext32_toNat] at hv0_par
                                                        exact hv0_par
                                                      have hpeq :
                                                          par_f[((scr_pool[(pc + 1#64).toNat]'
                                                            hp1_lt).setWidth 64).toNat]'hv0_par =
                                                          par_f[(scr_pool[(pc + 1#64).toNat]'
                                                            hp1_lt).toNat]'hv0_p :=
                                                        list_getElem_congr (bv_zext32_toNat _)
                                                          hv0_par hv0_p
                                                      rw [bv_zext32_toNat, hpeq]
                                                      rw [List.getElem?_eq_getElem hv0_p,
                                                        Option.getD_some] at hv_lt_c
                                                      omega
                                                    c0_hstraight
                                                    refine hJcnt2 _ ⟨_, ?_,
                                                      by rw [Std.ExtHashMap.sep_emp] at hm; ecancel⟩
                                                    simp [hlk_c]
                                                  · exact hJcnt2 m8 ⟨cnt_c, hlk_c, hm8⟩
                                              · exact hJcnt1 m8 ⟨cnt_c, hlk_c, hm8⟩
                                            · exact hJcnt_step m8 ⟨cnt_c, hlk_c, hm8⟩
                                          · exact hJcnt_step m8 ⟨cnt_c, hlk_c, hm8⟩
                                  · exact hJcnt_exit (pc, ()) m8 ⟨cnt_c, hlk_c, hm8⟩
                            · -- Loop B body: UF union pass
                              intro _ hJunion_exit
                              let Junion : Tup Val [i64] → Mem 64 → Prop := fun (pu, ()) m6 =>
                                ∃ par_p : List (BitVec 32),
                                  pu.toNat ≤ eq3.toNat ∧ par_p.length = 2 * c.max_vars ∧
                                  (∀ i < s4.core.cur_vars, (par_p[i]?.getD 0#32).toNat ≤ i) ∧
                                  XorEqPoolOk (cnfOfClauses F_cur) s4.core.cur_vars scr_pool
                                    eq3.toNat pu.toNat ∧
                                  (∀ q ∈ poolStarts scr_pool eq3.toNat 0 eq3.toNat,
                                    pu.toNat ≤ q →
                                      q ∈ poolStarts scr_pool eq3.toNat pu.toNat
                                        (eq3.toNat - pu.toNat)) ∧
                                  UfPoolMerged par_p scr_pool s4.core.cur_vars eq3.toNat pu.toNat ∧
                                  (array (t := i32) c.pScratchBuf scr_pool ⋆
                                   array (t := i32) c.pWorkStk1 par_p ⋆
                                   array (t := i32) c.pWorkStk2
                                                    s4.scratch.work_stk2 ⋆
                                   array (t := i32) c.pTarjanReach vc ⋆
                                   array (t := i32) c.pWsort cnt ⋆
                                   (FullGaussRest c s4 ⋆ R)) m6
                              refine wp_loop_inv Junion (fun (pu, ()) _ => eq3.toNat - pu.toNat)
                                (fun _ h => by
                                  c0_hstraight
                                  exact h (0#64, ()) m5 ⟨par, Nat.zero_le _, hlp, hord_init, hpool4,
                                    fun q hq _ => by simpa using hq,
                                    fun _ _ hlt => absurd hlt (Nat.not_lt_zero _), hm5⟩) ?_
                              rintro _ ⟨pu, _⟩ m6
                                ⟨par_p, hpu_le, hlpp, hord_p, hpool_pu, hstarts_pu, hmrg_p, hm6⟩
                                hJu_ih
                              c0_hsplit
                              · have hpu_lt : pu.toNat < eq3.toNat := by bv_omega
                                generalize hpun_eq : pu.toNat = pun at hpool_pu
                                cases hpool_pu with
                                | done => omega
                                | @step _ hdr st cl _ hhdr hst hcl hbd hbody hrest =>
                                  rw [← hpun_eq] at hhdr hbd hbody hrest
                                  have hpu_scr : pu.toNat < scr_pool.length := by omega
                                  have hpu_next_starts :
                                      ∀ q ∈ poolStarts scr_pool eq3.toNat 0 eq3.toNat,
                                        pu.toNat + 1 + st ≤ q →
                                          q ∈ poolStarts scr_pool eq3.toNat (pu.toNat + 1 + st)
                                            (eq3.toNat - (pu.toNat + 1 + st)) := by
                                    intro q hq hqge
                                    have hq1 := hstarts_pu q hq (by omega)
                                    have hsub : eq3.toNat - pu.toNat =
                                        (eq3.toNat - pu.toNat - 1) + 1 := by omega
                                    rw [hsub, poolStarts_step_iff hpu_lt] at hq1
                                    have hst' :
                                        (((scr_pool[pu.toNat]?.getD 0#32) >>> 16#32) &&&
                                          0x7FFF#32).toNat = st := by simp [hhdr, hst]
                                    rw [hst'] at hq1
                                    rcases hq1 with rfl | ⟨_, hr⟩
                                    · omega
                                    · -- Need exact fuel reduction: eq3 - (pu + 1 + st)
                                      have hstep_fuel : ∀ {p0 : Nat},
                                          XorEqPoolOk (cnfOfClauses F_cur) s4.core.cur_vars
                                            scr_pool eq3.toNat p0 →
                                          ∀ f q, q ∈ poolStarts scr_pool eq3.toNat p0 f →
                                            q ∈ poolStarts scr_pool eq3.toNat p0
                                              (eq3.toNat - p0) := by
                                        intro p0 hx
                                        induction hx with
                                        | done =>
                                          intro f q hq0
                                          cases f with
                                          | zero => exact nomatch hq0
                                          | succ f' => simp [poolStarts] at hq0
                                        | @step p1 h1 s1 c1 hp1 hh1 hs1 _ hb1 _ hr1 ih1 =>
                                          intro f q hq0
                                          cases f with
                                          | zero => exact nomatch hq0
                                          | succ f' =>
                                            rw [poolStarts_step_iff hp1] at hq0
                                            have hsub1 : eq3.toNat - p1 =
                                                (eq3.toNat - p1 - 1) + 1 := by omega
                                            rw [hsub1, poolStarts_step_iff hp1]
                                            have hs1' :
                                                (((scr_pool[p1]?.getD 0#32) >>> 16#32) &&&
                                                  0x7FFF#32).toNat = s1 := by simp [hh1, hs1]
                                            rw [hs1'] at hq0 ⊢
                                            rcases hq0 with rfl | ⟨hle1, hq_t⟩
                                            · exact Or.inl rfl
                                            · exact Or.inr ⟨hle1, by
                                                rw [poolStarts_eq_of_ge (scr := scr_pool)
                                                  (eq_end := eq3.toNat) (p := p1 + 1 + s1)
                                                  (f0 := eq3.toNat - (p1 + 1 + s1))
                                                  (f1 := eq3.toNat - p1 - 1) (Nat.le_refl _)
                                                  (by omega)] at ih1
                                                exact ih1 f' q hq_t⟩
                                      exact hstep_fuel hrest _ q hr
                                  have hq_pu_or : ∀ q ∈ poolStarts scr_pool eq3.toNat 0 eq3.toNat,
                                      q < pu.toNat + 1 + st → q < pu.toNat ∨ q = pu.toNat := by
                                    intro q hq hqlt
                                    by_cases hlt : q < pu.toNat
                                    · exact Or.inl hlt
                                    · have hq1 := hstarts_pu q hq (by omega)
                                      have hsub : eq3.toNat - pu.toNat =
                                          (eq3.toNat - pu.toNat - 1) + 1 := by omega
                                      rw [hsub, poolStarts_step_iff hpu_lt] at hq1
                                      have hst' :
                                          (((scr_pool[pu.toNat]?.getD 0#32) >>> 16#32) &&&
                                            0x7FFF#32).toNat = st := by simp [hhdr, hst]
                                      rw [hst'] at hq1
                                      rcases hq1 with rfl | ⟨hle, _⟩
                                      · exact Or.inr rfl
                                      · omega
                                  c0_hstraight
                                  have hhdr_eq : scr_pool[pu.toNat]'hpu_scr = hdr := by
                                    have := List.getElem?_eq_getElem hpu_scr
                                    rw [hhdr] at this; exact Option.some.inj this.symm
                                  have hst_c0 :
                                      (BitVec.setWidth 64
                                        (hdr >>> OfNat.ofNat 16 &&&
                                              (32767 : BitVec 32))).toNat =
                                      st := by rw [bv_zext32_toNat]; exact hst.symm
                                  have hst_nat :
                                      (hdr.toNat / 2 ^ OfNat.ofNat 16 &&& 32767 % 2 ^ 32) = st := by
                                    have := hst_c0
                                    rwa [bv_zext32_toNat, BitVec.toNat_and,
                                      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
                                  have hst_nat' :
                                      (hdr >>> OfNat.ofNat 16 &&& (32767 : BitVec 32)).toNat =
                                      st := by
                                    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight,
                                      Nat.shiftRight_eq_div_pow]
                                    exact hst_nat
                                  have hcl_c0 :
                                      (BitVec.setWidth 64 (hdr &&& (65535 : BitVec 32))).toNat =
                                      cl := by rw [bv_zext32_toNat]; exact hcl.symm
                                  have hcl_nat : (hdr.toNat &&& 65535 % 2 ^ 32) = cl := by
                                    have := hcl_c0
                                    rwa [bv_zext32_toNat, BitVec.toNat_and] at this
                                  c0_hsplit
                                  · exfalso; rw [hhdr_eq] at hc
                                    have := hst_nat; have := hst_nat'; bv_omega
                                  · let Jpu_step : Mem 64 → Prop := fun m6' =>
                                      ∃ par_n : List (BitVec 32),
                                        par_n.length = 2 * c.max_vars ∧
                                        (∀ i < s4.core.cur_vars, (par_n[i]?.getD 0#32).toNat ≤ i) ∧
                                        UfPoolMerged par_n scr_pool s4.core.cur_vars eq3.toNat
                                          (pu.toNat + 1 + st) ∧
                                        (array (t := i32) c.pScratchBuf scr_pool ⋆
                                         array (t := i32) c.pWorkStk1 par_n ⋆
                                         array (t := i32) c.pWorkStk2
                                                    s4.scratch.work_stk2 ⋆
                                         array (t := i32) c.pTarjanReach vc ⋆
                                         array (t := i32) c.pWsort cnt ⋆
                                         (FullGaussRest c s4 ⋆ R)) m6'
                                    refine wp_join0 Jpu_step ?_ ?_
                                    · rintro _ m6' ⟨par_n, hlpn, hord_n, hmrg_n, hm6'⟩
                                      c0_hstraight
                                      have hpu_next :
                                          (pu + (1 : BitVec 64) +
                                            BitVec.setWidth 64
                                              ((scr_pool[pu.toNat]'hpu_scr) >>> OfNat.ofNat 16
                                                &&& (32767 : BitVec 32))).toNat =
                                          pu.toNat + 1 + st := by
                                        rw [hhdr_eq]; have := hst_nat'; bv_omega
                                      refine hJu_ih _ m6' (by dsimp only; rw [hpu_next]; omega)
                                        ⟨par_n, by rw [hpu_next]; omega, hlpn, hord_n,
                                         by rw [hpu_next]; exact hrest,
                                         by rw [hpu_next]; exact hpu_next_starts,
                                         by rw [hpu_next]; exact hmrg_n, hm6'⟩
                                    · intro _ hJpu_step
                                      c0_hsplit
                                      · c0_hsplit
                                        · have hcl_pos : 0 < cl := by
                                            rw [hhdr_eq] at *; have := hcl_nat; bv_omega
                                          have hcl_le : cl ≤ st := by
                                            rw [hhdr_eq] at hc; have := hcl_nat
                                            have := hst_nat; bv_omega
                                          rcases hbody with rfl | ⟨_, _, _, hvars_lt, _⟩
                                          · omega
                                          · have hp1_nat : (pu + 1#64).toNat = pu.toNat + 1 := by
                                              bv_omega
                                            have hp1_lt : (pu + 1#64).toNat < scr_pool.length := by
                                              rw [hp1_nat]; omega
                                            let v0 := scr_pool[(pu + 1#64).toNat]'hp1_lt
                                            have hv0_lt : v0.toNat < s4.core.cur_vars := by
                                              have h0m := hvars_lt _ (List.mem_map.mpr
                                                ⟨0, List.mem_range.mpr hcl_pos, rfl⟩)
                                              dsimp only [v0]
                                              rwa [Nat.add_zero, List.getElem?_eq_getElem
                                                (by rw [← hp1_nat]; exact hp1_lt), Option.getD_some,
                                                list_getElem_congr hp1_nat.symm _ _] at h0m
                                            c0_hstraight
                                            refine wp_join0 Jpu_step (fun _ m h => hJpu_step m h) ?_
                                            intro _ hJpu1
                                            c0_hsplit
                                            · have hcv64 :
                                                  (BitVec.ofNat 64 s4.core.cur_vars).toNat =
                                                  s4.core.cur_vars := by
                                                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                                              c0_hstraight
                                              apply wp_call_of_spec
                                              dsimp only [vals, Arg.val]
                                              refine hUfFind _ _ _ _
                                                ⟨par_p,
                                                  array (t := i32) c.pScratchBuf scr_pool ⋆
                                                  array (t := i32) c.pWorkStk2
                                                    s4.scratch.work_stk2 ⋆
                                                  array (t := i32) c.pTarjanReach vc ⋆
                                                  array (t := i32) c.pWsort cnt ⋆
                                                  (FullGaussRest c s4 ⋆ R),
                                                  by rw [hcv64, hlpp]; omega, by rw [hlpp]; omega,
                                                  by rw [hcv64]; exact hv0_lt,
                                                  by rw [hcv64]; exact hord_p, by ecancel,
                                                  fun r0 par_0 m60 hlp0 hr0_eq hr0_lt hord_0 hrt_0
                                                    _ _ hm60 => ?_⟩
                                              dsimp only
                                              rw [hcv64] at hr0_eq hr0_lt hord_0 hrt_0
                                              have hmrg_0 : UfPoolMerged par_0 scr_pool
                                                  s4.core.cur_vars eq3.toNat pu.toNat :=
                                                ufPoolMerged_of_same_root hmrg_p hpool4 hrt_0
                                              have hr0_v0 : r0.toNat =
                                                  ufRoot par_0 v0.toNat s4.core.cur_vars := by
                                                rw [hr0_eq, hrt_0 v0.toNat hv0_lt]; rfl
                                              -- Inner loop: k = 1 .. cl
                                              let Jk : Tup Val [i32, i64] → Mem 64 → Prop :=
                                                fun (r0k, k, ()) m6k =>
                                                  ∃ par_k : List (BitVec 32),
                                                    1 ≤ k.toNat ∧ k.toNat ≤ cl ∧
                                                    par_k.length = 2 * c.max_vars ∧
                                                    (∀ i < s4.core.cur_vars,
                                                      (par_k[i]?.getD 0#32).toNat ≤ i) ∧
                                                    r0k.toNat < s4.core.cur_vars ∧
                                                    r0k.toNat =
                                                      ufRoot par_k v0.toNat s4.core.cur_vars ∧
                                                    UfPoolMerged par_k scr_pool s4.core.cur_vars
                                                      eq3.toNat pu.toNat ∧
                                                    (∀ j < k.toNat,
                                                      ufRoot par_k
                                                        (scr_pool[pu.toNat + 1 + j]?.getD
                                                          0#32).toNat
                                                        s4.core.cur_vars = r0k.toNat) ∧
                                                    (array (t := i32) c.pScratchBuf scr_pool ⋆
                                                     array (t := i32) c.pWorkStk1 par_k ⋆
                                                     array (t := i32) c.pWorkStk2
                                                       s4.scratch.work_stk2 ⋆
                                                     array (t := i32) c.pTarjanReach vc ⋆
                                                     array (t := i32) c.pWsort cnt ⋆
                                                     (FullGaussRest c s4 ⋆ R)) m6k
                                              refine wp_loop_inv Jk
                                                (fun (_, k, ()) _ => cl - k.toNat)
                                                (fun _ h => by
                                                  c0_hstraight
                                                  refine h (r0, 1#64, ()) m60
                                                    ⟨par_0, Nat.le_refl _, hcl_pos,
                                                     by rw [hlp0, hlpp], hord_0, hr0_lt, hr0_v0,
                                                     hmrg_0, ?_, by ecancel⟩
                                                  intro j hj
                                                  have hj0 : j = 0 := by
                                                    rw [show (1#64).toNat = 1 from rfl] at hj; omega
                                                  subst hj0
                                                  rw [Nat.add_zero,
                                                    List.getElem?_eq_getElem
                                                      (by rw [← hp1_nat]; exact hp1_lt),
                                                    Option.getD_some,
                                                    list_getElem_congr hp1_nat.symm _ _]
                                                  exact hr0_v0.symm) ?_
                                              rintro _ ⟨r0k, k, _⟩ m6k
                                                ⟨par_k, hk_ge1, hk_le, hlpk, hord_k, hr0k_lt,
                                                 hr0k_v0, hmrg_k, hj_eq, hm6k⟩ hJk_ih
                                              c0_hsplit
                                              · have hk_lt : k.toNat < cl := by
                                                  rw [hhdr_eq] at hc; have := hcl_nat; bv_omega
                                                have hpk_nat :
                                                    (pu + (1 : BitVec 64) + k).toNat =
                                                      pu.toNat + 1 + k.toNat := by bv_omega
                                                have hpk_lt :
                                                    (pu + (1 : BitVec 64) + k).toNat <
                                                      scr_pool.length := by rw [hpk_nat]; omega
                                                let vk :=
                                                  scr_pool[(pu + (1 : BitVec 64) + k).toNat]'hpk_lt
                                                have hvk_lt : vk.toNat < s4.core.cur_vars := by
                                                  have hkm := hvars_lt _ (List.mem_map.mpr
                                                    ⟨k.toNat, List.mem_range.mpr hk_lt, rfl⟩)
                                                  dsimp only [vk]
                                                  rwa [List.getElem?_eq_getElem
                                                    (by rw [← hpk_nat]; exact hpk_lt),
                                                    Option.getD_some,
                                                    list_getElem_congr hpk_nat.symm _ _] at hkm
                                                c0_hstraight
                                                let Jk_step : Tup Val [i32] → Mem 64 → Prop :=
                                                  fun (r0n, ()) m6n =>
                                                    ∃ par_n : List (BitVec 32),
                                                      par_n.length = 2 * c.max_vars ∧
                                                      (∀ i < s4.core.cur_vars,
                                                        (par_n[i]?.getD 0#32).toNat ≤ i) ∧
                                                      r0n.toNat < s4.core.cur_vars ∧
                                                      r0n.toNat =
                                                        ufRoot par_n v0.toNat s4.core.cur_vars ∧
                                                      UfPoolMerged par_n scr_pool s4.core.cur_vars
                                                        eq3.toNat pu.toNat ∧
                                                      (∀ j < k.toNat + 1,
                                                        ufRoot par_n
                                                          (scr_pool[pu.toNat + 1 + j]?.getD
                                                            0#32).toNat
                                                          s4.core.cur_vars = r0n.toNat) ∧
                                                      (array (t := i32) c.pScratchBuf scr_pool ⋆
                                                       array (t := i32) c.pWorkStk1 par_n ⋆
                                                       array (t := i32) c.pWorkStk2
                                                         s4.scratch.work_stk2 ⋆
                                                       array (t := i32) c.pTarjanReach vc ⋆
                                                       array (t := i32) c.pWsort cnt ⋆
                                                       (FullGaussRest c s4 ⋆ R)) m6n
                                                refine wp_join_group Jk_step ?_ ?_
                                                · rintro _ ⟨r0n, _⟩ m6n
                                                    ⟨par_n, hlpn, hord_n, hr0n_lt, hr0n_v0,
                                                     hmrg_n, hjn, hm6n⟩
                                                  c0_hstraight
                                                  have hk1 : (k + 1#64).toNat = k.toNat + 1 := by
                                                    bv_omega
                                                  exact hJk_ih (r0n, k + 1#64, ()) m6n
                                                    (by dsimp only; omega)
                                                    ⟨par_n, by omega, by omega, hlpn, hord_n,
                                                     hr0n_lt, hr0n_v0, hmrg_n,
                                                     by rw [hk1]; exact hjn, hm6n⟩
                                                · intro _ hJk_step
                                                  c0_hsplit
                                                  · c0_hstraight
                                                    apply wp_call_of_spec
                                                    dsimp only [vals, Arg.val]
                                                    refine hUfFind _ _ _ _
                                                      ⟨par_k,
                                                        array (t := i32) c.pScratchBuf scr_pool ⋆
                                                        array (t := i32) c.pWorkStk2
                                                          s4.scratch.work_stk2 ⋆
                                                        array (t := i32) c.pTarjanReach vc ⋆
                                                        array (t := i32) c.pWsort cnt ⋆
                                                        (FullGaussRest c s4 ⋆ R),
                                                        by rw [hcv64, hlpk]; omega,
                                                        by rw [hlpk]; omega,
                                                        by rw [hcv64]; exact hvk_lt,
                                                        by rw [hcv64]; exact hord_k, by ecancel,
                                                        fun rk par_k1 m6k1 hlpk1 hrk_eq hrk_lt
                                                          hord_k1 hrt_k1 _ _ hm6k1 => ?_⟩
                                                    dsimp only
                                                    rw [hcv64] at hrk_eq hrk_lt hord_k1 hrt_k1
                                                    have hmrg_k1 : UfPoolMerged par_k1 scr_pool
                                                        s4.core.cur_vars eq3.toNat pu.toNat :=
                                                      ufPoolMerged_of_same_root hmrg_k hpool4 hrt_k1
                                                    have hr0k_v0' : r0k.toNat =
                                                        ufRoot par_k1 v0.toNat
                                                          s4.core.cur_vars := by
                                                      rw [hrt_k1 v0.toNat hv0_lt, hr0k_v0]
                                                    have hrk_vk : rk.toNat =
                                                        ufRoot par_k1 vk.toNat
                                                          s4.core.cur_vars := by
                                                      rw [hrt_k1 vk.toNat hvk_lt, hrk_eq]
                                                    have hjk1 : ∀ j < k.toNat,
                                                        ufRoot par_k1
                                                          (scr_pool[pu.toNat + 1 + j]?.getD
                                                            0#32).toNat
                                                          s4.core.cur_vars = r0k.toNat := by
                                                      intro j hj
                                                      have hjl := hvars_lt _ (List.mem_map.mpr
                                                        ⟨j, List.mem_range.mpr (by omega), rfl⟩)
                                                      rw [hrt_k1 _ hjl, hj_eq j hj]
                                                    have hvk_scr :
                                                        (scr_pool[pu.toNat + 1 + k.toNat]?.getD
                                                          0#32).toNat = vk.toNat := by
                                                      dsimp only [vk]
                                                      rw [List.getElem?_eq_getElem
                                                        (by rw [← hpk_nat]; exact hpk_lt),
                                                        Option.getD_some,
                                                        list_getElem_congr hpk_nat.symm _ _]
                                                    refine wp_join_group Jk_step
                                                      (fun _ xs m h => hJk_step xs m h) ?_
                                                    intro _ hJk1
                                                    c0_hsplit
                                                    · c0_hsplit
                                                      · c0_hsplit
                                                        · have hne_rk : rk ≠ r0k := by bv_omega
                                                          have hrk_rt :
                                                              (par_k1[rk.toNat]?.getD 0#32).toNat =
                                                                rk.toNat := by
                                                            have := ufRoot_is_root hord_k1 hvk_lt
                                                              hvk_lt
                                                            rwa [← hrk_vk] at this
                                                          have hr0_rt :
                                                              (par_k1[r0k.toNat]?.getD 0#32).toNat =
                                                                r0k.toNat := by
                                                            have := ufRoot_is_root hord_k1 hv0_lt
                                                              hv0_lt
                                                            rwa [← hr0k_v0'] at this
                                                          refine wp_join_group Jk_step
                                                            (fun _ xs m h => hJk1 xs m h) ?_
                                                          intro _ hJk2
                                                          c0_hsplit
                                                          · -- rk < r0k: par[r0k] = rk; r0 = rk
                                                            have hlt_rk : rk.toNat < r0k.toNat := by
                                                              bv_omega
                                                            have hr0_len :
                                                                (r0k.setWidth 64).toNat <
                                                                  par_k1.length := by
                                                              rw [bv_zext32_toNat]; omega
                                                            c0_hstraight
                                                            have hsr := ufRoot_set_root hord_k1
                                                              (by omega) hlt_rk hr0k_lt hrk_rt
                                                                hr0_rt
                                                            have hmrg_u1 := ufPoolMerged_of_union
                                                              hmrg_k1 hpool4 hord_k1 (by omega)
                                                              hlt_rk hr0k_lt hrk_rt hr0_rt
                                                            refine hJk2 (rk, ()) _
                                                              ⟨par_k1.set r0k.toNat rk,
                                                               by simp [hlpk1, hlpk], hsr.1,
                                                               hrk_lt, ?_, hmrg_u1, ?_, ?_⟩
                                                            · rw [hsr.2 v0.toNat hv0_lt _ hv0_lt,
                                                                ← hr0k_v0', ite_eq_left rfl]
                                                            · intro j hj
                                                              by_cases hjk : j = k.toNat
                                                              · subst hjk
                                                                rw [hvk_scr,
                                                                  hsr.2 vk.toNat hvk_lt _ hvk_lt,
                                                                  ← hrk_vk,
                                                                  ite_eq_right (by omega)]
                                                              · have hjl := hvars_lt _
                                                                  (List.mem_map.mpr ⟨j,
                                                                    List.mem_range.mpr (by omega),
                                                                    rfl⟩)
                                                                rw [hsr.2 _ hjl _ hjl,
                                                                  hjk1 j (by omega),
                                                                  ite_eq_left rfl]
                                                            · rw [bv_zext32_toNat] at hm
                                                              ecancel
                                                          · -- r0k < rk: par[rk] = r0k
                                                            have hlt_r0 : r0k.toNat < rk.toNat := by
                                                              have : rk.toNat ≠ r0k.toNat :=
                                                                fun h => hne_rk
                                                                  (BitVec.eq_of_toNat_eq h)
                                                              bv_omega
                                                            have hrk_len :
                                                                (rk.setWidth 64).toNat <
                                                                  par_k1.length := by
                                                              rw [bv_zext32_toNat]; omega
                                                            c0_hstraight
                                                            have hsr := ufRoot_set_root hord_k1
                                                              (by omega) hlt_r0 hrk_lt hr0_rt hrk_rt
                                                            have hmrg_u1 := ufPoolMerged_of_union
                                                              hmrg_k1 hpool4 hord_k1 (by omega)
                                                              hlt_r0 hrk_lt hr0_rt hrk_rt
                                                            refine hJk2 (r0k, ()) _
                                                              ⟨par_k1.set rk.toNat r0k,
                                                               by simp [hlpk1, hlpk], hsr.1,
                                                               hr0k_lt, ?_, hmrg_u1, ?_, ?_⟩
                                                            · rw [hsr.2 v0.toNat hv0_lt _ hv0_lt,
                                                                ← hr0k_v0',
                                                                ite_eq_right (by omega)]
                                                            · intro j hj
                                                              by_cases hjk : j = k.toNat
                                                              · subst hjk
                                                                rw [hvk_scr,
                                                                  hsr.2 vk.toNat hvk_lt _ hvk_lt,
                                                                  ← hrk_vk, ite_eq_left rfl]
                                                              · have hjl := hvars_lt _
                                                                  (List.mem_map.mpr ⟨j,
                                                                    List.mem_range.mpr (by omega),
                                                                    rfl⟩)
                                                                rw [hsr.2 _ hjl _ hjl,
                                                                  hjk1 j (by omega),
                                                                  ite_eq_right (by omega)]
                                                            · rw [bv_zext32_toNat] at hm
                                                              ecancel
                                                        · exfalso; bv_omega
                                                      · exfalso; bv_omega
                                                    · -- rk == r0k: already merged!
                                                      have hrk_eq_r0 : rk.toNat = r0k.toNat := by
                                                        bv_omega
                                                      refine hJk1 (r0k, ()) m6k1
                                                        ⟨par_k1, by rw [hlpk1, hlpk], hord_k1,
                                                         hr0k_lt, hr0k_v0', hmrg_k1, ?_, by ecancel⟩
                                                      intro j hj
                                                      by_cases hjk : j = k.toNat
                                                      · subst hjk
                                                        rw [hvk_scr, ← hrk_vk, hrk_eq_r0]
                                                      · exact hjk1 j (by omega)
                                                  · exfalso
                                                    apply hc
                                                    rw [list_getElem_congr
                                                        (show _ = (pu + (1 : BitVec 64) + k).toNat
                                                          by bv_omega) _ hpk_lt,
                                                      Nat.mod_eq_of_lt (by omega)]
                                                    exact hvk_lt
                                              · -- End of inner k loop (k = cl): pu is merged!
                                                have hk_eq : k.toNat = cl := by
                                                  rw [hhdr_eq] at hc; have := hcl_nat; bv_omega
                                                refine hJpu1 m6k ⟨par_k, hlpk, hord_k, ?_, hm6k⟩
                                                intro q hq hqlt
                                                dsimp only
                                                intro hqpos j hj
                                                rcases hq_pu_or q hq hqlt with hlt_q | rfl
                                                · exact hmrg_k q hq hlt_q hqpos j hj
                                                · have hcl' :
                                                      ((scr_pool[pu.toNat]?.getD 0#32) &&&
                                                        0xFFFF#32).toNat = cl := by
                                                    rw [hhdr, Option.getD_some, ← hcl]
                                                  rw [hcl'] at hj
                                                  rw [hj_eq j (by omega),
                                                    hj_eq 0 (by omega)]
                                            · exfalso
                                              apply hc
                                              rw [list_getElem_congr
                                                  (show _ = (pu + 1#64).toNat by bv_omega) _
                                                  hp1_lt,
                                                Nat.mod_eq_of_lt (by omega)]
                                              exact hv0_lt
                                        · exfalso; rcases hbody with rfl | ⟨_, hle, _, _, _⟩
                                          · rw [hhdr_eq] at *; have := hcl_nat; bv_omega
                                          · rw [hhdr_eq] at hc; have := hcl_nat
                                            have := hst_nat; bv_omega
                                      · -- cl == 0: vacuous for block pu!
                                        have hcl0 : cl = 0 := by
                                          rw [hhdr_eq] at hc; have := hcl_nat; bv_omega
                                        refine hJpu_step m6 ⟨par_p, hlpp, hord_p, ?_, hm6⟩
                                        intro q hq hqlt
                                        dsimp only
                                        intro hqpos j hj
                                        rcases hq_pu_or q hq hqlt with hlt_q | rfl
                                        · exact hmrg_p q hq hlt_q hqpos j hj
                                        · have hcl' :
                                              ((scr_pool[pu.toNat]?.getD 0#32) &&&
                                                0xFFFF#32).toNat = 0 := by
                                            rw [hhdr, Option.getD_some, ← hcl, hcl0]
                                          rw [hcl'] at hqpos
                                          omega
                              · have hpu_eq : pu.toNat = eq3.toNat := by bv_omega
                                exact hJunion_exit (pu, ()) m6
                                  ⟨par_p, hlpp, hord_p, by simpa [hpu_eq] using hmrg_p, hm6⟩
                      · exact hJpost m3 ⟨s3, hsp3, hlvl3.trans (hlvl1.trans hlvl0),
                          by rw [hfuel3, hfuel1]; exact Nat.le_refl _, hm3⟩
            · -- ht_cap computation
              intro _ hJht
              c0_hsplit
              · have hcap_ge : 448 ≤ c.scratch_cap := by bv_omega
                let Jht_l : Tup Val [i64] → Mem 64 → Prop := fun (hc_v, ()) mh =>
                  mh = m0 ∧ 64 ≤ hc_v.toNat ∧ hc_v.toNat ≤ 4096 ∧
                  (hc_v = 64#64 ∨ hc_v = 128#64 ∨ hc_v = 256#64 ∨ hc_v = 512#64 ∨
                    hc_v = 1024#64 ∨ hc_v = 2048#64 ∨ hc_v = 4096#64) ∧
                  7 * hc_v.toNat ≤ c.scratch_cap
                refine wp_loop_inv Jht_l (fun (hc_v, ()) _ => 4096 - hc_v.toNat)
                  (fun _ h => by
                    c0_hstraight
                    exact h (64#64, ()) m0
                      ⟨rfl, by decide, by decide, Or.inl rfl, by simpa using hcap_ge⟩) ?_
                rintro _ ⟨hc_v, _⟩ mh ⟨rfl, hge64, hle4096, hpow2, h7le⟩ hJht_ih
                c0_hsplit
                · c0_hsplit
                  · have hlt4096 : hc_v.toNat < 4096 := by bv_omega
                    have hlt2048 : hc_v.toNat ≤ 2048 := by
                      rcases hpow2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                        first | decide | (simp at hlt4096)
                    have hsh1 : (hc_v <<< 1#64).toNat = 2 * hc_v.toNat := by
                      change (hc_v <<< (1 : Nat)).toNat = 2 * hc_v.toNat
                      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
                        Nat.mod_eq_of_lt (by omega)]
                      exact Nat.mul_comm _ _
                    have hpow2' : (hc_v <<< 1#64) = 64#64 ∨ (hc_v <<< 1#64) = 128#64 ∨
                        (hc_v <<< 1#64) = 256#64 ∨ (hc_v <<< 1#64) = 512#64 ∨
                        (hc_v <<< 1#64) = 1024#64 ∨ (hc_v <<< 1#64) = 2048#64 ∨
                        (hc_v <<< 1#64) = 4096#64 := by
                      rcases hpow2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
                      · exact Or.inr (Or.inl rfl)
                      · exact Or.inr (Or.inr (Or.inl rfl))
                      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
                      · simp at hlt4096
                    have h7_2 : 7 * (2 * hc_v.toNat) ≤ c.scratch_cap := by
                      rename_i hle_bv
                      change (hc_v.toNat * 2 ^ OfNat.ofNat 1 % 2 ^ 64 * (7#64).toNat) % 2 ^ 64 ≤
                        c.scratch_cap % 2 ^ 64 at hle_bv
                      have hshift : hc_v.toNat * 2 ^ OfNat.ofNat 1 % 2 ^ 64 = 2 * hc_v.toNat := by
                        have hpow : (2 : Nat) ^ OfNat.ofNat 1 = 2 := rfl
                        rw [hpow, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
                      rw [hshift, show (7#64).toNat = 7 from rfl, Nat.mod_eq_of_lt (by omega),
                        Nat.mod_eq_of_lt (by omega), Nat.mul_comm] at hle_bv
                      exact hle_bv
                    c0_hstraight
                    exact hJht_ih (hc_v <<< 1#64, ()) mh (by dsimp only; rw [hsh1]; omega)
                      ⟨rfl, by rw [hsh1]; omega, by rw [hsh1]; omega, hpow2',
                       by rw [hsh1]; exact h7_2⟩
                  · c0_hstraight; exact hJht (hc_v, ()) mh ⟨rfl, fun _ => ⟨h7le, by omega⟩⟩
                · c0_hstraight; exact hJht (hc_v, ()) mh ⟨rfl, fun _ => ⟨h7le, by omega⟩⟩
              · c0_hstraight; exact hJht (0#64, ()) m0 ⟨rfl, fun h => absurd rfl h⟩

/-! ## 3. Closed `19`-Row Spec Table, Parametric `TableImpl`, & `ModuleOk` -/

/-- Exact `19`-row specification table matching `m8XorGaussFns` (`noExit = true`). -/
@[expose] def m8XorGaussSpecTable : List SpecEntry :=
  [ ⟨"full_xor_sort5", [i64, i32, i32], [.bool], fullXorSort5Spec, true⟩
  , ⟨"full_xor_parity_mask", [i32, .bool], [i32], fullXorParityMaskSpec, true⟩
  , ⟨"full_xor_ht_insert", [i64, i64, i64, i64, i32], [i64], fullXorHtInsertSpec, true⟩
  , ⟨"full_xor_collect_arena", [i64, i64], [i64], fullXorCollectArenaSpec, true⟩
  , ⟨"full_xor_collect_bins", [i64, i64], [i64], fullXorCollectBinsSpec, true⟩
  , ⟨"full_xor_compact_pool", [i64, i64], [i64], fullXorCompactPoolSpec, true⟩
  , ⟨"full_xor_merge_two", [i64, i64, i64, i64], [i64], fullXorMergeTwoSpec, true⟩
  , ⟨"full_xor_chain_merge", [i64, i64], [i64], fullXorChainMergeSpec, true⟩
  , ⟨"full_xor_uf_find", [i64, i32, i64], [i32], fullXorUfFindSpec, true⟩
  , ⟨"full_xor_read_u64", [i64, i64], [i64], fullXorReadU64Spec, true⟩
  , ⟨"full_xor_write_u64", [i64, i64, i64], [], fullXorWriteU64Spec, true⟩
  , ⟨"full_xor_swap_rows", [i64, i64, i64, i64, i64], [], fullXorSwapRowsSpec, true⟩
  , ⟨"full_xor_xor_rows", [i64, i64, i64, i64, i64], [], fullXorXorRowsSpec, true⟩
  , ⟨"full_xor_set_bit", [i64, i64, i64], [], fullXorSetBitSpec, true⟩
  , ⟨"full_xor_build_mat", [i64, i64, i64, i64], [i64], fullXorBuildMatSpec, true⟩
  , ⟨"full_xor_rref", [i64, i64, i64, i64], [], fullXorRrefSpec, true⟩
  , ⟨"full_xor_emit_mat", [i64, i64, i64, i64], [i64], fullXorEmitMatSpec, true⟩
  , ⟨"full_xor_emit_pool_small", [i64, i64], [i64], fullXorEmitPoolSmallSpec, true⟩
  , ⟨"full_xor_gauss", [i64], [i64], fullXorGaussSpec, true⟩ ]

/-- The `7` Kissat extern specification rows consumed by `m8XorGaussModule`. -/
@[expose] def m8XorGaussExternRows : List SpecEntry :=
  [ ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  , ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], fullHasTernarySpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  , ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩ ]

/-- Standalone specification environment for `m8XorGaussModule` (`19` fns + `7` externs). -/
def m8XorGaussEnv : Env := Env.ofTable (m8XorGaussSpecTable ++ m8XorGaussExternRows)

theorem m8XorGaussSpecTable_len : m8XorGaussSpecTable.length = 19 := rfl

theorem m8XorGaussSpecTable_sigs :
    (m8XorGaussSpecTable ++ m8XorGaussExternRows).map (fun e => (e.name, e.as, e.rs)) =
      m8XorGaussModule.sigs := by
  unfold m8XorGaussSpecTable m8XorGaussExternRows m8XorGaussModule m8XorGaussFns m8XorGauss_fns
    m8XorGaussExterns Module.sigs Fn.sig Extern.sig
  t_kernel_rfl

theorem m8XorGaussSpecTable_nodup : (m8XorGaussSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m8XorGaussFullTable_nodup :
    ((m8XorGaussSpecTable ++ m8XorGaussExternRows).map SpecEntry.name).Nodup := by
  decide

theorem m8XorGaussSpecTable_noExit : ∀ e ∈ m8XorGaussSpecTable, e.noExit = true := by
  intro e he
  exact List.all_eq_true.mp (by decide : m8XorGaussSpecTable.all (·.noExit) = true) e he

theorem m8XorGaussEnv_noExit :
    ∀ f as bs xs m Q X X',
      m8XorGaussEnv f as bs xs m Q X → m8XorGaussEnv f as bs xs m Q X' :=
  Env.ofTable_noExit fun e he =>
    List.all_eq_true.mp
      (by decide : (m8XorGaussSpecTable ++ m8XorGaussExternRows).all (·.noExit) = true) e he

/-- Parametric `19/19` `TableImpl` builder for any environment `Γ` exposing `m8XorGaussSpecTable`
and the `7` Kissat externs (reused directly by `FullM8XorAssemblyProof`). -/
theorem m8XorGauss_tableImpl_of (Γ : Env)
    (hRows : ∀ e ∈ m8XorGaussSpecTable, ∀ xs m Q X, e.eff xs m Q X →
      Γ e.name e.as e.rs xs m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hHasBin : ∀ a m Q X, fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (hHasTern : ∀ a m Q X, fullHasTernarySpec a m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hAddClause : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    TableImpl Γ m8XorGaussFns m8XorGaussSpecTable := by
  have r0 := hRows _ (List.mem_of_getElem? (i := 0) rfl)
  have r1 := hRows _ (List.mem_of_getElem? (i := 1) rfl)
  have r2 := hRows _ (List.mem_of_getElem? (i := 2) rfl)
  have r3 := hRows _ (List.mem_of_getElem? (i := 3) rfl)
  have r4 := hRows _ (List.mem_of_getElem? (i := 4) rfl)
  have r5 := hRows _ (List.mem_of_getElem? (i := 5) rfl)
  have r6 := hRows _ (List.mem_of_getElem? (i := 6) rfl)
  have r7 := hRows _ (List.mem_of_getElem? (i := 7) rfl)
  have r8 := hRows _ (List.mem_of_getElem? (i := 8) rfl)
  have r9 := hRows _ (List.mem_of_getElem? (i := 9) rfl)
  have r10 := hRows _ (List.mem_of_getElem? (i := 10) rfl)
  have r11 := hRows _ (List.mem_of_getElem? (i := 11) rfl)
  have r12 := hRows _ (List.mem_of_getElem? (i := 12) rfl)
  have r13 := hRows _ (List.mem_of_getElem? (i := 13) rfl)
  have r14 := hRows _ (List.mem_of_getElem? (i := 14) rfl)
  have r15 := hRows _ (List.mem_of_getElem? (i := 15) rfl)
  have r16 := hRows _ (List.mem_of_getElem? (i := 16) rfl)
  have r17 := hRows _ (List.mem_of_getElem? (i := 17) rfl)
  exact
    ⟨ SpecEntry.Impl.of (full_xor_sort5_wp Γ)
    , SpecEntry.Impl.of (full_xor_parity_mask_wp Γ)
    , SpecEntry.Impl.of (full_xor_ht_insert_wp Γ)
    , SpecEntry.Impl.of (full_xor_collect_arena_wp Γ hArenaNext r0 r1 r2)
    , SpecEntry.Impl.of (full_xor_collect_bins_wp Γ hHasBin)
    , SpecEntry.Impl.of (full_xor_compact_pool_wp Γ)
    , SpecEntry.Impl.of (full_xor_merge_two_wp Γ)
    , SpecEntry.Impl.of (full_xor_chain_merge_wp Γ r6 r5)
    , SpecEntry.Impl.of (full_xor_uf_find_wp Γ)
    , SpecEntry.Impl.of (full_xor_read_u64_wp Γ)
    , SpecEntry.Impl.of (full_xor_write_u64_wp Γ)
    , SpecEntry.Impl.of (full_xor_swap_rows_wp Γ)
    , SpecEntry.Impl.of (full_xor_xor_rows_wp Γ r9 r10)
    , SpecEntry.Impl.of (full_xor_set_bit_wp Γ r9 r10)
    , SpecEntry.Impl.of (full_xor_build_mat_wp Γ r13)
    , SpecEntry.Impl.of (full_xor_rref_wp Γ r9 r11 r12)
    , SpecEntry.Impl.of (full_xor_emit_mat_wp Γ r9 hAddUnit hHasBin hAddBin hHasTern hAddClause)
    , SpecEntry.Impl.of (full_xor_emit_pool_small_wp Γ hAddUnit hHasBin hAddBin)
    , SpecEntry.Impl.of (full_xor_gauss_wp Γ r3 r4 r7 r17 r8 r14 r15 r16 hProp)
    , trivial ⟩

theorem m8XorGauss_tableImpl :
    TableImpl m8XorGaussEnv m8XorGaussFns m8XorGaussSpecTable := by
  have hmem : ∀ e ∈ m8XorGaussSpecTable ++ m8XorGaussExternRows,
      ∀ xs m Q X, e.eff xs m Q X → m8XorGaussEnv e.name e.as e.rs xs m Q X :=
    fun _ he _ _ _ _ hs => Env.ofTable_of_mem he m8XorGaussFullTable_nodup hs
  exact m8XorGauss_tableImpl_of m8XorGaussEnv
    (fun e he => hmem e (List.mem_append_left _ he))
    (hmem _ (List.mem_append_right _ (List.mem_of_getElem? (i := 0) rfl)))
    (hmem _ (List.mem_append_right _ (List.mem_of_getElem? (i := 1) rfl)))
    (hmem _ (List.mem_append_right _ (List.mem_of_getElem? (i := 2) rfl)))
    (hmem _ (List.mem_append_right _ (List.mem_of_getElem? (i := 3) rfl)))
    (hmem _ (List.mem_append_right _ (List.mem_of_getElem? (i := 4) rfl)))
    (hmem _ (List.mem_append_right _ (List.mem_of_getElem? (i := 5) rfl)))
    (hmem _ (List.mem_append_right _ (List.mem_of_getElem? (i := 6) rfl)))

private theorem ofTable_mem_names : ∀ {t : List SpecEntry} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost},
    Env.ofTable t f as bs xs m Q X → f ∈ t.map SpecEntry.name
  | [], _, _, _, _, _, _, _, h => False.elim h
  | e :: _, f, as, bs, xs, m, Q, X, h => by
    by_cases hnm : e.name = f
    · rw [← hnm]; exact List.mem_cons_self
    · rw [Env.ofTable_cons_ne hnm] at h
      exact List.mem_cons_of_mem _ (ofTable_mem_names h)

private theorem m8XorGauss_ofTable_ext_ne {f : Sym} (hf : f ∈ m8XorGaussFns.map Fn.name)
    {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable m8XorGaussExternRows f as bs xs m Q X) : False := by
  have hmem := ofTable_mem_names h
  have hdisj : ∀ x ∈ m8XorGaussFns.map Fn.name,
      x ∉ m8XorGaussExternRows.map SpecEntry.name := by decide
  exact hdisj f hf hmem

/-- Closed `19/19` `ModuleOk` for standalone `FullM8XorGauss.m8XorGaussModule`. -/
theorem m8XorGauss_moduleOk : ModuleOk m8XorGaussEnv m8XorGaussModule := by
  refine Module.moduleOk_of_checkAcyclic m8XorGauss_acyclic m8XorGaussFns_wf ?_
  have hnd : (m8XorGaussFns.map Fn.name).Nodup := by decide
  have hsound := Env.ofTable_sound hnd m8XorGauss_tableImpl
  intro f hf xs m Q X hs
  have hsp : Env.ofTable m8XorGaussSpecTable f.name f.as f.rs xs m Q X := by
    have hsplit : ∀ {t1 t2 : List SpecEntry} {nm as bs xs m Q X},
        Env.ofTable (t1 ++ t2) nm as bs xs m Q X →
        Env.ofTable t1 nm as bs xs m Q X ∨ Env.ofTable t2 nm as bs xs m Q X := by
      intro t1 t2 nm as bs xs m Q X
      induction t1 with
      | nil => intro h; exact Or.inr h
      | cons e es ih =>
        intro h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (Or.inl ⟨h1, h2⟩)
        · rcases ih h2 with hL | hR
          · exact Or.inl (Or.inr ⟨h1, hL⟩)
          · exact Or.inr hR
    rcases hsplit hs with hL | hR
    · exact hL
    · exact False.elim (m8XorGauss_ofTable_ext_ne (List.mem_map.mpr ⟨f, hf, rfl⟩) hR)
  exact hsound f hf xs m Q X hsp

end LeanQbe.T.Examples.Kissat.FullM8XorGauss
