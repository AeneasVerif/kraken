/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpDeduce0
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpDeduce1
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpCommon
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Header Framing, Exit Paths & Seed WP Helpers (`Proof.Deduce.WpDeduce2`)

Parametric `(Γ : Env)` WP helpers (`public section`, `0` legacy `Full*` imports, `0` `import all`,
`0` `@[expose]` on theorems/lemmas/sections, every declaration `<= 450` LOC) for
`full_deduce_1uip_m6_hdr`:
1. Structural core/witness/lower-lit/BitVec bridges over `WpDeduce0`/`WpDeduce1`.
2. `FullM6HdrMem` callee wrappers (`deduce_hdr_{clear,lit,otfs_bin,otfs_large,otfs_subsume}_wp`).
3. Clear-exit and seed-terminal helpers (`deduce_clear_ret0_wp`, `deduce_seed_unsat_or_ret0_wp`).
4. 1-UIP exit helper (`deduce_uip_exit_body_wp`) and seed WP (`deduce_seed_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Deduce
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics DeduceTactics

local elab "d_hsteps" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "d_hsteps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

/-! ## 1. Structural & Pure Helper Bridges -/

theorem ded_witnessCut_with_ana {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32)) (tc' tl' mcl' : Nat) :
    FullWitnessCutInv c F0 F_cur cut
      { k with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' } :=
  ⟨{ hw.toFullOtfsWitnessInv with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    hw.cut_le, hw.reason_inv_cut, hw.reason_lit_mem_cut⟩

theorem ded_otfsInvW_of_cleared_state {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s0 s_cur s' : FullState}
    (hlen' : FullState.LengthsOk c s')
    (hw' : FullWitnessCutInv c F0 F_cur cut s'.core)
    (hmrk0 : ∀ v < c.max_vars, s'.core.mrk[v]?.getD 0#8 = 0#8)
    (hlm0 : FullLitMarksClear c s0)
    (hlm_eq : s'.core.lit_mark = s0.core.lit_mark)
    (hnd' : FullArenaVarsNodup s')
    (hext0 : FullExtScratchOk c s0)
    (hextp : FullExtScratchPres s_cur s')
    (hext0_p : FullExtScratchPres s0 s_cur)
    (hcv' : s'.core.cur_vars = s0.core.cur_vars)
    (hrefs' : fullArenaClauseRefs s' = fullArenaClauseRefs s_cur)
    (hrefs0 : fullArenaClauseRefs s_cur = fullArenaClauseRefs s0)
    (hdm' : s'.core.dense_mode = 0#64) :
    FullOtfsInvW c F0 F_cur s' :=
  ded_otfsInvW_of_cutInv hlen' hw'
    (ded_litMarksClear_of_clear hlm0 hmrk0 hlm_eq) hnd'
    (ded_extScratchOk_of_pres hext0 ⟨hextp.1.trans hext0_p.1, hextp.2.trans hext0_p.2⟩
      hcv' (hrefs'.trans hrefs0))
    hdm'

theorem ded_curTrailIdxs_nil_of_clear {c : FullCfg} {k : FullCoreState} {lim : Nat}
    (hlim : lim ≤ k.trail_end) (hcv : k.cur_vars ≤ c.max_vars)
    (htr : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars)
    (hm0 : ∀ v < c.max_vars, k.mrk[v]?.getD 0#8 = 0#8) :
    fullCurTrailIdxs k k.mrk lim = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro idx hmem
  rw [fullCurTrailIdxs_mem_iff] at hmem
  have hlt := htr idx (Nat.lt_of_lt_of_le hmem.1 hlim)
  exact hmem.2.1 (hm0 _ (by omega))

theorem ded_fullLowerLits_set0 {tmp : List (BitVec 32)} {tl : Nat} (v : BitVec 32)
    (htl : 1 ≤ tl) (hlen : tl ≤ tmp.length) :
    fullLowerLits (tmp.set 0 v) tl = fullLowerLits tmp tl := by
  unfold fullLowerLits
  apply List.ext_getElem
  · simp [List.length_take, List.length_set]
  · intro i h1 h2
    have hlt_a : tl ≤ (tmp.set 0 v).length := by rw [List.length_set]; exact hlen
    simp only [List.length_map, List.length_drop, List.length_take, List.length_set,
      Nat.min_eq_left hlen] at h1
    have hi1 : i + 1 < tl := by omega
    have hget_a : ((tmp.set 0 v).take tl)[i + 1]? = tmp[i + 1]? := by
      rw [List.getElem?_take_of_lt hi1, List.getElem?_set_ne (by omega)]
    have hget_b : (tmp.take tl)[i + 1]? = tmp[i + 1]? := List.getElem?_take_of_lt hi1
    simp only [List.getElem_map, List.getElem_drop, Nat.add_comm 1 i]
    have ha := List.getElem?_eq_getElem (l := (tmp.set 0 v).take tl)
      (i := i + 1) (by rw [List.length_take, Nat.min_eq_left hlt_a]; omega)
    have hb := List.getElem?_eq_getElem (l := tmp.take tl)
      (i := i + 1) (by rw [List.length_take, Nat.min_eq_left hlen]; omega)
    rw [hget_a] at ha; rw [hget_b] at hb
    exact congrArg BitVec.toNat (Option.some.inj (ha.symm.trans hb))

theorem ded_fullLowerInv_set0 {c : FullCfg} {k : FullCoreState} {tmp : List (BitVec 32)}
    {mrk : List (BitVec 8)} {tl : Nat} (v : BitVec 32)
    (hlow : FullLowerInv c k tmp mrk tl) :
    FullLowerInv c k (tmp.set 0 v) mrk tl := by
  refine ⟨fun j hj1 hj2 => ?_, fun j1 j2 hj1 hj12 hj2 => ?_⟩
  · have hset : (tmp.set 0 v)[j]? = tmp[j]? := List.getElem?_set_ne (by omega)
    simpa only [hset] using hlow.1 j hj1 hj2
  · have hs1 : (tmp.set 0 v)[j1]? = tmp[j1]? := List.getElem?_set_ne (by omega)
    have hs2 : (tmp.set 0 v)[j2]? = tmp[j2]? := List.getElem?_set_ne (by omega)
    simpa only [hs1, hs2] using hlow.2 j1 j2 hj1 hj12 hj2

theorem ded_mem_activeResolvent_mono {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)}
    {tc' tl' mcl' : Nat}
    (hlen : k.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut k)
    (htl_len' : tl' ≤ tmp'.length) (htl_ge : k.tmp_len ≤ tl')
    (htp : ∀ i < k.tmp_len, tmp'[i]? = k.tmp[i]?)
    (hmp : ∀ v < c.max_vars, k.mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = k.mrk[v]?.getD 0#8) :
    ∀ {l}, l ∈ fullActiveResolvent k k.tmp k.mrk k.tmp_len k.trail_end →
      l ∈ fullActiveResolvent
        { k with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' }
        tmp' mrk' tl' k.trail_end := by
  intro l hl
  unfold fullActiveResolvent fullCurLits at hl ⊢
  rcases List.mem_append.mp hl with hl_trl | hl_low
  · refine List.mem_append.mpr (Or.inl ?_)
    rcases List.mem_map.mp hl_trl with ⟨j, hj_mem, rfl⟩
    rw [fullCurTrailIdxs_mem_iff] at hj_mem
    refine List.mem_map.mpr ⟨j, ?_, rfl⟩
    rw [fullCurTrailIdxs_mem_iff]
    have hlt := hw.trail_lits_lt j hj_mem.1
    have hmv : (k.trl[j]?.getD 0#32).toNat / 2 < c.max_vars := by
      have := hlen.cur_vars_le; omega
    refine ⟨hj_mem.1, ?_, hj_mem.2.2⟩
    dsimp only; rw [hmp _ hmv hj_mem.2.1]; exact hj_mem.2.1
  · refine List.mem_append.mpr (Or.inr ?_)
    have htl_len : k.tmp_len ≤ k.tmp.length := by
      rw [hlen.tmp_len_arr]; exact hlen.tmp_len_le
    rw [fullLowerLits_mem_iff htl_len] at hl_low
    rw [fullLowerLits_mem_iff htl_len']
    rcases hl_low with ⟨j, hj1, hj2, hxj⟩
    exact ⟨j, hj1, Nat.lt_of_lt_of_le hj2 htl_ge, by rw [htp j hj2, hxj]⟩

theorem ded_bv32_truncate_toNat_of_lt (x : BitVec 64) (hlt : x.toNat < 2 ^ 32) :
    (BitVec.truncate 32 x).toNat = x.toNat := by
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hlt

@[bv_c0] theorem ded_bv32_sext64_zero :
    (BitVec.signExtend 64 (0#32 : BitVec 32) : BitVec 64) = 0#64 := rfl

@[bv_c0] theorem ded_bv32_sext64_zero_mul4 :
    (BitVec.signExtend 64 (0#32 : BitVec 32) : BitVec 64) * 4#64 = 0#64 := rfl

/-! ## 2. `FullM6HdrMem` Callee Wrappers -/

theorem deduce_hdr_clear_wp {Γ : Env}
    (hClr : Γ.Has "full_clear_ana" Spec.fullClearAnaSpec)
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {rs : List Ty} {Q : Post rs} {X : XPost} {k : Tup Val [] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (mrk' : List (BitVec 8)) (m' : Mem 64),
      let s' : FullState := { s with core := { s.core with mrk := mrk', min_clr_len := 0 } }
      mrk'.length = c.max_vars →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 = 0#8) →
      (∀ i < s.core.min_clr_len, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars →
        mrk'[(s.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#8 = 0#8) →
      (FullAnaMarksCov c s → ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) k) m := by
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec _ _ (hClr (c.hdr, ()) m (fun r m' => wp Γ Q X (k r) m') X ?_)
  exact ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hmf,
    fun mrk' m' hlen' hm_pres hclr hm_all hm' =>
      hk mrk' m' hlen' hm_pres hclr hm_all (fullM6HdrMem_unfocus_full hm')⟩

theorem deduce_hdr_lit_wp {Γ : Env}
    (hLit : Γ.Has "full_analyze_lit" Spec.fullAnalyzeLitSpec)
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {lit skip_var : BitVec 32} {rs : List Ty} {Q : Post rs} {X : XPost}
    {k : Tup Val [.bool] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hcur32 : s.core.cur_level < 2 ^ 32)
    (htl_cv : s.core.tmp_len ≤ s.core.cur_vars) (htc_lt : s.core.tmp_cnt + 1 < 2 ^ 64)
    (hcov : FullAnaMarksCov c s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (ok : Bool) (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32))
        (tc' tl' mcl' : Nat) (ws1' : List (BitVec 32)) (ant' res' : BitVec 64) (m' : Mem 64),
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl' }
          scratch := { s.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } }
      s'.LengthsOk c → FullAnaMarksCov c s' →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.tmp_len + 1 → tl' ≤ s.core.cur_vars →
      s.core.tmp_cnt ≤ tc' →
      ant' = s.scratch.ant_sz +
        (if lit.toNat / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level
         then 1#64 else 0#64) →
      res' = s.scratch.res_sz +
        (if lit.toNat / 2 < s.core.cur_vars ∧ s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
            mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 then 1#64 else 0#64) →
      tc' = s.core.tmp_cnt +
        (if lit.toNat / 2 < s.core.cur_vars ∧ s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
            mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
            (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level then 1 else 0) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ i < s.core.tmp_len, tmp'[i]? = s.core.tmp[i]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        lit.toNat / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
        0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
        (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' →
        (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧ lit.toNat / 2 < s.core.cur_vars ∧
        lit.toNat / 2 ≠ skip_var.toNat ∧ s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
        0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level ∧
        mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) →
      (ok = true → lit.toNat / 2 < s.core.cur_vars ∧
        (lit.toNat / 2 ≠ skip_var.toNat →
          (0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat → mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 →
            (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
              (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
              tc' = s.core.tmp_cnt + 1) ∧
            (0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
              (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level →
              tl' = s.core.tmp_len + 1 ∧ tmp'[s.core.tmp_len]? = some lit)))) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_analyze_lit"
      (Arg.var c.hdr, Arg.var lit, Arg.var skip_var, ()) k) m := by
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec _ _ (hLit (c.hdr, lit, skip_var, ()) m
    (fun r m' => wp Γ Q X (k r) m') X ?_)
  exact ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hcur32, htl_cv, htc_lt, hcov, hmf,
    fun ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
      h14 hm' => hk ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
        h12 h13 h14 (fullM6HdrMem_unfocus_full hm')⟩

theorem deduce_hdr_otfs_bin_wp {Γ : Env}
    (hBin : Γ.Has "full_otfs_bin" Spec.fullOtfsBinSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut idx_u : Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {cref uip : BitVec 32} {rs : List Ty} {Q : Post rs} {X : XPost}
    {k : Tup Val [.bool] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s) (hdm : s.core.dense_mode = 0#64)
    (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false)
    (huip_lt : uip.toNat < 2 * s.core.cur_vars) (hidx_cut : idx_u < cut)
    (htrl_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hrsn_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlvl_u : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hent : ∀ f0 f1 : BitVec 32,
      f0.toNat ∈ fullArenaClauseLits s cref.toNat →
      f1.toNat ∈ fullArenaClauseLits s cref.toNat →
      f0 ≠ uip → f1 ≠ uip → f0 ≠ f1 →
      0 < (s.core.lvl[f0.toNat / 2]?.getD 0#32).toNat →
      0 < (s.core.lvl[f1.toNat / 2]?.getD 0#32).toNat →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, f1.toNat]))
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (ok : Bool) (arena' : List (BitVec 32)) (ag' : BitVec 64)
        (wvec' wstk' : List (BitVec 32)) (wlen' : Nat)
        (wu' nb' ctype' cr' c0' c1' oom' : BitVec 64) (sc' : FullScratch) (m' : Mem 64),
      let s' : FullState :=
        { core := { s.core with arena := arena', arena_garbage := ag', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                confl_type := ctype', confl_ref := cr', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
      FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → sc'.res_sz = s.scratch.res_sz →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → ctype' = 1#64 ∧ FullConflictOkCut F_cur idx_u s') →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_otfs_bin"
      (Arg.var c.hdr, Arg.var cref, Arg.var uip, ()) k) m := by
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec _ _ (hBin (c.hdr, cref, uip, ()) m
    (fun r m' => wp Γ Q X (k r) m') X ?_)
  exact ⟨c, F0, F_cur, cut, idx_u, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hw, hnd,
    hdm, href, hng, huip_lt, hidx_cut, htrl_u, hrsn_u, hlvl_u, hent, hmf,
    fun ok ar ag wv ws wl wu nb ct cr c0 c1 oom sc' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 hm' =>
      hk ok ar ag wv ws wl wu nb ct cr c0 c1 oom sc' m' h1 h2 h3 h4 h5 h6 h7 h8 h9
        (fullM6HdrMem_unfocus_full hm')⟩

theorem deduce_hdr_otfs_large_wp {Γ : Env}
    (hLarge : Γ.Has "full_otfs_large" Spec.step13OtfsLargeSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut idx_u : Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {cref uip : BitVec 32} {rs : List Ty} {Q : Post rs} {X : XPost}
    {k : Tup Val [.bool] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s) (hdm : s.core.dense_mode = 0#64)
    (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false)
    (huip_lt : uip.toNat < 2 * s.core.cur_vars) (hidx_cut : idx_u < cut)
    (htrl_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hrsn_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlvl_u : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause (List.filter
      (fun l => decide (l ≠ uip.toNat ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∨
        l = (s.core.arena[cref.toNat + 3]?.getD 0#32).toNat ∨
        l = (s.core.arena[cref.toNat + 4]?.getD 0#32).toNat)))
      (fullArenaClauseLits s cref.toNat))))
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (ok : Bool) (flags' arena' wvec' wstk' : List (BitVec 32)) (wlen' : Nat)
        (wu' oom' : BitVec 64) (sc' : FullScratch) (m' : Mem 64),
      let s' : FullState :=
        { core := { s.core with flags := flags', arena := arena', wvec := wvec', wstk := wstk',
                                wlen := wlen', wusable := wu', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
      FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → sc'.res_sz = s.scratch.res_sz →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → cref.toNat ∈ fullArenaClauseRefs s' ∧
        fullArenaClauseGarb s' cref.toNat = false ∧
        ∀ l ∈ fullArenaClauseLits s' cref.toNat, s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
            ∃ m, m < idx_u ∧ (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_otfs_large"
      (Arg.var c.hdr, Arg.var cref, Arg.var uip, ()) k) m := by
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec _ _ (hLarge (c.hdr, cref, uip, ()) m
    (fun r m' => wp Γ Q X (k r) m') X ?_)
  exact ⟨c, F0, F_cur, cut, idx_u, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hw, hnd,
    hdm, href, hng, huip_lt, hidx_cut, htrl_u, hrsn_u, hlvl_u, hent, hmf,
    fun ok fl ar wv ws wl wu oom sc' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 hm' =>
      hk ok fl ar wv ws wl wu oom sc' m' h1 h2 h3 h4 h5 h6 h7 h8 h9
        (fullM6HdrMem_unfocus_full hm')⟩

theorem deduce_hdr_otfs_subsume_wp {Γ : Env}
    (hSub : Γ.Has "full_otfs_subsume" Spec.fullOtfsSubsumeSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {new_confl : BitVec 32} {old_ctype old_cref : BitVec 64} {to_bin : Bool}
    {rs : List Ty} {Q : Post rs} {X : XPost} {k : Tup Val [] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s)
    (hpre : old_ctype = 2#64 → old_cref ≠ 0xFFFFFFFF#64 →
      old_cref.toNat ∈ fullArenaClauseRefs s ∧
      (to_bin = false → new_confl.toNat ∈ fullArenaClauseRefs s) ∧
      ∀ idx < s.core.trail_end,
        let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
        let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
        (idx < cut ∨ (s.core.lvl[v]?.getD 0#32).toNat < s.core.cur_level) →
        rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ old_cref.toNat)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (arena' : List (BitVec 32)) (ag' ni' nr' : BitVec 64) (m' : Mem 64),
      let s' : FullState :=
        { s with core := { s.core with arena := arena', arena_garbage := ag',
                                       num_irred := ni', num_redundant := nr' } }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullArenaVarsNodup s' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s,
        fullArenaClauseLits s' r = fullArenaClauseLits s r ∧
        ((old_ctype = 2#64 → r ≠ old_cref.toNat) →
          fullArenaClauseGarb s' r = fullArenaClauseGarb s r)) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i64, i64, .bool]) (bs := []) "full_otfs_subsume"
      (Arg.var c.hdr, Arg.var new_confl, Arg.var old_ctype, Arg.var old_cref, Arg.var to_bin, ())
      k) m := by
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec _ _ (hSub (c.hdr, new_confl, old_ctype, old_cref, to_bin, ()) m
    (fun r m' => wp Γ Q X (k r) m') X ?_)
  exact ⟨c, F0, F_cur, cut, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hw, hnd, hpre, hmf,
    fun ar ag ni nr m' h1 h2 h3 h4 h5 hm' =>
      hk ar ag ni nr m' h1 h2 h3 h4 h5 (fullM6HdrMem_unfocus_full hm')⟩

/-! ## 3. Clear-Exit & Seed-Terminal Helpers -/

theorem deduce_clear_ret0_wp {Γ : Env}
    (hClr : Γ.Has "full_clear_ana" Spec.fullClearAnaSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {ext : List (BitVec 64)} {s0 s_cur : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcut0 : FullCutInvW c F0 F_cur cut s0)
    (hext_ok : M6HdrExtOk ext) (hlen_c : s_cur.LengthsOk c)
    (hw_c : FullWitnessCutInv c F0 F_cur cut s_cur.core)
    (hcov_c : FullAnaMarksCov c s_cur) (hnd_c : FullArenaVarsNodup s_cur)
    (hext_p : FullExtScratchPres s0 s_cur) (hws2_c : s_cur.scratch.work_stk2 = s0.scratch.work_stk2)
    (hrefs_c : fullArenaClauseRefs s_cur = fullArenaClauseRefs s0)
    (hstat_c : FullDeduceStaticEq s0.core s_cur.core)
    (hm : (FullM6HdrMem c ext s_cur ⋆ R) m)
    (hQ0 : ∀ ext' (s' : FullState) m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → FullOtfsInvW c F0 F_cur s' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (0#64, ()) m') :
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
      Expr.ret (Arg.imm 0#64, ())) m := by
  refine deduce_hdr_clear_wp hClr hlen_c hm fun mrk' m' hm_len _ _ hm_all hm' => ?_
  d_hsteps
  let s' : FullState := { s_cur with core := { s_cur.core with mrk := mrk', min_clr_len := 0 } }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen_c.core_ok with mrk_len := hm_len, min_clr_len_le := Nat.zero_le _ }, hlen_c.scratch_ok⟩
  have hw' := ded_witnessCut_with_ana hw_c mrk' s_cur.core.tmp
    s_cur.core.tmp_cnt s_cur.core.tmp_len 0
  have hnd' : FullArenaVarsNodup s' := ded_arenaVarsNodup_same_core_arena hnd_c rfl rfl
  have hotfs := ded_otfsInvW_of_cleared_state hlen' hw' (hm_all hcov_c) hcut0.2.2.1
    hstat_c.lm hnd' hcut0.2.2.2.2.1 ⟨rfl, rfl⟩ hext_p hstat_c.cv rfl hrefs_c
    (hstat_c.dm.trans hcut0.2.2.2.2.2)
  exact hQ0 ext s' m' hext_ok hlen' hstat_c.cv hstat_c.fuel hws2_c hotfs hm'

theorem deduce_seed_unsat_or_ret0_wp {Γ : Env}
    (hClr : Γ.Has "full_clear_ana" Spec.fullClearAnaSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {ext : List (BitVec 64)} {s0 s_cur : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {ok : Bool}
    (hcut0 : FullCutInvW c F0 F_cur cut s0)
    (hext_ok : M6HdrExtOk ext) (hlen_c : s_cur.LengthsOk c)
    (hw_c : FullWitnessCutInv c F0 F_cur cut s_cur.core)
    (hcov_c : FullAnaMarksCov c s_cur) (hnd_c : FullArenaVarsNodup s_cur)
    (hext_p : FullExtScratchPres s0 s_cur) (hws2_c : s_cur.scratch.work_stk2 = s0.scratch.work_stk2)
    (hrefs_c : fullArenaClauseRefs s_cur = fullArenaClauseRefs s0)
    (hstat_c : FullDeduceStaticEq s0.core s_cur.core)
    (hok_inv : ok = true →
      FullDeduceStateInv c F0 F_cur cut s_cur.core.trail_end s0 s_cur ∧ s_cur.core.tmp_cnt = 0)
    (hm : (FullM6HdrMem c ext s_cur ⋆ R) m)
    (hQ0 : ∀ ext' (s' : FullState) m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → FullOtfsInvW c F0 F_cur s' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (0#64, ()) m')
    (hQ20 : ∀ ext' (s' : FullState) m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → F0.Unsat → FullOtfsInvW c F0 F_cur s' →
      s'.core.cur_level ≤ s0.core.cur_level → s'.core.dense_mode = s0.core.dense_mode →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (20#64, ()) m') :
    wp Γ Q X
      (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
        Expr.jnz (Arg.var ok)
          (Expr.let_ (ts := [i64]) { sig := [i64, i64], code := OpCode.add i64,
                                     args := (Arg.var c.hdr, Arg.imm 192, ()) } fun p =>
            Expr.load i64 (Arg.var p.fst) fun ld =>
              Expr.let_ (ts := [.bool])
                { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                  args := (Arg.var ld, Arg.imm 1#64, ()) } fun p =>
                Expr.jnz (Arg.var p.fst)
                  (Expr.ret (Arg.imm 20#64, ())) (Expr.ret (Arg.imm 0#64, ())))
          (Expr.ret (Arg.imm 0#64, ()))) m := by
  refine deduce_hdr_clear_wp hClr hlen_c hm fun mrk' m' hm_len _ _ hm_all hm' => ?_
  let s' : FullState := { s_cur with core := { s_cur.core with mrk := mrk', min_clr_len := 0 } }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen_c.core_ok with mrk_len := hm_len, min_clr_len_le := Nat.zero_le _ }, hlen_c.scratch_ok⟩
  have hw' := ded_witnessCut_with_ana hw_c mrk' s_cur.core.tmp
    s_cur.core.tmp_cnt s_cur.core.tmp_len 0
  have hnd' : FullArenaVarsNodup s' := ded_arenaVarsNodup_same_core_arena hnd_c rfl rfl
  have hotfs := ded_otfsInvW_of_cleared_state hlen' hw' (hm_all hcov_c) hcut0.2.2.1
    hstat_c.lm hnd' hcut0.2.2.2.2.1 ⟨rfl, rfl⟩ hext_p hstat_c.cv rfl hrefs_c
    (hstat_c.dm.trans hcut0.2.2.2.2.2)
  have hmax32 := fullInv_max_vars_lt32 c
  have htl_lt : s'.core.tmp_len < 2 ^ 64 := by
    have := hlen'.core_ok.tmp_len_le; omega
  refine wp_m6Hdr_focus_frame hm' fun hm'f => ?_
  d_hsteps
  · obtain ⟨hinv, htc0⟩ := hok_inv ‹ok = true›
    have hbv1 : BitVec.ofNat 64 s_cur.core.tmp_len = 1#64 := by assumption
    have htl1 : s_cur.core.tmp_len = 1 := by
      have := congrArg BitVec.toNat hbv1
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa [s'] using htl_lt)] at this
      exact this
    have hidx_empty : fullCurTrailIdxs s_cur.core s_cur.core.mrk s_cur.core.trail_end = [] :=
      List.length_eq_zero_iff.mp (by rw [← hinv.tc_eq, htc0])
    have hact_nil : fullActiveResolvent s_cur.core s_cur.core.tmp s_cur.core.mrk
        s_cur.core.tmp_len s_cur.core.trail_end = [] := by
      unfold fullActiveResolvent fullCurLits
      rw [htl1, fullLowerLits_one, hidx_empty, List.map_nil, List.nil_append]
    have hent_empty := hinv.ent
    rw [hact_nil] at hent_empty
    have hunsat_cur : (cnfOfClauses F_cur).Unsat := unsat_of_entails_nil hent_empty
    have hf0_unsat : F0.Unsat := hw'.ext_sound.2 hunsat_cur
    exact hQ20 ext s' m' hext_ok hlen' hstat_c.cv hstat_c.fuel hws2_c hf0_unsat hotfs
      (Nat.le_of_eq hstat_c.cl) (hstat_c.dm.trans rfl) (fullM6HdrMem_unfocus_full hm'f)
  · exact hQ0 ext s' m' hext_ok hlen' hstat_c.cv hstat_c.fuel hws2_c hotfs
      (fullM6HdrMem_unfocus_full hm'f)
  · exact hQ0 ext s' m' hext_ok hlen' hstat_c.cv hstat_c.fuel hws2_c hotfs
      (fullM6HdrMem_unfocus_full hm'f)

/-! ## 4. 1-UIP Exit WP (`deduce_uip_exit_body_wp`) -/

theorem deduce_uip_exit_body_wp {Γ : Env}
    (hClr : Γ.Has "full_clear_ana" Spec.fullClearAnaSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {ext : List (BitVec 64)} {s0 s_cur : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {uip_lit : BitVec 32}
    (hcut0 : FullCutInvW c F0 F_cur cut s0)
    (hext_ok : M6HdrExtOk ext) (hlen_c : s_cur.LengthsOk c)
    (hw_c : FullWitnessCutInv c F0 F_cur cut s_cur.core)
    (hcov_c : FullAnaMarksCov c s_cur) (hnd_c : FullArenaVarsNodup s_cur)
    (hext_p : FullExtScratchPres s0 s_cur) (hws2_c : s_cur.scratch.work_stk2 = s0.scratch.work_stk2)
    (hrefs_c : fullArenaClauseRefs s_cur = fullArenaClauseRefs s0)
    (hstat_c : FullDeduceStaticEq s0.core s_cur.core)
    (hgood : uip_lit ≠ 0xFFFFFFFF#32 → ∃ (idx' : Nat) (p_bv : BitVec 32),
      FullDeduceStateInv c F0 F_cur cut (idx' + 1) s0 s_cur ∧
      idx' < s_cur.core.trail_end ∧ (s_cur.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat ∧
      uip_lit = p_bv ^^^ 1#32 ∧ s_cur.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s_cur.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s_cur.core.cur_level ∧
      (fullCurTrailIdxs s_cur.core s_cur.core.mrk idx').length = 0)
    (hm : (FullM6HdrMem c ext s_cur ⋆ R) m)
    (hQ0 : ∀ ext' (s' : FullState) m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → FullOtfsInvW c F0 F_cur s' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (0#64, ()) m')
    (hQ1 : ∀ ext' (s' : FullState) m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 → FullOtfsInvW c F0 F_cur s' →
      s'.core.cur_level = s0.core.cur_level →
      1 ≤ s'.core.tmp_len → s'.core.tmp_len ≤ s'.core.cur_vars →
      (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup →
      (∀ k < s'.core.tmp_len,
        (s'.core.tmp[k]?.getD 0#32).toNat < 2 * s'.core.cur_vars ∧
        s'.core.vals[(s'.core.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) →
      (∀ k, 1 ≤ k → k < s'.core.tmp_len →
        0 < (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
        (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < s'.core.cur_level) →
      (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s'.core.cur_level →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp))) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (1#64, ()) m') :
    wp Γ Q X
      (Expr.let_ (ts := [.bool])
        { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
          args := (Arg.var uip_lit, Arg.imm 0xFFFFFFFF, ()) } fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
            Expr.ret (Arg.imm 0, ()))
          (Expr.let_ (ts := [i64])
            { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun p_2 =>
            Expr.let_ (ts := [i64])
              { sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var p_2.fst, Arg.imm 4, ()) } fun p_3 =>
              Expr.let_ (ts := [i64])
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var c.pTmp, Arg.var p_3.fst, ()) } fun p_4 =>
                Expr.store (t := i32) (Arg.var uip_lit) (Arg.var p_4.fst)
                  (Expr.let_ (ts := [i64])
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.hdr, Arg.imm 272, ()) } fun p =>
                    Expr.load i64 (Arg.var p.fst) fun ld =>
                      Expr.let_ (ts := [i64])
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var c.hdr, Arg.imm 1144, ()) } fun p =>
                        Expr.store (Arg.var ld) (Arg.var p.fst)
                          (Expr.call (as := [i64]) (bs := []) "full_clear_ana"
                            (Arg.var c.hdr, ()) fun _ => Expr.ret (Arg.imm 1, ()))))) m := by
  d_hsteps_nogrp
  · exact deduce_clear_ret0_wp hClr hcut0 hext_ok hlen_c hw_c hcov_c hnd_c hext_p hws2_c
      hrefs_c hstat_c hm hQ0
  · obtain ⟨idx', p_bv, hs1, hidx_te, hp_get, huip_eq, hm_p, hl_p, hempty⟩ := hgood ‹_›
    have hmcl_lt : s_cur.core.min_clr_len < 2 ^ 64 := by
      have := hlen_c.core_ok.min_clr_len_le; have := fullInv_max_vars_lt32 c; omega
    have htmp_pos : 0 < s_cur.core.tmp.length := by
      rw [hlen_c.core_ok.tmp_len_arr]
      have := hs1.tl_ge; have := hs1.tl_cv; have := hlen_c.core_ok.cur_vars_le; omega
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    d_hsteps_nogrp
    let s1 : FullState :=
      { s_cur with
        core := { s_cur.core with tmp := s_cur.core.tmp.set 0 uip_lit }
        scratch := { s_cur.scratch with res_sz := BitVec.ofNat 64 s_cur.core.min_clr_len } }
    have hso1 := hlen_c.scratch_ok
    have hlen1 : s1.LengthsOk c :=
      ⟨{ hlen_c.core_ok with tmp_len_arr := (by
           dsimp [s1]; rw [List.length_set, hlen_c.core_ok.tmp_len_arr]) },
        { hso1 with walk_vals_len := hso1.walk_vals_len }⟩
    have htmp0 : s1.core.tmp[0]? = some uip_lit := List.getElem?_set_self htmp_pos
    have htl_len1 : s1.core.tmp_len ≤ s1.core.tmp.length := by
      rw [hlen1.core_ok.tmp_len_arr]; exact hlen1.core_ok.tmp_len_le
    have huip_div2 : uip_lit.toNat / 2 = p_bv.toNat / 2 := by
      rw [huip_eq, BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, ded_lit_xor1_div2]
    have huip_nat : uip_lit.toNat = p_bv.toNat ^^^ 1 := by
      rw [huip_eq, BitVec.toNat_xor]; rfl
    have hnodup1 : (List.map (fun x => x.toNat / 2)
        (List.take s1.core.tmp_len s1.core.tmp)).Nodup := by
      refine fullTmpTake_uip_nodup hs1.tl_ge htl_len1 htmp0
        (ded_fullLowerInv_set0 uip_lit hs1.low) ?_
      rw [huip_div2]; exact hl_p
    have hp_lt : p_bv.toNat < 2 * s_cur.core.cur_vars := by
      rw [← hp_get]; exact hs1.hw.trail_lits_lt idx' hidx_te
    have huip_lt : uip_lit.toNat < 2 * s_cur.core.cur_vars := by rw [huip_nat]; omega
    have huip_fals : s_cur.core.vals[uip_lit.toNat]?.getD 0#8 = 0xFF#8 := by
      rw [huip_nat, hs1.hw.vals_false_iff (p_bv.toNat ^^^ 1) (by omega)]
      exact ⟨idx', hidx_te, by rw [hp_get, ded_lit_xor1_xor1]⟩
    have hent1 : (cnfOfClauses F_cur).EntailsClause
        (cnfClause (List.map BitVec.toNat (List.take s1.core.tmp_len s1.core.tmp))) := by
      rw [fullLowerLits_take_eq hs1.tl_ge htmp0,
        show fullLowerLits s1.core.tmp s1.core.tmp_len =
          fullLowerLits s_cur.core.tmp s_cur.core.tmp_len from
          ded_fullLowerLits_set0 uip_lit hs1.tl_ge
            (by rw [hlen_c.core_ok.tmp_len_arr]; exact hlen_c.core_ok.tmp_len_le),
        huip_eq]
      exact fullDeduce_uip_entails hempty (by rw [hp_get]; exact hm_p)
        (by rw [hp_get]; exact hl_p) hp_get hs1.ent
    refine deduce_hdr_clear_wp hClr hlen1 (fullM6HdrMem_unfocus_full (s := s1) ‹_›)
      fun mrk' m' hm_len _ _ hm_all hm' => ?_
    d_hsteps
    let s' : FullState := { s1 with core := { s1.core with mrk := mrk', min_clr_len := 0 } }
    have hlen' : s'.LengthsOk c :=
      ⟨{ hlen1.core_ok with mrk_len := hm_len, min_clr_len_le := Nat.zero_le _ }, hlen1.scratch_ok⟩
    have hw' := ded_witnessCut_with_ana hw_c mrk' s1.core.tmp s1.core.tmp_cnt s1.core.tmp_len 0
    have hnd' : FullArenaVarsNodup s' := ded_arenaVarsNodup_same_core_arena hnd_c rfl rfl
    have hotfs := ded_otfsInvW_of_cleared_state hlen' hw' (hm_all hcov_c) hcut0.2.2.1
      hstat_c.lm hnd' hcut0.2.2.2.2.1 ⟨rfl, rfl⟩ hext_p hstat_c.cv rfl hrefs_c
      (hstat_c.dm.trans hcut0.2.2.2.2.2)
    refine hQ1 ext s' m' hext_ok hlen' hstat_c.cv hstat_c.fuel hws2_c hotfs hstat_c.cl
      hs1.tl_ge hs1.tl_cv hnodup1 (fun k hk => ?_) (fun k hk1 hk2 => ?_) ?_ hent1 hm'
    · by_cases hk0 : k = 0
      · subst hk0
        dsimp only [s', s1]
        rw [List.getElem?_set_self htmp_pos, Option.getD_some]
        exact ⟨huip_lt, huip_fals⟩
      · have hs_set : s'.core.tmp[k]? = s_cur.core.tmp[k]? := List.getElem?_set_ne (by omega)
        have hlowk := hs1.low.1 k (by omega) hk
        dsimp only [s', s1] at hs_set ⊢
        rw [hs_set]
        exact ⟨hlowk.1, hlowk.2.1⟩
    · have hs_set : s'.core.tmp[k]? = s_cur.core.tmp[k]? := List.getElem?_set_ne (by omega)
      have hlowk := hs1.low.1 k hk1 hk2
      dsimp only [s', s1] at hs_set ⊢
      rw [hs_set]
      exact ⟨hlowk.2.2.1, hlowk.2.2.2.1⟩
    · dsimp only [s', s1]
      rw [List.getElem?_set_self htmp_pos, Option.getD_some, huip_div2]
      exact hl_p

/-! ## 5. Seed WP (`deduce_seed_wp`) -/

private theorem ded_seed_init_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s sl : FullState}
    (hcut0 : FullCutInvW c F0 F_cur cut s) (hpos : 0 < s.core.cur_level)
    (hsl_c : sl.core = { s.core with tmp_cnt := 0, tmp_len := 1, min_clr_len := 0 })
    (hsl_sc : sl.scratch = { s.scratch with ant_sz := 0#64, res_sz := 0#64 }) :
    FullState.LengthsOk c sl ∧ FullWitnessCutInv c F0 F_cur cut sl.core ∧
    FullAnaMarksCov c sl ∧ FullArenaVarsNodup sl ∧
    fullArenaClauseRefs sl = fullArenaClauseRefs s ∧ FullExtScratchPres s sl ∧
    sl.scratch.work_stk2 = s.scratch.work_stk2 ∧ FullDeduceStaticEq s.core sl.core ∧
    1 ≤ sl.core.cur_vars ∧ FullLowerInv c sl.core sl.core.tmp sl.core.mrk 1 ∧
    FullMarksCov sl.core sl.core.tmp sl.core.mrk 1 ∧
    FullCurMarksBelow sl.core.trail_end sl.core sl.core.mrk cut ∧
    sl.core.tmp_cnt = (fullCurTrailIdxs sl.core sl.core.mrk sl.core.trail_end).length := by
  have h1_cv : 1 ≤ s.core.cur_vars := by
    have := hcut0.2.1.cur_level_le; have := hcut0.1.core_ok.trail_end_le; omega
  have h1_mv : 1 ≤ c.max_vars := Nat.le_trans h1_cv hcut0.1.core_ok.cur_vars_le
  have hlen : sl.LengthsOk c := by
    refine ⟨?_, ?_⟩
    · rw [hsl_c]
      exact { hcut0.1.core_ok with tmp_len_le := h1_mv, min_clr_len_le := Nat.zero_le _ }
    · rw [hsl_sc]
      have hso := hcut0.1.scratch_ok
      exact { hso with walk_vals_len := hso.walk_vals_len }
  have hw : FullWitnessCutInv c F0 F_cur cut sl.core := by
    rw [hsl_c]; exact ded_witnessCut_with_ana hcut0.2.1 _ _ 0 1 0
  have hclr : ∀ v < c.max_vars, sl.core.mrk[v]?.getD 0#8 = 0#8 := by
    intro v hv; rw [hsl_c]; exact hcut0.2.2.1.1 v hv
  have hcov : FullAnaMarksCov c sl := fullAnaMarksCov_of_clear hclr (by rw [hsl_c])
  have hnd : FullArenaVarsNodup sl :=
    ded_arenaVarsNodup_same_core_arena hcut0.2.2.2.1 (by rw [hsl_c]) (by rw [hsl_c])
  have hrefs : fullArenaClauseRefs sl = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hsl_c]
  have hext : FullExtScratchPres s sl := by
    unfold FullExtScratchPres; rw [hsl_sc]; exact ⟨rfl, rfl⟩
  have hws2 : sl.scratch.work_stk2 = s.scratch.work_stk2 := by rw [hsl_sc]
  have hstat : FullDeduceStaticEq s.core sl.core := by
    rw [hsl_c]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hlow : FullLowerInv c sl.core sl.core.tmp sl.core.mrk 1 :=
    ⟨fun _ h1 h2 => by omega, fun _ _ h1 h2 _ => by omega⟩
  have hmcov : FullMarksCov sl.core sl.core.tmp sl.core.mrk 1 := by
    intro v hv hnz
    have hmv : v < c.max_vars := by
      have := hcut0.1.core_ok.cur_vars_le; rw [hsl_c] at hv; dsimp only at hv; omega
    exact absurd (hclr v hmv) hnz
  have hcm : FullCurMarksBelow sl.core.trail_end sl.core sl.core.mrk cut := by
    intro j hj hnz
    have hlt := hw.trail_lits_lt j hj
    have hv_lt : (sl.core.trl[j]?.getD 0#32).toNat / 2 < c.max_vars := by
      have := hcut0.1.core_ok.cur_vars_le; rw [hsl_c] at hlt ⊢; dsimp only at hlt ⊢; omega
    exact absurd (hclr _ hv_lt) hnz
  have hnil : fullCurTrailIdxs sl.core sl.core.mrk sl.core.trail_end = [] :=
    ded_curTrailIdxs_nil_of_clear (Nat.le_refl _) (by rw [hsl_c]; exact hcut0.1.core_ok.cur_vars_le)
      hw.trail_lits_lt hclr
  exact ⟨hlen, hw, hcov, hnd, hrefs, hext, hws2, hstat, by rw [hsl_c]; exact h1_cv,
    hlow, hmcov, hcm, by rw [hnil, hsl_c]; rfl⟩

theorem deduce_seed_wp {Γ : Env}
    (hLit : Γ.Has "full_analyze_lit" Spec.fullAnalyzeLitSpec)
    (hRsn : Γ.Has "full_analyze_rsn_m6_hdr" Spec.s13AnalyzeRsnHdrSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {ext : List (BitVec 64)} {s sl : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {J : Cont [.bool]} {X : XPost} {Q : Post [i64]}
    (hcfg : FullM6HdrCfgOk c) (hcut0 : FullCutInvW c F0 F_cur cut s) (hext_ok : M6HdrExtOk ext)
    (hpos : 0 < s.core.cur_level) (hconfl : FullConflictOkCut F_cur cut s)
    (hsl_c : sl.core = { s.core with tmp_cnt := 0, tmp_len := 1, min_clr_len := 0 })
    (hsl_sc : sl.scratch = { s.scratch with ant_sz := 0#64, res_sz := 0#64 })
    (hm : (FullM6HdrMem c ext sl ⋆ R) m)
    (hJ : ∀ (ok : Bool) (ext1 : List (BitVec 64)) (s1 : FullState) (ml : Mem 64),
      M6HdrExtOk ext1 → s1.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s1.core →
      FullAnaMarksCov c s1 → FullArenaVarsNodup s1 → FullExtScratchPres s s1 →
      s1.scratch.work_stk2 = s.scratch.work_stk2 →
      fullArenaClauseRefs s1 = fullArenaClauseRefs s →
      FullDeduceStaticEq s.core s1.core →
      (ok = true → FullDeduceStateInv c F0 F_cur cut s1.core.trail_end s s1) →
      (FullM6HdrMem c ext1 s1 ⋆ R) ml → J (ok, ()) ml) :
    wp Γ Q X
      (Expr.let_ (ts := [i64]) { sig := [i64, i64], code := OpCode.add i64,
                                 args := (Arg.var c.hdr, Arg.imm 528, ()) } fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
          Expr.let_ (ts := [.bool])
            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
              args := (Arg.var ld, Arg.imm 1, ()) } fun p =>
            Expr.jnz (Arg.var p.fst)
              (Expr.group (sig := [[.bool]]) (fun _ =>
                Blocks.cons (fun p => Expr.jump (ts := [.bool]) J (Arg.var p.fst, ()))
                  Blocks.nil) fun Js =>
                Expr.let_ (ts := [i64])
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var c.hdr, Arg.imm 536, ()) } fun p =>
                  Expr.load i64 (Arg.var p.fst) fun ld =>
                    Expr.let_ (ts := [i32])
                      { sig := [i64], code := OpCode.trunc 64 32,
                        args := (Arg.var ld, ()) } fun p =>
                      Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_analyze_lit"
                        (Arg.var c.hdr, Arg.var p.fst, Arg.imm 0xFFFFFFFF, ()) fun p =>
                        Expr.jnz (Arg.var p.fst)
                          (Expr.let_ (ts := [i64])
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var c.hdr, Arg.imm 544, ()) } fun p =>
                            Expr.load i64 (Arg.var p.fst) fun ld =>
                              Expr.let_ (ts := [i32])
                                { sig := [i64], code := OpCode.trunc 64 32,
                                  args := (Arg.var ld, ()) } fun p =>
                                Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_analyze_lit"
                                  (Arg.var c.hdr, Arg.var p.fst, Arg.imm 0xFFFFFFFF, ())
                                  fun p => Expr.jnz (Arg.var p.fst)
                                    (Expr.jump (ts := [.bool]) Js.fst (Arg.imm true, ()))
                                    (Expr.jump (ts := [.bool]) Js.fst (Arg.imm false, ())))
                          (Expr.jump (ts := [.bool]) Js.fst (Arg.imm false, ())))
              (Expr.group (sig := [[.bool]]) (fun _ =>
                Blocks.cons (fun p => Expr.jump (ts := [.bool]) J (Arg.var p.fst, ()))
                  Blocks.nil) fun Js =>
                Expr.let_ (ts := [i64])
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var c.hdr, Arg.imm 176, ()) } fun p =>
                  Expr.load i64 (Arg.var p.fst) fun ld =>
                    Expr.let_ (ts := [i64])
                      { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var ld, Arg.imm 3, ()) } fun p =>
                      Expr.let_ (ts := [i64])
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var c.hdr, Arg.imm 48, ()) } fun p_1 =>
                        Expr.load i64 (Arg.var p_1.fst) fun ld =>
                          Expr.let_ (ts := [.bool])
                            { sig := [i64, i64], code := OpCode.cmp CmpOp.ule i64 Ty.bool rfl,
                              args := (Arg.var p.fst, Arg.var ld, ()) } fun p =>
                            Expr.jnz (Arg.var p.fst)
                              (Expr.let_ (ts := [i64])
                                { sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var c.hdr, Arg.imm 176, ()) } fun p =>
                                Expr.load i64 (Arg.var p.fst) fun ld =>
                                  Expr.let_ (ts := [i32])
                                    { sig := [i64], code := OpCode.trunc 64 32,
                                      args := (Arg.var ld, ()) } fun p =>
                                    Expr.call (as := [i64, i32, i32]) (bs := [.bool])
                                      "full_analyze_rsn_m6_hdr"
                                      (Arg.var c.hdr, Arg.var p.fst, Arg.imm 0xFFFFFFFF, ())
                                      fun p => Expr.jump (ts := [.bool]) Js.fst
                                        (Arg.var p.fst, ()))
                              (Expr.jump (ts := [.bool]) Js.fst (Arg.imm false, ())))) m := by
  obtain ⟨hlen_l, hw_l, hcov_l, hnd_l, hrefs_l, hext_l, hws2_l, hstat_l, h1_cv_l,
    hlow_l, hmcov_l, hcm_l, htc_l⟩ := ded_seed_init_facts hcut0 hpos hsl_c hsl_sc
  have hmax28 : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hmax32 := fullInv_max_vars_lt32 c
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hcut0.1.core_ok.cur_vars_le
  have hcur32_l : sl.core.cur_level < 2 ^ 32 := by
    have := hw_l.cur_level_le; have := hlen_l.core_ok.trail_end_le
    have := hlen_l.core_ok.cur_vars_le; omega
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  d_hsteps_nogrp
  · have hct1 : sl.core.confl_type = 1#64 := by assumption
    have hct_s1 : s.core.confl_type = 1#64 := by rwa [hsl_c] at hct1
    have hco_w : s.core.confl_type = 1#64 ∧ s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
        s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
        s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
        s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat]) := by
      rcases hconfl.1 with hc1 | hc2
      · exact hc1
      · exfalso; rw [hct_s1] at hc2; cases hc2.1
    have hco_cut := hconfl.2; rw [ite_eq_left hct_s1] at hco_cut
    have hl0_32 : s.core.confl_lit0.toNat < 2 ^ 32 := by have := hco_w.2.1; omega
    have hl1_32 : s.core.confl_lit1.toNat < 2 ^ 32 := by have := hco_w.2.2.1; omega
    have hl0_tr : (BitVec.truncate 32 sl.core.confl_lit0).toNat = s.core.confl_lit0.toNat := by
      rw [hsl_c]; exact ded_bv32_truncate_toNat_of_lt _ hl0_32
    have hl1_tr : (BitVec.truncate 32 sl.core.confl_lit1).toNat = s.core.confl_lit1.toNat := by
      rw [hsl_c]; exact ded_bv32_truncate_toNat_of_lt _ hl1_32
    refine wp_unroll_group fun Js hJs => ?_
    d_hsteps_nogrp
    refine deduce_hdr_lit_wp hLit hlen_l hcur32_l
      (by have h := h1_cv_l; rw [hsl_c] at h ⊢; exact h)
      (by rw [hsl_c]; dsimp only; omega) hcov_l (fullM6HdrMem_unfocus_full hmf)
      fun ok1 mrk1 tmp1 tc1 tl1 mcl1 ws1_1 ant1 res1 m1 hlen1 hcov1 htl1_ge htl1_le htl1_cv
        htc1_ge hant1 hres1 htc1_eq hmp1 htp1 hnm1 hnt1 hok1 hm1 => ?_
    let sa : FullState :=
      { sl with
        core := { sl.core with mrk := mrk1, tmp := tmp1, tmp_cnt := tc1, tmp_len := tl1,
                               min_clr_len := mcl1 }
        scratch := { sl.scratch with work_stk1 := ws1_1, ant_sz := ant1, res_sz := res1 } }
    d_hsteps_nogrp
    · have hok1t : ok1 = true := by assumption
      subst ok1
      have h_ok1 := hok1 rfl
      have hff : (4294967295 : BitVec 32).toNat = 4294967295 := rfl
      have hne1 : (BitVec.setWidth 32 sl.core.confl_lit0, ()).fst.toNat / 2 ≠
          (4294967295 : BitVec 32).toNat := by
        have h1 := h_ok1.1; have h2 := hlen_l.core_ok.cur_vars_le; omega
      have hsa_pres := deduce_seed_lit_step hlen_l hw_l hnd_l hrefs_l hext_l hws2_l hstat_l
        (by rw [hsl_c]; dsimp only; omega) (by rw [hsl_c]; exact Nat.zero_le _) htc_l
        (by have h := hlow_l; rw [hsl_c] at h ⊢; exact h)
        (by have h := hmcov_l; rw [hsl_c] at h ⊢; exact h) hcm_l
        (by rw [hsl_c, hsl_sc]; rfl) (by rw [hl0_tr, hsl_c]; exact hco_w.2.1)
        (by rw [hl0_tr, hsl_c]; exact hco_w.2.2.2.1)
        (by rw [hl0_tr, hsl_c]; exact hco_cut.1) sa rfl rfl hlen1 hcov1 htl1_cv htl1_ge htl1_le
        hmp1 htp1 hnm1 hnt1 hres1 htc1_eq ⟨h_ok1.1, h_ok1.2 hne1⟩
      obtain ⟨hl_a, hw_a, hcov_a, hext_a, hws2_a, hnd_a, hrefs_a, hstat_a, htl1_a, htl_cv_a,
        htc_eq_a, hlow_a, hmcov_a, hcm_a, _, hl0_res, hres_a⟩ := hsa_pres
      have htc_a_le1 : sa.core.tmp_cnt ≤ 1 := by
        dsimp [sa]; rw [htc1_eq, hsl_c]; dsimp only; split <;> omega
      have hcur32_a : sa.core.cur_level < 2 ^ 32 := by
        rw [hstat_a.cl, ← hstat_l.cl]; exact hcur32_l
      refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
      d_hsteps_nogrp
      refine deduce_hdr_lit_wp hLit hl_a hcur32_a htl_cv_a (by omega) hcov_a
        (fullM6HdrMem_unfocus_full hm1f)
        fun ok2 mrk2 tmp2 tc2 tl2 mcl2 ws1_2 ant2 res2 m2 hlen2 hcov2 htl2_ge htl2_le htl2_cv
          htc2_ge hant2 hres2 htc2_eq hmp2 htp2 hnm2 hnt2 hok2 hm2 => ?_
      let sb : FullState :=
        { sa with
          core := { sa.core with mrk := mrk2, tmp := tmp2, tmp_cnt := tc2, tmp_len := tl2,
                                 min_clr_len := mcl2 }
          scratch := { sa.scratch with work_stk1 := ws1_2, ant_sz := ant2, res_sz := res2 } }
      have hw_b : FullWitnessCutInv c F0 F_cur cut sb.core :=
        ded_witnessCut_with_ana hw_a _ _ _ _ _
      have hnd_b : FullArenaVarsNodup sb := ded_arenaVarsNodup_same_core_arena hnd_a rfl rfl
      have hrefs_b : fullArenaClauseRefs sb = fullArenaClauseRefs s := hrefs_a
      have hext_b : FullExtScratchPres s sb := hext_a
      have hws2_b : sb.scratch.work_stk2 = s.scratch.work_stk2 := hws2_a
      have hstat_b : FullDeduceStaticEq s.core sb.core :=
        ⟨hstat_a.cv, hstat_a.cl, hstat_a.te, hstat_a.trl, hstat_a.lvl, hstat_a.rsns,
          hstat_a.vals, hstat_a.fuel, hstat_a.dm, hstat_a.lm⟩
      d_hsteps_nogrp
      · have hok2t : ok2 = true := by assumption
        subst ok2
        have h_ok2 := hok2 rfl
        have hne2 : (BitVec.setWidth 32 sa.core.confl_lit1, ()).fst.toNat / 2 ≠
            (4294967295 : BitVec 32).toNat := by
          have h1 := h_ok2.1; have h2 := hl_a.core_ok.cur_vars_le; omega
        have hl1_sa : (BitVec.setWidth 32 sa.core.confl_lit1, ()).fst.toNat =
            s.core.confl_lit1.toNat := by
          dsimp only [sa]; rw [← BitVec.truncate_eq_setWidth]; exact hl1_tr
        have hsb_sem := deduce_seed_lit_step hl_a hw_a hnd_a hrefs_a hext_a hws2_a hstat_a
          htl1_a htc_a_le1 htc_eq_a hlow_a hmcov_a hcm_a hres_a
          (by rw [hstat_a.cv, hl1_sa]; exact hco_w.2.2.1)
          (by rw [hstat_a.vals, hl1_sa]; exact hco_w.2.2.2.2.1)
          (by rw [hstat_a.lvl, hstat_a.cl, hstat_a.trl, hl1_sa]; exact hco_cut.2)
          sb rfl rfl hlen2 hcov2 htl2_cv htl2_ge htl2_le hmp2 htp2 hnm2 hnt2 hres2 htc2_eq
          ⟨h_ok2.1, h_ok2.2 hne2⟩
        obtain ⟨hl_b, hw_b', hcov_b, hext_b', hws2_b', hnd_b', hrefs_b', hstat_b',
          htl1_b, htl_cv_b, htc_eq_b, hlow_b, hmcov_b, hcm_b, _, hl1_res, hres_b⟩ := hsb_sem
        have hl0_sa : (BitVec.setWidth 32 sl.core.confl_lit0, ()).fst.toNat =
            s.core.confl_lit0.toNat := by
          dsimp only; rw [← BitVec.truncate_eq_setWidth]; exact hl0_tr
        have hl1_sb : (BitVec.setWidth 32 sl.core.confl_lit1).toNat =
            s.core.confl_lit1.toNat := by
          rw [← BitVec.truncate_eq_setWidth]; exact hl1_tr
        have hinv_b := deduce_seed_bin_sem (s := s) (sa := sa) (sb := sb)
          hco_w.2.2.2.2.2
          (by simpa only [hl0_sa] using hl0_res)
          (by simpa only [hl1_sb] using hl1_res)
          (fun hmem => ded_mem_activeResolvent_mono hl_a.core_ok hw_a
            (by dsimp only [sb] at hlen2
                rw [hlen2.core_ok.tmp_len_arr]; exact hlen2.core_ok.tmp_len_le)
            htl2_ge htp2 hmp2 hmem)
          hl_b hw_b' hcov_b hext_b' hws2_b' hnd_b' hrefs_b' hstat_b' htl1_b htl_cv_b
          htc_eq_b hlow_b hmcov_b hcm_b hres_b
        exact hJ true ext sb m2 hext_ok hl_b hw_b' hcov_b hnd_b'
          hext_b' hws2_b' hrefs_b' hstat_b' (fun _ => hinv_b) hm2
      · exact hJ false ext sb m2 hext_ok hlen2 hw_b hcov2 hnd_b
          hext_b hws2_b hrefs_b hstat_b (fun h => Bool.noConfusion h) hm2
    · have hw_a : FullWitnessCutInv c F0 F_cur cut sa.core :=
        ded_witnessCut_with_ana hw_l _ _ _ _ _
      have hstat_a : FullDeduceStaticEq s.core sa.core :=
        ⟨hstat_l.cv, hstat_l.cl, hstat_l.te, hstat_l.trl, hstat_l.lvl, hstat_l.rsns,
          hstat_l.vals, hstat_l.fuel, hstat_l.dm, hstat_l.lm⟩
      exact hJ false ext sa m1 hext_ok hlen1 hw_a hcov1
        (ded_arenaVarsNodup_same_core_arena hnd_l rfl rfl) hext_l hws2_l hrefs_l hstat_a
        (fun h => Bool.noConfusion h) hm1
  · have hn1_l : sl.core.confl_type ≠ 1#64 := by assumption
    have hpre_rsn := deduce_seed_rsn_pre hlen_l hw_l (by
      unfold FullConflictOkCut FullConflictOkW at hconfl ⊢
      simpa only [hsl_c, fullArenaClauseRefs, fullArenaClauseRefsCore,
        fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore,
        fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSize,
        fullArenaClauseSizeCore] using hconfl) hn1_l
    obtain ⟨hct2, hbd3, htr_cr, hne_cr, hnb_cr, href_cr, _⟩ := hpre_rsn
    have har_lt64 : sl.core.arena_len < 2 ^ 64 := by
      have := hlen_l.core_ok.arena_len_le
      have : c.arena_cap < 2 * 2 ^ 28 := c.harena
      omega
    have hcr_lt64 : sl.core.confl_ref.toNat + 3 < 2 ^ 64 := by omega
    refine wp_unroll_group fun Js hJs => ?_
    d_hsteps_nogrp
    · refine wp_call_of_spec _ _ (hRsn (c.hdr, BitVec.truncate 32 sl.core.confl_ref,
        0xFFFFFFFF#32, ()) _
        (fun r m' => wp Γ Q X (Expr.jump (ts := [.bool]) Js (Arg.var r.fst, ())) m') X ?_)
      refine ⟨c, F0, F_cur, cut, ext, sl, R, rfl, hcfg, hext_ok, hlen_l, hw_l, hcov_l,
        (by have h := h1_cv_l; rw [hsl_c] at h ⊢; exact h),
        (by have h := hlen_l.core_ok.cur_vars_le; rw [hsl_c] at h ⊢; dsimp only at *; omega),
        (fun _ _ => href_cr), fullM6HdrMem_unfocus_full hmf,
        fun ok mrk' tmp' mclr' tc' tl' mcl' arena' sc' ext' m' hext' _ hlen2 hw2 hcov2
          hext2 hws2_2 htl2_ge htl2_cv htc2_ge hrefs2 hcl2 hmp htp hnm hnt hnd_j hcnt hres2
          hok_lits hm2 => ?_⟩
      let s2 : FullState :=
        { core := { sl.core with tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl',
                                 mrk := mrk', tmp := tmp', min_clr := mclr', arena := arena' }
          scratch := sc' }
      have hnd2 : FullArenaVarsNodup s2 := ded_arenaVarsNodup_of_pres hnd_l hrefs2
        (fun r hr => ⟨(hcl2 r hr).2.1, (hcl2 r hr).2.2⟩)
      have hext_s2 : FullExtScratchPres s s2 := ⟨hext2.1.trans hext_l.1, hext2.2.trans hext_l.2⟩
      have hws2_s2 : s2.scratch.work_stk2 = s.scratch.work_stk2 := hws2_2.trans hws2_l
      have hrefs_s2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s := hrefs2.trans hrefs_l
      have hstat_s2 : FullDeduceStaticEq s.core s2.core :=
        ⟨hstat_l.cv, hstat_l.cl, hstat_l.te, hstat_l.trl, hstat_l.lvl, hstat_l.rsns,
          hstat_l.vals, hstat_l.fuel, hstat_l.dm, hstat_l.lm⟩
      d_hsteps_nogrp
      exact hJ ok ext' s2 m' hext' hlen2 hw2 hcov2 hnd2 hext_s2 hws2_s2
        hrefs_s2 hstat_s2 (fun hokt => by
          have hok_lits' := hok_lits hokt
          exact deduce_seed_rsn_sem hcut0 hconfl hsl_c hsl_sc hlen_l rfl hlen2 hw2 hcov2
            hext2 hws2_2 (by rw [hsl_c] at htl2_ge; exact htl2_ge) htl2_cv
            (by rw [hsl_c] at htc2_ge; exact htc2_ge) hrefs2 hcl2 hmp
            (by simpa only [hsl_c] using htp) hnm
            (by simpa only [hsl_c] using hnt)
            (by simpa only [hsl_c] using hnd_j)
            (by simpa only [hsl_c] using hcnt)
            hres2 (by simpa only [hsl_c] using hok_lits'.2.2) hn1_l) hm2
    · exfalso
      have hule : ¬(sl.core.confl_ref.toNat + (3 : BitVec 64).toNat) % 2 ^ 64 ≤
          sl.core.arena_len % 2 ^ 64 := by assumption
      rw [show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt hcr_lt64,
        Nat.mod_eq_of_lt har_lt64] at hule
      exact hule hbd3

end LeanQbe.T.Examples.Kissat.Proof.Deduce
