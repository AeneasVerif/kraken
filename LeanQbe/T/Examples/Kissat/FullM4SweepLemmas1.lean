module

public import LeanQbe.T.Examples.Kissat.FullM4SweepKitten4
public import LeanQbe.T.Examples.Kissat.FullSweepFwdLemmas1
public import LeanQbe.T.Examples.Kissat.FullSweepVarLemmas1

/-!
# Kissat `D-Full` M4b — Sweeping Scoped Tactics, Helpers, & `6/12` `Func.wp` Proofs (`Part 1`)

1. Strictly scoped `M4SweepTactics` (`@[scoped c0_load]`/`@[scoped c0_store]`/`@[scoped bv_c0]`)
   for `FullMem`-level accesses into `scratch_buf + K512_BASE` (`2304`), `tmp[0]`,
     and `work_stk1[0]`.
2. Pure `K512ScratchInv`, `ConeModelSet`, `PhtOk`, and `FullDenseInvW` preservation & entailment
   helpers shared across `FullM4SweepCone` and `FullM4SweepLemmas2`.
3. Parametric `(Γ : Env)` `Func.wp` proofs for `6/24` functions (`13..18/24`):
   - `full_m4_sweep_refine_sig_wp`
   - `full_m4_sweep_rand_phases_wp`
   - `full_m4_sweep_flip_round_wp`
   - `full_m4_sweep_rearm_wp`
   - `full_m4_sweep_build_pht_wp`
   - `full_m4_sweep_sim_wp`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullArenaTactics FullSweepFwdHelpers FullSweepVarHelpers

abbrev M4EnvSpec (Γ : Env) (name : Sym) {as rs : List Ty} (S : Spec as rs) : Prop :=
  ∀ xs m Q X, S xs m Q X → Γ name as rs xs m Q X

/-! ## 1. Strictly Scoped `FullMem` + `K512_BASE` Tactics (`M4SweepTactics`) -/

theorem m4_ptr_k_2304_eq (p i : BitVec 64) :
    (p + BitVec.ofNat 64 2304 * 4) + i * 4 = p + BitVec.ofNat 64 (4 * (2304 + i.toNat)) := by
  have hmul : i * 4 = BitVec.ofNat 64 (i.toNat * 4) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]
  rw [BitVec.add_assoc]; congr 1
  rw [hmul, show (BitVec.ofNat 64 2304 * 4 : BitVec 64) = BitVec.ofNat 64 9216 from rfl,
    ← BitVec.ofNat_add, show 9216 + i.toNat * 4 = 4 * (2304 + i.toNat) by omega]

theorem m4_ptr_k_9216_eq (p i : BitVec 64) :
    (p + 9216#64) + i * 4 = p + BitVec.ofNat 64 (4 * (2304 + i.toNat)) := by
  simpa [k5Ptr_base_eq] using m4_ptr_k_2304_eq p i

namespace M4SweepTactics

open FullArenaTactics
open scoped FullArenaTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64
attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

@[scoped bv_c0] theorem m4_fullState_core (k : FullCoreState) (sc : FullScratch) :
    ({ core := k, scratch := sc } : FullState).core = k := rfl

@[scoped bv_c0] theorem m4_fullState_scratch (k : FullCoreState) (sc : FullScratch) :
    ({ core := k, scratch := sc } : FullState).scratch = sc := rfl

@[scoped bv_c0] theorem m4_bv64_and_1023 (x : BitVec 64) :
    (x &&& BitVec.ofNat 64 1023).toNat = x.toNat % 1024 := by
  rw [BitVec.toNat_and, show (BitVec.ofNat 64 1023).toNat = 1023 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 10

@[scoped bv_c0] theorem m4_bv64_shl1_nat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m4_bv32_shl1_nat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m4_bv32_shl1_mod32 (x : BitVec 32) :
    x <<< ((1#32 : BitVec 32).toNat % 32) = x <<< (1 : Nat) := rfl

@[scoped c0_load] theorem load_k5_2304_dyn {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : 2304 + i.toNat < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 2304 * 4 + i * 4) =
      some s.scratch.scratch_buf[2304 + i.toNat] := by
  rw [m4_ptr_k_2304_eq]; exact load_full_scratch_buf hi hm

@[scoped c0_store] theorem store_k5_2304_dyn {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : 2304 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 2304 * 4 + i * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (2304 + i.toNat) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 2304 * 4 + i * 4) v) := by
  rw [m4_ptr_k_2304_eq]; exact store_full_scratch_buf v hi hm

@[scoped c0_load] theorem load_k5_9216_dyn {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : 2304 + i.toNat < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + 9216#64) + i * 4) =
      some s.scratch.scratch_buf[2304 + i.toNat] := by
  rw [m4_ptr_k_9216_eq]; exact load_full_scratch_buf hi hm

@[scoped c0_store] theorem store_k5_9216_dyn {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : 2304 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + 9216#64) + i * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (2304 + i.toNat) v } } ⋆ R)
        (storeMem m i32 ((c.pScratchBuf + 9216#64) + i * 4) v) := by
  rw [m4_ptr_k_9216_eq]; exact store_full_scratch_buf v hi hm

@[scoped c0_load] theorem load_m4_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pTmp = some s.core.tmp[0] := by
  simpa using load_full_tmp (i := 0) hi hm

@[scoped c0_store] theorem store_m4_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTmp ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 c.pTmp v) := by
  simpa using store_full_tmp (i := 0) v hi hm

@[scoped c0_load] theorem load_m4_ws1_0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pWorkStk1 = some s.scratch.work_stk1[0] := by
  simpa using load_full_work_stk1 (i := 0) hi hm

@[scoped c0_store] theorem store_m4_ws1_0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk1 ∧
      (FullMem c { s with scratch := { s.scratch with
        work_stk1 := s.scratch.work_stk1.set 0 v } } ⋆ R)
        (storeMem m i32 c.pWorkStk1 v) := by
  simpa using store_full_work_stk1 (i := 0) v hi hm

theorem m4_strip_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem m4_strip_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem m4_strip_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "m4_strip" : tactic =>
  `(tactic| first | apply m4_strip_32_64 | apply m4_strip_8_32 | apply m4_strip_8_64)

scoped macro "m4_steps" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_hsteps!))

scoped macro "m4_steps_soft" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_hsteps))

scoped macro "m4_split" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_hsplit))

scoped macro "m4_to_group" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_hsteps_nogrp))

scoped macro "m4_csteps!" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_steps!))

scoped macro "m4_call " h:ident : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

end M4SweepTactics

open scoped FullArenaTactics M4SweepTactics

/-! ## 2. Pure `K512ScratchInv`, `ConeModelSet`, `PhtOk`, & `FullDenseInvW` Helpers -/

theorem m4_bv32_add1 {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega

theorem m4_bv64_add1 {x : BitVec 64} (h : x.toNat < 2 ^ 63) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

theorem m4_list_drop_set_lt {α : Type _} (xs : List α) {k i : Nat} (v : α) (hik : i < k) :
    (xs.set i v).drop k = xs.drop k := by
  apply List.ext_getElem
  · simp
  · intro j hj1 _
    simp only [List.getElem_drop]
    rw [List.getElem_set_ne (by omega)]

theorem m4_list_drop_set_ge {α : Type _} (xs : List α) {k i : Nat} (v : α) (hki : k ≤ i) :
    (xs.set i v).drop k = (xs.drop k).set (i - k) v := by
  apply List.ext_getElem
  · simp
  · intro j hj1 _
    simp only [List.getElem_drop]
    by_cases hji : j = i - k
    · subst hji
      have hsum : k + (i - k) = i := by omega
      simp only [hsum, List.getElem_set_self]
    · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hji), List.getElem_drop]

theorem m4_list_take_set_ge {α : Type _} (xs : List α) {n i : Nat} (v : α) (hni : n ≤ i) :
    (xs.set i v).take n = xs.take n := by
  apply List.ext_getElem
  · simp
  · intro j hj1 _
    have hj : j < n := by simp at hj1; omega
    simp only [List.getElem_take]
    rw [List.getElem_set_ne (by omega)]

theorem m4_list_take_set_lt {α : Type _} (xs : List α) {n i : Nat} (v : α) (hin : i < n) :
    (xs.set i v).take n = (xs.take n).set i v := by
  apply List.ext_getElem
  · simp
  · intro j hj1 _
    have hj : j < n ∧ j < xs.length := by simp at hj1; omega
    simp only [List.getElem_take]
    by_cases hji : j = i
    · subst hji; simp only [List.getElem_set_self]
    · rw [List.getElem_set_ne (Ne.symm hji), List.getElem_set_ne (Ne.symm hji), List.getElem_take]

theorem k5StateOfScratch_set_lt {scr : List (BitVec 32)} {j : Nat} (v : BitVec 32)
    (hj : j < k5Base) :
    k5StateOfScratch (scr.set j v) = k5StateOfScratch scr := by
  unfold k5StateOfScratch
  rw [m4_list_drop_set_lt scr v hj]

theorem k5ScratchInv_set_lt {P : (Nat → Bool) → Prop} {scr : List (BitVec 32)} {j : Nat}
    (v : BitVec 32) (hj : j < k5Base) (h : K512ScratchInv P scr) :
    K512ScratchInv P (scr.set j v) := by
  obtain ⟨hmin, hlt, hinv⟩ := h
  refine ⟨by simp [hmin], by simp [hlt], ?_⟩
  rw [List.length_set, k5StateOfScratch_set_lt v hj]
  exact hinv

theorem k5ScratchInv_mono_P {P P' : (Nat → Bool) → Prop} {scr : List (BitVec 32)}
    (himp : ∀ β, P' β → P β) (h : K512ScratchInv P scr) : K512ScratchInv P' scr :=
  ⟨h.1, h.2.1, h.2.2.mono_P himp⟩

theorem k5StateOfScratch_set_nassump {scr : List (BitVec 32)} (v : BitVec 32)
    (hlen : k5MinScr ≤ scr.length) :
    k5StateOfScratch (scr.set (k5Base + 15) v) =
      (k5StateOfScratch scr).putHdr .nassump v := by
  unfold k5StateOfScratch
  rw [m4_list_drop_set_ge scr v (by unfold k5Base; omega),
    show k5Base + 15 - k5Base = 15 from rfl]
  have hdl : 19488 ≤ (scr.drop k5Base).length := by
    simp only [List.length_drop]; unfold k5MinScr at hlen; unfold k5Base; omega
  generalize scr.drop k5Base = xs at hdl ⊢
  apply k5State_ext
  all_goals (
    dsimp only [K512State.ofSlab, K512State.putHdr]
    try (rw [List.getElem?_set]; split <;> first | rfl | omega | (split <;> first | rfl | omega))
    try (rw [m4_list_drop_set_lt xs v (by decide)]))

theorem k5StateOfScratch_set_phase {scr : List (BitVec 32)} (v : BitVec 32)
    (hlen : k5MinScr ≤ scr.length) :
    k5StateOfScratch (scr.set (k5Base + 19) v) =
      (k5StateOfScratch scr).putHdr .phase v := by
  unfold k5StateOfScratch
  rw [m4_list_drop_set_ge scr v (by unfold k5Base; omega),
    show k5Base + 19 - k5Base = 19 from rfl]
  have hdl : 19488 ≤ (scr.drop k5Base).length := by
    simp only [List.length_drop]; unfold k5MinScr at hlen; unfold k5Base; omega
  generalize scr.drop k5Base = xs at hdl ⊢
  apply k5State_ext
  all_goals (
    dsimp only [K512State.ofSlab, K512State.putHdr]
    try (rw [List.getElem?_set]; split <;> first | rfl | omega | (split <;> first | rfl | omega))
    try (rw [m4_list_drop_set_lt xs v (by decide)]))

theorem k5StateOfScratch_set_flags {scr : List (BitVec 32)} {i : Nat} (v : BitVec 32)
    (hi : i < 512) (hlen : k5MinScr ≤ scr.length) :
    k5StateOfScratch (scr.set (k5Base + 3104 + i) v) =
      (k5StateOfScratch scr).putArr .flags i v := by
  unfold k5StateOfScratch
  rw [m4_list_drop_set_ge scr v (by unfold k5Base; omega),
    show k5Base + 3104 + i - k5Base = 3104 + i by omega]
  have hdl : 19488 ≤ (scr.drop k5Base).length := by
    simp only [List.length_drop]; unfold k5MinScr at hlen; unfold k5Base; omega
  generalize scr.drop k5Base = xs at hdl ⊢
  apply k5State_ext
  all_goals (
    dsimp only [K512State.ofSlab, K512State.putArr]
    try (rw [List.getElem?_set]; split <;> first | rfl | omega | (split <;> first | rfl | omega))
    try (rw [m4_list_drop_set_lt xs v (by omega)])
    try (rw [m4_list_drop_set_ge xs v (by omega), m4_list_take_set_ge _ v (by omega)])
    try (rw [m4_list_drop_set_ge xs v (by omega), show 3104 + i - 3104 = i by omega,
      m4_list_take_set_lt _ v hi]))

theorem k5StateOfScratch_set_assump {scr : List (BitVec 32)} {i : Nat} (v : BitVec 32)
    (hi : i < 512) (hlen : k5MinScr ≤ scr.length) :
    k5StateOfScratch (scr.set (k5Base + 4640 + i) v) =
      (k5StateOfScratch scr).putArr .assump i v := by
  unfold k5StateOfScratch
  rw [m4_list_drop_set_ge scr v (by unfold k5Base; omega),
    show k5Base + 4640 + i - k5Base = 4640 + i by omega]
  have hdl : 19488 ≤ (scr.drop k5Base).length := by
    simp only [List.length_drop]; unfold k5MinScr at hlen; unfold k5Base; omega
  generalize scr.drop k5Base = xs at hdl ⊢
  apply k5State_ext
  all_goals (
    dsimp only [K512State.ofSlab, K512State.putArr]
    try (rw [List.getElem?_set]; split <;> first | rfl | omega | (split <;> first | rfl | omega))
    try (rw [m4_list_drop_set_lt xs v (by omega)])
    try (rw [m4_list_drop_set_ge xs v (by omega), m4_list_take_set_ge _ v (by omega)])
    try (rw [m4_list_drop_set_ge xs v (by omega), show 4640 + i - 4640 = i by omega,
      m4_list_take_set_lt _ v hi]))

theorem k5ScratchInv_set_phase {P : (Nat → Bool) → Prop} {scr : List (BitVec 32)} (v : BitVec 32)
    (h : K512ScratchInv P scr) :
    K512ScratchInv P (scr.set (k5Base + 19) v) ∧
    (k5StateOfScratch (scr.set (k5Base + 19) v)).nv = (k5StateOfScratch scr).nv := by
  obtain ⟨hmin, hlt, hinv⟩ := h
  have hst := k5StateOfScratch_set_phase v hmin
  refine ⟨⟨by simp [hmin], by simp [hlt], ?_⟩, by rw [hst]; rfl⟩
  rw [List.length_set, hst]
  exact ⟨hinv.shapes.putHdr .phase v,
    ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, hinv.clauses.acap_eq, hinv.clauses.nv_le,
     hinv.clauses.nc_le, hinv.clauses.alen_le, hinv.clauses.nassump_le, hinv.clauses.nkl_le,
     hinv.clauses.nana_le, hinv.clauses.cl_wf, hinv.clauses.cl_mono, hinv.clauses.incons_ok,
     hinv.clauses.assump_ok, hinv.clauses.flags_clean⟩,
    hinv.watches, k5a_baseAssign_of_eq hinv.assign, hinv.reasons⟩

theorem k5ScratchInv_set_flags_bit0 {P : (Nat → Bool) → Prop} {scr : List (BitVec 32)}
    {i : Nat} (hi : i < 512) (b : BitVec 32) (h : K512ScratchInv P scr) :
    let fl := scr[k5Base + 3104 + i]?.getD 0#32
    let v := (fl &&& ~~~1#32) ||| (b &&& 1#32)
    K512ScratchInv P (scr.set (k5Base + 3104 + i) v) ∧
    (k5StateOfScratch (scr.set (k5Base + 3104 + i) v)).nv = (k5StateOfScratch scr).nv := by
  intro fl v
  obtain ⟨hmin, hlt, hinv⟩ := h
  have hst := k5StateOfScratch_set_flags v hi hmin
  have hfl_eq : (k5StateOfScratch scr).flags[i]?.getD 0#32 = fl := by
    dsimp only [fl, k5StateOfScratch, K512State.ofSlab]
    rw [List.getElem?_take_of_lt hi, List.getElem?_drop, List.getElem?_drop]
    congr 2; omega
  have hbit2 : (v &&& 2#32) = (fl &&& 2#32) := by
    dsimp only [v]; apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hk, decide_true,
      Bool.true_and]
    cases k with
    | zero => simp
    | succ k => cases k with | zero => simp | succ _ => simp
  refine ⟨⟨by simp [hmin], by simp [hlt], ?_⟩, by rw [hst]; rfl⟩
  rw [List.length_set, hst]
  refine ⟨hinv.shapes.putArr .flags i v,
    ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, hinv.clauses.acap_eq, hinv.clauses.nv_le,
     hinv.clauses.nc_le, hinv.clauses.alen_le, hinv.clauses.nassump_le, hinv.clauses.nkl_le,
     hinv.clauses.nana_le, hinv.clauses.cl_wf, hinv.clauses.cl_mono, hinv.clauses.incons_ok,
     hinv.clauses.assump_ok, ?_⟩,
    hinv.watches, k5a_baseAssign_of_eq hinv.assign, hinv.reasons⟩
  intro w hw
  dsimp only [K512State.putArr]
  by_cases hwi : w = i
  · subst hwi
    rw [List.getElem?_set_self (by rw [hinv.shapes.flags_len]; exact hi), Option.getD_some,
      hbit2, ← hfl_eq]
    exact hinv.clauses.flags_clean w hw
  · rw [List.getElem?_set_ne (Ne.symm hwi)]
    exact hinv.clauses.flags_clean w hw

theorem k5ScratchInv_set_nassump0 {P : (Nat → Bool) → Prop} {scr : List (BitVec 32)}
    (h : K512ScratchInv P scr) :
    let scr' := scr.set (k5Base + 15) 0#32
    K512ScratchInv P scr' ∧
    (k5StateOfScratch scr').nv = (k5StateOfScratch scr).nv ∧
    k5AssumpLitsS scr' = [] := by
  intro scr'
  obtain ⟨hmin, hlt, hinv⟩ := h
  have hst := k5StateOfScratch_set_nassump 0#32 hmin
  refine ⟨⟨by simp [scr', hmin], by simp [scr', hlt], ?_⟩, by rw [hst]; rfl, ?_⟩
  · rw [show scr'.length = scr.length from List.length_set, hst]
    exact ⟨hinv.shapes.putHdr .nassump 0#32,
      ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, hinv.clauses.acap_eq, hinv.clauses.nv_le,
       hinv.clauses.nc_le, hinv.clauses.alen_le, by simp [K512State.putHdr], hinv.clauses.nkl_le,
       hinv.clauses.nana_le, hinv.clauses.cl_wf, hinv.clauses.cl_mono, hinv.clauses.incons_ok,
       fun i hi => by simp [K512State.putHdr] at hi, hinv.clauses.flags_clean⟩,
      hinv.watches, k5a_baseAssign_of_eq hinv.assign, hinv.reasons⟩
  · unfold k5AssumpLitsS k5AssumpLits; dsimp only [scr']; rw [hst]; simp [K512State.putHdr]

theorem k5ScratchInv_set_assump1 {P : (Nat → Bool) → Prop} {scr : List (BitVec 32)}
    {a0 : BitVec 32} (ha0 : a0.toNat < 2 * (k5StateOfScratch scr).nv.toNat)
    (h : K512ScratchInv P scr) :
    let scr' := (scr.set (k5Base + 15) 1#32).set (k5Base + 4640) a0
    K512ScratchInv P scr' ∧
    (k5StateOfScratch scr').nv = (k5StateOfScratch scr).nv ∧
    k5AssumpLitsS scr' = [a0.toNat] := by
  intro scr'
  obtain ⟨hmin, hlt, hinv⟩ := h
  have hst1 := k5StateOfScratch_set_nassump 1#32 hmin
  have hst2 := k5StateOfScratch_set_assump (scr := scr.set (k5Base + 15) 1#32)
    (i := 0) a0 (by decide) (by simp [hmin])
  have hst :
      k5StateOfScratch scr' = ((k5StateOfScratch scr).putHdr .nassump 1#32).putArr .assump 0 a0 :=
        by
    simpa [scr', hst1] using hst2
  have hass_len : (k5StateOfScratch scr).assump.length = 512 := hinv.shapes.assump_len
  refine ⟨⟨by simp [scr', hmin], by simp [scr', hlt], ?_⟩, by rw [hst]; rfl, ?_⟩
  · rw [show scr'.length = scr.length by simp [scr'], hst]
    refine ⟨(hinv.shapes.putHdr .nassump 1#32).putArr .assump 0 a0,
      ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, hinv.clauses.acap_eq, hinv.clauses.nv_le,
       hinv.clauses.nc_le, hinv.clauses.alen_le,
       by simp [K512State.putArr, K512State.putHdr, k5MaxV],
       hinv.clauses.nkl_le, hinv.clauses.nana_le, hinv.clauses.cl_wf, hinv.clauses.cl_mono,
       hinv.clauses.incons_ok, ?_, hinv.clauses.flags_clean⟩,
      hinv.watches, k5a_baseAssign_of_eq hinv.assign, hinv.reasons⟩
    intro i hi
    simp only [K512State.putArr, K512State.putHdr] at hi ⊢
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    rw [List.getElem?_set_self (by omega), Option.getD_some]; exact ha0
  · unfold k5AssumpLitsS k5AssumpLits
    rw [hst]
    simp only [K512State.putArr, K512State.putHdr, show (1#32).toNat = 1 from rfl]
    cases h_as : (k5StateOfScratch scr).assump with
    | nil => simp [h_as] at hass_len
    | cons x xs => simp

theorem k5ScratchInv_set_assump2 {P : (Nat → Bool) → Prop} {scr : List (BitVec 32)}
    {a0 a1 : BitVec 32}
    (ha0 : a0.toNat < 2 * (k5StateOfScratch scr).nv.toNat)
    (ha1 : a1.toNat < 2 * (k5StateOfScratch scr).nv.toNat)
    (h : K512ScratchInv P scr) :
    let scr' := ((scr.set (k5Base + 15) 2#32).set (k5Base + 4640) a0).set (k5Base + 4641) a1
    K512ScratchInv P scr' ∧
    (k5StateOfScratch scr').nv = (k5StateOfScratch scr).nv ∧
    k5AssumpLitsS scr' = [a0.toNat, a1.toNat] := by
  intro scr'
  obtain ⟨hmin, hlt, hinv⟩ := h
  have hst1 := k5StateOfScratch_set_nassump 2#32 hmin
  have hst2 := k5StateOfScratch_set_assump (scr := scr.set (k5Base + 15) 2#32)
    (i := 0) a0 (by decide) (by simp [hmin])
  have hst3 := k5StateOfScratch_set_assump
    (scr := (scr.set (k5Base + 15) 2#32).set (k5Base + 4640) a0)
    (i := 1) a1 (by decide) (by simp [hmin])
  have hst : k5StateOfScratch scr' =
      (((k5StateOfScratch scr).putHdr .nassump 2#32).putArr .assump 0 a0).putArr .assump 1 a1 := by
    simpa [scr', hst1, hst2] using hst3
  have hass_len : (k5StateOfScratch scr).assump.length = 512 := hinv.shapes.assump_len
  refine ⟨⟨by simp [scr', hmin], by simp [scr', hlt], ?_⟩, by rw [hst]; rfl, ?_⟩
  · rw [show scr'.length = scr.length by simp [scr'], hst]
    refine ⟨((hinv.shapes.putHdr .nassump 2#32).putArr .assump 0 a0).putArr .assump 1 a1,
      ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, hinv.clauses.acap_eq, hinv.clauses.nv_le,
       hinv.clauses.nc_le, hinv.clauses.alen_le,
       by simp [K512State.putArr, K512State.putHdr, k5MaxV],
       hinv.clauses.nkl_le, hinv.clauses.nana_le, hinv.clauses.cl_wf, hinv.clauses.cl_mono,
       hinv.clauses.incons_ok, ?_, hinv.clauses.flags_clean⟩,
      hinv.watches, k5a_baseAssign_of_eq hinv.assign, hinv.reasons⟩
    intro i hi
    simp only [K512State.putArr, K512State.putHdr] at hi ⊢
    have hi2 : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases hi2 with rfl | rfl
    · rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega), Option.getD_some]
      exact ha0
    · rw [List.getElem?_set_self (by simp [hass_len]), Option.getD_some]; exact ha1
  · unfold k5AssumpLitsS k5AssumpLits
    rw [hst]
    simp only [K512State.putArr, K512State.putHdr, show (2#32).toNat = 2 from rfl]
    cases h_as : (k5StateOfScratch scr).assump with
    | nil => simp [h_as] at hass_len
    | cons x xs =>
      cases xs with
      | nil => simp [h_as] at hass_len
      | cons y ys => simp

theorem coneModelSet_push_var {F_cur : List (List Nat)} {ws1 : List (BitVec 32)} {nv : Nat}
    {ov : BitVec 32} (β : Nat → Bool)
    (h : ConeModelSet F_cur (ws1.set nv ov) (nv + 1) β) :
    ConeModelSet F_cur ws1 nv β := by
  obtain ⟨α, hα, hβ⟩ := h
  refine ⟨α, hα, fun i hi => ?_⟩
  have h1 := hβ i (by omega)
  rwa [List.getElem?_set_ne (by omega : nv ≠ i)] at h1

theorem coneModelSet_unsat_of_empty {F_cur : List (List Nat)} {ws1 : List (BitVec 32)} {nv : Nat}
    (h : ∀ β, ¬ ConeModelSet F_cur ws1 nv β) : (cnfOfClauses F_cur).Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  exact h (fun i => α (ws1[i]?.getD 0#32).toNat) ⟨α, hα, fun _ _ => rfl⟩

theorem coneModelSet_unsat_unit {F_cur : List (List Nat)} {ws1 : List (BitVec 32)} {nv a : Nat}
    (ha : a < 2 * nv)
    (h : ∀ β, ConeModelSet F_cur ws1 nv β → ¬ (unitsCnf [a]).Sat β) :
    SemEntails (ConeModelSet F_cur ws1 nv) [a ^^^ 1] ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [FullSweepFwdSpecs.coneLift ws1 (a ^^^ 1)]) := by
  have hsem : SemEntails (ConeModelSet F_cur ws1 nv) [a ^^^ 1] := fun β hβ => by
    rw [k5_litNeg_eq_xor1, sat_cnfClause_litNeg_iff]
    intro hsat
    exact h β hβ ((sat_unitsCnf_iff β [a]).mpr fun l hl => by
      simp only [List.mem_singleton] at hl; subst hl; exact hsat)
  refine ⟨hsem, ?_⟩
  rw [CNF.entails_clause_def]; intro α hα
  have hsat := hsem (fun i => α (ws1[i]?.getD 0#32).toNat) ⟨α, hα, fun _ _ => rfl⟩
  have hlift := (coneLift_sat_iff (α := α) (cone_v := ws1) (l := a ^^^ 1)).mp hsat
  exact hlift

theorem coneModelSet_unsat_bin {F_cur : List (List Nat)} {ws1 : List (BitVec 32)}
    {nv a0 a1 : Nat} (ha0 : a0 < 2 * nv) (ha1 : a1 < 2 * nv)
    (h : ∀ β, ConeModelSet F_cur ws1 nv β → ¬ (unitsCnf [a0, a1]).Sat β) :
    SemEntails (ConeModelSet F_cur ws1 nv) [a0 ^^^ 1, a1 ^^^ 1] ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      [FullSweepFwdSpecs.coneLift ws1 (a0 ^^^ 1),
       FullSweepFwdSpecs.coneLift ws1 (a1 ^^^ 1)]) := by
  have hsem : SemEntails (ConeModelSet F_cur ws1 nv) [a0 ^^^ 1, a1 ^^^ 1] := fun β hβ => by
    exact Classical.byContradiction fun hnot => by
      have h0 : (cnfClause [a0]).Sat β := Classical.byContradiction fun hn0 =>
        hnot ((clause_sat_cnfClause_iff β [a0 ^^^ 1, a1 ^^^ 1]).mpr ⟨a0 ^^^ 1,
          List.mem_cons_self .., (sat_cnfClause_singleton β (a0 ^^^ 1)).mp
            ((sat_cnfClause_litNeg_iff β a0).mpr hn0)⟩)
      have h1 : (cnfClause [a1]).Sat β := Classical.byContradiction fun hn1 =>
        hnot ((clause_sat_cnfClause_iff β [a0 ^^^ 1, a1 ^^^ 1]).mpr ⟨a1 ^^^ 1,
          List.mem_cons_of_mem _ (List.mem_cons_self ..),
          (sat_cnfClause_singleton β (a1 ^^^ 1)).mp ((sat_cnfClause_litNeg_iff β a1).mpr hn1)⟩)
      exact h β hβ ((sat_unitsCnf_iff β [a0, a1]).mpr fun l hl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact h0
        · exact h1)
  refine ⟨hsem, ?_⟩
  rw [CNF.entails_clause_def]; intro α hα
  have hsat := hsem (fun i => α (ws1[i]?.getD 0#32).toNat) ⟨α, hα, fun _ _ => rfl⟩
  have hlift := (coneLift_clause_sat_iff (α := α) (cone_v := ws1)
    (cl := [a0 ^^^ 1, a1 ^^^ 1])).mp hsat
  simpa using hlift

theorem m4_fullDenseInvW_with_fuel_rng_sig_scr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fuel' rng' : BitVec 64} {sig' : List (BitVec 64)} {scr' : List (BitVec 32)}
    (hsig : sig'.length = c.max_vars) (hscr : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with fuel := fuel' }
        scratch := { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } } :=
  fullDenseInvW_with_fuel_scratch h
    { h.1.scratch_ok with sim_sig_len := hsig, scratch_buf_len := hscr } rfl rfl

theorem m4_fullDenseInvW_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {flags' : List (BitVec 32)}
    (hfl : flags'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with flags := flags' } } := by
  refine ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩, ?_,
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  exact fullWitnessInv_with_tmp_flags_fuel h.2.1 s.core.tmp flags' s.core.fuel

/-! ## 3. `full_m4_sweep_refine_sig_wp` (`13/24`) -/

theorem full_m4_sweep_refine_sig_wp (Γ : Env) :
    ∀ args m Q X, m4SweepRefineSigSpec args m Q X →
      Func.wp Γ full_m4_sweep_refine_sig_body args m Q X := by
  rintro ⟨h, nv, bit_idx, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcap, hnv512, hnv_mx, hcone, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hws_len := hlen.scratch_ok.work_stk1_len
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  unfold Func.wp full_m4_sweep_refine_sig_body
  m4_steps
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) ml => i.toNat ≤ nv.toNat ∧ ∃ sig : List (BitVec 64),
      sig.length = c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig } } ⋆ R) ml)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun _ hJ => by
      m4_steps
      exact hJ (0#32, ()) m ⟨Nat.zero_le _, s.scratch.sim_sig, hlen.scratch_ok.sim_sig_len, hm⟩)
    (fun _ (i, ()) ml ⟨hi_le, sig, hsig_len, hml⟩ hJ => by
      m4_split
      · have hi_lt : i.toNat < nv.toNat := by bv_omega
        generalize hst_eq :
          ({ s with scratch := { s.scratch with sim_sig := sig } } : FullState) = st at hml
        have hwk_st : st.scratch.work_stk1.length = 2 * c.max_vars := by
          rw [← hst_eq]; exact hws_len
        have hscr_st : st.scratch.scratch_buf.length = c.scratch_cap := by
          rw [← hst_eq]; exact hscr_len
        have hsig_st : st.scratch.sim_sig.length = c.max_vars := by rw [← hst_eq]; exact hsig_len
        have hi_ws : (BitVec.setWidth 64 i).toNat < st.scratch.work_stk1.length := by
          rw [hwk_st, bv_c0_zext32_64]; omega
        have hgv_lt : (st.scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws).toNat <
            c.max_vars := by
          have hg := hcone i.toNat hi_lt
          have hws_s : st.scratch.work_stk1 = s.scratch.work_stk1 := by rw [← hst_eq]
          rw [List.getElem?_eq_getElem (by rw [hws_len]; omega), Option.getD_some] at hg
          have hi64 : (BitVec.setWidth 64 i).toNat = i.toNat := bv_c0_zext32_64 i
          simp only [hws_s, hi64]; exact Nat.lt_of_lt_of_le hg hcv_le
        have hgv_sig : (BitVec.setWidth 64 (st.scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'
            hi_ws)).toNat < st.scratch.sim_sig.length := by
          rw [hsig_st, bv_c0_zext32_64]; exact hgv_lt
        have hk_bd : 2304 + ((5152 + (i <<< (1 : Nat))).setWidth 64).toNat <
            st.scratch.scratch_buf.length := by
          rw [hscr_st, bv_c0_zext32_64]
          have hshl : (i <<< (1 : Nat)).toNat = 2 * i.toNat := by
            unfold k5MaxV at hnv512; bv_omega
          have hadd : (5152 + (i <<< (1 : Nat))).toNat = 5152 + 2 * i.toNat := by
            unfold k5MaxV at hnv512
            rw [BitVec.toNat_add, show (5152 : BitVec 32).toNat = 5152 from rfl, hshl,
              Nat.mod_eq_of_lt (by omega)]
          rw [hadd]; unfold k5MinScr at hcap; unfold k5MaxV at hnv512; omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
          m4_bv32_add1 (by unfold k5MaxV at hnv512; omega)
        m4_to_group; refine wp_unroll_group fun _ _ => ?_; m4_split
        all_goals
          m4_csteps!; subst hst_eq
          refine hJ (i + 1#32, ()) _ (by dsimp only; omega) ⟨by omega, _, ?_, by assumption⟩
          simp [hsig_len]
      · m4_steps; exact hQ sig ml hsig_len hml)

/-! ## 4. `full_m4_sweep_rand_phases_wp` (`14/24`) -/

private theorem m4_call_rng_next {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hRng : M4EnvSpec Γ "full_rng_next" fullRngNextSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (r rng' : BitVec 64) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with rng_state := rng' } }
      s'.LengthsOk c → (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i64]) "full_rng_next" (Arg.var c.hdr, ()) k) m := by
  refine wp_call_of_spec _ k ?_
  refine hRng (c.hdr, ()) m (fun r m' => wp Γ Q X (k r) m') X ⟨c, s, R, rfl, hlen, hm, ?_⟩
  rintro ⟨r, ⟨⟩⟩ st_r mr hcore_r hlen_r hscr_r hmr
  dsimp only [fullSafetySlice] at hcore_r hlen_r hmr
  generalize st_r.scratch.rng_state = rng' at hscr_r
  have hst_eq : ({ s with scratch :=
    { s.scratch with rng_state := rng' } } : FullState) = st_r := by
    cases st_r; exact congr (congrArg FullState.mk hcore_r.symm) hscr_r.symm
  exact hk r rng' mr (hst_eq ▸ hlen_r) (hst_eq ▸ hmr)

theorem full_m4_sweep_rand_phases_wp (Γ : Env)
    (hRng : M4EnvSpec Γ "full_rng_next" fullRngNextSpec) :
    ∀ args m Q X, m4SweepRandPhasesSpec args m Q X →
      Func.wp Γ full_m4_sweep_rand_phases_body args m Q X := by
  rintro ⟨h, nv, ⟨⟩⟩ m Q X ⟨c, s, P, R, rfl, hlen, hK0, hnv_eq, hm, hQ⟩
  have hcap : k5MinScr ≤ c.scratch_cap := hlen.scratch_ok.scratch_buf_len ▸ hK0.1
  have hnv512 : nv.toNat ≤ 512 := by
    have := hK0.2.2.clauses.nv_le; rw [hnv_eq] at this; exact this
  unfold Func.wp full_m4_sweep_rand_phases_body
  m4_steps
  refine m4_call_rng_next hRng hlen hm fun r0 rng0 m0 hlen0 hm0 => ?_
  m4_to_group
  refine wp_loop_inv (ts := [i64, i32])
    (fun (rbits, i, ()) ml => i.toNat ≤ nv.toNat ∧ ∃ rngL scrL,
      scrL.length = c.scratch_cap ∧
      (∀ j < k5Base, scrL[j]? = s.scratch.scratch_buf[j]?) ∧
      K512ScratchInv P scrL ∧ (k5StateOfScratch scrL).nv = nv ∧
      (FullMem c { s with scratch := { s.scratch with rng_state := rngL, scratch_buf := scrL } }
        ⋆ R) ml)
    (fun (_, i, ()) _ => nv.toNat - i.toNat)
    (fun _ hJ => by
      m4_steps
      exact hJ (r0, 0#32, ()) m0
        ⟨Nat.zero_le _, rng0, s.scratch.scratch_buf, hlen.scratch_ok.scratch_buf_len,
         fun _ _ => rfl, hK0, hnv_eq, hm0⟩)
    (fun _ (rbits, i, ()) ml ⟨hi_le, rngL, scrL, hslL, hpreL, hKL, hnvL, hml⟩ hJ => by
      let sL : FullState :=
        { s with scratch := { s.scratch with rng_state := rngL, scratch_buf := scrL } }
      have hlenL : sL.LengthsOk c :=
        ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hslL }⟩
      m4_split
      · have hi_lt : i.toNat < nv.toNat := by bv_omega
        m4_to_group
        refine wp_join_group (ts := [i64])
          (fun (rb1, ()) m1 => ∃ rng1,
            (FullMem c { s with scratch :=
              { s.scratch with rng_state := rng1, scratch_buf := scrL } } ⋆ R) m1)
          (fun _ (rb1, ()) m1 ⟨rng1, hm1⟩ => by
            let s1 : FullState :=
              { s with scratch := { s.scratch with rng_state := rng1, scratch_buf := scrL } }
            have hfl_idx : ((3104 : BitVec 32) + i).toNat = 3104 + i.toNat := by bv_omega
            have hk_bd : 2304 + ((3104 + i).setWidth 64).toNat < scrL.length := by
              rw [hslL, bv_c0_zext32_64, hfl_idx]; unfold k5MinScr at hcap; omega
            have hi1 : (i + 1#32).toNat = i.toNat + 1 := m4_bv32_add1 (by omega)
            m4_steps
            have hset := k5ScratchInv_set_flags_bit0 (i := i.toNat) (by omega)
              (rb1.setWidth 32) hKL
            have hidx_eq : 2304 + ((3104 + i).setWidth 64).toNat = k5Base + 3104 + i.toNat := by
              rw [bv_c0_zext32_64, hfl_idx]; unfold k5Base; omega
            have hfl_get : scrL[2304 + ((3104 + i).setWidth 64).toNat]'hk_bd =
                scrL[k5Base + 3104 + i.toNat]?.getD 0#32 := by
              rw [List.getElem?_eq_getElem (by rw [← hidx_eq]; exact hk_bd), Option.getD_some]
              congr 1
            refine hJ (rb1 >>> 1#64, i + 1#32, ()) _ (by dsimp only; omega)
              ⟨by omega, rng1, _, List.length_set.trans hslL, fun j hj => ?_, ?_, ?_, by assumption⟩
            · rw [List.getElem?_set_ne (by rw [hidx_eq]; unfold k5Base at hj ⊢; omega)]
              exact hpreL j hj
            · rw [hfl_get, hidx_eq]; exact hset.1
            · rw [hfl_get, hidx_eq]; exact hset.2.trans hnvL)
          (fun _ hJrb => by
            m4_split
            · m4_split
              · refine m4_call_rng_next hRng hlenL hml fun rb1 rng1 m1 _ hm1 => ?_
                m4_steps; exact hJrb (rb1, ()) m1 ⟨rng1, hm1⟩
              · m4_steps; exact hJrb (rbits, ()) ml ⟨rngL, hml⟩
            · m4_steps; exact hJrb (rbits, ()) ml ⟨rngL, hml⟩)
      · have hk19 : 2304 + (BitVec.ofNat 64 19).toNat < scrL.length := by
          rw [hslL]; unfold k5MinScr at hcap; simp; omega
        m4_steps
        let v19 : BitVec 32 := (scrL[2304 + (BitVec.ofNat 64 19).toNat]'hk19) ^^^ 1#32
        have hph := k5ScratchInv_set_phase v19 hKL
        have h19_eq : 2304 + (BitVec.ofNat 64 19).toNat = k5Base + 19 := by decide
        refine hQ rngL (scrL.set (2304 + (BitVec.ofNat 64 19).toNat) v19) _
          ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := List.length_set.trans hslL }⟩
          (fun j hj => by
            rw [List.getElem?_set_ne (by rw [h19_eq]; unfold k5Base at hj ⊢; omega)]
            exact hpreL j hj)
          (by rw [h19_eq]; exact hph.1) (by rw [h19_eq]; exact hph.2.trans hnvL) (by assumption))

/-! ## 5. `full_m4_sweep_flip_round_wp` (`15/24`) -/

theorem full_m4_sweep_flip_round_wp (Γ : Env)
    (hRng : M4EnvSpec Γ "full_rng_next" fullRngNextSpec)
    (hFlip : M4EnvSpec Γ "full_k512_flip" k5FlipSpec) :
    ∀ args m Q X, m4SweepFlipRoundSpec args m Q X →
      Func.wp Γ full_m4_sweep_flip_round_body args m Q X := by
  rintro ⟨h, nv, ⟨⟩⟩ m Q X ⟨c, s, P, R, rfl, hlen, hK0, hnv_eq, hm, hQ⟩
  have hcap : k5MinScr ≤ c.scratch_cap := hlen.scratch_ok.scratch_buf_len ▸ hK0.1
  have hnv512 : nv.toNat ≤ 512 := by
    have := hK0.2.2.clauses.nv_le; rw [hnv_eq] at this; exact this
  unfold Func.wp full_m4_sweep_flip_round_body
  m4_steps
  m4_split
  · m4_steps
    exact hQ 0#32 s.scratch.rng_state s.scratch.scratch_buf m hlen (fun _ _ => rfl) hK0 hnv_eq hm
  have hnv_pos : 0 < nv.toNat := by bv_omega
  have hnv64_nz : nv.setWidth 64 ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
  m4_steps
  refine m4_call_rng_next hRng hlen hm fun r0 rng0 m0 hlen0 hm0 => ?_
  m4_steps
  refine m4_call_rng_next hRng hlen0 hm0 fun rb0 rng1 m1 hlen1 hm1 => ?_
  let start : BitVec 32 := (r0 % nv.setWidth 64).setWidth 32
  have hstart_lt : start.toNat < nv.toNat := by
    have hrem : (r0 % nv.setWidth 64).toNat < nv.toNat := by
      rw [BitVec.toNat_umod, bv_c0_zext32_64]; exact Nat.mod_lt _ hnv_pos
    dsimp only [start]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hrem
  m4_to_group
  refine wp_loop_inv (ts := [i64, i32, i32])
    (fun (rbits, flipped, step, ()) ml => step.toNat ≤ nv.toNat ∧ ∃ rngL scrL,
      scrL.length = c.scratch_cap ∧
      (∀ j < k5Base, scrL[j]? = s.scratch.scratch_buf[j]?) ∧
      K512ScratchInv P scrL ∧ (k5StateOfScratch scrL).nv = nv ∧
      (FullMem c { s with scratch := { s.scratch with rng_state := rngL, scratch_buf := scrL } }
        ⋆ R) ml)
    (fun (_, _, step, ()) _ => nv.toNat - step.toNat)
    (fun _ hJ => by
      m4_steps
      exact hJ (rb0, 0#32, 0#32, ()) m1
        ⟨Nat.zero_le _, rng1, s.scratch.scratch_buf, hlen.scratch_ok.scratch_buf_len,
         fun _ _ => rfl, hK0, hnv_eq, hm1⟩)
    (fun _ (rbits, flipped, step, ()) ml ⟨hs_le, rngL, scrL, hslL, hpreL, hKL, hnvL, hml⟩ hJ => by
      let sL : FullState :=
        { s with scratch := { s.scratch with rng_state := rngL, scratch_buf := scrL } }
      have hlenL : sL.LengthsOk c :=
        ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hslL }⟩
      m4_split
      · have hs_lt : step.toNat < nv.toNat := by bv_omega
        have hs1 : (step + 1#32).toNat = step.toNat + 1 := m4_bv32_add1 (by omega)
        m4_to_group
        refine wp_join_group (ts := [i64])
          (fun (rb1, ()) m_rb => ∃ rng1,
            (FullMem c { s with scratch :=
              { s.scratch with rng_state := rng1, scratch_buf := scrL } } ⋆ R) m_rb)
          (fun _ (rb1, ()) m_rb ⟨rng1, hm_rb⟩ => by
            m4_to_group
            refine wp_join_group (ts := [i32])
              (fun (fl2, ()) m2 => ∃ scr2,
                scr2.length = c.scratch_cap ∧
                (∀ j < k5Base, scr2[j]? = s.scratch.scratch_buf[j]?) ∧
                K512ScratchInv P scr2 ∧ (k5StateOfScratch scr2).nv = nv ∧
                (FullMem c { s with scratch :=
                  { s.scratch with rng_state := rng1, scratch_buf := scr2 } } ⋆ R) m2)
              (fun _ (fl2, ()) m2 ⟨scr2, hsl2, hpre2, hK2, hnv2, hm2⟩ => by
                m4_steps
                exact hJ (rb1 >>> 1#64, fl2, step + 1#32, ()) m2 (by dsimp only; omega)
                  ⟨by omega, rng1, scr2, hsl2, hpre2, hK2, hnv2, hm2⟩)
              (fun _ hJfl => by
                m4_split; rotate_left
                · m4_steps; exact hJfl (flipped, ()) m_rb ⟨scrL, hslL, hpreL, hKL, hnvL, hm_rb⟩
                m4_to_group
                refine wp_join_group (ts := [i32])
                  (fun (v, ()) mv => mv = m_rb ∧ v.toNat < nv.toNat)
                  (fun _ (v, ()) mv ⟨hmv, hv_lt⟩ => by
                    subst mv
                    have hk_bd : 2304 + ((5152 + (v <<< (1 : Nat))).setWidth 64).toNat <
                        scrL.length := by
                      rw [hslL, bv_c0_zext32_64]
                      have hshl : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by bv_omega
                      have hadd : (5152 + (v <<< (1 : Nat))).toNat = 5152 + 2 * v.toNat := by
                        rw [BitVec.toNat_add, show (5152 : BitVec 32).toNat = 5152 from rfl, hshl,
                          Nat.mod_eq_of_lt (by omega)]
                      rw [hadd]; unfold k5MinScr at hcap; omega
                    m4_to_group
                    refine wp_join_group (ts := [i32])
                      (fun (lit, ()) mlit => mlit = m_rb ∧ lit.toNat < 2 * nv.toNat)
                      (fun _ (lit, ()) mlit ⟨hmlit, hlit_lt⟩ => by
                        subst hmlit
                        let s1 : FullState :=
                          { s with scratch :=
                            { s.scratch with rng_state := rng1, scratch_buf := scrL } }
                        have hlen1' : s1.LengthsOk c :=
                          ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hslL }⟩
                        m4_to_group; refine wp_unroll_group fun _ _ => ?_
                        m4_call hFlip
                        refine ⟨c, s1, P, R, rfl, hlen1', hKL, by rw [hnvL]; exact hlit_lt,
                          hm_rb, fun ok scr2 m2 hlen2 hpre_f hK2 hnv2 _ _ hm2 => ?_⟩
                        have hpre2 : ∀ j < k5Base, scr2[j]? = s.scratch.scratch_buf[j]? :=
                          fun j hj => (hpre_f j hj).trans (hpreL j hj)
                        m4_split
                        · m4_steps
                          exact hJfl (flipped + 1#32, ()) m2
                            ⟨scr2, hlen2.scratch_ok.scratch_buf_len, hpre2, hK2, hnv2.trans hnvL,
                              hm2⟩
                        · m4_steps
                          exact hJfl (flipped, ()) m2
                            ⟨scr2, hlen2.scratch_ok.scratch_buf_len, hpre2, hK2, hnv2.trans hnvL,
                              hm2⟩)
                      (fun _ hJlit => by
                        m4_split
                        · m4_steps; exact hJlit (v <<< (1 : Nat), ()) m_rb ⟨rfl, by bv_omega⟩
                        · m4_steps
                          refine hJlit ((v <<< (1 : Nat)) ||| 1#32, ()) m_rb ⟨rfl, ?_⟩
                          have := FullSweepVarHelpers.bv32_shl1_or_pol v 1#32 (by omega) (by decide)
                          rw [this]; simp; omega))
                  (fun _ hJv => by
                    m4_split
                    · m4_steps; exact hJv (start + step - nv, ()) m_rb
                        ⟨rfl, by dsimp only [start] at hstart_lt ⊢; bv_omega⟩
                    · m4_steps; exact hJv (start + step, ()) m_rb
                        ⟨rfl, by dsimp only [start] at hstart_lt ⊢; bv_omega⟩)))
          (fun _ hJrb => by
            m4_split
            · m4_split
              · refine m4_call_rng_next hRng hlenL hml fun rb1 rng1 m1 _ hm1 => ?_
                m4_steps; exact hJrb (rb1, ()) m1 ⟨rng1, hm1⟩
              · m4_steps; exact hJrb (rbits, ()) ml ⟨rngL, hml⟩
            · m4_steps; exact hJrb (rbits, ()) ml ⟨rngL, hml⟩)
      · m4_steps; exact hQ flipped rngL scrL ml hlenL hpreL hKL hnvL hml)

/-! ## 6. `full_m4_sweep_rearm_wp` (`16/24`) -/

private theorem m4_bv64_shl1_toNat (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := by
  have hx := x.isLt
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : x.toNat * 2 < 2 ^ 64)]; omega

private theorem m4_bv64_shl1_add1_toNat (x : BitVec 32) :
    ((x.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  have hx := x.isLt
  rw [BitVec.toNat_add, m4_bv64_shl1_toNat, show (1#64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : 2 * x.toNat + 1 < 2 ^ 64)]

theorem full_m4_sweep_rearm_wp (Γ : Env) :
    ∀ args m Q X, m4SweepRearmSpec args m Q X →
      Func.wp Γ full_m4_sweep_rearm_body args m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hm, hQ⟩
  have hlen := hinv.1
  have hw := hinv.2.1
  have hdm := hinv.2.2.2.2.2.2
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hfl_len := hlen.core_ok.flags_len
  have hwv_len := hlen.core_ok.wvec_len
  have hws_len := hlen.core_ok.wstk_len_arr
  have har_len := hlen.core_ok.arena_len_arr
  have hal_le := hlen.core_ok.arena_len_le
  have hwcap_lt := c.hwcap; unfold dimacsBound at hwcap_lt
  have hacap_lt := c.harena; unfold dimacsBound at hacap_lt
  have hdense : DenseWatchesInv F_cur s.core := by
    have hmw := hw.watches; unfold ModeWatchesInv at hmw; rwa [ite_eq_right hdm] at hmw
  unfold Func.wp full_m4_sweep_rearm_body
  m4_steps
  m4_split
  · m4_steps; exact hQ s.core.flags m hfl_len hinv hm
  have hv_lt : v.toNat < s.core.cur_vars := by
    have : ¬ s.core.cur_vars % 2 ^ 64 ≤ v.toNat := by bv_omega
    omega
  m4_to_group
  refine wp_loop_inv (ts := [i32])
    (fun (pol, ()) mp => pol.toNat ≤ 2 ∧ ∃ flP : List (BitVec 32), flP.length = c.max_vars ∧
      (FullMem c { s with core := { s.core with flags := flP } } ⋆ R) mp)
    (fun (pol, ()) _ => 2 - pol.toNat)
    (fun _ hJpol => by
      m4_steps; exact hJpol (0#32, ()) m ⟨Nat.zero_le _, s.core.flags, hfl_len, hm⟩)
    (fun _ (pol, ()) mp ⟨hpol_le, flP, hflP_len, hmp⟩ hJpol => by
      m4_split; rotate_left
      · m4_steps; exact hQ flP mp hflP_len (m4_fullDenseInvW_with_flags hinv hflP_len) hmp
      have hpol_lt : pol.toNat < 2 := by bv_omega
      have hpol1 : (pol + 1#32).toNat = pol.toNat + 1 := m4_bv32_add1 (by omega)
      let lit : BitVec 32 := (v <<< (1 : Nat)) ||| pol
      have hlit_eq : lit.toNat = 2 * v.toNat + pol.toNat :=
        FullSweepVarHelpers.bv32_shl1_or_pol v pol (by omega) hpol_lt
      have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
      have hlit_w0 : (BitVec.setWidth 64 (v <<< (1 : Nat) ||| pol) <<< (1 : Nat)).toNat <
          s.core.wvec.length := by
        rw [hwv_len, m4_bv64_shl1_toNat]; change 2 * lit.toNat < 4 * c.max_vars; omega
      have hlit_w1 : ((BitVec.setWidth 64 (v <<< (1 : Nat) ||| pol) <<< (1 : Nat)) + 1#64).toNat <
          s.core.wvec.length := by
        rw [hwv_len, m4_bv64_shl1_add1_toNat]; change 2 * lit.toNat + 1 < 4 * c.max_vars; omega
      let wOff : BitVec 64 :=
        (s.core.wvec[(BitVec.setWidth 64 (v <<< (1 : Nat) ||| pol) <<<
          (1 : Nat)).toNat]'hlit_w0).setWidth 64
      let wSz : BitVec 64 :=
        (s.core.wvec[((BitVec.setWidth 64 (v <<< (1 : Nat) ||| pol) <<< (1 : Nat)) +
          1#64).toNat]'hlit_w1).setWidth 64
      have hoff_eq : wOff.toNat = fullWatchOffCore s.core lit.toNat := by
        dsimp only [wOff, fullWatchOffCore]
        simp only [bv_c0_zext32_64, m4_bv64_shl1_toNat,
          List.getElem?_eq_getElem (by rw [hwv_len]; omega : 2 * lit.toNat < s.core.wvec.length),
          Option.getD_some]; rfl
      have hsz_eq : wSz.toNat = fullWatchSizeCore s.core lit.toNat := by
        dsimp only [wSz, fullWatchSizeCore]
        simp only [bv_c0_zext32_64, m4_bv64_shl1_add1_toNat,
          List.getElem?_eq_getElem
            (by rw [hwv_len]; omega : 2 * lit.toNat + 1 < s.core.wvec.length),
          Option.getD_some]; rfl
      have hbd_lit := hdense.layout.bounds lit.toNat hlit_lt
      have hwlen_le := hlen.core_ok.wlen_le
      have hend_eq : (wOff + wSz).toNat = wOff.toNat + wSz.toNat := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      have hw0_nat : 2 * (v <<< (1 : Nat) ||| pol).toNat % 2 ^ 64 =
          (BitVec.setWidth 64 (v <<< (1 : Nat) ||| pol) <<< (1 : Nat)).toNat := by
        rw [m4_bv64_shl1_toNat, Nat.mod_eq_of_lt (by change 2 * lit.toNat < 2 ^ 64; omega)]
      have hw1_nat : (2 * (v <<< (1 : Nat) ||| pol).toNat + (1#64).toNat) % 2 ^ 64 =
          ((BitVec.setWidth 64 (v <<< (1 : Nat) ||| pol) <<< (1 : Nat)) + 1#64).toNat := by
        rw [m4_bv64_shl1_add1_toNat, show (1#64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by change 2 * lit.toNat + 1 < 2 ^ 64; omega)]
      have hslice0 : DenseWatchSliceOk F_cur s.core lit.toNat wOff.toNat wSz.toNat := by
        rw [hoff_eq, hsz_eq]; exact hdense.slices lit.toNat hlit_lt
      m4_to_group
      refine wp_join_group (ts := [i64, i64])
        (fun (_pB, _lB, ()) mb => ∃ flB : List (BitVec 32), flB.length = c.max_vars ∧
          (FullMem c { s with core := { s.core with flags := flB } } ⋆ R) mb)
        (fun _ _ mb ⟨flB, hflB_len, hmb⟩ => by
          m4_steps
          exact hJpol (pol + 1#32, ()) mb (by dsimp only; omega)
            ⟨by omega, flB, hflB_len, hmb⟩)
        (fun _ hJbrk => by
          refine wp_loop_inv (ts := [i64, i64])
            (fun (p, lim, ()) mw => p.toNat ≤ (wOff + wSz).toNat ∧ lim.toNat ≤ 128 ∧
              DenseWatchSliceOk F_cur s.core lit.toNat p.toNat ((wOff + wSz).toNat - p.toNat) ∧
              ∃ flW : List (BitVec 32), flW.length = c.max_vars ∧
                (FullMem c { s with core := { s.core with flags := flW } } ⋆ R) mw)
            (fun (_, lim, ()) _ => 128 - lim.toNat)
            (fun _ hJw => by
              m4_steps
              refine hJw (wOff, 0#64, ()) mp ⟨by omega, by simp, ?_, flP, hflP_len, hmp⟩
              rw [hend_eq, Nat.add_sub_cancel_left]; exact hslice0)
            (fun Jw (p, lim, ()) mw ⟨hp_le, hlim_le, hslice, flW, hflW_len, hmw⟩ hJw => by
              m4_split; rotate_left
              · m4_steps; exact hJbrk (p, lim, ()) mw ⟨flW, hflW_len, hmw⟩
              m4_split; rotate_left
              · m4_steps; exact hJbrk (p, lim, ()) mw ⟨flW, hflW_len, hmw⟩
              have hp_lt : p.toNat < (wOff + wSz).toNat := by
                dsimp only [wOff, wSz]; rw [BitVec.toNat_add, bv_c0_zext32_64, bv_c0_zext32_64]
                simp only [← hw0_nat, ← hw1_nat]; assumption
              have hlim_lt : lim.toNat < 128 := by bv_omega
              have hp_ws : p.toNat < s.core.wstk.length := by omega
              have hp1 : (p + 1#64).toNat = p.toNat + 1 := m4_bv64_add1 (by omega)
              have hlim1 : (lim + 1#64).toNat = lim.toNat + 1 := m4_bv64_add1 (by omega)
              let w0 : BitVec 32 := s.core.wstk[p.toNat]'hp_ws
              have hw0_s : s.core.wstk[p.toNat]? = some w0 := List.getElem?_eq_getElem hp_ws
              m4_split
              · -- binary watch entry
                have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by dsimp only [w0]; bv_omega
                have hslice1 := (denseWatchSlice_step_bin hslice (by omega) hw0_s hbin).2.2.2
                m4_to_group
                refine wp_join_group (ts := [])
                  (fun (_ : Tup Val []) m1 => ∃ fl1 : List (BitVec 32), fl1.length = c.max_vars ∧
                    (FullMem c { s with core := { s.core with flags := fl1 } } ⋆ R) m1)
                  (fun _ () m1 ⟨fl1, hfl1_len, hm1⟩ => by
                    m4_steps
                    refine hJw (p + 1#64, lim + 1#64, ()) m1 (by dsimp only; omega)
                      ⟨by omega, by omega, ?_, fl1, hfl1_len, hm1⟩
                    rw [hp1, show (wOff + wSz).toNat - (p.toNat + 1) =
                      (wOff + wSz).toNat - p.toNat - 1 by omega]
                    exact hslice1)
                  (fun _ hJb => by
                    try refine wp_unroll_group fun _ _ => ?_
                    m4_split; rotate_left
                    · m4_steps; exact hJb () mw ⟨flW, hflW_len, hmw⟩
                    have hov_lt : (((w0 &&& 0x7FFFFFFF#32) >>> (1 : Nat)).setWidth 64).toNat <
                        c.max_vars := by
                      have : (((w0 &&& 0x7FFFFFFF#32) >>> (1 : Nat)).setWidth 64).toNat <
                          s.core.cur_vars % 2 ^ 64 := by dsimp only [w0]; bv_omega
                      omega
                    m4_split; rotate_left
                    · m4_steps; exact hJb () mw ⟨flW, hflW_len, hmw⟩
                    m4_split; rotate_left
                    · m4_steps; exact hJb () mw ⟨flW, hflW_len, hmw⟩
                    m4_steps; exact hJb () _ ⟨_, List.length_set.trans hflW_len, by assumption⟩)
              · -- occurrence watch entry
                have hocc : (w0 &&& 0x80000000#32) = 0#32 := by dsimp only [w0]; bv_omega
                obtain ⟨hrem2, _, cr, hcr_s, hcr_lt, hcr_ref, hslice2⟩ :=
                  denseWatchSlice_step_occ hslice (by omega) hw0_s hocc
                m4_split
                · exfalso
                  have hge : (wOff + wSz).toNat ≤ (p + 1#64).toNat := by
                    rw [BitVec.toNat_add, BitVec.toNat_add]
                    dsimp only [wOff, wSz]
                    rw [bv_c0_zext32_64, bv_c0_zext32_64]
                    simp only [← hw0_nat, ← hw1_nat]; assumption
                  omega
                have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
                  rw [m4_bv64_add1 (by rw [hp1]; omega), hp1]
                have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
                have hcr_eq : s.core.wstk[(p + 1#64).toNat]'(by omega) = cr := by
                  rw [List.getElem?_eq_getElem (by omega)] at hcr_s
                  simpa [hp1] using Option.some.inj hcr_s
                have hcr2_lt : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
                  simp [BitVec.toNat_add]; omega
                have hcr_bd : cr.toNat < s.core.arena.length := by omega
                have hcr2_bd : (cr.setWidth 64 + 2#64).toNat < s.core.arena.length := by omega
                have hcr_bd' : (BitVec.setWidth 64
                    (s.core.wstk[(p + 1#64).toNat]'(by omega))).toNat < s.core.arena.length := by
                  rw [hcr_eq, bv_c0_zext32_64]; exact hcr_bd
                have hcr2_bd' : (BitVec.setWidth 64
                    (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 2#64).toNat <
                    s.core.arena.length := by
                  rw [hcr_eq]; exact hcr2_bd
                let sz : BitVec 32 := s.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_bd
                have hsz_eq_ar : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                  unfold fullArenaClauseSizeCore; dsimp only [sz]
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  simp only [hcr2_lt]
                have hsz_eq_hc : s.core.arena[(BitVec.setWidth 64
                    (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 2#64).toNat]'(by
                      rw [hcr_eq]; exact hcr2_bd) = sz := by
                  simp only [hcr_eq, sz]
                have hstep_occ : ∀ flX mX, flX.length = c.max_vars →
                    (FullMem c { s with core := { s.core with flags := flX } } ⋆ R) mX →
                    Jw (p + 1#64 + 1#64, lim + 1#64, ()) mX := fun flX mX hflX hmX =>
                  hJw (p + 1#64 + 1#64, lim + 1#64, ()) mX (by dsimp only; omega)
                    ⟨by omega, by omega, by
                      rw [hp2, show (wOff + wSz).toNat - (p.toNat + 2) =
                        (wOff + wSz).toNat - p.toNat - 2 by omega]
                      exact hslice2, flX, hflX, hmX⟩
                m4_to_group; try refine wp_unroll_group fun _ _ => ?_
                try refine wp_unroll_group fun _ _ => ?_
                m4_split; · m4_steps; exact hstep_occ flW mw hflW_len hmw
                m4_split; · m4_steps; exact hstep_occ flW mw hflW_len hmw
                have hsz_le16 : sz.toNat ≤ 16 := by
                  have h1 : ¬ 16 < (s.core.arena[(BitVec.setWidth 64
                      (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 2#64).toNat]'(by
                        rw [hcr_eq]; exact hcr2_bd)).toNat := ‹_›
                  rw [hsz_eq_hc] at h1; omega
                have hcr3_sz : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
                  have := hcr_wf.2.2; omega
                m4_to_group
                refine wp_loop_inv (ts := [i32])
                  (fun (i, ()) mi => i.toNat ≤ sz.toNat ∧ ∃ flI : List (BitVec 32),
                    flI.length = c.max_vars ∧
                    (FullMem c { s with core := { s.core with flags := flI } } ⋆ R) mi)
                  (fun (i, ()) _ => sz.toNat - i.toNat)
                  (fun _ hJi => by
                    m4_steps; exact hJi (0#32, ()) mw ⟨Nat.zero_le _, flW, hflW_len, hmw⟩)
                  (fun _ (i, ()) mi ⟨hi_le, flI, hflI_len, hmi⟩ hJi => by
                    m4_split; rotate_left
                    · m4_steps; exact hstep_occ flI mi hflI_len hmi
                    have hi_lt : i.toNat < sz.toNat := by
                      have h1 : i.toNat < (s.core.arena[(BitVec.setWidth 64
                          (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 2#64).toNat]'(by
                            rw [hcr_eq]; exact hcr2_bd)).toNat := ‹_›
                      rwa [hsz_eq_hc] at h1
                    have hi1 : (i + 1#32).toNat = i.toNat + 1 := m4_bv32_add1 (by omega)
                    have hidx_ar : (cr.setWidth 64 + 3#64 + i.setWidth 64).toNat <
                        s.core.arena.length := by
                      simp [BitVec.toNat_add]; omega
                    have hidx_ar' : (BitVec.setWidth 64
                        (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 3#64 +
                        i.setWidth 64).toNat < s.core.arena.length := by
                      rw [hcr_eq]; exact hidx_ar
                    m4_to_group
                    refine wp_join_group (ts := [])
                      (fun (_ : Tup Val []) m2 => ∃ fl2 : List (BitVec 32),
                        fl2.length = c.max_vars ∧
                        (FullMem c { s with core := { s.core with flags := fl2 } } ⋆ R) m2)
                      (fun _ () m2 ⟨fl2, hfl2_len, hm2⟩ => by
                        m4_steps
                        exact hJi (i + 1#32, ()) m2 (by dsimp only; omega)
                          ⟨by omega, fl2, hfl2_len, hm2⟩)
                      (fun _ hJif => by
                        try refine wp_unroll_group fun _ _ => ?_
                        m4_split; rotate_left
                        · m4_steps; exact hJif () mi ⟨flI, hflI_len, hmi⟩
                        have hlv_lt : (((s.core.arena[(BitVec.setWidth 64
                            (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 3#64 +
                            i.setWidth 64).toNat]'(by rw [hcr_eq]; exact hidx_ar)) >>>
                            (1 : Nat)).setWidth 64).toNat < c.max_vars := by
                          have : (((s.core.arena[(BitVec.setWidth 64
                              (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 3#64 +
                              i.setWidth 64).toNat]'(by rw [hcr_eq]; exact hidx_ar)) >>>
                              (1 : Nat)).setWidth 64).toNat < s.core.cur_vars % 2 ^ 64 := by
                            simp only [bv_c0]; bv_omega
                          omega
                        m4_split; rotate_left
                        · m4_steps; exact hJif () mi ⟨flI, hflI_len, hmi⟩
                        m4_split; rotate_left
                        · m4_steps; exact hJif () mi ⟨flI, hflI_len, hmi⟩
                        m4_steps
                        exact hJif () _ ⟨_, List.length_set.trans hflI_len, by assumption⟩)))))

/-! ## 7. `full_m4_sweep_build_pht_wp` (`17/24`) -/

private theorem phtOk_zero {scr : List (BitVec 32)}
    (hhead : ∀ b < phtSz, scr[phtHead + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    PhtOk 0 scr :=
  ⟨fun b hb => Or.inl (hhead b hb), fun _ hi => by omega⟩

private theorem phtOk_step_unmerged {scr : List (BitVec 32)} {i hidx : Nat}
    (hi : i < k5MaxV) (hh : hidx < phtSz) (hlen : k5MinScr ≤ scr.length) (hp : PhtOk i scr) :
    let scr1 := scr.set (phtNext + i) (scr[phtHead + hidx]?.getD 0xFFFFFFFF#32)
    let scr2 := scr1.set (phtHead + hidx) (BitVec.ofNat 32 i)
    PhtOk (i + 1) scr2 := by
  intro scr1 scr2
  refine ⟨fun b hb => ?_, fun k hk => ?_⟩
  · have hb' : b < 1024 := hb
    have hh' : hidx < 1024 := hh
    have hi' : i < 512 := hi
    have hlen' : 24576 ≤ scr.length := hlen
    by_cases hbh : b = hidx
    · subst hbh; right
      dsimp only [scr2, scr1]; unfold phtHead phtNext
      have hbd : 256 + b < (scr.set (1280 + i) (scr[256 + b]?.getD 0xFFFFFFFF#32)).length := by
        simp; omega
      rw [List.getElem?_set_self hbd, Option.getD_some,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    · dsimp only [scr2, scr1]; unfold phtHead phtNext
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      rcases hp.1 b hb with hff | hlt
      · exact Or.inl hff
      · exact Or.inr (by unfold phtHead at hlt; omega)
  · have hh' : hidx < 1024 := hh
    have hi' : i < 512 := hi
    have hlen' : 24576 ≤ scr.length := hlen
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · dsimp only [scr2, scr1]; unfold phtHead phtNext
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hp.2 k hlt
    · dsimp only [scr2, scr1]; unfold phtHead phtNext
      have hbd : 1280 + k < scr.length := by omega
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hbd, Option.getD_some]
      exact hp.1 hidx hh

private theorem phtOk_step_merged {scr : List (BitVec 32)} {i : Nat}
    (hi : i < k5MaxV) (hlen : k5MinScr ≤ scr.length) (hp : PhtOk i scr) :
    PhtOk (i + 1) (scr.set (phtNext + i) 0xFFFFFFFF#32) := by
  have hi' : i < 512 := hi
  have hlen' : 24576 ≤ scr.length := hlen
  refine ⟨fun b hb => ?_, fun k hk => ?_⟩
  · have hb' : b < 1024 := hb
    unfold phtHead phtNext
    rw [List.getElem?_set_ne (by omega)]
    rcases hp.1 b hb with hff | hlt
    · exact Or.inl hff
    · exact Or.inr (by unfold phtHead at hlt; omega)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · unfold phtNext; rw [List.getElem?_set_ne (by omega)]; exact hp.2 k hlt
    · unfold phtNext; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact Or.inl rfl

theorem full_m4_sweep_build_pht_wp (Γ : Env) :
    ∀ args m Q X, m4SweepBuildPhtSpec args m Q X →
      Func.wp Γ full_m4_sweep_build_pht_body args m Q X := by
  rintro ⟨h, nv, smask, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcap, hnv512, hnv_mx, hcone, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hws_len := hlen.scratch_ok.work_stk1_len
  have hsig_len := hlen.scratch_ok.sim_sig_len
  unfold Func.wp full_m4_sweep_build_pht_body
  m4_to_group
  refine wp_loop_inv (ts := [i32])
    (fun (b, ()) mb => b.toNat ≤ phtSz ∧ ∃ scr1 : List (BitVec 32),
      scr1.length = c.scratch_cap ∧
      (∀ j < c.scratch_cap, j < phtHead ∨ phtMerged ≤ j →
        scr1[j]? = s.scratch.scratch_buf[j]?) ∧
      (∀ k < b.toNat, scr1[phtHead + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R) mb)
    (fun (b, ()) _ => phtSz - b.toNat)
    (fun _ hJb => by
      m4_steps
      exact hJb (0#32, ()) m ⟨Nat.zero_le _, s.scratch.scratch_buf, hscr_len,
        fun _ _ _ => rfl, fun _ hk => by simp at hk, hm⟩)
    (fun _ (b, ()) mb ⟨hb_le, scr1, hsl1, hpre1, hhd1, hmb⟩ hJb => by
      m4_split
      · have hb_lt : b.toNat < phtSz := by unfold phtSz; bv_omega
        have hb1 : (b + 1#32).toNat = b.toNat + 1 := m4_bv32_add1 (by unfold phtSz at hb_lt; omega)
        have hidx_eq : ((256 + b).setWidth 64).toNat = phtHead + b.toNat := by
          simp only [phtHead, phtSz] at hb_lt ⊢; rw [bv_c0_zext32_64]; bv_omega
        have hidx_bd : ((256 + b).setWidth 64).toNat < scr1.length := by
          rw [hsl1, hidx_eq]; simp only [phtHead, phtSz, k5MinScr] at hb_lt hcap ⊢; omega
        m4_steps
        refine hJb (b + 1#32, ()) _ (by dsimp only; omega)
          ⟨by omega, _, List.length_set.trans hsl1, fun j hj hdom => ?_, fun k hk => ?_,
           by assumption⟩
        · rw [List.getElem?_set_ne (by
            rw [hidx_eq]; simp only [phtHead, phtSz, phtMerged] at hdom hb_lt ⊢; omega)]
          exact hpre1 j hj hdom
        · rw [hb1] at hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
          · rw [List.getElem?_set_ne (by rw [hidx_eq]; omega)]; exact hhd1 k hlt
          · rw [hidx_eq, List.getElem?_set_self (by rw [← hidx_eq]; exact hidx_bd),
            Option.getD_some]
            rfl
      · have hb_eq : b.toNat = phtSz := by unfold phtSz at hb_le ⊢; bv_omega
        have hp0 : PhtOk 0 scr1 := phtOk_zero (hb_eq ▸ hhd1)
        m4_to_group
        refine wp_loop_inv (ts := [i32])
          (fun (i, ()) mi => i.toNat ≤ nv.toNat ∧ ∃ scr2 : List (BitVec 32),
            scr2.length = c.scratch_cap ∧
            (∀ j < c.scratch_cap, j < phtHead ∨ phtMerged ≤ j →
              scr2[j]? = s.scratch.scratch_buf[j]?) ∧
            PhtOk i.toNat scr2 ∧
            (FullMem c { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆ R) mi)
          (fun (i, ()) _ => nv.toNat - i.toNat)
          (fun _ hJi => by
            m4_steps; exact hJi (0#32, ()) mb ⟨Nat.zero_le _, scr1, hsl1, hpre1, hp0, hmb⟩)
          (fun _ (i, ()) mi ⟨hi_le, scr2, hsl2, hpre2, hp2, hmi⟩ hJi => by
            m4_split; rotate_left
            · have hi_eq : i.toNat = nv.toNat := by bv_omega
              m4_steps; exact hQ scr2 mi hsl2 hpre2 (hi_eq ▸ hp2) hmi
            have hi_lt : i.toNat < nv.toNat := by bv_omega
            have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
              m4_bv32_add1 (by unfold k5MaxV at hnv512; omega)
            have hmg_eq : ((1792 + i).setWidth 64).toNat = phtMerged + i.toNat := by
              simp only [phtMerged, k5MaxV] at hnv512 ⊢; rw [bv_c0_zext32_64]; bv_omega
            have hmg_bd : ((1792 + i).setWidth 64).toNat < scr2.length := by
              rw [hsl2, hmg_eq]; simp only [phtMerged, k5MaxV, k5MinScr] at hnv512 hcap ⊢; omega
            have hnx_eq : ((1280 + i).setWidth 64).toNat = phtNext + i.toNat := by
              simp only [phtNext, k5MaxV] at hnv512 ⊢; rw [bv_c0_zext32_64]; bv_omega
            have hnx_bd : ((1280 + i).setWidth 64).toNat < scr2.length := by
              rw [hsl2, hnx_eq]; simp only [phtNext, k5MaxV, k5MinScr] at hnv512 hcap ⊢; omega
            m4_to_group; refine wp_unroll_group fun _ _ => ?_; m4_split
            · -- unmerged node `i`: hash and push onto bucket `hidx`
              have hi_ws : (i.setWidth 64).toNat < s.scratch.work_stk1.length := by
                rw [hws_len, bv_c0_zext32_64]; omega
              have hgv_lt : (s.scratch.work_stk1[(i.setWidth 64).toNat]'hi_ws).toNat <
                  c.max_vars := by
                have hg := hcone i.toNat hi_lt
                rw [List.getElem?_eq_getElem (by rw [hws_len]; omega), Option.getD_some] at hg
                simp only [bv_c0_zext32_64]; exact Nat.lt_of_lt_of_le hg hcv_le
              have hgv_sig : (BitVec.setWidth 64
                  (s.scratch.work_stk1[(i.setWidth 64).toNat]'hi_ws)).toNat <
                  s.scratch.sim_sig.length := by
                rw [hsig_len, bv_c0_zext32_64]; exact hgv_lt
              m4_to_group
              refine wp_join_group (ts := [i64])
                (fun (key, ()) mkey => mkey = mi)
                (fun _ (key, ()) mkey hmkey => by
                  subst hmkey
                  let hidx : BitVec 32 :=
                    ((key ^^^ (key >>> (17 : Nat)) ^^^ (key >>> (34 : Nat)) ^^^
                      (key >>> (51 : Nat))) &&& 1023#64).setWidth 32
                  have hh_lt : hidx.toNat < phtSz := by
                    dsimp only [hidx]; unfold phtSz
                    have h1 : (((key ^^^ (key >>> (17 : Nat)) ^^^ (key >>> (34 : Nat)) ^^^
                        (key >>> (51 : Nat))) &&& 1023#64)).toNat < 1024 := by
                      rw [BitVec.toNat_and, show (1023#64).toNat = 1023 from rfl]
                      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact h1
                  have hh_eq : ((256 + hidx).setWidth 64).toNat = phtHead + hidx.toNat := by
                    simp only [phtHead, phtSz] at hh_lt ⊢; rw [bv_c0_zext32_64]; bv_omega
                  have hh_bd : ((256 + hidx).setWidth 64).toNat < scr2.length := by
                    rw [hsl2, hh_eq]; simp only [phtHead, phtSz, k5MinScr] at hh_lt hcap ⊢; omega
                  have hsl2_ge : 2304 ≤ scr2.length := by unfold k5MinScr at hcap; omega
                  m4_steps
                  have hstep := phtOk_step_unmerged (i := i.toNat) (hidx := hidx.toNat)
                    (by unfold k5MaxV at hnv512 ⊢; omega) hh_lt (by rw [hsl2]; exact hcap) hp2
                  have hhd_get : scr2[((256 + hidx).setWidth 64).toNat]'hh_bd =
                      scr2[phtHead + hidx.toNat]?.getD 0xFFFFFFFF#32 := by
                    rw [List.getElem?_eq_getElem (by rw [← hh_eq]; exact hh_bd), Option.getD_some]
                    congr 1
                  have hbuf_eq :
                      ((scr2.set ((1280 + i).setWidth 64).toNat
                          (scr2[((256 + hidx).setWidth 64).toNat]'hh_bd)).set
                        ((256 + hidx).setWidth 64).toNat i) =
                      ((scr2.set (phtNext + i.toNat)
                          (scr2[phtHead + hidx.toNat]?.getD 0xFFFFFFFF#32)).set
                        (phtHead + hidx.toNat) i) := by
                    rw [hnx_eq, hhd_get, hh_eq]
                  refine hJi (i + 1#32, ()) _ (by dsimp only; omega)
                    ⟨by omega,
                     (scr2.set (phtNext + i.toNat)
                       (scr2[phtHead + hidx.toNat]?.getD 0xFFFFFFFF#32)).set
                       (phtHead + hidx.toNat) i,
                     by simp [hsl2], fun j hj hdom => ?_, ?_, ?_⟩
                  · rw [List.getElem?_set_ne (by
                        simp only [phtHead, phtSz, phtMerged] at hdom hh_lt ⊢; omega),
                      List.getElem?_set_ne (by
                        simp only [phtHead, phtNext, phtMerged, k5MaxV] at hdom hnv512 ⊢; omega)]
                    exact hpre2 j hj hdom
                  · rw [hi1]; simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hstep
                  · rw [← hbuf_eq]; assumption)
                (fun _ hJkey => by
                  m4_split
                  · m4_steps; exact hJkey _ mi rfl
                  · m4_steps; exact hJkey _ mi rfl)
            · -- already merged: set next = 0xFFFFFFFF
              m4_steps
              refine hJi (i + 1#32, ()) _ (by dsimp only; omega)
                ⟨by omega, _, List.length_set.trans hsl2, fun j hj hdom => ?_, ?_, by assumption⟩
              · rw [List.getElem?_set_ne (by
                  rw [hnx_eq]; simp only [phtHead, phtNext, phtMerged, k5MaxV] at hdom hnv512 ⊢
                  omega)]
                exact hpre2 j hj hdom
              · rw [hi1, hnx_eq]
                exact phtOk_step_merged (by unfold k5MaxV at hnv512 ⊢; omega)
                  (by rw [hsl2]; exact hcap) hp2))

/-! ## 8. `full_m4_sweep_sim_wp` (`18/24`) -/

theorem full_m4_sweep_sim_wp (Γ : Env)
    (hSolve : M4EnvSpec Γ "full_k512_solve" k5SolveSpec)
    (hRef : M4EnvSpec Γ "full_m4_sweep_refine_sig" m4SweepRefineSigSpec)
    (hFlipR : M4EnvSpec Γ "full_m4_sweep_flip_round" m4SweepFlipRoundSpec)
    (hRand : M4EnvSpec Γ "full_m4_sweep_rand_phases" m4SweepRandPhasesSpec) :
    ∀ args m Q X, m4SweepSimSpec args m Q X →
      Func.wp Γ full_m4_sweep_sim_body args m Q X := by
  rintro ⟨h, nv, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hcone, hm, hQ⟩
  obtain ⟨hnv1, hnv512, hnv_cv, hws_lt, hK0, hnv_eq⟩ := hcone
  have hlen := hinv.1
  have hcv_le := hlen.core_ok.cur_vars_le
  have hws_len := hlen.scratch_ok.work_stk1_len
  have hsig_len := hlen.scratch_ok.sim_sig_len
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hcap : k5MinScr ≤ c.scratch_cap := hscr_len ▸ hK0.1
  have hnv_mx : nv.toNat ≤ 2 * c.max_vars := by omega
  let P := ConeModelSet F_cur s.scratch.work_stk1 nv.toNat
  have hnv_bv : (k5StateOfScratch s.scratch.scratch_buf).nv = nv := by
    rw [hnv_eq]; apply BitVec.eq_of_toNat_eq; simp
  have hmk_cone : ∀ (fuel' rng' : BitVec 64) (sig' : List (BitVec 64)) (scr' : List (BitVec 32)),
      K512ScratchInv P scr' → (k5StateOfScratch scr').nv = nv →
      M4SweepConeOk F_cur
        { s with
          core := { s.core with fuel := fuel' }
          scratch := { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } }
        nv.toNat := fun _ _ _ _ hK' hnv' =>
    ⟨hnv1, hnv512, hnv_cv, hws_lt, hK', by rw [hnv']; apply BitVec.eq_of_toNat_eq; simp⟩
  unfold Func.wp full_m4_sweep_sim_body
  m4_to_group
  -- Loop 1: zero `sig[cone_v[i]] = 0ULL` for `i < nv`
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) m1 => i.toNat ≤ nv.toNat ∧ ∃ sig1 : List (BitVec 64),
      sig1.length = c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig1 } } ⋆ R) m1)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun _ hJ0 => by
      m4_steps
      exact hJ0 (0#32, ()) m ⟨Nat.zero_le _, s.scratch.sim_sig, hsig_len, hm⟩)
    (fun _ (i, ()) m1 ⟨hi_le, sig1, hsig1_len, hm1⟩ hJ0 => by
      m4_split
      · have hi_lt : i.toNat < nv.toNat := by bv_omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
          m4_bv32_add1 (by unfold k5MaxV at hnv512; omega)
        have hi_ws : (i.setWidth 64).toNat < s.scratch.work_stk1.length := by
          rw [hws_len, bv_c0_zext32_64]; omega
        have hgv_sig : (BitVec.setWidth 64
            (s.scratch.work_stk1[(i.setWidth 64).toNat]'hi_ws)).toNat < sig1.length := by
          have hg := hws_lt i.toNat hi_lt
          rw [List.getElem?_eq_getElem (by rw [hws_len]; omega), Option.getD_some] at hg
          rw [hsig1_len, bv_c0_zext32_64]; simp only [bv_c0_zext32_64]; omega
        m4_steps
        exact hJ0 (i + 1#32, ()) _ (by dsimp only; omega)
          ⟨by omega, _, List.length_set.trans hsig1_len, by assumption⟩
      · -- Initial unconditional solve (`k[K5H_NASSUMP] = 0u; st0 = full_k512_solve(...)`)
        have hk15 : 2304 + (BitVec.ofNat 64 15).toNat < s.scratch.scratch_buf.length := by
          rw [hscr_len]; unfold k5MinScr at hcap; simp; omega
        have h15_eq : 2304 + (BitVec.ofNat 64 15).toNat = k5Base + 15 := by decide
        obtain ⟨hK_a0, hnv_a0, hass_a0⟩ := k5ScratchInv_set_nassump0 hK0
        m4_steps
        let scrA0 := s.scratch.scratch_buf.set (k5Base + 15) 0#32
        let sA0 : FullState :=
          { s with scratch := { s.scratch with sim_sig := sig1, scratch_buf := scrA0 } }
        have hlenA0 : sA0.LengthsOk c :=
          ⟨hlen.core_ok, { hlen.scratch_ok with
            sim_sig_len := hsig1_len, scratch_buf_len := by simp [sA0, scrA0, hscr_len] }⟩
        have hmA0 : (FullMem c sA0 ⋆ R) m := by
          simpa only [sA0, scrA0, h15_eq] using ‹(FullMem c _ ⋆ R) m›
        m4_call hSolve
        refine ⟨c, sA0, P, R, rfl, hlenA0, hK_a0, hmA0,
          fun st0 fuel0 scr0 m0 hlen0 hfuel0 _ hK_s0 hnv_s0 _ hass_s0 _ huns0 hm0 => ?_⟩
        have hscr0_len := hlen0.scratch_ok.scratch_buf_len
        have hnv_s0' : (k5StateOfScratch scr0).nv = nv :=
          hnv_s0.trans (hnv_a0.trans hnv_bv)
        m4_split
        · have hst20 : st0 = 20#64 := by bv_omega
          have huns_cur : (cnfOfClauses F_cur).Unsat := by
            apply coneModelSet_unsat_of_empty (ws1 := s.scratch.work_stk1) (nv := nv.toNat)
            intro β hβ
            have hna := huns0 hst20 β hβ
            rw [hass_s0, hass_a0] at hna
            exact hna (by simp [unitsCnf])
          m4_steps
          exact hQ 0xFFFFFFFF#32 fuel0 s.scratch.rng_state sig1 scr0 m0
            (m4_fullDenseInvW_with_fuel_rng_sig_scr hinv hsig1_len hscr0_len)
            hfuel0 (hmk_cone _ _ _ _ hK_s0 hnv_s0') (fun _ => huns_cur)
            (fun h => absurd rfl h) hm0
        m4_split
        · m4_steps
          exact hQ 0#32 fuel0 s.scratch.rng_state sig1 scr0 m0
            (m4_fullDenseInvW_with_fuel_rng_sig_scr hinv hsig1_len hscr0_len)
            hfuel0 (hmk_cone _ _ _ _ hK_s0 hnv_s0') (fun h => by cases h) (fun _ => by decide) hm0
        -- Refine bit 0, compute `sim_lim`, and enter round loop (`round < 4 && rbit < 64 && fuel >
        -- 0`)
        m4_call hRef
        refine ⟨c, _, R, rfl, hlen0, hcap, hnv512, hnv_mx, hws_lt, hm0,
          fun sig2 m2 hsig2_len hm2 => ?_⟩
        m4_to_group
        refine wp_join_group (ts := [i64])
          (fun (_sim_lim, ()) msl => msl = m2)
          (fun _ (sim_lim, ()) msl hmsl => by
            subst msl
            m4_to_group
            refine wp_join_group (ts := [i32, i32])
              (fun (rbitB, _roundB, ()) mB => rbitB.toNat ≤ 64 ∧
                ∃ fuelB rngB sigB scrB,
                  fuelB.toNat ≤ s.core.fuel.toNat ∧ sigB.length = c.max_vars ∧
                  scrB.length = c.scratch_cap ∧ K512ScratchInv P scrB ∧
                  (k5StateOfScratch scrB).nv = nv ∧
                  (FullMem c { s with
                    core := { s.core with fuel := fuelB }
                    scratch := { s.scratch with rng_state := rngB, sim_sig := sigB,
                                                scratch_buf := scrB } } ⋆ R) mB)
              (fun _ (rbitB, _, ()) mB ⟨hr_le, fuelB, rngB, sigB, scrB, hflB, hsgB, hscB, hKB, hnvB,
                hmB⟩ => by
                m4_steps
                exact hQ rbitB fuelB rngB sigB scrB mB
                  (m4_fullDenseInvW_with_fuel_rng_sig_scr hinv hsgB hscB) hflB
                  (hmk_cone _ _ _ _ hKB hnvB)
                  (fun h => by rw [h] at hr_le; exfalso; revert hr_le; decide)
                  (fun _ => hr_le) hmB)
              (fun _ hJbrk => by
                refine wp_loop_inv (ts := [i32, i32])
                  (fun (rbit, round, ()) ml => round.toNat ≤ 4 ∧ rbit.toNat ≤ 64 ∧
                    ∃ fuelL rngL sigL scrL,
                      fuelL.toNat ≤ s.core.fuel.toNat ∧ sigL.length = c.max_vars ∧
                      scrL.length = c.scratch_cap ∧ K512ScratchInv P scrL ∧
                      (k5StateOfScratch scrL).nv = nv ∧
                      (FullMem c { s with
                        core := { s.core with fuel := fuelL }
                        scratch := { s.scratch with rng_state := rngL, sim_sig := sigL,
                                                    scratch_buf := scrL } } ⋆ R) ml)
                  (fun (_, round, ()) _ => 4 - round.toNat)
                  (fun _ hJrd => by
                    m4_steps
                    exact hJrd (1#32, 0#32, ()) m2
                      ⟨Nat.zero_le _, by decide, fuel0, s.scratch.rng_state, sig2, scr0,
                       hfuel0, hsig2_len, hscr0_len, hK_s0, hnv_s0', hm2⟩)
                  (fun _ (rbit, round, ()) ml
                      ⟨hrd_le, hrb_le, fuelL, rngL, sigL, scrL, hflL, hsgL, hscL, hKL, hnvL,
                        hml⟩ hJrd => by
                    have hbrkL := hJbrk (rbit, round, ()) ml
                      ⟨hrb_le, fuelL, rngL, sigL, scrL, hflL, hsgL, hscL, hKL, hnvL, hml⟩
                    m4_split; rotate_left; · m4_steps; exact hbrkL
                    m4_split; rotate_left; · m4_steps; exact hbrkL
                    m4_split; rotate_left; · m4_steps; exact hbrkL
                    have hrd_lt : round.toNat < 4 := by bv_omega
                    have hrd1 : (round + 1#32).toNat = round.toNat + 1 := m4_bv32_add1 (by omega)
                    -- Inner flip loop: `while (fr < 3u && rbit < 64u)`
                    m4_to_group
                    refine wp_join_group (ts := [i32, i32])
                      (fun (rbitF, _frF, ()) mF => rbitF.toNat ≤ 64 ∧
                        ∃ rngF sigF scrF,
                          sigF.length = c.max_vars ∧ scrF.length = c.scratch_cap ∧
                          K512ScratchInv P scrF ∧ (k5StateOfScratch scrF).nv = nv ∧
                          (FullMem c { s with
                            core := { s.core with fuel := fuelL }
                            scratch := { s.scratch with rng_state := rngF, sim_sig := sigF,
                                                        scratch_buf := scrF } } ⋆ R) mF)
                      (fun _ (rbitF, _, ()) mF ⟨hrbF_le, rngF, sigF, scrF, hsgF, hscF, hKF, hnvF,
                        hmF⟩ => by
                        have hnext := hJrd (rbitF, round + 1#32, ()) mF (by dsimp only; omega)
                          ⟨by omega, hrbF_le, fuelL, rngF, sigF, scrF, hflL, hsgF, hscF, hKF, hnvF,
                            hmF⟩
                        have hk11F : 2304 + (BitVec.ofNat 64 11).toNat < scrF.length := by
                          rw [hscF]; unfold k5MinScr at hcap; simp; omega
                        m4_to_group
                        try refine wp_unroll_group fun _ _ => ?_
                        try refine wp_unroll_group fun _ _ => ?_
                        m4_split; rotate_left; · m4_steps; exact hnext
                        m4_split; rotate_left; · m4_steps; exact hnext
                        m4_split; rotate_left; · m4_steps; exact hnext
                        m4_split; rotate_left; · m4_steps; exact hnext
                        have hrbF_lt : rbitF.toNat < 64 := by bv_omega
                        have hrbF1 : (rbitF + 1#32).toNat = rbitF.toNat + 1 :=
                          m4_bv32_add1 (by omega)
                        let sF : FullState :=
                          { s with
                            core := { s.core with fuel := fuelL }
                            scratch := { s.scratch with rng_state := rngF, sim_sig := sigF,
                                                        scratch_buf := scrF } }
                        have hlenF : sF.LengthsOk c :=
                          ⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len },
                           { hlen.scratch_ok with
                            sim_sig_len := hsgF, scratch_buf_len := hscF }⟩
                        m4_call hRand
                        refine ⟨c, sF, P, R, rfl, hlenF, hKF, hnvF, hmF,
                          fun rngR scrR mR hlenR _ hKR hnvR hmR => ?_⟩
                        have hscR := hlenR.scratch_ok.scratch_buf_len
                        have hk15R : 2304 + (BitVec.ofNat 64 15).toNat < scrR.length := by
                          rw [hscR]; unfold k5MinScr at hcap; simp; omega
                        obtain ⟨hKR0, hnvR0, hassR0⟩ := k5ScratchInv_set_nassump0 hKR
                        m4_steps
                        let scrR0 := scrR.set (k5Base + 15) 0#32
                        let sR0 : FullState :=
                          { s with
                            core := { s.core with fuel := fuelL }
                            scratch := { s.scratch with rng_state := rngR, sim_sig := sigF,
                                                        scratch_buf := scrR0 } }
                        have hlenR0 : sR0.LengthsOk c :=
                          ⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len },
                           { hlen.scratch_ok with
                            sim_sig_len := hsgF, scratch_buf_len := by simp [sR0, scrR0, hscR] }⟩
                        have hmR0 : (FullMem c sR0 ⋆ R) m := by
                          simpa only [sR0, scrR0, h15_eq] using ‹(FullMem c _ ⋆ R) m›
                        m4_call hSolve
                        refine ⟨c, sR0, P, R, rfl, hlenR0, hKR0, hmR0,
                          fun stS fuelS scrS mS hlenS hfuelS _ hKS hnvS _ hassS _ hunsS hmS => ?_⟩
                        have hscS := hlenS.scratch_ok.scratch_buf_len
                        have hflS0 : fuelS.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuelS hflL
                        have hnvS' : (k5StateOfScratch scrS).nv = nv :=
                          hnvS.trans (hnvR0.trans hnvR)
                        m4_split
                        · have hstS20 : stS = 20#64 := by bv_omega
                          have huns_cur : (cnfOfClauses F_cur).Unsat := by
                            apply coneModelSet_unsat_of_empty
                              (ws1 := s.scratch.work_stk1) (nv := nv.toNat)
                            intro β hβ
                            have hna := hunsS hstS20 β hβ
                            rw [hassS, hassR0] at hna
                            exact hna (by simp [unitsCnf])
                          m4_steps
                          exact hQ 0xFFFFFFFF#32 fuelS rngR sigF scrS mS
                            (m4_fullDenseInvW_with_fuel_rng_sig_scr hinv hsgF hscS)
                            hflS0 (hmk_cone _ _ _ _ hKS hnvS') (fun _ => huns_cur)
                            (fun h => absurd rfl h) hmS
                        m4_split
                        · m4_steps
                          exact hJbrk (rbitF, round + 1#32, ()) mS
                            ⟨hrbF_le, fuelS, rngR, sigF, scrS, hflS0, hsgF, hscS, hKS, hnvS', hmS⟩
                        m4_call hRef
                        refine ⟨c, _, R, rfl, hlenS, hcap, hnv512, hnv_mx, hws_lt, hmS,
                          fun sigS mS' hsgS hmS' => ?_⟩
                        m4_steps
                        exact hJrd (rbitF + 1#32, round + 1#32, ()) mS' (by dsimp only; omega)
                          ⟨by omega, by omega, fuelS, rngR, sigS, scrS, hflS0, hsgS, hscS, hKS,
                           hnvS', hmS'⟩)
                      (fun _ hJfrBrk => by
                        refine wp_loop_inv (ts := [i32, i32])
                          (fun (rbitI, fr, ()) mI => fr.toNat ≤ 3 ∧ rbitI.toNat ≤ 64 ∧
                            ∃ rngI sigI scrI,
                              sigI.length = c.max_vars ∧ scrI.length = c.scratch_cap ∧
                              K512ScratchInv P scrI ∧ (k5StateOfScratch scrI).nv = nv ∧
                              (FullMem c { s with
                                core := { s.core with fuel := fuelL }
                                scratch := { s.scratch with rng_state := rngI, sim_sig := sigI,
                                                            scratch_buf := scrI } } ⋆ R) mI)
                          (fun (_, fr, ()) _ => 3 - fr.toNat)
                          (fun _ hJfr => by
                            m4_steps
                            exact hJfr (rbit, 0#32, ()) ml
                              ⟨Nat.zero_le _, hrb_le, rngL, sigL, scrL, hsgL, hscL, hKL, hnvL, hml⟩)
                          (fun _ (rbitI, fr, ()) mI
                              ⟨hfr_le, hrbI_le, rngI, sigI, scrI, hsgI, hscI, hKI, hnvI,
                                hmI⟩ hJfr => by
                            have hbrkI := hJfrBrk (rbitI, fr, ()) mI
                              ⟨hrbI_le, rngI, sigI, scrI, hsgI, hscI, hKI, hnvI, hmI⟩
                            m4_split; rotate_left; · m4_steps; exact hbrkI
                            m4_split; rotate_left; · m4_steps; exact hbrkI
                            have hfr_lt : fr.toNat < 3 := by bv_omega
                            have hrbI_lt : rbitI.toNat < 64 := by bv_omega
                            have hfr1 : (fr + 1#32).toNat = fr.toNat + 1 := m4_bv32_add1 (by omega)
                            have hrbI1 : (rbitI + 1#32).toNat = rbitI.toNat + 1 :=
                              m4_bv32_add1 (by omega)
                            let sI : FullState :=
                              { s with
                                core := { s.core with fuel := fuelL }
                                scratch := { s.scratch with rng_state := rngI, sim_sig := sigI,
                                                            scratch_buf := scrI } }
                            have hlenI : sI.LengthsOk c :=
                              ⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len },
                               { hlen.scratch_ok with
                                sim_sig_len := hsgI, scratch_buf_len := hscI }⟩
                            m4_call hFlipR
                            refine ⟨c, sI, P, R, rfl, hlenI, hKI, hnvI, hmI,
                              fun flp rngF1 scrF1 mF1 hlenF1 _ hKF1 hnvF1 hmF1 => ?_⟩
                            have hscF1 := hlenF1.scratch_ok.scratch_buf_len
                            m4_split; rotate_left
                            · m4_steps
                              exact hJfrBrk (rbitI, fr, ()) mF1
                                ⟨hrbI_le, rngF1, sigI, scrF1, hsgI, hscF1, hKF1, hnvF1, hmF1⟩
                            m4_call hRef
                            refine ⟨c, _, R, rfl, hlenF1, hcap, hnv512, hnv_mx, hws_lt, hmF1,
                              fun sigF1 mF2 hsgF1 hmF2 => ?_⟩
                            m4_steps
                            exact hJfr (rbitI + 1#32, fr + 1#32, ()) mF2 (by dsimp only; omega)
                              ⟨by omega, by omega, rngF1, sigF1, scrF1, hsgF1, hscF1, hKF1,
                               hnvF1, hmF2⟩)))))
          (fun _ hJsl => by
            m4_split <;> (m4_steps; exact hJsl _ m2 rfl)))

end LeanQbe.T.Examples.Kissat.FullM4Sweep
