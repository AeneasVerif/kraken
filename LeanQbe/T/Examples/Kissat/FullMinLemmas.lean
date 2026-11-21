module

public import LeanQbe.T.Examples.Kissat.FullMinLemmas4
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for Kissat `D-Full` Main Minimization (`Stage 4`, Part 5)

Proves the parametric `(Γ : Env)` `Func.wp` contract for `full_min_shrink`
(`FullMinSpecs.fullMinShrinkSpec`, `full_min_shrink_wp`), tying together all `8` self-contained
clause minimization & block-shrinking functions:
`full_min_mark`, `full_min_lit`, `full_tmp_less`, `full_sort_tmp_sift`, `full_sort_tmp`,
`full_shrink_lower`, `full_shrink_blk`, `full_min_shrink`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test
open FullArenaTactics FullMinSpecs

open scoped FullMinTactics

/-! ## 1. Pure list, invariant, and post-sort helpers -/

private theorem list_take_succ_set {α : Type _} {xs : List α} {i : Nat} (v : α)
    (hi : i < xs.length) : (xs.set i v).take (i + 1) = xs.take i ++ [v] := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_set, List.length_append, List.length_take]
    simp only [List.length_singleton]; omega
  · intro j hj1 _; rw [List.getElem_take]
    by_cases hjl : j < min i xs.length
    · rw [List.getElem_append_left (by rw [List.length_take]; exact hjl),
        List.getElem_take, List.getElem_set_ne (by omega)]
    · have hje : j = i := by rw [List.length_take, List.length_set] at hj1; omega
      subst hje
      rw [List.getElem_set_self (by rw [List.length_set]; exact hi),
        List.getElem_append_right (by rw [List.length_take]; omega)]
      simp [List.length_take_of_le (Nat.le_of_lt hi)]

private theorem list_filter_ne_eq_self {xs : List (BitVec 32)} {k : Nat}
    (hk : k ≤ xs.length) (h : ∀ j < k, (xs[j]?.getD 0#32).toNat < 2 ^ 31) :
    (xs.take k).filter (· ≠ 0xFFFFFFFF#32) = xs.take k := by
  rw [List.filter_eq_self]; intro x hx; rw [List.mem_iff_getElem] at hx
  obtain ⟨j, hj, rfl⟩ := hx; rw [List.length_take] at hj
  have hlt := h j (by omega); rw [List.getElem_take]
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hlt
  rw [decide_eq_true_eq]; intro heq; have := congrArg BitVec.toNat heq
  have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega

private theorem fullMinMarkInv_mrk_ne_zero_iff {k : FullCoreState} {keep : List Nat}
    (hmin : FullMinMarkInv k keep) (hno8 : ∀ v < k.cur_vars, (k.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    {v : Nat} (hv : v < k.cur_vars) :
    k.mrk[v]?.getD 0#8 ≠ 0#8 ↔ (k.mrk[v]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
  have hd := hmin.mrk_dom v hv; have h8 := hno8 v hv
  generalize k.mrk[v]?.getD 0#8 = b at hd h8 ⊢; revert b hd h8; decide

private theorem min_shrink_scratch_ok {c : FullCfg} {sc : FullScratch} (hok : sc.LengthsOk c)
    {cf ll mr : BitVec 64} :
    ({ sc with conflicts := cf, learned_lits := ll, min_removed := mr } : FullScratch).LengthsOk
      c := { hok with walk_vals_len := hok.walk_vals_len }

private theorem min_shrink_post_sort {c : FullCfg} {s : FullState}
    (htl1 : 1 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars) (hlen_tmp : s.core.tmp.length = c.max_vars)
    (htmp_vals : ∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (htmp_lvls : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level)
    {tmp1 : List (BitVec 32)} (ht1_len : tmp1.length = c.max_vars)
    (ht1_0 : 0 < s.core.tmp_len → tmp1[0]? = s.core.tmp[0]?)
    (ht1_r : ∀ j, 1 ≤ j → j < s.core.tmp_len →
      ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp1[j]? = s.core.tmp[i]?)
    (ht1_l : ∀ i, 1 ≤ i → i < s.core.tmp_len →
      ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp1[j]?) :
    let keep0 := ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    keep0 = (tmp1.take s.core.tmp_len).map BitVec.toNat ∧
    (∀ F_cur, (cnfOfClauses F_cur).EntailsClause (cnfClause
        ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause keep0)) ∧
    (∀ k < s.core.tmp_len, let l := (tmp1[k]?.getD 0#32).toNat
      tmp1[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ l ∈ keep0) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level) := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlt1 : ∀ k < s.core.tmp_len, (tmp1[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.vals[(tmp1[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
    intro k hk; cases k with
    | zero => rw [ht1_0 htl1]; exact htmp_vals 0 hk
    | succ k' => obtain ⟨i, _, hi2, heq⟩ := ht1_r (k' + 1) (by omega) hk
                 rw [heq]; exact htmp_vals i hi2
  have hkeep_eq : ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat =
      (tmp1.take s.core.tmp_len).map BitVec.toNat := by
    rw [list_filter_ne_eq_self (by omega) fun j hj => by have := (hlt1 j hj).1; omega]
  refine ⟨hkeep_eq, ?_, ?_, fun k hk1 hk2 => by
      obtain ⟨i, hi1, hi2, heq⟩ := ht1_r k hk1 hk2; rw [heq]; exact htmp_lvls i hi1 hi2⟩
  · intro F_cur hEnt0; rw [hkeep_eq]; rw [CNF.entails_clause_def] at hEnt0 ⊢
    intro α hα; obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (hEnt0 α hα)
    refine (clause_sat_cnfClause_iff α _).mpr ⟨l, ?_, hsat⟩
    rw [List.mem_map] at hl ⊢; obtain ⟨b, hb, rfl⟩ := hl
    rw [List.mem_iff_getElem] at hb; obtain ⟨i, hi, rfl⟩ := hb
    rw [List.length_take] at hi; rw [List.getElem_take]
    obtain ⟨j, hj, heq⟩ : ∃ j < s.core.tmp_len, s.core.tmp[i]? = tmp1[j]? := by
      cases i with
      | zero => exact ⟨0, htl1, (ht1_0 htl1).symm⟩
      | succ i' => obtain ⟨j, _, hj2, heq⟩ := ht1_l (i' + 1) (by omega) (by omega)
                   exact ⟨j, hj2, heq⟩
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
    exact ⟨tmp1[j]'(by omega), List.mem_iff_getElem.mpr ⟨j, by rw [List.length_take]; omega,
      by rw [List.getElem_take]⟩, by rw [Option.some.inj heq]⟩
  · intro k hk; have hkv := hlt1 k hk
    have hk_ne : tmp1[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; intro heq
      have hto := congrArg BitVec.toNat heq; have h1' := hkv.1
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1'
      have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
    have hk_mem : (tmp1[k]?.getD 0#32).toNat ∈
        ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat := by
      rw [hkeep_eq, List.mem_map]
      exact ⟨tmp1[k]'(by omega), List.mem_iff_getElem.mpr ⟨k, by rw [List.length_take]; omega,
        by rw [List.getElem_take]⟩, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
    exact ⟨hk_ne, hkv.1, hkv.2, hk_mem⟩

/-! ## 2. Cleanup and compaction sub-expressions (`minShrinkCleanExpr`, `minShrinkCompactExpr`) -/

private def minShrinkCleanExpr (p ld ld_1 ld_6 keep : Val i64) : Expr Val Cont [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk c (a, b, ())
  .group (sig := [[]]) (fun _ => .cons (fun _ =>
    .let_ (op64 (.add i64) (.var p) (.imm 272)) fun p_21 =>
    .store (t := i64) (.imm 0) (.var p_21.fst)
      (.let_ (op64 (.add i64) (.var p) (.imm 280)) fun p_22 =>
       .store (t := i64) (.imm 0) (.var p_22.fst)
         (.let_ (op64 (.add i64) (.var p) (.imm 192)) fun p_23 =>
          .store (.var keep) (.var p_23.fst)
            (.let_ (op64 (.add i64) (.var p) (.imm 352)) fun p_24 =>
             .load i64 (.var p_24.fst) fun ld =>
             .let_ (op64 (.sub i64) (.var ld_1) (.var keep)) fun p_25 =>
             .let_ (op64 (.add i64) (.var ld) (.var p_25.fst)) fun p_26 =>
             .let_ (op64 (.add i64) (.var p) (.imm 352)) fun p_27 =>
             .store (.var p_26.fst) (.var p_27.fst)
               (.let_ (op64 (.add i64) (.var p) (.imm 344)) fun p_28 =>
                .load i64 (.var p_28.fst) fun ld =>
                .let_ (op64 (.add i64) (.var ld) (.var keep)) fun p_29 =>
                .let_ (op64 (.add i64) (.var p) (.imm 344)) fun p =>
                .store (.var p_29.fst) (.var p.fst) (.ret ())))))) .nil)
    fun Js =>
    .let_ (op64 (.add i64) (.var p) (.imm 280)) fun p_20 =>
    .load i64 (.var p_20.fst) fun ld_7 =>
    .let_ (Op.mk (.cmp .ne i64 .bool rfl) (.var ld_7, .imm 0, ())) fun p_21 =>
    .jnz (.var p_21.fst)
      (.group (sig := [[i64]]) (fun Js_1 => .cons (fun p =>
        .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.fst, .var ld, ())) fun p_22 =>
        .jnz (.var p_22.fst)
          (.let_ (op64 (.add i64) (.var ld_6) (.var p.fst)) fun p_23 =>
           .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun p_24 =>
           .store (.var p_24.fst) (.var p_23.fst)
             (.let_ (op64 (.add i64) (.var p.fst) (.imm 1)) fun p =>
              .jump Js_1.fst (.var p.fst, ())))
          (.jump Js.fst ())) .nil) fun Js => .jump Js.fst (.imm 0, ()))
      (.let_ (op64 (.add i64) (.var p) (.imm 240)) fun p_22 =>
       .load i64 (.var p_22.fst) fun ld_8 =>
       .group (sig := [[i64]]) (fun Js_1 => .cons (fun p_23 =>
         .let_ (op64 (.add i64) (.var p) (.imm 272)) fun p =>
         .load i64 (.var p.fst) fun ld_9 =>
         .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_23.fst, .var ld_9, ())) fun p =>
         .jnz (.var p.fst)
           (.let_ (op64 (.mul i64) (.var p_23.fst) (.imm 4)) fun p =>
            .let_ (op64 (.add i64) (.var ld_8) (.var p.fst)) fun p =>
            .load i32 (.var p.fst) fun ld_10 =>
            .group (sig := [[]]) (fun _ => .cons (fun _ =>
              .let_ (op64 (.add i64) (.var p_23.fst) (.imm 1)) fun p =>
              .jump Js_1.fst (.var p.fst, ())) .nil) fun Js =>
            .let_ (Op.mk (.zext 32 64) (.var ld_10, ())) fun p =>
            .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.fst, .var ld, ())) fun p =>
            .jnz (.var p.fst)
              (.let_ (Op.mk (.zext 32 64) (.var ld_10, ())) fun p =>
               .let_ (op64 (.add i64) (.var ld_6) (.var p.fst)) fun p =>
               .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun p_24 =>
               .store (.var p_24.fst) (.var p.fst) (.jump Js.fst ()))
              (.jump Js.fst ()))
           (.jump Js.fst ())) .nil) fun Js => .jump Js.fst (.imm 0, ()))

private theorem min_shrink_clean_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost} (hcore : FullOtfsCoreInv c F0 s)
    {keep_bv : BitVec 64} {m : Mem 64} (hm_in : (FullMem c s ⋆ R) m)
    (hmin : FullMinMarkInv s.core
      (((s.core.tmp.take keep_bv.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hno8 : ∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hpost : ∀ (mrk' : List (BitVec 8)) (m' : Mem 64),
      let sc' := { s.scratch with
        min_removed := s.scratch.min_removed + (BitVec.ofNat 64 s.core.tmp_len - keep_bv),
        learned_lits := s.scratch.learned_lits + keep_bv }
      let s' : FullState := {
        core := { s.core with mrk := mrk', min_clr_len := 0, min_clr_full := 0#64,
                              tmp_len := keep_bv.toNat }
        scratch := sc' }
      mrk'.length = c.max_vars → (∀ w, s.core.cur_vars ≤ w → mrk'[w]? = s.core.mrk[w]?) →
      FullMarksClear s' → (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (minShrinkCleanExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      (BitVec.ofNat 64 s.core.tmp_len) c.pMark keep_bv) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlen := hcore.1.core_ok; have hcv := hlen.cur_vars_le
  have h0v : (0#64 : BitVec 64).toNat = 0 := rfl
  have hz8 : (0 : BitVec 32).setWidth 8 = 0#8 := rfl
  have hmcl_le := hlen.min_clr_len_le; have hmcl_arr := hlen.min_clr_len_arr
  have hmcl_bv : (BitVec.ofNat 64 s.core.min_clr_len).toNat = s.core.min_clr_len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcv_bv : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  dsimp only [minShrinkCleanExpr]
  refine wp_join_group (ts := []) (fun () mc => ∃ mrk',
      mrk'.length = c.max_vars ∧ (∀ w, s.core.cur_vars ≤ w → mrk'[w]? = s.core.mrk[w]?) ∧
      (∀ v < s.core.cur_vars, mrk'[v]?.getD 0#8 = 0#8) ∧
      (FullMem c { s with core := { s.core with mrk := mrk' } } ⋆ R) mc) ?_ ?_
  · rintro Js ⟨⟩ mc ⟨mrk', hml, hab, hmc, hm_c⟩; rw [Blocks.get_here]; ml_lets
    let sc0 : FullState := { s with core := { s.core with mrk := mrk' } }
    ml_st m1, hm1 := store_full_min_clr_len (s := sc0) 0 (Nat.zero_lt_succ _) hm_c; ml_lets
    let sc0b : FullState := { sc0 with core := { sc0.core with min_clr_len := 0 } }
    ml_st m2, hm2 := store_full_min_clr_full (s := sc0b) 0#64 hm1; ml_lets
    ml_st m3, hm3 := c0_store_full_tmp_len
      (s := { sc0b with core := { sc0b.core with min_clr_full := 0#64 } }) keep_bv hm2
    let sc1 : FullState := { s with core := { s.core with
      mrk := mrk', min_clr_len := 0, min_clr_full := 0#64, tmp_len := keep_bv.toNat } }
    ml_ld load_full_min_removed (s := sc1) hm3; ml_lets
    ml_st m4, hm4 := store_full_min_removed (s := sc1)
      (s.scratch.min_removed + (BitVec.ofNat 64 s.core.tmp_len - keep_bv)) hm3
    let sc2 : FullState := { sc1 with scratch := { sc1.scratch with
      min_removed := s.scratch.min_removed + (BitVec.ofNat 64 s.core.tmp_len - keep_bv) } }
    ml_ld load_full_learned_lits (s := sc2) hm4; ml_lets
    ml_st m5, hm5 := store_full_learned_lits (s := sc2) (s.scratch.learned_lits + keep_bv) hm4
    rw [wp]; exact hpost mrk' m5 hml hab hmc hm5
  rintro Js hJs; ml_ld load_full_min_clr_full hm_in; ml_lets; ml_jnz
  refine ⟨fun _ => ?_, fun hnf => ?_⟩
  · refine wp_loop_group (ts := [i64]) (fun n (z, ()) mz =>
        n = s.core.cur_vars - z.toNat ∧ z.toNat ≤ s.core.cur_vars ∧ ∃ mrk_z,
        mrk_z.length = c.max_vars ∧ (∀ w, s.core.cur_vars ≤ w → mrk_z[w]? = s.core.mrk[w]?) ∧
        (∀ w < z.toNat, mrk_z[w]?.getD 0#8 = 0#8) ∧
        (FullMem c { s with core := { s.core with mrk := mrk_z } } ⋆ R) mz) ?_
      (fun J1 hJ1 => by
        ml_lets; exact hJ1 (s.core.cur_vars - 0) (0#64, ()) m
          ⟨by rw [h0v], by rw [h0v]; exact Nat.zero_le _, s.core.mrk, hlen.mrk_len,
           fun _ _ => rfl, fun _ h => by rw [h0v] at h; omega, hm_in⟩)
    rintro J1 n ⟨z, ⟨⟩⟩ mz hJ1 ⟨rfl, hzle, mrk_z, hml_z, hab_z, hz0, hm_z⟩
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · c0_cond hlt; have hzx : z.toNat < s.core.cur_vars := by bv_omega
      have hzm : z.toNat < ({ s with core := { s.core with mrk := mrk_z } } :
          FullState).core.mrk.length := by dsimp only; rw [hml_z]; omega
      ml_lets; ml_st m_z', hm_z' := c0_store_full_mrk (s := { s with core := { s.core with
        mrk := mrk_z } }) (i := z) ((0 : BitVec 32).setWidth 8) hzm hm_z
      have hz1 : (z + 1).toNat = z.toNat + 1 := by bv_omega
      rw [hz8] at hm_z'; ml_lets
      refine hJ1 (s.core.cur_vars - (z + 1).toNat) (z + 1, ()) m_z' (by omega)
        ⟨rfl, by omega, mrk_z.set z.toNat 0#8, by rw [List.length_set, hml_z],
         fun w hw => by rw [List.getElem?_set_ne (by omega)]; exact hab_z w hw,
         fun w hw => ?_, hm_z'⟩
      by_cases hwe : w = z.toNat
      · subst w; rw [List.getElem?_set_self (by omega)]; rfl
      · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hz0 w (by omega)
    · c0_cond hge; have hze : z.toNat = s.core.cur_vars := by bv_omega; ml_lets
      exact hJs () mz ⟨mrk_z, hml_z, hab_z, fun w hw => hz0 w (hze ▸ hw), hm_z⟩
  · c0_cond hnf; have hnf' : s.core.min_clr_full = 0#64 := hnf; ml_ld load_full_min_clr_ptr hm_in
    refine wp_loop_group (ts := [i64]) (fun n (z, ()) mz =>
        n = s.core.min_clr_len - z.toNat ∧ z.toNat ≤ s.core.min_clr_len ∧ ∃ mrk_z,
        mrk_z.length = c.max_vars ∧ (∀ w, s.core.cur_vars ≤ w → mrk_z[w]? = s.core.mrk[w]?) ∧
        (∀ w < s.core.cur_vars, mrk_z[w]?.getD 0#8 ≠ 0#8 →
          ∃ k, z.toNat ≤ k ∧ k < s.core.min_clr_len ∧ (s.core.min_clr[k]?.getD 0#32).toNat = w) ∧
        (FullMem c { s with core := { s.core with mrk := mrk_z } } ⋆ R) mz) ?_
      (fun J1 hJ1 => by
        ml_lets; refine hJ1 (s.core.min_clr_len - 0) (0#64, ()) m
          ⟨by rw [h0v], by rw [h0v]; exact Nat.zero_le _, s.core.mrk, hlen.mrk_len,
           fun _ _ => rfl, fun w hw hnz => ?_, hm_in⟩
        obtain ⟨k, hk, hke⟩ :=
          hmin.clr_cov hnf' w hw ((fullMinMarkInv_mrk_ne_zero_iff hmin hno8 hw).mp hnz)
        exact ⟨k, by rw [h0v]; exact Nat.zero_le _, hk, hke⟩)
    rintro J1 n ⟨z, ⟨⟩⟩ mz hJ1 ⟨rfl, hzle, mrk_z, hml_z, hab_z, hcov_z, hm_z⟩
    let st_z : FullState := { s with core := { s.core with mrk := mrk_z } }
    rw [Blocks.get_here]; ml_ld load_full_min_clr_len (s := st_z) hm_z; ml_lets; ml_jnz
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have hzm : z.toNat < s.core.min_clr_len := by
        rw [BitVec.ult, decide_eq_true_eq, hmcl_bv] at hlt; exact hlt
      have hzl : z.toNat < st_z.core.min_clr.length := by
        dsimp only [st_z]; rw [hmcl_arr]; exact lt_of_lt_of_le hzm hmcl_le
      ml_ld c0_load_full_min_clr (s := st_z) (i := z) hzl hm_z
      let v32 := s.core.min_clr[z.toNat]'hzl
      have hz1 : (z + 1).toNat = z.toNat + 1 := by bv_omega
      refine wp_join_group (ts := []) (fun () mn => ∃ mrk_n,
          mrk_n.length = c.max_vars ∧ (∀ w, s.core.cur_vars ≤ w → mrk_n[w]? = s.core.mrk[w]?) ∧
          (∀ w < s.core.cur_vars, mrk_n[w]?.getD 0#8 ≠ 0#8 → ∃ k, z.toNat + 1 ≤ k ∧
            k < s.core.min_clr_len ∧ (s.core.min_clr[k]?.getD 0#32).toNat = w) ∧
          (FullMem c { s with core := { s.core with mrk := mrk_n } } ⋆ R) mn)
        (fun _ ⟨⟩ mn ⟨mrk_n, hml_n, hab_n, hcov_n, hm_n⟩ => by
          rw [Blocks.get_here]; ml_lets
          exact hJ1 (s.core.min_clr_len - (z + 1).toNat) (z + 1, ()) mn (by omega)
            ⟨rfl, by omega, mrk_n, hml_n, hab_n,
             fun w hw hnz => by rw [hz1]; exact hcov_n w hw hnz, hm_n⟩) ?_
      rintro J2 hJ2; ml_lets; ml_jnz; refine ⟨fun hvlt => ?_, fun hvge => ?_⟩
      · have hvx : (v32.setWidth 64).toNat < s.core.cur_vars := by
          rw [BitVec.ult, decide_eq_true_eq, hcv_bv] at hvlt; exact hvlt
        have hvx' : v32.toNat < s.core.cur_vars := by rwa [bv_c0_zext32_64] at hvx
        have hvm : (v32.setWidth 64).toNat < st_z.core.mrk.length := by
          dsimp only [st_z]; rw [hml_z]; omega
        ml_lets; ml_st mn, hmn := c0_store_full_mrk (s := st_z) (i := v32.setWidth 64)
          ((0 : BitVec 32).setWidth 8) hvm hm_z
        rw [hz8, bv_c0_zext32_64] at hmn; ml_lets
        refine hJ2 () mn ⟨mrk_z.set v32.toNat 0#8, by rw [List.length_set, hml_z],
          fun w hw => by rw [List.getElem?_set_ne (by omega)]; exact hab_z w hw,
          fun w hw hnz => ?_, hmn⟩
        have hwne : w ≠ v32.toNat := by
          rintro rfl; rw [List.getElem?_set_self (by rw [hml_z]; omega)] at hnz; exact hnz rfl
        rw [List.getElem?_set_ne (Ne.symm hwne)] at hnz
        obtain ⟨k, hk1, hk2, hke⟩ := hcov_z w hw hnz
        have hknz : k ≠ z.toNat := by
          rintro rfl; rw [List.getElem?_eq_getElem hzl, Option.getD_some] at hke
          exact hwne hke.symm
        exact ⟨k, by omega, hk2, hke⟩
      · have hvx : s.core.cur_vars ≤ v32.toNat := by
          rw [BitVec.ult, decide_eq_false_iff_not, not_lt, bv_c0_zext32_64, hcv_bv] at hvge
          exact hvge
        ml_lets; refine hJ2 () mz ⟨mrk_z, hml_z, hab_z, fun w hw hnz => ?_, hm_z⟩
        obtain ⟨k, hk1, hk2, hke⟩ := hcov_z w hw hnz
        have hknz : k ≠ z.toNat := by
          rintro rfl; dsimp only [v32] at hvx
          rw [List.getElem?_eq_getElem hzl, Option.getD_some] at hke; dsimp only [st_z] at hke
          omega
        exact ⟨k, by omega, hk2, hke⟩
    · have hze : z.toNat = s.core.min_clr_len := by
        rw [BitVec.ult, decide_eq_false_iff_not, hmcl_bv] at hge; omega
      ml_lets; refine hJs () mz ⟨mrk_z, hml_z, hab_z, fun w hw => ?_, hm_z⟩
      by_cases hz : mrk_z[w]?.getD 0#8 = 0#8; · exact hz
      exfalso; obtain ⟨k, hk1, hk2, _⟩ := hcov_z w hw hz; omega

private def minShrinkCompactExpr (p ld ld_1 ld_3 : Val i64) : Expr Val Cont [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk c (a, b, ())
  .group (sig := [[i64, i64]]) (fun Js => .cons (fun p_17 =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_17.snd.fst, .var ld_1, ())) fun p_18 =>
    .jnz (.var p_18.fst)
      (.group (sig := [[i64]]) (fun _ => .cons (fun p =>
        .let_ (op64 (.add i64) (.var p_17.snd.fst) (.imm 1)) fun p_19 =>
        .jump Js.fst (.var p.fst, .var p_19.fst, ())) .nil) fun Js =>
       .let_ (op64 (.mul i64) (.var p_17.snd.fst) (.imm 4)) fun p =>
       .let_ (op64 (.add i64) (.var ld_3) (.var p.fst)) fun p =>
       .load i32 (.var p.fst) fun ld =>
       .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var ld, .imm 4294967295, ())) fun p =>
       .jnz (.var p.fst)
         (.let_ (op64 (.mul i64) (.var p_17.fst) (.imm 4)) fun p =>
          .let_ (op64 (.add i64) (.var ld_3) (.var p.fst)) fun p =>
          .let_ (op64 (.mul i64) (.var p_17.snd.fst) (.imm 4)) fun p_19 =>
          .let_ (op64 (.add i64) (.var ld_3) (.var p_19.fst)) fun p_20 =>
          .load i32 (.var p_20.fst) fun ld =>
          .store (.var ld) (.var p.fst)
            (.let_ (op64 (.add i64) (.var p_17.fst) (.imm 1)) fun p =>
             .jump Js.fst (.var p.fst, ())))
         (.jump Js.fst (.var p_17.fst, ())))
      (.let_ (op64 (.add i64) (.var p) (.imm 72)) fun p_19 =>
       .load i64 (.var p_19.fst) fun ld_6 =>
       minShrinkCleanExpr p ld ld_1 ld_6 p_17.fst)) .nil)
    fun Js => .jump Js.fst (.imm 1, .imm 1, ())

private theorem min_shrink_compact_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost} (hcore : FullOtfsCoreInv c F0 s)
    (htl1 : 1 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hmin_in : FullMinMarkInv s.core
      (((s.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hno8 : ∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (h0_ok : s.core.tmp[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hns_ok : ∀ k, 1 ≤ k → k < s.core.tmp_len → s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level)
    (hns_sort : ∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
      s.core.tmp[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      s.core.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[(s.core.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    {m : Mem 64} (hm_in : (FullMem c s ⋆ R) m)
    (hpost : ∀ (tmp' : List (BitVec 32)) (tl' : Nat) (mrk' : List (BitVec 8)) (m' : Mem 64),
      let sc' := { s.scratch with
        min_removed := s.scratch.min_removed +
          (BitVec.ofNat 64 s.core.tmp_len - BitVec.ofNat 64 tl'),
        learned_lits := s.scratch.learned_lits + BitVec.ofNat 64 tl' }
      let s' : FullState := {
        core := { s.core with tmp := tmp', mrk := mrk', min_clr_len := 0, min_clr_full := 0#64,
                              tmp_len := tl' }
        scratch := sc' }
      tmp'.length = c.max_vars → mrk'.length = c.max_vars →
      (∀ w, s.core.cur_vars ≤ w → mrk'[w]? = s.core.mrk[w]?) → FullMarksClear s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
        lv < s.core.cur_level ∧
        lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (∀ i j, 1 ≤ i → i ≤ j → j < tl' →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      tmp'.take tl' = (s.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (minShrinkCompactExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      (BitVec.ofNat 64 s.core.tmp_len) c.pTmp) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlen := hcore.1.core_ok; have hcv := hlen.cur_vars_le
  have htl_bv : (BitVec.ofNat 64 s.core.tmp_len).toNat = s.core.tmp_len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1v : (1#64 : BitVec 64).toNat = 1 := rfl
  dsimp only [minShrinkCompactExpr]
  refine wp_loop_group (ts := [i64, i64]) (fun n (kp, k, ()) mk =>
      n = s.core.tmp_len - k.toNat ∧ 1 ≤ kp.toNat ∧ kp.toNat ≤ k.toNat ∧
      k.toNat ≤ s.core.tmp_len ∧ ∃ tmp_k, tmp_k.length = c.max_vars ∧
      tmp_k[0]? = s.core.tmp[0]? ∧
      tmp_k.take kp.toNat = (s.core.tmp.take k.toNat).filter (· ≠ 0xFFFFFFFF#32) ∧
      (∀ j, k.toNat ≤ j → j < s.core.tmp_len → tmp_k[j]? = s.core.tmp[j]?) ∧
      (∀ j, 1 ≤ j → j < kp.toNat →
        let l := (tmp_k[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level) ∧
      (∀ a b, 1 ≤ a → a ≤ b → b < kp.toNat →
        (s.core.lvl[(tmp_k[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp_k[b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (∀ a, 1 ≤ a → a < kp.toNat → ∀ j, k.toNat ≤ j → j < s.core.tmp_len →
        s.core.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        (s.core.lvl[(tmp_k[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (FullMem c { s with core := { s.core with tmp := tmp_k } } ⋆ R) mk) ?_
    (fun Js hJs => by
      ml_lets; have h0lt : 0 < s.core.tmp.length := by rw [hlen.tmp_len_arr]; omega
      have htake1 : s.core.tmp.take 1 = [s.core.tmp[0]'h0lt] := by
        simpa using List.take_succ_eq_append_getElem (i := 0) h0lt
      have h0ne : (s.core.tmp[0]'h0lt) ≠ 0xFFFFFFFF#32 := by
        rwa [List.getElem?_eq_getElem h0lt, Option.getD_some] at h0_ok
      exact hJs (s.core.tmp_len - 1) (1#64, 1#64, ()) m
        ⟨by rw [h1v], by rw [h1v]; exact le_refl _, by rw [h1v]; exact le_refl _, htl1,
         s.core.tmp, hlen.tmp_len_arr, rfl, by rw [h1v, htake1]; simp [h0ne], fun _ _ _ => rfl,
         fun _ h1 h2 => by rw [h1v] at h2; omega, fun _ _ _ _ h => by rw [h1v] at h; omega,
         fun _ _ h => by rw [h1v] at h; omega, hm_in⟩)
  rintro Js n ⟨kp, k, ⟨⟩⟩ mk hJs
    ⟨rfl, hkp1, hkpk, hkle, tmp_k, htkl, htk0, htk_f, htk_r, htk_l, htk_s, htk_c, hm_k⟩
  let st_k : FullState := { s with core := { s.core with tmp := tmp_k } }
  rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · have hkx : k.toNat < s.core.tmp_len := by
      rw [BitVec.ult, decide_eq_true_eq, htl_bv] at hlt; exact hlt
    have hk_tl : k.toNat < st_k.core.tmp.length := by dsimp only [st_k]; rw [htkl]; omega
    have hkp_tl : kp.toNat < st_k.core.tmp.length := by dsimp only [st_k]; rw [htkl]; omega
    have hk_eq : tmp_k[k.toNat]? = s.core.tmp[k.toNat]? := htk_r k.toNat (le_refl _) hkx
    have hk1 : (k + 1).toNat = k.toNat + 1 := by bv_omega
    have htake_k : s.core.tmp.take (k.toNat + 1) = s.core.tmp.take k.toNat ++
        [s.core.tmp[k.toNat]'(by rw [hlen.tmp_len_arr]; omega)] :=
      List.take_succ_eq_append_getElem (by rw [hlen.tmp_len_arr]; omega)
    refine wp_join_group (ts := [i64]) (fun (kp', ()) mk' =>
        1 ≤ kp'.toNat ∧ kp'.toNat ≤ k.toNat + 1 ∧ ∃ tmp_n, tmp_n.length = c.max_vars ∧
        tmp_n[0]? = s.core.tmp[0]? ∧
        tmp_n.take kp'.toNat = (s.core.tmp.take (k.toNat + 1)).filter (· ≠ 0xFFFFFFFF#32) ∧
        (∀ j, k.toNat + 1 ≤ j → j < s.core.tmp_len → tmp_n[j]? = s.core.tmp[j]?) ∧
        (∀ j, 1 ≤ j → j < kp'.toNat →
          let l := (tmp_n[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          0 < lv ∧ lv < s.core.cur_level) ∧
        (∀ a b, 1 ≤ a → a ≤ b → b < kp'.toNat →
          (s.core.lvl[(tmp_n[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(tmp_n[b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
        (∀ a, 1 ≤ a → a < kp'.toNat → ∀ j, k.toNat + 1 ≤ j → j < s.core.tmp_len →
          s.core.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(tmp_n[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
        (FullMem c { s with core := { s.core with tmp := tmp_n } } ⋆ R) mk')
      (fun _ ⟨kp', ⟨⟩⟩ mk'
          ⟨hkp'1, hkp'k, tmp_n, htnl, htn0, htn_f, htn_r, htn_l, htn_s, htn_c, hm_n⟩ => by
        rw [Blocks.get_here]; ml_lets
        exact hJs (s.core.tmp_len - (k + 1).toNat) (kp', k + 1, ()) mk' (by omega)
          ⟨rfl, hkp'1, by omega, by omega, tmp_n, htnl, htn0, by rw [hk1]; exact htn_f,
           fun j hj => htn_r j (by omega), htn_l, htn_s,
           fun a ha1 ha2 j hj => htn_c a ha1 ha2 j (by omega), hm_n⟩) ?_
    rintro J1 hJ1; ml_ld c0_load_full_tmp (s := st_k) (i := k) hk_tl hm_k; ml_lets; ml_jnz
    refine ⟨fun hne => ?_, fun heq => ?_⟩
    · have hne' : tmp_k[k.toNat]'hk_tl ≠ 0xFFFFFFFF#32 := bne_iff_ne.mp hne
      ml_ld c0_load_full_tmp (s := st_k) (i := k) hk_tl hm_k; ml_lets
      ml_st m_n, hm_n := c0_store_full_tmp (s := st_k) (i := kp) (tmp_k[k.toNat]'hk_tl)
        hkp_tl hm_k
      have hkp1' : (kp + 1).toNat = kp.toNat + 1 := by bv_omega
      have hkne : s.core.tmp[k.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        rw [← hk_eq, List.getElem?_eq_getElem hk_tl, Option.getD_some]; exact hne'
      have hktl : k.toNat < s.core.tmp.length := by rw [hlen.tmp_len_arr]; omega
      have hk_get : s.core.tmp[k.toNat]?.getD 0#32 = s.core.tmp[k.toNat]'hktl := by
        rw [List.getElem?_eq_getElem hktl, Option.getD_some]
      have hval_k := hns_ok k.toNat (by omega) hkx hkne
      have hkv_eq : tmp_k[k.toNat]'hk_tl = s.core.tmp[k.toNat]'hktl := by
        rw [List.getElem?_eq_getElem hk_tl, List.getElem?_eq_getElem hktl] at hk_eq
        exact Option.some.inj hk_eq
      let tmp_n := tmp_k.set kp.toNat (tmp_k[k.toNat]'hk_tl)
      have hset_k : tmp_n[kp.toNat]?.getD 0#32 = s.core.tmp[k.toNat]?.getD 0#32 := by
        dsimp only [tmp_n]; rw [List.getElem?_set_self (by rw [htkl]; omega),
          Option.getD_some, hkv_eq, hk_get]
      have htn_l : ∀ j, 1 ≤ j → j < (kp + 1).toNat →
          let l := (tmp_n[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          0 < lv ∧ lv < s.core.cur_level := by
        intro j hj1 hj2; dsimp only [tmp_n]; rw [hkp1'] at hj2; by_cases hje : j = kp.toNat
        · subst j; simpa [tmp_n, hset_k] using hval_k
        · rw [List.getElem?_set_ne (Ne.symm hje)]; exact htk_l j hj1 (by omega)
      have htn_s : ∀ a b, 1 ≤ a → a ≤ b → b < (kp + 1).toNat →
          (s.core.lvl[(tmp_n[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(tmp_n[b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
        intro a b ha1 hab hb2; dsimp only [tmp_n]; rw [hkp1'] at hb2; by_cases hbe : b = kp.toNat
        · subst b; by_cases hae : a = kp.toNat
          · subst a; exact le_refl _
          · have h1 := htk_c a ha1 (by omega) k.toNat (le_refl _) hkx hkne
            rw [List.getElem?_set_ne (Ne.symm hae)]; simpa [tmp_n, hset_k] using h1
        · rw [List.getElem?_set_ne (Ne.symm hbe), List.getElem?_set_ne (by omega)]
          exact htk_s a b ha1 hab (by omega)
      have htn_c : ∀ a, 1 ≤ a → a < (kp + 1).toNat → ∀ j, k.toNat + 1 ≤ j → j < s.core.tmp_len →
          s.core.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(tmp_n[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
        intro a ha1 ha2 j hj1 hj2 hjne; dsimp only [tmp_n]; rw [hkp1'] at ha2
        by_cases hae : a = kp.toNat
        · subst a; simpa [tmp_n, hset_k] using
            hns_sort k.toNat j (by omega) (by omega) hj2 hkne hjne
        · rw [List.getElem?_set_ne (Ne.symm hae)]
          exact htk_c a ha1 (by omega) j (by omega) hj2 hjne
      ml_lets; have hne_s : s.core.tmp[k.toNat]'hktl ≠ 0xFFFFFFFF#32 := hkv_eq ▸ hne'
      refine hJ1 (kp + 1, ()) m_n ⟨by omega, by omega, tmp_n, by rw [List.length_set, htkl],
        by rw [List.getElem?_set_ne (by omega)]; exact htk0, ?_, ?_, htn_l, htn_s, htn_c, hm_n⟩
      · rw [hkp1', htake_k, List.filter_append, list_take_succ_set _ (by omega), htk_f, hkv_eq]
        simp [hne_s]
      · intro j hj1 hj2; dsimp only [tmp_n]
        rw [List.getElem?_set_ne (by omega)]; exact htk_r j (by omega) hj2
    · ml_lets; have heq' : tmp_k[k.toNat]'hk_tl = 0xFFFFFFFF#32 := bne_eq_false_iff_eq.mp heq
      have hkeq : s.core.tmp[k.toNat]'(by rw [hlen.tmp_len_arr]; omega) = 0xFFFFFFFF#32 := by
        rw [List.getElem?_eq_getElem hk_tl,
          List.getElem?_eq_getElem (by rw [hlen.tmp_len_arr]; omega)] at hk_eq
        exact (Option.some.inj hk_eq) ▸ heq'
      refine hJ1 (kp, ()) mk ⟨hkp1, by omega, tmp_k, htkl, htk0, ?_, ?_, htk_l, htk_s, ?_, hm_k⟩
      · rw [htake_k, List.filter_append, htk_f]; simp [hkeq]
      · intro j hj1 hj2; exact htk_r j (by omega) hj2
      · intro a ha1 ha2 j hj1 hj2 hjne; exact htk_c a ha1 ha2 j (by omega) hj2 hjne
  · have hke : k.toNat = s.core.tmp_len := by
      rw [BitVec.ult, decide_eq_false_iff_not, htl_bv] at hge; omega
    rw [hke] at htk_f hkpk; ml_ld load_full_mark_ptr (s := st_k) hm_k
    have hmin_k : FullMinMarkInv st_k.core
        (((tmp_k.take kp.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := by
      have hflt_eq : (tmp_k.take kp.toNat).filter (· ≠ 0xFFFFFFFF#32) = tmp_k.take kp.toNat :=
        List.filter_eq_self.mpr fun x hx => by rw [htk_f, List.mem_filter] at hx; exact hx.2
      rw [hflt_eq, htk_f]; exact ⟨hmin_in.mrk_dom, hmin_in.clr_cov, hmin_in.rem_sound⟩
    have hcore_k : FullOtfsCoreInv c F0 st_k :=
      fullOtfsCoreInv_with_min_tmp hcore htkl hlen.tmp_len_le hlen.mrk_len hlen.min_stk_len
        hlen.min_clr_len_arr hlen.min_clr_len_le hcore.1.scratch_ok
    refine min_shrink_clean_wp hcore_k hm_k hmin_k hno8 fun mrk' m' hml hab hmc hm' => ?_
    refine hpost tmp_k kp.toNat mrk' m' htkl hml hab hmc hkp1 hkpk htk0 ?_ htk_s htk_f ?_
    · intro j hj1 hj2; have hjv := htk_l j hj1 hj2
      exact ⟨hjv.1, hjv.2.1, hjv.2.2.1, hjv.2.2.2, htk_s j (kp.toNat - 1) hj1 (by omega) (by omega)⟩
    · simpa [bv_ofNat_toNat_eq kp] using hm'

/-! ## 3. Outer block loop sub-expression (`minShrinkOuterExpr`) -/

private def minShrinkOuterExpr (p ld ld_1 ld_3 ld_4 ld_5 : Val i64) : Expr Val Cont [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) := Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Js0 => .cons (fun p_15 =>
    .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var p_15.fst, .imm 1, ())) fun p_16 =>
    .jnz (.var p_16.fst)
      (.let_ (op64 (.sub i64) (.var p_15.fst) (.imm 1)) fun p_17 =>
       .let_ (op64 (.mul i64) (.var p_17.fst) (.imm 4)) fun p_18 =>
       .let_ (op64 (.add i64) (.var ld_3) (.var p_18.fst)) fun p_19 =>
       .load i32 (.var p_19.fst) fun ld =>
       .let_ (Op.mk (.lshr i32) (.var ld, .imm 1, ())) fun p_20 =>
       .let_ (Op.mk (.zext 32 64) (.var p_20.fst, ())) fun p_21 =>
       .let_ (op64 (.mul i64) (.var p_21.fst) (.imm 4)) fun p_22 =>
       .let_ (op64 (.add i64) (.var ld_4) (.var p_22.fst)) fun p_23 =>
       .load i32 (.var p_23.fst) fun ld =>
       .let_ (op64 (.mul i64) (.var p_17.fst) (.imm 4)) fun p_24 =>
       .let_ (op64 (.add i64) (.var ld_3) (.var p_24.fst)) fun p_25 =>
       .load i32 (.var p_25.fst) fun ld_6 =>
       .let_ (Op.mk (.lshr i32) (.var ld_6, .imm 1, ())) fun p_26 =>
       .let_ (Op.mk (.zext 32 64) (.var p_26.fst, ())) fun p_27 =>
       .let_ (op64 (.mul i64) (.var p_27.fst) (.imm 4)) fun p_28 =>
       .let_ (op64 (.add i64) (.var ld_5) (.var p_28.fst)) fun p_29 =>
       .load i32 (.var p_29.fst) fun ld_7 =>
       .let_ (Op.mk (.zext 32 64) (.var ld_7, ())) fun p_30 =>
       .group (sig := [[i64, i64]]) (fun Js_1 => .cons (fun p_31 =>
         .group (sig := [[]]) (fun _ => .cons (fun _ =>
           .group (sig := [[]]) (fun _ => .cons (fun _ =>
             .jump Js0.fst (.var p_31.fst, ())) .nil) fun Js =>
           .let_ (op64 (.sub i64) (.var p_15.fst) (.var p_31.fst)) fun p_33 =>
           .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var p_33.fst, .imm 1, ())) fun p_34 =>
           .jnz (.var p_34.fst)
             (.group (sig := [[]]) (fun _ => .cons (fun _ => .jump Js.fst ()) .nil) fun Js =>
              .let_ (op64 (.mul i64) (.var p_31.fst) (.imm 4)) fun p_35 =>
              .let_ (op64 (.add i64) (.var ld_3) (.var p_35.fst)) fun p_36 =>
              .load i32 (.var p_36.fst) fun ld =>
              .call "full_min_lit" (as := [i64, i32]) (bs := [.bool])
                (.var p, .var ld, ()) fun p =>
              .jnz (.var p.fst)
                (.let_ (op64 (.mul i64) (.var p_31.fst) (.imm 4)) fun p =>
                 .let_ (op64 (.add i64) (.var ld_3) (.var p.fst)) fun p =>
                 .store (t := i32) (.imm 4294967295) (.var p.fst) (.jump Js.fst ()))
                (.jump Js.fst ()))
             (.call "full_shrink_blk" (as := [i64, i64, i64, i32, i64]) (bs := [])
                (.var p, .var p_31.fst, .var p_15.fst, .var ld,
                 .var p_31.snd.fst, ()) fun _ => .jump Js.fst ())) .nil) fun Js =>
         .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var p_31.fst, .imm 1, ())) fun p =>
         .jnz (.var p.fst)
           (.let_ (op64 (.sub i64) (.var p_31.fst) (.imm 1)) fun p =>
            .let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
            .let_ (op64 (.add i64) (.var ld_3) (.var p.fst)) fun p =>
            .load i32 (.var p.fst) fun ld_8 =>
            .let_ (Op.mk (.lshr i32) (.var ld_8, .imm 1, ())) fun p =>
            .let_ (Op.mk (.zext 32 64) (.var p.fst, ())) fun p =>
            .let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
            .let_ (op64 (.add i64) (.var ld_4) (.var p.fst)) fun p =>
            .load i32 (.var p.fst) fun ld_9 =>
            .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var ld_9, .var ld, ())) fun p =>
            .jnz (.var p.fst)
              (.let_ (op64 (.sub i64) (.var p_31.fst) (.imm 1)) fun p =>
               .let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun p_32 =>
               .let_ (op64 (.add i64) (.var ld_3) (.var p_32.fst)) fun p_33 =>
               .load i32 (.var p_33.fst) fun ld =>
               .let_ (Op.mk (.lshr i32) (.var ld, .imm 1, ())) fun p_34 =>
               .let_ (Op.mk (.zext 32 64) (.var p_34.fst, ())) fun p_35 =>
               .let_ (op64 (.mul i64) (.var p_35.fst) (.imm 4)) fun p_36 =>
               .let_ (op64 (.add i64) (.var ld_5) (.var p_36.fst)) fun p_37 =>
               .load i32 (.var p_37.fst) fun ld =>
               .let_ (Op.mk (.zext 32 64) (.var ld, ())) fun p_38 =>
               .group (sig := [[i64]]) (fun _ => .cons (fun p_39 =>
                 .jump Js_1.fst (.var p.fst, .var p_39.fst, ())) .nil) fun Js =>
               .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var p_38.fst, .var p_31.snd.fst, ()))
                 fun p =>
               .jnz (.var p.fst) (.jump Js.fst (.var p_38.fst, ()))
                 (.jump Js.fst (.var p_31.snd.fst, ())))
              (.jump Js.fst ()))
           (.jump Js.fst ())) .nil)
         fun Js => .jump Js.fst (.var p_17.fst, .var p_30.fst, ()))
      (minShrinkCompactExpr p ld ld_1 ld_3)) .nil)
    fun Js => .jump Js.fst (.var ld_1, ())

private abbrev outerState (s : FullState) (tmp : List (BitVec 32)) (mrk : List (BitVec 8))
    (mstk mclr sstk : List (BitVec 32)) (mcl : Nat) (mcf : BitVec 64) : FullState :=
  { core := { s.core with
      tmp, mrk, min_stk := mstk, min_clr := mclr, min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with shrink_stk := sstk } }

private abbrev minShrinkRes (s : FullState) (tmp : List (BitVec 32)) (tl : Nat)
    (mrk : List (BitVec 8)) (mstk mclr sstk : List (BitVec 32)) (mcl : Nat)
    (mcf conf llits mrem : BitVec 64) : FullState :=
  { core := { s.core with
      tmp, tmp_len := tl, mrk, min_stk := mstk, min_clr := mclr,
      min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with
      conflicts := conf, learned_lits := llits, min_removed := mrem, shrink_stk := sstk } }

private structure OuterInv (c : FullCfg) (F0 : CNF Nat) (s : FullState)
    (tmp1 : List (BitVec 32)) (end_b : Nat) (cur : FullState) : Prop where
  core : FullOtfsCoreInv c F0 cur
  min_inv : FullMinMarkInv cur.core
    (((cur.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)
  entails : ∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
    FullOtfsWitnessInv c F0 F_cur cur.core ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      (((cur.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
  nodup : ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup →
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
        (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
    (((cur.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map
      fun x => x.toNat / 2).Nodup
  mrk_above : ∀ v, s.core.cur_vars ≤ v → cur.core.mrk[v]? = s.core.mrk[v]?
  no8 : ∀ v < s.core.cur_vars, (cur.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8
  cv_eq : cur.core.cur_vars = s.core.cur_vars
  tl_eq : cur.core.tmp_len = s.core.tmp_len
  lvl_eq : cur.core.lvl = s.core.lvl
  vals_eq : cur.core.vals = s.core.vals
  clvl_eq : cur.core.cur_level = s.core.cur_level
  tpos_eq : cur.core.trail_pos = s.core.trail_pos
  prefix_eq : ∀ k < end_b, cur.core.tmp[k]? = tmp1[k]?
  rem_mrk : ∀ k < s.core.tmp_len, cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    let l := (cur.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
    (cur.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8
  post_lvls : ∀ k, 1 ≤ k → k < s.core.tmp_len →
    cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    let l := (cur.core.tmp[k]?.getD 0#32).toNat
    0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
    (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧
    (s.core.lvl[l / 2]?.getD 0#32).toNat =
      (s.core.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  blk_gt : ∀ k, end_b ≤ k → k < s.core.tmp_len → 1 < end_b →
    cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    (s.core.lvl[(tmp1[end_b - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      (s.core.lvl[(cur.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

private theorem min_shrink_lit_step {c : FullCfg} {F0 : CNF Nat} {s cur : FullState}
    {tmp1 : List (BitVec 32)} {beg : Nat} (ho : OuterInv c F0 s tmp1 (beg + 1) cur)
    (hbeg_tl : beg < s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    {root_lit : BitVec 32} (hroot_eq : cur.core.tmp[beg]? = some root_lit)
    (hroot_ne : root_lit ≠ 0xFFFFFFFF#32)
    (hbeg_lt : 1 < beg →
      (s.core.lvl[(tmp1[beg - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat)
    {ok : Bool} {mrk' : List (BitVec 8)} {mstk' mclr' : List (BitVec 32)}
    {mcl' : Nat} {mcf' : BitVec 64}
    (hlen' : (minLitState cur mrk' mstk' mclr' mcl' mcf').LengthsOk c)
    (hab' : ∀ v, cur.core.cur_vars ≤ v → mrk'[v]? = cur.core.mrk[v]?)
    (hmono2 : ∀ v < cur.core.cur_vars,
      (cur.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8 : ∀ v < cur.core.cur_vars,
      (mrk'[v]?.getD 0#8 &&& 8#8) = (cur.core.mrk[v]?.getD 0#8 &&& 8#8))
    (hmin' : FullMinMarkInv (minLitState cur mrk' mstk' mclr' mcl' mcf').core
      (((cur.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hok_true : ok = true →
      (∀ keep', (∀ l ∈ (((cur.core.tmp.take s.core.tmp_len).filter
            (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat), l = root_lit.toNat ∨ l ∈ keep') →
        FullMinMarkInv (minLitState cur mrk' mstk' mclr' mcl' mcf').core keep') ∧
      FullMinMarkInv (fullMinMarkState (minLitState cur mrk' mstk' mclr' mcl' mcf')
          (root_lit.toNat / 2) 2#8).core
        (((cur.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) :
    let tmp_n := if ok then cur.core.tmp.set beg 0xFFFFFFFF#32 else cur.core.tmp
    let st_n : FullState := { cur with core := { cur.core with
      tmp := tmp_n, mrk := mrk', min_stk := mstk', min_clr := mclr',
      min_clr_len := mcl', min_clr_full := mcf' } }
    OuterInv c F0 s tmp1 beg st_n := by
  have hcv := ho.core.1.core_ok.cur_vars_le
  have hcv_s : s.core.cur_vars ≤ c.max_vars := ho.cv_eq ▸ hcv
  have hbeg_s : beg + 1 - 1 = beg := Nat.add_sub_cancel beg 1
  have hrm_b : cur.core.tmp[beg]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    rw [hroot_eq, Option.getD_some]; exact hroot_ne
  have hrb := ho.rem_mrk beg hbeg_tl hrm_b
  have hr_nat : (cur.core.tmp[beg]?.getD 0#32).toNat = root_lit.toNat := by
    rw [hroot_eq, Option.getD_some]
  have htmp1_beg : (tmp1[beg]?.getD 0#32).toNat = root_lit.toNat := by
    rw [← ho.prefix_eq beg (by omega)]; exact hr_nat
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨fullOtfsCoreInv_with_min ho.core hlen'.core_ok.mrk_len hlen'.core_ok.min_stk_len
        hlen'.core_ok.min_clr_len_arr hlen'.core_ok.min_clr_len_le,
      by simpa [ho.tl_eq] using hmin', fun F_cur hw hEnt0 =>
        let ⟨hwc, hEc⟩ := ho.entails F_cur hw hEnt0; ⟨fullOtfsWitness_with_min hwc, hEc⟩,
      ho.nodup, fun v hv => (hab' v (by rw [ho.cv_eq]; exact hv)).trans (ho.mrk_above v hv),
      fun v hv => by rw [hbit8 v (by rw [ho.cv_eq]; exact hv)]; exact ho.no8 v hv,
      ho.cv_eq, ho.tl_eq, ho.lvl_eq, ho.vals_eq, ho.clvl_eq, ho.tpos_eq,
      fun k hk => ho.prefix_eq k (by omega), fun k hk hne => by
        have hrk := ho.rem_mrk k hk hne
        exact ⟨hrk.1, hrk.2.1,
          hmono2 ((cur.core.tmp[k]?.getD 0#32).toNat / 2) (by rw [ho.cv_eq]; omega) hrk.2.2⟩,
      ho.post_lvls, fun k hk1 hk2 hb1 hne => ?_⟩
    · by_cases hkb : k = beg
      · subst k; rw [hr_nat]; exact hbeg_lt hb1
      · have hbt := ho.blk_gt k (by omega) hk2 (by omega) hne; rw [hbeg_s] at hbt
        exact Nat.lt_trans (by rw [htmp1_beg]; exact hbeg_lt hb1) hbt
  | true =>
    dsimp only; let tmp_n := cur.core.tmp.set beg 0xFFFFFFFF#32
    let st_base := minLitState cur mrk' mstk' mclr' mcl' mcf'
    let st_n : FullState := { st_base with core := { st_base.core with tmp := tmp_n } }
    have htl_n : tmp_n.length = c.max_vars := by
      dsimp only [tmp_n]; rw [List.length_set, ho.core.1.core_ok.tmp_len_arr]
    have hcore_n : FullOtfsCoreInv c F0 st_n := fullOtfsCoreInv_with_min_tmp ho.core htl_n
      ho.core.1.core_ok.tmp_len_le hlen'.core_ok.mrk_len hlen'.core_ok.min_stk_len
      hlen'.core_ok.min_clr_len_arr hlen'.core_ok.min_clr_len_le ho.core.1.scratch_ok
    let keep' := ((tmp_n.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    have hsub : ∀ l ∈ (((cur.core.tmp.take s.core.tmp_len).filter
        (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat), l = root_lit.toNat ∨ l ∈ keep' := by
      intro l hl; rw [mem_filter_map_toNat_take] at hl; obtain ⟨k, hk, b, hkb, hne, rfl⟩ := hl
      by_cases hke : k = beg
      · subst k; rw [hkb] at hroot_eq; left; exact congrArg BitVec.toNat (Option.some.inj hroot_eq)
      · right; exact mem_filter_map_toNat_take.mpr ⟨k,
          by dsimp only [tmp_n]; rw [List.length_set]; exact hk, b,
          by dsimp only [tmp_n]; rw [List.getElem?_set_ne (Ne.symm hke)]; exact hkb, hne, rfl⟩
    have hmin_base : FullMinMarkInv st_base.core keep' := (hok_true rfl).1 keep' hsub
    have hmin_n : FullMinMarkInv st_n.core keep' :=
      ⟨hmin_base.mrk_dom, hmin_base.clr_cov, hmin_base.rem_sound⟩
    have hent_n : ∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
        FullOtfsWitnessInv c F0 F_cur st_n.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause keep') := by
      intro F_cur hw hEnt0; obtain ⟨hwc, hEc⟩ := ho.entails F_cur hw hEnt0
      have hwb : FullOtfsWitnessInv c F0 F_cur st_base.core := fullOtfsWitness_with_min hwc
      refine ⟨fullOtfsWitness_with_min hwc, fullMinMark_entails hwb hmin_base hEc fun l hl => ?_⟩
      rw [mem_filter_map_toNat_take] at hl; obtain ⟨k, hk, b, hkb, hne, rfl⟩ := hl
      have hrk := ho.rem_mrk k (lt_of_lt_of_le hk (Nat.min_le_left _ _))
        (by rw [hkb, Option.getD_some]; exact hne)
      have hbk : (cur.core.tmp[k]?.getD 0#32).toNat = b.toNat := by rw [hkb, Option.getD_some]
      rw [hbk] at hrk
      refine ⟨by dsimp only [st_base]; rw [ho.cv_eq]; exact hrk.1,
        by dsimp only [st_base]; rw [ho.vals_eq]; exact hrk.2.1, ?_⟩
      rcases hsub b.toNat (mem_filter_map_toNat_take.mpr ⟨k, hk, b, hkb, hne, rfl⟩) with
        heqb | hin
      · right; rw [heqb, ← hr_nat]; exact hmono2 _ (by rw [ho.cv_eq, hr_nat]; omega) hrb.2.2
      · exact Or.inl hin
    have htl_lt_c : s.core.tmp_len ≤ cur.core.tmp.length := by
      rw [ho.core.1.core_ok.tmp_len_arr]; omega
    have hbeg_lt' : beg < cur.core.tmp.length := lt_of_lt_of_le hbeg_tl htl_lt_c
    have hnb : ∀ k, tmp_n[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 → k ≠ beg := fun k hk => by
      rintro rfl; exact hk (by dsimp only [tmp_n]; rw [List.getElem?_set_self hbeg_lt']; rfl)
    refine ⟨hcore_n, hmin_n, hent_n,
      fun hnd hne0 => nodup_filter_set_sent htl_lt_c hbeg_tl (ho.nodup hnd hne0),
      fun v hv => (hab' v (by rw [ho.cv_eq]; exact hv)).trans (ho.mrk_above v hv),
      fun v hv => by rw [hbit8 v (by rw [ho.cv_eq]; exact hv)]; exact ho.no8 v hv,
      ho.cv_eq, ho.tl_eq, ho.lvl_eq, ho.vals_eq, ho.clvl_eq, ho.tpos_eq,
      fun k hk => by simp only [↓reduceIte]; rw [List.getElem?_set_ne (by omega)]
                     exact ho.prefix_eq k (by omega),
      fun k hk hne => ?_, fun k hk1 hk2 hne => ?_, fun k hk1 hk2 hb1 hne => ?_⟩
    · simp only [↓reduceIte] at hne ⊢; have hke := Ne.symm (hnb k hne)
      rw [List.getElem?_set_ne hke] at hne ⊢; have hrk := ho.rem_mrk k hk hne
      exact ⟨hrk.1, hrk.2.1,
        hmono2 ((cur.core.tmp[k]?.getD 0#32).toNat / 2) (by rw [ho.cv_eq]; omega) hrk.2.2⟩
    · simp only [↓reduceIte] at hne ⊢; have hke := Ne.symm (hnb k hne)
      rw [List.getElem?_set_ne hke] at hne ⊢; exact ho.post_lvls k hk1 hk2 hne
    · simp only [↓reduceIte] at hne ⊢; have hke := Ne.symm (hnb k hne)
      rw [List.getElem?_set_ne hke] at hne ⊢
      have hbt := ho.blk_gt k (by omega) hk2 (by omega) hne; rw [hbeg_s] at hbt
      exact Nat.lt_trans (by rw [htmp1_beg]; exact hbeg_lt hb1) hbt

private theorem min_shrink_outer_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    (hMl : ∀ args m Q X, fullMinLitSpec args m Q X → Γ "full_min_lit" [i64, i32] [.bool] args m Q X)
    (hSb : ∀ args m Q X, fullShrinkBlkSpec args m Q X →
      Γ "full_shrink_blk" [i64, i64, i64, i32, i64] [] args m Q X)
    {tmp1 : List (BitVec 32)} {s_in : FullState} (ho_in : OuterInv c F0 s tmp1 s.core.tmp_len s_in)
    (ht1_0 : tmp1[0]? = s.core.tmp[0]?)
    (ht1_src : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp1[k]? = s.core.tmp[i]?)
    (htl1 : 1 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (htmp1_sort : ∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
      (s.core.lvl[(tmp1[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(tmp1[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (htmp1_ne : ∀ k < s.core.tmp_len, tmp1[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (htmp1_lvls : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      0 < (s.core.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    {m : Mem 64} (hm_in : (FullMem c s_in ⋆ R) m)
    (hpost : ∀ (tmp' : List (BitVec 32)) (tl' : Nat) (mrk' : List (BitVec 8))
        (mstk' mclr' sstk' : List (BitVec 32)) (mcl' : Nat) (mcf' llits' mrem' : BitVec 64)
        (m' : Mem 64),
      let s' := minShrinkRes s_in tmp' tl' mrk' mstk' mclr' sstk' mcl' mcf'
        s_in.scratch.conflicts llits' mrem'
      tmp'.length = c.max_vars → mrk'.length = c.max_vars → mstk'.length = 2 * c.minDepth →
      mclr'.length = c.max_vars → mcl' ≤ c.max_vars → sstk'.length = c.max_vars →
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) → FullMarksClear s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = tmp1[0]? →
      (((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup →
        (∀ k, 1 ≤ k → k < s.core.tmp_len →
          (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
          (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
        ((tmp'.take tl').map fun x => x.toNat / 2).Nodup) →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
        lv < s.core.cur_level ∧
        lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (∀ i j, 1 ≤ i → i ≤ j → j < tl' →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
        FullOtfsWitnessInv c F0 F_cur s'.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat))) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (minShrinkOuterExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel c.pTrailPos) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := ho_in.core.1.core_ok.cur_vars_le; rw [ho_in.cv_eq] at hcv
  dsimp only [minShrinkOuterExpr]
  refine wp_loop_group (ts := [i64]) (fun n (end_b, ()) me =>
      n = end_b.toNat - 1 ∧ 1 ≤ end_b.toNat ∧ end_b.toNat ≤ s.core.tmp_len ∧
      ∃ (mrk_e : List (BitVec 8)) (tmp_e mstk_e mclr_e sstk_e : List (BitVec 32))
        (mcl_e : Nat) (mcf_e : BitVec 64),
      let cur := outerState s_in tmp_e mrk_e mstk_e mclr_e sstk_e mcl_e mcf_e
      OuterInv c F0 s tmp1 end_b.toNat cur ∧ (FullMem c cur ⋆ R) me) ?_
    (fun Js0 hJs0 => by
      ml_lets; have htl_lt : s.core.tmp_len < 2 ^ 64 := by omega
      have htl_bv : (BitVec.ofNat 64 s.core.tmp_len).toNat = s.core.tmp_len := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl_lt]
      exact hJs0 (s.core.tmp_len - 1) (BitVec.ofNat 64 s.core.tmp_len, ()) m
        ⟨by rw [htl_bv], by rw [htl_bv]; exact htl1, by rw [htl_bv]; exact le_refl _,
         s_in.core.mrk, s_in.core.tmp, s_in.core.min_stk, s_in.core.min_clr,
         s_in.scratch.shrink_stk, s_in.core.min_clr_len, s_in.core.min_clr_full,
         by rw [htl_bv]; exact ho_in, hm_in⟩)
  rintro Js0 n ⟨end_b, ⟨⟩⟩ me hJs0
    ⟨rfl, hend1, hend_tl, mrk_e, tmp_e, mstk_e, mclr_e, sstk_e, mcl_e, mcf_e, ho, hm_e⟩
  let cur := outerState s_in tmp_e mrk_e mstk_e mclr_e sstk_e mcl_e mcf_e
  rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hgt => ?_, fun hle => ?_⟩
  · c0_cond hgt; have h1lt : 1 < end_b.toNat := by bv_omega
    have he1_nat : (end_b - 1).toNat = end_b.toNat - 1 := by bv_omega
    have he1_tl : (end_b - 1).toNat < cur.core.tmp.length := by
      dsimp only [cur]; rw [ho.core.1.core_ok.tmp_len_arr]; omega
    ml_ld c0_load_full_tmp (s := cur) (i := end_b - 1) he1_tl hm_e
    let lit_e1 := cur.core.tmp[(end_b - 1).toNat]'he1_tl
    have he1_t1 : cur.core.tmp[(end_b - 1).toNat]? = tmp1[(end_b - 1).toNat]? :=
      ho.prefix_eq _ (by omega)
    have hne_e1 : cur.core.tmp[(end_b - 1).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rw [he1_t1]; exact htmp1_ne (end_b - 1).toNat (by omega)
    have hl_e1 : lit_e1.toNat < 2 * s.core.cur_vars := by
      have hrm := ho.rem_mrk (end_b - 1).toNat (by omega) hne_e1
      rw [List.getElem?_eq_getElem he1_tl, Option.getD_some] at hrm; exact hrm.1
    have he1_var_lt : (lit_e1 >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr_1]; omega
    have he1_lvl_l : ((lit_e1 >>> 1).setWidth 64).toNat < cur.core.lvl.length := by
      rw [ho.core.1.core_ok.lvl_len, bv_c0_zext32_64]; omega
    ml_ld c0_load_full_lvl (s := cur) (i := (lit_e1 >>> 1).setWidth 64) he1_lvl_l hm_e
    ml_ld c0_load_full_tmp (s := cur) (i := end_b - 1) he1_tl hm_e
    have he1_tp_l : ((lit_e1 >>> 1).setWidth 64).toNat < cur.core.trail_pos.length := by
      rw [ho.core.1.core_ok.trail_pos_len, bv_c0_zext32_64]; omega
    ml_ld c0_load_full_trail_pos (s := cur) (i := (lit_e1 >>> 1).setWidth 64) he1_tp_l hm_e
    let blvl := cur.core.lvl[((lit_e1 >>> 1).setWidth 64).toNat]'he1_lvl_l
    let mtr0 := cur.core.trail_pos[((lit_e1 >>> 1).setWidth 64).toNat]'he1_tp_l
    have hlit_e1_t1 : (tmp1[(end_b - 1).toNat]?.getD 0#32).toNat = lit_e1.toNat := by
      rw [← he1_t1, List.getElem?_eq_getElem he1_tl, Option.getD_some]
    have hblvl_eq : blvl.toNat = (s.core.lvl[lit_e1.toNat / 2]?.getD 0#32).toNat := by
      dsimp only [blvl]
      rw [← ho.lvl_eq, ← bv32_lshr_1 lit_e1, ← bv_c0_zext32_64 (lit_e1 >>> 1),
        List.getElem?_eq_getElem he1_lvl_l, Option.getD_some]
    have hblvl_bounds : 0 < blvl.toNat ∧ blvl.toNat < s.core.cur_level := by
      rw [hblvl_eq, ← hlit_e1_t1]; exact htmp1_lvls (end_b - 1).toNat (by omega) (by omega)
    have hm_e' : (FullMem c cur ⋆ R) me := hm_e; ml_lets
    refine wp_loop_group (ts := [i64, i64]) (fun n1 (beg', max_tr', ()) m_s =>
        n1 = beg'.toNat - 1 ∧ m_s = me ∧ 1 ≤ beg'.toNat ∧ beg'.toNat < end_b.toNat ∧
        ∀ k, beg'.toNat ≤ k → k < end_b.toNat →
          (s.core.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat ∧
          (s.core.trail_pos[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_tr'.toNat) ?_
      (fun Js_1 hJs_1 => by
        ml_lets
        have hm0_eq : (s.core.trail_pos[(tmp1[(end_b - 1).toNat]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat = (mtr0.setWidth 64).toNat := by
          dsimp only [mtr0]
          rw [hlit_e1_t1, ← ho.tpos_eq, bv_c0_zext32_64, ← bv32_lshr_1 lit_e1,
            ← bv_c0_zext32_64 (lit_e1 >>> 1), List.getElem?_eq_getElem he1_tp_l, Option.getD_some]
        refine hJs_1 ((end_b - 1).toNat - 1) (end_b - 1, mtr0.setWidth 64, ()) me
          ⟨rfl, rfl, by omega, by omega, fun k hk1 hk2 => ?_⟩
        have hke : k = (end_b - 1).toNat := by omega
        subst k; rw [hlit_e1_t1]
        exact ⟨hblvl_eq.symm, by rw [← hlit_e1_t1, hm0_eq]; exact le_refl _⟩)
    rintro Js_1 n1 ⟨beg', max_tr', ⟨⟩⟩ m_s hJs_1 ⟨rfl, rfl, hbg1, hbg_end, hscan⟩
    rw [Blocks.get_here]
    refine wp_join_group (ts := []) (fun () m_exit => m_exit = m_s ∧ (1 < beg'.toNat →
      (s.core.lvl[(tmp1[beg'.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
        blvl.toNat)) ?_ ?_
    · rintro Js_2 ⟨⟩ m_exit ⟨rfl, hbeg_lt_blvl⟩; rw [Blocks.get_here]
      refine wp_join_group (ts := []) (fun () mf =>
          ∃ (mrk_f : List (BitVec 8)) (tmp_f mstk_f mclr_f sstk_f : List (BitVec 32))
            (mcl_f : Nat) (mcf_f : BitVec 64),
          let cf := outerState s_in tmp_f mrk_f mstk_f mclr_f sstk_f mcl_f mcf_f
          OuterInv c F0 s tmp1 beg'.toNat cf ∧ (FullMem c cf ⋆ R) mf)
        (fun _ ⟨⟩ mf ⟨mrk_f, tmp_f, mstk_f, mclr_f, sstk_f, mcl_f, mcf_f, hof, hmf⟩ => by
          rw [Blocks.get_here]; ml_lets
          exact hJs0 (beg'.toNat - 1) (beg', ()) mf (by omega)
            ⟨rfl, hbg1, by omega, mrk_f, tmp_f, mstk_f, mclr_f, sstk_f, mcl_f, mcf_f, hof, hmf⟩) ?_
      rintro Js hJs; ml_lets; ml_jnz; refine ⟨fun hdiff1 => ?_, fun _ => ?_⟩
      · c0_cond hdiff1; have hend_eq : end_b.toNat = beg'.toNat + 1 := by bv_omega
        refine wp_join_group (ts := []) (fun () mf =>
            ∃ (mrk_f : List (BitVec 8)) (tmp_f mstk_f mclr_f sstk_f : List (BitVec 32))
              (mcl_f : Nat) (mcf_f : BitVec 64),
            let cf := outerState s_in tmp_f mrk_f mstk_f mclr_f sstk_f mcl_f mcf_f
            OuterInv c F0 s tmp1 beg'.toNat cf ∧ (FullMem c cf ⋆ R) mf)
          (fun _ ⟨⟩ mf hmf => by rw [Blocks.get_here]; ml_lets; exact hJs () mf hmf) ?_
        rintro Js_3 hJs_3
        have hbg_tl : beg'.toNat < cur.core.tmp.length := by
          dsimp only [cur]; rw [ho.core.1.core_ok.tmp_len_arr]; omega
        ml_ld c0_load_full_tmp (s := cur) (i := beg') hbg_tl hm_e'
        let rlit := cur.core.tmp[beg'.toNat]'hbg_tl
        have hr_t1 : cur.core.tmp[beg'.toNat]? = tmp1[beg'.toNat]? := ho.prefix_eq _ hbg_end
        have hr_ne : rlit ≠ 0xFFFFFFFF#32 := by
          have := htmp1_ne beg'.toNat (by omega)
          rwa [← hr_t1, List.getElem?_eq_getElem hbg_tl, Option.getD_some] at this
        have hrm_b := ho.rem_mrk beg'.toNat (by omega) (by
          rw [List.getElem?_eq_getElem hbg_tl, Option.getD_some]; exact hr_ne)
        rw [List.getElem?_eq_getElem hbg_tl, Option.getD_some] at hrm_b
        have hr_lt : rlit.toNat < 2 * cur.core.cur_vars := by rw [ho.cv_eq]; exact hrm_b.1
        have hr_vals : cur.core.vals[rlit.toNat]?.getD 0#8 = 0xFF#8 := by
          rw [ho.vals_eq]; exact hrm_b.2.1
        have hr_lvl : (cur.core.lvl[rlit.toNat / 2]?.getD 0#32).toNat < cur.core.cur_level := by
          rw [ho.lvl_eq, ho.clvl_eq]
          have hpl := (ho.post_lvls beg'.toNat hbg1 (by omega) (by
            rw [List.getElem?_eq_getElem hbg_tl, Option.getD_some]; exact hr_ne)).2.1
          rwa [List.getElem?_eq_getElem hbg_tl, Option.getD_some] at hpl
        ml_lets; apply wp_call_of_spec; apply hMl; dsimp only [fullMinLitSpec, vals, Arg.val]
        refine ⟨c, F0, cur,
          (((cur.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat), R,
          rfl, ho.core, ho.min_inv, hr_lt, hr_vals, hr_lvl,
          fun _ hv _ => ho.no8 _ (by rw [← ho.cv_eq]; exact hv), hm_e',
          fun ok mrk' mstk' mclr' mcl' mcf' m' hlen' hab' hmono2' hbit8' hmin' hokt hm' => ?_⟩
        have hstep := min_shrink_lit_step (beg := beg'.toNat) (by rw [← hend_eq]; exact ho)
          (by omega) htl_cv (List.getElem?_eq_getElem hbg_tl) hr_ne
          (fun h1b => by
            have hlt := hbeg_lt_blvl h1b
            rwa [← (hscan beg'.toNat (le_refl _) hbg_end).1, ← hr_t1,
              List.getElem?_eq_getElem hbg_tl, Option.getD_some] at hlt)
          hlen' hab' hmono2' hbit8' hmin' hokt
        ml_lets; ml_jnz; refine ⟨fun htrue => ?_, fun hfalse => ?_⟩
        · ml_st mf, hmf := c0_store_full_tmp (s := minLitState cur mrk' mstk' mclr' mcl' mcf')
            (i := beg') 0xFFFFFFFF#32 (by dsimp only; rw [hlen'.core_ok.tmp_len_arr]; omega) hm'
          rw [htrue] at hstep; simp only [↓reduceIte] at hstep; ml_lets
          exact hJs_3 () mf ⟨mrk', cur.core.tmp.set beg'.toNat 0xFFFFFFFF#32, mstk', mclr',
            sstk_e, mcl', mcf', hstep, hmf⟩
        · rw [hfalse] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep; ml_lets
          exact hJs_3 () m' ⟨mrk', cur.core.tmp, mstk', mclr', sstk_e, mcl', mcf', hstep, hm'⟩
      · ml_lets; apply wp_call_of_spec; apply hSb; dsimp only [fullShrinkBlkSpec, vals, Arg.val]
        have htake_cur : cur.core.tmp.take cur.core.tmp_len = cur.core.tmp.take s.core.tmp_len := by
          rw [ho.tl_eq]
        have hmin_cur : FullMinMarkInv cur.core (((cur.core.tmp.take cur.core.tmp_len).filter
            (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := by rw [htake_cur]; exact ho.min_inv
        have hblvl_cur_lt :
            (cur.core.lvl[((lit_e1 >>> 1).setWidth 64).toNat]'he1_lvl_l).toNat <
              cur.core.cur_level := by
          change blvl.toNat < cur.core.cur_level; rw [ho.clvl_eq]; exact hblvl_bounds.2
        refine ⟨c, F0, cur, R, rfl, ho.core, hmin_cur,
          fun v hv => ho.no8 v (by rw [← ho.cv_eq]; exact hv),
          hbg1, hbg_end, by rw [ho.tl_eq]; exact hend_tl, by rw [ho.tl_eq, ho.cv_eq]; exact htl_cv,
          hblvl_bounds.1, hblvl_cur_lt, ?_, ?_, hm_e',
          fun tmp_f mrk_f mstk_f mclr_f mcl_f mcf_f sstk_f m_f hcore_f hmin_f hab_f hno8_f
            _hmono2_f hother_f hlvl_f hnodup_f hent_f hrem_f hm_f => ?_⟩
        · intro k hk1 hk2; change beg'.toNat ≤ k at hk1; change k < end_b.toNat at hk2
          have hpk : cur.core.tmp[k]? = tmp1[k]? := ho.prefix_eq k hk2
          have hkne : cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
            rw [hpk]; exact htmp1_ne k (by omega)
          have hrk := ho.rem_mrk k (by omega) hkne; have hsc := hscan k hk1 hk2; rw [hpk] at hrk ⊢
          exact ⟨by rw [ho.cv_eq]; exact hrk.1, by rw [ho.vals_eq]; exact hrk.2.1,
            by change (cur.core.lvl[_]?.getD 0#32).toNat = blvl.toNat; rw [ho.lvl_eq]; exact hsc.1,
            by rw [ho.tpos_eq]; exact hsc.2⟩
        · intro k hk hne; rw [ho.tl_eq] at hk; have hrk := ho.rem_mrk k hk hne
          exact ⟨by rw [ho.cv_eq]; exact hrk.1, by rw [ho.vals_eq]; exact hrk.2.1, hrk.2.2⟩
        · let cf := outerState cur tmp_f mrk_f mstk_f mclr_f sstk_f mcl_f mcf_f
          have htake_eq : tmp_f.take cur.core.tmp_len = tmp_f.take s.core.tmp_len := by
            rw [ho.tl_eq]
          rw [htake_eq] at hmin_f; rw [ho.tl_eq] at hother_f hrem_f
          have hof : OuterInv c F0 s tmp1 beg'.toNat cf :=
            ⟨hcore_f, hmin_f, fun F_cur hw hEnt0 => by
               obtain ⟨hwc, hEc⟩ := ho.entails F_cur hw hEnt0
               have h1 := hent_f F_cur hwc (by rw [htake_cur]; exact hEc)
               rw [htake_eq] at h1; exact h1,
             fun hnd hne0 => by
               rw [← htake_eq]
               refine hnodup_f (by rw [htake_cur]; exact ho.nodup hnd hne0)
                 fun k hk_tl h_out hkne => ?_
               rw [ho.tl_eq] at hk_tl
               change (cur.core.lvl[(cur.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
                 blvl.toNat
               rw [ho.lvl_eq]; rcases Nat.eq_zero_or_pos k with rfl | hk1
               · obtain ⟨i, hi1, hi2, hi_eq⟩ := ht1_src (end_b - 1).toNat (by omega) (by omega)
                 have h0e : cur.core.tmp[0]? = s.core.tmp[0]? :=
                   (ho.prefix_eq 0 (by omega)).trans ht1_0
                 rw [h0e, hblvl_eq, ← hlit_e1_t1, hi_eq]; exact hne0 i hi1 hi2
               · rcases h_out with hlt_b | hge_e
                 · have hk_eq := ho.prefix_eq k (by omega)
                   have hle := htmp1_sort k (beg'.toNat - 1) hk1 (by omega) (by omega)
                   have hlt := hbeg_lt_blvl (by omega); rw [hk_eq]; omega
                 · have hgt := ho.blk_gt k hge_e hk_tl h1lt hkne
                   rw [← he1_nat, hlit_e1_t1, ← hblvl_eq] at hgt
                   dsimp only [cur, outerState] at hgt ⊢; omega,
             fun v hv => (hab_f v (by rw [ho.cv_eq]; exact hv)).trans (ho.mrk_above v hv),
             fun v hv => hno8_f v (by rw [ho.cv_eq]; exact hv),
             ho.cv_eq, ho.tl_eq, ho.lvl_eq, ho.vals_eq, ho.clvl_eq, ho.tpos_eq,
             fun k hk => by
               rw [hother_f k (by omega)
                 (by change k < beg'.toNat ∨ end_b.toNat ≤ k; exact Or.inl hk)]
               exact ho.prefix_eq k (by omega),
             fun k hk hne => by
               have hrk := hrem_f k hk hne
               exact ⟨by rw [← ho.cv_eq]; exact hrk.1,
                 by rw [← ho.vals_eq]; exact hrk.2.1, hrk.2.2⟩,
             fun k hk1 hk2 hne => by
               by_cases hmid : beg'.toNat ≤ k ∧ k < end_b.toNat
               · have hlv_s : (s.core.lvl[(tmp_f[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                     blvl.toNat := by rw [← ho.lvl_eq]; exact hlvl_f k hmid.1 hmid.2 hne
                 have hsc := hscan k hmid.1 hmid.2
                 exact ⟨hlv_s ▸ hblvl_bounds.1, hlv_s ▸ hblvl_bounds.2, hlv_s.trans hsc.1.symm⟩
               · have hoth := hother_f k hk2 (by change k < beg'.toNat ∨ end_b.toNat ≤ k; omega)
                 dsimp only [cf]; rw [hoth]; exact ho.post_lvls k hk1 hk2 (by rwa [← hoth]),
             fun k hk1 hk2 hb1 hne => by
               have hlt := hbeg_lt_blvl hb1; by_cases hmid : k < end_b.toNat
               · have hlv_s : (s.core.lvl[(tmp_f[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                     blvl.toNat := by rw [← ho.lvl_eq]; exact hlvl_f k hk1 hmid hne
                 dsimp only [cf]; rw [hlv_s]; exact hlt
               · have hoth := hother_f k hk2 (Or.inr (by omega))
                 dsimp only [cf] at hoth ⊢; rw [hoth]
                 have hgt := ho.blk_gt k (by omega) hk2 h1lt (by rwa [← hoth])
                 rw [← he1_nat, hlit_e1_t1, ← hblvl_eq] at hgt; exact Nat.lt_trans hlt hgt⟩
          ml_lets; exact hJs () m_f ⟨mrk_f, tmp_f, mstk_f, mclr_f, sstk_f, mcl_f, mcf_f, hof, hm_f⟩
    rintro Js_2 hJs_2; ml_lets; ml_jnz
    refine ⟨?_, fun hle1' => by
      c0_cond hle1'; ml_lets; exact hJs_2 () m_s ⟨rfl, fun h => by bv_omega⟩⟩
    intro hbg1'; c0_cond hbg1'
    have h1_bg : 1 < beg'.toNat := by bv_omega
    have hbm1 : (beg' - 1).toNat = beg'.toNat - 1 := by bv_omega
    have hbm_tl : (beg' - 1).toNat < cur.core.tmp.length := by
      dsimp only [cur]; rw [ho.core.1.core_ok.tmp_len_arr]; omega
    ml_ld c0_load_full_tmp (s := cur) (i := beg' - 1) hbm_tl hm_e'
    let lit_b := cur.core.tmp[(beg' - 1).toNat]'hbm_tl
    have hb_t1 : cur.core.tmp[(beg' - 1).toNat]? = tmp1[(beg' - 1).toNat]? :=
      ho.prefix_eq _ (by omega)
    have hne_b : cur.core.tmp[(beg' - 1).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rw [hb_t1]; exact htmp1_ne (beg' - 1).toNat (by omega)
    have hl_b : lit_b.toNat < 2 * s.core.cur_vars := by
      have hrm := ho.rem_mrk (beg' - 1).toNat (by omega) hne_b
      rw [List.getElem?_eq_getElem hbm_tl, Option.getD_some] at hrm; exact hrm.1
    have hb_var_lt : (lit_b >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr_1]; omega
    have hb_lvl_l : ((lit_b >>> 1).setWidth 64).toNat < cur.core.lvl.length := by
      rw [ho.core.1.core_ok.lvl_len, bv_c0_zext32_64]; omega
    ml_ld c0_load_full_lvl (s := cur) (i := (lit_b >>> 1).setWidth 64) hb_lvl_l hm_e'
    have hlit_b_t1 : (tmp1[(beg' - 1).toNat]?.getD 0#32).toNat = lit_b.toNat := by
      rw [← hb_t1, List.getElem?_eq_getElem hbm_tl, Option.getD_some]
    ml_lets; ml_jnz
    refine ⟨?_, fun hlvl_ne => by
      have hlt_b : (s.core.lvl[(tmp1[beg'.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
          blvl.toNat := by
        have hle_b := htmp1_sort (beg'.toNat - 1) (end_b - 1).toNat (by omega) (by omega) (by omega)
        have hne_b : (s.core.lvl[(tmp1[beg'.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
            blvl.toNat := by
          have hbl := hb_lvl_l; dsimp only [cur] at hbl
          rw [← hbm1, hlit_b_t1, ← ho.lvl_eq, ← bv32_lshr_1 lit_b, ← bv_c0_zext32_64 (lit_b >>> 1),
            List.getElem?_eq_getElem hbl, Option.getD_some]
          exact fun heq => (beq_eq_false_iff_ne.mp hlvl_ne) (BitVec.eq_of_toNat_eq heq)
        rw [hlit_e1_t1, ← hblvl_eq] at hle_b; omega
      ml_lets; exact hJs_2 () m_s ⟨rfl, fun _ => hlt_b⟩⟩
    intro hlvl_eq; ml_ld c0_load_full_tmp (s := cur) (i := beg' - 1) hbm_tl hm_e'
    have hb_tp_l : ((lit_b >>> 1).setWidth 64).toNat < cur.core.trail_pos.length := by
      rw [ho.core.1.core_ok.trail_pos_len, bv_c0_zext32_64]; omega
    ml_ld c0_load_full_trail_pos (s := cur) (i := (lit_b >>> 1).setWidth 64) hb_tp_l hm_e'
    let tp_b := (cur.core.trail_pos[((lit_b >>> 1).setWidth 64).toNat]'hb_tp_l).setWidth 64
    have hlb_eq : (s.core.lvl[(tmp1[(beg' - 1).toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
        blvl.toNat := by
      have hbl := hb_lvl_l; dsimp only [cur] at hbl
      rw [hlit_b_t1, ← ho.lvl_eq, ← bv32_lshr_1 lit_b, ← bv_c0_zext32_64 (lit_b >>> 1),
        List.getElem?_eq_getElem hbl, Option.getD_some]
      exact congrArg BitVec.toNat (beq_iff_eq.mp hlvl_eq)
    have htp_b_eq :
        (s.core.trail_pos[(tmp1[(beg' - 1).toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
        tp_b.toNat := by
      dsimp only [tp_b]; have htp := hb_tp_l; dsimp only [cur] at htp
      rw [hlit_b_t1, ← ho.tpos_eq, bv_c0_zext32_64, ← bv32_lshr_1 lit_b,
        ← bv_c0_zext32_64 (lit_b >>> 1), List.getElem?_eq_getElem htp, Option.getD_some]
    ml_lets; refine wp_join_group (ts := [i64]) (fun (mx, ()) mn =>
        mn = m_s ∧ max_tr'.toNat ≤ mx.toNat ∧ tp_b.toNat ≤ mx.toNat)
      (fun _ ⟨mx, ⟨⟩⟩ mn ⟨rfl, hmx1, hmx2⟩ => by
        rw [Blocks.get_here]; ml_lets
        refine hJs_1 ((beg' - 1).toNat - 1) (beg' - 1, mx, ()) mn (by omega)
          ⟨rfl, rfl, by omega, by omega, fun k hk1 hk2 => ?_⟩
        by_cases hke : k = (beg' - 1).toNat
        · subst k; exact ⟨hlb_eq, by rw [htp_b_eq]; exact hmx2⟩
        · have hsc := hscan k (by omega) hk2; exact ⟨hsc.1, le_trans hsc.2 hmx1⟩) ?_
    rintro Js hJs; ml_lets; ml_jnz; refine ⟨fun hmgt => ?_, fun hmle => ?_⟩
    · rw [BitVec.ult, decide_eq_true_eq] at hmgt
      exact hJs (tp_b, ()) m_s ⟨rfl, le_of_lt hmgt, le_refl _⟩
    · rw [BitVec.ult, decide_eq_false_iff_not] at hmle
      exact hJs (max_tr', ()) m_s ⟨rfl, le_refl _, Nat.le_of_not_lt hmle⟩
  · c0_cond hle; have hend_eq : end_b.toNat = 1 := by bv_omega
    rw [hend_eq] at ho; have hmin_c := ho.min_inv; rw [← ho.tl_eq] at hmin_c
    have h0_c : cur.core.tmp[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rw [ho.prefix_eq 0 (by omega)]; exact htmp1_ne 0 (by omega)
    have hcomp : wp Γ Q X (minShrinkCompactExpr c.hdr (BitVec.ofNat 64 cur.core.cur_vars)
        (BitVec.ofNat 64 cur.core.tmp_len) c.pTmp) me := by
      refine min_shrink_compact_wp ho.core (by rw [ho.tl_eq]; exact htl1)
        (by rw [ho.tl_eq, ho.cv_eq]; exact htl_cv) hmin_c
        (fun v hv => ho.no8 v (by rw [← ho.cv_eq]; exact hv)) h0_c ?_ ?_ hm_e ?_
      · intro k hk1 hk2 hne; rw [ho.tl_eq] at hk2
        have hrk := ho.rem_mrk k hk2 hne; have hpk := ho.post_lvls k hk1 hk2 hne
        rw [← ho.lvl_eq, ← ho.clvl_eq] at hpk; rw [← ho.vals_eq, ← ho.cv_eq] at hrk
        exact ⟨hrk.1, hrk.2.1, hpk.1, hpk.2.1⟩
      · intro i j hi1 hij hj hne_i hne_j; rw [ho.tl_eq] at hj
        have hpi := ho.post_lvls i hi1 (by omega) hne_i
        have hpj := ho.post_lvls j (by omega) hj hne_j
        rw [ho.lvl_eq, hpi.2.2, hpj.2.2]; exact htmp1_sort i j hi1 (by omega) hj
      · intro tmp' tl' mrk' m' sc_c s_c htl_f hml_f hab_f hmc_f h1_f htl_le h0_f hns_f
          hsort_f htake_f hm_f
        have h0_fin : tmp'[0]? = tmp1[0]? := h0_f.trans (ho.prefix_eq 0 (by omega))
        have hlen_e := ho.core.1
        refine hpost tmp' tl' mrk' mstk_e mclr_e sstk_e 0 0#64
          (cur.scratch.learned_lits + BitVec.ofNat 64 tl')
          (cur.scratch.min_removed + (BitVec.ofNat 64 cur.core.tmp_len - BitVec.ofNat 64 tl')) m'
          htl_f hml_f hlen_e.core_ok.min_stk_len hlen_e.core_ok.min_clr_len_arr (Nat.zero_le _)
          hlen_e.scratch_ok.shrink_stk_len
          (fun v hv => (hab_f v (by rw [ho.cv_eq]; exact hv)).trans (ho.mrk_above v hv))
          hmc_f h1_f (by rw [← ho.tl_eq]; exact htl_le) h0_fin
          (fun hnd hne0 => by rw [htake_f, ho.tl_eq]; exact ho.nodup hnd hne0)
          (fun j hj1 hj2 => by
            simpa [show s_in.core.cur_vars = s.core.cur_vars from ho.cv_eq,
              show s_in.core.vals = s.core.vals from ho.vals_eq,
              show s_in.core.lvl = s.core.lvl from ho.lvl_eq,
              show s_in.core.cur_level = s.core.cur_level from ho.clvl_eq] using hns_f j hj1 hj2)
          (fun i j hi1 hij hj => by
            simpa [show s_in.core.lvl = s.core.lvl from ho.lvl_eq] using hsort_f i j hi1 hij hj)
          (fun F_cur hw hEnt0 => by
            obtain ⟨hwc, hEc⟩ := ho.entails F_cur hw hEnt0
            exact ⟨fullOtfsWitness_with_min hwc, by rw [htake_f, ho.tl_eq]; exact hEc⟩) hm_f
    rwa [ho.tl_eq, ho.cv_eq] at hcomp

/-! ## 4. Main `full_min_shrink_wp` and canonical `full_min_shrink_spec_wp` -/

theorem full_min_shrink_wp (Γ : Env)
    (hSt : ∀ args m Q X, fullSortTmpSpec args m Q X → Γ "full_sort_tmp" [i64] [] args m Q X)
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hMl : ∀ args m Q X, fullMinLitSpec args m Q X →
      Γ "full_min_lit" [i64, i32] [.bool] args m Q X)
    (hSb : ∀ args m Q X, fullShrinkBlkSpec args m Q X →
      Γ "full_shrink_blk" [i64, i64, i64, i32, i64] [] args m Q X) :
    ∀ args m Q X, fullMinShrinkSpec args m Q X → Func.wp Γ full_min_shrink_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, ⟨hcore0, hw0⟩, hmc0, htl1, htl_cv, htmp_vals,
    htmp_lvls, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlen0 := hcore0.core_ok; have hcv := hlen0.cur_vars_le
  dsimp only [Func.wp, full_min_shrink_body]
  ml_ld load_full_cur_vars hm; ml_lets; ml_ld load_full_tmp_len hm; ml_lets
  ml_ld load_full_conflicts hm; ml_lets
  ml_st m0, hm0 := store_full_conflicts (s.scratch.conflicts + 1) hm
  let s0 := { s with scratch := { s.scratch with conflicts := s.scratch.conflicts + 1 } }
  have hs0_core : FullOtfsCoreInv c F0 s0 :=
    ⟨⟨hlen0, min_shrink_scratch_ok hcore0.scratch_ok⟩, hw0⟩; clear hcore0 hw0
  refine wp_join_group (ts := []) (fun () mq =>
      ∃ (tmp' : List (BitVec 32)) (tl' : Nat) (mrk' : List (BitVec 8))
        (mstk' mclr' sstk' : List (BitVec 32)) (mcl' : Nat) (mcf' conf' llits' mrem' : BitVec 64),
      let s' := minShrinkRes s tmp' tl' mrk' mstk' mclr' sstk' mcl' mcf' conf' llits' mrem'
      FullOtfsCoreInv c F0 s' ∧ FullMarksClear s' ∧
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) ∧
      1 ≤ tl' ∧ tl' ≤ s.core.tmp_len ∧ tmp'[0]? = s.core.tmp[0]? ∧
      (((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup →
        (∀ k, 1 ≤ k → k < s.core.tmp_len →
          (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
          (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
        ((tmp'.take tl').map fun x => x.toNat / 2).Nodup) ∧
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
        lv < s.core.cur_level ∧
        lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (∀ i j, 1 ≤ i → i ≤ j → j < tl' →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
        FullOtfsWitnessInv c F0 F_cur s'.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat))) ∧
      (FullMem c s' ⋆ R) mq) ?_ ?_
  · rintro Js ⟨⟩ mq ⟨tmp', tl', mrk', mstk', mclr', sstk', mcl', mcf', conf', llits', mrem',
      hcore', hmc', hab', h1', htl', h0', hnd', hns', hsort', hent', hmq⟩
    rw [Blocks.get_here]
    let sf := minShrinkRes s tmp' tl' mrk' mstk' mclr' sstk' mcl' mcf' conf' llits' mrem'
    ml_ld load_full_learned_lits (s := sf) hmq; ml_lets
    ml_st m_f, hm_f := store_full_learned_lits (s := sf)
      (llits' + BitVec.ofNat 64 s.core.tmp_len) hmq
    rw [wp]
    have hcore_f : FullOtfsCoreInv c F0 { sf with scratch := { sf.scratch with
        learned_lits := llits' + BitVec.ofNat 64 s.core.tmp_len } } :=
      ⟨⟨hcore'.1.core_ok, min_shrink_scratch_ok hcore'.1.scratch_ok⟩, hcore'.2⟩
    exact hQ tmp' tl' mrk' mstk' mclr' mcl' mcf' conf'
      (llits' + BitVec.ofNat 64 s.core.tmp_len) mrem' sstk' m_f hcore_f hmc' hab'
      (fun hlm => fullLitMarksClear_of_clear hlm rfl hmc' hab' rfl)
      h1' htl' h0' hnd' hns' hsort' hent' hm_f
  rintro Js hJs; ml_lets; ml_jnz; refine ⟨fun hle1 => ?_, fun hgt1 => ?_⟩
  · c0_cond hle1; have htl_eq1 : s.core.tmp_len = 1 := by bv_omega; ml_lets
    exact hJs () m0 ⟨s.core.tmp, s.core.tmp_len, s.core.mrk, s.core.min_stk, s.core.min_clr,
      s.scratch.shrink_stk, s.core.min_clr_len, s.core.min_clr_full, s.scratch.conflicts + 1,
      s.scratch.learned_lits, s.scratch.min_removed, hs0_core, hmc0, fun _ _ => rfl, htl1,
      le_refl _, rfl, fun hnd _ => hnd, fun _ h1 h2 => by omega, fun _ _ h1 _ h3 => by omega,
      fun _ hw hE => ⟨hw, hE⟩, hm0⟩
  c0_cond hgt1; have h2lt : 2 ≤ s.core.tmp_len := by bv_omega
  ml_lets; ml_jnz; refine ⟨fun hoob => by exfalso; c0_cond hoob; bv_omega, fun _ => ?_⟩
  ml_lets; apply wp_call_of_spec; apply hSt; dsimp only [fullSortTmpSpec, vals, Arg.val]
  refine ⟨c, s0, R, rfl, hs0_core.1, by dsimp only [s0]; omega,
    fun k hk1 hk2 => by dsimp only [s0] at hk2 ⊢; have := (htmp_vals k (by omega)).1; omega, hm0,
    fun tmp1 m1 ht1_len ht1_perm ht1_0 ht1_r ht1_l ht1_sort hm1 => ?_⟩
  obtain ⟨hkeep_eq, hEnt1, htmp1_vals, htmp1_lvls⟩ := min_shrink_post_sort
    htl1 htl_cv hcv hlen0.tmp_len_arr htmp_vals htmp_lvls ht1_len ht1_0 ht1_r ht1_l
  let s1 : FullState := { s0 with core := { s0.core with tmp := tmp1 } }
  ml_ld load_full_tmp_lits_ptr (s := s1) hm1; ml_ld load_full_level_ptr (s := s1) hm1
  ml_ld load_full_trail_pos_ptr (s := s1) hm1
  ml_st m2, hm2 := store_full_min_clr_len (s := s1) 0 (Nat.zero_lt_succ _) hm1
  ml_st m3, hm3 :=
    store_full_min_clr_full (s := { s1 with core := { s1.core with min_clr_len := 0 } }) 0#64 hm2
  let s2 : FullState := { s1 with core := { s1.core with min_clr_len := 0, min_clr_full := 0#64 } }
  have hs2_core : FullOtfsCoreInv c F0 s2 := fullOtfsCoreInv_with_min_tmp hs0_core ht1_len
    hlen0.tmp_len_le hlen0.mrk_len hlen0.min_stk_len hlen0.min_clr_len_arr (Nat.zero_le _)
    hs0_core.1.scratch_ok
  let keep0 := ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
  have hmin2_init : FullMinMarkInv s2.core keep0 := fullMinMarkInv_init hs2_core hmc0 keep0
  clear hm hm0 m0 hm1 m1 hm2 m2 hs0_core htmp_vals htmp_lvls hkeep_eq
  refine wp_loop_group (ts := [i64]) (fun n (i_bv, ()) mi =>
      n = s.core.tmp_len - i_bv.toNat ∧ i_bv.toNat ≤ s.core.tmp_len ∧
      ∃ (mrk_i : List (BitVec 8)) (mclr_i : List (BitVec 32)) (mcl_i : Nat) (mcf_i : BitVec 64),
      let cur : FullState := { s2 with core := { s2.core with
        mrk := mrk_i, min_clr := mclr_i, min_clr_len := mcl_i, min_clr_full := mcf_i } }
      mrk_i.length = c.max_vars ∧ mclr_i.length = c.max_vars ∧ mcl_i ≤ c.max_vars ∧
      (∀ v, s.core.cur_vars ≤ v → mrk_i[v]? = s.core.mrk[v]?) ∧ FullMinMarkInv cur.core keep0 ∧
      (∀ v < s.core.cur_vars, (mrk_i[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
      (∀ j < i_bv.toNat, (mrk_i[(tmp1[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
      (FullMem c cur ⋆ R) mi) ?_
    (fun Jm hJm => by
      ml_lets; have h0v : (0#64 : BitVec 64).toNat = 0 := rfl
      exact hJm (s.core.tmp_len - 0) (0#64, ()) m3
        ⟨by rw [h0v], by rw [h0v]; exact Nat.zero_le _, s2.core.mrk, s2.core.min_clr,
         s2.core.min_clr_len, s2.core.min_clr_full, hs2_core.1.core_ok.mrk_len,
         hs2_core.1.core_ok.min_clr_len_arr, hs2_core.1.core_ok.min_clr_len_le, fun _ _ => rfl,
         hmin2_init, fun v hv => by dsimp only [s2, s1, s0]; rw [hmc0 v hv]; decide,
         fun _ h => by rw [h0v] at h; omega, hm3⟩)
  rintro Jm n ⟨i_bv, ⟨⟩⟩ mi hJm
    ⟨rfl, hile, mrk_i, mclr_i, mcl_i, mcf_i, hmrkl, hmclrl, hmcll, hab_i, hmin_i, hno8_i,
      hmark_i, hm_i⟩
  let cur : FullState := { s2 with core := { s2.core with
    mrk := mrk_i, min_clr := mclr_i, min_clr_len := mcl_i, min_clr_full := mcf_i } }
  rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · c0_cond hlt; have hix : i_bv.toNat < s.core.tmp_len := by bv_omega
    have hi_tl : i_bv.toNat < cur.core.tmp.length := by dsimp only [cur, s2]; rw [ht1_len]; omega
    ml_ld c0_load_full_tmp (s := cur) (i := i_bv) hi_tl hm_i
    let lit_i := tmp1[i_bv.toNat]'(by rw [ht1_len]; omega)
    have hl_i := htmp1_vals i_bv.toNat hix
    rw [List.getElem?_eq_getElem (by rw [ht1_len]; omega), Option.getD_some] at hl_i
    have hlit_lt : lit_i.toNat < 2 * s.core.cur_vars := hl_i.2.1
    have hv_i : (lit_i >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr_1]; omega
    have hv_i' : lit_i.toNat / 2 < s.core.cur_vars := by omega
    have hcore_i : FullOtfsCoreInv c F0 cur :=
      fullOtfsCoreInv_with_min hs2_core hmrkl hs2_core.1.core_ok.min_stk_len hmclrl hmcll
    ml_lets; apply wp_call_of_spec; apply hMm
    refine fullMinMarkSpec_step hcore_i.1 hm_i (lit_i >>> 1) hv_i ((2 : BitVec 32).setWidth 8)
      fun m_n hm_n => ?_
    have h2_eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl; rw [h2_eq, bv32_lshr_1] at hm_n
    let nxt := fullMinMarkStepState cur (lit_i.toNat / 2) 2#8
    have hnxt_eq : { s2 with core := { s2.core with
        mrk := nxt.core.mrk, min_clr := nxt.core.min_clr,
        min_clr_len := nxt.core.min_clr_len, min_clr_full := nxt.core.min_clr_full } } = nxt := by
      dsimp only [nxt, fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore, cur]
      split <;> rfl
    have hlen_n := fullMinMarkStepState_lengths hcore_i.1 (lit_i.toNat / 2) 2#8
    have hmin_n := fullMinMarkInv_step_keep hcore_i hmin_i hlit_lt hl_i.2.2.2 hl_i.2.2.1
      (hno8_i _ hv_i')
    obtain ⟨hbit8_n, hmono2_n⟩ :=
      fullMinMarkStepState_bit8_mono2 hcore_i.1 hv_i' (Or.inl rfl) (hno8_i _ hv_i')
    have hab_n : ∀ v, s.core.cur_vars ≤ v → nxt.core.mrk[v]? = s.core.mrk[v]? := fun v hv =>
      (fullMinMarkStepState_mrk_above (s := cur) hv_i' 2#8 v hv).trans (hab_i v hv)
    have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 := by bv_omega; ml_lets
    refine hJm (s.core.tmp_len - (i_bv + 1).toNat) (i_bv + 1, ()) m_n (by omega)
      ⟨rfl, by omega, nxt.core.mrk, nxt.core.min_clr, nxt.core.min_clr_len, nxt.core.min_clr_full,
       hlen_n.core_ok.mrk_len, hlen_n.core_ok.min_clr_len_arr, hlen_n.core_ok.min_clr_len_le,
       hab_n, by rw [hnxt_eq]; exact hmin_n,
       fun v hv => by rw [hbit8_n v hv]; exact hno8_i v hv, fun j hj => ?_,
       by rw [hnxt_eq]; exact hm_n⟩
    rw [hi1] at hj; by_cases hje : j = i_bv.toNat
    · subst j
      have hti : tmp1[i_bv.toNat]?.getD 0#32 = lit_i := by
        rw [List.getElem?_eq_getElem (by rw [ht1_len]; omega), Option.getD_some]
      rw [hti]; dsimp only [nxt, fullMinMarkStepState, fullMinMarkStepCore]; split
      · rename_i hc; exact hc.resolve_left (Nat.not_le.mpr hv_i')
      · dsimp only [fullMinMarkCore]
        rw [List.getElem?_set_self (hmrkl ▸ lt_of_lt_of_le hv_i' hcv), Option.getD_some]
        exact bv8_and2_of_or2 _
    · have hjlt : (tmp1[j]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
        have := (htmp1_vals j (by omega)).2.1; omega
      exact hmono2_n _ hjlt (hmark_i j (by omega))
  · c0_cond hge; have hie : i_bv.toNat = s.core.tmp_len := by bv_omega
    have hcore_i : FullOtfsCoreInv c F0 cur :=
      fullOtfsCoreInv_with_min hs2_core hmrkl hs2_core.1.core_ok.min_stk_len hmclrl hmcll
    have ho_i : OuterInv c F0 s tmp1 s.core.tmp_len cur :=
      ⟨hcore_i, hmin_i, fun F_cur hw hE => ⟨fullOtfsWitness_with_min hw, hEnt1 F_cur hE⟩,
       fun hnd _ => by
         dsimp only [cur, s2, s1, s0]
         rw [list_filter_ne_eq_self (by rw [ht1_len]; omega) fun j hj => by
           have := (htmp1_vals j hj).2.1; omega]
         exact nodup_take_map_div2_of_perm ht1_perm hnd,
       hab_i, hno8_i, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
       fun k hk _ => let hkv := htmp1_vals k hk; ⟨hkv.2.1, hkv.2.2.1, hmark_i k (hie ▸ hk)⟩,
       fun k hk1 hk2 _ => let hlv := htmp1_lvls k hk1 hk2; ⟨hlv.1, hlv.2, rfl⟩,
       fun _ _ hk2 _ => absurd hk2 (by omega)⟩
    change wp Γ Q X (minShrinkOuterExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel c.pTrailPos) mi
    refine min_shrink_outer_wp hMl hSb ho_i (ht1_0 htl1) ht1_r htl1 htl_cv ht1_sort
      (fun k hk => (htmp1_vals k hk).1) htmp1_lvls hm_i
      fun tmp' tl' mrk' mstk' mclr' sstk' mcl' mcf' llits' mrem' m'
        htl_f hml_f hmstk_f hmclr_f hmcl_f hsstk_f hab_f hmc_f h1_f htl_le h0_f hnd_f
        hns_f hsort_f hent_f hm' => ?_
    let sc_f := { cur.scratch with
      learned_lits := llits', min_removed := mrem', shrink_stk := sstk' }
    have hsc_f : sc_f.LengthsOk c := { hcore_i.1.scratch_ok with shrink_stk_len := hsstk_f }
    have hcore_f : FullOtfsCoreInv c F0 (minShrinkRes s tmp' tl' mrk' mstk' mclr' sstk'
        mcl' mcf' (s.scratch.conflicts + 1) llits' mrem') :=
      fullOtfsCoreInv_with_min_tmp hcore_i htl_f (by omega) hml_f hmstk_f hmclr_f hmcl_f hsc_f
    exact hQ tmp' tl' mrk' mstk' mclr' mcl' mcf' (s.scratch.conflicts + 1) llits' mrem' sstk' m'
      hcore_f hmc_f hab_f (fun hlm => fullLitMarksClear_of_clear hlm rfl hmc_f hab_f rfl)
      h1_f htl_le (h0_f.trans (ht1_0 htl1)) hnd_f hns_f hsort_f hent_f hm'

theorem full_min_shrink_spec_wp (Γ : Env)
    (hSt : ∀ args m Q X, fullSortTmpSpec args m Q X → Γ "full_sort_tmp" [i64] [] args m Q X)
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    (hMl : ∀ args m Q X, fullMinLitSpec args m Q X →
      Γ "full_min_lit" [i64, i32] [.bool] args m Q X)
    (hSb : ∀ args m Q X, fullShrinkBlkSpec args m Q X →
      Γ "full_shrink_blk" [i64, i64, i64, i32, i64] [] args m Q X) :
    ∀ args m Q X,
      (fun (h, ()) m Q _ =>
        ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
          (R : Mem 64 → Prop),
          h = c.hdr ∧ s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧
          FullLitMarksClear c s ∧ 1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
          ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
          (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
            l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
          (∀ k, 1 ≤ k → k < s.core.tmp_len →
            let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
            0 < lv ∧ lv < s.core.cur_level) ∧
          (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
            s.core.cur_level ∧
          (FullMem c s ⋆ R) m ∧
          ∀ tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' m',
            let s' : FullState := {
              core := { s.core with
                tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk',
                min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' },
              scratch := { s.scratch with
                conflicts := conf', learned_lits := llits', min_removed := mrem',
                shrink_stk := sstk' } }
            s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core →
            FullLitMarksClear c s' → 1 ≤ tl' → tl' ≤ s.core.tmp_len →
            tmp'[0]? = s.core.tmp[0]? → ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
            (∀ j, 1 ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
              let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
              l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
              lv < s.core.cur_level ∧
              lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
            (FullMem c s' ⋆ R) m' → Q () m') args m Q X →
      Func.wp Γ full_min_shrink_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, h1, htl, hnd, hEnt, hvals, hlvls,
    hlvl0, hm, hQ⟩
  refine full_min_shrink_wp Γ hSt hMm hMl hSb (c.hdr, ()) m Q X
    ⟨c, F0, s, R, rfl, ⟨hlen, F_cur, hw⟩, hlm.toFullMarksClear hlen, h1, htl, hvals, hlvls, hm,
      fun tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' m' hcore' _hmc' _hab' hlm'
        h1' htl' h0' hnd' hns' _hsort' hEnt' hm' => ?_⟩
  have ⟨hw', hEc'⟩ := hEnt' F_cur hw hEnt
  have hne0 : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
      (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := fun k hk1 hk2 => by
    have := (hlvls k hk1 hk2).2; omega
  exact hQ tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' m' hcore'.1 hw' (hlm' hlm)
    h1' htl' h0' (hnd' hnd hne0) hns' hEc' hm'

end LeanQbe.T.Examples.Kissat.Full
