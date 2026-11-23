module

public import LeanQbe.T.Examples.Kissat.PlainMinLemmas4

/-!
# Soundness Proofs for Kissat `D-Plain` Main Minimization (Part 5)

Proves parametric `(Γ : Env)` `Func.wp` contract for `plain_min_shrink`
(`plainMinShrinkSpec`, `plain_min_shrink_wp`, `PlainSpec.lean:1008`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open scoped PlainMinTactics

/-! ## 1. Pure list, invariant, and sub-expression helpers -/

private theorem list_take_succ_set {α : Type _} {xs : List α} {i : Nat} (v : α)
    (hi : i < xs.length) :
    (xs.set i v).take (i + 1) = xs.take i ++ [v] := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_set, List.length_append, List.length_take]
    simp only [List.length_singleton]; omega
  · intro j hj1 hj2
    rw [List.getElem_take]
    by_cases hjl : j < min i xs.length
    · rw [List.getElem_append_left (by rw [List.length_take]; exact hjl),
        List.getElem_take, List.getElem_set_ne (by omega)]
    · have hje : j = i := by rw [List.length_take, List.length_set] at hj1; omega
      subst hje
      have hi_j : j < (xs.set j v).length := by rw [List.length_set]; exact hi
      have htake_len : (xs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hi)
      rw [List.getElem_set_self hi_j]
      simp [List.getElem_append_right, htake_len]

private theorem list_filter_ne_eq_self {xs : List (BitVec 32)} {k : Nat}
    (hk : k ≤ xs.length) (h : ∀ j < k, (xs[j]?.getD 0#32).toNat < 2 ^ 31) :
    (xs.take k).filter (· ≠ 0xFFFFFFFF#32) = xs.take k := by
  rw [List.filter_eq_self]
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  rw [List.length_take] at hj
  have hlt := h j (by omega)
  rw [List.getElem_take]
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hlt
  rw [decide_eq_true_eq]
  intro heq
  have hto := congrArg BitVec.toNat heq
  have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl
  omega

private theorem min_shrink_heur_ok {c : PlainCfg} {s : PlainState} (hok : s.heur.LengthsOk c)
    {cf ll mr : BitVec 64} :
    ({ s.heur with conflicts := cf, learned_lits := ll, min_removed := mr } :
      PlainHeur).LengthsOk c :=
  { hok with heap_len_arr := hok.heap_len_arr }

private theorem min_shrink_post_sort {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (htl1 : 1 ≤ s.tmp_len) (htl_mv : s.tmp_len ≤ c.mv)
    (hlen_tmp : s.tmp.length = c.mv)
    (hEnt0 : F0.EntailsClause (cnfClause ((s.tmp.take s.tmp_len).map BitVec.toNat)))
    (htmp_vals : ∀ k < s.tmp_len, let l := (s.tmp[k]?.getD 0#32).toNat
      l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8)
    (htmp_lvls : ∀ k, 1 ≤ k → k < s.tmp_len →
      let lv := (s.lvl[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.cur_level)
    {tmp1 : List (BitVec 32)} (ht1_len : tmp1.length = c.mv)
    (ht1_0 : 0 < s.tmp_len → tmp1[0]? = s.tmp[0]?)
    (ht1_r : ∀ j, 1 ≤ j → j < s.tmp_len → ∃ i, 1 ≤ i ∧ i < s.tmp_len ∧ tmp1[j]? = s.tmp[i]?)
    (ht1_l : ∀ i, 1 ≤ i → i < s.tmp_len → ∃ j, 1 ≤ j ∧ j < s.tmp_len ∧ s.tmp[i]? = tmp1[j]?) :
    let keep0 := ((tmp1.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    keep0 = (tmp1.take s.tmp_len).map BitVec.toNat ∧
    F0.EntailsClause (cnfClause keep0) ∧
    (∀ k < s.tmp_len,
      let l := (tmp1[k]?.getD 0#32).toNat
      tmp1[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
      l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧ l ∈ keep0) ∧
    (∀ k, 1 ≤ k → k < s.tmp_len →
      let lv := (s.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.cur_level) := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hlt1 : ∀ k < s.tmp_len, (tmp1[k]?.getD 0#32).toNat < 2 * c.mv ∧
      s.vals[(tmp1[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
    intro k hk
    cases k with
    | zero => rw [ht1_0 htl1]; exact htmp_vals 0 hk
    | succ k' =>
      obtain ⟨i, _, hi2, heq⟩ := ht1_r (k' + 1) (by omega) hk
      rw [heq]; exact htmp_vals i hi2
  have hkeep_eq : ((tmp1.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat =
      (tmp1.take s.tmp_len).map BitVec.toNat := by
    rw [list_filter_ne_eq_self (by omega) fun j hj => by
      have := (hlt1 j hj).1; omega]
  refine ⟨hkeep_eq, ?_, ?_, ?_⟩
  · rw [hkeep_eq]
    rw [CNF.entails_clause_def] at hEnt0 ⊢
    intro α hα
    obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (hEnt0 α hα)
    refine (clause_sat_cnfClause_iff α _).mpr ⟨l, ?_, hsat⟩
    rw [List.mem_map] at hl ⊢
    obtain ⟨b, hb, rfl⟩ := hl
    rw [List.mem_iff_getElem] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    rw [List.length_take] at hi
    have hi_tl : i < s.tmp_len := by omega
    rw [List.getElem_take]
    cases i with
    | zero =>
      have h0 : tmp1[0]? = s.tmp[0]? := ht1_0 htl1
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h0
      refine ⟨tmp1[0]'(by omega), List.mem_iff_getElem.mpr ⟨0, by rw [List.length_take]; omega,
        by rw [List.getElem_take]⟩, by rw [Option.some.inj h0]⟩
    | succ i' =>
      obtain ⟨j, _, hj2, heq⟩ := ht1_l (i' + 1) (by omega) hi_tl
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
      refine ⟨tmp1[j]'(by omega), List.mem_iff_getElem.mpr ⟨j, by rw [List.length_take]; omega,
        by rw [List.getElem_take]⟩, by rw [Option.some.inj heq]⟩
  · intro k hk
    have hkv := hlt1 k hk
    have hk_ne : tmp1[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      intro heq
      have hto := congrArg BitVec.toNat heq
      have h1' := hkv.1
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1'
      have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl
      omega
    have hk_mem : (tmp1[k]?.getD 0#32).toNat ∈
        ((tmp1.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat := by
      rw [hkeep_eq, List.mem_map]
      refine ⟨tmp1[k]'(by omega), List.mem_iff_getElem.mpr ⟨k, by rw [List.length_take]; omega,
        by rw [List.getElem_take]⟩, ?_⟩
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact ⟨hk_ne, hkv.1, hkv.2, hk_mem⟩
  · intro k hk1 hk2
    obtain ⟨i, hi1, hi2, heq⟩ := ht1_r k hk1 hk2
    rw [heq]; exact htmp_lvls i hi1 hi2

/-! ## 2. Cleanup and compaction sub-expressions (`minShrinkCleanExpr`, `minShrinkCompactExpr`) -/

private def minShrinkCleanExpr (p ld ld_1 ld_6 keep : Val i64) : Expr Val Cont [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) : Op Val [i64] :=
    Op.mk c (a, b, ())
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

private theorem min_shrink_clean_wp {Γ : Env} {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost} (hcore : PlainCoreInv c F0 s)
    {keep_bv : BitVec 64} {m : Mem 64} (hm_in : (PlainMem c s ⋆ R) m)
    (hmin : PlainMinMarkInv c F0 s
      (((s.tmp.take keep_bv.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hno8 : ∀ v < c.mv, (s.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hpost : ∀ (mrk' : List (BitVec 8)) (m' : Mem 64),
      let heur' := { s.heur with
        min_removed := s.heur.min_removed + (BitVec.ofNat 64 s.tmp_len - keep_bv),
        learned_lits := s.heur.learned_lits + keep_bv }
      let s' := { s with mrk := mrk', min_clr_len := 0, min_clr_full := 0#64,
                         tmp_len := keep_bv.toNat, heur := heur' }
      mrk'.length = c.mv → MarksClear c s' → (PlainMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (minShrinkCleanExpr c.hdr (BitVec.ofNat 64 c.mv)
      (BitVec.ofNat 64 s.tmp_len) c.pMark keep_bv) m := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hlen := hcore.lengths
  have h0v : (0#64 : BitVec 64).toNat = 0 := rfl
  have hmcl_le := hlen.min_clr_len_le
  have hmcl_arr := hlen.min_clr_len_arr
  have hmcl_lt : s.min_clr_len < 2 ^ 64 := by omega
  have hmv_lt : c.mv < 2 ^ 64 := by omega
  dsimp only [minShrinkCleanExpr]
  refine wp_join_group (ts := []) (fun () mc => ∃ mrk',
      mrk'.length = c.mv ∧ (∀ v < c.mv, mrk'[v]?.getD 0#8 = 0#8) ∧
      (PlainMem c { s with mrk := mrk' } ⋆ R) mc) ?_ ?_
  · rintro Js ⟨⟩ mc ⟨mrk', hml, hmc, hm_c⟩
    rw [Blocks.get_here]; ml_lets
    let sc0 : PlainState := { s with mrk := mrk' }
    have hmc0 : MarksClear c sc0 := hmc
    ml_st m1, hm1 := store_arena_min_clr_len (s := sc0) 0 (Nat.zero_lt_succ _) hm_c
    ml_lets
    ml_st m2, hm2 := store_arena_min_clr_full (s := { sc0 with min_clr_len := 0 }) 0#64 hm1
    ml_lets
    ml_st m3, hm3 := c0_store_arena_tmp_len
      (s := { sc0 with min_clr_len := 0, min_clr_full := 0#64 }) keep_bv hm2
    let sc1 : PlainState := { s with
      mrk := mrk', min_clr_len := 0, min_clr_full := 0#64, tmp_len := keep_bv.toNat }
    ml_ld load_arena_min_removed (s := sc1) hm3
    ml_lets
    ml_st m4, hm4 := store_arena_min_removed (s := sc1)
      (s.heur.min_removed + (BitVec.ofNat 64 s.tmp_len - keep_bv)) hm3
    let sc2 : PlainState := { sc1 with
      heur := { sc1.heur with
        min_removed := s.heur.min_removed + (BitVec.ofNat 64 s.tmp_len - keep_bv) } }
    ml_ld load_arena_learned_lits (s := sc2) hm4
    ml_lets
    ml_st m5, hm5 := store_arena_learned_lits (s := sc2) (s.heur.learned_lits + keep_bv) hm4
    rw [wp]
    exact hpost mrk' m5 hml hmc0 hm5
  · rintro Js hJs
    ml_ld load_arena_min_clr_full hm_in
    ml_lets; ml_jnz; refine ⟨fun hfull => ?_, fun hnf => ?_⟩
    · clear hfull
      refine wp_loop_group (ts := [i64]) (fun n (z, ()) mz =>
          n = c.mv - z.toNat ∧ z.toNat ≤ c.mv ∧ ∃ mrk_z,
          mrk_z.length = c.mv ∧ (∀ w < z.toNat, mrk_z[w]?.getD 0#8 = 0#8) ∧
          (PlainMem c { s with mrk := mrk_z } ⋆ R) mz) ?_ ?_
      · rintro J1 n ⟨z, ⟨⟩⟩ mz hJ1 ⟨rfl, hzle, mrk_z, hml_z, hz0, hm_z⟩
        rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
        · c0_cond hlt
          have hzx : z.toNat < c.mv := by bv_omega
          have hzm : z.toNat < ({ s with mrk := mrk_z } : PlainState).mrk.length := by
            dsimp only; rw [hml_z]; exact hzx
          ml_lets
          ml_st m_z', hm_z' := c0_store_arena_mrk (s := { s with mrk := mrk_z })
            (i := z) ((0 : BitVec 32).setWidth 8) hzm hm_z
          have hz1 : (z + 1).toNat = z.toNat + 1 := by bv_omega
          have hz0' : ∀ w < (z + 1).toNat, (mrk_z.set z.toNat 0#8)[w]?.getD 0#8 = 0#8 := by
            intro w hw
            by_cases hwe : w = z.toNat
            · subst w; rw [List.getElem?_set_self (by omega)]; rfl
            · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hz0 w (by omega)
          have hz8 : (0 : BitVec 32).setWidth 8 = 0#8 := rfl
          rw [hz8] at hm_z'
          ml_lets
          exact hJ1 (c.mv - (z + 1).toNat) (z + 1, ()) m_z' (by omega)
            ⟨rfl, by omega, mrk_z.set z.toNat 0#8, by rw [List.length_set, hml_z], hz0', hm_z'⟩
        · c0_cond hge
          have hze : z.toNat = c.mv := by bv_omega
          ml_lets
          exact hJs () mz ⟨mrk_z, hml_z, fun w hw => hz0 w (hze ▸ hw), hm_z⟩
      · rintro J1 hJ1; ml_lets
        exact hJ1 (c.mv - 0) (0#64, ()) m
          ⟨by rw [h0v], by rw [h0v]; exact Nat.zero_le _, s.mrk, hlen.mrk_len,
           fun _ h => by rw [h0v] at h; omega, hm_in⟩
    · c0_cond hnf
      have hnf' : s.min_clr_full = 0#64 := hnf
      ml_ld load_arena_min_clr_ptr hm_in
      refine wp_loop_group (ts := [i64]) (fun n (z, ()) mz =>
          n = s.min_clr_len - z.toNat ∧ z.toNat ≤ s.min_clr_len ∧ ∃ mrk_z,
          mrk_z.length = c.mv ∧
          (∀ w < c.mv, mrk_z[w]?.getD 0#8 ≠ 0#8 →
            ∃ k, z.toNat ≤ k ∧ k < s.min_clr_len ∧ (s.min_clr[k]?.getD 0#32).toNat = w) ∧
          (PlainMem c { s with mrk := mrk_z } ⋆ R) mz) ?_ ?_
      · rintro J1 n ⟨z, ⟨⟩⟩ mz hJ1 ⟨rfl, hzle, mrk_z, hml_z, hcov_z, hm_z⟩
        rw [Blocks.get_here]
        ml_ld load_arena_min_clr_len (s := { s with mrk := mrk_z }) hm_z
        ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
        · have hzm : z.toNat < s.min_clr_len := by
            rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hmcl_lt] at hlt
            exact hlt
          have hzl : z.toNat < ({ s with mrk := mrk_z } : PlainState).min_clr.length := by
            dsimp only; rw [hmcl_arr]; exact lt_of_lt_of_le hzm hmcl_le
          ml_ld c0_load_arena_min_clr (s := { s with mrk := mrk_z }) (i := z) hzl hm_z
          let v32 := s.min_clr[z.toNat]'hzl
          have hz1 : (z + 1).toNat = z.toNat + 1 := by bv_omega
          refine wp_join_group (ts := []) (fun () mn => ∃ mrk_n,
              mrk_n.length = c.mv ∧
              (∀ w < c.mv, mrk_n[w]?.getD 0#8 ≠ 0#8 →
                ∃ k, z.toNat + 1 ≤ k ∧ k < s.min_clr_len ∧
                  (s.min_clr[k]?.getD 0#32).toNat = w) ∧
              (PlainMem c { s with mrk := mrk_n } ⋆ R) mn) ?_ ?_
          · rintro J2 ⟨⟩ mn ⟨mrk_n, hml_n, hcov_n, hm_n⟩
            rw [Blocks.get_here]; ml_lets
            exact hJ1 (s.min_clr_len - (z + 1).toNat) (z + 1, ()) mn (by omega)
              ⟨rfl, by omega, mrk_n, hml_n, fun w hw hnz => by rw [hz1]; exact hcov_n w hw hnz,
               hm_n⟩
          · rintro J2 hJ2
            ml_lets; ml_jnz; refine ⟨fun hvlt => ?_, fun hvge => ?_⟩
            · have hvx : (v32.setWidth 64).toNat < c.mv := by
                rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt hmv_lt] at hvlt
                exact hvlt
              have hvm : (v32.setWidth 64).toNat <
                  ({ s with mrk := mrk_z } : PlainState).mrk.length := by
                dsimp only; rw [hml_z]; exact hvx
              ml_lets
              ml_st mn, hmn := c0_store_arena_mrk (s := { s with mrk := mrk_z })
                (i := v32.setWidth 64) ((0 : BitVec 32).setWidth 8) hvm hm_z
              have hz8 : (0 : BitVec 32).setWidth 8 = 0#8 := rfl
              rw [hz8, bv_c0_zext32_64] at hmn
              ml_lets
              refine hJ2 () mn ⟨mrk_z.set v32.toNat 0#8, by rw [List.length_set, hml_z],
                fun w hw hnz => ?_, hmn⟩
              have hwne : w ≠ v32.toNat := by
                rintro rfl
                rw [List.getElem?_set_self (by rw [hml_z]; rw [← bv_c0_zext32_64]; exact hvx)]
                  at hnz
                exact hnz rfl
              rw [List.getElem?_set_ne (Ne.symm hwne)] at hnz
              obtain ⟨k, hk1, hk2, hke⟩ := hcov_z w hw hnz
              have hknz : k ≠ z.toNat := by
                rintro rfl
                rw [List.getElem?_eq_getElem hzl, Option.getD_some] at hke
                exact hwne hke.symm
              exact ⟨k, by omega, hk2, hke⟩
            · have hvx : c.mv ≤ v32.toNat := by
                rw [BitVec.ult, decide_eq_false_iff_not, not_lt, bv_c0_zext32_64,
                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmv_lt] at hvge
                exact hvge
              ml_lets
              refine hJ2 () mz ⟨mrk_z, hml_z, fun w hw hnz => ?_, hm_z⟩
              obtain ⟨k, hk1, hk2, hke⟩ := hcov_z w hw hnz
              have hknz : k ≠ z.toNat := by
                rintro rfl
                dsimp only [v32] at hvx
                have hzl0 : z.toNat < s.min_clr.length := by
                  rw [hmcl_arr]; exact lt_of_lt_of_le hzm hmcl_le
                rw [List.getElem?_eq_getElem hzl0, Option.getD_some] at hke
                omega
              exact ⟨k, by omega, hk2, hke⟩
        · have hze : z.toNat = s.min_clr_len := by
            rw [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hmcl_lt] at hge
            omega
          ml_lets
          refine hJs () mz ⟨mrk_z, hml_z, fun w hw => ?_, hm_z⟩
          by_cases hz : mrk_z[w]?.getD 0#8 = 0#8
          · exact hz
          · exfalso; obtain ⟨k, hk1, hk2, _⟩ := hcov_z w hw hz; omega
      · rintro J1 hJ1; ml_lets
        refine hJ1 (s.min_clr_len - 0) (0#64, ()) m
          ⟨by rw [h0v], by rw [h0v]; exact Nat.zero_le _, s.mrk, hlen.mrk_len,
           fun w hw hnz => ?_, hm_in⟩
        have h6 : (s.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 :=
          (plainMinMarkInv_mrk_ne_zero_iff hmin hno8 hw).mp hnz
        obtain ⟨k, hk, hke⟩ := hmin.clr_cov hnf' w hw h6
        exact ⟨k, by rw [h0v]; exact Nat.zero_le _, hk, hke⟩

private def minShrinkCompactExpr (p ld ld_1 ld_3 : Val i64) : Expr Val Cont [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) : Op Val [i64] :=
    Op.mk c (a, b, ())
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

private theorem min_shrink_compact_wp {Γ : Env} {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost} (hcore : PlainCoreInv c F0 s)
    (htl1 : 1 ≤ s.tmp_len) (htl_mv : s.tmp_len ≤ c.mv)
    (hmin_in : PlainMinMarkInv c F0 s
      (((s.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hno8 : ∀ v < c.mv, (s.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (h0_ok : s.tmp[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hns_ok : ∀ k, 1 ≤ k → k < s.tmp_len → s.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.tmp[k]?.getD 0#32).toNat
      l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧
      0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level)
    (hns_sort : ∀ i j, 1 ≤ i → i ≤ j → j < s.tmp_len →
      s.tmp[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      s.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.lvl[(s.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.lvl[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    {m : Mem 64} (hm_in : (PlainMem c s ⋆ R) m)
    (hpost : ∀ (tmp' : List (BitVec 32)) (tl' : Nat) (mrk' : List (BitVec 8)) (m' : Mem 64),
      let heur' := { s.heur with
        min_removed := s.heur.min_removed +
          (BitVec.ofNat 64 s.tmp_len - BitVec.ofNat 64 tl'),
        learned_lits := s.heur.learned_lits + BitVec.ofNat 64 tl' }
      let s' := { s with tmp := tmp', mrk := mrk', min_clr_len := 0, min_clr_full := 0#64,
                         tmp_len := tl', heur := heur' }
      tmp'.length = c.mv → mrk'.length = c.mv → MarksClear c s' →
      1 ≤ tl' → tl' ≤ s.tmp_len → tmp'[0]? = s.tmp[0]? →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧ lv < s.cur_level ∧
        lv ≤ (s.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      tmp'.take tl' = (s.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32) →
      (PlainMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (minShrinkCompactExpr c.hdr (BitVec.ofNat 64 c.mv)
      (BitVec.ofNat 64 s.tmp_len) c.pTmp) m := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hlen := hcore.lengths
  have htl_lt : s.tmp_len < 2 ^ 64 := by omega
  have h1v : (1#64 : BitVec 64).toNat = 1 := rfl
  dsimp only [minShrinkCompactExpr]
  refine wp_loop_group (ts := [i64, i64]) (fun n (kp, k, ()) mk =>
      n = s.tmp_len - k.toNat ∧ 1 ≤ kp.toNat ∧ kp.toNat ≤ k.toNat ∧ k.toNat ≤ s.tmp_len ∧
      ∃ tmp_k, tmp_k.length = c.mv ∧ tmp_k[0]? = s.tmp[0]? ∧
      tmp_k.take kp.toNat = (s.tmp.take k.toNat).filter (· ≠ 0xFFFFFFFF#32) ∧
      (∀ j, k.toNat ≤ j → j < s.tmp_len → tmp_k[j]? = s.tmp[j]?) ∧
      (∀ j, 1 ≤ j → j < kp.toNat →
        let l := (tmp_k[j]?.getD 0#32).toNat
        let lv := (s.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧ lv < s.cur_level) ∧
      (∀ a b, 1 ≤ a → a ≤ b → b < kp.toNat →
        (s.lvl[(tmp_k[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.lvl[(tmp_k[b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (∀ a, 1 ≤ a → a < kp.toNat → ∀ j, k.toNat ≤ j → j < s.tmp_len →
        s.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        (s.lvl[(tmp_k[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.lvl[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (PlainMem c { s with tmp := tmp_k } ⋆ R) mk) ?_ ?_
  · rintro Js n ⟨kp, k, ⟨⟩⟩ mk hJs
      ⟨rfl, hkp1, hkpk, hkle, tmp_k, htkl, htk0, htk_f, htk_r, htk_l, htk_s, htk_c, hm_k⟩
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have hkx : k.toNat < s.tmp_len := by
        rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl_lt] at hlt
        exact hlt
      have hk_tl : k.toNat < ({ s with tmp := tmp_k } : PlainState).tmp.length := by
        dsimp only; rw [htkl]; omega
      have hkp_tl : kp.toNat < ({ s with tmp := tmp_k } : PlainState).tmp.length := by
        dsimp only; rw [htkl]; omega
      have hk_eq : tmp_k[k.toNat]? = s.tmp[k.toNat]? := htk_r k.toNat (le_refl _) hkx
      have hk1 : (k + 1).toNat = k.toNat + 1 := by bv_omega
      have htake_k : s.tmp.take (k.toNat + 1) = s.tmp.take k.toNat ++ [s.tmp[k.toNat]'
          (by rw [hlen.tmp_len_arr]; omega)] :=
        List.take_succ_eq_append_getElem (by rw [hlen.tmp_len_arr]; omega)
      refine wp_join_group (ts := [i64]) (fun (kp', ()) mk' =>
          1 ≤ kp'.toNat ∧ kp'.toNat ≤ k.toNat + 1 ∧ ∃ tmp_n, tmp_n.length = c.mv ∧
          tmp_n[0]? = s.tmp[0]? ∧
          tmp_n.take kp'.toNat = (s.tmp.take (k.toNat + 1)).filter (· ≠ 0xFFFFFFFF#32) ∧
          (∀ j, k.toNat + 1 ≤ j → j < s.tmp_len → tmp_n[j]? = s.tmp[j]?) ∧
          (∀ j, 1 ≤ j → j < kp'.toNat →
            let l := (tmp_n[j]?.getD 0#32).toNat
            let lv := (s.lvl[l / 2]?.getD 0#32).toNat
            l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧ lv < s.cur_level) ∧
          (∀ a b, 1 ≤ a → a ≤ b → b < kp'.toNat →
            (s.lvl[(tmp_n[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            (s.lvl[(tmp_n[b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
          (∀ a, 1 ≤ a → a < kp'.toNat → ∀ j, k.toNat + 1 ≤ j → j < s.tmp_len →
            s.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
            (s.lvl[(tmp_n[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            (s.lvl[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
          (PlainMem c { s with tmp := tmp_n } ⋆ R) mk') ?_ ?_
      · rintro J1 ⟨kp', ⟨⟩⟩ mk' ⟨hkp'1, hkp'k, tmp_n, htnl, htn0, htn_f, htn_r, htn_l, htn_s,
            htn_c, hm_n⟩
        rw [Blocks.get_here]; ml_lets
        exact hJs (s.tmp_len - (k + 1).toNat) (kp', k + 1, ()) mk' (by omega)
          ⟨rfl, hkp'1, by omega, by omega, tmp_n, htnl, htn0, by rw [hk1]; exact htn_f,
           fun j hj => htn_r j (by omega), htn_l, htn_s,
           fun a ha1 ha2 j hj => htn_c a ha1 ha2 j (by omega), hm_n⟩
      · rintro J1 hJ1
        ml_ld c0_load_arena_tmp (s := { s with tmp := tmp_k }) (i := k) hk_tl hm_k
        ml_lets; ml_jnz; refine ⟨fun hne => ?_, fun heq => ?_⟩
        · have hne' : tmp_k[k.toNat]'hk_tl ≠ 0xFFFFFFFF#32 := by
            simp only [bne_iff_ne, ne_eq] at hne; exact hne
          ml_ld c0_load_arena_tmp (s := { s with tmp := tmp_k }) (i := k) hk_tl hm_k
          ml_lets
          ml_st m_n, hm_n := c0_store_arena_tmp (s := { s with tmp := tmp_k }) (i := kp)
            (tmp_k[k.toNat]'hk_tl) hkp_tl hm_k
          have hkp1' : (kp + 1).toNat = kp.toNat + 1 := by bv_omega
          have hkne : s.tmp[k.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
            rw [← hk_eq, List.getElem?_eq_getElem hk_tl, Option.getD_some]; exact hne'
          have hktl : k.toNat < s.tmp.length := by rw [hlen.tmp_len_arr]; omega
          have hk_get : s.tmp[k.toNat]?.getD 0#32 = s.tmp[k.toNat]'hktl := by
            rw [List.getElem?_eq_getElem hktl, Option.getD_some]
          have hval_k := hns_ok k.toNat (by omega) hkx hkne
          have hkv_eq : tmp_k[k.toNat]'hk_tl = s.tmp[k.toNat]'hktl := by
            rw [List.getElem?_eq_getElem hk_tl, List.getElem?_eq_getElem hktl] at hk_eq
            exact Option.some.inj hk_eq
          let tmp_n := tmp_k.set kp.toNat (tmp_k[k.toNat]'hk_tl)
          have hset_k : tmp_n[kp.toNat]?.getD 0#32 = s.tmp[k.toNat]?.getD 0#32 := by
            dsimp only [tmp_n]
            rw [List.getElem?_set_self (by rw [htkl]; omega), Option.getD_some, hkv_eq, hk_get]
          have htn_l : ∀ j, 1 ≤ j → j < (kp + 1).toNat →
              let l := (tmp_n[j]?.getD 0#32).toNat
              let lv := (s.lvl[l / 2]?.getD 0#32).toNat
              l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧ lv < s.cur_level := by
            intro j hj1 hj2; dsimp only [tmp_n]
            rw [hkp1'] at hj2
            by_cases hje : j = kp.toNat
            · subst j; simpa [tmp_n, hset_k] using hval_k
            · rw [List.getElem?_set_ne (Ne.symm hje)]
              exact htk_l j hj1 (by omega)
          have htn_s : ∀ a b, 1 ≤ a → a ≤ b → b < (kp + 1).toNat →
              (s.lvl[(tmp_n[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
              (s.lvl[(tmp_n[b]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
            intro a b ha1 hab hb2; dsimp only [tmp_n]
            rw [hkp1'] at hb2
            by_cases hbe : b = kp.toNat
            · subst b
              by_cases hae : a = kp.toNat
              · subst a; exact le_refl _
              · have h1 := htk_c a ha1 (by omega) k.toNat (le_refl _) hkx hkne
                rw [List.getElem?_set_ne (Ne.symm hae)]
                simpa [tmp_n, hset_k] using h1
            · rw [List.getElem?_set_ne (Ne.symm hbe), List.getElem?_set_ne (by omega)]
              exact htk_s a b ha1 hab (by omega)
          have htn_c : ∀ a, 1 ≤ a → a < (kp + 1).toNat → ∀ j, k.toNat + 1 ≤ j → j < s.tmp_len →
              s.tmp[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
              (s.lvl[(tmp_n[a]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
              (s.lvl[(s.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
            intro a ha1 ha2 j hj1 hj2 hjne; dsimp only [tmp_n]
            rw [hkp1'] at ha2
            by_cases hae : a = kp.toNat
            · subst a
              have h1 := hns_sort k.toNat j (by omega) (by omega) hj2 hkne hjne
              simpa [tmp_n, hset_k] using h1
            · rw [List.getElem?_set_ne (Ne.symm hae)]
              exact htk_c a ha1 (by omega) j (by omega) hj2 hjne
          ml_lets
          have hne_s : s.tmp[k.toNat]'hktl ≠ 0xFFFFFFFF#32 := hkv_eq ▸ hne'
          refine hJ1 (kp + 1, ()) m_n ⟨by omega, by omega, tmp_n, by rw [List.length_set, htkl],
            by rw [List.getElem?_set_ne (by omega)]; exact htk0, ?_, ?_, htn_l, htn_s, htn_c, hm_n⟩
          · rw [hkp1', htake_k, List.filter_append, list_take_succ_set _ (by omega), htk_f, hkv_eq]
            simp [hne_s]
          · intro j hj1 hj2; dsimp only [tmp_n]
            rw [List.getElem?_set_ne (by omega)]; exact htk_r j (by omega) hj2
        · ml_lets
          have heq' : tmp_k[k.toNat]'hk_tl = 0xFFFFFFFF#32 := by
            simp only [bne_eq_false_iff_eq] at heq; exact heq
          have hkeq : s.tmp[k.toNat]'(by rw [hlen.tmp_len_arr]; omega) = 0xFFFFFFFF#32 := by
            rw [List.getElem?_eq_getElem hk_tl,
              List.getElem?_eq_getElem (by rw [hlen.tmp_len_arr]; omega)] at hk_eq
            exact (Option.some.inj hk_eq) ▸ heq'
          refine hJ1 (kp, ()) mk ⟨hkp1, by omega, tmp_k, htkl, htk0, ?_, ?_, htk_l, htk_s, ?_, hm_k⟩
          · rw [htake_k, List.filter_append, htk_f]
            simp [hkeq]
          · intro j hj1 hj2; exact htk_r j (by omega) hj2
          · intro a ha1 ha2 j hj1 hj2 hjne; exact htk_c a ha1 ha2 j (by omega) hj2 hjne
    · have hke : k.toNat = s.tmp_len := by
        rw [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl_lt]
          at hge
        omega
      rw [hke] at htk_f hkpk
      ml_ld load_arena_mark (s := { s with tmp := tmp_k }) hm_k
      have hmin_k : PlainMinMarkInv c F0 { s with tmp := tmp_k }
          (((tmp_k.take kp.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := by
        have hflt_eq : (tmp_k.take kp.toNat).filter (· ≠ 0xFFFFFFFF#32) = tmp_k.take kp.toNat :=
          List.filter_eq_self.mpr fun x hx => by rw [htk_f, List.mem_filter] at hx; exact hx.2
        rw [hflt_eq, htk_f]
        exact ⟨hmin_in.mrk_dom, hmin_in.clr_cov, hmin_in.rem_sound⟩
      have hcore_k : PlainCoreInv c F0 { s with tmp := tmp_k } :=
        { hcore with
          lengths := { hcore.lengths with tmp_len_arr := htkl }
          arena := { hcore.arena with len_ok := hcore.arena.len_ok }
          watches := hcore.watches.with_wstk rfl rfl rfl rfl }
      refine min_shrink_clean_wp hcore_k hm_k hmin_k hno8 fun mrk' m' hml hmc hm' => ?_
      refine hpost tmp_k kp.toNat mrk' m' htkl hml hmc hkp1 hkpk htk0 ?_ htk_f ?_
      · intro j hj1 hj2
        have hjv := htk_l j hj1 hj2
        exact ⟨hjv.1, hjv.2.1, hjv.2.2.1, hjv.2.2.2,
          htk_s j (kp.toNat - 1) hj1 (by omega) (by omega)⟩
      · simpa [bv_ofNat_toNat_eq kp] using hm'
  · rintro Js hJs; ml_lets
    have h0lt : 0 < s.tmp.length := by rw [hlen.tmp_len_arr]; omega
    have htake1 : s.tmp.take 1 = [s.tmp[0]'h0lt] := by
      simpa using List.take_succ_eq_append_getElem (i := 0) h0lt
    have h0ne : (s.tmp[0]'h0lt) ≠ 0xFFFFFFFF#32 := by
      rwa [List.getElem?_eq_getElem h0lt, Option.getD_some] at h0_ok
    exact hJs (s.tmp_len - 1) (1#64, 1#64, ()) m
      ⟨by rw [h1v], by rw [h1v]; exact le_refl _, by rw [h1v]; exact le_refl _,
       htl1, s.tmp, hlen.tmp_len_arr, rfl,
       by rw [h1v, htake1]; simp [h0ne], fun _ _ _ => rfl,
       fun _ h1 h2 => by rw [h1v] at h2; omega,
       fun _ _ _ _ h => by rw [h1v] at h; omega,
       fun _ _ h => by rw [h1v] at h; omega, hm_in⟩

/-! ## 3. Outer block loop sub-expression (`minShrinkOuterExpr`) -/

private def minShrinkOuterExpr (p ld ld_1 ld_3 ld_4 ld_5 : Val i64) : Expr Val Cont [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) : Op Val [i64] :=
    Op.mk c (a, b, ())
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
              .call "plain_min_lit" (as := [i64, i32]) (bs := [.bool])
                (.var p, .var ld, ()) fun p =>
              .jnz (.var p.fst)
                (.let_ (op64 (.mul i64) (.var p_31.fst) (.imm 4)) fun p =>
                 .let_ (op64 (.add i64) (.var ld_3) (.var p.fst)) fun p =>
                 .store (t := i32) (.imm 4294967295) (.var p.fst) (.jump Js.fst ()))
                (.jump Js.fst ()))
             (.call "plain_shrink_blk" (as := [i64, i64, i64, i32, i64]) (bs := [])
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

private structure OuterInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (tmp1 : List (BitVec 32)) (end_b : Nat) (cur : PlainState) : Prop where
  core : PlainCoreInv c F0 cur
  min_inv : PlainMinMarkInv c F0 cur
    (((cur.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)
  entails : F0.EntailsClause (cnfClause
    (((cur.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
  no8 : ∀ v < c.mv, (cur.mrk[v]?.getD 0#8 &&& 8#8) = 0#8
  tl_eq : cur.tmp_len = s.tmp_len
  rel_eq : cur.heur.rel_trigger = s.heur.rel_trigger
  lvl_eq : cur.lvl = s.lvl
  vals_eq : cur.vals = s.vals
  clvl_eq : cur.cur_level = s.cur_level
  tpos_eq : cur.trail_pos = s.trail_pos
  prefix_eq : ∀ k < end_b, cur.tmp[k]? = tmp1[k]?
  rem_mrk : ∀ k < s.tmp_len, cur.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    let l := (cur.tmp[k]?.getD 0#32).toNat
    l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧ (cur.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8
  post_lvls : ∀ k, 1 ≤ k → k < s.tmp_len →
    cur.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    let l := (cur.tmp[k]?.getD 0#32).toNat
    0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
    (s.lvl[l / 2]?.getD 0#32).toNat = (s.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

private theorem min_shrink_lit_step {c : PlainCfg} {F0 : CNF Nat} {s cur : PlainState}
    {tmp1 : List (BitVec 32)} {beg : Nat} (ho : OuterInv c F0 s tmp1 (beg + 1) cur)
    (_hbeg1 : 1 ≤ beg) (hbeg_tl : beg < s.tmp_len) (htl_mv : s.tmp_len ≤ c.mv)
    {root_lit : BitVec 32} (hroot_eq : cur.tmp[beg]? = some root_lit)
    (hroot_ne : root_lit ≠ 0xFFFFFFFF#32)
    {ok : Bool} {mrk' : List (BitVec 8)} {mstk' mclr' : List (BitVec 32)}
    {mcl' : Nat} {mcf' : BitVec 64}
    (hlen' : ({ cur with mrk := mrk', min_stk := mstk', min_clr := mclr',
                         min_clr_len := mcl', min_clr_full := mcf' } : PlainState).LengthsOk c)
    (hmono2 : ∀ v < c.mv, (cur.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8 : ∀ v < c.mv, (mrk'[v]?.getD 0#8 &&& 8#8) = (cur.mrk[v]?.getD 0#8 &&& 8#8))
    (hmin' : PlainMinMarkInv c F0
      { cur with mrk := mrk', min_stk := mstk', min_clr := mclr',
                 min_clr_len := mcl', min_clr_full := mcf' }
      (((cur.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hok_true : ok = true →
      (∀ keep', (∀ l ∈ (((cur.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat),
          l = root_lit.toNat ∨ l ∈ keep') →
        PlainMinMarkInv c F0
          { cur with mrk := mrk', min_stk := mstk', min_clr := mclr',
                     min_clr_len := mcl', min_clr_full := mcf' } keep') ∧
      PlainMinMarkInv c F0
        (plainMinMarkState c
          { cur with mrk := mrk', min_stk := mstk', min_clr := mclr',
                     min_clr_len := mcl', min_clr_full := mcf' }
          (root_lit.toNat / 2) 2#8)
        (((cur.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) :
    let tmp_n := if ok then cur.tmp.set beg 0xFFFFFFFF#32 else cur.tmp
    let st_n : PlainState := { cur with
      tmp := tmp_n, mrk := mrk', min_stk := mstk', min_clr := mclr',
      min_clr_len := mcl', min_clr_full := mcf' }
    OuterInv c F0 s tmp1 beg st_n := by
  have hrm_b : cur.tmp[beg]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    rw [hroot_eq, Option.getD_some]; exact hroot_ne
  have hrb := ho.rem_mrk beg hbeg_tl hrm_b
  have hr_nat : (cur.tmp[beg]?.getD 0#32).toNat = root_lit.toNat := by
    rw [hroot_eq, Option.getD_some]
  cases ok with
  | false =>
    dsimp only
    let st_n : PlainState := { cur with
      mrk := mrk', min_stk := mstk', min_clr := mclr',
      min_clr_len := mcl', min_clr_full := mcf' }
    exact ⟨{ ho.core with
        lengths := hlen', arena := { ho.core.arena with len_ok := ho.core.arena.len_ok },
        watches := ho.core.watches.with_wstk rfl rfl rfl rfl },
      by simpa [ho.tl_eq] using hmin', ho.entails,
      fun v hv => by rw [hbit8 v hv]; exact ho.no8 v hv,
      ho.tl_eq, ho.rel_eq, ho.lvl_eq, ho.vals_eq, ho.clvl_eq, ho.tpos_eq,
      fun k hk => ho.prefix_eq k (by omega),
      fun k hk hne => by
        have hrk := ho.rem_mrk k hk hne
        have hrl : (cur.tmp[k]?.getD 0#32).toNat / 2 < c.mv := by have := hrk.1; omega
        exact ⟨hrk.1, hrk.2.1, hmono2 _ hrl hrk.2.2⟩,
      ho.post_lvls⟩
  | true =>
    dsimp only
    let tmp_n := cur.tmp.set beg 0xFFFFFFFF#32
    let st_base : PlainState := { cur with
      mrk := mrk', min_stk := mstk', min_clr := mclr',
      min_clr_len := mcl', min_clr_full := mcf' }
    let st_n : PlainState := { st_base with tmp := tmp_n }
    have htl_n : tmp_n.length = c.mv := by
      dsimp only [tmp_n]; rw [List.length_set, ho.core.lengths.tmp_len_arr]
    have hcore_base : PlainCoreInv c F0 st_base :=
      { ho.core with
        lengths := hlen', arena := { ho.core.arena with len_ok := ho.core.arena.len_ok },
        watches := ho.core.watches.with_wstk rfl rfl rfl rfl }
    have hcore_n : PlainCoreInv c F0 st_n :=
      { hcore_base with
        lengths := { hlen' with tmp_len_arr := htl_n }
        arena := { hcore_base.arena with len_ok := hcore_base.arena.len_ok }
        watches := hcore_base.watches.with_wstk rfl rfl rfl rfl }
    let keep' := ((tmp_n.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    have hsub : ∀ l ∈ (((cur.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat),
        l = root_lit.toNat ∨ l ∈ keep' := by
      intro l hl
      rw [mem_filter_map_toNat_take] at hl
      obtain ⟨k, hk, b, hkb, hne, rfl⟩ := hl
      by_cases hke : k = beg
      · subst k; rw [hkb] at hroot_eq; left; exact congrArg BitVec.toNat (Option.some.inj hroot_eq)
      · right
        rw [mem_filter_map_toNat_take]
        refine ⟨k, by dsimp only [tmp_n]; rw [List.length_set]; exact hk, b, ?_, hne, rfl⟩
        dsimp only [tmp_n]; rw [List.getElem?_set_ne (Ne.symm hke)]; exact hkb
    have hmin_base : PlainMinMarkInv c F0 st_base keep' := (hok_true rfl).1 keep' hsub
    have hmin_n : PlainMinMarkInv c F0 st_n keep' :=
      ⟨hmin_base.mrk_dom, hmin_base.clr_cov, hmin_base.rem_sound⟩
    have hent_n : F0.EntailsClause (cnfClause keep') := by
      refine plainMinMark_entails hcore_base hmin_base ho.entails fun l hl => ?_
      rw [mem_filter_map_toNat_take] at hl
      obtain ⟨k, hk, b, hkb, hne, rfl⟩ := hl
      have hk_tl : k < s.tmp_len := lt_of_lt_of_le hk (Nat.min_le_left _ _)
      have hkne : cur.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        rw [hkb, Option.getD_some]; exact hne
      have hrk := ho.rem_mrk k hk_tl hkne
      have hbk : (cur.tmp[k]?.getD 0#32).toNat = b.toNat := by rw [hkb, Option.getD_some]
      rw [hbk] at hrk
      refine ⟨hrk.1, by rw [ho.vals_eq]; exact hrk.2.1, ?_⟩
      rcases hsub b.toNat (mem_filter_map_toNat_take.mpr ⟨k, hk, b, hkb, hne, rfl⟩) with
        heqb | hin
      · right; rw [heqb, ← hr_nat]; exact hmono2 _ (by rw [hr_nat]; omega) hrb.2.2
      · exact Or.inl hin
    refine ⟨hcore_n, hmin_n, hent_n,
      fun v hv => by rw [hbit8 v hv]; exact ho.no8 v hv,
      ho.tl_eq, ho.rel_eq, ho.lvl_eq, ho.vals_eq, ho.clvl_eq, ho.tpos_eq,
      fun k hk => by
        simp only [↓reduceIte]
        rw [List.getElem?_set_ne (by omega)]; exact ho.prefix_eq k (by omega),
      fun k hk hne => ?_, fun k hk1 hk2 hne => ?_⟩
    · simp only [↓reduceIte] at hne ⊢
      by_cases hke : k = beg
      · subst k
        exfalso; apply hne
        rw [List.getElem?_set_self (by rw [ho.core.lengths.tmp_len_arr]; omega)]; rfl
      · rw [List.getElem?_set_ne (Ne.symm hke)] at hne ⊢
        have hrk := ho.rem_mrk k hk hne
        have hrl : (cur.tmp[k]?.getD 0#32).toNat / 2 < c.mv := by have := hrk.1; omega
        exact ⟨hrk.1, hrk.2.1, hmono2 _ hrl hrk.2.2⟩
    · simp only [↓reduceIte] at hne ⊢
      by_cases hke : k = beg
      · subst k
        exfalso; apply hne
        rw [List.getElem?_set_self (by rw [ho.core.lengths.tmp_len_arr]; omega)]; rfl
      · rw [List.getElem?_set_ne (Ne.symm hke)] at hne ⊢
        exact ho.post_lvls k hk1 hk2 hne

private theorem min_shrink_outer_wp {Γ : Env} {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    (hMl : ∀ args m Q X, plainMinLitSpec args m Q X →
      Γ "plain_min_lit" [i64, i32] [.bool] args m Q X)
    (hSb : ∀ args m Q X, plainShrinkBlkSpec args m Q X →
      Γ "plain_shrink_blk" [i64, i64, i64, i32, i64] [] args m Q X)
    {tmp1 : List (BitVec 32)} {s_in : PlainState} (ho_in : OuterInv c F0 s tmp1 s.tmp_len s_in)
    (htl1 : 1 ≤ s.tmp_len) (htl_mv : s.tmp_len ≤ c.mv)
    (htmp1_sort : ∀ i j, 1 ≤ i → i ≤ j → j < s.tmp_len →
      (s.lvl[(tmp1[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.lvl[(tmp1[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (htmp1_ne : ∀ k < s.tmp_len, tmp1[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (htmp1_lvls : ∀ k, 1 ≤ k → k < s.tmp_len →
      0 < (s.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < s.cur_level)
    {m : Mem 64} (hm_in : (PlainMem c s_in ⋆ R) m)
    (hpost : ∀ (tmp' : List (BitVec 32)) (tl' : Nat) (mrk' : List (BitVec 8))
        (mstk' mclr' : List (BitVec 32)) (mcl' : Nat) (mcf' : BitVec 64)
        (heur' : PlainHeur) (m' : Mem 64),
      let s' : PlainState := { s_in with
        tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk', min_clr := mclr',
        min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
      tmp'.length = c.mv → mrk'.length = c.mv → mstk'.length = 2 * c.minDepth →
      mclr'.length = c.mv → mcl' ≤ c.mv → MarksClear c s' →
      1 ≤ tl' → tl' ≤ s.tmp_len → tmp'[0]? = tmp1[0]? →
      heur'.LengthsOk c → heur'.rel_trigger = s.heur.rel_trigger →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧ lv < s.cur_level ∧
        lv ≤ (s.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      F0.EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (PlainMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (minShrinkOuterExpr c.hdr (BitVec.ofNat 64 c.mv)
      (BitVec.ofNat 64 s.tmp_len) c.pTmp c.pLevel c.pTrailPos) m := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  dsimp only [minShrinkOuterExpr]
  refine wp_loop_group (ts := [i64]) (fun n (end_b, ()) me =>
      n = end_b.toNat - 1 ∧ 1 ≤ end_b.toNat ∧ end_b.toNat ≤ s.tmp_len ∧
      ∃ (mrk_e : List (BitVec 8)) (tmp_e mstk_e mclr_e : List (BitVec 32))
        (mcl_e : Nat) (mcf_e : BitVec 64) (heur_e : PlainHeur),
      let cur : PlainState := { s_in with
        tmp := tmp_e, mrk := mrk_e, min_stk := mstk_e, min_clr := mclr_e,
        min_clr_len := mcl_e, min_clr_full := mcf_e, heur := heur_e }
      OuterInv c F0 s tmp1 end_b.toNat cur ∧ (PlainMem c cur ⋆ R) me) ?_ ?_
  · rintro Js0 n ⟨end_b, ⟨⟩⟩ me hJs0
      ⟨rfl, hend1, hend_tl, mrk_e, tmp_e, mstk_e, mclr_e, mcl_e, mcf_e, heur_e, ho, hm_e⟩
    let cur : PlainState := { s_in with
      tmp := tmp_e, mrk := mrk_e, min_stk := mstk_e, min_clr := mclr_e,
      min_clr_len := mcl_e, min_clr_full := mcf_e, heur := heur_e }
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hgt => ?_, fun hle => ?_⟩
    · c0_cond hgt
      have h1lt : 1 < end_b.toNat := by bv_omega
      have he1_nat : (end_b - 1).toNat = end_b.toNat - 1 := by bv_omega
      have he1_tl : (end_b - 1).toNat < cur.tmp.length := by
        dsimp only [cur]; rw [ho.core.lengths.tmp_len_arr]; omega
      ml_ld c0_load_arena_tmp (s := cur) (i := end_b - 1) he1_tl hm_e
      let lit_e1 := cur.tmp[(end_b - 1).toNat]'he1_tl
      have he1_t1 : cur.tmp[(end_b - 1).toNat]? = tmp1[(end_b - 1).toNat]? :=
        ho.prefix_eq _ (by omega)
      have hne_e1 : cur.tmp[(end_b - 1).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        rw [he1_t1]; exact htmp1_ne (end_b - 1).toNat (by omega)
      have hl_e1 : lit_e1.toNat < 2 * c.mv := by
        have hrm := ho.rem_mrk (end_b - 1).toNat (by omega) hne_e1
        rw [List.getElem?_eq_getElem he1_tl, Option.getD_some] at hrm
        exact hrm.1
      have he1_var_lt : (lit_e1 >>> 1).toNat < c.mv := by rw [bv32_lshr_1]; omega
      have he1_lvl_l : ((lit_e1 >>> 1).setWidth 64).toNat < cur.lvl.length := by
        rw [ho.core.lengths.lvl_len, bv_c0_zext32_64]; exact he1_var_lt
      ml_ld c0_load_arena_lvl (s := cur) (i := (lit_e1 >>> 1).setWidth 64) he1_lvl_l hm_e
      ml_ld c0_load_arena_tmp (s := cur) (i := end_b - 1) he1_tl hm_e
      have he1_tp_l : ((lit_e1 >>> 1).setWidth 64).toNat < cur.trail_pos.length := by
        rw [ho.core.lengths.trail_pos_len, bv_c0_zext32_64]; exact he1_var_lt
      ml_ld c0_load_arena_tpos (s := cur) (i := (lit_e1 >>> 1).setWidth 64) he1_tp_l hm_e
      let blvl := cur.lvl[((lit_e1 >>> 1).setWidth 64).toNat]'he1_lvl_l
      let mtr0 := cur.trail_pos[((lit_e1 >>> 1).setWidth 64).toNat]'he1_tp_l
      have hlit_e1_t1 : (tmp1[(end_b - 1).toNat]?.getD 0#32).toNat = lit_e1.toNat := by
        rw [← he1_t1, List.getElem?_eq_getElem he1_tl, Option.getD_some]
      have hblvl_eq : blvl.toNat = (s.lvl[lit_e1.toNat / 2]?.getD 0#32).toNat := by
        dsimp only [blvl]
        rw [← ho.lvl_eq, ← bv32_lshr_1 lit_e1, ← bv_c0_zext32_64 (lit_e1 >>> 1),
          List.getElem?_eq_getElem he1_lvl_l, Option.getD_some]
      have hblvl_bounds : 0 < blvl.toNat ∧ blvl.toNat < s.cur_level := by
        rw [hblvl_eq, ← hlit_e1_t1]
        exact htmp1_lvls (end_b - 1).toNat (by omega) (by omega)
      have hm_e' : (PlainMem c cur ⋆ R) me := hm_e
      ml_lets
      refine wp_loop_group (ts := [i64, i64]) (fun n1 (beg', max_tr', ()) m_s =>
          n1 = beg'.toNat - 1 ∧ m_s = me ∧ 1 ≤ beg'.toNat ∧ beg'.toNat < end_b.toNat ∧
          ∀ k, beg'.toNat ≤ k → k < end_b.toNat →
            (s.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat ∧
            (s.trail_pos[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_tr'.toNat)
        ?_ ?_
      · rintro Js_1 n1 ⟨beg', max_tr', ⟨⟩⟩ m_s hJs_1 ⟨rfl, rfl, hbg1, hbg_end, hscan⟩
        rw [Blocks.get_here]
        refine wp_join_group (ts := []) (fun () m_exit => m_exit = m_s) ?_ ?_
        · rintro Js_2 ⟨⟩ m_exit rfl
          rw [Blocks.get_here]
          refine wp_join_group (ts := []) (fun () mf =>
              ∃ (mrk_f : List (BitVec 8)) (tmp_f mstk_f mclr_f : List (BitVec 32))
                (mcl_f : Nat) (mcf_f : BitVec 64) (heur_f : PlainHeur),
              let cf : PlainState := { s_in with
                tmp := tmp_f, mrk := mrk_f, min_stk := mstk_f, min_clr := mclr_f,
                min_clr_len := mcl_f, min_clr_full := mcf_f, heur := heur_f }
              OuterInv c F0 s tmp1 beg'.toNat cf ∧ (PlainMem c cf ⋆ R) mf) ?_ ?_
          · rintro Js ⟨⟩ mf ⟨mrk_f, tmp_f, mstk_f, mclr_f, mcl_f, mcf_f, heur_f, hof, hmf⟩
            rw [Blocks.get_here]; ml_lets
            exact hJs0 (beg'.toNat - 1) (beg', ()) mf (by omega)
              ⟨rfl, hbg1, by omega, mrk_f, tmp_f, mstk_f, mclr_f, mcl_f, mcf_f, heur_f, hof, hmf⟩
          · rintro Js hJs
            ml_lets; ml_jnz; refine ⟨fun hdiff1 => ?_, fun hdiff_ne => ?_⟩
            · c0_cond hdiff1
              have hend_eq : end_b.toNat = beg'.toNat + 1 := by bv_omega
              refine wp_join_group (ts := []) (fun () mf =>
                  ∃ (mrk_f : List (BitVec 8)) (tmp_f mstk_f mclr_f : List (BitVec 32))
                    (mcl_f : Nat) (mcf_f : BitVec 64) (heur_f : PlainHeur),
                  let cf : PlainState := { s_in with
                    tmp := tmp_f, mrk := mrk_f, min_stk := mstk_f, min_clr := mclr_f,
                    min_clr_len := mcl_f, min_clr_full := mcf_f, heur := heur_f }
                  OuterInv c F0 s tmp1 beg'.toNat cf ∧ (PlainMem c cf ⋆ R) mf) ?_ ?_
              · rintro Js_3 ⟨⟩ mf hmf
                rw [Blocks.get_here]; ml_lets; exact hJs () mf hmf
              · rintro Js_3 hJs_3
                have hbg_tl : beg'.toNat < cur.tmp.length := by
                  dsimp only [cur]; rw [ho.core.lengths.tmp_len_arr]; omega
                ml_ld c0_load_arena_tmp (s := cur) (i := beg') hbg_tl hm_e'
                let rlit := cur.tmp[beg'.toNat]'hbg_tl
                have hr_t1 : cur.tmp[beg'.toNat]? = tmp1[beg'.toNat]? :=
                  ho.prefix_eq _ hbg_end
                have hr_ne : rlit ≠ 0xFFFFFFFF#32 := by
                  have := htmp1_ne beg'.toNat (by omega)
                  rw [← hr_t1, List.getElem?_eq_getElem hbg_tl, Option.getD_some] at this
                  exact this
                have hrm_b := ho.rem_mrk beg'.toNat (by omega) (by
                  rw [List.getElem?_eq_getElem hbg_tl, Option.getD_some]; exact hr_ne)
                rw [List.getElem?_eq_getElem hbg_tl, Option.getD_some] at hrm_b
                have hr_lt : rlit.toNat < 2 * c.mv := hrm_b.1
                have hr_vals : cur.vals[rlit.toNat]?.getD 0#8 = 0xFF#8 := by
                  rw [ho.vals_eq]; exact hrm_b.2.1
                ml_lets; apply wp_call_of_spec; apply hMl
                refine ⟨c, F0, cur,
                  (((cur.tmp.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat), R,
                  rfl, ho.core, ho.min_inv, hr_lt, hr_vals, fun _ hv _ => ho.no8 _ hv, hm_e',
                  fun ok mrk' mstk' mclr' mcl' mcf' m' hlen' hmono2' hbit8' hmin' hokt hm' => ?_⟩
                have hstep := min_shrink_lit_step (beg := beg'.toNat)
                  (by rw [← hend_eq]; exact ho) hbg1 (by omega) htl_mv
                  (List.getElem?_eq_getElem hbg_tl) hr_ne hlen' hmono2' hbit8' hmin' hokt
                dsimp only; ml_lets; ml_jnz; refine ⟨fun htrue => ?_, fun hfalse => ?_⟩
                · ml_st mf, hmf := c0_store_arena_tmp (s := { cur with
                      mrk := mrk', min_stk := mstk', min_clr := mclr',
                      min_clr_len := mcl', min_clr_full := mcf' })
                    (i := beg') 0xFFFFFFFF#32 (by
                      dsimp only; rw [hlen'.tmp_len_arr]; omega) hm'
                  rw [htrue] at hstep
                  ml_lets
                  exact hJs_3 () mf ⟨mrk', cur.tmp.set beg'.toNat 0xFFFFFFFF#32, mstk', mclr',
                    mcl', mcf', heur_e, hstep, hmf⟩
                · rw [hfalse] at hstep
                  ml_lets
                  exact hJs_3 () m' ⟨mrk', cur.tmp, mstk', mclr', mcl', mcf', heur_e, hstep, hm'⟩
            · ml_lets; apply wp_call_of_spec; apply hSb
              have htake_cur : cur.tmp.take cur.tmp_len = cur.tmp.take s.tmp_len := by
                rw [ho.tl_eq]
              have hmin_cur : PlainMinMarkInv c F0 cur
                  (((cur.tmp.take cur.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) := by
                rw [htake_cur]; exact ho.min_inv
              have hent_cur : F0.EntailsClause (cnfClause
                  (((cur.tmp.take cur.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) := by
                rw [htake_cur]; exact ho.entails
              have hblvl_cur_lt : (cur.lvl[((lit_e1 >>> 1).setWidth 64).toNat]'he1_lvl_l).toNat <
                  cur.cur_level := by
                change blvl.toNat < cur.cur_level
                rw [ho.clvl_eq]; exact hblvl_bounds.2
              refine ⟨c, F0, cur, R, rfl, ho.core, hmin_cur, ho.no8,
                hbg1, hbg_end, by rw [ho.tl_eq]; exact hend_tl, by rw [ho.tl_eq]; exact htl_mv,
                hblvl_bounds.1, hblvl_cur_lt, hent_cur, ?_, ?_,
                hm_e', fun tmp_f mrk_f mstk_f mclr_f mcl_f mcf_f heur_f m_f
                  hcore_f hmin_f hno8_f htl_f hrel_f hmono2_f hother_f hlvl_f hent_f
                  hrem_f hm_f => ?_⟩
              · intro k hk1 hk2
                change beg'.toNat ≤ k at hk1
                change k < end_b.toNat at hk2
                have hpk : cur.tmp[k]? = tmp1[k]? := ho.prefix_eq k hk2
                have hkne : cur.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                  rw [hpk]; exact htmp1_ne k (by omega)
                have hrk := ho.rem_mrk k (by omega) hkne
                have hsc := hscan k hk1 hk2
                rw [hpk] at hrk ⊢
                have hlb_c : (cur.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                    blvl.toNat := by
                  rw [ho.lvl_eq]; exact hsc.1
                exact ⟨hrk.1, by rw [ho.vals_eq]; exact hrk.2.1, hlb_c,
                  by rw [ho.tpos_eq]; exact hsc.2⟩
              · intro k hk hne
                rw [ho.tl_eq] at hk
                have hrk := ho.rem_mrk k hk hne
                exact ⟨hrk.1, by rw [ho.vals_eq]; exact hrk.2.1, hrk.2.2⟩
              · let cf : PlainState := { cur with
                    tmp := tmp_f, mrk := mrk_f, min_stk := mstk_f, min_clr := mclr_f,
                    min_clr_len := mcl_f, min_clr_full := mcf_f, heur := heur_f }
                have htake_eq : tmp_f.take cur.tmp_len = tmp_f.take s.tmp_len := by rw [ho.tl_eq]
                rw [htake_eq] at hmin_f hent_f
                rw [ho.tl_eq] at hother_f hrem_f
                have hof : OuterInv c F0 s tmp1 beg'.toNat cf :=
                  ⟨hcore_f, hmin_f, hent_f, hno8_f, ho.tl_eq,
                   by dsimp only [cf]; rw [hrel_f, ho.rel_eq],
                   ho.lvl_eq, ho.vals_eq, ho.clvl_eq, ho.tpos_eq,
                   fun k hk => by
                     rw [hother_f k (by omega)
                       (by change k < beg'.toNat ∨ end_b.toNat ≤ k; exact Or.inl hk)]
                     exact ho.prefix_eq k (by omega),
                   fun k hk hne => by
                     have hrk := hrem_f k hk hne
                     exact ⟨hrk.1, by dsimp only at hrk; rw [← ho.vals_eq]; exact hrk.2.1, hrk.2.2⟩,
                   fun k hk1 hk2 hne => by
                     by_cases hmid : beg'.toNat ≤ k ∧ k < end_b.toNat
                     · have hlv := hlvl_f k hmid.1 hmid.2 hne
                       have hlv_s : (s.lvl[(tmp_f[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                           blvl.toNat := by
                         rw [← ho.lvl_eq]; exact hlv
                       have hsc := hscan k hmid.1 hmid.2
                       exact ⟨hlv_s ▸ hblvl_bounds.1, hlv_s ▸ hblvl_bounds.2,
                         hlv_s.trans hsc.1.symm⟩
                     · have hoth := hother_f k hk2
                         (by change k < beg'.toNat ∨ end_b.toNat ≤ k; omega)
                       have hne' : cur.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                         rwa [← hoth]
                       dsimp only [cf]; rw [hoth]; exact ho.post_lvls k hk1 hk2 hne'⟩
                ml_lets
                exact hJs () m_f ⟨mrk_f, tmp_f, mstk_f, mclr_f, mcl_f, mcf_f, heur_f, hof, hm_f⟩
        · rintro Js_2 hJs_2
          ml_lets; ml_jnz; refine ⟨fun hbg1' => ?_, fun hbg_le1 => ?_⟩
          · c0_cond hbg1'
            have h1_bg : 1 < beg'.toNat := by bv_omega
            have hbm1 : (beg' - 1).toNat = beg'.toNat - 1 := by bv_omega
            have hbm_tl : (beg' - 1).toNat < cur.tmp.length := by
              dsimp only [cur]; rw [ho.core.lengths.tmp_len_arr]; omega
            ml_ld c0_load_arena_tmp (s := cur) (i := beg' - 1) hbm_tl hm_e'
            let lit_b := cur.tmp[(beg' - 1).toNat]'hbm_tl
            have hb_t1 : cur.tmp[(beg' - 1).toNat]? = tmp1[(beg' - 1).toNat]? :=
              ho.prefix_eq _ (by omega)
            have hne_b : cur.tmp[(beg' - 1).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
              rw [hb_t1]; exact htmp1_ne (beg' - 1).toNat (by omega)
            have hl_b : lit_b.toNat < 2 * c.mv := by
              have hrm := ho.rem_mrk (beg' - 1).toNat (by omega) hne_b
              rw [List.getElem?_eq_getElem hbm_tl, Option.getD_some] at hrm; exact hrm.1
            have hb_var_lt : (lit_b >>> 1).toNat < c.mv := by rw [bv32_lshr_1]; omega
            have hb_lvl_l : ((lit_b >>> 1).setWidth 64).toNat < cur.lvl.length := by
              rw [ho.core.lengths.lvl_len, bv_c0_zext32_64]; exact hb_var_lt
            ml_ld c0_load_arena_lvl (s := cur) (i := (lit_b >>> 1).setWidth 64) hb_lvl_l hm_e'
            ml_lets; ml_jnz; refine ⟨fun hlvl_eq => ?_, fun hlvl_ne => ?_⟩
            · ml_ld c0_load_arena_tmp (s := cur) (i := beg' - 1) hbm_tl hm_e'
              have hb_tp_l : ((lit_b >>> 1).setWidth 64).toNat < cur.trail_pos.length := by
                rw [ho.core.lengths.trail_pos_len, bv_c0_zext32_64]; exact hb_var_lt
              ml_ld c0_load_arena_tpos (s := cur) (i := (lit_b >>> 1).setWidth 64) hb_tp_l hm_e'
              let tp_b := (cur.trail_pos[((lit_b >>> 1).setWidth 64).toNat]'hb_tp_l).setWidth 64
              have hlit_b_t1 : (tmp1[(beg' - 1).toNat]?.getD 0#32).toNat = lit_b.toNat := by
                rw [← hb_t1, List.getElem?_eq_getElem hbm_tl, Option.getD_some]
              have hlb_eq : (s.lvl[(tmp1[(beg' - 1).toNat]?.getD 0#32).toNat / 2]?.getD
                  0#32).toNat = blvl.toNat := by
                have hbl := hb_lvl_l; dsimp only [cur] at hbl
                rw [hlit_b_t1, ← ho.lvl_eq, ← bv32_lshr_1 lit_b, ← bv_c0_zext32_64 (lit_b >>> 1),
                  List.getElem?_eq_getElem hbl, Option.getD_some]
                exact congrArg BitVec.toNat (beq_iff_eq.mp hlvl_eq)
              have htp_b_eq :
                  (s.trail_pos[(tmp1[(beg' - 1).toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                  tp_b.toNat := by
                dsimp only [tp_b]
                have htp := hb_tp_l; dsimp only [cur] at htp
                rw [hlit_b_t1, ← ho.tpos_eq, bv_c0_zext32_64, ← bv32_lshr_1 lit_b,
                  ← bv_c0_zext32_64 (lit_b >>> 1), List.getElem?_eq_getElem htp, Option.getD_some]
              ml_lets
              refine wp_join_group (ts := [i64]) (fun (mx, ()) mn =>
                  mn = m_s ∧ max_tr'.toNat ≤ mx.toNat ∧ tp_b.toNat ≤ mx.toNat) ?_ ?_
              · rintro Js ⟨mx, ⟨⟩⟩ mn ⟨rfl, hmx1, hmx2⟩
                rw [Blocks.get_here]; ml_lets
                refine hJs_1 ((beg' - 1).toNat - 1) (beg' - 1, mx, ()) mn (by omega)
                  ⟨rfl, rfl, by omega, by omega, fun k hk1 hk2 => ?_⟩
                by_cases hke : k = (beg' - 1).toNat
                · subst k; exact ⟨hlb_eq, by rw [htp_b_eq]; exact hmx2⟩
                · have hsc := hscan k (by omega) hk2
                  exact ⟨hsc.1, le_trans hsc.2 hmx1⟩
              · rintro Js hJs
                ml_lets; ml_jnz; refine ⟨fun hmgt => ?_, fun hmle => ?_⟩
                · rw [BitVec.ult, decide_eq_true_eq] at hmgt
                  exact hJs (tp_b, ()) m_s ⟨rfl, le_of_lt hmgt, le_refl _⟩
                · rw [BitVec.ult, decide_eq_false_iff_not] at hmle
                  exact hJs (max_tr', ()) m_s ⟨rfl, le_refl _, Nat.le_of_not_lt hmle⟩
            · ml_lets; exact hJs_2 () m_s rfl
          · ml_lets; exact hJs_2 () m_s rfl
      · rintro Js_1 hJs_1; ml_lets
        have hm0_eq : (s.trail_pos[(tmp1[(end_b - 1).toNat]?.getD 0#32).toNat / 2]?.getD
            0#32).toNat = (mtr0.setWidth 64).toNat := by
          dsimp only [mtr0]
          rw [hlit_e1_t1, ← ho.tpos_eq, bv_c0_zext32_64, ← bv32_lshr_1 lit_e1,
            ← bv_c0_zext32_64 (lit_e1 >>> 1), List.getElem?_eq_getElem he1_tp_l, Option.getD_some]
        refine hJs_1 ((end_b - 1).toNat - 1) (end_b - 1, mtr0.setWidth 64, ()) me
          ⟨rfl, rfl, by omega, by omega, fun k hk1 hk2 => ?_⟩
        have hke : k = (end_b - 1).toNat := by omega
        subst k; rw [hlit_e1_t1]
        exact ⟨hblvl_eq.symm, by rw [← hlit_e1_t1, hm0_eq]; exact le_refl _⟩
    · c0_cond hle
      have hend_eq : end_b.toNat = 1 := by bv_omega
      rw [hend_eq] at ho
      have hmin_c := ho.min_inv; rw [← ho.tl_eq] at hmin_c
      have h0_c : cur.tmp[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        rw [ho.prefix_eq 0 (by omega)]; exact htmp1_ne 0 (by omega)
      have hcomp : wp Γ Q X (minShrinkCompactExpr c.hdr (BitVec.ofNat 64 c.mv)
          (BitVec.ofNat 64 cur.tmp_len) c.pTmp) me := by
        refine min_shrink_compact_wp ho.core (by rw [ho.tl_eq]; exact htl1)
          (by rw [ho.tl_eq]; exact htl_mv) hmin_c ho.no8 h0_c ?_ ?_ hm_e ?_
        · intro k hk1 hk2 hne
          rw [ho.tl_eq] at hk2
          have hrk := ho.rem_mrk k hk2 hne
          have hpk := ho.post_lvls k hk1 hk2 hne
          rw [← ho.lvl_eq, ← ho.clvl_eq] at hpk; rw [← ho.vals_eq] at hrk
          exact ⟨hrk.1, hrk.2.1, hpk.1, hpk.2.1⟩
        · intro i j hi1 hij hj hne_i hne_j
          rw [ho.tl_eq] at hj
          have hpi := ho.post_lvls i hi1 (by omega) hne_i
          have hpj := ho.post_lvls j (by omega) hj hne_j
          rw [ho.lvl_eq, hpi.2.2, hpj.2.2]
          exact htmp1_sort i j hi1 (by omega) hj
        · intro tmp' tl' mrk' m' heur_c s_c htl_f hml_f hmc_f h1_f htl_le h0_f hns_f
            htake_f hm_f
          have hent_f : F0.EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) := by
            rw [htake_f]
            change F0.EntailsClause (cnfClause
              (((cur.tmp.take cur.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
            rw [ho.tl_eq]; exact ho.entails
          have h0_fin : tmp'[0]? = tmp1[0]? := h0_f.trans (ho.prefix_eq 0 (by omega))
          have hns_fin : ∀ j, 1 ≤ j → j < tl' →
              let l := (tmp'[j]?.getD 0#32).toNat
              let lv := (s.lvl[l / 2]?.getD 0#32).toNat
              l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧ lv < s.cur_level ∧
              lv ≤ (s.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
            intro j hj1 hj2
            have hv_eq : s_in.vals = s.vals := ho.vals_eq
            have hl_eq : s_in.lvl = s.lvl := ho.lvl_eq
            have hcl_eq : s_in.cur_level = s.cur_level := ho.clvl_eq
            simpa [hv_eq, hl_eq, hcl_eq] using hns_f j hj1 hj2
          have hlen_e := ho.core.lengths
          refine hpost tmp' tl' mrk' mstk_e mclr_e 0 0#64 heur_c m'
            htl_f hml_f hlen_e.min_stk_len hlen_e.min_clr_len_arr (Nat.zero_le _)
            hmc_f h1_f (by rw [← ho.tl_eq]; exact htl_le) h0_fin
            (min_shrink_heur_ok hlen_e.heur_ok) ho.rel_eq hns_fin hent_f hm_f
      rwa [ho.tl_eq] at hcomp
  · rintro Js0 hJs0; ml_lets
    have htl_lt : s.tmp_len < 2 ^ 64 := by omega
    have htl_bv : (BitVec.ofNat 64 s.tmp_len).toNat = s.tmp_len := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl_lt]
    exact hJs0 (s.tmp_len - 1) (BitVec.ofNat 64 s.tmp_len, ()) m
      ⟨by rw [htl_bv], by rw [htl_bv]; exact htl1, by rw [htl_bv]; exact le_refl _,
       s_in.mrk, s_in.tmp, s_in.min_stk, s_in.min_clr, s_in.min_clr_len, s_in.min_clr_full,
       s_in.heur, by rw [htl_bv]; exact ho_in, hm_in⟩

/-! ## 4. Main `plain_min_shrink_wp` contract theorem -/

theorem plain_min_shrink_wp (Γ : Env)
    (hSt : ∀ args m Q X, plainSortTmpSpec args m Q X →
      Γ "plain_sort_tmp" [i64] [] args m Q X)
    (hMm : ∀ args m Q X, plainMinMarkSpec args m Q X →
      Γ "plain_min_mark" [i64, i32, i8] [] args m Q X)
    (hMl : ∀ args m Q X, plainMinLitSpec args m Q X →
      Γ "plain_min_lit" [i64, i32] [.bool] args m Q X)
    (hSb : ∀ args m Q X, plainShrinkBlkSpec args m Q X →
      Γ "plain_shrink_blk" [i64, i64, i64, i32, i64] [] args m Q X) :
    ∀ args m Q X, plainMinShrinkSpec args m Q X →
      Func.wp Γ plain_min_shrink_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, htl1, htl_mv, hEnt0, htmp_vals, htmp_lvls, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hlen0 := hinv.core.lengths
  dsimp only [Func.wp, plain_min_shrink_body]
  ml_ld load_arena_mv hm
  ml_lets
  ml_ld load_arena_tmp_len hm
  ml_lets
  ml_ld load_arena_conflicts hm
  ml_lets
  ml_st m0, hm0 := store_arena_conflicts (s.heur.conflicts + 1) hm
  let s0 : PlainState := { s with heur := { s.heur with conflicts := s.heur.conflicts + 1 } }
  have hs0_inv : PlainInv c F0 s0 :=
    hinv.with_heur (min_shrink_heur_ok hlen0.heur_ok)
  clear hinv
  refine wp_join_group (ts := []) (fun () mq =>
      ∃ (tmp' : List (BitVec 32)) (tl' : Nat) (mrk' : List (BitVec 8))
        (mstk' mclr' : List (BitVec 32)) (mcl' : Nat) (mcf' : BitVec 64) (heur' : PlainHeur),
      let s' : PlainState := { s with
        tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk', min_clr := mclr',
        min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
      PlainInv c F0 s' ∧ 1 ≤ tl' ∧ tl' ≤ s.tmp_len ∧ tmp'[0]? = s.tmp[0]? ∧
      heur'.rel_trigger = s.heur.rel_trigger ∧
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧ lv < s.cur_level ∧
        lv ≤ (s.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      F0.EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) ∧
      (PlainMem c s' ⋆ R) mq) ?_ ?_
  · rintro Js ⟨⟩ mq ⟨tmp', tl', mrk', mstk', mclr', mcl', mcf', heur', hinv',
        h1', htl', h0', hrel', hns', hent', hmq⟩
    rw [Blocks.get_here]
    let sf : PlainState := { s with
      tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk', min_clr := mclr',
      min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
    ml_ld load_arena_learned_lits (s := sf) hmq
    ml_lets
    ml_st m_f, hm_f := store_arena_learned_lits (s := sf)
      (heur'.learned_lits + BitVec.ofNat 64 s.tmp_len) hmq
    rw [wp]
    have hinv_f : PlainInv c F0 { sf with heur := { heur' with
        learned_lits := heur'.learned_lits + BitVec.ofNat 64 s.tmp_len } } :=
      hinv'.with_heur (min_shrink_heur_ok hinv'.core.lengths.heur_ok)
    exact hQ tmp' tl' mrk' mstk' mclr' mcl' mcf'
      { heur' with learned_lits := heur'.learned_lits + BitVec.ofNat 64 s.tmp_len } m_f
      hinv_f h1' htl' h0' hrel' hns' hent' hm_f
  · rintro Js hJs
    ml_lets; ml_jnz; refine ⟨fun hle1 => ?_, fun hgt1 => ?_⟩
    · c0_cond hle1
      have htl_eq1 : s.tmp_len = 1 := by bv_omega
      ml_lets
      exact hJs () m0 ⟨s.tmp, s.tmp_len, s.mrk, s.min_stk, s.min_clr, s.min_clr_len,
        s.min_clr_full, s0.heur, hs0_inv, htl1, le_refl _, rfl, rfl,
        fun _ h1 h2 => by omega, hEnt0, hm0⟩
    · c0_cond hgt1
      have h2lt : 2 ≤ s.tmp_len := by bv_omega
      ml_lets; ml_jnz; refine ⟨fun hoob => ?_, fun hinb => ?_⟩
      · exfalso; c0_cond hoob; bv_omega
      · clear hinb
        ml_lets; apply wp_call_of_spec; apply hSt
        refine ⟨c, s0, R, rfl, hs0_inv.core.lengths, htl_mv,
          fun k hk1 hk2 => (htmp_vals k (by omega)).1, hm0,
          fun tmp1 m1 ht1_len ht1_0 ht1_r ht1_l ht1_sort hm1 => ?_⟩
        obtain ⟨hkeep_eq, hEnt1, htmp1_vals, htmp1_lvls⟩ := min_shrink_post_sort
          htl1 htl_mv hlen0.tmp_len_arr hEnt0 htmp_vals htmp_lvls
          ht1_len ht1_0 ht1_r ht1_l
        let s1 : PlainState := { s0 with tmp := tmp1 }
        ml_ld load_arena_tmp_lits (s := s1) hm1
        ml_ld load_arena_level (s := s1) hm1
        ml_ld load_arena_trail_pos (s := s1) hm1
        ml_st m2, hm2 := store_arena_min_clr_len (s := s1) 0 (Nat.zero_lt_succ _) hm1
        ml_st m3, hm3 := store_arena_min_clr_full (s := { s1 with min_clr_len := 0 }) 0#64 hm2
        let s2 : PlainState := { s1 with min_clr_len := 0, min_clr_full := 0#64 }
        have hmcl_le0 : s2.min_clr_len ≤ c.mv := by dsimp only [s2]; omega
        have hs2_len : s2.LengthsOk c :=
          { hs0_inv.core.lengths with tmp_len_arr := ht1_len, min_clr_len_le := hmcl_le0 }
        have hs2_core : PlainCoreInv c F0 s2 :=
          { hs0_inv.core with
            lengths := hs2_len
            arena := { hs0_inv.core.arena with len_ok := hs0_inv.core.arena.len_ok }
            watches := hs0_inv.core.watches.with_wstk rfl rfl rfl rfl }
        have hs2_mc : MarksClear c s2 := hs0_inv.marks
        let keep0 := ((tmp1.take s.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
        have hmin2_init : PlainMinMarkInv c F0 s2 keep0 :=
          plainMinMarkInv_init hs2_core hs2_mc keep0
        clear hm hm0 m0 hm1 m1 hm2 m2 hs0_inv htmp_vals htmp_lvls hEnt0 hkeep_eq
        refine wp_loop_group (ts := [i64]) (fun n (i_bv, ()) mi =>
            n = s.tmp_len - i_bv.toNat ∧ i_bv.toNat ≤ s.tmp_len ∧
            ∃ (mrk_i : List (BitVec 8)) (mclr_i : List (BitVec 32))
              (mcl_i : Nat) (mcf_i : BitVec 64),
            let cur : PlainState := { s2 with
              mrk := mrk_i, min_clr := mclr_i, min_clr_len := mcl_i, min_clr_full := mcf_i }
            mrk_i.length = c.mv ∧ mclr_i.length = c.mv ∧ mcl_i ≤ c.mv ∧
            PlainMinMarkInv c F0 cur keep0 ∧
            (∀ v < c.mv, (mrk_i[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
            (∀ j < i_bv.toNat, (mrk_i[(tmp1[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
            (PlainMem c cur ⋆ R) mi) ?_ ?_
        · rintro Jm n ⟨i_bv, ⟨⟩⟩ mi hJm
            ⟨rfl, hile, mrk_i, mclr_i, mcl_i, mcf_i, hmrkl, hmclrl, hmcll, hmin_i, hno8_i,
              hmark_i, hm_i⟩
          let cur : PlainState := { s2 with
            mrk := mrk_i, min_clr := mclr_i, min_clr_len := mcl_i, min_clr_full := mcf_i }
          rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
          · c0_cond hlt
            have hix : i_bv.toNat < s.tmp_len := by bv_omega
            have hi_tl : i_bv.toNat < cur.tmp.length := by
              dsimp only [cur, s2]; rw [ht1_len]; omega
            ml_ld c0_load_arena_tmp (s := cur) (i := i_bv) hi_tl hm_i
            let lit_i := tmp1[i_bv.toNat]'(by rw [ht1_len]; omega)
            have hl_i := htmp1_vals i_bv.toNat hix
            rw [List.getElem?_eq_getElem (by rw [ht1_len]; omega), Option.getD_some] at hl_i
            have hlit_lt : lit_i.toNat < 2 * c.mv := hl_i.2.1
            have hv_i : (lit_i >>> 1).toNat < c.mv := by rw [bv32_lshr_1]; omega
            have hv_i' : lit_i.toNat / 2 < c.mv := by omega
            have hcore_i : PlainCoreInv c F0 cur :=
              coreInv_with_min hs2_core hmrkl hs2_core.lengths.min_stk_len hmclrl hmcll
            ml_lets; apply wp_call_of_spec; apply hMm
            refine plainMinMarkSpec_step hcore_i.lengths hm_i (lit_i >>> 1) hv_i
              ((2 : BitVec 32).setWidth 8) fun m_n hm_n => ?_
            have h2_eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl
            rw [h2_eq, bv32_lshr_1] at hm_n
            let nxt := plainMinMarkStepState c cur (lit_i.toNat / 2) 2#8
            have hnxt_eq : { s2 with
                mrk := nxt.mrk, min_clr := nxt.min_clr,
                min_clr_len := nxt.min_clr_len, min_clr_full := nxt.min_clr_full } = nxt := by
              dsimp only [nxt, plainMinMarkStepState, plainMinMarkState, cur]
              split <;> (try split) <;> rfl
            have hlen_n := plainMinMarkStepState_lengths hcore_i.lengths (lit_i.toNat / 2) 2#8
            have hmin_n := plainMinMarkInv_step_keep hcore_i hmin_i hlit_lt hl_i.2.2.2
              hl_i.2.2.1 (hno8_i _ hv_i')
            obtain ⟨hbit8_n, hmono2_n⟩ := plainMinMarkStepState_bit8_mono2 hcore_i.lengths
              hv_i' (Or.inl rfl) (hno8_i _ hv_i')
            have hi1 : (i_bv + 1).toNat = i_bv.toNat + 1 := by bv_omega
            ml_lets
            refine hJm (s.tmp_len - (i_bv + 1).toNat) (i_bv + 1, ()) m_n (by omega)
              ⟨rfl, by omega, nxt.mrk, nxt.min_clr, nxt.min_clr_len, nxt.min_clr_full,
               hlen_n.mrk_len, hlen_n.min_clr_len_arr, hlen_n.min_clr_len_le,
               by rw [hnxt_eq]; exact hmin_n,
               fun v hv => by rw [hbit8_n v hv]; exact hno8_i v hv, fun j hj => ?_,
               by rw [hnxt_eq]; exact hm_n⟩
            rw [hi1] at hj
            by_cases hje : j = i_bv.toNat
            · subst j
              have hi_len1 : i_bv.toNat < tmp1.length := by rw [ht1_len]; omega
              rw [List.getElem?_eq_getElem hi_len1, Option.getD_some]
              change (nxt.mrk[lit_i.toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8
              dsimp only [nxt, plainMinMarkStepState]
              split
              · rename_i hhas; exact hhas
              · dsimp only [plainMinMarkState]
                rw [List.getElem?_set_self (by rw [hmrkl]; exact hv_i'), Option.getD_some]
                exact bv8_and2_of_or2 _
            · have hjm := hmark_i j (by omega)
              have hjlt : (tmp1[j]?.getD 0#32).toNat / 2 < c.mv := by
                have := (htmp1_vals j (by omega)).2.1; omega
              exact hmono2_n _ hjlt hjm
          · c0_cond hge
            have hie : i_bv.toNat = s.tmp_len := by bv_omega
            have hcore_i : PlainCoreInv c F0 cur :=
              coreInv_with_min hs2_core hmrkl hs2_core.lengths.min_stk_len hmclrl hmcll
            have ho_i : OuterInv c F0 s tmp1 s.tmp_len cur :=
              ⟨hcore_i, hmin_i, hEnt1, hno8_i, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
               fun k hk _ => by
                 have hkv := htmp1_vals k hk
                 exact ⟨hkv.2.1, hkv.2.2.1, hmark_i k (hie ▸ hk)⟩,
               fun k hk1 hk2 _ => by
                 have hlv := htmp1_lvls k hk1 hk2
                 exact ⟨hlv.1, hlv.2, rfl⟩⟩
            have hcon : wp Γ Q X (minShrinkOuterExpr c.hdr (BitVec.ofNat 64 c.mv)
                (BitVec.ofNat 64 s.tmp_len) c.pTmp c.pLevel c.pTrailPos) mi → _ := id
            change wp Γ Q X (minShrinkOuterExpr c.hdr (BitVec.ofNat 64 c.mv)
              (BitVec.ofNat 64 s.tmp_len) c.pTmp c.pLevel c.pTrailPos) mi
            refine min_shrink_outer_wp hMl hSb ho_i htl1 htl_mv ht1_sort
              (fun k hk => (htmp1_vals k hk).1) htmp1_lvls hm_i
              fun tmp' tl' mrk' mstk' mclr' mcl' mcf' heur' m'
                htl_f hml_f hmstk_f hmclr_f hmcl_f hmc_f h1_f htl_le h0_f hok_f hrel_f
                hns_f hent_f hm' => ?_
            have hcore_f : PlainCoreInv c F0 { s with
                tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk', min_clr := mclr',
                min_clr_len := mcl', min_clr_full := mcf', heur := heur' } :=
              { hcore_i with
                lengths := { hcore_i.lengths with
                  tmp_len_arr := htl_f, tmp_len_le := by dsimp only; omega, mrk_len := hml_f,
                  min_stk_len := hmstk_f, min_clr_len_arr := hmclr_f, min_clr_len_le := hmcl_f,
                  heur_ok := hok_f }
                arena := { hcore_i.arena with len_ok := hcore_i.arena.len_ok }
                watches := hcore_i.watches.with_wstk rfl rfl rfl rfl }
            have h0_s : tmp'[0]? = s.tmp[0]? := h0_f.trans (ht1_0 htl1)
            clear hcon
            let sf : PlainState := { s with
              tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk', min_clr := mclr',
              min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
            exact hQ tmp' tl' mrk' mstk' mclr' mcl' mcf' heur' m'
              ⟨hcore_f, hmc_f⟩ h1_f htl_le h0_s hrel_f hns_f hent_f hm'
        · rintro Jm hJm; ml_lets
          have h0v : (0#64 : BitVec 64).toNat = 0 := rfl
          exact hJm (s.tmp_len - 0) (0#64, ()) m3
            ⟨by rw [h0v], by rw [h0v]; exact Nat.zero_le _, s2.mrk, s2.min_clr, s2.min_clr_len,
             s2.min_clr_full, hs2_core.lengths.mrk_len, hs2_core.lengths.min_clr_len_arr,
             hs2_core.lengths.min_clr_len_le, hmin2_init, fun v hv => by
               dsimp only [s2, s1, s0]; rw [hs2_mc v hv]; decide,
             fun _ h => by rw [h0v] at h; omega, hm3⟩

end LeanQbe.T.Examples.Kissat.Plain

