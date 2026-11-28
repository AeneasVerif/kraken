/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpOtfsLarge0
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpCommon
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import Kraken.Mem
import Kraken.Separation

/-!
# Large OTFS Loops 1, MaxLvl, Loop 2 & Flags (`Proof.Deduce.WpOtfsLarge1`)

Sub-expression definitions and weakest-precondition proofs for active-literal counting,
max-level blocking literal search, in-place compaction, and irredundant flag marking
in `full_otfs_large_body`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics DeduceTactics

/-! ## 1. BitVec & Cut-Invariant Bridges -/

theorem otfs_bv32_lshr1_zext_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 (x >>> 1#32)).toNat = x.toNat / 2 := by
  rw [zext_toNat _ (by decide)]
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem otfs_lvl_lshr_eq (lvl : List (BitVec 32)) (x : BitVec 32)
    (hb1 : (BitVec.setWidth 64 (x >>> 1#32)).toNat < lvl.length)
    (hb2 : x.toNat / 2 < lvl.length) :
    lvl[(BitVec.setWidth 64 (x >>> 1#32)).toNat]'hb1 = lvl[x.toNat / 2]'hb2 :=
  getElem_eq_of_idx (otfs_bv32_lshr1_zext_toNat x)

theorem otfs_lvl_idx_eq {ar lvl : List (BitVec 32)} {i j : Nat}
    (hi : i < ar.length) (hj : j < ar.length)
    (hl1 : (ar[i]'hi).toNat / 2 < lvl.length) (hl2 : (ar[j]'hj).toNat / 2 < lvl.length)
    (heq : i = j) :
    (lvl[(ar[i]'hi).toNat / 2]'hl1).toNat = (lvl[(ar[j]'hj).toNat / 2]'hl2).toNat := by
  subst heq; rfl

theorem s13_otfs_cut_shrink {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut cut' : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    (hle : cut' ≤ cut) : FullWitnessCutInv c F0 F_cur cut' k :=
  ⟨hw.toFullOtfsWitnessInv, Nat.le_trans hle hw.cut_le,
    fun idx hi => hw.reason_inv_cut idx (Nat.lt_of_lt_of_le hi hle),
    fun idx hi => hw.reason_lit_mem_cut idx (Nat.lt_of_lt_of_le hi hle)⟩

theorem s13_otfs_cut_with_watch_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    {wv ws : List (BitVec 32)} {wl : Nat} {wu oom : BitVec 64}
    (hmw : ModeWatchesInv F_cur
      { k with wvec := wv, wstk := ws, wlen := wl, wusable := wu, oom := oom }) :
    FullWitnessCutInv c F0 F_cur cut
      { k with wvec := wv, wstk := ws, wlen := wl, wusable := wu, oom := oom } :=
  ⟨{ hw.toFullOtfsWitnessInv with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hmw },
    hw.cut_le, hw.reason_inv_cut, hw.reason_lit_mem_cut⟩

theorem s13_otfs_cut_swap1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hnd : FullArenaVarsNodup s)
    {cref : BitVec 32} {bp : Nat} (hcref : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false)
    (hbp_gt : 1 < bp) (hbp_lt : bp < fullArenaClauseSize s cref.toNat) :
    let l1 := s.core.arena[cref.toNat + 4]?.getD 0#32
    let lbp := s.core.arena[cref.toNat + 3 + bp]?.getD 0#32
    let ar' := (s.core.arena.set (cref.toNat + 4) lbp).set (cref.toNat + 3 + bp) l1
    let s' : FullState := { s with core := { s.core with arena := ar' } }
    FullWitnessCutInv c F0 F_cur cut s'.core ∧ FullArenaVarsNodup s' ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    fullArenaClauseSize s' cref.toNat = fullArenaClauseSize s cref.toNat ∧
    fullArenaClauseGarb s' cref.toNat = false ∧
    (fullArenaClauseLits s' cref.toNat).Perm (fullArenaClauseLits s cref.toNat) ∧
    ar'[cref.toNat + 4]? = some lbp := by
  intro l1 lbp ar' s'
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have hal := hlen.core_ok.arena_len_le
  have har_len := hlen.core_ok.arena_len_arr
  have h4 : cref.toNat + 4 < s.core.arena.length := by
    have := hwf.1; have := hwf.2.1; have := hwf.2.2.1; omega
  have har'_eq : ((s.core.arena.set (cref.toNat + 3 + 1)
      (s.core.arena[cref.toNat + 3 + bp]?.getD 0#32)).set (cref.toNat + 3 + bp)
      (s.core.arena[cref.toNat + 3 + 1]?.getD 0#32)) = ar' := by
    dsimp only [ar', l1, lbp]
  obtain ⟨hw', hrefs', hsz', hng', hperm', hother'⟩ :=
    fa_swapCl_preserves_fullWitnessCut hlen.core_ok hw hcref (i := 1) (j := bp)
      (by omega) hbp_lt
  rw [har'_eq] at hw' hrefs' hsz' hng' hperm' hother'
  have hnd' : FullArenaVarsNodup s' := fun r hr hngr => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs'] at hr
    by_cases hrc : r = cref.toNat
    · subst r; exact (hperm'.map (· / 2)).nodup_iff.mpr (hnd _ hr hng)
    · have ho := hother' r hr hrc
      change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [ho.2.2]
      exact hnd r hr (by
        change fullArenaClauseGarbCore s.core r = false; rw [← ho.2.1]; exact hngr)
  refine ⟨hw', hnd', hrefs', hsz', hng'.trans hng, hperm', ?_⟩
  dsimp only [ar']
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_self h4]

/-! ## 2. Loop 1 (`full_otfs_large` active literal count check) -/

@[expose] def otfs_loop1_expr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (pArena pLevel cr3 : V i64) (old_sz : V i32)
    (cont : Tup V [i32, i32] → Expr V L rs) : Expr V L rs :=
  Expr.group (sig := [[i32, i32]]) (fun Js =>
    Blocks.cons (fun p_15 => cont p_15) Blocks.nil)
  fun Js =>
    Expr.group (sig := [[i32, i32]]) (fun Js_1 =>
      Blocks.cons (fun p =>
        Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var p.snd.fst, Arg.var old_sz, ()))
          fun p_15 =>
        Expr.jnz (Arg.var p_15.fst)
          (Expr.group (sig := [[i32]]) (fun Js_2 =>
            Blocks.cons (fun p_16 =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.snd.fst, Arg.imm 1, ()))
                fun p_n =>
              Expr.jump Js_1.fst (Arg.var p_16.fst, Arg.var p_n.fst, ())) Blocks.nil)
          fun Js_2 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.snd.fst, ())) fun p_16 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var cr3, Arg.var p_16.fst, ())) fun p_17 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_17.fst, Arg.imm 4, ())) fun p_18 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var p_18.fst, ())) fun p_19 =>
            Expr.load i32 (Arg.var p_19.fst) fun ld_lit =>
            Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld_lit, Arg.imm 1, ())) fun p_20 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_20.fst, ())) fun p_21 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_21.fst, Arg.imm 4, ())) fun p_22 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pLevel, Arg.var p_22.fst, ())) fun p_23 =>
            Expr.load i32 (Arg.var p_23.fst) fun ld_lv =>
            Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i32) (Arg.var ld_lv, Arg.imm 0, ()))
              fun p_24 =>
            Expr.jnz (Arg.var p_24.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p_25 =>
               Expr.let_ (Op.mk (OpCode.cmp CmpOp.uge i32) (Arg.var p_25.fst, Arg.imm 3, ()))
                 fun p_26 =>
               Expr.jnz (Arg.var p_26.fst)
                 (Expr.jump Js.fst (Arg.var p_25.fst, Arg.var p.snd.fst, ()))
                 (Expr.jump Js_2.fst (Arg.var p_25.fst, ())))
              (Expr.jump Js_2.fst (Arg.var p.fst, ())))
          (Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ()))) Blocks.nil)
    fun Js_1 => Expr.jump Js_1.fst (Arg.imm 1, Arg.imm 2, ())

theorem s13_otfs_loop1_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {cref : BitVec 32} {old_sz : Nat}
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hcap : c.arena_cap < 2 ^ 31 - 1)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (h3_old : 3 ≤ old_sz)
    (hlits : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (cont : Tup Val [i32, i32] → Expr Val Cont [.bool])
    (hcont : ∀ (nsz i_ext : BitVec 32),
      (3 ≤ nsz.toNat → 3 ≤ 1 + otfsActCnt s.core cref.toNat old_sz) →
      wp Γ Q X (cont (nsz, i_ext, ())) m) :
    wp Γ Q X (otfs_loop1_expr c.pArena c.pLevel (cref.setWidth 64 + 3#64)
      (BitVec.ofNat 32 old_sz) cont) m := by
  have har_len := hlen.core_ok.arena_len_arr
  have hlvl_len := hlen.core_ok.lvl_len
  have hcv_le := hlen.core_ok.cur_vars_le
  unfold otfs_loop1_expr
  refine wp_join_group (ts := [i32, i32])
    (fun (nsz_v, i_v, ()) m1 =>
      m1 = m ∧ (3 ≤ nsz_v.toNat → 3 ≤ 1 + otfsActCnt s.core cref.toNat old_sz))
    ?_ ?_
  · rintro J0 ⟨nsz_v, i_v, ⟨⟩⟩ m1 ⟨hm1, h3⟩; subst m1
    c0_hstraight
    exact hcont nsz_v i_v h3
  · intro J0 hJ0
    refine wp_loop_inv (ts := [i32, i32])
      (fun (nsz_v, i_v, ()) m1 =>
        m1 = m ∧ ∃ i_nat : Nat, 2 ≤ i_nat ∧ i_nat ≤ old_sz ∧
          i_v = BitVec.ofNat 32 i_nat ∧
          nsz_v = BitVec.ofNat 32 (1 + otfsActCnt s.core cref.toNat i_nat) ∧
          1 + otfsActCnt s.core cref.toNat i_nat < 3)
      (fun (_, i_v, ()) _ => old_sz - i_v.toNat) ?_ ?_
    · intro J1 hL1
      have hact2 : otfsActCnt s.core cref.toNat 2 = 0 := by
        simp [otfsActCnt, List.drop_eq_nil_of_le (show (List.range 2).length ≤ 2 by simp)]
      c0_hstraight
      exact hL1 (1#32, 2#32, ()) m ⟨rfl, 2, Nat.le_refl _, by omega, rfl,
        by rw [hact2], by rw [hact2]; omega⟩
    · rintro J1 ⟨nsz_v, i_v, ⟨⟩⟩ m1 ⟨hm1, i_nat, hi2, hile, rfl, rfl, hcnt_lt3⟩ hL1
      subst m1
      have hi_32 : (BitVec.ofNat 32 i_nat).toNat = i_nat := bv32_ofNat_toNat (by omega)
      have hold_32 : (BitVec.ofNat 32 old_sz).toNat = old_sz := bv32_ofNat_toNat (by omega)
      c0_hstraight
      c0_hstep_np
      · have hilt : i_nat < old_sz := by
          have hc' : (BitVec.ofNat 32 i_nat).toNat < (BitVec.ofNat 32 old_sz).toNat := by c0_bound
          rwa [hi_32, hold_32] at hc'
        obtain ⟨hz_idx, hidx_bd⟩ := s13_otfs_ar_idx3_lt_len hcap har_len h3o hilt
        have har_bd : cref.toNat + 3 + i_nat < s.core.arena.length := by rw [har_len]; omega
        let idx := (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat
        have hot_eq : s.core.arena[idx]'hidx_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd :=
          getElem_eq_of_idx hz_idx
        have hv_bd : (s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2 <
            s.core.lvl.length := by
          have := hlits i_nat hilt; rw [hlvl_len]; omega
        have hlvl_bd : (BitVec.setWidth 64 ((s.core.arena[idx]'hidx_bd) >>> 1#32)).toNat <
            s.core.lvl.length := by
          rw [otfs_bv32_lshr1_zext_toNat, hot_eq]
          rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd; exact hv_bd
        have hlvl_bd' : (s.core.arena[idx]'hidx_bd).toNat / 2 < s.core.lvl.length := by
          rw [hot_eq]; rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd; exact hv_bd
        have hi1_32 : BitVec.ofNat 32 i_nat + 1 = BitVec.ofNat 32 (i_nat + 1) :=
          otfs_bv32_ofNat_add1 i_nat
        refine wp_join_group (ts := [i32])
          (fun (nsz_next, ()) m2 => m2 = m ∧
            nsz_next = BitVec.ofNat 32 (1 + otfsActCnt s.core cref.toNat (i_nat + 1)) ∧
            1 + otfsActCnt s.core cref.toNat (i_nat + 1) < 3) ?_ ?_
        · rintro J2 ⟨nsz_next, ⟨⟩⟩ m2 ⟨hm2, hns_eq, hns_lt⟩; subst m2
          c0_hstraight
          exact hL1 (_, _, ()) m (by
            dsimp only; rw [hi1_32, bv32_ofNat_toNat (by omega), hi_32]; omega)
            ⟨rfl, i_nat + 1, by omega, by omega, hi1_32, hns_eq, hns_lt⟩
        · intro J2 hJ2
          c0_hstraight
          c0_hstep_np
          · have hhc : (cref.toNat + 3 + i_nat % 2 ^ 32) % 2 ^ 64 = idx := by
              dsimp only [idx]
              rw [hz_idx, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            have hpos0 : (0#32 : BitVec 32).toNat <
                (s.core.lvl[(s.core.arena[idx]'hidx_bd).toNat / 2]'hlvl_bd').toNat := by
              rw [otfs_lvl_idx_eq _ hidx_bd _ hlvl_bd' hhc] at hc; exact hc
            have hlv_pos := s13_otfs_p1_lv_pos har_bd hv_bd hot_eq hpos0
            c0_hstraight
            c0_hstep_np
            · have hz_cnt : (BitVec.ofNat 32 (1 + otfsActCnt s.core cref.toNat i_nat)).toNat =
                  1 + otfsActCnt s.core cref.toNat i_nat := bv32_ofNat_toNat (by omega)
              have hge3 : (3#32 : BitVec 32).toNat ≤
                  (1 + otfsActCnt s.core cref.toNat i_nat + 1) % 2 ^ 32 := by
                have hc' : (3#32 : BitVec 32).toNat ≤ (BitVec.ofNat 32
                    (1 + otfsActCnt s.core cref.toNat i_nat) + 1#32).toNat := by c0_bound
                rw [BitVec.toNat_add, hz_cnt,
                  show (1#32 : BitVec 32).toNat = 1 from rfl] at hc'
                exact hc'
              c0_hstraight
              exact hJ0 (_, _, ()) m
                ⟨rfl, fun _ => s13_otfs_p1_brk hi2 hilt hlv_pos hcnt_lt3 hge3⟩
            · have hz_cnt : (BitVec.ofNat 32 (1 + otfsActCnt s.core cref.toNat i_nat)).toNat =
                  1 + otfsActCnt s.core cref.toNat i_nat := bv32_ofNat_toNat (by omega)
              have hlt3 : ¬ (3#32 : BitVec 32).toNat ≤
                  (1 + otfsActCnt s.core cref.toNat i_nat + 1) % 2 ^ 32 := by
                have hc' : ¬ (3#32 : BitVec 32).toNat ≤ (BitVec.ofNat 32
                    (1 + otfsActCnt s.core cref.toNat i_nat) + 1#32).toNat := by c0_bound
                rw [BitVec.toNat_add, hz_cnt,
                  show (1#32 : BitVec 32).toNat = 1 from rfl] at hc'
                exact hc'
              obtain ⟨hns_eq, hns_lt⟩ := s13_otfs_p1_inc hi2 hlv_pos hcnt_lt3 hlt3
              c0_hstraight
              exact hJ2 (_, ()) m ⟨rfl, hns_eq, hns_lt⟩
          · have hhc : (cref.toNat + 3 + i_nat % 2 ^ 32) % 2 ^ 64 = idx := by
              dsimp only [idx]
              rw [hz_idx, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            have hzero0 : ¬ (0#32 : BitVec 32).toNat <
                (s.core.lvl[(s.core.arena[idx]'hidx_bd).toNat / 2]'hlvl_bd').toNat := by
              rw [otfs_lvl_idx_eq _ hidx_bd _ hlvl_bd' hhc] at hc; exact hc
            have hlv_0 := s13_otfs_p1_lv_zero har_bd hv_bd hot_eq hzero0
            c0_hstraight
            refine hJ2 (_, ()) m ⟨rfl, ?_, ?_⟩
            · rw [otfsActCnt_succ hi2, ite_eq_right hlv_0, Nat.add_zero]
            · rwa [otfsActCnt_succ hi2, ite_eq_right hlv_0, Nat.add_zero]
      · have heq_old : i_nat = old_sz := by
          have hc' : ¬ (BitVec.ofNat 32 i_nat).toNat < (BitVec.ofNat 32 old_sz).toNat := by
            c0_bound
          rw [hi_32, hold_32] at hc'; omega
        subst heq_old
        c0_hstraight
        exact hJ0 (_, _, ()) m ⟨rfl, fun hge3 => by
          have hle_act := otfsActCnt_le s.core cref.toNat i_nat
          have hns_eq : (BitVec.ofNat 32 (1 + otfsActCnt s.core cref.toNat i_nat)).toNat =
              1 + otfsActCnt s.core cref.toNat i_nat := bv32_ofNat_toNat (by omega)
          rw [hns_eq] at hge3; omega⟩

/-! ## 3. Max-Level Blocking Literal Loop -/

@[expose] def otfs_maxlvl_expr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (pArena pLevel cr3 : V i64) (old_sz uip : V i32)
    (cont : V i32 → Expr V L rs) : Expr V L rs :=
  Expr.group (sig := [[i32, i32, i32]]) (fun Js =>
    Blocks.cons (fun p_17 =>
      Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var p_17.fst, Arg.var old_sz, ()))
        fun p_18 =>
      Expr.jnz (Arg.var p_18.fst)
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_17.fst, ())) fun p0 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var cr3, Arg.var p0.fst, ())) fun p1 =>
         Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p1.fst, Arg.imm 4, ())) fun p2 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var p2.fst, ())) fun p3 =>
         Expr.load i32 (Arg.var p3.fst) fun ld_lit =>
         Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld_lit, Arg.imm 1, ())) fun p4 =>
         Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p4.fst, ())) fun p5 =>
         Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p5.fst, Arg.imm 4, ())) fun p6 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pLevel, Arg.var p6.fst, ())) fun p7 =>
         Expr.load i32 (Arg.var p7.fst) fun ld_lv =>
         Expr.group (sig := [[i32, i32]]) (fun Js_1 =>
           Blocks.cons (fun p =>
             Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p_17.fst, Arg.imm 1, ())) fun p_19 =>
             Expr.jump Js.fst
               (Arg.var p_19.fst, Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil)
         fun Js_1 =>
           Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i32) (Arg.var ld_lv, Arg.var p_17.snd.fst, ()))
             fun p_b =>
           Expr.jnz (Arg.var p_b.fst)
             (Expr.jump Js_1.fst (Arg.var ld_lv, Arg.var ld_lit, ()))
             (Expr.jump Js_1.fst (Arg.var p_17.snd.fst, Arg.var p_17.snd.snd.fst, ())))
        (cont p_17.snd.snd.fst)) Blocks.nil)
  fun Js => Expr.jump Js.fst (Arg.imm 2, Arg.imm 0, Arg.var uip, ())

theorem s13_otfs_maxlvl_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {cref uip : BitVec 32} {old_sz : Nat}
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hcap : c.arena_cap < 2 ^ 31 - 1)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (h3_old : 3 ≤ old_sz)
    (hlits : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (cont : Val i32 → Expr Val Cont [.bool])
    (hcont : ∀ (l1 : BitVec 32), wp Γ Q X (cont l1) m) :
    wp Γ Q X (otfs_maxlvl_expr c.pArena c.pLevel (cref.setWidth 64 + 3#64)
      (BitVec.ofNat 32 old_sz) uip cont) m := by
  have har_len := hlen.core_ok.arena_len_arr
  have hlvl_len := hlen.core_ok.lvl_len
  have hcv_le := hlen.core_ok.cur_vars_le
  unfold otfs_maxlvl_expr
  refine wp_loop_inv (ts := [i32, i32, i32])
    (fun (i_v, _, _, ()) m1 =>
      m1 = m ∧ ∃ i_nat : Nat, 2 ≤ i_nat ∧ i_nat ≤ old_sz ∧ i_v = BitVec.ofNat 32 i_nat)
    (fun (i_v, _, _, ()) _ => old_sz - i_v.toNat) ?_ ?_
  · intro J0 hL0
    c0_hstraight
    exact hL0 (2#32, 0#32, uip, ()) m ⟨rfl, 2, Nat.le_refl _, by omega, rfl⟩
  · rintro J0 ⟨i_v, bl_v, l1_v, ⟨⟩⟩ m1 ⟨hm1, i_nat, hi2, hile, rfl⟩ hL0
    subst m1
    have hi_32 : (BitVec.ofNat 32 i_nat).toNat = i_nat := bv32_ofNat_toNat (by omega)
    have hold_32 : (BitVec.ofNat 32 old_sz).toNat = old_sz := bv32_ofNat_toNat (by omega)
    c0_hstraight
    c0_hstep_np
    · have hilt : i_nat < old_sz := by
        have hc' : (BitVec.ofNat 32 i_nat).toNat < (BitVec.ofNat 32 old_sz).toNat := by c0_bound
        rwa [hi_32, hold_32] at hc'
      obtain ⟨hz_idx, hidx_bd⟩ := s13_otfs_ar_idx3_lt_len hcap har_len h3o hilt
      have har_bd : cref.toNat + 3 + i_nat < s.core.arena.length := by rw [har_len]; omega
      let idx := (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat
      have hot_eq : s.core.arena[idx]'hidx_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd :=
        getElem_eq_of_idx hz_idx
      have hv_bd : (s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2 <
          s.core.lvl.length := by
        have := hlits i_nat hilt; rw [hlvl_len]; omega
      have hlvl_bd : (BitVec.setWidth 64 ((s.core.arena[idx]'hidx_bd) >>> 1#32)).toNat <
          s.core.lvl.length := by
        rw [otfs_bv32_lshr1_zext_toNat, hot_eq]
        rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd; exact hv_bd
      have hi1_32 : BitVec.ofNat 32 i_nat + 1 = BitVec.ofNat 32 (i_nat + 1) :=
        otfs_bv32_ofNat_add1 i_nat
      c0_hstraight
      refine wp_join_group (ts := [i32, i32]) (fun _ m2 => m2 = m) ?_ ?_
      · rintro J1 ⟨bl', l1', ⟨⟩⟩ m2 hm2; subst m2
        c0_hstraight
        exact hL0 (_, bl', l1', ()) m (by
          dsimp only; rw [hi1_32, bv32_ofNat_toNat (by omega), hi_32]; omega)
          ⟨rfl, i_nat + 1, by omega, by omega, hi1_32⟩
      · intro J1 hJ1
        c0_hstraight
        c0_hstep_np
        · c0_hstraight; exact hJ1 (_, _, ()) m rfl
        · c0_hstraight; exact hJ1 (_, _, ()) m rfl
    · c0_hstraight; exact hcont l1_v

/-! ## 4. Loop 2 (In-Place Compaction & Best Position) -/

@[expose] def otfs_loop2_expr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (pArena pLevel cr3 : V i64) (old_sz : V i32)
    (cont : V i32 → V i32 → Expr V L rs) : Expr V L rs :=
  Expr.group (sig := [[i32, i32, i32, i32]]) (fun Js =>
    Blocks.cons (fun p_28 =>
      Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var p_28.fst, Arg.var old_sz, ()))
        fun p_29 =>
      Expr.jnz (Arg.var p_29.fst)
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_28.fst, ())) fun p0 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var cr3, Arg.var p0.fst, ())) fun p1 =>
         Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p1.fst, Arg.imm 4, ())) fun p2 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var p2.fst, ())) fun p3 =>
         Expr.load i32 (Arg.var p3.fst) fun ld_5 =>
         Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld_5, Arg.imm 1, ())) fun p4 =>
         Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p4.fst, ())) fun p5 =>
         Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p5.fst, Arg.imm 4, ())) fun p6 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pLevel, Arg.var p6.fst, ())) fun p7 =>
         Expr.load i32 (Arg.var p7.fst) fun ld_6 =>
         Expr.group (sig := [[i32, i32, i32]]) (fun Js_1 =>
           Blocks.cons (fun p =>
             Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p_28.fst, Arg.imm 1, ())) fun p_30 =>
             Expr.jump Js.fst (Arg.var p_30.fst, Arg.var p.fst, Arg.var p.snd.fst,
               Arg.var p.snd.snd.fst, ())) Blocks.nil)
         fun Js_1 =>
           Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i32) (Arg.var ld_6, Arg.imm 0, ())) fun p_b =>
           Expr.jnz (Arg.var p_b.fst)
             (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_28.snd.fst, ())) fun p_q0 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var cr3, Arg.var p_q0.fst, ())) fun p_q1 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_q1.fst, Arg.imm 4, ())) fun p_q2 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var p_q2.fst, ())) fun p_q3 =>
              Expr.store (Arg.var ld_5) (Arg.var p_q3.fst)
                (Expr.group (sig := [[i32, i32]]) (fun Js_2 =>
                   Blocks.cons (fun p =>
                     Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p_28.snd.fst, Arg.imm 1, ()))
                       fun p_30 =>
                     Expr.jump Js_1.fst (Arg.var p_30.fst, Arg.var p.fst, Arg.var p.snd.fst, ()))
                     Blocks.nil)
                 fun Js_2 =>
                   Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i32)
                       (Arg.var ld_6, Arg.var p_28.snd.snd.snd.fst, ())) fun p_b2 =>
                   Expr.jnz (Arg.var p_b2.fst)
                     (Expr.jump Js_2.fst (Arg.var p_28.snd.fst, Arg.var ld_6, ()))
                     (Expr.jump Js_2.fst
                       (Arg.var p_28.snd.snd.fst, Arg.var p_28.snd.snd.snd.fst, ()))))
             (Expr.jump Js_1.fst (Arg.var p_28.snd.fst, Arg.var p_28.snd.snd.fst,
               Arg.var p_28.snd.snd.snd.fst, ())))
        (cont p_28.snd.fst p_28.snd.snd.fst)) Blocks.nil)
  fun Js => Expr.jump Js.fst (Arg.imm 2, Arg.imm 1, Arg.imm 1, Arg.imm 0, ())

theorem s13_otfs_loop2_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {cref l0 uip : BitVec 32} {old_sz : Nat}
    (hlen : s.LengthsOk c) (hlen2 : s2.LengthsOk c)
    (hm : (FullMem c s2 ⋆ R) m)
    (hlvl_eq : s2.core.lvl = s.core.lvl) (_hcv_eq : s2.core.cur_vars = s.core.cur_vars)
    (hcap : c.arena_cap < 2 ^ 31 - 1)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (h4_old : 4 ≤ old_sz)
    (hs01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip))
    (har2_eq : s2.core.arena = (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip)
    (hlits : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (cont : Val i32 → Val i32 → Expr Val Cont [.bool])
    (hcont : ∀ (nsz bp : Nat) (ar_cur : List (BitVec 32)) (origMap : List Nat) (m' : Mem 64),
      S13OtfsShrinkInv c s ((s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip)
        cref l0 uip old_sz 0 old_sz nsz ar_cur origMap →
      nsz < old_sz → (nsz = 1 → bp = 1) → (2 ≤ nsz → 1 ≤ bp ∧ bp < nsz) →
      (FullMem c { s2 with core := { s2.core with arena := ar_cur } } ⋆ R) m' →
      wp Γ Q X (cont (BitVec.ofNat 32 nsz) (BitVec.ofNat 32 bp)) m') :
    wp Γ Q X (otfs_loop2_expr c.pArena c.pLevel (cref.setWidth 64 + 3#64)
      (BitVec.ofNat 32 old_sz) cont) m := by
  have har_len := hlen.core_ok.arena_len_arr
  have hlvl_len := hlen.core_ok.lvl_len
  have har2_len := hlen2.core_ok.arena_len_arr
  have hlvl2_len := hlen2.core_ok.lvl_len
  have hcv_le := hlen.core_ok.cur_vars_le
  let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
  obtain ⟨orig0, hinv0⟩ := s13_otfs_loop2_init har_len h3o h4_old hs01
  unfold otfs_loop2_expr
  refine wp_loop_inv (ts := [i32, i32, i32, i32])
    (fun (i_v, nsz_v, bp_v, bl_v, ()) m1 =>
      ∃ i_nat nsz bp ar_cur origMap,
        i_v = BitVec.ofNat 32 i_nat ∧ nsz_v = BitVec.ofNat 32 nsz ∧
        bp_v = BitVec.ofNat 32 bp ∧
        (nsz = 1 → bp = 1 ∧ bl_v = 0#32) ∧ (2 ≤ nsz → 1 ≤ bp ∧ bp < nsz) ∧
        S13OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - i_nat) i_nat nsz ar_cur origMap ∧
        (FullMem c { s2 with core := { s2.core with arena := ar_cur } } ⋆ R) m1)
    (fun (i_v, _, _, _, ()) _ => old_sz - i_v.toNat) ?_ ?_
  · intro J0 hL0
    c0_hstraight
    have hm0 : (FullMem c { s2 with core := { s2.core with arena := ar1 } } ⋆ R) m := by
      dsimp only [ar1]; rw [← har2_eq]; exact hm
    exact hL0 (2#32, 1#32, 1#32, 0#32, ()) m
      ⟨2, 1, 1, ar1, orig0, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by omega),
        hinv0, hm0⟩
  · rintro J0 ⟨i_v, nsz_v, bp_v, bl_v, ⟨⟩⟩ m1
      ⟨i_nat, nsz, bp, ar_cur, origMap, rfl, rfl, rfl, hbp1, hbp2, hinv, hm1⟩ hL0
    have hinv_cp := hinv
    obtain ⟨har_c, _, hi2, hile, hns1, _, _, _, _, _, _, _, hout⟩ := hinv
    have hnsz_lt_i : nsz < i_nat ∨ (i_nat = 2 ∧ nsz = 1) := by
      have := otfsActCnt_le s.core cref.toNat i_nat; omega
    have hi_32 : (BitVec.ofNat 32 i_nat).toNat = i_nat := bv32_ofNat_toNat (by omega)
    have hns_32 : (BitVec.ofNat 32 nsz).toNat = nsz := bv32_ofNat_toNat (by omega)
    have hold_32 : (BitVec.ofNat 32 old_sz).toNat = old_sz := bv32_ofNat_toNat (by omega)
    have hbp_le : bp ≤ nsz := by
      rcases Nat.eq_or_lt_of_le hns1 with rfl | hgt
      · exact (hbp1 rfl).1 ▸ Nat.le_refl 1
      · exact Nat.le_of_lt (hbp2 hgt).2
    have hbp_ge1 : 1 ≤ bp := by
      rcases Nat.eq_or_lt_of_le hns1 with rfl | hgt
      · exact (hbp1 rfl).1 ▸ Nat.le_refl 1
      · exact (hbp2 hgt).1
    have hbp_32 : (BitVec.ofNat 32 bp).toNat = bp := bv32_ofNat_toNat (by omega)
    c0_hstraight
    c0_hstep_np
    · have hilt : i_nat < old_sz := by
        have hc' : (BitVec.ofNat 32 i_nat).toNat < (BitVec.ofNat 32 old_sz).toNat := by c0_bound
        rwa [hi_32, hold_32] at hc'
      have hnsz_lt_i' : nsz < i_nat := by omega
      obtain ⟨hz_idx, hidx_bd⟩ := s13_otfs_ar_idx3_lt_len hcap har_c h3o hilt
      have har_bd : cref.toNat + 3 + i_nat < s.core.arena.length := by rw [har_len]; omega
      let idx := (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i_nat).setWidth 64).toNat
      have hot_c_eq : ar_cur[idx]'hidx_bd = s.core.arena[cref.toNat + 3 + i_nat]'har_bd := by
        dsimp only [idx]
        rw [← Option.some_inj, ← List.getElem?_eq_getElem har_bd,
          ← List.getElem?_eq_getElem hidx_bd, hz_idx, hout _ (Or.inr (by omega))]
        dsimp only [ar1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      have hv_bd : (s.core.arena[cref.toNat + 3 + i_nat]?.getD 0#32).toNat / 2 <
          s.core.lvl.length := by
        have := hlits i_nat hilt; rw [hlvl_len]; omega
      have hlvl_bd : (BitVec.setWidth 64 ((ar_cur[idx]'hidx_bd) >>> 1#32)).toNat <
          s2.core.lvl.length := by
        rw [otfs_bv32_lshr1_zext_toNat, hot_c_eq, hlvl_eq]
        rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd; exact hv_bd
      have hlvl_bd' : (ar_cur[idx]'hidx_bd).toNat / 2 < s2.core.lvl.length := by
        rw [hot_c_eq, hlvl_eq]
        rw [List.getElem?_eq_getElem har_bd, Option.getD_some] at hv_bd; exact hv_bd
      have hi1_32 : BitVec.ofNat 32 i_nat + 1 = BitVec.ofNat 32 (i_nat + 1) :=
        otfs_bv32_ofNat_add1 i_nat
      c0_hstraight
      refine wp_join_group (ts := [i32, i32, i32])
        (fun (nsz_next, bp_next, bl_next, ()) m2 =>
          ∃ nsz' bp' ar' origMap',
            nsz_next = BitVec.ofNat 32 nsz' ∧ bp_next = BitVec.ofNat 32 bp' ∧
            (nsz' = 1 → bp' = 1 ∧ bl_next = 0#32) ∧ (2 ≤ nsz' → 1 ≤ bp' ∧ bp' < nsz') ∧
            S13OtfsShrinkInv c s ar1 cref l0 uip old_sz (old_sz - (i_nat + 1)) (i_nat + 1) nsz'
              ar' origMap' ∧
            (FullMem c { s2 with core := { s2.core with arena := ar' } } ⋆ R) m2) ?_ ?_
      · rintro J1 ⟨nsz_next, bp_next, bl_next, ⟨⟩⟩ m2
          ⟨nsz', bp', ar', origMap', hns', hbp', h1', h2', hinv', hm2⟩
        c0_hstraight
        exact hL0 (_, _, _, _, ()) m2 (by
          dsimp only; rw [hi1_32, bv32_ofNat_toNat (by omega), hi_32]; omega)
          ⟨i_nat + 1, nsz', bp', ar', origMap', hi1_32, hns', hbp', h1', h2', hinv', hm2⟩
      · intro J1 hJ1
        c0_hstraight
        c0_hstep_np
        · have hhc : (cref.toNat + 3 + i_nat % 2 ^ 32) % 2 ^ 64 = idx := by
            dsimp only [idx]; rw [hz_idx, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have hpos0 : (0#32 : BitVec 32).toNat <
              (s2.core.lvl[(ar_cur[idx]'hidx_bd).toNat / 2]'hlvl_bd').toNat := by
            rw [otfs_lvl_idx_eq _ hidx_bd _ hlvl_bd' hhc] at hc; exact hc
          have hlv_pos := s13_otfs_p2_lv_pos har_bd hv_bd hlvl_eq hot_c_eq hpos0
          obtain ⟨hz_ns, hns_bd⟩ :=
            s13_otfs_ar_idx3_lt_len hcap har_c h3o (j := nsz) (by omega)
          let idx_ns := (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 nsz).setWidth 64).toNat
          have har_set_eq : ar_cur.set idx_ns (ar_cur[idx]'hidx_bd) =
              ar_cur.set (cref.toNat + 3 + nsz)
                (s.core.arena[cref.toNat + 3 + i_nat]'har_bd) := by
            dsimp only [idx_ns]; rw [hz_ns, hot_c_eq]
          have hns1_32 : BitVec.ofNat 32 nsz + 1 = BitVec.ofNat 32 (nsz + 1) :=
            otfs_bv32_ofNat_add1 nsz
          have hstep := s13_otfs_shrink_loop_step har_len hinv_cp hilt h3o hlv_pos
          c0_hstraight
          have hm_step : (FullMem c { s2 with core := { s2.core with
              arena := ar_cur.set (cref.toNat + 3 + nsz)
                (s.core.arena[cref.toNat + 3 + i_nat]'har_bd) } } ⋆ R) m := by
            rw [← har_set_eq]; assumption
          refine wp_join_group (ts := [i32, i32])
            (fun (bp_next, bl_next, ()) m2 =>
              ∃ bp', bp_next = BitVec.ofNat 32 bp' ∧ 1 ≤ bp' ∧ bp' < nsz + 1 ∧
                (FullMem c { s2 with core := { s2.core with
                  arena := ar_cur.set (cref.toNat + 3 + nsz)
                    (s.core.arena[cref.toNat + 3 + i_nat]'har_bd) } } ⋆ R) m2) ?_ ?_
          · rintro J2 ⟨bp_next, bl_next, ⟨⟩⟩ m2 ⟨bp', hbp', hge1', hlt', hm2⟩
            c0_hstraight
            exact hJ1 (_, _, _, ()) m2
              ⟨nsz + 1, bp', _, origMap ++ [i_nat], hns1_32, hbp',
                fun h => absurd h (by omega), fun _ => ⟨hge1', hlt'⟩, hstep, hm2⟩
          · intro J2 hJ2
            c0_hstraight
            c0_hstep_np
            · c0_hstraight
              exact hJ2 (_, _, ()) _ ⟨nsz, rfl, hns1, Nat.lt_succ_self _, hm_step⟩
            · rcases Nat.eq_or_lt_of_le hns1 with rfl | hgt
              · exfalso
                obtain ⟨_, rfl⟩ := hbp1 rfl
                have hno : ¬ (0#32 : BitVec 32).toNat <
                    (s2.core.lvl[(ar_cur[idx]'hidx_bd).toNat / 2]'hlvl_bd').toNat := by
                  rw [otfs_lvl_idx_eq _ hidx_bd _ hlvl_bd' hhc] at hc; exact hc
                exact hno hpos0
              · c0_hstraight
                exact hJ2 (_, _, ()) _
                  ⟨bp, rfl, (hbp2 hgt).1, Nat.lt_succ_of_lt (hbp2 hgt).2, hm_step⟩
        · have hhc : (cref.toNat + 3 + i_nat % 2 ^ 32) % 2 ^ 64 = idx := by
            dsimp only [idx]; rw [hz_idx, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have hzero0 : ¬ (0#32 : BitVec 32).toNat <
              (s2.core.lvl[(ar_cur[idx]'hidx_bd).toNat / 2]'hlvl_bd').toNat := by
            rw [otfs_lvl_idx_eq _ hidx_bd _ hlvl_bd' hhc] at hc; exact hc
          have hinv_skip := s13_otfs_p2_skip_inv hinv_cp hilt har_bd hv_bd hlvl_eq hot_c_eq
            hzero0
          c0_hstraight
          exact hJ1 (_, _, _, ()) m1
            ⟨nsz, bp, ar_cur, origMap, rfl, rfl, hbp1, hbp2, hinv_skip, hm1⟩
    · have heq_old : i_nat = old_sz := by
        have hc' : ¬ (BitVec.ofNat 32 i_nat).toNat < (BitVec.ofNat 32 old_sz).toNat := by c0_bound
        rw [hi_32, hold_32] at hc'; omega
      subst heq_old
      c0_hstraight
      dsimp only [ar1] at hinv_cp
      rw [show i_nat - i_nat = 0 from Nat.sub_self i_nat] at hinv_cp
      exact hcont nsz bp ar_cur origMap m1 hinv_cp (by omega)
        (fun h => (hbp1 h).1) hbp2 hm1

/-! ## 5. Irredundant Flags Marking (`full_otfs_large`) -/

@[expose] def otfs_flags_expr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hdr pArena cr3 : V i64) (uip nsz hdr0 : V i32)
    (J_out : L [i32]) : Expr V L rs :=
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var hdr, Arg.imm 800, ())) fun p_43 =>
  Expr.load i64 (Arg.var p_43.fst) fun ld_6 =>
  Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var uip, Arg.imm 1, ())) fun p_44 =>
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_44.fst, ())) fun p_45 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_45.fst, Arg.imm 4, ())) fun p_46 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld_6, Arg.var p_46.fst, ())) fun p_47 =>
  Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var uip, Arg.imm 1, ())) fun p0 =>
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p0.fst, ())) fun p1 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p1.fst, Arg.imm 4, ())) fun p2 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld_6, Arg.var p2.fst, ())) fun p3 =>
  Expr.load i32 (Arg.var p3.fst) fun ld_7 =>
  Expr.let_ (Op.mk (OpCode.or i32) (Arg.var ld_7, Arg.imm 24, ())) fun p_or =>
  Expr.store (Arg.var p_or.fst) (Arg.var p_47.fst)
    (Expr.group (sig := [[i32]]) (fun Js_1 =>
      Blocks.cons (fun p =>
        Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var p.fst, Arg.var nsz, ())) fun p_48 =>
        Expr.jnz (Arg.var p_48.fst)
          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ())) fun p_49 =>
           Expr.let_ (Op.mk (OpCode.add i64) (Arg.var cr3, Arg.var p_49.fst, ())) fun p_50 =>
           Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_50.fst, Arg.imm 4, ())) fun p_51 =>
           Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var p_51.fst, ())) fun p_52 =>
           Expr.load i32 (Arg.var p_52.fst) fun ld_a =>
           Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld_a, Arg.imm 1, ())) fun p_53 =>
           Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_53.fst, ())) fun p_54 =>
           Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_54.fst, Arg.imm 4, ())) fun p_55 =>
           Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld_6, Arg.var p_55.fst, ())) fun p_56 =>
           Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld_a, Arg.imm 1, ())) fun p_57 =>
           Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_57.fst, ())) fun p_58 =>
           Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_58.fst, Arg.imm 4, ())) fun p_59 =>
           Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld_6, Arg.var p_59.fst, ())) fun p_60 =>
           Expr.load i32 (Arg.var p_60.fst) fun ld_f =>
           Expr.let_ (Op.mk (OpCode.or i32) (Arg.var ld_f, Arg.imm 24, ())) fun p_61 =>
           Expr.store (Arg.var p_61.fst) (Arg.var p_56.fst)
             (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p_n =>
              Expr.jump Js_1.fst (Arg.var p_n.fst, ())))
          (Expr.jump J_out (Arg.var hdr0, ()))) Blocks.nil)
    fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, ()))

theorem s13_otfs_flags_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {cref uip hdr0 : BitVec 32} {ar_a : List (BitVec 32)} {old_sz nsz : Nat}
    {J_out : Cont [i32]}
    (hlen2 : s2.LengthsOk c)
    (hm : (FullMem c { s2 with core := { s2.core with arena := ar_a } } ⋆ R) m)
    (har_len : ar_a.length = c.arena_cap)
    (hcap : c.arena_cap < 2 ^ 31 - 1) (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap)
    (hnsz_lt : nsz < old_sz) (huip_bd : uip.toNat < 2 * s2.core.cur_vars)
    (hlits_a : ∀ k < nsz, (ar_a[cref.toNat + 3 + k]?.getD 0#32).toNat < 2 * s2.core.cur_vars)
    (hJ_out : ∀ (fl3 : List (BitVec 32)) (m' : Mem 64),
      fl3.length = c.max_vars →
      (FullMem c { s2 with core := { s2.core with arena := ar_a, flags := fl3 } } ⋆ R) m' →
      J_out (hdr0, ()) m') :
    wp Γ Q X (otfs_flags_expr c.hdr c.pArena (cref.setWidth 64 + 3#64) uip
      (BitVec.ofNat 32 nsz) hdr0 J_out) m := by
  have hfl_len := hlen2.core_ok.flags_len
  have hcv_le := hlen2.core_ok.cur_vars_le
  have huip_idx : (BitVec.setWidth 64 (uip >>> 1#32)).toNat < s2.core.flags.length := by
    rw [otfs_bv32_lshr1_zext_toNat, hfl_len]; omega
  unfold otfs_flags_expr
  c0_hstraight
  refine wp_loop_inv (ts := [i32])
    (fun (k_v, ()) ml => ∃ (k_nat : Nat) (fl : List (BitVec 32)),
      k_nat ≤ nsz ∧ k_v = BitVec.ofNat 32 k_nat ∧ fl.length = c.max_vars ∧
      (FullMem c { s2 with core := { s2.core with arena := ar_a, flags := fl } } ⋆ R) ml)
    (fun (k_v, ()) _ => nsz - k_v.toNat) ?_ ?_
  · intro J1 hL1
    c0_hstraight
    refine hL1 (0#32, ()) _ ⟨0, _, Nat.zero_le _, rfl, ?_, by assumption⟩
    rw [List.length_set, hfl_len]
  · rintro J1 ⟨k_v, ⟨⟩⟩ ml ⟨k_nat, fl, hk_le, rfl, hfl_cur_len, hml⟩ hL1
    have hk_32 : (BitVec.ofNat 32 k_nat).toNat = k_nat := bv32_ofNat_toNat (by omega)
    have hns_32 : (BitVec.ofNat 32 nsz).toNat = nsz := bv32_ofNat_toNat (by omega)
    c0_hstraight
    c0_hstep_np
    · have hk_lt : k_nat < nsz := by
        have hc' : (BitVec.ofNat 32 k_nat).toNat < (BitVec.ofNat 32 nsz).toNat := by c0_bound
        rwa [hk_32, hns_32] at hc'
      obtain ⟨hz_idx, hidx_bd⟩ := s13_otfs_ar_idx3_lt_len hcap har_len h3o (j := k_nat) (by omega)
      have hfl_k : (BitVec.setWidth 64
          ((ar_a[(cref.setWidth 64 + 3#64 +
            (BitVec.ofNat 32 k_nat).setWidth 64).toNat]'hidx_bd) >>> 1#32)).toNat <
          fl.length := by
        have har_k : cref.toNat + 3 + k_nat < ar_a.length := by rw [← hz_idx]; exact hidx_bd
        rw [otfs_bv32_lshr1_zext_toNat, getElem_eq_of_idx hz_idx (hj := har_k), hfl_cur_len]
        have := hlits_a k_nat hk_lt
        rw [List.getElem?_eq_getElem har_k, Option.getD_some] at this
        omega
      have hk1_32 : BitVec.ofNat 32 k_nat + 1 = BitVec.ofNat 32 (k_nat + 1) :=
        otfs_bv32_ofNat_add1 k_nat
      c0_hstraight
      refine hL1 _ _ (by dsimp only; rw [hk1_32, bv32_ofNat_toNat (by omega), hk_32]; omega) ?_
      refine ⟨k_nat + 1, _, by omega, hk1_32, ?_, by assumption⟩
      rw [List.length_set, hfl_cur_len]
    · c0_hstraight
      exact hJ_out fl ml hfl_cur_len hml

end LeanQbe.T.Examples.Kissat.Proof.Deduce
