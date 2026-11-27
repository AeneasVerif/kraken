/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Src.Minimize
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpMinDfsHelpers
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# `full_min_lit_dfs_m8` WP Proof for `Kissat.Src.Minimize`

Proves `Func.wp Γ full_min_lit_dfs_m8_body ...` against canonical `Spec.fullMinLitDfsSpec`,
consuming callee contract `Γ.Has "full_min_mark" Spec.fullMinMarkSpec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Src.Minimize
open FullMinTactics
open scoped FullArenaTactics FullMinTactics
open Kraken.Bedrock2.Test

private theorem m8MinLit_maxSteps_toNat {c : FullCfg} {s : FullState}
    (hle : s.core.arena_len ≤ c.arena_cap) (hcv : s.core.cur_vars ≤ c.max_vars) :
    ((BitVec.ofNat 64 s.core.arena_len + BitVec.ofNat 64 s.core.cur_vars) * 4 + 64).toNat =
      (s.core.arena_len + s.core.cur_vars) * 4 + 64 := by
  have har := c.harena; have hmx := c.hmaxv; unfold Ref.dimacsBound at har hmx
  have ha : (BitVec.ofNat 64 s.core.arena_len).toNat = s.core.arena_len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hc : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : (BitVec.ofNat 64 s.core.arena_len + BitVec.ofNat 64 s.core.cur_vars).toNat =
      s.core.arena_len + s.core.cur_vars := by
    rw [BitVec.toNat_add, ha, hc, Nat.mod_eq_of_lt (by omega)]
  have h2 :
      ((BitVec.ofNat 64 s.core.arena_len + BitVec.ofNat 64 s.core.cur_vars) * 4).toNat =
        (s.core.arena_len + s.core.cur_vars) * 4 := by
    rw [BitVec.toNat_mul, h1, show (4 : BitVec 64).toNat = 4 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, h2, show (64 : BitVec 64).toNat = 64 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private noncomputable def m8MinLitMaxSteps (s : FullState) : Nat :=
  (s.core.arena_len + s.core.cur_vars) * 4 + 64

private def M8MinBrkPost (c : FullCfg) (s : FullState) (keepSet : List Nat) (root_lit : BitVec 32)
    (idx0 : Nat) (R : Mem 64 → Prop) : Tup Val [i64, i64, .bool, i64] → Mem 64 → Prop :=
  fun (sp, _cd, ok, _steps, ()) m' =>
    ∃ mrk1 wsort1 mclr1 mcl1 mcf1 ticks1,
      let st1 := Spec.m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1
      M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks1 ∧
      (FullMem c st1 ⋆ R) m' ∧
      (if ok then
        ∃ idxs lim, M8MinStkInv s.core wsort1 mrk1 0 idx0 idxs true ∧
          sp.toNat = 0 ∧ lim = (wsort1[1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat ∧
          (if (s.core.rsns[root_lit.toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
            then 1 else fullArenaClauseSizeCore s.core
              (s.core.rsns[root_lit.toNat / 2]?.getD 0xFFFFFFFF#32).toNat) ≤ lim ∧
          M8FrameCov s.core mrk1 idx0 lim
       else
        sp.toNat < c.max_vars ∧ ∃ idxs, M8MinStkInv s.core wsort1 mrk1 sp.toNat idx0 idxs false)

private def M8MinLpInv (c : FullCfg) (s : FullState) (keepSet : List Nat) (idx0 : Nat)
    (R : Mem 64 → Prop) : Nat → Tup Val [i64, i64, i64] → Mem 64 → Prop :=
  fun n (sp, cd, steps, ()) m' =>
    sp.toNat < c.max_vars ∧ cd.toNat < c.minDepth ∧
    steps.toNat ≤ m8MinLitMaxSteps s ∧ n = m8MinLitMaxSteps s - steps.toNat ∧
    ∃ mrk1 wsort1 mclr1 mcl1 mcf1 ticks1 idxs,
      M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks1 ∧
      (FullMem c (Spec.m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) ⋆ R) m' ∧
      M8MinStkInv s.core wsort1 mrk1 sp.toNat idx0 idxs true

private def m8MinLitDfsBrkExpr {V : Ty → Type} {C : List Ty → Type}
    (h pWsort sp : V i64) (ok : V .bool) : Expr V C [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .jnz (.var ok) (.ret (.imm true, ()))
    (.group (sig := [[i64]]) (fun Js => .cons (fun j =>
      .let_ (Op.mk (.cmp .ule i64 .bool rfl) (.var j.fst, .var sp, ())) fun p_33 =>
      .jnz (.var p_33.fst)
        (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun p_34 =>
         .let_ (op64 (.shl i64) (.var j.fst) (.var p_34.fst)) fun p_35 =>
         .let_ (op64 (.mul i64) (.var p_35.fst) (.imm 4)) fun p_36 =>
         .let_ (op64 (.add i64) (.var pWsort) (.var p_36.fst)) fun p_37 =>
         .load i32 (.var p_37.fst) fun ld =>
         .let_ (Op.mk (.trunc 32 8) (.imm 4, ())) fun p_38 =>
         .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
           (.var h, .var ld, .var p_38.fst, ()) fun _ =>
         .let_ (op64 (.add i64) (.var j.fst) (.imm 1)) fun j1 =>
         .jump Js.fst (.var j1.fst, ()))
        (.ret (.imm false, ()))) .nil)
      fun Js => .jump Js.fst (.imm 1, ()))

private theorem m8MinLitDfs_brk_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur0 : List (List Nat)} {s : FullState} {keepSet : List Nat}
    {root_lit : BitVec 32} {idx0 : Nat} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    {sp_b cd_b steps_b : Val i64} {ok_b : Val .bool} {m_b : Mem 64}
    (hMm : Γ.Has "full_min_mark" Spec.fullMinMarkSpec)
    (hcore : FullOtfsCoreInv c F0 s) (hw0 : FullOtfsWitnessInv c F0 F_cur0 s.core)
    (hi0 : idx0 < s.core.trail_end)
    (hi0_eq : (s.core.trl[idx0]?.getD 0#32).toNat = root_lit.toNat ^^^ 1)
    (hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2)
    (hrl_lvl : (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (hno8 : ∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hQ : ∀ ok mrk' wsort' mclr' mcl' mcf' ticks' m',
      let s' := Spec.m8MinLitDfsState s mrk' wsort' mclr' mcl' mcf' ticks'
      FullState.LengthsOk c s' →
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 →
        (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      FullMinMarkInv s'.core keepSet →
      (ok = true →
        (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
          FullMinMarkInv s'.core keep') ∧
        FullMinMarkInv (fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m')
    (hm_post_false : ∀ (st_f : FullState) m_f,
      M8MinStInv c s keepSet st_f.core.mrk st_f.scratch.wsort st_f.core.min_clr
        st_f.core.min_clr_len st_f.core.min_clr_full st_f.scratch.search_ticks →
      st_f = Spec.m8MinLitDfsState s st_f.core.mrk st_f.scratch.wsort st_f.core.min_clr
        st_f.core.min_clr_len st_f.core.min_clr_full st_f.scratch.search_ticks →
      (FullMem c st_f ⋆ R) m_f → Q (false, ()) m_f)
    (hB : M8MinBrkPost c s keepSet root_lit idx0 R (sp_b, cd_b, ok_b, steps_b, ()) m_b) :
    wp Γ Q X (m8MinLitDfsBrkExpr c.hdr c.pWsort sp_b ok_b) m_b := by
  have hlen0 := hcore.1.core_ok
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hcv := hlen0.cur_vars_le
  dsimp only [m8MinLitDfsBrkExpr]
  rcases hB with ⟨mrk_b, wsort_b, mclr_b, mcl_b, mcf_b, ticks_b, hsi_b, hm_b, hok_b⟩
  ml_lets; ml_jnz; refine ⟨fun hyes => ?_, fun hno => ?_⟩
  · have hok_t : ok_b = true := by
      cases ok_b with | false => simp at hyes | true => rfl
    simp only [hok_t, ↓reduceIte] at hok_b
    rcases hok_b with ⟨idxs_b, lim_b, hstk_b, hsp0, hlim_eq, hlim_le, hcov_b⟩
    have hlen1 : idxs_b.length = 1 := by rw [hstk_b.len]
    have hid0 : idxs_b = [idx0] := by
      rcases idxs_b with _ | ⟨x0, xs⟩ <;> simp at hlen1
      subst hlen1
      have hx := hstk_b.idx0_eq; simp at hx; subst hx; rfl
    subst hid0
    obtain ⟨hdrop, hmk⟩ := m8MinLitDfs_ok_final hcore hsi_b hi0 hi0_eq hrl_lvl hno8
      hlim_le hcov_b
    ml_lets; rw [wp]
    exact hQ true mrk_b wsort_b mclr_b mcl_b mcf_b ticks_b m_b
      (hsi_b.core hcore).1 hsi_b.mrk_above hsi_b.mono2 hsi_b.bit8
      hsi_b.min_inv (fun _ => ⟨hdrop, hmk⟩) hm_b
  · have hok_f : ok_b = false := by
      cases ok_b with | false => rfl | true => cases hno
    simp only [hok_f] at hok_b
    rcases hok_b with ⟨hsp_b_lt, idxs_b, hstk_b⟩
    have hcv_b := hlen0.cur_vars_le
    refine wp_loop_group (ts := [i64]) (fun n (j_bv, ()) m_j =>
        n = sp_b.toNat + 1 - j_bv.toNat ∧ 1 ≤ j_bv.toNat ∧ j_bv.toNat ≤ sp_b.toNat + 1 ∧
        ∃ mrk_j mclr_j mcl_j mcf_j,
          M8MinStInv c s keepSet mrk_j wsort_b mclr_j mcl_j mcf_j ticks_b ∧
          (∀ k, j_bv.toNat ≤ k → ∀ hk : k < idxs_b.length,
            mrk_j[(s.core.trl[idxs_b[k]'hk]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) ∧
          (FullMem c (Spec.m8MinLitDfsState s mrk_j wsort_b mclr_j mcl_j mcf_j ticks_b) ⋆ R) m_j)
      ?_
      (fun Jp hJp => by
        ml_lets; exact hJp sp_b.toNat (1#64, ()) m_b
          ⟨by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega, by decide,
            by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega,
            mrk_b, mclr_b, mcl_b, mcf_b, hsi_b,
            fun k hk1 hk2 => (hstk_b.slot k hk2).2 hk1, hm_b⟩)
    rintro Jp n_j ⟨j_bv, ⟨⟩⟩ m_j hJp
      ⟨rfl, hj1, hj_le, mrk_j, mclr_j, mcl_j, mcf_j, hsi_j, hclr_j, hm_j⟩
    rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hj_s => ?_, fun hj_done => ?_⟩
    · have hj_le_sp : j_bv.toNat ≤ sp_b.toNat := by c0_cond hj_s; exact hj_s
      have hj_idxs : j_bv.toNat < idxs_b.length := by rw [hstk_b.len]; omega
      have hj2_len : (j_bv <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
          wsort_b.length := by rw [m8_bv64_shl1_toNat (by omega), hsi_j.wsort_len]; omega
      ml_ld c0_load_full_wsort
        (s := Spec.m8MinLitDfsState s mrk_j wsort_b mclr_j mcl_j mcf_j ticks_b)
        (i := j_bv <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) hj2_len hm_j
      let sv := wsort_b[(j_bv <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat]'
        hj2_len
      have hsv_nat : sv.toNat =
          (s.core.trl[idxs_b[j_bv.toNat]'hj_idxs]?.getD 0#32).toNat / 2 := by
        have hslot := (hstk_b.slot j_bv.toNat hj_idxs).1
        rw [List.getElem?_eq_getElem (by rw [hsi_j.wsort_len]; omega), Option.getD_some] at hslot
        dsimp only [sv]; simp only [m8_bv64_shl1_toNat (x := j_bv) (by omega)]; exact hslot
      have hsv_lt : sv.toNat < s.core.cur_vars := by
        rw [hsv_nat]; have := hw0.trail_lits_lt _ (hstk_b.bd j_bv.toNat hj_idxs); omega
      have hsv_lvl_root : (s.core.lvl[sv.toNat]?.getD 0#32).toNat ≤
          (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat := by
        rw [hsv_nat, ← hrv_root]; exact hstk_b.lvl_le_root j_bv.toNat hj_idxs
      have hno8_sv : (mrk_j[sv.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
        rw [hsi_j.bit8 sv.toNat hsv_lt]; exact hno8 sv.toNat hsv_lt hsv_lvl_root
      have hz_sv : mrk_j[sv.toNat]?.getD 0#8 = 0#8 := by
        rw [hsv_nat]; exact hclr_j j_bv.toNat (Nat.le_refl _) hj_idxs
      ml_lets; apply wp_call_of_spec; apply hMm
      refine m8_fullMinMarkSpec_zero_inv hcore hsi_j.mrk_len hsi_j.wsort_len hsi_j.mclr_len
        hsi_j.mcl_le hm_j hsv_lt hz_sv ((4 : BitVec 32).setWidth 8) fun m_j1 hm_j1 => ?_
      have h4 : (4 : BitVec 32).setWidth 8 = 4#8 := rfl
      rw [h4] at hm_j1
      have hj1_nat : (j_bv + 1#64).toNat = j_bv.toNat + 1 := min_bv64_add1 (by omega)
      obtain ⟨hsi_j1, hclr_j1⟩ := m8MinLit_unwind_post hcore hw0 hsi_j hstk_b hj_idxs
        hsv_nat hsv_lt hno8_sv hz_sv hj1_nat hclr_j
      ml_lets
      exact hJp (sp_b.toNat + 1 - (j_bv + 1#64).toNat) (j_bv + 1#64, ()) m_j1
        (by rw [hj1_nat]; omega)
        ⟨by rw [hj1_nat], by omega, by rw [hj1_nat]; omega, _, _, _, _, hsi_j1, hclr_j1, hm_j1⟩
    · ml_lets; rw [wp]; exact hm_post_false _ m_j hsi_j rfl hm_j

private def m8MinLitDfsCuExpr {V : Ty → Type} {C : List Ty → Type}
    (clvl cur_vars pShrinkStk sp cd steps : V i64) (ul : V i32) (check_used : V .bool)
    (Js : C [i64, i64, .bool, i64]) (Jcu : C []) : Expr V C [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .jnz (.var check_used)
    (.let_ (Op.mk (.zext 32 64) (.var ul, ())) fun p_88 =>
     .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_88.fst, .var cur_vars, ())) fun p_89 =>
     .jnz (.var p_89.fst)
       (.let_ (Op.mk (.zext 32 64) (.var ul, ())) fun p_90 =>
        .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_90.fst, .var clvl, ())) fun p2 =>
        .jnz (.var p2.fst)
          (.let_ (Op.mk (.zext 32 64) (.var ul, ())) fun p3 =>
           .let_ (op64 (.mul i64) (.var p3.fst) (.imm 4)) fun p4 =>
           .let_ (op64 (.add i64) (.var pShrinkStk) (.var p4.fst)) fun p5 =>
           .load i32 (.var p5.fst) fun ld =>
           .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var ld, .imm 0, ())) fun p6 =>
           .jnz (.var p6.fst)
             (.jump Js (.var sp, .var cd, .imm false, .var steps, ()))
             (.jump Jcu ()))
          (.jump Jcu ()))
       (.jump Jcu ()))
    (.jump Jcu ())

private theorem m8MinLitDfs_cu_wp {Γ : Env} {c : FullCfg} {s : FullState}
    {mrk1 : List (BitVec 8)} {wsort2 mclr1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks_x : BitVec 64} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    {sp cd steps : Val i64} {ul : Val i32} {check_used : Val .bool}
    {Js : Cont [i64, i64, .bool, i64]} {Jcu : Cont []} {m_p : Mem 64}
    (hst_ok : s.LengthsOk c) (hcv_bd : s.core.cur_vars < 2 ^ 64)
    (hm_p : (FullMem c (Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1 ticks_x) ⋆ R) m_p)
    (hB : Js (sp, cd, false, steps, ()) m_p)
    (hJcu : Jcu () m_p) :
    wp Γ Q X (m8MinLitDfsCuExpr (BitVec.ofNat 64 s.core.cur_level)
      (BitVec.ofNat 64 s.core.cur_vars) c.pShrinkStk sp cd steps ul check_used Js Jcu) m_p := by
  have hcv := hst_ok.core_ok.cur_vars_le
  dsimp only [m8MinLitDfsCuExpr]
  ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
  · ml_lets; ml_jnz; refine ⟨fun hul_cv => ?_, fun _ => ?_⟩
    · have hul_cv' : ul.toNat < s.core.cur_vars := by
        c0_cond hul_cv; rw [Nat.mod_eq_of_lt hcv_bd] at hul_cv; exact hul_cv
      ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
      · have hul_ss : (ul.setWidth 64).toNat <
            (Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1
              ticks_x).scratch.shrink_stk.length := by
          dsimp only [Spec.m8MinLitDfsState]
          rw [hst_ok.scratch_ok.shrink_stk_len, bv_c0_zext32_64]
          exact Nat.lt_of_lt_of_le hul_cv' hcv
        ml_ld c0_load_full_shrink_stk
          (s := Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1 ticks_x)
          (i := ul.setWidth 64) hul_ss hm_p
        ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
        · ml_lets; exact hB
        · ml_lets; exact hJcu
      · ml_lets; exact hJcu
    · ml_lets; exact hJcu
  · ml_lets; exact hJcu

private def m8MinLitDfsCdExpr {V : Ty → Type} {C : List Ty → Type}
    (cd : V i64) (rsn : V i32) (Jcd : C [i64]) : Expr V C [.bool] :=
  .let_ (Op.mk (.and i32) (.var rsn, .imm 2147483648, ())) fun p1 =>
  .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var p1.fst, .imm 0, ())) fun p2 =>
  .jnz (.var p2.fst)
    (.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var cd, .imm 0, ())) fun p3 =>
     .jnz (.var p3.fst)
       (.let_ (Op.mk (.sub i64) (.var cd, .imm 1, ())) fun p4 =>
        .jump Jcd (.var p4.fst, ()))
       (.jump Jcd (.var cd, ())))
    (.jump Jcd (.var cd, ()))

private theorem m8MinLitDfs_cd_wp {Γ : Env} {c : FullCfg} {Q : Post [.bool]} {X : XPost}
    {cd : Val i64} {rsn : Val i32} {Jcd : Cont [i64]} {m4 : Mem 64}
    (hcd_lt : cd.toNat < c.minDepth)
    (hJcd : ∀ cd', cd'.toNat < c.minDepth → Jcd (cd', ()) m4) :
    wp Γ Q X (m8MinLitDfsCdExpr cd rsn Jcd) m4 := by
  dsimp only [m8MinLitDfsCdExpr]
  ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
  · ml_lets; ml_jnz; refine ⟨fun hcd_nz => ?_, fun _ => ?_⟩
    · c0_cond hcd_nz
      have hcd_pos : 0 < cd.toNat := hcd_nz
      ml_lets; exact hJcd (cd - 1) (by rw [min_bv64_sub1 hcd_pos]; omega)
    · ml_lets; exact hJcd cd hcd_lt
  · ml_lets; exact hJcd cd hcd_lt

private def m8MinLitDfsBinExpr {V : Ty → Type} {C : List Ty → Type}
    (h pRsns pMark pLvl pWsort pShrinkStk sp cd steps cur_vars mv clvl : V i64)
    (v pword pos rsn : V i32) (check_used : V .bool)
    (B : C [i64, i64, .bool, i64]) (L : C [i64, i64, i64]) : Expr V C [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  let op32 (c : OpCode [i32, i32] [i32]) (a b : Arg V i32) := Op.mk c (a, b, ())
  .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var pos, .imm 0, ())) fun p_52 =>
  .jnz (.var p_52.fst)
    (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun p_53 =>
     .let_ (op64 (.shl i64) (.var sp) (.var p_53.fst)) fun p_54 =>
     .let_ (op64 (.add i64) (.var p_54.fst) (.imm 1)) fun p_55 =>
     .let_ (op64 (.mul i64) (.var p_55.fst) (.imm 4)) fun p_56 =>
     .let_ (op64 (.add i64) (.var pWsort) (.var p_56.fst)) fun p_57 =>
     .let_ (op32 (.or i32) (.var pword) (.imm 1)) fun p_58 =>
     .store (.var p_58.fst) (.var p_57.fst)
       (.let_ (op32 (.and i32) (.var rsn) (.imm 2147483647)) fun p_59 =>
        .let_ (Op.mk (.lshr i32) (.var p_59.fst, .imm 1, ())) fun p_60 =>
        .let_ (Op.mk (.zext 32 64) (.var p_60.fst, ())) fun p_61 =>
        .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var p_61.fst, .var cur_vars, ())) fun p_62 =>
        .jnz (.var p_62.fst)
          (.jump B (.var sp, .var cd, .imm false, .var steps, ()))
          (.let_ (Op.mk (.zext 32 64) (.var p_60.fst, ())) fun p_63 =>
           .let_ (op64 (.mul i64) (.var p_63.fst) (.imm 4)) fun p_64 =>
           .let_ (op64 (.add i64) (.var pLvl) (.var p_64.fst)) fun p_65 =>
           .load i32 (.var p_65.fst) fun ld_14 =>
           .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var p_60.fst, .var v, ())) fun p_66 =>
           .jnz (.var p_66.fst)
             (.jump L (.var sp, .var cd, .var steps, ()))
             (.let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var ld_14, .imm 0, ())) fun p_67 =>
              .jnz (.var p_67.fst)
                (.jump L (.var sp, .var cd, .var steps, ()))
                (.let_ (Op.mk (.zext 32 64) (.var p_60.fst, ())) fun p_68 =>
                 .let_ (op64 (.add i64) (.var pMark) (.var p_68.fst)) fun p_69 =>
                 .load i8 (.var p_69.fst) fun ld_15 =>
                 .let_ (Op.mk (.trunc 32 8) (.imm 2, ())) fun p_70 =>
                 .let_ (Op.mk (.zext 8 32) (.var ld_15, ())) fun p_71 =>
                 .let_ (Op.mk (.zext 8 32) (.var p_70.fst, ())) fun p_72 =>
                 .let_ (op32 (.and i32) (.var p_71.fst) (.var p_72.fst)) fun p_73 =>
                 .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p_74 =>
                 .let_ (Op.mk (.zext 8 32) (.var p_74.fst, ())) fun p_75 =>
                 .let_ (Op.mk (.cmp .ne i32 .bool rfl)
                   (.var p_73.fst, .var p_75.fst, ())) fun p_76 =>
                 .jnz (.var p_76.fst)
                   (.jump L (.var sp, .var cd, .var steps, ()))
                   (.let_ (Op.mk (.trunc 32 8) (.imm 4, ())) fun p_77 =>
                    .let_ (Op.mk (.zext 8 32) (.var ld_15, ())) fun p_78 =>
                    .let_ (Op.mk (.zext 8 32) (.var p_77.fst, ())) fun p_79 =>
                    .let_ (op32 (.and i32) (.var p_78.fst) (.var p_79.fst)) fun p_80 =>
                    .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p_81 =>
                    .let_ (Op.mk (.zext 8 32) (.var p_81.fst, ())) fun p_82 =>
                    .let_ (Op.mk (.cmp .ne i32 .bool rfl)
                      (.var p_80.fst, .var p_82.fst, ())) fun p_83 =>
                    .jnz (.var p_83.fst)
                      (.jump B (.var sp, .var cd, .imm false, .var steps, ()))
                      (.let_ (Op.mk (.zext 32 64) (.var p_60.fst, ())) fun p_84 =>
                       .let_ (op64 (.mul i64) (.var p_84.fst) (.imm 4)) fun p_85 =>
                       .let_ (op64 (.add i64) (.var pRsns) (.var p_85.fst)) fun p_86 =>
                       .load i32 (.var p_86.fst) fun ld_16 =>
                       .let_ (Op.mk (.cmp .eq i32 .bool rfl)
                         (.var ld_16, .imm 4294967295, ())) fun p_87 =>
                       .jnz (.var p_87.fst)
                         (.let_ (Op.mk (.trunc 32 8) (.imm 4, ())) fun p_88 =>
                          .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
                            (.var h, .var p_60.fst, .var p_88.fst, ()) fun _ =>
                          .jump B (.var sp, .var cd, .imm false, .var steps, ()))
                         (.group (sig := [[]]) (fun _ => .cons (fun _ =>
                           .let_ (op64 (.add i64) (.var sp) (.imm 1)) fun p_89 =>
                           .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                             (.var p_89.fst, .var mv, ())) fun p =>
                           .jnz (.var p.fst)
                             (.jump B (.var sp, .var cd, .imm false, .var steps, ()))
                             (.let_ (op64 (.add i64) (.var sp) (.imm 1)) fun p =>
                              .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun p_90 =>
                              .let_ (op64 (.shl i64) (.var p.fst) (.var p_90.fst)) fun p_91 =>
                              .let_ (op64 (.mul i64) (.var p_91.fst) (.imm 4)) fun p_92 =>
                              .let_ (op64 (.add i64) (.var pWsort) (.var p_92.fst)) fun p_93 =>
                              .store (.var p_60.fst) (.var p_93.fst)
                                (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun p_94 =>
                                 .let_ (op64 (.shl i64) (.var p.fst) (.var p_94.fst)) fun p_95 =>
                                 .let_ (op64 (.add i64) (.var p_95.fst) (.imm 1)) fun p_96 =>
                                 .let_ (op64 (.mul i64) (.var p_96.fst) (.imm 4)) fun p_97 =>
                                 .let_ (op64 (.add i64) (.var pWsort) (.var p_97.fst)) fun p_98 =>
                                 .store (t := i32) (.imm 0) (.var p_98.fst)
                                   (.jump L (.var p.fst, .var cd, .var steps, ()))))) .nil)
                          fun Js_2 => m8MinLitDfsCuExpr clvl cur_vars pShrinkStk sp cd steps
                            ld_14 check_used B Js_2.fst))))))))
    (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var sp, .imm 0, ())) fun p_53 =>
     .jnz (.var p_53.fst)
       (.jump B (.var sp, .var cd, .imm true, .var steps, ()))
       (.let_ (Op.mk (.trunc 32 8) (.imm 2, ())) fun p_54 =>
        .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
          (.var h, .var v, .var p_54.fst, ()) fun _ =>
        .group (sig := [[i64]]) (fun _Js => .cons (fun cd' =>
          .let_ (op64 (.sub i64) (.var sp) (.imm 1)) fun p_55 =>
          .jump L (.var p_55.fst, .var cd'.fst, .var steps, ())) .nil)
          fun Js => m8MinLitDfsCdExpr cd pword Js.fst))

private theorem m8MinLitDfs_bin_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur0 : List (List Nat)} {s : FullState} {keepSet : List Nat}
    {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)} {mcl1 idx0 : Nat}
    {mcf1 ticks1 : BitVec 64} {root_lit : BitVec 32} {R : Mem 64 → Prop}
    {Q : Post [.bool]} {X : XPost} {B : Cont [i64, i64, .bool, i64]}
    {L : Cont [i64, i64, i64]} {sp cd steps : Val i64} {idxs : List Nat}
    {v pword pos rsn : Val i32} {check_used : Val .bool} {m' : Mem 64}
    (hMm : Γ.Has "full_min_mark" Spec.fullMinMarkSpec)
    (hcore : FullOtfsCoreInv c F0 s) (hw0 : FullOtfsWitnessInv c F0 F_cur0 s.core)
    (hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hno8 : ∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hB : ∀ r m', M8MinBrkPost c s keepSet root_lit idx0 R r m' → B r m')
    (hL : ∀ n' ys m', n' < m8MinLitMaxSteps s - steps.toNat →
      M8MinLpInv c s keepSet idx0 R n' ys m' → L ys m')
    (hsp_lt : sp.toNat < c.max_vars) (hcd_lt : cd.toNat < c.minDepth)
    (hlt_st : steps.toNat < (s.core.arena_len + s.core.cur_vars) * 4 + 64)
    (hsteps1 : (steps + 1).toNat = steps.toNat + 1)
    (hdec_n : m8MinLitMaxSteps s - (steps + 1).toNat < m8MinLitMaxSteps s - steps.toNat)
    (hstk_od : (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat <
      wsort1.length)
    (hsp_idxs : sp.toNat < idxs.length)
    (hsi : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks1)
    (hstk : M8MinStkInv s.core wsort1 mrk1 sp.toNat idx0 idxs true)
    (hv_nat : v.toNat = (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2)
    (hv_lt : v.toNat < s.core.cur_vars)
    (_hpw_eq : pword = wsort1[(sp <<< ((BitVec.signExtend 64
      (1 : BitVec 32)).toNat % 64) + 1).toNat]'hstk_od)
    (hpos_eq : pos = pword &&& 0x7FFFFFFF#32)
    (hpos_nat : pos.toNat = (wsort1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32)
    (hcov_sp : M8FrameCov s.core mrk1 (idxs[sp.toNat]'hsp_idxs) pos.toNat)
    (hbin' : (rsn &&& 0x80000000#32) ≠ 0#32)
    (hm' : (FullMem c (Spec.m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1) ⋆ R) m') :
    wp Γ Q X (m8MinLitDfsBinExpr c.hdr c.pReason c.pMark c.pLevel c.pWsort c.pShrinkStk sp cd
      (steps + 1) (BitVec.ofNat 64 s.core.cur_vars) (BitVec.ofNat 64 c.max_vars)
      (BitVec.ofNat 64 s.core.cur_level) v pword pos rsn check_used B L) m' := by
  have hlen0 := hcore.1.core_ok
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hcv := hlen0.cur_vars_le
  let maxSteps := m8MinLitMaxSteps s
  dsimp only [m8MinLitDfsBinExpr]
  ml_lets; ml_jnz; refine ⟨fun hpos0 => ?_, fun hpos_nz => ?_⟩
  · c0_cond hpos0
    have hpos_0 : pos.toNat = 0 := congrArg BitVec.toNat hpos0
    have hpos_pw0 : (pword &&& 0x7FFFFFFF#32) = 0#32 := hpos_eq ▸ hpos0
    have hsz_lt : pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1 else
        fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
          0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
      simp only [← hrsn_eq, eq_true hbin', ↓reduceIte]; omega
    have hpar_eq : ((pword ||| 1#32) &&& 0x7FFFFFFF#32).toNat =
        (wsort1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1 := by
      rw [← hpos_nat, hpos_0]; exact m8_bv32_mask31_or1_eq hpos_pw0
    ml_st m_p, hm_p' := m8_store_wsort (s := s) (mrk := mrk1) (wsort := wsort1)
      (mclr := mclr1) (mcl := mcl1) (mcf := mcf1) (ticks := ticks1)
      (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1)
      (pword ||| 1#32) hstk_od hm'
    let wsort2 := wsort1.set (2 * sp.toNat + 1) (pword ||| 1#32)
    rw [m8_bv64_shl1_add1_toNat (x := sp) (by omega)] at hm_p'
    have hw2_len : wsort2.length = 2 * c.max_vars := by simp [wsort2, hsi.wsort_len]
    have hsi_p := m8MinStInv_with_wsort hsi hw2_len
    let lit := rsn &&& 0x7FFFFFFF#32
    have hlit_eq : lit.toNat = m8RsnLit s.core rsn pos.toNat := by
      dsimp only [m8RsnLit, lit]; simp only [eq_true hbin', ↓reduceIte]
    have hstk2_drop : M8MinStkInv s.core wsort2 mrk1 sp.toNat idx0 idxs false := by
      refine ⟨hstk.len, hstk.idx0_eq, hstk.bd, hstk.dec, hstk.lvl_le_root,
        fun j hj => ?_, fun hc => by cases hc⟩
      dsimp only [wsort2]; rw [List.getElem?_set_ne (by omega)]; exact hstk.slot j hj
    ml_lets; ml_jnz; refine ⟨fun hu_ge => ?_, fun hu_lt_cv => ?_⟩
    · exfalso
      change (BitVec.ofNat 64 s.core.cur_vars).ule ((lit >>> 1).setWidth 64) = true at hu_ge
      c0_cond hu_ge
      have hu_lt_2v : lit.toNat < 2 * s.core.cur_vars := by
        by_cases heq_var : lit.toNat / 2 =
            (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2
        · have hl1 := hw0.trail_lits_lt _ (hstk.bd sp.toNat hsp_idxs); omega
        · have hfc := m8FrameCov_edge_exists hcore (hstk.bd sp.toNat hsp_idxs)
            (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
            hcov_sp hsz_lt (by rwa [← hrsn_eq, ← hlit_eq])
          rw [← hrsn_eq, ← hlit_eq] at hfc; exact hfc.1
      have := bv_c0_zext32_64 (lit >>> 1); rw [bv32_lshr_1] at *; omega
    · have hu_cv : (lit >>> 1).toNat < s.core.cur_vars := by
        change (BitVec.ofNat 64 s.core.cur_vars).ule ((lit >>> 1).setWidth 64) = false at hu_lt_cv
        c0_cond hu_lt_cv
        have := bv_c0_zext32_64 (lit >>> 1); rw [bv32_lshr_1] at *; omega
      have hu_lvl_len : ((lit >>> 1).setWidth 64).toNat <
          (Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1 ticks1).core.lvl.length := by
        dsimp only [Spec.m8MinLitDfsState]; rw [hlen0.lvl_len, bv_c0_zext32_64]; omega
      ml_ld c0_load_full_lvl
        (s := Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1 ticks1)
        (i := (lit >>> 1).setWidth 64) hu_lvl_len hm_p'
      let ul := s.core.lvl[((lit >>> 1).setWidth 64).toNat]'hu_lvl_len
      ml_lets; ml_jnz; refine ⟨fun heq_uv => ?_, fun hne_uv => ?_⟩
      · change ((lit >>> 1) == v) = true at heq_uv
        c0_cond heq_uv
        have heq_var : lit.toNat / 2 =
            (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
          rw [← hv_nat, ← bv32_lshr_1, heq_uv]
        refine hL (maxSteps - (steps + 1).toNat) (sp, cd, steps + 1, ()) _ hdec_n
          ⟨hsp_lt, hcd_lt, hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl, mrk1, wsort2, mclr1,
            mcl1, mcf1, ticks1, idxs, hsi_p, hm_p',
            m8MinLitDfs_ok_res hcore hstk hi0_lvl hsi.wsort_len hsp_lt hsp_idxs _ hpar_eq
              (hpos_nat ▸ hsz_lt) (u_idx := 0) (by
                rw [← hpos_nat, ← hrsn_eq, ← hlit_eq]; exact Or.inl heq_var)⟩
      · have hu_neq : lit.toNat / 2 ≠
            (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
          change ((lit >>> 1) == v) = false at hne_uv
          c0_cond hne_uv; rw [← hv_nat]; intro heq; apply hne_uv
          apply BitVec.eq_of_toNat_eq; simpa only [bv32_lshr_1] using heq
        have hfc := m8FrameCov_edge_exists hcore (hstk.bd sp.toNat hsp_idxs)
          (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
          hcov_sp hsz_lt (by rwa [← hrsn_eq, ← hlit_eq])
        rw [← hrsn_eq, ← hlit_eq] at hfc
        obtain ⟨hu_lt2, u_idx, hu_idx_lt, hu_idx_eq, hu_lvl_le⟩ := hfc
        have hu_bd_lt : (lit >>> 1).toNat < s.core.cur_vars := by
          rw [bv32_lshr_1]; exact Nat.div_lt_of_lt_mul hu_lt2
        ml_lets; ml_jnz; refine ⟨fun hlvl0 => ?_, fun _ => ?_⟩
        · c0_cond hlvl0
          refine hL (maxSteps - (steps + 1).toNat) (sp, cd, steps + 1, ()) _ hdec_n
            ⟨hsp_lt, hcd_lt, hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl, mrk1, wsort2, mclr1,
              mcl1, mcf1, ticks1, idxs, hsi_p, hm_p', ?_⟩
          refine m8MinStkInv_step_top hstk hsi.wsort_len hsp_lt (pword ||| 1#32) fun _ => ?_
          rw [hpar_eq, ← hpos_nat]
          refine m8FrameCov_step hcore (hstk.bd sp.toNat hsp_idxs)
            (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
            hcov_sp hsz_lt (Or.inr ⟨u_idx, hu_idx_lt, by rwa [← hrsn_eq, ← hlit_eq], Or.inl ?_⟩)
          rw [← hrsn_eq, ← hlit_eq]
          have hvw : ((lit >>> 1).setWidth 64).toNat = lit.toNat / 2 := by
            rw [bv_c0_zext32_64, bv32_lshr_1]
          have hlvl_bd : lit.toNat / 2 < s.core.lvl.length := hvw ▸ hu_lvl_len
          rw [List.getElem?_eq_getElem hlvl_bd, Option.getD_some]
          exact congrArg BitVec.toNat hlvl0
        · have hu_mrk_len : ((lit >>> 1).setWidth 64).toNat <
              (Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1 ticks1).core.mrk.length := by
            dsimp only [Spec.m8MinLitDfsState]; rw [hsi.mrk_len, bv_c0_zext32_64]
            exact Nat.lt_of_lt_of_le hu_bd_lt hcv
          ml_ld c0_load_full_mrk
            (s := Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1 ticks1)
            (i := (lit >>> 1).setWidth 64) hu_mrk_len hm_p'
          let mu := mrk1[((lit >>> 1).setWidth 64).toNat]'hu_mrk_len
          have hmu_eq : mu = mrk1[(lit >>> 1).toNat]?.getD 0#8 := by
            have hvw := bv_c0_zext32_64 (lit >>> 1); dsimp only [mu]
            rw [List.getElem?_eq_getElem (by rw [hsi.mrk_len]; omega), Option.getD_some]; congr 1
          ml_lets; ml_jnz; refine ⟨fun hmu2 => ?_, fun hmu_n2 => ?_⟩
          · have hmu_is2 : (mu &&& 2#8) ≠ 0#8 := bv8_c0_bit_ne0 hmu2
            refine hL (maxSteps - (steps + 1).toNat) (sp, cd, steps + 1, ()) _ hdec_n
              ⟨hsp_lt, hcd_lt, hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl, mrk1, wsort2, mclr1,
                mcl1, mcf1, ticks1, idxs, hsi_p, hm_p', ?_⟩
            refine m8MinStkInv_step_top hstk hsi.wsort_len hsp_lt (pword ||| 1#32) fun _ => ?_
            rw [hpar_eq, ← hpos_nat]
            refine m8FrameCov_step hcore (hstk.bd sp.toNat hsp_idxs)
              (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
              hcov_sp hsz_lt (Or.inr ⟨u_idx, hu_idx_lt,
                by rwa [← hrsn_eq, ← hlit_eq], Or.inr ?_⟩)
            rw [← hrsn_eq, ← hlit_eq, ← bv32_lshr_1, ← hmu_eq]; exact hmu_is2
          · ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hmu_n4 => ?_⟩
            · ml_lets; apply hB
              exact ⟨mrk1, wsort2, mclr1, mcl1, mcf1, ticks1, hsi_p, hm_p',
                ⟨hsp_lt, idxs, hstk2_drop⟩⟩
            · obtain ⟨hu_nat_idx, hu_lvl_root, hno8_u⟩ := m8MinLit_leaf_pre hsi hstk hsp_idxs
                hu_idx_eq hu_lvl_le hu_bd_lt hno8 hrv_root
              have hu_rsns_len : ((lit >>> 1).setWidth 64).toNat <
                  (Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1
                    ticks1).core.rsns.length := by
                dsimp only [Spec.m8MinLitDfsState]
                rw [hlen0.rsns_len, bv_c0_zext32_64, bv32_lshr_1]
                omega
              ml_ld c0_load_full_rsns
                (s := Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1 ticks1)
                (i := (lit >>> 1).setWidth 64) hu_rsns_len hm_p'
              ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hur_some => ?_⟩
              · ml_lets; apply wp_call_of_spec; apply hMm
                refine m8MinLitDfs_poison_leaf hcore hsi_p hstk2_drop
                  hsp_idxs hu_idx_lt hu_nat_idx hu_bd_lt (u_bv := lit >>> 1) hno8_u
                  (by rw [← hmu_eq]; exact bv8_c0_bit_eq0 hmu_n2)
                  (by rw [← hmu_eq]; exact bv8_c0_bit_eq0 hmu_n4) hm_p'
                  fun mrk4 mclr4 mcl4 mcf4 m4 _ _ _ _ hsi4 hm4 hstk4 => by
                    ml_lets; apply hB
                    exact ⟨mrk4, wsort2, mclr4, mcl4, mcf4, ticks1, hsi4, hm4,
                      ⟨hsp_lt, idxs, hstk4⟩⟩
              · refine wp_join_group (ts := []) (fun _ m_cu => m_cu = m_p) ?_ ?_
                · rintro _ ⟨⟩ m_cu rfl; rw [Blocks.get_here]
                  ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hsp_ok => ?_⟩
                  · ml_lets; apply hB
                    exact ⟨mrk1, wsort2, mclr1, mcl1, mcf1, ticks1, hsi_p, hm_p',
                      ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                  · c0_cond hsp_ok
                    have hsp1_nat : (sp + 1).toNat = sp.toNat + 1 := min_bv64_add1 (by omega)
                    have hsp1_lt : sp.toNat + 1 < c.max_vars := by
                      have h1 : (1 : BitVec 64).toNat = 1 := rfl
                      rw [h1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hsp_ok
                      omega
                    have hstk_ev1 : ((sp + 1) <<<
                        ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
                        wsort2.length := by
                      rw [m8_bv64_shl1_toNat (x := sp + 1) (by omega), hw2_len]; omega
                    have hstk_od1 : ((sp + 1) <<<
                        ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat <
                        wsort2.length := by
                      rw [m8_bv64_shl1_add1_toNat (x := sp + 1) (by omega), hw2_len]; omega
                    ml_st m_u, hm_u' := m8_store_wsort (s := s) (mrk := mrk1) (wsort := wsort2)
                      (mclr := mclr1) (mcl := mcl1) (mcf := mcf1) (ticks := ticks1)
                      (i := (sp + 1) <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64))
                      (lit >>> 1) hstk_ev1 hm_p'
                    let wsort_mid := wsort2.set (2 * (sp.toNat + 1)) (lit >>> 1)
                    rw [m8_bv64_shl1_toNat (x := sp + 1) (by omega), hsp1_nat] at hm_u'
                    have hw_mid_len : wsort_mid.length = 2 * c.max_vars := by
                      simp [wsort_mid, hw2_len]
                    ml_st m_z, hm_z' := m8_store_wsort (s := s) (mrk := mrk1)
                      (wsort := wsort_mid) (mclr := mclr1) (mcl := mcl1) (mcf := mcf1)
                      (ticks := ticks1)
                      (i := (sp + 1) <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1)
                      (0#32 : BitVec 32) (by rw [hw_mid_len, ← hw2_len]; exact hstk_od1) hm_u'
                    ml_lets
                    let wsort3 := ((wsort1.set (2 * sp.toNat + 1) (pword ||| 1#32)).set
                      (2 * (sp.toNat + 1)) (lit >>> 1)).set (2 * (sp.toNat + 1) + 1) 0#32
                    rw [m8_bv64_shl1_add1_toNat (x := sp + 1) (by omega), hsp1_nat] at hm_z'
                    have hm_z'' : (FullMem c (Spec.m8MinLitDfsState s mrk1 wsort3 mclr1 mcl1 mcf1
                        ticks1) ⋆ R) m_z := by
                      simpa only [wsort3, wsort_mid, wsort2] using hm_z'
                    have hrsn_u_ne :
                        s.core.rsns[(lit >>> 1).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                      dsimp only [Spec.m8MinLitDfsState] at hur_some hu_rsns_len
                      have hvw := bv_c0_zext32_64 (lit >>> 1)
                      rw [← hvw, List.getElem?_eq_getElem hu_rsns_len, Option.getD_some]
                      intro heq
                      have ht : (s.core.rsns[((lit >>> 1).setWidth 64).toNat] ==
                          (4294967295 : BitVec 32)) = true := beq_iff_eq.mpr heq
                      rw [ht] at hur_some; cases hur_some
                    have h2z : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 2#8) = 0#8 := by
                      rw [← hmu_eq]; exact bv8_c0_bit_eq0 hmu_n2
                    have h4z : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 4#8) = 0#8 := by
                      rw [← hmu_eq]; exact bv8_c0_bit_eq0 hmu_n4
                    obtain ⟨hsi3, hstk3⟩ := m8MinLit_push_stk hcore hsi hstk hi0_lvl hsp_idxs
                      hsp1_lt hpar_eq m8_bv32_mask31_zero_eq0 hpos_nat hsz_lt hu_bd_lt hu_idx_lt
                      hu_idx_eq hu_nat_idx hu_lvl_root hno8_u h2z h4z hrsn_u_ne hrsn_eq hlit_eq
                    exact hL (maxSteps - (steps + 1).toNat) (sp + 1, cd, steps + 1, ()) m_z
                      hdec_n ⟨by rw [hsp1_nat]; exact hsp1_lt, hcd_lt,
                        hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl, mrk1, wsort3, mclr1, mcl1, mcf1,
                        ticks1, idxs ++ [u_idx], hsi3, hm_z'', by rwa [hsp1_nat]⟩
                · rintro Jcu hJcu
                  exact m8MinLitDfs_cu_wp hcore.1 (by omega) hm_p'
                    (hB _ _ ⟨mrk1, wsort2, mclr1, mcl1, mcf1, ticks1, hsi_p, hm_p',
                      ⟨hsp_lt, idxs, hstk2_drop⟩⟩)
                    (hJcu () m_p rfl)
  · have hpos_ge1 : 1 ≤ pos.toNat := by
      c0_cond hpos_nz
      exact Nat.pos_of_ne_zero fun h0 => hpos_nz (BitVec.eq_of_toNat_eq h0)
    ml_lets; ml_jnz; refine ⟨fun hsp0 => ?_, fun hsp_pos => ?_⟩
    · ml_lets; apply hB; c0_cond hsp0
      have hsp0' : sp.toNat = 0 := congrArg BitVec.toNat hsp0
      have hi0_eq_w : idxs[sp.toNat]'hsp_idxs = idx0 := by
        have he := hstk.idx0_eq
        have hz : idxs[sp.toNat]'hsp_idxs = idxs[0]'(by rw [hstk.len]; omega) := by
          simp only [hsp0']
        rw [hz]; rw [List.getElem?_eq_getElem (by rw [hstk.len]; omega)] at he
        exact Option.some.inj he
      simp only [hi0_eq_w] at hcov_sp hrsn_eq
      exact ⟨mrk1, wsort1, mclr1, mcl1, mcf1, ticks1, hsi, hm',
        ⟨idxs, pos.toNat, hsp0' ▸ hstk, hsp0', by rw [hpos_nat, hsp0'],
          by simp only [← hrv_root, ← hrsn_eq, eq_true hbin', ↓reduceIte]; exact hpos_ge1,
          hcov_sp⟩⟩
    · c0_cond hsp_pos
      have hsp_gt0 : 0 < sp.toNat := bv64_pos_of_ne0 hsp_pos
      ml_lets; apply wp_call_of_spec; apply hMm
      refine m8MinLitDfs_pop_state hcore hsi hstk hsp_gt0 hsp_idxs
        hi0_lvl hv_nat hv_lt (lim := pos.toNat)
        (by simp only [← hrsn_eq, eq_true hbin', ↓reduceIte]; omega) hcov_sp hm'
        fun k4 m4 hk4 hsi4 hstk4 hm4 => ?_
      ml_lets
      refine wp_join_group (ts := [i64]) (fun (cd', _) m_cd =>
          cd'.toNat < c.minDepth ∧ m_cd = m4)
        (fun _ ⟨cd', ⟨⟩⟩ m_cd ⟨hcd', rfl⟩ => by
          rw [Blocks.get_here]; ml_lets
          have hsp_m1 : (sp - 1).toNat = sp.toNat - 1 := min_bv64_sub1 (by omega)
          exact hL (maxSteps - (steps + 1).toNat) (sp - 1, cd', steps + 1, ()) m_cd hdec_n
            ⟨by rw [hsp_m1]; omega, hcd', hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl, k4.mrk, wsort1,
              k4.min_clr, k4.min_clr_len, k4.min_clr_full, ticks1, idxs.take sp.toNat, hsi4, hm4,
              by rwa [hsp_m1]⟩)
        ?_
      rintro Jcd hJcd
      exact m8MinLitDfs_cd_wp hcd_lt fun cd' hcd' => by
        ml_lets; exact hJcd (cd', ()) m4 ⟨hcd', rfl⟩

private theorem m8MinLitDfs_false_post {c : FullCfg} {F0 : CNF Nat} {s st_f : FullState}
    {keepSet : List Nat} {root_lit : BitVec 32} {R : Mem 64 → Prop} {Q : Post [.bool]}
    {m_f : Mem 64} (hcore : FullOtfsCoreInv c F0 s)
    (hQ : ∀ ok mrk' wsort' mclr' mcl' mcf' ticks' m',
      let s' := Spec.m8MinLitDfsState s mrk' wsort' mclr' mcl' mcf' ticks'
      FullState.LengthsOk c s' →
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 →
        (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      FullMinMarkInv s'.core keepSet →
      (ok = true →
        (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
          FullMinMarkInv s'.core keep') ∧
        FullMinMarkInv (fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m')
    (hsi_f : M8MinStInv c s keepSet st_f.core.mrk st_f.scratch.wsort st_f.core.min_clr
      st_f.core.min_clr_len st_f.core.min_clr_full st_f.scratch.search_ticks)
    (hst_eq : st_f = Spec.m8MinLitDfsState s st_f.core.mrk st_f.scratch.wsort st_f.core.min_clr
      st_f.core.min_clr_len st_f.core.min_clr_full st_f.scratch.search_ticks)
    (hm_f : (FullMem c st_f ⋆ R) m_f) : Q (false, ()) m_f := by
  have hcore_f := hsi_f.core hcore
  have h := hQ false st_f.core.mrk st_f.scratch.wsort st_f.core.min_clr
    st_f.core.min_clr_len st_f.core.min_clr_full st_f.scratch.search_ticks m_f
    hcore_f.1 hsi_f.mrk_above hsi_f.mono2 hsi_f.bit8 hsi_f.min_inv (fun hc => by cases hc)
  rw [hst_eq] at hm_f; exact h hm_f

private theorem m8MinLitDfs_big_push_lp {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)}
    {mcl1 idx0 u_idx : Nat} {mcf1 ticks2 : BitVec 64} {sp cd steps : BitVec 64}
    {idxs : List Nat} {rsn lit pos newPw : BitVec 32} {R : Mem 64 → Prop} {m_z : Mem 64}
    (hcore : FullOtfsCoreInv c F0 s)
    (hsi2 : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks2)
    (hstk : M8MinStkInv s.core wsort1 mrk1 sp.toNat idx0 idxs true)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hsp_idxs : sp.toNat < idxs.length)
    (hsp1_nat : (sp + 1).toNat = sp.toNat + 1) (hcd1_nat : (cd + 1).toNat = cd.toNat + 1)
    (hsp1_lt : sp.toNat + 1 < c.max_vars) (hcd1_lt : cd.toNat + 1 < c.minDepth)
    (hsteps1 : (steps + 1).toNat = steps.toNat + 1) (hlt_st : steps.toNat < m8MinLitMaxSteps s)
    (hpar_eq : (newPw &&& 0x7FFFFFFF#32).toNat =
      (wsort1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1)
    (hpos_nat : pos.toNat = (wsort1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
    (hsz_lt : pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1 else
        fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
          0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hu_bd_lt : (lit >>> 1).toNat < s.core.cur_vars)
    (hu_idx_lt : u_idx < idxs[sp.toNat]'hsp_idxs)
    (hu_idx_eq : (s.core.trl[u_idx]?.getD 0#32).toNat = lit.toNat ^^^ 1)
    (hu_nat_idx : (lit >>> 1).toNat = (s.core.trl[u_idx]?.getD 0#32).toNat / 2)
    (hu_lvl_root : (s.core.lvl[(s.core.trl[u_idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hno8_u : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8)
    (h2z : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 2#8) = 0#8)
    (h4z : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 4#8) = 0#8)
    (hrsn_u_ne : s.core.rsns[(lit >>> 1).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32)
    (hlit_eq : lit.toNat = m8RsnLit s.core rsn pos.toNat)
    (hm_z : (FullMem c (Spec.m8MinLitDfsState s mrk1
      (((wsort1.set (2 * sp.toNat + 1) newPw).set (2 * (sp.toNat + 1)) (lit >>> 1)).set
        (2 * (sp.toNat + 1) + 1) 0x80000000#32)
      mclr1 mcl1 mcf1 ticks2) ⋆ R) m_z) :
    M8MinLpInv c s keepSet idx0 R (m8MinLitMaxSteps s - (steps + 1).toNat)
      (sp + 1, cd + 1, steps + 1, ()) m_z := by
  obtain ⟨hsi3, hstk3⟩ := m8MinLit_push_stk hcore hsi2 hstk hi0_lvl hsp_idxs hsp1_lt hpar_eq
    m8_bv32_mask31_hi_eq0 hpos_nat hsz_lt hu_bd_lt hu_idx_lt hu_idx_eq hu_nat_idx hu_lvl_root
    hno8_u h2z h4z hrsn_u_ne hrsn_eq hlit_eq
  exact ⟨by rwa [hsp1_nat], by rwa [hcd1_nat], by omega, rfl, mrk1, _, mclr1, mcl1, mcf1, ticks2,
    idxs ++ [u_idx], hsi3, hm_z, by rwa [hsp1_nat]⟩

private theorem m8MinLitDfs_init_entry {c : FullCfg} {F0 : CNF Nat} {F_cur0 : List (List Nat)}
    {s : FullState} {root_lit : BitVec 32}
    (hcore : FullOtfsCoreInv c F0 s) (hw0 : FullOtfsWitnessInv c F0 F_cur0 s.core)
    (hrl : root_lit.toNat < 2 * s.core.cur_vars)
    (hval : s.core.vals[root_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hrl_lvl : (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (hrl_rsns : ((root_lit >>> 1).setWidth 64).toNat < s.core.rsns.length)
    (hrsn_some : (s.core.rsns[((root_lit >>> 1).setWidth 64).toNat]'hrl_rsns == 0xFFFFFFFF#32) =
      false) :
    ∃ idx0, idx0 < s.core.trail_end ∧ (s.core.trl[idx0]?.getD 0#32).toNat = root_lit.toNat ^^^ 1 ∧
      (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2 ∧
      (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
        s.core.cur_level ∧
      s.core.rsns[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
  have hlen0 := hcore.1.core_ok; have hcv := hlen0.cur_vars_le
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  obtain ⟨idx0, hi0, hi0_eq⟩ := (hw0.vals_false_iff root_lit.toNat hrl).mp hval
  have hrv : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2 := by
    have hl := litVar_litNeg root_lit.toNat; unfold litVar litNeg at hl; rw [hi0_eq, hl]
  refine ⟨idx0, hi0, hi0_eq, hrv, by rw [hrv]; exact hrl_lvl, ?_⟩
  have hrl_lt : (root_lit >>> 1).toNat < s.core.rsns.length := by
    rw [hlen0.rsns_len, bv32_lshr_1]; omega
  have _ := hrl_lt
  rw [hrv, ← bv32_lshr_1, ← bv_c0_zext32_64 (root_lit >>> 1),
    List.getElem?_eq_getElem hrl_rsns, Option.getD_some]
  intro heq; c0_cond hrsn_some; exact hrsn_some heq

private theorem m8MinLitDfs_big_pre_facts {c : FullCfg} {s : FullState}
    {wsort1 : List (BitVec 32)} {sp : BitVec 64} {idxs : List Nat}
    {rsn pword pos sz : BitVec 32} (hlen0 : FullCoreState.LengthsOk c s.core)
    (hsp_idxs : sp.toNat < idxs.length)
    (hwf : rsn.toNat + 3 ≤ s.core.arena_len ∧ 3 ≤ fullArenaClauseSizeCore s.core rsn.toNat ∧
      rsn.toNat + 3 + fullArenaClauseSizeCore s.core rsn.toNat ≤
        fullArenaNextOff s.core.arena s.core.arena_len rsn.toNat ∧
      fullArenaNextOff s.core.arena s.core.arena_len rsn.toNat ≤ s.core.arena_len ∧
      (fullArenaNextOff s.core.arena s.core.arena_len rsn.toNat = s.core.arena_len ∨
        fullArenaNextOff s.core.arena s.core.arena_len rsn.toNat + 3 ≤ s.core.arena_len))
    (hsz_e : sz.toNat = fullArenaClauseSizeCore s.core rsn.toNat)
    (hpos_nat : pos.toNat = (wsort1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32)
    (hbin_f : ¬ (rsn &&& 0x80000000#32) ≠ 0#32) (hpos_lt : pos.ult sz = true) :
    pos.toNat < sz.toNat ∧
    (pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1 else
      fullArenaClauseSizeCore s.core
        (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32).toNat) ∧
    (((pword &&& 0x80000000#32) ||| (pos + 1#32)) &&& 0x7FFFFFFF#32).toNat =
      (wsort1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1 := by
  have har := c.harena; unfold Ref.dimacsBound at har
  have hpos_lt' : pos.toNat < sz.toNat := by
    rw [BitVec.ult, decide_eq_true_eq] at hpos_lt; exact hpos_lt
  have hsz_lt : pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
      0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1 else
      fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
    simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte, ← hsz_e]; exact hpos_lt'
  have hpos_add1 : (pos + 1#32).toNat = pos.toNat + 1 := by
    have := hwf.2.2.1; have := hlen0.arena_len_le; rw [hsz_e] at hpos_lt'
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pos.toNat + 1 < 2 ^ 32)]
  have hpos_add1_lt : (pos + 1#32).toNat < 2 ^ 31 := by
    have := hwf.2.2.1; have := hlen0.arena_len_le; rw [hsz_e] at hpos_lt'; omega
  exact ⟨hpos_lt', hsz_lt, by
    rw [m8_bv32_mask31_hi_or_add1 _ _ hpos_add1_lt, hpos_add1, hpos_nat]⟩

private theorem m8MinLitDfs_big_push_pre {c : FullCfg} {wsort2 : List (BitVec 32)}
    {sp cd : BitVec 64} (hsp_lt : sp.toNat < c.max_vars) (hcd_lt : cd.toNat < c.minDepth)
    (hw2_len : wsort2.length = 2 * c.max_vars)
    (hcd_lt' : ((BitVec.ofNat 64 c.minDepth).ule (cd + 1)) = false)
    (hsp_ok : ((BitVec.ofNat 64 c.max_vars).ule (sp + 1)) = false) :
    cd.toNat + 1 < c.minDepth ∧ (sp + 1).toNat = sp.toNat + 1 ∧ (cd + 1).toNat = cd.toNat + 1 ∧
    sp.toNat + 1 < c.max_vars ∧
    ((sp + 1) <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat < wsort2.length ∧
    ((sp + 1) <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat <
      wsort2.length := by
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hmd_le : c.minDepth ≤ 1000 := fullMinDepthOf_le c.max_vars
  c0_cond hcd_lt'; c0_cond hsp_ok
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  have hcd1_lt : cd.toNat + 1 < c.minDepth := by
    rw [h1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hcd_lt'
    unfold FullCfg.minDepth at hcd_lt' ⊢; omega
  have hsp1_lt : sp.toNat + 1 < c.max_vars := by
    rw [h1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hsp_ok; omega
  have hsp1_nat : (sp + 1).toNat = sp.toNat + 1 := min_bv64_add1 (by omega)
  have hcd1_nat : (cd + 1).toNat = cd.toNat + 1 := min_bv64_add1 (by omega)
  refine ⟨hcd1_lt, hsp1_nat, hcd1_nat, hsp1_lt, ?_, ?_⟩
  · rw [m8_bv64_shl1_toNat (x := sp + 1) (by omega), hw2_len]; omega
  · rw [m8_bv64_shl1_add1_toNat (x := sp + 1) (by omega), hw2_len]; omega

private theorem m8MinLitDfs_big_pop_brk {c : FullCfg} {s : FullState}
    {keepSet : List Nat} {root_lit rsn sz pos : BitVec 32} {mrk1 : List (BitVec 8)}
    {wsort1 mclr1 : List (BitVec 32)} {mcl1 idx0 : Nat} {mcf1 ticks2 sp cd steps : BitVec 64}
    {idxs : List Nat} {R : Mem 64 → Prop} {m_tk : Mem 64}
    (hsi2 : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks2)
    (hstk : M8MinStkInv s.core wsort1 mrk1 sp.toNat idx0 idxs true)
    (hsp_idxs : sp.toNat < idxs.length)
    (hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2)
    (hpos_nat : pos.toNat = (wsort1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32)
    (hbin_f : ¬ (rsn &&& 0x80000000#32) ≠ 0#32)
    (hsz_e : sz.toNat = fullArenaClauseSizeCore s.core rsn.toNat)
    (hpos_ge : pos.ult sz = false)
    (hcov_sp : M8FrameCov s.core mrk1 (idxs[sp.toNat]'hsp_idxs) pos.toNat)
    (hsp0 : sp = 0) (hm_tk : (FullMem c (Spec.m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1
      ticks2) ⋆ R) m_tk) :
    M8MinBrkPost c s keepSet root_lit idx0 R (sp, cd, true, steps, ()) m_tk := by
  have hpos_ge' : sz.toNat ≤ pos.toNat := by
    rw [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt] at hpos_ge; exact hpos_ge
  have hsp0' : sp.toNat = 0 := congrArg BitVec.toNat hsp0
  have hi0_eq_w : idxs[sp.toNat]'hsp_idxs = idx0 := by
    have he := hstk.idx0_eq
    have hz : idxs[sp.toNat]'hsp_idxs = idxs[0]'(by rw [hstk.len]; omega) := by simp only [hsp0']
    rw [hz]; rw [List.getElem?_eq_getElem (by rw [hstk.len]; omega)] at he
    exact Option.some.inj he
  simp only [hi0_eq_w] at hcov_sp hrsn_eq
  exact ⟨mrk1, wsort1, mclr1, mcl1, mcf1, ticks2, hsi2, hm_tk,
    ⟨idxs, pos.toNat, hsp0' ▸ hstk, hsp0', by rw [hpos_nat, hsp0'],
      by simp only [← hrv_root, ← hrsn_eq, eq_false hbin_f, ↓reduceIte, ← hsz_e]; exact hpos_ge',
      hcov_sp⟩⟩

private theorem m8MinLitDfs_big_wsort2_inv {c : FullCfg} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)}
    {mcl1 idx0 : Nat} {mcf1 ticks2 sp : BitVec 64} {idxs : List Nat} {newPw : BitVec 32}
    (hsi2 : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks2)
    (hstk : M8MinStkInv s.core wsort1 mrk1 sp.toNat idx0 idxs true) :
    let wsort2 := wsort1.set (2 * sp.toNat + 1) newPw
    wsort2.length = 2 * c.max_vars ∧
    M8MinStInv c s keepSet mrk1 wsort2 mclr1 mcl1 mcf1 ticks2 ∧
    M8MinStkInv s.core wsort2 mrk1 sp.toNat idx0 idxs false := by
  intro wsort2
  have hw2_len : wsort2.length = 2 * c.max_vars := by simp [wsort2, hsi2.wsort_len]
  refine ⟨hw2_len, m8MinStInv_with_wsort hsi2 hw2_len,
    ⟨hstk.len, hstk.idx0_eq, hstk.bd, hstk.dec, hstk.lvl_le_root, fun j hj => ?_,
      fun hc => by cases hc⟩⟩
  dsimp only [wsort2]; rw [List.getElem?_set_ne (by omega)]; exact hstk.slot j hj

private theorem m8MinLitDfs_big_push_post {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {wsort1 mclr1 : List (BitVec 32)}
    {mcl1 idx0 u_idx : Nat} {mcf1 ticks2 sp cd steps : BitVec 64} {idxs : List Nat}
    {rsn lit pos newPw : BitVec 32} {R : Mem 64 → Prop} {m_z : Mem 64}
    (hcore : FullOtfsCoreInv c F0 s)
    (hsi2 : M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks2)
    (hstk : M8MinStkInv s.core wsort1 mrk1 sp.toNat idx0 idxs true)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hsp_idxs : sp.toNat < idxs.length)
    (hsp1_nat : (sp + 1).toNat = sp.toNat + 1) (hcd1_nat : (cd + 1).toNat = cd.toNat + 1)
    (hsp1_lt : sp.toNat + 1 < c.max_vars) (hcd1_lt : cd.toNat + 1 < c.minDepth)
    (hsteps1 : (steps + 1).toNat = steps.toNat + 1) (hlt_st : steps.toNat < m8MinLitMaxSteps s)
    (hpar_eq : (newPw &&& 0x7FFFFFFF#32).toNat =
      (wsort1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1)
    (hpos_nat : pos.toNat = (wsort1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
    (hsz_lt : pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1 else
        fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
          0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hu_bd_lt : (lit >>> 1).toNat < s.core.cur_vars)
    (hu_idx_lt : u_idx < idxs[sp.toNat]'hsp_idxs)
    (hu_idx_eq : (s.core.trl[u_idx]?.getD 0#32).toNat = lit.toNat ^^^ 1)
    (hu_nat_idx : (lit >>> 1).toNat = (s.core.trl[u_idx]?.getD 0#32).toNat / 2)
    (hu_lvl_root : (s.core.lvl[(s.core.trl[u_idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hno8_u : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8)
    (h2z : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 2#8) = 0#8)
    (h4z : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 4#8) = 0#8)
    (hu_rsns_len : ((lit >>> 1).setWidth 64).toNat < s.core.rsns.length)
    (hur_some : (s.core.rsns[((lit >>> 1).setWidth 64).toNat]'hu_rsns_len == 0xFFFFFFFF#32) =
      false)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32)
    (hlit_eq : lit.toNat = m8RsnLit s.core rsn pos.toNat)
    (hm_z' : (FullMem c (Spec.m8MinLitDfsState s mrk1 (((wsort1.set (2 * sp.toNat + 1) newPw).set
        (2 * (sp.toNat + 1)) (lit >>> 1)).set (((sp + 1) <<< ((BitVec.signExtend 64
          (1 : BitVec 32)).toNat % 64)) + 1).toNat 0x80000000#32)
        mclr1 mcl1 mcf1 ticks2) ⋆ R) m_z) :
    M8MinLpInv c s keepSet idx0 R (m8MinLitMaxSteps s - (steps + 1).toNat)
      (sp + 1, cd + 1, steps + 1, ()) m_z := by
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  rw [m8_bv64_shl1_add1_toNat (x := sp + 1) (by rw [hsp1_nat]; omega), hsp1_nat] at hm_z'
  have hrsn_u_ne : s.core.rsns[(lit >>> 1).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    rw [← bv_c0_zext32_64 (lit >>> 1), List.getElem?_eq_getElem hu_rsns_len, Option.getD_some]
    intro heq
    have ht : (s.core.rsns[((lit >>> 1).setWidth 64).toNat]'hu_rsns_len == 0xFFFFFFFF#32) =
        true := beq_iff_eq.mpr heq
    rw [ht] at hur_some; cases hur_some
  exact m8MinLitDfs_big_push_lp hcore hsi2 hstk hi0_lvl hsp_idxs hsp1_nat hcd1_nat hsp1_lt hcd1_lt
    hsteps1 hlt_st hpar_eq hpos_nat hsz_lt hu_bd_lt hu_idx_lt hu_idx_eq hu_nat_idx hu_lvl_root
    hno8_u
    h2z h4z hrsn_u_ne hrsn_eq hlit_eq hm_z'

private theorem m8MinLitDfs_init_lp_entry {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} {keepSet : List Nat} {root_lit : BitVec 32} {idx0 : Nat} {R : Mem 64 → Prop}
    {m1 : Mem 64} (hcore : FullOtfsCoreInv c F0 s)
    (hsi_init : M8MinStInv c s keepSet s.core.mrk s.scratch.wsort s.core.min_clr s.core.min_clr_len
      s.core.min_clr_full s.scratch.search_ticks)
    (hmd_pos : 1 ≤ c.minDepth) (hcv_pos : 0 < s.core.cur_vars)
    (hi0 : idx0 < s.core.trail_end)
    (hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hrsn_ne0 : s.core.rsns[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
      0xFFFFFFFF#32)
    (hm1 : (FullMem c (Spec.m8MinLitDfsState s s.core.mrk ((s.scratch.wsort.set
        (BitVec.signExtend 64 (0 : BitVec 32)).toNat (root_lit >>> 1)).set
        (BitVec.signExtend 64 (1 : BitVec 32)).toNat 0#32) s.core.min_clr s.core.min_clr_len
        s.core.min_clr_full s.scratch.search_ticks) ⋆ R) m1) :
    M8MinLpInv c s keepSet idx0 R (m8MinLitMaxSteps s) (0#64, 0#64, 0#64, ()) m1 := by
  have hlen0 := hcore.1.core_ok; have hcv := hlen0.cur_vars_le
  have hwl := hcore.1.scratch_ok.wsort_len
  have hstk0 := m8MinLit_init_stk0 hcore hwl hcv_pos hcv hi0 hrv_root hi0_lvl hrsn_ne0
  have hwl0 : ((s.scratch.wsort.set (BitVec.signExtend 64 (0 : BitVec 32)).toNat
      (root_lit >>> 1)).set (BitVec.signExtend 64 (1 : BitVec 32)).toNat 0#32).length =
      2 * c.max_vars := by simp [hwl]
  have hsi0 := m8MinStInv_with_wsort hsi_init hwl0
  have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
  exact ⟨by rw [h0]; omega, by rw [h0]; exact hmd_pos, by rw [h0]; exact Nat.zero_le _,
    (by rw [h0, Nat.sub_zero]), s.core.mrk, _, s.core.min_clr, s.core.min_clr_len,
    s.core.min_clr_full, s.scratch.search_ticks, [idx0], hsi0, hm1, hstk0⟩

public section

theorem full_min_lit_dfs_m8_wp (Γ : Env)
    (hMm : Γ.Has "full_min_mark" Spec.fullMinMarkSpec) :
    ∀ args m Q X, Spec.fullMinLitDfsSpec args m Q X →
      Func.wp Γ full_min_lit_dfs_m8_body args m Q X := by
  rintro ⟨h, root_lit, minimizing, check_used, ⟨⟩⟩ m Q X hsp
  obtain ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hrl, hval, hrl_lvl, hno8, hm, hQ⟩ :=
    Spec.fullMinLitDfsSpec_elim hsp
  unfold Func.wp full_min_lit_dfs_m8_body; dsimp only [full_min_lit_dfs_m8_body]
  have hlen0 := hcore.1.core_ok
  have hmx := c.hmaxv; have har := c.harena; unfold Ref.dimacsBound at hmx har
  have hcv := hlen0.cur_vars_le
  have hm_post_false : ∀ (st_f : FullState) m_f, M8MinStInv c s keepSet st_f.core.mrk
      st_f.scratch.wsort st_f.core.min_clr st_f.core.min_clr_len st_f.core.min_clr_full
      st_f.scratch.search_ticks → st_f = Spec.m8MinLitDfsState s st_f.core.mrk st_f.scratch.wsort
      st_f.core.min_clr st_f.core.min_clr_len st_f.core.min_clr_full st_f.scratch.search_ticks →
      (FullMem c st_f ⋆ R) m_f → Q (false, ()) m_f :=
        fun st_f m_f => m8MinLitDfs_false_post hcore hQ
  have hsi_init : M8MinStInv c s keepSet s.core.mrk s.scratch.wsort s.core.min_clr
      s.core.min_clr_len s.core.min_clr_full s.scratch.search_ticks :=
    ⟨hlen0.mrk_len, hcore.1.scratch_ok.wsort_len, hlen0.min_clr_len_arr, hlen0.min_clr_len_le,
      fun _ _ => rfl, hmin, fun _ _ h => h, fun _ _ => rfl⟩
  ml_ld load_full_cur_vars hm; ml_lets; ml_jnz; refine ⟨fun hge => ?_, fun _ => ?_⟩
  · exfalso; c0_cond hge; bv_omega
  · ml_ld load_full_min_depth hm; ml_lets; ml_jnz; refine ⟨fun hz => ?_, fun _ => ?_⟩
    · exfalso; c0_cond hz; have := fullMinDepthOf_pos c.max_vars
      have := fullMinDepthOf_le c.max_vars; unfold FullCfg.minDepth at *; bv_omega
    · ml_ld load_full_reason_ptr hm
      ml_ld c0_load_full_rsns (i := (root_lit >>> 1).setWidth 64)
        (by rw [hlen0.rsns_len, bv_c0_zext32_64, bv32_lshr_1]; omega) hm
      ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hrsn_some => ?_⟩
      · ml_lets; rw [wp]; exact hm_post_false s m hsi_init rfl hm
      · ml_ld load_full_mark_ptr hm; ml_ld load_full_level_ptr hm; ml_ld load_full_arena_ptr hm
        ml_ld load_full_wsort_ptr hm; ml_ld load_full_shrink_stk_ptr hm
        ml_ld c0_load_full_lvl (i := (root_lit >>> 1).setWidth 64)
          (by rw [hlen0.lvl_len, bv_c0_zext32_64, bv32_lshr_1]; omega) hm
        ml_lets
        refine wp_join_group (ts := []) (fun _ m0 => m0 = m) ?_ ?_
        · rintro _ ⟨⟩ m0 rfl; rw [Blocks.get_here]
          have hmd_pos := fullMinDepthOf_pos c.max_vars
          have hcv_pos : 0 < s.core.cur_vars := by omega
          have hwl := hcore.1.scratch_ok.wsort_len
          ml_ld load_full_max_vars hm; ml_ld load_full_arena_len hm
          ml_ld load_full_cur_level hm; ml_ld load_full_min_depth hm
          ml_lets
          ml_st m_w0, hm0 := m8_store_wsort (s := s) (mrk := s.core.mrk)
            (wsort := s.scratch.wsort) (mclr := s.core.min_clr) (mcl := s.core.min_clr_len)
            (mcf := s.core.min_clr_full) (ticks := s.scratch.search_ticks)
            (i := BitVec.signExtend 64 (0 : BitVec 32)) (root_lit >>> 1)
            (by show 0 < s.scratch.wsort.length; omega) hm; ml_lets
          ml_st m1, hm1 := m8_store_wsort (s := s) (mrk := s.core.mrk)
            (wsort := s.scratch.wsort.set (BitVec.signExtend 64 (0 : BitVec 32)).toNat
              (root_lit >>> 1)) (mclr := s.core.min_clr) (mcl := s.core.min_clr_len)
            (mcf := s.core.min_clr_full) (ticks := s.scratch.search_ticks)
            (i := BitVec.signExtend 64 (1 : BitVec 32)) 0#32
            (by show 1 < _; rw [List.length_set]; omega) hm0; clear hm hm0 m_w0; ml_lets
          obtain ⟨F_cur0, hw0⟩ := hcore.2
          obtain ⟨idx0, hi0, hi0_eq, hrv_root, hi0_lvl, hrsn_ne0⟩ := m8MinLitDfs_init_entry
            hcore hw0 hrl hval hrl_lvl _ hrsn_some
          let maxSteps := m8MinLitMaxSteps s
          let BrkPost := M8MinBrkPost c s keepSet root_lit idx0 R
          let LpInv := M8MinLpInv c s keepSet idx0 R
          refine wp_loop_break_group (brkTs := [i64, i64, .bool, i64])
            (lpTs := [i64, i64, i64]) BrkPost LpInv ?_ ?_ ?_
          · rintro B ⟨sp_b, cd_b, ok_b, steps_b, ⟨⟩⟩ m_b hB; rw [Blocks.get_here]
            exact m8MinLitDfs_brk_wp hMm hcore hw0 hi0 hi0_eq hrv_root hrl_lvl hno8 hQ
              hm_post_false hB
          · rintro B L n ⟨sp, cd, steps, ⟨⟩⟩ m' hB hL ⟨hsp_lt, hcd_lt, hsteps_le, rfl, mrk1,
                wsort1, mclr1, mcl1, mcf1, ticks1, idxs, hsi, hm', hstk⟩
            clear hm1 m1
            rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt_st => ?_, fun _ => ?_⟩
            · have hms_eq := m8MinLit_maxSteps_toNat hlen0.arena_len_le hcv
              rw [BitVec.ult, decide_eq_true_eq, hms_eq] at hlt_st
              have hsteps1 : (steps + 1).toNat = steps.toNat + 1 := min_bv64_add1 (by omega)
              have hdec_n : maxSteps - (steps + 1).toNat < maxSteps - steps.toNat := by
                dsimp only [maxSteps, m8MinLitMaxSteps]; omega
              have hmd_le : c.minDepth ≤ 1000 := fullMinDepthOf_le c.max_vars
              have hstk_ev :
                  (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
                    wsort1.length := by rw [m8_bv64_shl1_toNat (by omega), hsi.wsort_len]; omega
              have hstk_od :
                  (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat <
                    wsort1.length := by
                rw [m8_bv64_shl1_add1_toNat (by omega), hsi.wsort_len]; omega
              have hsp_idxs : sp.toNat < idxs.length := by rw [hstk.len]; omega
              ml_ld c0_load_full_wsort
                (s := Spec.m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1)
                (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) hstk_ev hm'
              ml_ld c0_load_full_wsort
                (s := Spec.m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1)
                (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1) hstk_od hm'
              let v := wsort1[(sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat]'
                hstk_ev
              let pword := wsort1[(sp <<< ((BitVec.signExtend 64
                (1 : BitVec 32)).toNat % 64) + 1).toNat]'hstk_od
              let pos := pword &&& 0x7FFFFFFF#32
              have hv_nat : v.toNat =
                  (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
                have hslot := (hstk.slot sp.toNat hsp_idxs).1
                rw [List.getElem?_eq_getElem (by rw [hsi.wsort_len]; omega), Option.getD_some]
                  at hslot
                dsimp only [v]; simp only [m8_bv64_shl1_toNat (x := sp) (by omega)]; exact hslot
              have hv_lt : v.toNat < s.core.cur_vars := by
                rw [hv_nat]; have := hw0.trail_lits_lt _ (hstk.bd sp.toNat hsp_idxs); omega
              have hpos_nat : pos.toNat =
                  (wsort1[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat := by
                dsimp only [pos, pword]; simp only [m8_bv64_shl1_add1_toNat (x := sp) (by omega)]
                rw [List.getElem?_eq_getElem (by rw [hsi.wsort_len]; omega), Option.getD_some]
              ml_lets; ml_jnz; refine ⟨fun hv_ge => ?_, fun _ => ?_⟩
              · exfalso
                change (BitVec.ofNat 64 s.core.cur_vars).ule (v.setWidth 64) = true at hv_ge
                c0_cond hv_ge; rw [Nat.mod_eq_of_lt (by omega)] at hv_ge; omega
              · have hv_rsns : (v.setWidth 64).toNat < (Spec.m8MinLitDfsState s mrk1 wsort1 mclr1
                    mcl1 mcf1 ticks1).core.rsns.length := by
                  dsimp only [Spec.m8MinLitDfsState]; rw [hlen0.rsns_len, bv_c0_zext32_64]; omega
                ml_ld c0_load_full_rsns (s := Spec.m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1
                  ticks1) (i := v.setWidth 64) hv_rsns hm'
                let rsn := s.core.rsns[(v.setWidth 64).toNat]'hv_rsns
                have hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
                    0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
                  have hvw := bv_c0_zext32_64 v; dsimp only [rsn]; simp only [hvw, ← hv_nat]
                  rw [List.getElem?_eq_getElem (by rw [hlen0.rsns_len]; omega), Option.getD_some]
                have hcov_sp := (hstk.cov rfl sp.toNat hsp_idxs).2
                have hilen := hstk.len
                simp only [show sp.toNat + 1 = idxs.length by omega, ↓reduceIte, ← hpos_nat]
                  at hcov_sp
                ml_lets; ml_jnz; refine ⟨fun hno_rsn => ?_, fun _ => ?_⟩
                · exfalso; dsimp only [M8FrameCov] at hcov_sp
                  c0_cond hno_rsn; exact hcov_sp.1 (hrsn_eq.symm.trans hno_rsn)
                · ml_lets; ml_jnz; refine ⟨fun hbin => ?_, fun hbig => ?_⟩
                  · have hbin' : (rsn &&& 0x80000000#32) ≠ 0#32 := by c0_cond hbin; exact hbin
                    exact m8MinLitDfs_bin_wp hMm hcore hw0 hrv_root hi0_lvl hno8 hB hL hsp_lt
                      hcd_lt hlt_st hsteps1 hdec_n hstk_od hsp_idxs hsi hstk hv_nat hv_lt
                      rfl rfl hpos_nat hrsn_eq hcov_sp hbin' hm'
                  · have hbin_f : ¬ (rsn &&& 0x80000000#32) ≠ 0#32 := by
                      c0_cond hbig; intro hne; exact hne hbig
                    have hcov_big := hcov_sp; dsimp only [M8FrameCov] at hcov_big
                    rcases hcov_big with ⟨_, hif⟩
                    simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte] at hif
                    have hwf := hw0.arena.refs_wf _ hif.1
                    ml_lets; ml_jnz; refine ⟨fun har1 => ?_, fun _ => ?_⟩
                    · exfalso; have hlt1 := bv64_lt_zext32_add3
                        (by have := hlen0.arena_len_le; omega) rsn har1; have := hwf.1; omega
                    · have har2 : (rsn.setWidth 64 + 2).toNat < (Spec.m8MinLitDfsState s mrk1
                          wsort1 mclr1 mcl1 mcf1 ticks1).core.arena.length := by
                        rw [bv64_zext32_add2]; dsimp only [Spec.m8MinLitDfsState]
                        have := hwf.1; have := hlen0.arena_len_le; have := hlen0.arena_len_arr
                        omega
                      ml_ld c0_load_full_arena (s := Spec.m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1
                        mcf1 ticks1) (i := rsn.setWidth 64 + 2) har2 hm'
                      let sz := s.core.arena[(rsn.setWidth 64 + 2).toNat]'har2
                      have hsz_e : sz.toNat = fullArenaClauseSizeCore s.core rsn.toNat := by
                        have hopt : (Spec.m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1
                            ticks1).core.arena[(rsn.setWidth 64 + 2).toNat]? =
                            s.core.arena[rsn.toNat + 2]? := by
                          dsimp only [Spec.m8MinLitDfsState]; rw [bv64_zext32_add2]
                        rw [List.getElem?_eq_getElem har2] at hopt
                        exact congrArg (fun o => (o.getD 0#32).toNat) hopt
                      ml_lets; ml_jnz; refine ⟨fun hsz3 => ?_, fun _ => ?_⟩
                      · exfalso; rw [BitVec.ult, decide_eq_true_eq] at hsz3
                        have h3 : (3 : BitVec 32).toNat = 3 := rfl
                        rw [h3, hsz_e] at hsz3; have := hwf.2.1; omega
                      · ml_lets; ml_jnz; refine ⟨fun har_oob => ?_, fun _ => ?_⟩
                        · exfalso; have hlt2 := bv64_lt_zext32_add3_add
                            (by have := hlen0.arena_len_le; omega) rsn sz har_oob
                          have := hwf.2.2.1; have := hwf.2.2.2.1; rw [hsz_e] at hlt2; omega
                        · refine wp_join_group (ts := []) (fun _ m_tk => ∃ ticks2 : BitVec 64,
                              M8MinStInv c s keepSet mrk1 wsort1 mclr1 mcl1 mcf1 ticks2 ∧
                              (FullMem c (Spec.m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1
                                ticks2) ⋆ R) m_tk)
                            ?_ (fun Jtk hJtk => by
                              ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
                              · ml_ld load_full_search_ticks (s := Spec.m8MinLitDfsState s mrk1
                                  wsort1 mclr1 mcl1 mcf1 ticks1) hm'
                                ml_lets; ml_st m_tk, hm_tk := store_full_search_ticks
                                  (s := Spec.m8MinLitDfsState s mrk1 wsort1 mclr1 mcl1 mcf1 ticks1)
                                  (ticks1 + 1#64) hm'
                                exact hJtk () m_tk ⟨ticks1 + 1#64, m8MinStInv_with_ticks hsi, hm_tk⟩
                              · exact hJtk () m' ⟨ticks1, hsi, hm'⟩)
                          rintro Jtk ⟨⟩ m_tk ⟨ticks2, hsi2, hm_tk⟩; rw [Blocks.get_here]
                          ml_lets; ml_jnz; refine ⟨fun hpos_lt => ?_, fun hpos_ge => ?_⟩
                          · obtain ⟨hpos_lt', hsz_lt, hpar_eq⟩ := m8MinLitDfs_big_pre_facts hlen0
                              hsp_idxs hwf hsz_e hpos_nat hrsn_eq hbin_f hpos_lt
                            let newPw := (pword &&& 0x80000000#32) ||| (pos + 1#32)
                            ml_st m_p, hm_p' := m8_store_wsort (s := s) (mrk := mrk1)
                              (wsort := wsort1) (mclr := mclr1) (mcl := mcl1) (mcf := mcf1)
                              (ticks := ticks2)
                              (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1)
                              newPw hstk_od hm_tk
                            let wsort2 := wsort1.set (2 * sp.toNat + 1) newPw
                            rw [m8_bv64_shl1_add1_toNat (x := sp) (by omega)] at hm_p'
                            obtain ⟨hw2_len, hsi_p, hstk2_drop⟩ :=
                              m8MinLitDfs_big_wsort2_inv hsi2 hstk
                            have har_lit_bd : (rsn.setWidth 64 + 3 + pos.setWidth 64).toNat <
                                (Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1
                                  ticks2).core.arena.length := by
                              dsimp only [Spec.m8MinLitDfsState]
                              rw [bv64_zext32_add3_add, hlen0.arena_len_arr]
                              have := hwf.2.2.1; have := hwf.2.2.2.1; have := hlen0.arena_len_le
                              rw [hsz_e] at hpos_lt'; omega
                            ml_ld c0_load_full_arena (s := Spec.m8MinLitDfsState s mrk1 wsort2 mclr1
                              mcl1 mcf1 ticks2) (i := rsn.setWidth 64 + 3 + pos.setWidth 64)
                              har_lit_bd hm_p'
                            let lit := s.core.arena[(rsn.setWidth 64 + 3 +
                              pos.setWidth 64).toNat]'har_lit_bd
                            have hlit_eq : lit.toNat = m8RsnLit s.core rsn pos.toNat := by
                              dsimp only [m8RsnLit, lit]; simp only [eq_false hbin_f, ↓reduceIte]
                              have ha_opt : (Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1
                                  ticks2).core.arena[(rsn.setWidth 64 + 3 +
                                    pos.setWidth 64).toNat]? = s.core.arena[rsn.toNat + 3 +
                                    pos.toNat]? := by
                                dsimp only [Spec.m8MinLitDfsState]; rw [bv64_zext32_add3_add]
                              rw [List.getElem?_eq_getElem har_lit_bd] at ha_opt
                              exact congrArg (fun o => (o.getD 0#32).toNat) ha_opt
                            ml_lets; ml_jnz; refine ⟨fun hu_ge => ?_, fun hu_lt_cv => ?_⟩
                            · exfalso; change (BitVec.ofNat 64 s.core.cur_vars).ule
                                ((lit >>> 1).setWidth 64) = true at hu_ge
                              c0_cond hu_ge
                              have hlt_2v := hw0.arena.lits_lt _ hif.1 hif.2.1 lit.toNat (by
                                rw [hlit_eq]; dsimp only [m8RsnLit]
                                simp only [eq_false hbin_f, ↓reduceIte]
                                exact m8FrameCov_arena_lits_mem hcore hif.1
                                  (by rw [← hsz_e]; exact hpos_lt'))
                              have := bv_c0_zext32_64 (lit >>> 1); rw [bv32_lshr_1] at *; omega
                            · have hu_cv : (lit >>> 1).toNat < s.core.cur_vars := by
                                change (BitVec.ofNat 64 s.core.cur_vars).ule
                                  ((lit >>> 1).setWidth 64) = false at hu_lt_cv
                                c0_cond hu_lt_cv
                                have := bv_c0_zext32_64 (lit >>> 1); rw [bv32_lshr_1] at *; omega
                              have hu_lvl_len : ((lit >>> 1).setWidth 64).toNat <
                                (Spec.m8MinLitDfsState
                                  s mrk1 wsort2 mclr1 mcl1 mcf1 ticks2).core.lvl.length := by
                                dsimp only [Spec.m8MinLitDfsState]
                                rw [hlen0.lvl_len, bv_c0_zext32_64]; omega
                              ml_ld c0_load_full_lvl (s := Spec.m8MinLitDfsState s mrk1 wsort2 mclr1
                                mcl1 mcf1 ticks2) (i := (lit >>> 1).setWidth 64) hu_lvl_len hm_p'
                              ml_lets; ml_jnz; refine ⟨fun heq_uv => ?_, fun hne_uv => ?_⟩
                              · change ((lit >>> 1) == v) = true at heq_uv; c0_cond heq_uv
                                have heq_var : lit.toNat / 2 =
                                    (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
                                  rw [← hv_nat, ← bv32_lshr_1, heq_uv]
                                exact hL (maxSteps - (steps + 1).toNat) (sp, cd, steps + 1, ()) _
                                  hdec_n ⟨hsp_lt, hcd_lt, hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl,
                                    mrk1, wsort2, mclr1, mcl1, mcf1, ticks2, idxs, hsi_p, hm_p',
                                    m8MinLitDfs_ok_res hcore hstk hi0_lvl hsi.wsort_len hsp_lt
                                      hsp_idxs newPw hpar_eq (hpos_nat ▸ hsz_lt) (u_idx := 0)
                                      (by rw [← hpos_nat, ← hrsn_eq, ← hlit_eq]
                                          exact Or.inl heq_var)⟩
                              · have hu_neq : lit.toNat / 2 ≠ (s.core.trl[idxs[sp.toNat]'
                                    hsp_idxs]?.getD 0#32).toNat / 2 := by
                                  change ((lit >>> 1) == v) = false at hne_uv; c0_cond hne_uv
                                  rw [← hv_nat]; intro heq; apply hne_uv
                                  exact BitVec.eq_of_toNat_eq
                                    (by simpa only [bv32_lshr_1] using heq)
                                have hfc := m8FrameCov_edge_exists hcore (hstk.bd sp.toNat hsp_idxs)
                                  (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
                                  hcov_sp hsz_lt (by rwa [← hrsn_eq, ← hlit_eq])
                                rw [← hrsn_eq, ← hlit_eq] at hfc
                                obtain ⟨hu_lt2, u_idx, hu_idx_lt, hu_idx_eq, hu_lvl_le⟩ := hfc
                                have hu_bd_lt : (lit >>> 1).toNat < s.core.cur_vars := by
                                  rw [bv32_lshr_1]; exact Nat.div_lt_of_lt_mul hu_lt2
                                ml_lets; ml_jnz; refine ⟨fun hlvl0 => ?_, fun _ => ?_⟩
                                · c0_cond hlvl0
                                  refine hL (maxSteps - (steps + 1).toNat) (sp, cd, steps + 1, ()) _
                                    hdec_n ⟨hsp_lt, hcd_lt, hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl,
                                      mrk1, wsort2, mclr1, mcl1, mcf1, ticks2, idxs, hsi_p,
                                        hm_p', ?_⟩
                                  refine m8MinStkInv_step_top hstk hsi.wsort_len hsp_lt newPw
                                    fun _ => ?_
                                  rw [hpar_eq, ← hpos_nat]
                                  refine m8FrameCov_step hcore (hstk.bd sp.toNat hsp_idxs)
                                    (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs)
                                      hi0_lvl)
                                    hcov_sp hsz_lt (Or.inr ⟨u_idx, hu_idx_lt,
                                      by rwa [← hrsn_eq, ← hlit_eq], Or.inl ?_⟩)
                                  rw [← hrsn_eq, ← hlit_eq]
                                  have hvw := bv_c0_zext32_64 (lit >>> 1); rw [bv32_lshr_1] at hvw
                                  rw [List.getElem?_eq_getElem (hvw ▸ hu_lvl_len), Option.getD_some]
                                  exact congrArg BitVec.toNat hlvl0
                                · have hu_mrk_len : ((lit >>> 1).setWidth 64).toNat <
                                      (Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1
                                        ticks2).core.mrk.length := by
                                    dsimp only [Spec.m8MinLitDfsState]
                                    rw [hsi.mrk_len, bv_c0_zext32_64]
                                    exact Nat.lt_of_lt_of_le hu_bd_lt hcv
                                  ml_ld c0_load_full_mrk
                                    (s := Spec.m8MinLitDfsState s mrk1 wsort2 mclr1
                                    mcl1 mcf1 ticks2)
                                      (i := (lit >>> 1).setWidth 64) hu_mrk_len hm_p'
                                  let mu := mrk1[((lit >>> 1).setWidth 64).toNat]'hu_mrk_len
                                  have hmu_eq : mu = mrk1[(lit >>> 1).toNat]?.getD 0#8 := by
                                    have hvw := bv_c0_zext32_64 (lit >>> 1); dsimp only [mu]
                                    rw [List.getElem?_eq_getElem (by rw [hsi.mrk_len]; omega),
                                      Option.getD_some]; congr 1
                                  ml_lets; ml_jnz; refine ⟨fun hmu2 => ?_, fun hmu_n2 => ?_⟩
                                  · have hmu_is2 : (mu &&& 2#8) ≠ 0#8 := bv8_c0_bit_ne0 hmu2
                                    refine hL (maxSteps - (steps + 1).toNat)
                                      (sp, cd, steps + 1, ()) _
                                      hdec_n ⟨hsp_lt, hcd_lt,
                                        hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl,
                                        mrk1, wsort2, mclr1, mcl1, mcf1, ticks2, idxs, hsi_p,
                                          hm_p', ?_⟩
                                    refine m8MinStkInv_step_top hstk hsi.wsort_len hsp_lt newPw
                                      fun _ => ?_
                                    rw [hpar_eq, ← hpos_nat]
                                    refine m8FrameCov_step hcore (hstk.bd sp.toNat hsp_idxs)
                                      (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs)
                                        hi0_lvl)
                                      hcov_sp hsz_lt (Or.inr ⟨u_idx, hu_idx_lt,
                                        by rwa [← hrsn_eq, ← hlit_eq], Or.inr ?_⟩)
                                    rw [← hrsn_eq, ← hlit_eq, ← bv32_lshr_1, ← hmu_eq]
                                    exact hmu_is2
                                  · ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hmu_n4 => ?_⟩
                                    · ml_lets; apply hB; exact ⟨mrk1, wsort2, mclr1, mcl1, mcf1,
                                        ticks2, hsi_p, hm_p', ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                                    · obtain ⟨hu_nat_idx, hu_lvl_root, hno8_u⟩ :=
                                        m8MinLit_leaf_pre hsi hstk hsp_idxs hu_idx_eq hu_lvl_le
                                          hu_bd_lt hno8 hrv_root
                                      have hu_rsns_len : ((lit >>> 1).setWidth 64).toNat <
                                          (Spec.m8MinLitDfsState s mrk1 wsort2 mclr1 mcl1 mcf1
                                            ticks2).core.rsns.length := by
                                        dsimp only [Spec.m8MinLitDfsState]
                                        rw [hlen0.rsns_len, bv_c0_zext32_64, bv32_lshr_1]; omega
                                      ml_ld c0_load_full_rsns (s := Spec.m8MinLitDfsState s mrk1
                                        wsort2 mclr1 mcl1 mcf1 ticks2)
                                          (i := (lit >>> 1).setWidth 64)
                                        hu_rsns_len hm_p'
                                      ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hur_some => ?_⟩
                                      · ml_lets; apply wp_call_of_spec; apply hMm
                                        refine m8MinLitDfs_poison_leaf hcore hsi_p hstk2_drop
                                          hsp_idxs hu_idx_lt hu_nat_idx hu_bd_lt (u_bv := lit >>> 1)
                                          hno8_u (by rw [← hmu_eq]; exact bv8_c0_bit_eq0 hmu_n2)
                                          (by rw [← hmu_eq]; exact bv8_c0_bit_eq0 hmu_n4) hm_p'
                                          fun mrk4 mclr4 mcl4 mcf4 m4 _ _ _ _ hsi4 hm4 hstk4 => by
                                            ml_lets; apply hB; exact ⟨mrk4, wsort2, mclr4, mcl4,
                                              mcf4, ticks2, hsi4, hm4, ⟨hsp_lt, idxs, hstk4⟩⟩
                                      · refine wp_join_group (ts := []) (fun _ m_cu => m_cu = m_p)
                                          ?_ ?_
                                        · rintro _ ⟨⟩ m_cu rfl; rw [Blocks.get_here]
                                          ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hcd_lt' => ?_⟩
                                          · ml_lets; apply hB; exact ⟨mrk1, wsort2, mclr1, mcl1,
                                              mcf1, ticks2,
                                                hsi_p, hm_p', ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                                          · ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hsp_ok => ?_⟩
                                            · ml_lets; apply hB; exact ⟨mrk1, wsort2, mclr1, mcl1,
                                                mcf1, ticks2, hsi_p, hm_p',
                                                ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                                            · obtain ⟨hcd1_lt, hsp1_nat, hcd1_nat, hsp1_lt,
                                              hstk_ev1, hstk_od1⟩ :=
                                                m8MinLitDfs_big_push_pre hsp_lt hcd_lt hw2_len
                                                  hcd_lt' hsp_ok
                                              ml_st m_u, hm_u' := m8_store_wsort (s := s)
                                                (mrk := mrk1) (wsort := wsort2) (mclr := mclr1)
                                                (mcl := mcl1) (mcf := mcf1) (ticks := ticks2)
                                                (i := (sp + 1) <<< ((BitVec.signExtend 64
                                                  (1 : BitVec 32)).toNat % 64))
                                                (lit >>> 1) hstk_ev1 hm_p'
                                              let wsort_mid := wsort2.set (2 * (sp.toNat + 1))
                                                (lit >>> 1)
                                              rw [m8_bv64_shl1_toNat (x := sp + 1) (by omega),
                                                hsp1_nat] at hm_u'
                                              have hw_mid_len :
                                                  wsort_mid.length = 2 * c.max_vars := by
                                                dsimp only [wsort_mid]
                                                rw [List.length_set, hw2_len]
                                              ml_st m_z, hm_z' := m8_store_wsort (s := s)
                                                (mrk := mrk1) (wsort := wsort_mid) (mclr := mclr1)
                                                (mcl := mcl1) (mcf := mcf1) (ticks := ticks2)
                                                (i := (sp + 1) <<< ((BitVec.signExtend 64
                                                  (1 : BitVec 32)).toNat % 64) + 1)
                                                (0x80000000#32 : BitVec 32)
                                                (by rw [hw_mid_len, ← hw2_len]; exact hstk_od1)
                                                hm_u'
                                              ml_lets
                                              exact hL (maxSteps - (steps + 1).toNat)
                                                (sp + 1, cd + 1, steps + 1, ()) m_z hdec_n
                                                (m8MinLitDfs_big_push_post hcore hsi2 hstk hi0_lvl
                                                  hsp_idxs hsp1_nat hcd1_nat hsp1_lt hcd1_lt
                                                  hsteps1 hlt_st hpar_eq hpos_nat hsz_lt hu_bd_lt
                                                  hu_idx_lt hu_idx_eq hu_nat_idx hu_lvl_root hno8_u
                                                  (by rw [← hmu_eq]; exact bv8_c0_bit_eq0 hmu_n2)
                                                  (by rw [← hmu_eq]; exact bv8_c0_bit_eq0 hmu_n4)
                                                  hu_rsns_len hur_some hrsn_eq hlit_eq hm_z')
                                        · rintro Jcu hJcu
                                          exact m8MinLitDfs_cu_wp hcore.1 (by omega) hm_p'
                                            (hB _ _ ⟨mrk1, wsort2, mclr1, mcl1, mcf1, ticks2, hsi_p,
                                              hm_p', ⟨hsp_lt, idxs, hstk2_drop⟩⟩)
                                            (hJcu () m_p rfl)
                          · have hpos_ge' : sz.toNat ≤ pos.toNat := by
                              change pos.ult sz = false at hpos_ge
                              rw [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt] at hpos_ge
                              exact hpos_ge
                            ml_lets; ml_jnz; refine ⟨fun hsp0 => ?_, fun hsp_pos => ?_⟩
                            · ml_lets; apply hB; c0_cond hsp0
                              exact m8MinLitDfs_big_pop_brk hsi2 hstk hsp_idxs hrv_root hpos_nat
                                hrsn_eq hbin_f hsz_e hpos_ge hcov_sp hsp0 hm_tk
                            · c0_cond hsp_pos
                              have hsp_gt0 : 0 < sp.toNat := bv64_pos_of_ne0 hsp_pos
                              ml_lets; apply wp_call_of_spec; apply hMm
                              refine m8MinLitDfs_pop_state hcore hsi2 hstk hsp_gt0 hsp_idxs
                                hi0_lvl hv_nat hv_lt (lim := pos.toNat)
                                (by simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte, ← hsz_e]
                                    exact hpos_ge') hcov_sp hm_tk
                                fun k4 m4 hk4 hsi4 hstk4 hm4 => ?_
                              ml_lets
                              refine wp_join_group (ts := [i64]) (fun (cd', _) m_cd =>
                                  cd'.toNat < c.minDepth ∧ m_cd = m4)
                                (fun _ ⟨cd', ⟨⟩⟩ m_cd ⟨hcd', rfl⟩ => by
                                  rw [Blocks.get_here]; ml_lets
                                  have hsp_m1 := min_bv64_sub1 (x := sp) (by omega)
                                  exact hL (maxSteps - (steps + 1).toNat)
                                    (sp - 1, cd', steps + 1, ()) m_cd hdec_n
                                    ⟨by rw [hsp_m1]; omega, hcd',
                                      hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl, k4.mrk, wsort1,
                                      k4.min_clr, k4.min_clr_len, k4.min_clr_full, ticks2,
                                      idxs.take sp.toNat, hsi4, hm4, by rwa [hsp_m1]⟩) ?_
                              rintro Jcd hJcd; exact m8MinLitDfs_cd_wp hcd_lt fun cd' hcd' => by
                                ml_lets; exact hJcd (cd', ()) m4 ⟨hcd', rfl⟩
            · ml_lets; apply hB; exact ⟨mrk1, wsort1, mclr1, mcl1, mcf1, ticks1, hsi, hm',
                hsp_lt, idxs, ⟨hstk.len, hstk.idx0_eq, hstk.bd, hstk.dec, hstk.lvl_le_root,
                  fun j hj => hstk.slot j hj, fun hc => by cases hc⟩⟩
          · intro B L hB hL; ml_lets; exact hL maxSteps (0#64, 0#64, 0#64, ()) m1
              (m8MinLitDfs_init_lp_entry hcore hsi_init hmd_pos hcv_pos hi0 hrv_root hi0_lvl
                hrsn_ne0 hm1)
        · rintro Jinit hJinit
          ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => by rw [wp]; exact hJinit () m rfl⟩
          ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => by rw [wp]; exact hJinit () m rfl⟩
          ml_lets; ml_jnz; refine ⟨fun hrl_cv => ?_, fun _ => by rw [wp]; exact hJinit () m rfl⟩
          have hrl_lt1 : ((root_lit >>> 1).setWidth 64).toNat < s.core.lvl.length := by
            rw [hlen0.lvl_len, bv_c0_zext32_64, bv32_lshr_1]; omega
          have hrl_lt2 : root_lit.toNat / 2 < s.core.lvl.length := by rw [hlen0.lvl_len]; omega
          have hrl_cv' : (s.core.lvl[root_lit.toNat / 2]'hrl_lt2).toNat < s.core.cur_vars := by
            c0_cond hrl_cv; rwa [Nat.mod_eq_of_lt (by omega)] at hrl_cv
          ml_ld load_full_cur_level hm; ml_lets; ml_jnz
          refine ⟨fun _ => ?_, fun _ => by rw [wp]; exact hJinit () m rfl⟩
          have hrl_ss : ((s.core.lvl[((root_lit >>> 1).setWidth 64).toNat]'hrl_lt1).setWidth
              64).toNat < s.scratch.shrink_stk.length := by
            have h_eq : s.core.lvl[((root_lit >>> 1).setWidth 64).toNat]?.getD 0#32 =
                s.core.lvl[root_lit.toNat / 2]?.getD 0#32 := by rw [bv_c0_zext32_64, bv32_lshr_1]
            rw [List.getElem?_eq_getElem hrl_lt1, List.getElem?_eq_getElem hrl_lt2,
              Option.getD_some, Option.getD_some] at h_eq
            rw [hcore.1.scratch_ok.shrink_stk_len, bv_c0_zext32_64, h_eq]
            exact Nat.lt_of_lt_of_le hrl_cv' hcv
          ml_ld c0_load_full_shrink_stk (i :=
            (s.core.lvl[((root_lit >>> 1).setWidth 64).toNat]'hrl_lt1).setWidth 64) hrl_ss hm
          ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => by rw [wp]; exact hJinit () m rfl⟩
          ml_lets; rw [wp]; exact hm_post_false s m hsi_init rfl hm

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize
