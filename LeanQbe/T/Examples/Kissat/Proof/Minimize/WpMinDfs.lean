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
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0Grind
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# `full_min_lit_dfs_m8` WP Proof for `Kissat.Src.Minimize`

Proves `Func.wp Γ full_min_lit_dfs_m8_body ...` against canonical `Spec.fullMinLitDfsSpec`,
consuming callee contract `Γ.Has "full_min_mark" Spec.minMarkSpec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Grind LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
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
  c0_bound

private noncomputable def m8MinLitMaxSteps (s : FullState) : Nat :=
  (s.core.arena_len + s.core.cur_vars) * 4 + 64

private def M8MinBrkPost (c : FullCfg) (s : FullState) (keepSet : List Nat) (root_lit : BitVec 32)
    (idx0 : Nat) (R : Mem 64 → Prop) : Tup Val [i64, i64, .bool, i64] → Mem 64 → Prop :=
  fun (sp, _cd, ok, _steps, ()) m' =>
    ∃ d : M8DfsScratch,
      d.Inv c s keepSet ∧ (FullMem c (d.st s) ⋆ R) m' ∧
      (if ok then
        ∃ idxs lim, M8MinStkInv s.core d.wsort d.mrk 0 idx0 idxs true ∧
          sp.toNat = 0 ∧ lim = (d.wsort[1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat ∧
          (if (s.core.rsns[root_lit.toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
            then 1 else fullArenaClauseSizeCore s.core
              (s.core.rsns[root_lit.toNat / 2]?.getD 0xFFFFFFFF#32).toNat) ≤ lim ∧
          M8FrameCov s.core d.mrk idx0 lim
       else
        sp.toNat < c.max_vars ∧ ∃ idxs, M8MinStkInv s.core d.wsort d.mrk sp.toNat idx0 idxs false)

private def M8MinLpInv (c : FullCfg) (s : FullState) (keepSet : List Nat) (idx0 : Nat)
    (R : Mem 64 → Prop) : Nat → Tup Val [i64, i64, i64] → Mem 64 → Prop :=
  fun n (sp, cd, steps, ()) m' =>
    sp.toNat < c.max_vars ∧ cd.toNat < c.minDepth ∧
    steps.toNat ≤ m8MinLitMaxSteps s ∧ n = m8MinLitMaxSteps s - steps.toNat ∧
    ∃ (d : M8DfsScratch) (idxs : List Nat),
      d.Inv c s keepSet ∧ (FullMem c (d.st s) ⋆ R) m' ∧
      M8MinStkInv s.core d.wsort d.mrk sp.toNat idx0 idxs true

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

private theorem m8Dfs_mem_wsort_cast {c : FullCfg} {st1 st2 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (h : st1 = st2)
    (hm : (FullMem c st1 ⋆ R) m) : (FullMem c st2 ⋆ R) m := h ▸ hm

private theorem m8Dfs_mem_wsort_cast' {c : FullCfg} {st1 st2 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c st1 ⋆ R) m)
    (h : st1 = st2) : (FullMem c st2 ⋆ R) m := h ▸ hm

private theorem m8Dfs_st_wsort_eq (d : M8DfsScratch) (s : FullState)
    {i j : Nat} {v : BitVec 32} (h : i = j) :
    { d.st s with scratch := { (d.st s).scratch with
      wsort := (d.st s).scratch.wsort.set i v } } =
      ({ d with wsort := d.wsort.set j v }.st s) := by
  subst h; rfl

private theorem m8MinLitDfs_brk_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur0 : List (List Nat)} {s : FullState} {keepSet : List Nat}
    {root_lit : BitVec 32} {idx0 : Nat} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    {sp_b cd_b steps_b : Val i64} {ok_b : Val .bool} {m_b : Mem 64}
    (hMm : Γ.Has "full_min_mark" Spec.minMarkSpec)
    (hcore : FullOtfsCoreInv c F0 s) (hw0 : FullOtfsWitnessInv c F0 F_cur0 s.core)
    (hi0 : idx0 < s.core.trail_end)
    (hi0_eq : (s.core.trl[idx0]?.getD 0#32).toNat = root_lit.toNat ^^^ 1)
    (hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2)
    (hrl_lvl : (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (hno8 : ∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hQ : ∀ (res : Tup Val [.bool]) (s' : FullState) m',
      s'.LengthsOk c →
      Spec.MinMarkPost s s' keepSet ∧
        (res.1 = true →
          (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
            FullMinMarkInv s'.core keep') ∧
          FullMinMarkInv (fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
      (FullMem c s' ⋆ R) m' → Q res m')
    (hm_post_false : ∀ (d_f : M8DfsScratch) m_f,
      d_f.Inv c s keepSet → (FullMem c (d_f.st s) ⋆ R) m_f → Q (false, ()) m_f)
    (hB : M8MinBrkPost c s keepSet root_lit idx0 R (sp_b, cd_b, ok_b, steps_b, ()) m_b) :
    wp Γ Q X (m8MinLitDfsBrkExpr c.hdr c.pWsort sp_b ok_b) m_b := by
  have hlen0 := hcore.1.core_ok
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hcv := hlen0.cur_vars_le
  dsimp only [m8MinLitDfsBrkExpr]
  rcases hB with ⟨db, hsi_b, hm_b, hok_b⟩
  c0_hsplit
  · have hok_t : ok_b = true := by c0_grind
    simp only [hok_t, ↓reduceIte] at hok_b
    rcases hok_b with ⟨idxs_b, lim_b, hstk_b, hsp0, hlim_eq, hlim_le, hcov_b⟩
    have hlen1 : idxs_b.length = 1 := by rw [hstk_b.len]
    have hid0 : idxs_b = [idx0] := by
      rcases idxs_b with _ | ⟨x0, xs⟩ <;> simp at hlen1
      subst hlen1; have hx := hstk_b.idx0_eq; simp at hx; subst hx; rfl
    subst hid0
    obtain ⟨hdrop, hmk⟩ := m8MinLitDfs_ok_final hcore hsi_b hi0 hi0_eq hrl_lvl hno8 hlim_le hcov_b
    c0_hsteps!
    exact hQ (true, ()) (db.st s) m_b (hsi_b.core hcore).1
      ⟨⟨rfl, hsi_b.mrk_above, hsi_b.mono2, hsi_b.bit8, hsi_b.min_inv⟩, fun _ => ⟨hdrop, hmk⟩⟩
      hm_b
  · have hok_f : ok_b = false := by c0_grind
    simp only [hok_f] at hok_b
    rcases hok_b with ⟨hsp_b_lt, idxs_b, hstk_b⟩
    refine wp_loop_group (ts := [i64]) (fun n (j_bv, ()) m_j =>
        n = sp_b.toNat + 1 - j_bv.toNat ∧ 1 ≤ j_bv.toNat ∧ j_bv.toNat ≤ sp_b.toNat + 1 ∧
        ∃ dj : M8DfsScratch, dj.wsort = db.wsort ∧ dj.ticks = db.ticks ∧
          dj.Inv c s keepSet ∧
          (∀ k, j_bv.toNat ≤ k → ∀ hk : k < idxs_b.length,
            dj.mrk[(s.core.trl[idxs_b[k]'hk]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) ∧
          (FullMem c (dj.st s) ⋆ R) m_j)
      ?_
      (fun Jp hJp => by
        c0_hsteps!
        exact hJp sp_b.toNat (1#64, ()) m_b
          ⟨by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega, by decide,
            by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega,
            db, rfl, rfl, hsi_b, fun k hk1 hk2 => (hstk_b.slot k hk2).2 hk1, hm_b⟩)
    rintro Jp n_j ⟨j_bv, ⟨⟩⟩ m_j hJp
      ⟨rfl, hj1, hj_le, dj, hws_eq, htk_eq, hsi_j, hclr_j, hm_j⟩
    rw [Blocks.get_here]; c0_hsplit
    · have hj_le_sp : j_bv.toNat ≤ sp_b.toNat := by c0_grind
      have hj_idxs : j_bv.toNat < idxs_b.length := by rw [hstk_b.len]; omega
      have hj2_len : (j_bv <<< (1 : Nat)).toNat < (dj.st s).scratch.wsort.length := by
        dsimp only [M8DfsScratch.st, m8MinLitDfsState]
        change (j_bv <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
          dj.wsort.length
        rw [m8_bv64_shl1_toNat (by omega), hsi_j.wsort_len]; omega
      let sv := dj.wsort[(j_bv <<< (1 : Nat)).toNat]'hj2_len
      have hsv_nat : sv.toNat =
          (s.core.trl[idxs_b[j_bv.toNat]'hj_idxs]?.getD 0#32).toNat / 2 := by
        have hslot := (hstk_b.slot j_bv.toNat hj_idxs).1
        rw [List.getElem?_eq_getElem (by rw [← hws_eq, hsi_j.wsort_len]; omega), Option.getD_some]
          at hslot
        dsimp only [sv]
        change (dj.wsort[(j_bv <<< ((BitVec.signExtend 64
          (1 : BitVec 32)).toNat % 64)).toNat]'hj2_len).toNat = _
        simp only [m8_bv64_shl1_toNat (x := j_bv) (by omega), hws_eq]
        exact hslot
      have hsv_lt : sv.toNat < s.core.cur_vars := by
        rw [hsv_nat]; have := hw0.trail_lits_lt _ (hstk_b.bd j_bv.toNat hj_idxs); omega
      have hsv_lvl_root : (s.core.lvl[sv.toNat]?.getD 0#32).toNat ≤
          (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat := by
        rw [hsv_nat, ← hrv_root]; exact hstk_b.lvl_le_root j_bv.toNat hj_idxs
      have hno8_sv : (dj.mrk[sv.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
        rw [hsi_j.bit8 sv.toNat hsv_lt]; exact hno8 sv.toNat hsv_lt hsv_lvl_root
      have hz_sv : dj.mrk[sv.toNat]?.getD 0#8 = 0#8 := by
        rw [hsv_nat]; exact hclr_j j_bv.toNat (Nat.le_refl _) hj_idxs
      c0_hsteps!; apply wp_call_of_spec; apply hMm
      refine m8_fullMinMarkSpec_zero_inv hcore hsi_j.mrk_len hsi_j.wsort_len hsi_j.mclr_len
        hsi_j.mcl_le hm_j hsv_lt hz_sv ((4 : BitVec 32).setWidth 8) fun m_j1 hm_j1 => ?_
      have h4 : (4 : BitVec 32).setWidth 8 = 4#8 := rfl
      rw [h4] at hm_j1
      have hj1_nat : (j_bv + 1#64).toNat = j_bv.toNat + 1 := min_bv64_add1 (by omega)
      have hsi_j' : M8MinStInv c s keepSet dj.mrk db.wsort dj.min_clr dj.mcl dj.mcf dj.ticks := by
        dsimp only [M8DfsScratch.Inv] at hsi_j; rwa [← hws_eq]
      obtain ⟨hsi_j1, hclr_j1⟩ := m8MinLit_unwind_post hcore hw0 hsi_j' hstk_b hj_idxs
        hsv_nat hsv_lt hno8_sv hz_sv hj1_nat hclr_j
      c0_hsteps!
      let k' := fullMinMarkCore
        (m8MinLitDfsState s dj.mrk dj.wsort dj.min_clr dj.mcl dj.mcf dj.ticks).core
        sv.toNat 4#8
      let dj1 : M8DfsScratch := { dj with
        mrk := k'.mrk, min_clr := k'.min_clr, mcl := k'.min_clr_len, mcf := k'.min_clr_full }
      exact hJp (sp_b.toNat + 1 - (j_bv + 1#64).toNat) (j_bv + 1#64, ()) m_j1
        (by rw [hj1_nat]; omega)
        ⟨by rw [hj1_nat], by omega, by rw [hj1_nat]; omega, dj1, hws_eq, htk_eq,
          by simpa only [M8DfsScratch.Inv, dj1, k', hws_eq] using hsi_j1,
          by simpa only [dj1, k', hws_eq] using hclr_j1,
          by simpa only [M8DfsScratch.st, dj1, k', hws_eq, htk_eq] using hm_j1⟩
    · c0_hsteps!; exact hm_post_false dj m_j hsi_j hm_j

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

private theorem m8MinLitDfs_cu_wp {Γ : Env} {c : FullCfg} {s : FullState} {d : M8DfsScratch}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {sp cd steps : Val i64} {ul : Val i32}
    {check_used : Val .bool} {Js : Cont [i64, i64, .bool, i64]} {Jcu : Cont []} {m_p : Mem 64}
    (hst_ok : s.LengthsOk c) (_hcv_bd : s.core.cur_vars < 2 ^ 64)
    (hm_p : (FullMem c (d.st s) ⋆ R) m_p)
    (hB : Js (sp, cd, false, steps, ()) m_p) (hJcu : Jcu () m_p) :
    wp Γ Q X (m8MinLitDfsCuExpr (BitVec.ofNat 64 s.core.cur_level)
      (BitVec.ofNat 64 s.core.cur_vars) c.pShrinkStk sp cd steps ul check_used Js Jcu) m_p := by
  have hcv := hst_ok.core_ok.cur_vars_le
  dsimp only [m8MinLitDfsCuExpr]
  c0_hsplit
  · c0_hsplit
    · have hul_ss : (ul.setWidth 64).toNat < (d.st s).scratch.shrink_stk.length := by
        dsimp only [M8DfsScratch.st, m8MinLitDfsState]
        rw [hst_ok.scratch_ok.shrink_stk_len, bv_c0_zext32_64]
        have hul_cv : ul.toNat < s.core.cur_vars := by c0_grind
        omega
      c0_hsplit
      · c0_hsplit <;> (first | exact hB | exact hJcu)
      · exact hJcu
    · exact hJcu
  · exact hJcu

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
  c0_hsplit
  · c0_hsplit
    · have hcd_pos : 0 < cd.toNat := by c0_grind
      c0_hsteps!; exact hJcd (cd - 1) (by rw [min_bv64_sub1 hcd_pos]; omega)
    · exact hJcd cd hcd_lt
  · exact hJcd cd hcd_lt

private def m8MinLitDfsBodyExpr {V : Ty → Type} {C : List Ty → Type}
    (h pRsns pMark pLvl pShrinkStk sp cd steps cur_vars clvl : V i64)
    (v u : V i32) (check_used : V .bool)
    (B : C [i64, i64, .bool, i64]) (L : C [i64, i64, i64])
    (kPush : Expr V C [.bool]) : Expr V C [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  let op32 (c : OpCode [i32, i32] [i32]) (a b : Arg V i32) := Op.mk c (a, b, ())
  .let_ (Op.mk (.zext 32 64) (.var u, ())) fun p_63 =>
  .let_ (op64 (.mul i64) (.var p_63.fst) (.imm 4)) fun p_64 =>
  .let_ (op64 (.add i64) (.var pLvl) (.var p_64.fst)) fun p_65 =>
  .load i32 (.var p_65.fst) fun ld_14 =>
  .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var u, .var v, ())) fun p_66 =>
  .jnz (.var p_66.fst)
    (.jump L (.var sp, .var cd, .var steps, ()))
    (.let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var ld_14, .imm 0, ())) fun p_67 =>
     .jnz (.var p_67.fst)
       (.jump L (.var sp, .var cd, .var steps, ()))
       (.let_ (Op.mk (.zext 32 64) (.var u, ())) fun p_68 =>
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
             (.let_ (Op.mk (.zext 32 64) (.var u, ())) fun p_84 =>
              .let_ (op64 (.mul i64) (.var p_84.fst) (.imm 4)) fun p_85 =>
              .let_ (op64 (.add i64) (.var pRsns) (.var p_85.fst)) fun p_86 =>
              .load i32 (.var p_86.fst) fun ld_16 =>
              .let_ (Op.mk (.cmp .eq i32 .bool rfl)
                (.var ld_16, .imm 4294967295, ())) fun p_87 =>
              .jnz (.var p_87.fst)
                (.let_ (Op.mk (.trunc 32 8) (.imm 4, ())) fun p_88 =>
                 .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
                   (.var h, .var u, .var p_88.fst, ()) fun _ =>
                 .jump B (.var sp, .var cd, .imm false, .var steps, ()))
                (.group (sig := [[]]) (fun _ => .cons (fun _ => kPush) .nil)
                 fun Js_2 => m8MinLitDfsCuExpr clvl cur_vars pShrinkStk sp cd steps
                   ld_14 check_used B Js_2.fst)))))

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
          (m8MinLitDfsBodyExpr h pRsns pMark pLvl pShrinkStk sp cd steps cur_vars clvl
            v p_60.fst check_used B L
            (.let_ (op64 (.add i64) (.var sp) (.imm 1)) fun p_89 =>
             .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var p_89.fst, .var mv, ())) fun p =>
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
                     (.jump L (.var p.fst, .var cd, .var steps, ()))))))))
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

private theorem m8MinLitDfs_body_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur0 : List (List Nat)} {s : FullState} {keepSet : List Nat}
    {d d2 : M8DfsScratch} {idx0 : Nat} {root_lit : BitVec 32} {R : Mem 64 → Prop}
    {Q : Post [.bool]} {X : XPost} {B : Cont [i64, i64, .bool, i64]}
    {L : Cont [i64, i64, i64]} {sp cd steps : Val i64} {idxs : List Nat}
    {v _pword pos rsn lit newPw u_c0 : Val i32} {check_used : Val .bool} {m : Mem 64}
    {kPush : Expr Val Cont [.bool]}
    (hMm : Γ.Has "full_min_mark" Spec.minMarkSpec)
    (hcore : FullOtfsCoreInv c F0 s) (_hw0 : FullOtfsWitnessInv c F0 F_cur0 s.core)
    (hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hno8 : ∀ w < s.core.cur_vars,
      (s.core.lvl[w]?.getD 0#32).toNat ≤ (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[w]?.getD 0#8 &&& 8#8) = 0#8)
    (hB : ∀ r m', M8MinBrkPost c s keepSet root_lit idx0 R r m' → B r m')
    (hL : ∀ n' ys m', n' < m8MinLitMaxSteps s - steps.toNat →
      M8MinLpInv c s keepSet idx0 R n' ys m' → L ys m')
    (hsp_lt : sp.toNat < c.max_vars) (hcd_lt : cd.toNat < c.minDepth)
    (hlt_st : steps.toNat < m8MinLitMaxSteps s)
    (hsteps1 : (steps + 1).toNat = steps.toNat + 1)
    (hdec_n : m8MinLitMaxSteps s - (steps + 1).toNat < m8MinLitMaxSteps s - steps.toNat)
    (hsp_idxs : sp.toNat < idxs.length)
    (hsi : d.Inv c s keepSet) (hsi_p : d2.Inv c s keepSet) (hmrk_d2 : d2.mrk = d.mrk)
    (hd2_ws : d2.wsort = d.wsort.set (2 * sp.toNat + 1) newPw)
    (hstk : M8MinStkInv s.core d.wsort d.mrk sp.toNat idx0 idxs true)
    (hstk2_drop : M8MinStkInv s.core d2.wsort d2.mrk sp.toNat idx0 idxs false)
    (hv_nat : v.toNat = (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2)
    (hpos_nat : pos.toNat = (d.wsort[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
    (hpar_eq : (newPw &&& 0x7FFFFFFF#32).toNat =
      (d.wsort[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1)
    (hsz_lt : pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1 else
        fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
          0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32)
    (hcov_sp : M8FrameCov s.core d.mrk (idxs[sp.toNat]'hsp_idxs) pos.toNat)
    (hlit_eq : lit.toNat = m8RsnLit s.core rsn pos.toNat)
    (hu_eq_lit : u_c0 = lit >>> 1)
    (hu_cv : (lit >>> 1).toNat < s.core.cur_vars)
    (hm : (FullMem c (d2.st s) ⋆ R) m)
    (hkPush : ∀ u_idx (_hu_idx_lt : u_idx < idxs[sp.toNat]'hsp_idxs)
      (_hu_idx_eq : (s.core.trl[u_idx]?.getD 0#32).toNat = lit.toNat ^^^ 1)
      (_hu_bd_lt : (lit >>> 1).toNat < s.core.cur_vars)
      (_hu_nat_idx : (lit >>> 1).toNat = (s.core.trl[u_idx]?.getD 0#32).toNat / 2)
      (_hu_lvl_root : (s.core.lvl[(s.core.trl[u_idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
      (_hno8_u : (d.mrk[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8)
      (_hmu2 : (d.mrk[(lit >>> 1).toNat]?.getD 0#8 &&& 2#8) = 0#8)
      (_hmu4 : (d.mrk[(lit >>> 1).toNat]?.getD 0#8 &&& 4#8) = 0#8)
      (_hu_rsns_len : ((lit >>> 1).setWidth 64).toNat < (d2.st s).core.rsns.length)
      (_hrsn_u_ne : s.core.rsns[(lit >>> 1).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32),
      wp Γ Q X kPush m) :
    wp Γ Q X (m8MinLitDfsBodyExpr c.hdr c.pReason c.pMark c.pLevel c.pShrinkStk sp cd
      (steps + 1) (BitVec.ofNat 64 s.core.cur_vars) (BitVec.ofNat 64 s.core.cur_level)
      v u_c0 check_used B L kPush) m := by
  subst hu_eq_lit
  have hlen0 := hcore.1.core_ok
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hcv := hlen0.cur_vars_le
  let maxSteps := m8MinLitMaxSteps s
  have hu_lvl_len : ((lit >>> 1).setWidth 64).toNat < (d2.st s).core.lvl.length := by
    dsimp only [M8DfsScratch.st, m8MinLitDfsState]; rw [hlen0.lvl_len, bv_c0_zext32_64]; omega
  dsimp only [m8MinLitDfsBodyExpr]
  c0_hsplit
  · have heq_var : lit.toNat / 2 = (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
      have heq_uv : lit >>> 1 = v := hc
      rw [← hv_nat, ← bv32_lshr_1, heq_uv]
    exact hL (maxSteps - (steps + 1).toNat) (sp, cd, steps + 1, ()) m hdec_n
      ⟨hsp_lt, hcd_lt, hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl, d2, idxs, hsi_p, hm, by
        rw [hd2_ws, hmrk_d2]
        exact m8MinLitDfs_ok_res hcore hstk hi0_lvl hsi.wsort_len hsp_lt hsp_idxs newPw hpar_eq
          (hpos_nat ▸ hsz_lt) (u_idx := 0) (by
            rw [← hpos_nat, ← hrsn_eq, ← hlit_eq]; exact Or.inl heq_var)⟩
  · have hu_neq : lit.toNat / 2 ≠ (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
      have hne_uv : lit >>> 1 ≠ v := hc
      rw [← hv_nat]; intro heq; apply hne_uv
      exact BitVec.eq_of_toNat_eq (by simpa only [bv32_lshr_1] using heq)
    have hfc := m8FrameCov_edge_exists hcore (hstk.bd sp.toNat hsp_idxs)
      (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
      hcov_sp hsz_lt (by rwa [← hrsn_eq, ← hlit_eq])
    rw [← hrsn_eq, ← hlit_eq] at hfc
    obtain ⟨hu_lt2, u_idx, hu_idx_lt, hu_idx_eq, hu_lvl_le⟩ := hfc
    have hu_bd_lt : (lit >>> 1).toNat < s.core.cur_vars := by
      rw [bv32_lshr_1]; exact Nat.div_lt_of_lt_mul hu_lt2
    c0_hsplit
    · refine hL (maxSteps - (steps + 1).toNat) (sp, cd, steps + 1, ()) m hdec_n
        ⟨hsp_lt, hcd_lt, hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl, d2, idxs, hsi_p, hm, by
          rw [hd2_ws, hmrk_d2]
          refine m8MinStkInv_step_top hstk hsi.wsort_len hsp_lt newPw fun _ => ?_
          rw [hpar_eq, ← hpos_nat]
          refine m8FrameCov_step hcore (hstk.bd sp.toNat hsp_idxs)
            (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
            hcov_sp hsz_lt (Or.inr ⟨u_idx, hu_idx_lt, by rwa [← hrsn_eq, ← hlit_eq], Or.inl ?_⟩)
          rw [← hrsn_eq, ← hlit_eq]
          have hvw := bv_c0_zext32_64 (lit >>> 1); rw [bv32_lshr_1] at hvw
          rw [List.getElem?_eq_getElem (hvw ▸ hu_lvl_len), Option.getD_some]
          exact congrArg BitVec.toNat hc⟩
    · have hu_mrk_len : ((lit >>> 1).setWidth 64).toNat < (d2.st s).core.mrk.length := by
        dsimp only [M8DfsScratch.st, m8MinLitDfsState]
        rw [hsi_p.mrk_len, bv_c0_zext32_64]; exact Nat.lt_of_lt_of_le hu_bd_lt hcv
      let mu := d.mrk[((lit >>> 1).setWidth 64).toNat]'(hmrk_d2 ▸ hu_mrk_len)
      have hmu_eq : mu = d.mrk[(lit >>> 1).toNat]?.getD 0#8 := by
        rw [List.getElem?_eq_getElem
          (by rw [hsi.mrk_len]; exact Nat.lt_of_lt_of_le hu_bd_lt hcv), Option.getD_some]
        dsimp only [mu]; simp only [bv_c0_zext32_64]
      have hmu_mrk : d2.mrk[((lit >>> 1).setWidth 64).toNat]'hu_mrk_len = mu := by
        dsimp only [mu]; simp only [hmrk_d2]
      c0_hsplit
      · have hmu_is2 : (mu &&& 2#8) ≠ 0#8 := by
          rw [← hmu_mrk]; simp only [bv_c0_zext32_64] at *; c0_bv_bit_grind
        refine hL (maxSteps - (steps + 1).toNat) (sp, cd, steps + 1, ()) m hdec_n
          ⟨hsp_lt, hcd_lt, hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl, d2, idxs, hsi_p, hm, by
            rw [hd2_ws, hmrk_d2]
            refine m8MinStkInv_step_top hstk hsi.wsort_len hsp_lt newPw fun _ => ?_
            rw [hpar_eq, ← hpos_nat]
            refine m8FrameCov_step hcore (hstk.bd sp.toNat hsp_idxs)
              (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
              hcov_sp hsz_lt (Or.inr ⟨u_idx, hu_idx_lt,
                by rwa [← hrsn_eq, ← hlit_eq], Or.inr ?_⟩)
            rw [← hrsn_eq, ← hlit_eq, ← bv32_lshr_1, ← hmu_eq]; exact hmu_is2⟩
      · have hmu_n2 : (mu &&& 2#8) = 0#8 := by
          rw [← hmu_mrk]; simp only [bv_c0_zext32_64] at *; c0_bv_bit_grind
        c0_hsplit
        · c0_hsteps!; exact hB _ _ ⟨d2, hsi_p, hm, ⟨hsp_lt, idxs, hstk2_drop⟩⟩
        · obtain ⟨hu_nat_idx, hu_lvl_root, hno8_u⟩ := m8MinLit_leaf_pre hsi hstk hsp_idxs
            hu_idx_eq hu_lvl_le hu_bd_lt hno8 hrv_root
          have hu_rsns_len : ((lit >>> 1).setWidth 64).toNat < (d2.st s).core.rsns.length := by
            dsimp only [M8DfsScratch.st, m8MinLitDfsState]
            rw [hlen0.rsns_len, bv_c0_zext32_64, bv32_lshr_1]; omega
          have hmu_n4 : (mu &&& 4#8) = 0#8 := by
            rw [← hmu_mrk]; simp only [bv_c0_zext32_64] at *; c0_bv_bit_grind
          c0_hsplit
          · c0_hsteps!; apply wp_call_of_spec; apply hMm
            refine m8MinLitDfs_poison_leaf hcore hsi_p hstk2_drop
              hsp_idxs hu_idx_lt hu_nat_idx hu_bd_lt (u_bv := lit >>> 1) (hmrk_d2 ▸ hno8_u)
              (hmrk_d2 ▸ by rwa [← hmu_eq]) (hmrk_d2 ▸ by rwa [← hmu_eq]) hm
              fun mrk4 mclr4 mcl4 mcf4 m4 _ _ _ _ hsi4 hm4 hstk4 => by
                c0_hsteps!
                exact hB _ _ ⟨{ d2 with
                  mrk := mrk4, min_clr := mclr4, mcl := mcl4, mcf := mcf4 },
                  hsi4, hm4, ⟨hsp_lt, idxs, hstk4⟩⟩
          · have hrsn_u_ne :
                s.core.rsns[(lit >>> 1).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
              rw [List.getElem?_eq_getElem (by rw [hlen0.rsns_len, bv32_lshr_1]; omega),
                Option.getD_some]
              simp only [bv32_lshr_1]; exact hc
            refine wp_join_group (ts := []) (fun _ m_cu => m_cu = m) ?_ ?_
            · rintro _ ⟨⟩ m_cu rfl; rw [Blocks.get_here]
              exact hkPush u_idx hu_idx_lt hu_idx_eq hu_bd_lt hu_nat_idx hu_lvl_root hno8_u
                (by rwa [← hmu_eq]) (by rwa [← hmu_eq]) hu_rsns_len hrsn_u_ne
            · rintro Jcu hJcu
              exact m8MinLitDfs_cu_wp hcore.1 (by omega) hm
                (hB _ _ ⟨d2, hsi_p, hm, ⟨hsp_lt, idxs, hstk2_drop⟩⟩) (hJcu () m rfl)

private theorem m8MinLitDfs_bin_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur0 : List (List Nat)} {s : FullState} {keepSet : List Nat}
    {d : M8DfsScratch} {idx0 : Nat} {root_lit : BitVec 32} {R : Mem 64 → Prop}
    {Q : Post [.bool]} {X : XPost} {B : Cont [i64, i64, .bool, i64]}
    {L : Cont [i64, i64, i64]} {sp cd steps : Val i64} {idxs : List Nat}
    {v pword pos rsn : Val i32} {check_used : Val .bool} {m' : Mem 64}
    (hMm : Γ.Has "full_min_mark" Spec.minMarkSpec)
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
      d.wsort.length)
    (hsp_idxs : sp.toNat < idxs.length)
    (hsi : d.Inv c s keepSet)
    (hstk : M8MinStkInv s.core d.wsort d.mrk sp.toNat idx0 idxs true)
    (hv_nat : v.toNat = (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2)
    (hv_lt : v.toNat < s.core.cur_vars)
    (_hpw_eq : pword = d.wsort[(sp <<< ((BitVec.signExtend 64
      (1 : BitVec 32)).toNat % 64) + 1).toNat]'hstk_od)
    (_hpos_eq : pos = pword &&& 0x7FFFFFFF#32)
    (hpos_nat : pos.toNat = (d.wsort[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32)
    (hcov_sp : M8FrameCov s.core d.mrk (idxs[sp.toNat]'hsp_idxs) pos.toNat)
    (hbin' : (rsn &&& 0x80000000#32) ≠ 0#32)
    (hm' : (FullMem c (d.st s) ⋆ R) m') :
    wp Γ Q X (m8MinLitDfsBinExpr c.hdr c.pReason c.pMark c.pLevel c.pWsort c.pShrinkStk sp cd
      (steps + 1) (BitVec.ofNat 64 s.core.cur_vars) (BitVec.ofNat 64 c.max_vars)
      (BitVec.ofNat 64 s.core.cur_level) v pword pos rsn check_used B L) m' := by
  have hlen0 := hcore.1.core_ok
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hcv := hlen0.cur_vars_le
  let maxSteps := m8MinLitMaxSteps s
  dsimp only [m8MinLitDfsBinExpr]
  c0_hsplit
  · have hpos_0 : pos.toNat = 0 := by c0_grind
    have hpos_pw0 : (pword &&& 0x7FFFFFFF#32) = 0#32 := by c0_grind
    have hsz_lt : pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1 else
        fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
          0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
      simp only [← hrsn_eq, eq_true hbin', ↓reduceIte]; omega
    have hpar_eq : ((pword ||| 1#32) &&& 0x7FFFFFFF#32).toNat =
        (d.wsort[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1 := by
      rw [← hpos_nat, hpos_0]; exact m8_bv32_mask31_or1_eq hpos_pw0
    have hstk_od' : (sp <<< (1 : Nat) + 1).toNat < (d.st s).scratch.wsort.length := hstk_od
    let d2 : M8DfsScratch := { d with wsort := d.wsort.set (2 * sp.toNat + 1) (pword ||| 1#32) }
    have hw2_len : d2.wsort.length = 2 * c.max_vars := by simp [d2, hsi.wsort_len]
    have hsi_p := m8MinStInv_with_wsort hsi hw2_len
    let lit := rsn &&& 0x7FFFFFFF#32
    have hlit_eq : lit.toNat = m8RsnLit s.core rsn pos.toNat := by
      dsimp only [m8RsnLit, lit]; simp only [eq_true hbin', ↓reduceIte]
    have hstk2_drop : M8MinStkInv s.core d2.wsort d.mrk sp.toNat idx0 idxs false := by
      refine ⟨hstk.len, hstk.idx0_eq, hstk.bd, hstk.dec, hstk.lvl_le_root,
        fun j hj => ?_, fun hc => by cases hc⟩
      dsimp only [d2]; rw [List.getElem?_set_ne (by omega)]; exact hstk.slot j hj
    c0_hsplit
    · exfalso
      have hu_ge : s.core.cur_vars ≤ (lit >>> 1).toNat := by c0_grind
      have hu_lt_2v : lit.toNat < 2 * s.core.cur_vars := by
        by_cases heq_var : lit.toNat / 2 =
            (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2
        · have hl1 := hw0.trail_lits_lt _ (hstk.bd sp.toNat hsp_idxs); omega
        · have hfc := m8FrameCov_edge_exists hcore (hstk.bd sp.toNat hsp_idxs)
            (Nat.lt_of_le_of_lt (hstk.lvl_le_root sp.toNat hsp_idxs) hi0_lvl)
            hcov_sp hsz_lt (by rwa [← hrsn_eq, ← hlit_eq])
          rw [← hrsn_eq, ← hlit_eq] at hfc; exact hfc.1
      rw [bv32_lshr_1] at hu_ge; omega
    · rw [m8Dfs_st_wsort_eq d s (by
          show (sp <<< (1 : Nat) + 1).toNat = 2 * sp.toNat + 1
          change (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat = _
          exact m8_bv64_shl1_add1_toNat (by omega))] at hm
      have hu_cv : (lit >>> 1).toNat < s.core.cur_vars := by c0_grind
      refine m8MinLitDfs_body_wp (d := d) (d2 := d2) (_pword := pword) (newPw := pword ||| 1#32)
        hMm hcore hw0 hrv_root hi0_lvl hno8 hB hL
        hsp_lt hcd_lt hlt_st hsteps1 hdec_n hsp_idxs hsi hsi_p rfl rfl hstk hstk2_drop
        hv_nat hpos_nat hpar_eq hsz_lt hrsn_eq hcov_sp hlit_eq rfl hu_cv hm
        fun u_idx hu_idx_lt hu_idx_eq hu_bd_lt hu_nat_idx hu_lvl_root hno8_u hmu2 hmu4
            hu_rsns_len hrsn_u_ne => by
          c0_hsplit
          · c0_hsteps!; exact hB _ _ ⟨d2, hsi_p, hm, ⟨hsp_lt, idxs, hstk2_drop⟩⟩
          · have hsp1_nat : (sp + 1).toNat = sp.toNat + 1 := by c0_bound
            have hsp1_lt : sp.toNat + 1 < c.max_vars := by
              have h_not_le : ¬ c.max_vars ≤ (sp + 1).toNat := by c0_grind
              omega
            have hstk_ev1 : ((sp + 1) <<< (1 : Nat)).toNat <
                (d2.st s).scratch.wsort.length := by
              dsimp only [M8DfsScratch.st, m8MinLitDfsState]
              change ((sp + 1) <<< ((BitVec.signExtend 64
                (1 : BitVec 32)).toNat % 64)).toNat < d2.wsort.length
              rw [m8_bv64_shl1_toNat (x := sp + 1) (by omega), hw2_len]; omega
            let d2a : M8DfsScratch :=
              { d2 with wsort := d2.wsort.set (2 * (sp.toNat + 1)) (lit >>> 1) }
            have hstk_od1 : ((sp + 1) <<< (1 : Nat) + 1).toNat <
                (d2a.st s).scratch.wsort.length := by
              dsimp only [M8DfsScratch.st, m8MinLitDfsState, d2a]
              rw [List.length_set]
              change ((sp + 1) <<< ((BitVec.signExtend 64
                (1 : BitVec 32)).toNat % 64) + 1).toNat < d2.wsort.length
              rw [m8_bv64_shl1_add1_toNat (x := sp + 1) (by omega), hw2_len]; omega
            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
            replace hm : (FullMem c (d2a.st s) ⋆ R) m := m8Dfs_mem_wsort_cast (by
              dsimp only [M8DfsScratch.st, m8MinLitDfsState, d2a]
              congr 1; congr 1
              exact congrArg (fun idx => d2.wsort.set idx (lit >>> 1)) (by
                change ((sp + 1) <<< ((BitVec.signExtend 64
                  (1 : BitVec 32)).toNat % 64)).toNat = 2 * (sp.toNat + 1)
                rw [m8_bv64_shl1_toNat (x := sp + 1) (by omega), hsp1_nat])) hm
            c0_hsteps!
            let d3 : M8DfsScratch := { d2a with
              wsort := d2a.wsort.set (2 * (sp.toNat + 1) + 1) 0#32 }
            replace hm : (FullMem c (d3.st s) ⋆ R) m := m8Dfs_mem_wsort_cast (by
              dsimp only [M8DfsScratch.st, m8MinLitDfsState, d3, d2a]
              congr 1; congr 1
              exact congrArg (fun idx =>
                  (d2.wsort.set (2 * (sp.toNat + 1)) (lit >>> 1)).set idx 0#32) (by
                change ((sp + 1) <<< ((BitVec.signExtend 64
                  (1 : BitVec 32)).toNat % 64) + 1).toNat = 2 * (sp.toNat + 1) + 1
                rw [m8_bv64_shl1_add1_toNat (x := sp + 1) (by omega), hsp1_nat])) hm
            obtain ⟨hsi3, hstk3⟩ := m8MinLit_push_stk hcore hsi hstk hi0_lvl hsp_idxs
              hsp1_lt hpar_eq m8_bv32_mask31_zero_eq0 hpos_nat hsz_lt hu_bd_lt hu_idx_lt
              hu_idx_eq hu_nat_idx hu_lvl_root hno8_u hmu2 hmu4 hrsn_u_ne hrsn_eq hlit_eq
            exact hL (maxSteps - (steps + 1).toNat) (sp + 1, cd, steps + 1, ()) m hdec_n
              ⟨by rw [hsp1_nat]; exact hsp1_lt, hcd_lt,
                hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl, d3, idxs ++ [u_idx], hsi3, hm,
                by rwa [hsp1_nat]⟩
  · have hpos_ge1 : 1 ≤ pos.toNat :=
      Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq h0)
    c0_hsplit
    · c0_hsteps!
      have hsp0' : sp.toNat = 0 := congrArg BitVec.toNat hc
      have hsp0 : sp = 0 := BitVec.eq_of_toNat_eq hsp0'
      have hi0_eq_w : idxs[sp.toNat]'hsp_idxs = idx0 := by
        have he := hstk.idx0_eq
        have hz : idxs[sp.toNat]'hsp_idxs = idxs[0]'(by rw [hstk.len]; omega) := by
          simp only [hsp0']
        rw [List.getElem?_eq_getElem (by rw [hstk.len]; omega)] at he
        exact hz.trans (Option.some.inj he)
      simp only [hi0_eq_w] at hcov_sp hrsn_eq
      exact hB _ _ ⟨d, hsi, hm', ⟨idxs, pos.toNat, hsp0' ▸ hstk, hsp0', by rw [hpos_nat, hsp0'],
        by simp only [← hrv_root, ← hrsn_eq, eq_true hbin', ↓reduceIte]; exact hpos_ge1, hcov_sp⟩⟩
    · have hsp_gt0 : 0 < sp.toNat :=
        Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq h)
      c0_hsteps!; apply wp_call_of_spec; apply hMm
      dsimp only [M8DfsScratch.st] at hm'
      refine m8MinLitDfs_pop_state hcore hsi hstk hsp_gt0 hsp_idxs hi0_lvl hv_nat hv_lt
        (lim := pos.toNat) (by simp only [← hrsn_eq, eq_true hbin', ↓reduceIte]; omega)
        hcov_sp hm' fun k4 m4 hk4 hsi4 hstk4 hm4 => ?_
      refine wp_join_group (ts := [i64]) (fun (cd', _) m_cd =>
          cd'.toNat < c.minDepth ∧ m_cd = m4)
        (fun _ ⟨cd', ⟨⟩⟩ m_cd ⟨hcd', rfl⟩ => by
          rw [Blocks.get_here]; c0_hsteps!
          have hsp_m1 : (sp - 1).toNat = sp.toNat - 1 := by c0_bound
          exact hL (maxSteps - (steps + 1).toNat) (sp - 1, cd', steps + 1, ()) m_cd hdec_n
            ⟨by rw [hsp_m1]; omega, hcd', hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl,
              { d with
                mrk := k4.mrk, min_clr := k4.min_clr, mcl := k4.min_clr_len,
                mcf := k4.min_clr_full }, idxs.take sp.toNat, hsi4, hm4, by rwa [hsp_m1]⟩)
        ?_
      rintro Jcd hJcd
      exact m8MinLitDfs_cd_wp hcd_lt fun cd' hcd' => by
        c0_hsteps!; exact hJcd (cd', ()) m4 ⟨hcd', rfl⟩

private theorem m8MinLitDfs_false_post {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {root_lit : BitVec 32} {R : Mem 64 → Prop} {Q : Post [.bool]}
    {d_f : M8DfsScratch} {m_f : Mem 64} (hcore : FullOtfsCoreInv c F0 s)
    (hQ : ∀ (res : Tup Val [.bool]) (s' : FullState) m',
      s'.LengthsOk c →
      Spec.MinMarkPost s s' keepSet ∧
        (res.1 = true →
          (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
            FullMinMarkInv s'.core keep') ∧
          FullMinMarkInv (fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
      (FullMem c s' ⋆ R) m' → Q res m')
    (hsi_f : d_f.Inv c s keepSet) (hm_f : (FullMem c (d_f.st s) ⋆ R) m_f) :
    Q (false, ()) m_f := by
  have hcore_f := hsi_f.core hcore
  exact hQ (false, ()) (d_f.st s) m_f hcore_f.1
    ⟨⟨rfl, hsi_f.mrk_above, hsi_f.mono2, hsi_f.bit8, hsi_f.min_inv⟩, fun hc => by cases hc⟩ hm_f

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
  rw [hrv, ← bv32_lshr_1, ← bv_c0_zext32_64 (root_lit >>> 1),
    List.getElem?_eq_getElem hrl_rsns, Option.getD_some]
  c0_grind

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
  have hpos_lt' : pos.toNat < sz.toNat := by c0_grind
  have hsz_lt : pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
      0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1 else
      fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
    simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte, ← hsz_e]; exact hpos_lt'
  have := hwf.2.2.1; have := hlen0.arena_len_le
  have hpos_lt_sz : pos.toNat < fullArenaClauseSizeCore s.core rsn.toNat := hsz_e ▸ hpos_lt'
  have hpos_add1 : (pos + 1#32).toNat = pos.toNat + 1 := by c0_bound
  have hpos_add1_lt : (pos + 1#32).toNat < 2 ^ 31 := by omega
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
  have hcd1_lt : cd.toNat + 1 < c.minDepth := by unfold FullCfg.minDepth at hcd_lt' ⊢; c0_grind
  have hsp1_lt : sp.toNat + 1 < c.max_vars := by c0_grind
  have hsp1_nat : (sp + 1).toNat = sp.toNat + 1 := by c0_bound
  have hcd1_nat : (cd + 1).toNat = cd.toNat + 1 := by c0_bound
  refine ⟨hcd1_lt, hsp1_nat, hcd1_nat, hsp1_lt, ?_, ?_⟩
  · rw [m8_bv64_shl1_toNat (x := sp + 1) (by omega), hw2_len]; omega
  · rw [m8_bv64_shl1_add1_toNat (x := sp + 1) (by omega), hw2_len]; omega

private theorem m8MinLitDfs_big_pop_brk {c : FullCfg} {s : FullState}
    {keepSet : List Nat} {root_lit rsn sz pos : BitVec 32} {d : M8DfsScratch}
    {idx0 : Nat} {sp cd steps : BitVec 64} {idxs : List Nat} {R : Mem 64 → Prop} {m_tk : Mem 64}
    (hsi2 : d.Inv c s keepSet)
    (hstk : M8MinStkInv s.core d.wsort d.mrk sp.toNat idx0 idxs true)
    (hsp_idxs : sp.toNat < idxs.length)
    (hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2)
    (hpos_nat : pos.toNat = (d.wsort[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32)
    (hbin_f : ¬ (rsn &&& 0x80000000#32) ≠ 0#32)
    (hsz_e : sz.toNat = fullArenaClauseSizeCore s.core rsn.toNat)
    (hpos_ge : pos.ult sz = false)
    (hcov_sp : M8FrameCov s.core d.mrk (idxs[sp.toNat]'hsp_idxs) pos.toNat)
    (hsp0 : sp = 0) (hm_tk : (FullMem c (d.st s) ⋆ R) m_tk) :
    M8MinBrkPost c s keepSet root_lit idx0 R (sp, cd, true, steps, ()) m_tk := by
  have hpos_ge' : sz.toNat ≤ pos.toNat := by c0_grind
  have hsp0' : sp.toNat = 0 := congrArg BitVec.toNat hsp0
  have hi0_eq_w : idxs[sp.toNat]'hsp_idxs = idx0 := by
    have he := hstk.idx0_eq
    have hz : idxs[sp.toNat]'hsp_idxs = idxs[0]'(by rw [hstk.len]; omega) := by simp only [hsp0']
    rw [List.getElem?_eq_getElem (by rw [hstk.len]; omega)] at he
    exact hz.trans (Option.some.inj he)
  simp only [hi0_eq_w] at hcov_sp hrsn_eq
  exact ⟨d, hsi2, hm_tk, ⟨idxs, pos.toNat, hsp0' ▸ hstk, hsp0', by rw [hpos_nat, hsp0'],
    by simp only [← hrv_root, ← hrsn_eq, eq_false hbin_f, ↓reduceIte, ← hsz_e]; exact hpos_ge',
    hcov_sp⟩⟩

private theorem m8MinLitDfs_big_wsort2_inv {c : FullCfg} {s : FullState}
    {keepSet : List Nat} {d : M8DfsScratch} {idx0 : Nat} {sp : BitVec 64}
    {idxs : List Nat} {newPw : BitVec 32} (hsi2 : d.Inv c s keepSet)
    (hstk : M8MinStkInv s.core d.wsort d.mrk sp.toNat idx0 idxs true) :
    let d2 : M8DfsScratch := { d with wsort := d.wsort.set (2 * sp.toNat + 1) newPw }
    d2.wsort.length = 2 * c.max_vars ∧
    d2.Inv c s keepSet ∧
    M8MinStkInv s.core d2.wsort d.mrk sp.toNat idx0 idxs false := by
  intro d2
  have hw2_len : d2.wsort.length = 2 * c.max_vars := by simp [d2, hsi2.wsort_len]
  refine ⟨hw2_len, m8MinStInv_with_wsort hsi2 hw2_len,
    ⟨hstk.len, hstk.idx0_eq, hstk.bd, hstk.dec, hstk.lvl_le_root, fun j hj => ?_,
      fun hc => by cases hc⟩⟩
  dsimp only [d2]; rw [List.getElem?_set_ne (by omega)]; exact hstk.slot j hj

private theorem m8MinLitDfs_big_push_post {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {d : M8DfsScratch} {idx0 u_idx : Nat} {sp cd steps : BitVec 64}
    {idxs : List Nat} {rsn lit pos newPw : BitVec 32} {R : Mem 64 → Prop} {m_z : Mem 64}
    (hcore : FullOtfsCoreInv c F0 s) (hsi2 : d.Inv c s keepSet)
    (hstk : M8MinStkInv s.core d.wsort d.mrk sp.toNat idx0 idxs true)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hsp_idxs : sp.toNat < idxs.length)
    (hsp1_nat : (sp + 1).toNat = sp.toNat + 1) (hcd1_nat : (cd + 1).toNat = cd.toNat + 1)
    (hsp1_lt : sp.toNat + 1 < c.max_vars) (hcd1_lt : cd.toNat + 1 < c.minDepth)
    (hsteps1 : (steps + 1).toNat = steps.toNat + 1) (hlt_st : steps.toNat < m8MinLitMaxSteps s)
    (hpar_eq : (newPw &&& 0x7FFFFFFF#32).toNat =
      (d.wsort[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat + 1)
    (hpos_nat : pos.toNat = (d.wsort[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
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
    (hno8_u : (d.mrk[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8)
    (h2z : (d.mrk[(lit >>> 1).toNat]?.getD 0#8 &&& 2#8) = 0#8)
    (h4z : (d.mrk[(lit >>> 1).toNat]?.getD 0#8 &&& 4#8) = 0#8)
    (hu_rsns_len : ((lit >>> 1).setWidth 64).toNat < s.core.rsns.length)
    (hur_some : (s.core.rsns[((lit >>> 1).setWidth 64).toNat]'hu_rsns_len == 0xFFFFFFFF#32) =
      false)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32)
    (hlit_eq : lit.toNat = m8RsnLit s.core rsn pos.toNat)
    (hm_z' : (FullMem c ({ d with wsort := (((d.wsort.set (2 * sp.toNat + 1) newPw).set
        (2 * (sp.toNat + 1)) (lit >>> 1)).set (2 * (sp.toNat + 1) + 1)
        0x80000000#32) }.st s) ⋆ R) m_z) :
    M8MinLpInv c s keepSet idx0 R (m8MinLitMaxSteps s - (steps + 1).toNat)
      (sp + 1, cd + 1, steps + 1, ()) m_z := by
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hrsn_u_ne : s.core.rsns[(lit >>> 1).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    rw [← bv_c0_zext32_64 (lit >>> 1), List.getElem?_eq_getElem hu_rsns_len, Option.getD_some]
    c0_grind
  obtain ⟨hsi3, hstk3⟩ := m8MinLit_push_stk hcore hsi2 hstk hi0_lvl hsp_idxs hsp1_lt hpar_eq
    m8_bv32_mask31_hi_eq0 hpos_nat hsz_lt hu_bd_lt hu_idx_lt hu_idx_eq hu_nat_idx hu_lvl_root
    hno8_u h2z h4z hrsn_u_ne hrsn_eq hlit_eq
  exact ⟨by rwa [hsp1_nat], by rwa [hcd1_nat], by omega, rfl, _, idxs ++ [u_idx], hsi3, hm_z',
    by rwa [hsp1_nat]⟩

private theorem m8MinLitDfs_init_lp_entry {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} {keepSet : List Nat} {root_lit : BitVec 32} {idx0 : Nat} {R : Mem 64 → Prop}
    {m1 : Mem 64} (hcore : FullOtfsCoreInv c F0 s)
    (hsi_init : (M8DfsScratch.ofState s).Inv c s keepSet)
    (hmd_pos : 1 ≤ c.minDepth) (hcv_pos : 0 < s.core.cur_vars)
    (hi0 : idx0 < s.core.trail_end)
    (hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2)
    (hi0_lvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hrsn_ne0 : s.core.rsns[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
      0xFFFFFFFF#32)
    (hm1 : (FullMem c ({ M8DfsScratch.ofState s with
        wsort := (s.scratch.wsort.set (BitVec.signExtend 64 (0 : BitVec 32)).toNat
          (root_lit >>> 1)).set (BitVec.signExtend 64 (1 : BitVec 32)).toNat 0#32 }.st s) ⋆
        R) m1) :
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
    (by rw [h0, Nat.sub_zero]), _, [idx0], hsi0, hm1, hstk0⟩

private def m8MinLitDfsBigExpr {V : Ty → Type} {C : List Ty → Type}
    (h pArena pRsns pMark pLvl pWsort pShrinkStk sp cd steps alen cur_vars mv mdepth clvl : V i64)
    (v pword pos rsn : V i32) (check_used : V .bool)
    (B : C [i64, i64, .bool, i64]) (L : C [i64, i64, i64]) : Expr V C [.bool] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  let op32 (c : OpCode [i32, i32] [i32]) (a b : Arg V i32) := Op.mk c (a, b, ())
  .let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun r64 =>
  .let_ (op64 (.add i64) (.var r64.fst) (.imm 3)) fun r3 =>
  .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var r3.fst, .var alen, ())) fun c_a =>
  .jnz (.var c_a.fst) (.jump B (.var sp, .var cd, .imm false, .var steps, ()))
    (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun r64_2 =>
     .let_ (op64 (.add i64) (.var r64_2.fst) (.imm 2)) fun r2 =>
     .let_ (op64 (.mul i64) (.var r2.fst) (.imm 4)) fun off2 =>
     .let_ (op64 (.add i64) (.var pArena) (.var off2.fst)) fun a2 =>
     .load i32 (.var a2.fst) fun sz =>
     .let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var sz, .imm 3, ())) fun c_sz =>
     .jnz (.var c_sz.fst) (.jump B (.var sp, .var cd, .imm false, .var steps, ()))
       (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun r64_3 =>
        .let_ (op64 (.add i64) (.var r64_3.fst) (.imm 3)) fun r3_b =>
        .let_ (Op.mk (.zext 32 64) (.var sz, ())) fun sz64 =>
        .let_ (op64 (.add i64) (.var r3_b.fst) (.var sz64.fst)) fun end_ar =>
        .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var end_ar.fst, .var alen, ())) fun c_ar =>
        .jnz (.var c_ar.fst) (.jump B (.var sp, .var cd, .imm false, .var steps, ()))
          (.group (sig := [[]]) (fun _Jtk => .cons (fun _ =>
             .let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var pos, .var sz, ())) fun c_ps =>
             .jnz (.var c_ps.fst)
               (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun s1 =>
                .let_ (op64 (.shl i64) (.var sp) (.var s1.fst)) fun s2 =>
                .let_ (op64 (.add i64) (.var s2.fst) (.imm 1)) fun s3 =>
                .let_ (op64 (.mul i64) (.var s3.fst) (.imm 4)) fun s4 =>
                .let_ (op64 (.add i64) (.var pWsort) (.var s4.fst)) fun s5 =>
                .let_ (op32 (.and i32) (.var pword) (.imm 2147483648)) fun hi =>
                .let_ (op32 (.add i32) (.var pos) (.imm 1)) fun p1 =>
                .let_ (op32 (.or i32) (.var hi.fst) (.var p1.fst)) fun npw =>
                .store (.var npw.fst) (.var s5.fst)
                  (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun r64_4 =>
                   .let_ (op64 (.add i64) (.var r64_4.fst) (.imm 3)) fun r3_c =>
                   .let_ (Op.mk (.zext 32 64) (.var pos, ())) fun pos64 =>
                   .let_ (op64 (.add i64) (.var r3_c.fst) (.var pos64.fst)) fun lidx =>
                   .let_ (op64 (.mul i64) (.var lidx.fst) (.imm 4)) fun loff =>
                   .let_ (op64 (.add i64) (.var pArena) (.var loff.fst)) fun ladd =>
                   .load i32 (.var ladd.fst) fun lit =>
                   .let_ (Op.mk (.lshr i32) (.var lit, .imm 1, ())) fun u =>
                   .let_ (Op.mk (.zext 32 64) (.var u.fst, ())) fun u64 =>
                   .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                     (.var u64.fst, .var cur_vars, ())) fun c_u =>
                   .jnz (.var c_u.fst) (.jump B (.var sp, .var cd, .imm false, .var steps, ()))
                     (m8MinLitDfsBodyExpr h pRsns pMark pLvl pShrinkStk sp cd steps cur_vars clvl
                       v u.fst check_used B L
                       (.let_ (op64 (.add i64) (.var cd) (.imm 1)) fun cd1 =>
                        .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                          (.var cd1.fst, .var mdepth, ())) fun c_cd =>
                        .jnz (.var c_cd.fst)
                          (.jump B (.var sp, .var cd, .imm false, .var steps, ()))
                          (.let_ (op64 (.add i64) (.var sp) (.imm 1)) fun sp1 =>
                           .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                             (.var sp1.fst, .var mv, ())) fun c_sp =>
                           .jnz (.var c_sp.fst)
                             (.jump B (.var sp, .var cd, .imm false, .var steps, ()))
                             (.let_ (op64 (.add i64) (.var cd) (.imm 1)) fun cd2 =>
                              .let_ (op64 (.add i64) (.var sp) (.imm 1)) fun sp2 =>
                              .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun a1 =>
                              .let_ (op64 (.shl i64) (.var sp2.fst) (.var a1.fst)) fun a2 =>
                              .let_ (op64 (.mul i64) (.var a2.fst) (.imm 4)) fun a3 =>
                              .let_ (op64 (.add i64) (.var pWsort) (.var a3.fst)) fun a4 =>
                              .store (.var u.fst) (.var a4.fst)
                                (.let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun b1 =>
                                 .let_ (op64 (.shl i64) (.var sp2.fst) (.var b1.fst)) fun b2 =>
                                 .let_ (op64 (.add i64) (.var b2.fst) (.imm 1)) fun b3 =>
                                 .let_ (op64 (.mul i64) (.var b3.fst) (.imm 4)) fun b4 =>
                                 .let_ (op64 (.add i64) (.var pWsort) (.var b4.fst)) fun b5 =>
                                 .store (t := i32) (.imm 2147483648) (.var b5.fst)
                                   (.jump L (.var sp2.fst, .var cd2.fst, .var steps, ())))))))))
               (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var sp, .imm 0, ())) fun c_z =>
                .jnz (.var c_z.fst)
                  (.jump B (.var sp, .var cd, .imm true, .var steps, ()))
                  (.let_ (Op.mk (.trunc 32 8) (.imm 2, ())) fun t2 =>
                   .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
                     (.var h, .var v, .var t2.fst, ()) fun _ =>
                   .group (sig := [[i64]]) (fun _Js => .cons (fun cd' =>
                     .let_ (op64 (.sub i64) (.var sp) (.imm 1)) fun spm1 =>
                     .jump L (.var spm1.fst, .var cd'.fst, .var steps, ())) .nil)
                     fun Js => m8MinLitDfsCdExpr cd pword Js.fst))) .nil)
             fun Jtk =>
               .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var pos, .imm 0, ())) fun c_p0 =>
               .jnz (.var c_p0.fst)
                 (.let_ (op64 (.add i64) (.var h) (.imm 600)) fun tk_a =>
                  .load i64 (.var tk_a.fst) fun tk =>
                  .let_ (op64 (.add i64) (.var tk) (.imm 1)) fun tk1 =>
                  .let_ (op64 (.add i64) (.var h) (.imm 600)) fun tk_a2 =>
                  .store (.var tk1.fst) (.var tk_a2.fst) (.jump Jtk.fst ()))
                 (.jump Jtk.fst ()))))

private theorem m8MinLitDfs_big_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur0 : List (List Nat)} {s : FullState} {keepSet : List Nat}
    {d : M8DfsScratch} {idx0 : Nat} {root_lit : BitVec 32} {R : Mem 64 → Prop}
    {Q : Post [.bool]} {X : XPost} {B : Cont [i64, i64, .bool, i64]}
    {L : Cont [i64, i64, i64]} {sp cd steps : Val i64} {idxs : List Nat}
    {v pword pos rsn : Val i32} {check_used : Val .bool} {m' : Mem 64}
    (hMm : Γ.Has "full_min_mark" Spec.minMarkSpec)
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
      d.wsort.length)
    (hsp_idxs : sp.toNat < idxs.length)
    (hsi : d.Inv c s keepSet)
    (hstk : M8MinStkInv s.core d.wsort d.mrk sp.toNat idx0 idxs true)
    (hv_nat : v.toNat = (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2)
    (hv_lt : v.toNat < s.core.cur_vars)
    (_hpw_eq : pword = d.wsort[(sp <<< ((BitVec.signExtend 64
      (1 : BitVec 32)).toNat % 64) + 1).toNat]'hstk_od)
    (_hpos_eq : pos = pword &&& 0x7FFFFFFF#32)
    (hpos_nat : pos.toNat = (d.wsort[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat)
    (hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32)
    (hcov_sp : M8FrameCov s.core d.mrk (idxs[sp.toNat]'hsp_idxs) pos.toNat)
    (hbin_f : ¬ (rsn &&& 0x80000000#32) ≠ 0#32)
    (hm' : (FullMem c (d.st s) ⋆ R) m') :
    wp Γ Q X (m8MinLitDfsBigExpr c.hdr c.pArena c.pReason c.pMark c.pLevel c.pWsort c.pShrinkStk
      sp cd (steps + 1) (BitVec.ofNat 64 s.core.arena_len) (BitVec.ofNat 64 s.core.cur_vars)
      (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 c.minDepth) (BitVec.ofNat 64 s.core.cur_level)
      v pword pos rsn check_used B L) m' := by
  have hlen0 := hcore.1.core_ok
  have hmx := c.hmaxv; have har := c.harena; unfold Ref.dimacsBound at hmx har
  have hcv := hlen0.cur_vars_le; have hal_le := hlen0.arena_len_le
  have hmd_le : c.minDepth ≤ 1000 := fullMinDepthOf_le c.max_vars
  let maxSteps := m8MinLitMaxSteps s
  have hcov_big := hcov_sp; dsimp only [M8FrameCov] at hcov_big
  rcases hcov_big with ⟨_, hif⟩
  simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte] at hif
  have hwf := hw0.arena.refs_wf _ hif.1
  dsimp only [m8MinLitDfsBigExpr]
  c0_hsplit
  · exfalso; have := hwf.1; c0_grind
  · have har2 : (rsn.setWidth 64 + 2).toNat < (d.st s).core.arena.length := by
      rw [bv64_zext32_add2]; dsimp only [M8DfsScratch.st, m8MinLitDfsState]
      have := hwf.1; have := hlen0.arena_len_arr; omega
    let sz := s.core.arena[(rsn.setWidth 64 + 2).toNat]'har2
    have hsz_e : sz.toNat = fullArenaClauseSizeCore s.core rsn.toNat := by
      have hopt : (d.st s).core.arena[(rsn.setWidth 64 + 2).toNat]? =
          s.core.arena[rsn.toNat + 2]? := by
        dsimp only [M8DfsScratch.st, m8MinLitDfsState]; rw [bv64_zext32_add2]
      rw [List.getElem?_eq_getElem har2] at hopt
      exact congrArg (fun o => (o.getD 0#32).toNat) hopt
    c0_hsplit
    · exfalso; have := hwf.2.1; c0_grind
    · c0_hsplit
      · exfalso; have := hwf.2.2.1; have := hwf.2.2.2.1
        have har2_idx : (rsn.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 =
            (rsn.setWidth 64 + 2).toNat := by
          change (rsn.toNat + 2) % 2 ^ 64 = _; rw [bv64_zext32_add2]
          exact Nat.mod_eq_of_lt (by omega)
        simp only [har2_idx] at hc
        change s.core.arena_len % 2 ^ 64 < (rsn.toNat + 3 + sz.toNat) % 2 ^ 64 at hc
        rw [hsz_e, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
      · refine wp_join_group (ts := []) (fun _ m_tk => ∃ ticks2 : BitVec 64,
            { d with ticks := ticks2 }.Inv c s keepSet ∧
            (FullMem c ({ d with ticks := ticks2 }.st s) ⋆ R) m_tk)
          ?_ (fun Jtk hJtk => by
            c0_hsplit
            · c0_hsteps!; exact hJtk () m ⟨d.ticks + 1#64, m8MinStInv_with_ticks hsi, hm⟩
            · exact hJtk () m' ⟨d.ticks, hsi, hm'⟩)
        rintro Jtk ⟨⟩ m_tk ⟨ticks2, hsi2, hm_tk⟩; rw [Blocks.get_here]
        let dt : M8DfsScratch := { d with ticks := ticks2 }
        have hstk_od' : (sp <<< (1 : Nat) + 1).toNat < (dt.st s).scratch.wsort.length := hstk_od
        c0_hsplit
        · have hpos_lt : pos.ult sz = true := by rw [BitVec.ult, decide_eq_true_eq]; c0_grind
          obtain ⟨hpos_lt', hsz_lt, hpar_eq⟩ := m8MinLitDfs_big_pre_facts
            (pword := pword) hlen0 hsp_idxs hwf hsz_e hpos_nat hrsn_eq hbin_f hpos_lt
          let newPw := (pword &&& 0x80000000#32) ||| (pos + 1#32)
          let d2 : M8DfsScratch := { dt with wsort := dt.wsort.set (2 * sp.toNat + 1) newPw }
          obtain ⟨hw2_len, hsi_p, hstk2_drop⟩ :=
            m8MinLitDfs_big_wsort2_inv (newPw := newPw) hsi2 hstk
          have har_lit_bd : (rsn.setWidth 64 + 3 + pos.setWidth 64).toNat <
              (dt.st s).core.arena.length := by
            dsimp only [M8DfsScratch.st, m8MinLitDfsState]
            rw [bv64_zext32_add3_add, hlen0.arena_len_arr]
            have := hwf.2.2.1; have := hwf.2.2.2.1; have := hlen0.arena_len_le
            rw [hsz_e] at hpos_lt'; omega
          let lit := s.core.arena[(rsn.setWidth 64 + 3 + pos.setWidth 64).toNat]'har_lit_bd
          have hlit_eq : lit.toNat = m8RsnLit s.core rsn pos.toNat := by
            dsimp only [m8RsnLit, lit]; simp only [eq_false hbin_f, ↓reduceIte]
            have ha_opt : (dt.st s).core.arena[(rsn.setWidth 64 + 3 + pos.setWidth 64).toNat]? =
                s.core.arena[rsn.toNat + 3 + pos.toNat]? := by
              dsimp only [M8DfsScratch.st, m8MinLitDfsState]; rw [bv64_zext32_add3_add]
            rw [List.getElem?_eq_getElem har_lit_bd] at ha_opt
            exact congrArg (fun o => (o.getD 0#32).toNat) ha_opt
          have hidx_hc : (rsn.toNat + (3 : BitVec 64).toNat + pos.toNat) % 2 ^ 64 =
              (rsn.setWidth 64 + 3 + pos.setWidth 64).toNat := by
            change (rsn.toNat + 3 + pos.toNat) % 2 ^ 64 = _
            rw [bv64_zext32_add3_add]; exact Nat.mod_eq_of_lt (by
              have := hwf.2.2.1; have := hwf.2.2.2.1
              rw [hsz_e] at hpos_lt'; omega)
          c0_hsplit
          · exfalso
            have hlt_2v := hw0.arena.lits_lt _ hif.1 hif.2.1 lit.toNat (by
              rw [hlit_eq]; dsimp only [m8RsnLit]; simp only [eq_false hbin_f, ↓reduceIte]
              exact m8FrameCov_arena_lits_mem hcore hif.1 (by rw [← hsz_e]; exact hpos_lt'))
            simp only [hidx_hc] at hc
            have h_cv_mod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars :=
              Nat.mod_eq_of_lt (by omega)
            rw [h_cv_mod] at hc; change s.core.cur_vars ≤ lit.toNat / 2 at hc; omega
          · rw [m8Dfs_st_wsort_eq dt s (by
                show (sp <<< (1 : Nat) + 1).toNat = 2 * sp.toNat + 1
                change (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat = _
                exact m8_bv64_shl1_add1_toNat (by omega))] at hm
            replace hm : (FullMem c (d2.st s) ⋆ R) m := m8Dfs_mem_wsort_cast' hm (by
              dsimp only [M8DfsScratch.st, m8MinLitDfsState, d2, newPw]; rfl)
            have hu_cv : (lit >>> 1).toNat < s.core.cur_vars := by
              simp only [hidx_hc] at hc
              have h_cv_mod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars :=
                Nat.mod_eq_of_lt (by omega)
              rw [h_cv_mod] at hc; rw [bv32_lshr_1]
              change ¬ s.core.cur_vars ≤ lit.toNat / 2 at hc; omega
            refine m8MinLitDfs_body_wp (d := dt) (d2 := d2) (_pword := pword)
              (newPw := newPw) (u_c0 := _)
              hMm hcore hw0 hrv_root hi0_lvl hno8 hB hL
              hsp_lt hcd_lt hlt_st hsteps1 hdec_n hsp_idxs hsi2 hsi_p rfl rfl hstk
              hstk2_drop hv_nat hpos_nat hpar_eq hsz_lt hrsn_eq hcov_sp hlit_eq
              rfl hu_cv hm
              fun u_idx hu_idx_lt hu_idx_eq hu_bd_lt hu_nat_idx hu_lvl_root
                  hno8_u hmu2 hmu4 hu_rsns_len hrsn_u_ne => by
                c0_hsplit
                · c0_hsteps!; exact hB _ _ ⟨d2, hsi_p, hm, ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                · have hcd_lt' : ((BitVec.ofNat 64 c.minDepth).ule (cd + 1)) = false := by
                    rw [BitVec.ule, decide_eq_false_iff_not]
                    simpa only [BitVec.toNat_ofNat, BitVec.toNat_add,
                      Nat.mod_eq_of_lt (by omega)] using hc
                  c0_hsplit
                  · c0_hsteps!; exact hB _ _ ⟨d2, hsi_p, hm, ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                  · have hsp_ok : ((BitVec.ofNat 64 c.max_vars).ule (sp + 1)) = false := by
                      rw [BitVec.ule, decide_eq_false_iff_not]
                      simpa only [BitVec.toNat_ofNat, BitVec.toNat_add,
                        Nat.mod_eq_of_lt (by omega)] using hc
                    obtain ⟨hcd1_lt, hsp1_nat, hcd1_nat, hsp1_lt, hstk_ev1, hstk_od1⟩ :=
                      m8MinLitDfs_big_push_pre hsp_lt hcd_lt hw2_len hcd_lt' hsp_ok
                    have hstk_ev1' : ((sp + 1) <<< (1 : Nat)).toNat <
                        (d2.st s).scratch.wsort.length := hstk_ev1
                    let d2a : M8DfsScratch := { d2 with
                      wsort := d2.wsort.set (2 * (sp.toNat + 1)) (lit >>> 1) }
                    have hstk_od1' : ((sp + 1) <<< (1 : Nat) + 1).toNat <
                        (d2a.st s).scratch.wsort.length := by
                      dsimp only [M8DfsScratch.st, m8MinLitDfsState, d2a]
                      rw [List.length_set]; exact hstk_od1
                    c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                    rw [m8Dfs_st_wsort_eq d2 s (by
                      change ((sp + 1) <<< ((BitVec.signExtend 64
                        (1 : BitVec 32)).toNat % 64)).toNat = 2 * (sp.toNat + 1)
                      rw [m8_bv64_shl1_toNat (x := sp + 1) (by omega), hsp1_nat])] at hm
                    c0_hsteps!
                    rw [m8Dfs_st_wsort_eq d2a s (by
                      change ((sp + 1) <<< ((BitVec.signExtend 64
                        (1 : BitVec 32)).toNat % 64) + 1).toNat = 2 * (sp.toNat + 1) + 1
                      rw [m8_bv64_shl1_add1_toNat (x := sp + 1) (by omega), hsp1_nat])] at hm
                    have hur_some : (s.core.rsns[((lit >>> 1).setWidth 64).toNat]'hu_rsns_len ==
                        0xFFFFFFFF#32) = false := beq_eq_false_iff_ne.mpr (by
                      simp only [bv_c0_zext32_64]
                      rw [List.getElem?_eq_getElem
                        (by rw [hlen0.rsns_len]; exact Nat.lt_of_lt_of_le hu_bd_lt hcv),
                        Option.getD_some] at hrsn_u_ne
                      exact hrsn_u_ne)
                    exact hL (maxSteps - (steps + 1).toNat) (sp + 1, cd + 1, steps + 1, ()) m hdec_n
                      (m8MinLitDfs_big_push_post hcore hsi2 hstk hi0_lvl hsp_idxs hsp1_nat hcd1_nat
                        hsp1_lt hcd1_lt hsteps1 hlt_st hpar_eq hpos_nat hsz_lt hu_bd_lt hu_idx_lt
                        hu_idx_eq hu_nat_idx hu_lvl_root hno8_u hmu2 hmu4 hu_rsns_len hur_some
                        hrsn_eq hlit_eq hm)
        · have hpos_ge : pos.ult sz = false := by
            rw [BitVec.ult, decide_eq_false_iff_not]; c0_grind
          have hpos_ge' : sz.toNat ≤ pos.toNat := by c0_grind
          c0_hsplit
          · c0_hsteps!
            have hsp0 : sp = 0 := BitVec.eq_of_toNat_eq (congrArg BitVec.toNat hc)
            exact hB _ _ (m8MinLitDfs_big_pop_brk hsi2 hstk hsp_idxs hrv_root hpos_nat hrsn_eq
              hbin_f hsz_e hpos_ge hcov_sp hsp0 hm_tk)
          · have hsp_gt0 : 0 < sp.toNat :=
              Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq h)
            c0_hsteps!; apply wp_call_of_spec; apply hMm
            dsimp only [M8DfsScratch.st] at hm_tk
            refine m8MinLitDfs_pop_state hcore hsi2 hstk hsp_gt0 hsp_idxs hi0_lvl hv_nat hv_lt
              (lim := pos.toNat) (by simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte, ← hsz_e];
                                      exact hpos_ge')
              hcov_sp hm_tk fun k4 m4 hk4 hsi4 hstk4 hm4 => ?_
            refine wp_join_group (ts := [i64]) (fun (cd', _) m_cd =>
                cd'.toNat < c.minDepth ∧ m_cd = m4)
              (fun _ ⟨cd', ⟨⟩⟩ m_cd ⟨hcd', rfl⟩ => by
                rw [Blocks.get_here]; c0_hsteps!
                have hsp_m1 : (sp - 1).toNat = sp.toNat - 1 := by c0_bound
                exact hL (maxSteps - (steps + 1).toNat) (sp - 1, cd', steps + 1, ()) m_cd hdec_n
                  ⟨by rw [hsp_m1]; omega, hcd', hsteps1 ▸ Nat.succ_le_of_lt hlt_st, rfl,
                    { dt with mrk := k4.mrk, min_clr := k4.min_clr,
                              mcl := k4.min_clr_len, mcf := k4.min_clr_full },
                    idxs.take sp.toNat, hsi4, hm4, by rwa [hsp_m1]⟩) ?_
            rintro Jcd hJcd; exact m8MinLitDfs_cd_wp hcd_lt fun cd' hcd' => by
              c0_hsteps!; exact hJcd (cd', ()) m4 ⟨hcd', rfl⟩

public section

theorem full_min_lit_dfs_m8_wp (Γ : Env)
    (hMm : Γ.Has "full_min_mark" Spec.minMarkSpec) :
    ∀ args m Q X, Spec.minLitDfsSpec args m Q X →
      Func.wp Γ full_min_lit_dfs_m8_body args m Q X := by
  rintro ⟨h, root_lit, minimizing, check_used, ⟨⟩⟩ m Q X hsp
  obtain ⟨c, s, ⟨F0, keepSet⟩, R, rfl, _, ⟨hcore, hmin, hrl, hval, hrl_lvl, hno8⟩, hm, hQ⟩ :=
    FullContract.elim hsp
  unfold Func.wp full_min_lit_dfs_m8_body; dsimp only [full_min_lit_dfs_m8_body]
  have hlen0 := hcore.1.core_ok
  have hmx := c.hmaxv; have har := c.harena; unfold Ref.dimacsBound at hmx har
  have hcv := hlen0.cur_vars_le
  have hm_post_false : ∀ (d_f : M8DfsScratch) m_f,
      d_f.Inv c s keepSet → (FullMem c (d_f.st s) ⋆ R) m_f → Q (false, ()) m_f :=
    fun d_f m_f => m8MinLitDfs_false_post hcore hQ
  have hsi_init : (M8DfsScratch.ofState s).Inv c s keepSet :=
    ⟨hlen0.mrk_len, hcore.1.scratch_ok.wsort_len, hlen0.min_clr_len_arr, hlen0.min_clr_len_le,
      fun _ _ => rfl, hmin, fun _ _ h => h, fun _ _ => rfl⟩
  have hrsn_bd : ((root_lit >>> 1).setWidth 64).toNat < s.core.rsns.length := by
    rw [hlen0.rsns_len, bv_c0_zext32_64, bv32_lshr_1]; omega
  c0_hsplit
  · exfalso; c0_grind
  · c0_hsplit
    · exfalso; have := fullMinDepthOf_pos c.max_vars
      have := fullMinDepthOf_le c.max_vars; unfold FullCfg.minDepth at *; c0_grind
    · c0_hsplit
      · c0_hsteps!; exact hm_post_false (M8DfsScratch.ofState s) m hsi_init hm
      · have hrl_lvl_bd : ((root_lit >>> 1).setWidth 64).toNat < s.core.lvl.length := by
          rw [hlen0.lvl_len, bv_c0_zext32_64, bv32_lshr_1]; omega
        have hrsn_some :
            (s.core.rsns[((root_lit >>> 1).setWidth 64).toNat]'hrsn_bd == 0xFFFFFFFF#32) =
              false := beq_eq_false_iff_ne.mpr (by c0_grind)
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun _ m0 => m0 = m) ?_ ?_
        · rintro _ ⟨⟩ m0 rfl; rw [Blocks.get_here]
          have hmd_pos := fullMinDepthOf_pos c.max_vars
          have hcv_pos : 0 < s.core.cur_vars := by omega
          have hwl := hcore.1.scratch_ok.wsort_len
          have hw0_bd : (BitVec.signExtend 64 (0 : BitVec 32)).toNat < s.scratch.wsort.length := by
            show 0 < s.scratch.wsort.length; omega
          c0_hsteps_nogrp
          have hw1_bd : (BitVec.signExtend 64 (1 : BitVec 32)).toNat <
              (s.scratch.wsort.set (BitVec.signExtend 64 (0 : BitVec 32)).toNat
                (root_lit >>> 1)).length := by
            show 1 < _; rw [List.length_set]; omega
          c0_hsteps_nogrp
          change (FullMem c ({ M8DfsScratch.ofState s with
            wsort := (s.scratch.wsort.set (BitVec.signExtend 64 (0 : BitVec 32)).toNat
              (root_lit >>> 1)).set (BitVec.signExtend 64 (1 : BitVec 32)).toNat 0#32 }.st s) ⋆
            R) m at hm
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
          · rintro B L n ⟨sp, cd, steps, ⟨⟩⟩ m' hB hL ⟨hsp_lt, hcd_lt, hsteps_le, rfl, d,
                idxs, hsi, hm', hstk⟩
            clear hm
            rw [Blocks.get_here]; c0_hsplit
            · have hms_eq := m8MinLit_maxSteps_toNat hlen0.arena_len_le hcv
              have hlt_st : steps.toNat < maxSteps := by
                dsimp only [maxSteps, m8MinLitMaxSteps]; c0_grind
              have hsteps1 : (steps + 1).toNat = steps.toNat + 1 := by c0_bound
              have hdec_n : maxSteps - (steps + 1).toNat < maxSteps - steps.toNat := by omega
              have hmd_le : c.minDepth ≤ 1000 := fullMinDepthOf_le c.max_vars
              have hstk_ev :
                  (sp <<< (1 : Nat)).toNat < (d.st s).scratch.wsort.length := by
                dsimp only [M8DfsScratch.st, m8MinLitDfsState]
                change (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
                  d.wsort.length
                rw [m8_bv64_shl1_toNat (by omega), hsi.wsort_len]; omega
              have hstk_od :
                  (sp <<< (1 : Nat) + 1).toNat < (d.st s).scratch.wsort.length := by
                dsimp only [M8DfsScratch.st, m8MinLitDfsState]
                change (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat <
                  d.wsort.length
                rw [m8_bv64_shl1_add1_toNat (by omega), hsi.wsort_len]; omega
              have hsp_idxs : sp.toNat < idxs.length := by rw [hstk.len]; omega
              let v := d.wsort[(sp <<< (1 : Nat)).toNat]'hstk_ev
              let pword := d.wsort[(sp <<< (1 : Nat) + 1).toNat]'hstk_od
              let pos := pword &&& 0x7FFFFFFF#32
              have hv_nat : v.toNat =
                  (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
                have hslot := (hstk.slot sp.toNat hsp_idxs).1
                rw [List.getElem?_eq_getElem (by rw [hsi.wsort_len]; omega), Option.getD_some]
                  at hslot
                dsimp only [v]
                change (d.wsort[(sp <<< ((BitVec.signExtend 64
                  (1 : BitVec 32)).toNat % 64)).toNat]'hstk_ev).toNat = _
                simp only [m8_bv64_shl1_toNat (x := sp) (by omega)]; exact hslot
              have hv_lt : v.toNat < s.core.cur_vars := by
                rw [hv_nat]; have := hw0.trail_lits_lt _ (hstk.bd sp.toNat hsp_idxs); omega
              have hpos_nat : pos.toNat =
                  (d.wsort[2 * sp.toNat + 1]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat := by
                dsimp only [pos, pword]
                change ((d.wsort[(sp <<< ((BitVec.signExtend 64
                  (1 : BitVec 32)).toNat % 64) + 1).toNat]'hstk_od) &&& 0x7FFFFFFF#32).toNat = _
                simp only [m8_bv64_shl1_add1_toNat (x := sp) (by omega)]
                rw [List.getElem?_eq_getElem (by rw [hsi.wsort_len]; omega), Option.getD_some]
              c0_hsplit
              · exfalso; c0_grind
              · have hv_rsns : (v.setWidth 64).toNat < (d.st s).core.rsns.length := by
                  dsimp only [M8DfsScratch.st, m8MinLitDfsState]
                  rw [hlen0.rsns_len, bv_c0_zext32_64]; omega
                let rsn := s.core.rsns[(v.setWidth 64).toNat]'hv_rsns
                have hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
                    0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
                  have hvw := bv_c0_zext32_64 v; dsimp only [rsn]; simp only [hvw, ← hv_nat]
                  rw [List.getElem?_eq_getElem (by rw [hlen0.rsns_len]; omega), Option.getD_some]
                have hcov_sp := (hstk.cov rfl sp.toNat hsp_idxs).2
                have hilen := hstk.len
                simp only [show sp.toNat + 1 = idxs.length by omega, ↓reduceIte, ← hpos_nat]
                  at hcov_sp
                c0_hsplit
                · exfalso; dsimp only [M8FrameCov] at hcov_sp
                  have : rsn = 0xFFFFFFFF#32 := by c0_grind
                  exact hcov_sp.1 (hrsn_eq.symm.trans this)
                · c0_hsplit
                  · have hbin' : (rsn &&& 0x80000000#32) ≠ 0#32 := by c0_bv_bit_grind
                    exact m8MinLitDfs_bin_wp hMm hcore hw0 hrv_root hi0_lvl hno8 hB hL hsp_lt
                      hcd_lt hlt_st hsteps1 hdec_n hstk_od hsp_idxs hsi hstk hv_nat hv_lt
                      rfl rfl hpos_nat hrsn_eq hcov_sp hbin' hm'
                  · have hbin_f : ¬ (rsn &&& 0x80000000#32) ≠ 0#32 := by c0_bv_bit_grind
                    exact m8MinLitDfs_big_wp hMm hcore hw0 hrv_root hi0_lvl hno8 hB hL hsp_lt
                      hcd_lt hlt_st hsteps1 hdec_n hstk_od hsp_idxs hsi hstk hv_nat hv_lt
                      rfl rfl hpos_nat hrsn_eq hcov_sp hbin_f hm'
            · c0_hsteps!; exact hB _ _ ⟨d, hsi, hm', hsp_lt, idxs,
                ⟨hstk.len, hstk.idx0_eq, hstk.bd, hstk.dec, hstk.lvl_le_root,
                  fun j hj => hstk.slot j hj, fun hc => by cases hc⟩⟩
          · intro B L hB hL; c0_hsteps!; exact hL maxSteps (0#64, 0#64, 0#64, ()) m
              (m8MinLitDfs_init_lp_entry hcore hsi_init hmd_pos hcv_pos hi0 hrv_root hi0_lvl
                hrsn_ne0 hm)
        · rintro Jinit hJinit
          c0_hsplit
          · c0_hsplit
            · c0_hsplit
              · have hrl_lt1 : ((root_lit >>> 1).setWidth 64).toNat < s.core.lvl.length := by
                  rw [hlen0.lvl_len, bv_c0_zext32_64, bv32_lshr_1]; omega
                have hrl_lt2 : root_lit.toNat / 2 < s.core.lvl.length := by
                  rw [hlen0.lvl_len]; omega
                have hrl_cv' : (s.core.lvl[root_lit.toNat / 2]'hrl_lt2).toNat <
                    s.core.cur_vars := by c0_grind
                c0_hsplit
                · have hrl_ss : ((s.core.lvl[((root_lit >>> 1).setWidth 64).toNat]'
                      hrl_lt1).setWidth 64).toNat < s.scratch.shrink_stk.length := by
                    have h_eq : s.core.lvl[((root_lit >>> 1).setWidth 64).toNat]?.getD 0#32 =
                        s.core.lvl[root_lit.toNat / 2]?.getD 0#32 := by
                      rw [bv_c0_zext32_64, bv32_lshr_1]
                    rw [List.getElem?_eq_getElem hrl_lt1, List.getElem?_eq_getElem hrl_lt2,
                      Option.getD_some, Option.getD_some] at h_eq
                    rw [hcore.1.scratch_ok.shrink_stk_len, bv_c0_zext32_64, h_eq]
                    exact Nat.lt_of_lt_of_le hrl_cv' hcv
                  c0_hsplit
                  · c0_hsteps!; exact hm_post_false (M8DfsScratch.ofState s) m hsi_init hm
                  · c0_hsteps!; exact hJinit () m rfl
                · c0_hsteps!; exact hJinit () m rfl
              · c0_hsteps!; exact hJinit () m rfl
            · c0_hsteps!; exact hJinit () m rfl
          · c0_hsteps!; exact hJinit () m rfl

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize
