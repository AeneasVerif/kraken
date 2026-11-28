/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Dense.WpDenseProp
public import LeanQbe.T.Examples.Kissat.Src.Dense
import LeanQbe.T.Logic.ControlComb

/-!
# Flat-Env WP Proofs for Dense Unit Flushing
(`full_dense_prop_unit_m7`, `full_dense_flush_units_m7`)

Proves `Spec.fullDensePropUnitSpec` and `Spec.fullDenseFlushUnitsSpec` directly on
`CanonicalEnv` without legacy imports (`0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Dense

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Dense
open scoped FullArenaTactics

local macro "dr_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Pure Helpers for Unit Propagation & Flushing -/

private def FuPres (s s' : FullState) : Prop :=
  s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.arena_len = s.core.arena_len ∧
  s'.core.fuel = s.core.fuel ∧
  fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.red_refs = s.scratch.red_refs ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

private theorem fu_pres_refl (s : FullState) : FuPres s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem fu_pres_trans {s0 s1 s2 : FullState}
    (h1 : FuPres s0 s1) (h2 : FuPres s1 s2) : FuPres s0 s2 := by
  rcases h1 with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
  rcases h2 with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8, b9.trans a9, b10.trans a10⟩

private theorem fu_close_q_true {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sF : FullState} {R : Mem 64 → Prop} {mF : Mem 64} {Q : Post [.bool]}
    (hinvF : FullDenseInvW c F0 F_cur sF) (hpresF : DensePropPres s sF)
    (hredF : sF.scratch.red_refs = s.scratch.red_refs) (hmF : (FullMem c sF ⋆ R) mF)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (true, ()) mF := by
  rcases hpresF with ⟨p1, p2, p3, -, p5, p6, -, -, p9, p10, p11, p12, -⟩
  exact hQ true sF mF hinvF p1 p2 p3 p5 p6 hredF p9 p10 p11 p12 (by simp) hmF

private theorem fu_close_q_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sF : FullState} {R : Mem 64 → Prop} {mF : Mem 64} {Q : Post [.bool]}
    (hinvF : FullDenseInvW c F0 F_cur sF) (hpresF : DensePropPres s sF)
    (hredF : sF.scratch.red_refs = s.scratch.red_refs) (hunsat : F0.Unsat)
    (hmF : (FullMem c sF ⋆ R) mF)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (false, ()) mF := by
  rcases hpresF with ⟨p1, p2, p3, -, p5, p6, -, -, p9, p10, p11, p12, -⟩
  exact hQ false sF mF hinvF p1 p2 p3 p5 p6 hredF p9 p10 p11 p12 (fun _ => hunsat) hmF

private theorem fu_inv_inconsistent {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (hu : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } :=
  dp_inv_set_confl h hu s.core.confl_type s.core.confl_ref s.core.confl_lit0 s.core.confl_lit1

private theorem fu_val_one_of_sle_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars)
    (hb : l < k.vals.length)
    (hf : (BitVec.signExtend 32 (k.vals[l]'hb)).sle 0#32 = false) :
    k.vals[l]?.getD 0#8 = 1#8 := by
  rw [List.getElem?_eq_getElem hb]
  rcases dp_val_mem hw hl hb with hv | hv | hv <;> rw [hv] at hf ⊢
  · revert hf; decide
  · rfl
  · revert hf; decide

private theorem fu_xor_xor_self (lit : BitVec 32) : (lit ^^^ 1#32) ^^^ 1#32 = lit := by
  rw [BitVec.xor_assoc, show (1#32 ^^^ 1#32) = 0#32 by decide, BitVec.xor_zero]

private theorem fu_bv64_add1_eq {p : BitVec 64} (h : p.toNat + 1 < 2 ^ 64) :
    (p + 1#64).toNat = p.toNat + 1 := by
  have h1 : 1 < 2 ^ 64 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h]

private theorem fu_unit_lt_of_not_le {c : FullCfg} {k : FullCoreState}
    (hlk : FullCoreState.LengthsOk c k) (hcv : 2 * k.cur_vars < 2 ^ 64) (u : BitVec 32)
    (hhc : ¬2 * (k.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ u.toNat) :
    u.toNat < 2 * k.cur_vars ∧ u.toNat < k.vals.length := by
  have hcv64 : k.cur_vars < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt hcv] at hhc
  have hu := Nat.lt_of_not_le hhc
  have := hlk.vals_len; have := hlk.cur_vars_le
  exact ⟨hu, by omega⟩

private theorem fu_unit_wvec_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) (u : BitVec 32)
    (hu_lt : u.toNat < 2 * s.core.cur_vars) :
    (BitVec.setWidth 64 u <<< 1#64).toNat = 2 * u.toNat ∧
    (BitVec.setWidth 64 u <<< 1#64).toNat < s.core.wvec.length ∧
    (BitVec.setWidth 64 u <<< 1#64 + 1#64).toNat = 2 * u.toNat + 1 ∧
    (BitVec.setWidth 64 u <<< 1#64 + 1#64).toNat < s.core.wvec.length ∧
    2 * u.toNat % 2 ^ 64 < s.core.wvec.length ∧
    (2 * u.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s.core.wvec.length := by
  have h := dp_lit_wvec_bounds hinv (u ^^^ 1#32) (by rw [fu_xor_xor_self]; exact hu_lt)
  simp only [fu_xor_xor_self, dp_not_not_lit] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    by simpa only [show ((1#64 : BitVec 64)).toNat = BitVec.toNat (1 : BitVec 64) from rfl]
      using h.2.2.2.2.2⟩

private theorem fu_unit_end_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) (u : BitVec 32)
    (hu_lt : u.toNat < 2 * s.core.cur_vars)
    {h2u_shl : (BitVec.setWidth 64 u <<< 1#64).toNat < s.core.wvec.length}
    {h2u_shl1 : (BitVec.setWidth 64 u <<< 1#64 + 1#64).toNat < s.core.wvec.length}
    {hm0 : 2 * u.toNat % 2 ^ 64 < s.core.wvec.length}
    {hm1 : (2 * u.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s.core.wvec.length} :
    let off := s.core.wvec[(BitVec.setWidth 64 u <<< 1#64).toNat]'h2u_shl
    let sz := s.core.wvec[(BitVec.setWidth 64 u <<< 1#64 + 1#64).toNat]'h2u_shl1
    let end_off : BitVec 64 := BitVec.setWidth 64 off + BitVec.setWidth 64 sz
    off.toNat = fullWatchOffCore s.core u.toNat ∧
    sz.toNat = fullWatchSizeCore s.core u.toNat ∧
    end_off.toNat = off.toNat + sz.toNat ∧ end_off.toNat ≤ c.wcap ∧
    ((s.core.wvec[2 * u.toNat % 2 ^ 64]'hm0).toNat +
      (s.core.wvec[(2 * u.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'hm1).toNat) % 2 ^ 64 =
      off.toNat + sz.toNat := by
  obtain ⟨_, _, _, _, hm0', hm1'⟩ :=
    dp_lit_wvec_bounds hinv (u ^^^ 1#32) (by rw [fu_xor_xor_self]; exact hu_lt)
  have h := dp_lit_end_eq hinv (u ^^^ 1#32) (by rw [fu_xor_xor_self]; exact hu_lt)
    (h2nl_shl := by rw [fu_xor_xor_self]; exact h2u_shl)
    (h2nl_shl1 := by rw [fu_xor_xor_self]; exact h2u_shl1) (hm0 := hm0') (hm1 := hm1')
  simp only [fu_xor_xor_self, dp_not_not_lit] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by
    simpa only [show ((1#64 : BitVec 64)).toNat = BitVec.toNat (1 : BitVec 64) from rfl] using
      h.2.2.2.2.2.trans h.2.2.1⟩

private theorem fu_occ_unass0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {cref szc : Nat} (hcr_ref : cref ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k cref = false)
    (hsz_c : szc = fullArenaClauseSizeCore k cref) (hbd_c : cref + 3 + szc ≤ k.arena.length)
    {sat : Bool} {ul : BitVec 32} (hsf : sat = false)
    (h79 : sat = true ∨
      (sat = false ∧ (0#32 : BitVec 32) = 0#32 ∧ DpOccScanInv k cref szc hsz_c hbd_c
        0#32 ul szc (le_refl _)) ∨
      (sat = false ∧ (0#32 : BitVec 32) = 1#32 ∧ DpOccScanInv k cref szc hsz_c hbd_c
        1#32 ul szc (le_refl _)) ∨
      (sat = false ∧ (0#32 : BitVec 32) ≠ 0#32 ∧ (0#32 : BitVec 32) ≠ 1#32)) :
    (cnfOfClauses F_cur).Unsat := by
  have h0 : DpOccScanInv k cref szc hsz_c hbd_c 0#32 ul szc (le_refl _) := by
    rcases h79 with h | ⟨-, -, hs⟩ | ⟨-, h1, -⟩ | ⟨-, hn0, -⟩
    · rw [hsf] at h; cases h
    · exact hs
    · cases h1
    · exact absurd rfl hn0
  rcases h0 with ⟨-, hall⟩ | ⟨h1, -⟩
  · exact dp_occ_all_false_unsat hw hcl0 hcr_ref hng hsz_c hbd_c hall
  · cases h1

private theorem fu_occ_unass1_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {cref szc : Nat} (hcr_ref : cref ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k cref = false)
    (hsz_c : szc = fullArenaClauseSizeCore k cref) (hbd_c : cref + 3 + szc ≤ k.arena.length)
    {sat : Bool} {ul : BitVec 32} (hsf : sat = false)
    (h79 : sat = true ∨
      (sat = false ∧ (1#32 : BitVec 32) = 0#32 ∧ DpOccScanInv k cref szc hsz_c hbd_c
        0#32 ul szc (le_refl _)) ∨
      (sat = false ∧ (1#32 : BitVec 32) = 1#32 ∧ DpOccScanInv k cref szc hsz_c hbd_c
        1#32 ul szc (le_refl _)) ∨
      (sat = false ∧ (1#32 : BitVec 32) ≠ 0#32 ∧ (1#32 : BitVec 32) ≠ 1#32)) :
    ul.toNat < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat]) := by
  have h1 : DpOccScanInv k cref szc hsz_c hbd_c 1#32 ul szc (le_refl _) := by
    rcases h79 with h | ⟨-, h0, -⟩ | ⟨-, -, hs⟩ | ⟨-, -, hn1⟩
    · rw [hsf] at h; cases h
    · cases h0
    · exact hs
    · exact absurd rfl hn1
  rcases h1 with ⟨h01, -⟩ | ⟨-, q0, hq0, heq0, hv0, hall⟩
  · cases h01
  · exact dp_occ_unit_entails hw hcl0 hcr_ref hng hsz_c hbd_c hq0 heq0 hv0 hall

private theorem fu_addUnit_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} (hinvL : FullDenseInvW c F0 F_cur sL) (hpresL : DensePropPres s sL)
    (hredL : sL.scratch.red_refs = s.scratch.red_refs)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' unfl' inc' : BitVec 64} {phases' : List (BitVec 8)}
    {ta' ba' : BitVec 64} {pt' pb' : List (BitVec 8)} {hp' ps' : List (BitVec 32)} {hl' : Nat}
    {qsi' qss' : BitVec 64}
    (sA : FullState)
    (hsA : sA = {
      core := { sL.core with
        unassigned := unass', unflushed := unfl', trail_end := te', propagated := prop',
        cur_level := cl', inconsistent := inc', vals := vals', flags := flags',
        lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp' },
      scratch := { sL.scratch with
        heap_len := hl', q_search_idx := qsi', q_search_stamp := qss',
        target_assigned := ta', best_assigned := ba', phases := phases',
        phases_target := pt', phases_best := pb', heap := hp', pos := ps' } })
    (hlkA : FullState.LengthsOk c sA) (hwA : FullWitnessInv c F0 F_cur sA.core) (hclA : cl' = 0) :
    FullDenseInvW c F0 F_cur sA ∧ DensePropPres s sA ∧
      sA.scratch.red_refs = s.scratch.red_refs := by
  subst hsA
  have hinvA := fullDenseInvW_of_addUnit hinvL hlkA hwA hclA rfl rfl rfl rfl rfl rfl rfl rfl
  exact ⟨hinvA, dp_pres_trans hpresL (dp_pres_refl sL), hredL⟩

private theorem fu_bin_addUnit_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sL : FullState} {R : Mem 64 → Prop} {mL : Mem 64}
    {Q : Post [.bool]} {X : XPost} {not_unit other : BitVec 32}
    {p : BitVec 64} {end1 : Nat}
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hinvL : FullDenseInvW c F0 F_cur sL) (hpresL : DensePropPres s sL)
    (hredL : sL.scratch.red_refs = s.scratch.red_refs)
    (hmL : (FullMem c sL ⋆ R) mL) (hoth_lt : other.toNat < 2 * sL.core.cur_vars)
    (hent_oth : (cnfOfClauses F_cur).EntailsClause (cnfClause [other.toNat]))
    (hslice_n' : DenseWatchSliceOk F_cur sL.core not_unit.toNat
      (p + 1#64).toNat (end1 - (p + 1#64).toNat))
    (hp1_eq : (p + 1#64).toNat = p.toNat + 1) (hp1_le : p.toNat + 1 ≤ end1)
    {L40 : Cont [i64]}
    (hLp : ∀ (ys : Tup Val [i64]) (m' : Mem 64),
      end1 - ys.fst.toNat < end1 - p.toNat →
      (∃ sL', FullDenseInvW c F0 F_cur sL' ∧ DensePropPres s sL' ∧
        sL'.scratch.red_refs = s.scratch.red_refs ∧ ys.fst.toNat ≤ end1 ∧
        DenseWatchSliceOk F_cur sL'.core not_unit.toNat ys.fst.toNat (end1 - ys.fst.toNat) ∧
        (FullMem c sL' ⋆ R) m') → L40 ys m')
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    let args : Tup (Arg Val) [i64, i32] := (Arg.var c.hdr, Arg.var other, ())
    let jArgs : Tup (Arg Val) [i64] := (Arg.var (p + 1#64), ())
    let rFalse : Tup (Arg Val) [.bool] := (Arg.imm false, ())
    wp Γ Q X (Expr.call "full_add_unit" args fun (ok : Tup Val [.bool]) =>
      Expr.jnz (Arg.var ok.1) (Expr.jump L40 jArgs) (Expr.ret rFalse)) mL := by
  dr_call hAddUnit
  refine ⟨c, F0, F_cur, sL, R, rfl, hinvL.1, hinvL.2.1, fun _ => hent_oth, hmL,
    fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc' phases'
      ta' ba' pt' pb' hp' ps' hl' qsi' qss' mA hlkA hwA hclA hf _ hmA => ?_⟩
  obtain ⟨hinvA, hpresA, hredA⟩ := fu_addUnit_step hinvL hpresL hredL _ rfl hlkA hwA hclA
  c0_hstraight; c0_hsplit
  · c0_hsteps_nogrp
    exact hLp (p + 1#64, ()) mA (by dsimp only; rw [hp1_eq]; omega)
      ⟨_, hinvA, hpresA, hredA, by rw [hp1_eq]; exact hp1_le,
        dp_slice_mono hslice_n' rfl rfl rfl, hmA⟩
  · have hok_f : ok = false := by
      first | exact (by assumption) | exact Bool.eq_false_iff.mpr (by assumption)
    c0_hsteps_nogrp
    exact fu_close_q_false hinvA hpresA hredA (hf hoth_lt hok_f).1 hmA hQ

private theorem fu_occ_addUnit_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sG : FullState} {R : Mem 64 → Prop} {mG : Mem 64}
    {Q : Post [.bool]} {X : XPost} {lit ul : BitVec 32} {p2_nat rem2 : Nat}
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hinvG : FullDenseInvW c F0 F_cur sG) (hpresG : DensePropPres s sG)
    (hredG : sG.scratch.red_refs = s.scratch.red_refs) (hmG : (FullMem c sG ⋆ R) mG)
    (hlt_u : ul.toNat < 2 * sG.core.cur_vars)
    (hent_u : (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat]))
    (hsliceG : DenseWatchSliceOk F_cur sG.core lit.toNat p2_nat rem2)
    {L73 : Cont []}
    (hL73 : ∀ (xs : Tup Val []) (m : Mem 64),
      (∃ s73, FullDenseInvW c F0 F_cur s73 ∧ DensePropPres s s73 ∧
        s73.scratch.red_refs = s.scratch.red_refs ∧
        DenseWatchSliceOk F_cur s73.core lit.toNat p2_nat rem2 ∧
        (FullMem c s73 ⋆ R) m) → L73 xs m)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.sim_sig = s.scratch.sim_sig →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    let args : Tup (Arg Val) [i64, i32] := (Arg.var c.hdr, Arg.var ul, ())
    let jNil : Tup (Arg Val) [] := ()
    let rFalse : Tup (Arg Val) [.bool] := (Arg.imm false, ())
    wp Γ Q X (Expr.call "full_add_unit" args fun (ok : Tup Val [.bool]) =>
      Expr.jnz (Arg.var ok.1) (Expr.jump L73 jNil) (Expr.ret rFalse)) mG := by
  dr_call hAddUnit
  refine ⟨c, F0, F_cur, sG, R, rfl, hinvG.1, hinvG.2.1, fun _ => hent_u, hmG,
    fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc' phases'
      ta' ba' pt' pb' hp' ps' hl' qsi' qss' mA hlkA hwA hclA hf _ hmA => ?_⟩
  obtain ⟨hinvA, hpresA, hredA⟩ := fu_addUnit_step hinvG hpresG hredG _ rfl hlkA hwA hclA
  c0_hstraight; c0_hsplit
  · c0_hsteps_nogrp
    exact hL73 () mA ⟨_, hinvA, hpresA, hredA, dp_slice_mono hsliceG rfl rfl rfl, hmA⟩
  · have hok_f : ok = false := by
      first | exact (by assumption) | exact Bool.eq_false_iff.mpr (by assumption)
    c0_hsteps_nogrp
    exact fu_close_q_false hinvA hpresA hredA (hf hlt_u hok_f).1 hmA hQ

/-! ## 2. `full_dense_prop_unit_m7_wp` (`Spec.fullDensePropUnitSpec`) -/

theorem full_dense_prop_unit_m7_wp (Γ : Env)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (a : Tup Val [i64, i32]) (m : Mem 64) (Q : Post [.bool]) (X : XPost)
    (hPre : Spec.fullDensePropUnitSpec a m Q X) :
    Func.wp Γ full_dense_prop_unit_m7_body a m Q X := by
  rcases a with ⟨h, unit, ⟨⟩⟩
  rcases hPre with ⟨c, F0, F_cur, s, R, rfl, hinv, hm, hQ⟩
  have hlk := hinv.1.core_ok
  have hw := hinv.2.1
  have hcl0 := hinv.2.2.2.2.2.1
  have hcv_lt : 2 * s.core.cur_vars < 2 ^ 64 := by
    have := c.hmaxv; unfold dimacsBound at this; have := hlk.cur_vars_le; omega
  have hcv_shl : (BitVec.ofNat 64 s.core.cur_vars <<< 1#64).toNat = 2 * s.core.cur_vars :=
    dp_bv64_shl1_nat _ hcv_lt
  c0_hstraight; c0_hsplit
  · c0_hsteps_nogrp
    exact fu_close_q_true hinv (dp_pres_refl s) rfl hm hQ
  · obtain ⟨hu_lt, hu_bd⟩ := fu_unit_lt_of_not_le hlk hcv_lt unit (by assumption)
    c0_hstraight; c0_hsplit
    · c0_hsteps_nogrp
      exact fu_close_q_true hinv (dp_pres_refl s) rfl hm hQ
    · have hu_one : s.core.vals[unit.toNat]?.getD 0#8 = 1#8 := by
        have hsf : (BitVec.signExtend 32 (s.core.vals[unit.toNat]'hu_bd)).sle 0#32 = false := by
          assumption
        exact fu_val_one_of_sle_false hw hu_lt hu_bd hsf
      have hunit_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat]) :=
        dense_vals_true_entails hw hcl0 hu_lt hu_one
      let not_unit : BitVec 32 := unit ^^^ 1#32
      have hnot_lt : not_unit.toNat < 2 * s.core.cur_vars := by
        apply dp_not_lit_lt; rw [fu_xor_xor_self]; exact hu_lt
      obtain ⟨hshl_eq, h2nl_shl, hshl1_eq, h2nl_shl1, hm0_bd, hm1_bd⟩ :=
        dp_lit_wvec_bounds hinv unit hnot_lt
      c0_hstraight
      let off1 := s.core.wvec[(BitVec.setWidth 64 not_unit <<< 1#64).toNat]'h2nl_shl
      let sz1 := s.core.wvec[(BitVec.setWidth 64 not_unit <<< 1#64 + 1#64).toNat]'h2nl_shl1
      let end1 : BitVec 64 := BitVec.setWidth 64 off1 + BitVec.setWidth 64 sz1
      let end1n : Nat := off1.toNat + sz1.toNat
      obtain ⟨hoff1_eq, hsz1_eq, hend1_nat, hend1_le, _, hend1_mod⟩ :=
        dp_lit_end_eq hinv unit hnot_lt (hm0 := hm0_bd) (hm1 := hm1_bd)
      have hend1_bv : end1.toNat = end1n := hend1_nat
      have hend1n_le : end1n ≤ c.wcap := by
        dsimp only [end1n, off1, sz1]; rw [← hend1_nat]; exact hend1_le
      have hend1_mod' : (s.core.wvec[2 * (BitVec.toNat unit ^^^ 1) % 2 ^ 64].toNat +
          s.core.wvec[(2 * (BitVec.toNat unit ^^^ 1) +
            BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat) % 2 ^ 64 = end1n := by
        simpa only [show ((1#64 : BitVec 64)).toNat = BitVec.toNat (1 : BitVec 64) from rfl] using
          hend1_mod.trans hend1_nat
      have hdw0 := dp_dense_watches hinv
      have hwcap_lt : c.wcap < 2 ^ 31 := by have := c.hwcap; unfold dimacsBound at this; omega
      refine wp_join_group (ts := [i64])
        (fun _ mP2 => ∃ sP2, FullDenseInvW c F0 F_cur sP2 ∧ DensePropPres s sP2 ∧
          sP2.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sP2 ⋆ R) mP2)
        (fun _ _ mP2 ⟨sP2, hinvP2, hpresP2, hredP2, hmP2⟩ => by
          have hlk2 := hinvP2.1.core_ok
          have hw2 := hinvP2.2.1
          have hcv2_lt : 2 * sP2.core.cur_vars < 2 ^ 64 := by
            have := c.hmaxv; unfold dimacsBound at this; have := hlk2.cur_vars_le; omega
          have hu2_lt : unit.toNat < 2 * sP2.core.cur_vars := by rw [hpresP2.1]; exact hu_lt
          obtain ⟨hshl2_eq, h2u_shl, hshl21_eq, h2u_shl1, hm20_bd, hm21_bd⟩ :=
            fu_unit_wvec_bounds hinvP2 unit hu2_lt
          c0_hstraight
          let off2 := sP2.core.wvec[(BitVec.setWidth 64 unit <<< 1#64).toNat]'h2u_shl
          let sz2 := sP2.core.wvec[(BitVec.setWidth 64 unit <<< 1#64 + 1#64).toNat]'h2u_shl1
          let end2 : BitVec 64 := BitVec.setWidth 64 off2 + BitVec.setWidth 64 sz2
          let end2n : Nat := off2.toNat + sz2.toNat
          obtain ⟨hoff2_eq, hsz2_eq, hend2_nat, hend2_le, hend2_mod⟩ :=
            fu_unit_end_eq hinvP2 unit hu2_lt (hm0 := hm20_bd) (hm1 := hm21_bd)
          have hend2_bv : end2.toNat = end2n := hend2_nat
          have hend2n_le : end2n ≤ c.wcap := by
            dsimp only [end2n, off2, sz2]; rw [← hend2_nat]; exact hend2_le
          have hend2_mod' : (sP2.core.wvec[2 * unit.toNat % 2 ^ 64].toNat +
              sP2.core.wvec[(2 * unit.toNat +
                BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat) % 2 ^ 64 = end2n := hend2_mod
          have hdw2 := dp_dense_watches hinvP2
          refine wp_join_group (ts := [i64])
            (fun _ mF => ∃ sF, FullDenseInvW c F0 F_cur sF ∧ DensePropPres s sF ∧
              sF.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sF ⋆ R) mF)
            (fun _ _ mF ⟨sF, hinvF, hpresF, hredF, hmF⟩ => by
              c0_hsteps_nogrp; exact fu_close_q_true hinvF hpresF hredF hmF hQ) ?_
          intro L58 hL58
          refine wp_loop_inv (ts := [i64])
            (fun (p, _) mL => ∃ sL, FullDenseInvW c F0 F_cur sL ∧ DensePropPres s sL ∧
              sL.scratch.red_refs = s.scratch.red_refs ∧ p.toNat ≤ end2n ∧
              DenseWatchSliceOk F_cur sL.core unit.toNat p.toNat (end2n - p.toNat) ∧
              (FullMem c sL ⋆ R) mL)
            (fun (p, _) _ => end2n - p.toNat)
            (fun L59 hL59 => by
              c0_hsteps_nogrp
              have hslice0 : DenseWatchSliceOk F_cur sP2.core unit.toNat
                  (BitVec.setWidth 64 off2).toNat
                  (end2n - (BitVec.setWidth 64 off2).toNat) := by
                rw [dense_zext32_toNat, Nat.add_sub_cancel_left, hoff2_eq, hsz2_eq]
                exact hdw2.slices unit.toNat hu2_lt
              exact hL59 (BitVec.setWidth 64 off2, ()) mP2 ⟨sP2, hinvP2, hpresP2, hredP2,
                (by rw [dense_zext32_toNat]; exact Nat.le_add_right _ _), hslice0, hmP2⟩)
            (fun L59 ⟨p, ⟨⟩⟩ mL ⟨sL, hinvL, hpresL, hredL, hp_le, hsliceL, hmL⟩ hLp => by
              have hlkL := hinvL.1.core_ok
              c0_hsplit
              · have hp_lt : p.toNat < end2n := by rw [← hend2_mod']; exact (by assumption)
                have hrem_pos : 0 < end2n - p.toNat := by omega
                have hp_bd : p.toNat < sL.core.wstk.length := by rw [hlkL.wstk_len_arr]; omega
                c0_hstraight
                let w0 := sL.core.wstk[p.toNat]'hp_bd
                have hp1_eq := fu_bv64_add1_eq (p := p) (by omega)
                c0_hsplit
                · have hbin_step := denseSlice_step_bin hsliceL hrem_pos
                    (List.getElem?_eq_getElem hp_bd) (by assumption)
                  have hslice_n' : DenseWatchSliceOk F_cur sL.core unit.toNat
                      (p + 1#64).toNat (end2n - (p + 1#64).toNat) := by
                    rw [hp1_eq, ← Nat.sub_sub]; exact hbin_step.2.2.2
                  c0_hsteps_nogrp
                  exact hLp (p + 1#64, ()) mL (by dsimp only; rw [hp1_eq]; omega)
                    ⟨sL, hinvL, hpresL, hredL, by rw [hp1_eq]; omega, hslice_n', hmL⟩
                · have hocc_step := denseSlice_step_occ hsliceL hrem_pos
                    (List.getElem?_eq_getElem hp_bd) (by assumption)
                  rcases hocc_step with ⟨cref32, h2rem, hw_cr, _, _, hcr_ref, hslice_n2⟩
                  c0_hstraight; c0_hsplit
                  · c0_hsteps_nogrp; exact hL58 _ mL ⟨sL, hinvL, hpresL, hredL, hmL⟩
                  · have hp2_le_n : p.toNat + 2 ≤ end2n := by omega
                    obtain ⟨hp1_bd, hp1_m_bd, hcr_bd, hcr2_bd, hcr_m_bd, hcr2_m_bd,
                        hcr_wstk, hcr_w_bv, hp2_eq, hp2_bv, hcr_ze, ha0_mem,
                        _, har_hdr_bv, hsz_bv, hsz_eq, _, _, hbd_c⟩ :=
                      dp_occ_cref_setup hinvL hend2_le (hend2_bv.symm ▸ hp2_le_n)
                        hp1_eq hcr_ref hw_cr
                    have hslice2 : DenseWatchSliceOk F_cur sL.core unit.toNat
                        (p + 2#64).toNat (end2n - (p + 2#64).toNat) := by
                      rw [hp2_eq, ← Nat.sub_sub]; exact hslice_n2
                    c0_hstraight; c0_hsplit
                    · c0_hsteps_nogrp; rw [hp2_bv]
                      exact hLp (p + 2#64, ()) mL (by dsimp only; rw [hp2_eq]; omega)
                        ⟨sL, hinvL, hpresL, hredL, by rw [hp2_eq]; exact hp2_le_n,
                          hslice2, hmL⟩
                    · have hng_hdr : sL.core.arena[cref32.toNat]'hcr_bd &&& 524288#32 = 0#32 := by
                        rw [← har_hdr_bv]; exact (by assumption)
                      have hng := dp_garb_false_of_hdr hcr_bd hng_hdr
                      let szc32 := sL.core.arena[cref32.toNat + 2]'hcr2_bd
                      have hsz_c : szc32.toNat =
                          fullArenaClauseSizeCore sL.core cref32.toNat := hsz_eq
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [.bool, i32])
                        (fun _ m70 => m70 = mL)
                        (fun _ ⟨sat, _, ⟨⟩⟩ m70 hm70 => by
                          subst m70
                          refine wp_join_group (ts := [])
                            (fun _ m71 => ∃ s71, FullDenseInvW c F0 F_cur s71 ∧
                              DensePropPres s s71 ∧ s71.scratch.red_refs = s.scratch.red_refs ∧
                              DenseWatchSliceOk F_cur s71.core unit.toNat (p + 2#64).toNat
                                (end2n - (p + 2#64).toNat) ∧ (FullMem c s71 ⋆ R) m71)
                            (fun _ _ m71 ⟨s71, hinv71, hpres71, hred71, hslice71, hm71⟩ => by
                              c0_hsteps_nogrp; rw [hp2_bv]
                              exact hLp (p + 2#64, ()) m71 (by dsimp only; rw [hp2_eq]; omega)
                                ⟨s71, hinv71, hpres71, hred71,
                                  by rw [hp2_eq]; exact hp2_le_n, hslice71, hm71⟩) ?_
                          intro L71 hL71; c0_hsplit
                          · c0_hsteps_nogrp
                            obtain ⟨hinvG, hpresG, hsliceG⟩ := dp_occ_mark_garb_bv hinvL hpresL
                              (by rw [hcr_wstk, hcr_ze]) hcr_ref ha0_mem hslice2 _
                            exact hL71 () _ ⟨_, hinvG, hpresG, hredL, hsliceG, by assumption⟩
                          · c0_hsteps_nogrp
                            exact hL71 () mL ⟨sL, hinvL, hpresL, hredL, hslice2, hmL⟩) ?_
                      intro L70 hL70
                      refine wp_loop_inv (ts := [i32])
                        (fun (j, _) m85 => m85 = mL ∧ j.toNat ≤ szc32.toNat)
                        (fun (j, _) _ => szc32.toNat - j.toNat)
                        (fun L85 hL85 => by
                          c0_hsteps_nogrp
                          have h0 : (0#32 : BitVec 32).toNat ≤ szc32.toNat := by simp
                          exact hL85 (0#32, ()) mL ⟨rfl, h0⟩)
                        (fun L85 ⟨j, ⟨⟩⟩ m85 ⟨hm85, hj_le⟩ hLp85 => by
                          subst m85; c0_hsplit
                          · have hj_lt : j.toNat < szc32.toNat := by
                              dsimp only [szc32]; rw [← hsz_bv]; exact (by assumption)
                            obtain ⟨ha_lit_bd, _, hlj_bd, _, hj1_eq, hlj_bv, _, _, _⟩ :=
                              dp_occ_lit_setup hinvL hcr_ref hng hsz_c hbd_c hj_lt
                                hcr_wstk hcr_w_bv
                            c0_hstraight
                            have hlj_bv_bd : (BitVec.setWidth 64 (sL.core.arena[(BitVec.setWidth
                                  64 (sL.core.wstk[(p + 1#64).toNat]'hp1_bd) + 3#64 +
                                  BitVec.setWidth 64 j).toNat]'ha_lit_bd)).toNat <
                                  sL.core.vals.length := by
                              rw [hlj_bv, dense_zext32_toNat]; exact hlj_bd
                            c0_hstraight; c0_hsplit
                            · exact hL70 (true, j, ()) mL rfl
                            · c0_hsteps_nogrp
                              have hj1_le : (j + 1#32).toNat ≤ szc32.toNat := by
                                rw [hj1_eq]; exact Nat.succ_le_of_lt hj_lt
                              exact hLp85 (j + 1#32, ()) mL (by dsimp only; rw [hj1_eq]; omega)
                                ⟨rfl, hj1_le⟩
                          · c0_hsteps_nogrp; exact hL70 (false, j, ()) mL rfl)
              · c0_hsteps_nogrp; exact hL58 (p, ()) mL ⟨sL, hinvL, hpresL, hredL, hmL⟩)) ?_
      intro L_p2 hL_p2
      refine wp_loop_inv (ts := [i64])
        (fun (p, _) mL => ∃ sL, FullDenseInvW c F0 F_cur sL ∧ DensePropPres s sL ∧
          sL.scratch.red_refs = s.scratch.red_refs ∧ p.toNat ≤ end1n ∧
          DenseWatchSliceOk F_cur sL.core not_unit.toNat p.toNat (end1n - p.toNat) ∧
          (FullMem c sL ⋆ R) mL)
        (fun (p, _) _ => end1n - p.toNat)
        (fun L40 hL40 => by
          c0_hsteps_nogrp
          have hslice0 : DenseWatchSliceOk F_cur s.core not_unit.toNat
              (BitVec.setWidth 64 off1).toNat
              (end1n - (BitVec.setWidth 64 off1).toNat) := by
            rw [dense_zext32_toNat, Nat.add_sub_cancel_left, hoff1_eq, hsz1_eq]
            exact hdw0.slices not_unit.toNat hnot_lt
          exact hL40 (BitVec.setWidth 64 off1, ()) m ⟨s, hinv, dp_pres_refl s, rfl,
            (by rw [dense_zext32_toNat]; exact Nat.le_add_right _ _), hslice0, hm⟩)
        (fun L40 ⟨p, ⟨⟩⟩ mL ⟨sL, hinvL, hpresL, hredL, hp_le, hsliceL, hmL⟩ hLp => by
          have hlkL := hinvL.1.core_ok
          have hwL := hinvL.2.1
          have hcl0L := hinvL.2.2.2.2.2.1
          c0_hsplit
          · have hp_lt : p.toNat < end1n := by rw [← hend1_mod']; exact (by assumption)
            have hrem_pos : 0 < end1n - p.toNat := by omega
            have hp_bd : p.toNat < sL.core.wstk.length := by rw [hlkL.wstk_len_arr]; omega
            c0_hstraight
            let w0 := sL.core.wstk[p.toNat]'hp_bd
            have hp1_eq := fu_bv64_add1_eq (p := p) (by omega)
            c0_hsplit
            · have hbin_step := denseSlice_step_bin hsliceL hrem_pos
                (List.getElem?_eq_getElem hp_bd) (by assumption)
              let other := w0 &&& 0x7FFFFFFF#32
              have hoth_lt : other.toNat < 2 * sL.core.cur_vars := hbin_step.2.1
              have hoth_bd : other.toNat < sL.core.vals.length := by
                have := hlkL.vals_len; have := hlkL.cur_vars_le; omega
              have hoth_bv_bd : (BitVec.setWidth 64 other).toNat < sL.core.vals.length := by
                rw [dense_zext32_toNat]; exact hoth_bd
              have hslice_n' : DenseWatchSliceOk F_cur sL.core not_unit.toNat
                  (p + 1#64).toNat (end1n - (p + 1#64).toNat) := by
                rw [hp1_eq, ← Nat.sub_sub]; exact hbin_step.2.2.2
              have hent_oth : (cnfOfClauses F_cur).EntailsClause (cnfClause [other.toNat]) := by
                have hl' : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [not_unit.toNat ^^^ 1]) := by
                  simpa only [not_unit, dp_not_not_lit] using hunit_ent
                have hr := dense_resolve_bin_unit hbin_step.2.2.1 (Or.inl rfl) hl'
                simpa [other, BitVec.toNat_and] using hr
              c0_hstraight; c0_hsplit
              · have h2 : (BitVec.signExtend 32 (sL.core.vals[other.toNat]'hoth_bd)).slt 0#32 =
                    true := by assumption
                have hoth_ff := dp_val_ff_of_slt_true hwL hoth_lt hoth_bd h2
                have hunsat : (cnfOfClauses F_cur).Unsat :=
                  dense_unsat_of_lit_neg hent_oth
                    (dense_vals_false_entails hwL hcl0L hoth_lt hoth_ff)
                c0_hsteps_nogrp
                exact fu_close_q_false (fu_inv_inconsistent hinvL hunsat) hpresL hredL
                  (hwL.ext_sound.2 hunsat) (by assumption) hQ
              · c0_hstraight; c0_hsplit
                · exact fu_bin_addUnit_wp hAddUnit hinvL hpresL hredL hmL hoth_lt hent_oth
                    hslice_n' hp1_eq (by omega) hLp hQ
                · c0_hsteps_nogrp
                  exact hLp (p + 1#64, ()) mL (by dsimp only; rw [hp1_eq]; omega)
                    ⟨sL, hinvL, hpresL, hredL, by rw [hp1_eq]; omega, hslice_n', hmL⟩
            · have hocc_step := denseSlice_step_occ hsliceL hrem_pos
                (List.getElem?_eq_getElem hp_bd) (by assumption)
              rcases hocc_step with ⟨cref32, h2rem, hw_cr, _, _, hcr_ref, hslice_n2⟩
              c0_hstraight; c0_hsplit
              · c0_hsteps_nogrp; exact hL_p2 _ mL ⟨sL, hinvL, hpresL, hredL, hmL⟩
              · have hp2_le_n : p.toNat + 2 ≤ end1n := by omega
                obtain ⟨hp1_bd, hp1_m_bd, hcr_bd, hcr2_bd, hcr_m_bd, hcr2_m_bd,
                    hcr_wstk, hcr_w_bv, hp2_eq, hp2_bv, hcr_ze, ha0_mem,
                    _, har_hdr_bv, hsz_bv, hsz_eq, _, _, hbd_c⟩ :=
                  dp_occ_cref_setup hinvL hend1_le (hend1_bv.symm ▸ hp2_le_n)
                    hp1_eq hcr_ref hw_cr
                have hslice2 : DenseWatchSliceOk F_cur sL.core not_unit.toNat
                    (p + 2#64).toNat (end1n - (p + 2#64).toNat) := by
                  rw [hp2_eq, ← Nat.sub_sub]; exact hslice_n2
                c0_hstraight; c0_hsplit
                · c0_hsteps_nogrp; rw [hp2_bv]
                  exact hLp (p + 2#64, ()) mL (by dsimp only; rw [hp2_eq]; omega)
                    ⟨sL, hinvL, hpresL, hredL, by rw [hp2_eq]; exact hp2_le_n, hslice2, hmL⟩
                · have hng_hdr : sL.core.arena[cref32.toNat]'hcr_bd &&& 524288#32 = 0#32 := by
                    rw [← har_hdr_bv]; exact (by assumption)
                  have hng := dp_garb_false_of_hdr hcr_bd hng_hdr
                  let szc32 := sL.core.arena[cref32.toNat + 2]'hcr2_bd
                  have hsz_c : szc32.toNat =
                      fullArenaClauseSizeCore sL.core cref32.toNat := hsz_eq
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [.bool, i32, i32, i32])
                    (fun (sat, unass, ul, _) m79 => m79 = mL ∧ (sat = true ∨
                      (sat = false ∧ unass = 0#32 ∧ DpOccScanInv sL.core cref32.toNat
                        szc32.toNat hsz_c hbd_c 0#32 ul szc32.toNat (le_refl _)) ∨
                      (sat = false ∧ unass = 1#32 ∧ DpOccScanInv sL.core cref32.toNat
                        szc32.toNat hsz_c hbd_c 1#32 ul szc32.toNat (le_refl _)) ∨
                      (sat = false ∧ unass ≠ 0#32 ∧ unass ≠ 1#32)))
                    (fun _ ⟨sat, unass, ul, _⟩ m79 ⟨hm79, h79⟩ => by
                      subst m79
                      refine wp_join_group (ts := [])
                        (fun _ m71 => ∃ s71, FullDenseInvW c F0 F_cur s71 ∧
                          DensePropPres s s71 ∧ s71.scratch.red_refs = s.scratch.red_refs ∧
                          DenseWatchSliceOk F_cur s71.core not_unit.toNat (p + 2#64).toNat
                            (end1n - (p + 2#64).toNat) ∧ (FullMem c s71 ⋆ R) m71)
                        (fun _ _ m71 ⟨s71, hinv71, hpres71, hred71, hslice71, hm71⟩ => by
                          c0_hsteps_nogrp; rw [hp2_bv]
                          exact hLp (p + 2#64, ()) m71 (by dsimp only; rw [hp2_eq]; omega)
                            ⟨s71, hinv71, hpres71, hred71,
                              by rw [hp2_eq]; exact hp2_le_n, hslice71, hm71⟩) ?_
                      intro L71 hL71; c0_hsplit
                      · c0_hsteps_nogrp
                        obtain ⟨hinvG, hpresG, hsliceG⟩ := dp_occ_mark_garb_bv hinvL hpresL
                          (by rw [hcr_wstk, hcr_ze]) hcr_ref ha0_mem hslice2 _
                        exact hL71 () _ ⟨_, hinvG, hpresG, hredL, hsliceG, by assumption⟩
                      · c0_hsplit
                        · have hc0 : unass = 0#32 := by assumption
                          subst hc0
                          have hsf : sat = false := by
                            first
                            | exact (by assumption)
                            | exact Bool.eq_false_iff.mpr (by assumption)
                          have hunsat := fu_occ_unass0_unsat hwL hcl0L hcr_ref hng hsz_c
                            hbd_c hsf h79
                          c0_hsteps_nogrp
                          exact fu_close_q_false (fu_inv_inconsistent hinvL hunsat) hpresL hredL
                            (hwL.ext_sound.2 hunsat) (by assumption) hQ
                        · refine wp_join_group (ts := [])
                            (fun _ m73 => ∃ s73, FullDenseInvW c F0 F_cur s73 ∧
                              DensePropPres s s73 ∧ s73.scratch.red_refs = s.scratch.red_refs ∧
                              DenseWatchSliceOk F_cur s73.core not_unit.toNat (p + 2#64).toNat
                                (end1n - (p + 2#64).toNat) ∧ (FullMem c s73 ⋆ R) m73)
                            (fun _ _ m73 ⟨s73, hinv73, hpres73, hred73, hslice73, hm73⟩ => by
                              c0_hsteps_nogrp
                              exact hL71 () m73 ⟨s73, hinv73, hpres73, hred73, hslice73, hm73⟩) ?_
                          intro L73 hL73; c0_hsplit
                          · have hc1 : unass = 1#32 := by assumption
                            subst hc1
                            have hsf : sat = false := by
                              first
                              | exact (by assumption)
                              | exact Bool.eq_false_iff.mpr (by assumption)
                            obtain ⟨hlt_u, hent_u⟩ := fu_occ_unass1_entails hwL hcl0L hcr_ref
                              hng hsz_c hbd_c hsf h79
                            c0_hsteps_nogrp
                            obtain ⟨hinvG, hpresG, hsliceG⟩ := dp_occ_mark_garb_bv hinvL hpresL
                              (by rw [hcr_wstk, hcr_ze]) hcr_ref ha0_mem hslice2 _
                            exact fu_occ_addUnit_wp hAddUnit hinvG hpresG hredL (by assumption)
                              (by rw [hpresG.1, ← hpresL.1]; exact hlt_u) hent_u hsliceG hL73 hQ
                          · c0_hsteps_nogrp
                            exact hL73 () mL ⟨sL, hinvL, hpresL, hredL, hslice2, hmL⟩) ?_
                  intro L79 hL79
                  refine wp_loop_inv (ts := [i32, i32, i32])
                    (fun (unass, ul, j, _) m86 => m86 = mL ∧
                      ∃ hj : j.toNat ≤ szc32.toNat,
                        DpOccScanInv sL.core cref32.toNat szc32.toNat hsz_c hbd_c
                          unass ul j.toNat hj)
                    (fun (_, _, j, _) _ => szc32.toNat - j.toNat)
                    (fun L86 hL86 => by
                      c0_hsteps_nogrp
                      have h0 : (0#32 : BitVec 32).toNat ≤ szc32.toNat := by simp
                      exact hL86 (0#32, 0#32, 0#32, ()) mL
                        ⟨rfl, h0, Or.inl ⟨rfl, fun _ hq => by simp at hq⟩⟩)
                    (fun L86 ⟨unass, ul, j, ⟨⟩⟩ m86 ⟨hm86, hj_le, hscan⟩ hLp86 => by
                      subst m86; c0_hsplit
                      · have hj_lt : j.toNat < szc32.toNat := by
                          dsimp only [szc32]; rw [← hsz_bv]; exact (by assumption)
                        obtain ⟨ha_lit_bd, _, hlj_bd, _, hj1_eq, hlj_bv,
                            _, hlj_lt, hval_lit_mod⟩ :=
                          dp_occ_lit_setup hinvL hcr_ref hng hsz_c hbd_c hj_lt hcr_wstk hcr_w_bv
                        c0_hstraight
                        let lit_j := sL.core.arena[cref32.toNat + 3 + j.toNat]'(by omega)
                        have hlj_bv1 : sL.core.arena[(BitVec.setWidth 64
                            (sL.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_bd) +
                            (3 : BitVec 64) + BitVec.setWidth 64 j).toNat]'ha_lit_bd =
                            lit_j := hlj_bv
                        have hlj_bv_bd : (BitVec.setWidth 64 (sL.core.arena[(BitVec.setWidth 64
                              (sL.core.wstk[(p + 1#64).toNat]'hp1_bd) + 3#64 +
                              BitVec.setWidth 64 j).toNat]'ha_lit_bd)).toNat <
                              sL.core.vals.length := by
                            rw [hlj_bv, dense_zext32_toNat]; exact hlj_bd
                        c0_hstraight; c0_hsplit
                        · exact hL79 (true, unass, ul, j, ()) mL ⟨rfl, Or.inl rfl⟩
                        · have hsgt_f : (0#32).slt (BitVec.signExtend 32
                              (sL.core.vals[lit_j.toNat]'hlj_bd)) = false := by
                            rw [← hval_lit_mod]; exact (by assumption)
                          have hstep := dp_occ_scan_step hj_lt rfl hscan
                          refine wp_join_group (ts := [i32, i32])
                            (fun (u', ul', _) m102 => m102 = mL ∧
                              DpOccScanInv sL.core cref32.toNat szc32.toNat hsz_c hbd_c
                                u' ul' (j.toNat + 1) (Nat.succ_le_of_lt hj_lt))
                            (fun _ ⟨u', ul', ⟨⟩⟩ m102 ⟨hm102, hinv102⟩ => by
                              c0_hsteps_nogrp
                              have hj1_le : (j + 1#32).toNat ≤ szc32.toNat := by
                                rw [hj1_eq]; exact Nat.succ_le_of_lt hj_lt
                              exact hLp86 (u', ul', j + 1#32, ()) m102
                                (by dsimp only; rw [hj1_eq]; omega)
                                ⟨hm102, hj1_le, dp_occ_scan_cast hj1_eq.symm hinv102⟩) ?_
                          intro L102 hL102; c0_hstraight; c0_hsplit
                          · have heq0 : BitVec.signExtend 32
                                (sL.core.vals[lit_j.toNat]'hlj_bd) = 0#32 := by
                              rw [← hval_lit_mod]; exact (by assumption)
                            have hv0 := dp_val_zero_of_sext_eq hwL hlj_lt hlj_bd heq0
                            c0_hstraight; c0_hsplit
                            · have hne : unass ≠ 0#32 := fun hu0 => by
                                subst hu0
                                have h1 : BitVec.toNat (1 : BitVec 32) <
                                    (BitVec.toNat 0#32 + BitVec.toNat (1 : BitVec 32)) %
                                      2 ^ 32 := by assumption
                                exact absurd h1 (by decide)
                              have hu1 : unass = 1#32 := (hstep.1 hv0).2 hne
                              c0_hsteps_nogrp
                              exact hL79 (false, unass + (1 : BitVec 32), ul, j, ()) mL
                                ⟨rfl, Or.inr (Or.inr (Or.inr
                                  ⟨rfl, by rw [hu1]; decide, by rw [hu1]; decide⟩))⟩
                            · have hu0 : unass = 0#32 := by
                                rcases hscan with ⟨h0, -⟩ | ⟨h1, -⟩
                                · exact h0
                                · subst h1
                                  exact absurd (by
                                    decide : BitVec.toNat (1 : BitVec 32) <
                                      (BitVec.toNat 1#32 + BitVec.toNat (1 : BitVec 32)) %
                                        2 ^ 32)
                                    (by assumption)
                              c0_hsteps_nogrp; rw [hlj_bv1]
                              exact hL102 (unass + (1 : BitVec 32), lit_j, ()) mL
                                ⟨rfl, by rw [hu0]; exact (hstep.1 hv0).1 hu0⟩
                          · have hne0 : BitVec.signExtend 32
                                (sL.core.vals[lit_j.toNat]'hlj_bd) ≠ 0#32 := by
                              rw [← hval_lit_mod]; exact (by assumption)
                            have hvff := dp_val_ff_of_slt_ne hwL hlj_lt hlj_bd hsgt_f hne0
                            exact hL102 (unass, ul, ()) mL ⟨rfl, hstep.2 hvff⟩
                      · c0_hsteps_nogrp
                        have hjeq : j.toNat = szc32.toNat := by
                          have hhc : ¬j.toNat <
                              (sL.core.arena[((sL.core.wstk[(p.toNat +
                                BitVec.toNat 1#64) % 2 ^ 64]'hp1_m_bd).toNat +
                                BitVec.toNat 2#64) % 2 ^ 64]'hcr2_m_bd).toNat := by assumption
                          dsimp only [szc32]; rw [hsz_bv] at hhc; omega
                        rcases hscan with ⟨hu0, hall⟩ | ⟨hu1, q0, hq0, heq0, hv0, hall⟩
                        · exact hL79 (false, unass, ul, j, ()) mL
                            ⟨rfl, Or.inr (Or.inl ⟨rfl, hu0,
                              Or.inl ⟨rfl, fun q hq => hall q (hjeq ▸ hq)⟩⟩)⟩
                        · exact hL79 (false, unass, ul, j, ()) mL
                            ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, hu1, Or.inr ⟨rfl, q0,
                              hjeq ▸ hq0, heq0, hv0, fun q hq => hall q (hjeq ▸ hq)⟩⟩))⟩)
          · c0_hsteps_nogrp; exact hL_p2 (p, ()) mL ⟨sL, hinvL, hpresL, hredL, hmL⟩)

/-! ## 3. `full_dense_flush_units_m7_wp` (`Spec.fullDenseFlushUnitsSpec`) -/

theorem full_dense_flush_units_m7_wp (Γ : Env)
    (hPropUnit : Γ.Has "full_dense_prop_unit_m7" Spec.fullDensePropUnitSpec)
    (a : Tup Val [i64]) (m : Mem 64) (Q : Post [.bool]) (X : XPost)
    (hPre : Spec.fullDenseFlushUnitsSpec a m Q X) :
    Func.wp Γ full_dense_flush_units_m7_body a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rcases hPre with ⟨c, F0, F_cur, s, R, rfl, hinv, hm, hQ⟩
  have hlk := hinv.1.core_ok
  have hp_lt64 : s.core.propagated < 2 ^ 64 := by
    have := c.hmaxv; unfold dimacsBound at this
    have := hlk.propagated_le; have := hlk.trail_end_le; have := hlk.cur_vars_le; omega
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64])
    (fun (i, _) mL => ∃ sL, FullDenseInvW c F0 F_cur sL ∧ FuPres s sL ∧
      i.toNat ≤ c.max_vars ∧ (FullMem c sL ⋆ R) mL)
    (fun (i, _) _ => c.max_vars - i.toNat)
    (fun L5 hL5 => by
      c0_hsteps_nogrp
      exact hL5 (BitVec.ofNat 64 s.core.propagated, ()) m ⟨s, hinv, fu_pres_refl s,
        by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp_lt64]
           exact le_trans hlk.propagated_le (le_trans hlk.trail_end_le hlk.cur_vars_le),
        hm⟩)
    (fun L5 ⟨i, ⟨⟩⟩ mL ⟨sL, hinvL, hpresL, hi_le, hmL⟩ hLp => by
      have hlkL := hinvL.1.core_ok
      refine wp_join_group (ts := [])
        (fun _ mE => ∃ sE, FullDenseInvW c F0 F_cur sE ∧ FuPres s sE ∧ (FullMem c sE ⋆ R) mE)
        (fun _ _ mE ⟨sE, hinvE, hpresE, hmE⟩ => by
          have hlkE := hinvE.1.core_ok
          have hwE := hinvE.2.1
          have hteE64 : sE.core.trail_end < 2 ^ 64 := by
            have := c.hmaxv; unfold dimacsBound at this
            have := hlkE.trail_end_le; have := hlkE.cur_vars_le; omega
          refine wp_join_group (ts := [i64])
            (fun (p5, _) m8 => ∃ s8, FullDenseInvW c F0 F_cur s8 ∧ FuPres s s8 ∧
              p5.toNat ≤ s8.core.trail_end ∧ (FullMem c s8 ⋆ R) m8)
            (fun _ ⟨p5, ⟨⟩⟩ m8 ⟨s8, hinv8, hpres8, hp5_le, hm8⟩ => by
              c0_hsteps_nogrp
              let sF := { s8 with core := { s8.core with propagated := p5.toNat } }
              have hinvF := fullDenseInvW_with_prop hinv8 hp5_le
              have hpresF : FuPres s sF := fu_pres_trans hpres8 (fu_pres_refl s8)
              rcases hpresF with ⟨p1, p2, p3, p4, p5f, p6, p7, p8, p9, p10⟩
              by_cases hinc : s8.core.inconsistent = 0#64
              · have hbeq : (s8.core.inconsistent == 0) = true := beq_iff_eq.mpr hinc
                rw [hbeq]
                exact hQ true sF _ hinvF p1 p2 p3 p4 p5f p6 p7 p8 p9 p10
                  (by simp) (by assumption)
              · have hbeq : (s8.core.inconsistent == 0) = false := beq_false_of_ne hinc
                rw [hbeq]
                have hunsat : F0.Unsat :=
                  hinv8.2.1.ext_sound.2 (hinv8.2.1.inconsistent_sound hinc)
                exact hQ false sF _ hinvF p1 p2 p3 p4 p5f p6 p7 p8 p9 p10
                  (fun _ => hunsat) (by assumption)) ?_
          intro L8 hL8
          c0_hsteps_nogrp
          · exact hL8 (i, ()) mE ⟨sE, hinvE, hpresE, by
              have hle : i.toNat ≤ sE.core.trail_end % 2 ^ 64 := by assumption
              rwa [Nat.mod_eq_of_lt hteE64] at hle, hmE⟩
          · exact hL8 (BitVec.ofNat 64 sE.core.trail_end, ()) mE ⟨sE, hinvE, hpresE,
              by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hteE64]; exact Nat.le_refl _, hmE⟩) ?_
      intro L7 hL7
      c0_hsteps_nogrp
      · have hi_lt_te : i.toNat < sL.core.trail_end := by
          have hc' : i.toNat < sL.core.trail_end % 2 ^ 64 := by assumption
          have h1 : sL.core.trail_end < 2 ^ 64 := by
            have := c.hmaxv; unfold dimacsBound at this
            have := hlkL.trail_end_le; have := hlkL.cur_vars_le; omega
          rwa [Nat.mod_eq_of_lt h1] at hc'
        have hi_bd : i.toNat < sL.core.trl.length := by
          have := hlkL.trl_len; have := hlkL.trail_end_le; have := hlkL.cur_vars_le; omega
        have hi1_lt64 : i.toNat + 1 < 2 ^ 64 := by
          have := c.hmaxv; unfold dimacsBound at this; omega
        have hi1_eq := fu_bv64_add1_eq hi1_lt64
        c0_hstraight
        dr_call hPropUnit
        refine ⟨c, F0, F_cur, sL, R, rfl, hinvL, hmL,
          fun ok s1 m1 hinv1 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 hf1 hm1 => ?_⟩
        have hpres1 : FuPres s s1 :=
          fu_pres_trans hpresL ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩
        have hte_le := hlkL.trail_end_le
        have hcv_le := hlkL.cur_vars_le
        c0_hsplit
        · c0_hsteps_nogrp
          exact hLp (i + 1#64, ()) m1 (by dsimp only; rw [hi1_eq]; omega)
            ⟨s1, hinv1, hpres1, by rw [hi1_eq]; omega, hm1⟩
        · have hok_f : ok = false := by
            first | exact (by assumption) | exact Bool.eq_false_iff.mpr (by assumption)
          rcases hpres1 with ⟨p1', p2', p3', p4', p5', p6', p7', p8', p9', p10'⟩
          c0_hsteps_nogrp
          exact hQ false s1 m1 hinv1 p1' p2' p3' p4' p5' p6' p7' p8' p9' p10'
            (fun _ => hf1 hok_f) hm1
      · exact hL7 () mL ⟨sL, hinvL, hpresL, hmL⟩
      · exact hL7 () mL ⟨sL, hinvL, hpresL, hmL⟩)

end LeanQbe.T.Examples.Kissat.Proof.Dense
