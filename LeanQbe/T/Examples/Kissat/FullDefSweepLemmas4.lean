module

public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` `kitten` Cone Construction & Refinement `Func.wp` Proofs (`Part 4`)

Proves the parametric `(Γ : Env)` `Func.wp` contracts for `2` `kitten` cone helpers
in `FullDefSweep`:
1. `full_sweep_refine_kitten_wp`
2. `full_sweep_cone_wp`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullDefSweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullArenaTactics FullSweepFwdHelpers FullSweepVarHelpers

theorem dsSweep_ptr_k_256_eq (p i : BitVec 64) :
    (p + BitVec.ofNat 64 256 * 4) + i * 4 = p + BitVec.ofNat 64 (4 * (256 + i.toNat)) := by
  have hmul : i * 4 = BitVec.ofNat 64 (i.toNat * 4) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]
  rw [BitVec.add_assoc]; congr 1
  rw [hmul, show (BitVec.ofNat 64 256 * 4 : BitVec 64) = BitVec.ofNat 64 1024 from rfl,
    ← BitVec.ofNat_add, show 1024 + i.toNat * 4 = 4 * (256 + i.toNat) by omega]

namespace FullDefSweepTactics

@[scoped c0_load] theorem load_k_256_dyn {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : 256 + i.toNat < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 256 * 4 + i * 4) =
      some s.scratch.scratch_buf[256 + i.toNat] := by
  rw [dsSweep_ptr_k_256_eq]; exact load_full_scratch_buf hi hm

@[scoped c0_store] theorem store_k_256_dyn {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : 256 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 256 * 4 + i * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (256 + i.toNat) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 256 * 4 + i * 4) v) := by
  rw [dsSweep_ptr_k_256_eq]; exact store_full_scratch_buf v hi hm

@[scoped bv_c0] theorem bv32_shl1_mod32 (x : BitVec 32) :
    x <<< ((1#32 : BitVec 32).toNat % 32) = x <<< (1 : Nat) := rfl

end FullDefSweepTactics

open scoped FullArenaTactics FullCongTactics FullDefSweepTactics

theorem fullSweepGlobalLit_eq_coneLift' (s : FullState) :
    fullSweepGlobalLit s = FullSweepFwdSpecs.coneLift s.scratch.work_stk1 := by
  funext ll; unfold fullSweepGlobalLit FullSweepFwdSpecs.coneLift; omega

/-! ## 1. Pure, Separation, & Semantic Helpers for `kitten` Cone Sweeping -/

private theorem getElem_eq_getElem?_getD {α : Type} (xs : List α) {i : Nat}
    (h : i < xs.length) (d : α) : xs[i]'h = xs[i]?.getD d := by
  rw [List.getElem?_eq_getElem h, Option.getD_some]

private theorem list_getElem_congr {α : Type} {xs : List α} {i j : Nat}
    (hij : i = j) (hi : i < xs.length) (hj : j < xs.length) :
    xs[i]'hi = xs[j]'hj := by subst hij; rfl

theorem dsSweep_bv32_add1_lt {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega

private theorem bv32_sub1_nat {x : BitVec 32} (hpos : 1 ≤ x.toNat) (hle : x.toNat ≤ 128) :
    (x - 1#32).toNat = x.toNat - 1 := by bv_omega

private theorem bv32_eq_add1_of_sub1 {x y : BitVec 32} (h : x - 1#32 = y) :
    x = y + 1#32 := by bv_omega

private theorem bv32_add1_sub1_small (x : BitVec 32) :
    (x + 1#32 - 1#32).toNat = x.toNat := by bv_omega

private theorem bv32_ofNat_add1_small (x : BitVec 32) :
    BitVec.ofNat 32 (x.toNat + 1) = x + 1#32 := by bv_omega

private theorem bv64_pack_nv_nc_gen {nv nc : Nat} (hnv : nv < 2 ^ 16) (hnc : nc < 2 ^ 16) :
    (BitVec.ofNat 64 (nv ||| (nc <<< 16)) &&& 0xFFFF#64).toNat = nv ∧
    (BitVec.ofNat 64 (nv ||| (nc <<< 16)) >>> (16 : Nat)).toNat = nc := by
  have hlt16 : ∀ {x : Nat}, x < 2 ^ 16 → ∀ j, 16 ≤ j → x.testBit j = false := fun hx j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
  have hmask : ∀ j, Nat.testBit 65535 j = decide (j < 16) := fun j => by
    rw [show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  have hor_lt : nv ||| (nc <<< 16) < 2 ^ 32 :=
    Nat.or_lt_two_pow (by omega) (by rw [Nat.shiftLeft_eq]; omega)
  have h1 : (BitVec.ofNat 64 (nv ||| (nc <<< 16)) &&& 0xFFFF#64) = BitVec.ofNat 64 nv := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_or, Nat.testBit_shiftLeft,
      hmask, decide_eq_true hi, Bool.true_and]
    by_cases h16 : i < 16
    · simp [h16, show ¬ (16 ≤ i) by omega]
    · simp [h16, hlt16 hnv i (by omega)]
  have h2 : (BitVec.ofNat 64 (nv ||| (nc <<< 16)) >>> (16 : Nat)) = BitVec.ofNat 64 nc := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat]
    by_cases h48 : 16 + i < 64
    · simp only [decide_eq_true hi, decide_eq_true h48, Bool.true_and, Nat.testBit_or,
        Nat.testBit_shiftLeft, show 16 ≤ 16 + i by omega, decide_true,
        show 16 + i - 16 = i by omega, hlt16 hnv (16 + i) (by omega), Bool.false_or]
    · simp [decide_eq_true hi, decide_eq_false h48, hlt16 hnc i (by omega)]
  rw [h1, h2, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  exact ⟨rfl, rfl⟩

private theorem cone_pack_nv_nc (nv nc : BitVec 32) (hnv : nv.toNat ≤ 128)
    (hnc : nc.toNat ≤ 512) :
    ((nv.setWidth 64 ||| (nc.setWidth 64 <<< 16#64)) &&& 0xFFFF#64).toNat = nv.toNat ∧
    ((nv.setWidth 64 ||| (nc.setWidth 64 <<< 16#64)) >>> 16#64).toNat = nc.toNat := by
  have heq : nv.setWidth 64 ||| (nc.setWidth 64 <<< 16#64) =
      BitVec.ofNat 64 (nv.toNat ||| (nc.toNat <<< 16)) := by
    apply BitVec.eq_of_toNat_eq
    have hshl : (nc.setWidth 64 <<< 16#64).toNat = nc.toNat <<< 16 := by
      rw [show (nc.setWidth 64 <<< 16#64) = (nc.setWidth 64 <<< (16 : Nat)) from rfl,
        BitVec.toNat_shiftLeft, bv_c0_zext32_64,
        Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega : nc.toNat <<< 16 < 2 ^ 64)]
    have hor : nv.toNat ||| (nc.toNat <<< 16) < 2 ^ 32 :=
      Nat.or_lt_two_pow (by omega) (by rw [Nat.shiftLeft_eq]; omega)
    rw [BitVec.toNat_or, bv_c0_zext32_64, hshl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [heq, show ∀ z : BitVec 64, z >>> 16#64 = z >>> (16 : Nat) from fun _ => rfl]
  exact bv64_pack_nv_nc_gen (by omega) (by omega)

private def coneKMask (t : FullState) : FullState :=
  { core := { t.core with tmp := [] }
    scratch := { t.scratch with work_stk1 := [], tarjan_mark := [], scratch_buf := [] } }

private theorem coneKMask_core_eq {s st : FullState} (h : AgreesExcept coneKMask s st) :
    st.core = { s.core with tmp := st.core.tmp } := by
  have hc : ({ st.core with tmp := [] } : FullCoreState) = { s.core with tmp := [] } :=
    congrArg FullState.core h
  cases h1 : st.core; cases h2 : s.core
  rw [h1, h2] at hc; cases hc; rfl

private theorem coneKMask_state_eq {s st : FullState} (h : AgreesExcept coneKMask s st) :
    st = { s with
      core := { s.core with tmp := st.core.tmp }
      scratch := { s.scratch with
        work_stk1 := st.scratch.work_stk1
        tarjan_mark := st.scratch.tarjan_mark
        scratch_buf := st.scratch.scratch_buf } } := by
  have hc := coneKMask_core_eq h
  have hs : (coneKMask st).scratch = (coneKMask s).scratch := congrArg FullState.scratch h
  cases st with | mk c1 sc1 => cases s with | mk c2 sc2 =>
  dsimp only [coneKMask] at hc hs ⊢
  cases sc1; cases sc2; cases hs; rw [hc]

private theorem coneKMask_preserves_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hag : AgreesExcept coneKMask s st)
    (hlen : st.LengthsOk c) (hdw : FullDenseInvW c F0 F_cur s) :
    FullDenseInvW c F0 F_cur st := by
  have hc0 := coneKMask_core_eq hag
  generalize st.core.tmp = tmp' at hc0
  have hll : st.scratch.last_learned = s.scratch.last_learned := hag.get (·.scratch.last_learned)
  have hex : st.scratch.extend_len = s.scratch.extend_len := hag.get (·.scratch.extend_len)
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc0]; exact fullWitnessInv_with_tmp_flags_fuel hdw.2.1 tmp' s.core.flags s.core.fuel
  · have hmc := hdw.2.2.1
    exact ⟨fun v hv => by simpa [hc0] using hmc.1 v hv,
      fun l hl => by simpa [hc0] using hmc.2 l hl⟩
  · have hnda := hdw.2.2.2.1; intro r hr hng
    dsimp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseLits] at hr hng ⊢
    simp only [fullArenaClauseRefsCore, fullArenaClauseGarbCore, fullArenaClauseLitsCore, hc0]
      at hr hng ⊢
    exact hnda r hr hng
  · refine ⟨fun i hi => ?_, by simpa [hex] using hdw.2.2.2.2.1.2⟩
    have h1 := hdw.2.2.2.2.1.1 i hi
    dsimp only at h1 ⊢; rw [hll, fullArenaClauseRefs, hc0]; exact h1
  · rw [hc0]; exact hdw.2.2.2.2.2.1
  · rw [hc0]; exact hdw.2.2.2.2.2.2

private def SweepKittenConeOk
    (KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop)
    (F_cur : List (List Nat)) (st : FullState) (root_v nv nc : Nat)
    (cls : List (Nat × List Nat)) : Prop :=
  1 ≤ nv ∧ nv ≤ 128 ∧ nv ≤ st.core.cur_vars ∧ nc = cls.length ∧ cls.length ≤ 512 ∧
  KInv 128 cls false .fresh st.scratch.scratch_buf ∧
  st.scratch.scratch_buf[256 + 18]? = some 0#32 ∧
  (st.scratch.work_stk1[0]?.getD 0#32).toNat = root_v ∧
  (∀ i < nv,
    (st.scratch.work_stk1[i]?.getD 0#32).toNat < st.core.cur_vars ∧
    st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#32 =
      BitVec.ofNat 32 (i + 1)) ∧
  (∀ v < st.core.cur_vars,
    st.scratch.tarjan_mark[v]?.getD 0#32 = 0#32 ∨
    ∃ i < nv,
      (st.scratch.work_stk1[i]?.getD 0#32).toNat = v ∧
      st.scratch.tarjan_mark[v]?.getD 0#32 = BitVec.ofNat 32 (i + 1)) ∧
  (∀ cl ∈ cls,
    (∀ l ∈ cl.2, l < 2 * nv) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause (cl.2.map (fullSweepGlobalLit st))))

private theorem sweepKittenConeOk_tmp_irrel
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    {F_cur : List (List Nat)} {st : FullState} {root_v nv nc : Nat}
    {cls : List (Nat × List Nat)} {tmp' : List (BitVec 32)}
    (h : SweepKittenConeOk KInv F_cur st root_v nv nc cls) :
    SweepKittenConeOk KInv F_cur { st with core := { st.core with tmp := tmp' } }
      root_v nv nc cls := h

private theorem sweepKittenConeOk_init
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState} {scr0 : List (BitVec 32)}
    {root_v : BitVec 32} (hlen : s.LengthsOk c) (hroot : root_v.toNat < s.core.cur_vars)
    (htmk : TmkZero s) (hscr0 : scr0.length = c.scratch_cap)
    (h18 : scr0[256 + 18]? = some 0#32) (hK : KInv 128 [] false .fresh scr0) :
    let s1 : FullState :=
      { s with scratch :=
        { s.scratch with
          scratch_buf := scr0
          work_stk1 := s.scratch.work_stk1.set 0 root_v
          tarjan_mark := s.scratch.tarjan_mark.set root_v.toNat 1#32 } }
    s1.LengthsOk c ∧ AgreesExcept coneKMask s s1 ∧
    SweepKittenConeOk KInv F_cur s1 root_v.toNat 1 0 [] := by
  intro s1
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwk_len := hlen.scratch_ok.work_stk1_len
  have htm_len := hlen.scratch_ok.tarjan_mark_len
  refine ⟨⟨hlen.core_ok, { hlen.scratch_ok with
      work_stk1_len := by simp [s1, hwk_len]
      tarjan_mark_len := by simp [s1, htm_len]
      scratch_buf_len := by simp [s1, hscr0] }⟩,
    rfl, by omega, by omega, by dsimp [s1]; omega, rfl, by simp, hK, h18, ?_, ?_, ?_,
    fun _ hx => by cases hx⟩
  · dsimp only [s1]; rw [List.getElem?_set_self (by omega), Option.getD_some]
  · intro i hi; have hi0 : i = 0 := by omega
    subst hi0; dsimp only [s1]
    rw [List.getElem?_set_self (by omega), Option.getD_some,
      List.getElem?_set_self (by omega), Option.getD_some]
    exact ⟨hroot, rfl⟩
  · intro v hv; dsimp only [s1]
    by_cases hvr : v = root_v.toNat
    · subst hvr; right; refine ⟨0, by omega, ?_, ?_⟩
      · rw [List.getElem?_set_self (by omega), Option.getD_some]
      · rw [List.getElem?_set_self (by omega), Option.getD_some]
    · left; rw [List.getElem?_set_ne (Ne.symm hvr)]; exact htmk v hv

private theorem sweepKittenConeOk_push_var
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {root_v nv nc : Nat} {cls : List (Nat × List Nat)} {ov : BitVec 32}
    (hlen : s.LengthsOk c) (hc : SweepKittenConeOk KInv F_cur s root_v nv nc cls)
    (hnv128 : nv < 128) (hov : ov.toNat < s.core.cur_vars)
    (hmiss : s.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = 0#32) :
    nv < s.core.cur_vars ∧
    let s' : FullState :=
      { s with scratch :=
        { s.scratch with
          tarjan_mark := s.scratch.tarjan_mark.set ov.toNat (BitVec.ofNat 32 (nv + 1))
          work_stk1 := s.scratch.work_stk1.set nv ov } }
    SweepKittenConeOk KInv F_cur s' root_v (nv + 1) nc cls := by
  obtain ⟨hnv1, _, _, hnc_len, hcls_512, hK, h18, hroot, hfwd, hrev, hcls⟩ := hc
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwk_len := hlen.scratch_ok.work_stk1_len
  have htm_len := hlen.scratch_ok.tarjan_mark_len
  have hne_ov : ∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat ≠ ov.toNat := fun i hi heq => by
    have hti := (hfwd i hi).2; rw [heq, hmiss] at hti
    have htn := congrArg BitVec.toNat hti
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 32)] at htn
    omega
  have hnv_lt : nv < s.core.cur_vars :=
    inj_lt_of_missing (fun i => (s.scratch.work_stk1[i]?.getD 0#32).toNat)
      (fun i j hi hj heq => by
        have hti := (hfwd i hi).2; have htj := (hfwd j hj).2
        rw [heq] at hti
        have htn := congrArg BitVec.toNat (hti.symm.trans htj)
        simp only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 32)] at htn
        omega)
      (fun i hi => (hfwd i hi).1) hov hne_ov
  refine ⟨hnv_lt, ?_⟩
  intro s'
  have hwk_lt : ∀ i < nv, s'.scratch.work_stk1[i]? = s.scratch.work_stk1[i]? := fun i hi =>
    List.getElem?_set_ne (by omega)
  have hwk_nv : s'.scratch.work_stk1[nv]? = some ov := List.getElem?_set_self (by omega)
  refine ⟨by omega, by omega, by dsimp [s']; omega, hnc_len, hcls_512, hK, h18, ?_, ?_, ?_, ?_⟩
  · rw [hwk_lt 0 (by omega)]; exact hroot
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · rw [hwk_lt i hi']
      have hne := hne_ov i hi'
      refine ⟨(hfwd i hi').1, ?_⟩
      dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hne)]; exact (hfwd i hi').2
    · rw [hwk_nv, Option.getD_some]
      refine ⟨hov, ?_⟩
      dsimp only [s']; rw [List.getElem?_set_self (by omega), Option.getD_some]
  · intro v hv
    by_cases hvo : v = ov.toNat
    · subst hvo; right; refine ⟨nv, by omega, ?_, ?_⟩
      · rw [hwk_nv, Option.getD_some]
      · dsimp only [s']; rw [List.getElem?_set_self (by omega), Option.getD_some]
    · dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hvo)]
      rcases hrev v hv with hz | ⟨i, hi, hwi, hti⟩
      · exact Or.inl hz
      · exact Or.inr ⟨i, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hwi, hti⟩
  · intro cl hcl
    obtain ⟨hbds, hent⟩ := hcls cl hcl
    refine ⟨fun l hl => Nat.lt_trans (hbds l hl) (by omega), ?_⟩
    have hmap : cl.2.map (fullSweepGlobalLit s') = cl.2.map (fullSweepGlobalLit s) := by
      apply List.map_congr_left; intro l hl
      have hlt : l < 2 * nv := hbds l hl
      unfold fullSweepGlobalLit; rw [hwk_lt (l / 2) (by omega)]
    rw [hmap]; exact hent

private theorem sweepKittenConeOk_add_cl
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    {F_cur : List (List Nat)} {s : FullState} {root_v nv nc eid sz : Nat}
    {cls : List (Nat × List Nat)} {xs scr' : List (BitVec 32)}
    (hc : SweepKittenConeOk KInv F_cur s root_v nv nc cls)
    (hnc : nc < 512) (hsz : sz ≤ xs.length)
    (hlts : ∀ k < sz, (xs[k]?.getD 0#32).toNat < 2 * nv)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((xs.take sz).map (fun x => fullSweepGlobalLit s x.toNat))))
    (h18 : scr'[256 + 18]? = some 0#32)
    (hK' : KInv 128 (cls ++ [(eid, (xs.take sz).map BitVec.toNat)]) false .fresh scr') :
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    SweepKittenConeOk KInv F_cur s' root_v nv (nc + 1)
      (cls ++ [(eid, (xs.take sz).map BitVec.toNat)]) := by
  obtain ⟨hnv1, hnv128, hnv_cv, hnc_len, _, _, _, hroot, hfwd, hrev, hcls⟩ := hc
  refine ⟨hnv1, hnv128, hnv_cv, by simp [hnc_len], by simp; omega, hK', h18, hroot, hfwd, hrev, ?_⟩
  intro cl hcl
  rw [List.mem_append, List.mem_singleton] at hcl
  rcases hcl with hold | rfl
  · exact hcls cl hold
  · refine ⟨fun l hl => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
      have hkl : k < sz := by rw [List.length_take] at hk; omega
      have hxk := hlts k hkl
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hxk
      rwa [List.getElem_take]
    · simp only [List.map_map]
      simpa [Function.comp_def, fullSweepGlobalLit] using hent

private theorem sweepKittenConeOk_to_spec
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hLaws : KittenInvLaws KInv)
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {root_v nv nc : Nat} {cls : List (Nat × List Nat)}
    (hlen : s.LengthsOk c)
    (hc : SweepKittenConeOk KInv F_cur s root_v nv nc cls) :
    let scr' :=
      (s.scratch.scratch_buf.set 256 (BitVec.ofNat 32 nv)).set 262 (BitVec.ofNat 32 nv)
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    s'.LengthsOk c ∧
    fullSweepKittenConeOk F_cur s' cls nv nc ∧
    KInv nv cls false .fresh scr' ∧
    (s'.scratch.work_stk1[0]?.getD 0#32).toNat = root_v ∧
    (∀ v < s.core.cur_vars, s'.scratch.tarjan_mark[v]?.getD 0#32 ≠ 0#32 →
      ∃ i < nv, (s'.scratch.work_stk1[i]?.getD 0#32).toNat = v) := by
  obtain ⟨hnv1, hnv128, hnv_cv, hnc_len, hcls_512, hK, h18, hroot, hfwd, hrev, hcls⟩ := hc
  intro scr' s'
  have hscr_l : scr'.length = c.scratch_cap := by
    simp [scr', hlen.scratch_ok.scratch_buf_len]
  have hK' : KInv nv cls false .fresh scr' :=
    hLaws.set_nv hK hnv1 hnv128 (by rw [h18]; rfl) (fun cl hcl => (hcls cl hcl).1)
  have hrev' : ∀ v < s.core.cur_vars, s'.scratch.tarjan_mark[v]?.getD 0#32 ≠ 0#32 →
      ∃ i < nv, (s'.scratch.work_stk1[i]?.getD 0#32).toNat = v := fun v hv hne => by
    rcases hrev v hv with hz | ⟨i, hi, hwi, _⟩
    · exact absurd hz hne
    · exact ⟨i, hi, hwi⟩
  exact ⟨⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr_l }⟩,
    ⟨hnv1, hnv128, hnv_cv, hnc_len, hcls_512, fun i hi => (hfwd i hi).1, hcls⟩,
    hK', hroot, hrev'⟩

private theorem bv32_shr1_toNat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem bv32_and1_toNat (x : BitVec 32) : (x &&& 1#32).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1#32).toNat = 1 from rfl]
  simp [Nat.and_two_pow_sub_one_eq_mod x.toNat 1]

private theorem bv32_shl1_or_and1 (t l : BitVec 32) (ht : t.toNat < 2 ^ 31) :
    ((t <<< (1 : Nat)) ||| (l &&& 1#32)).toNat = 2 * t.toNat + l.toNat % 2 := by
  have h1 : (l &&& 1#32).toNat < 2 := by rw [bv32_and1_toNat]; omega
  simpa [bv32_and1_toNat] using FullSweepVarHelpers.bv32_shl1_or_pol t (l &&& 1#32) ht h1

private theorem bv64_shl1_toNat (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := by
  have hx := x.isLt
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : x.toNat * 2 < 2 ^ 64)]; omega

private theorem bv64_shl1_add1_toNat (x : BitVec 32) :
    ((x.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  have hx := x.isLt
  rw [BitVec.toNat_add, bv64_shl1_toNat, show (1#64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : 2 * x.toNat + 1 < 2 ^ 64)]

private theorem cone_clause_entails_of_filtered {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} {cr : Nat} {kept : List Nat}
    (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    (href : cr ∈ fullArenaClauseRefsCore k) (hng : fullArenaClauseGarbCore k cr = false)
    (hcov : ∀ l ∈ fullArenaClauseLitsCore k cr, k.vals[l]?.getD 0#8 = 0xFF#8 ∨ l ∈ kept) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause kept) := by
  rw [CNF.entails_clause_def]; intro α hα
  have hent := hw.arena.entails cr href hng; rw [CNF.entails_clause_def] at hent
  obtain ⟨l, hl_mem, hl_sat⟩ := (clause_sat_cnfClause_iff _ _).mp (hent α hα)
  rcases hcov l hl_mem with hfals | hkept
  · exact absurd ((sat_cnfClause_singleton _ _).mpr hl_sat)
      (level0_false_not_sat hw hl0 (hw.arena.lits_lt cr href hng l hl_mem) hfals hα)
  · exact (clause_sat_cnfClause_iff _ _).mpr ⟨l, hkept, hl_sat⟩

private theorem fullArenaClauseLitsCore_mem_iff {k : FullCoreState} {cr l : Nat}
    (hbd : cr + 3 + (k.arena[cr + 2]?.getD 0#32).toNat ≤ k.arena.length) :
    l ∈ fullArenaClauseLitsCore k cr ↔
      ∃ i < (k.arena[cr + 2]?.getD 0#32).toNat, (k.arena[cr + 3 + i]?.getD 0#32).toNat = l := by
  unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
  generalize (k.arena[cr + 2]?.getD 0#32).toNat = sz at hbd ⊢
  simp only [List.mem_map]; constructor
  · rintro ⟨w, hw, rfl⟩; obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hw
    simp only [List.length_take, List.length_drop,
      Nat.min_eq_left (by omega : sz ≤ k.arena.length - (cr + 3))] at hi
    refine ⟨i, hi, ?_⟩; simp only [List.getElem_take, List.getElem_drop] at heq
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, heq]
  · rintro ⟨i, hi, rfl⟩
    have hmem : ((k.arena.drop (cr + 3)).take sz)[i]'(by simp; omega) ∈
        (k.arena.drop (cr + 3)).take sz := List.getElem_mem _
    exact ⟨k.arena[cr + 3 + i]'(by omega),
      by simpa [List.getElem_take, List.getElem_drop] using hmem,
      by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩

private theorem cone_occ_hdr_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_w : FullState} {cr sz : BitVec 32} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hnd : FullArenaVarsNodup s)
    (har_eq : st_w.core.arena = s.core.arena) (hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hsz_core : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (hgr0 : (st_w.core.arena[cr.toNat]'(by
      have := (hw.arena.refs_wf cr.toNat hcr_ref).1; have := hlen.core_ok.arena_len_le
      rw [har_eq, hlen.core_ok.arena_len_arr]; omega) &&& (0x00080000#32 ||| 0x00400000#32)) =
      0#32) :
    fullArenaClauseGarbCore s.core cr.toNat = false ∧
    cr.toNat + 3 + sz.toNat ≤ s.core.arena_len ∧ sz.toNat ≤ s.core.cur_vars ∧
    cr.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
  have hwf := hw.arena.refs_wf cr.toNat hcr_ref
  have hal := hlen.core_ok.arena_len_le; have har := hlen.core_ok.arena_len_arr
  have hng : fullArenaClauseGarbCore s.core cr.toNat = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have h0 := bv32_garb_false_of_and_garb_red hgr0; simp [har_eq] at h0; simp [h0]
  have hsz_le : cr.toNat + 3 + sz.toNat ≤ s.core.arena_len := by have := hwf.2.2; omega
  have hsz_cv : sz.toNat ≤ s.core.cur_vars := by
    have hlen_lits : (fullArenaClauseLits s cr.toNat).length = sz.toNat := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore
      rw [List.length_map, List.length_take, List.length_drop, ← hsz_core]
      exact Nat.min_eq_left (by omega)
    rw [← hlen_lits]
    have hle := nodup_length_le_of_lt (xs := (fullArenaClauseLits s cr.toNat).map (· / 2))
      (n := s.core.cur_vars) (hnd cr.toNat hcr_ref hng) fun v hv => by
        rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
        have := hw.arena.lits_lt cr.toNat hcr_ref hng l hl; omega
    simpa [List.length_map] using hle
  exact ⟨hng, hsz_le, hsz_cv, by omega⟩

private theorem cone_bin_lits_ok {st : FullState}
    {cv qi pol lit ot ov nv : BitVec 32} {iov : Nat}
    (hqi_lt : qi.toNat < nv.toNat) (hnv128 : nv.toNat ≤ 128) (hpol_lt : pol.toNat < 2)
    (hlit_eq : lit.toNat = 2 * cv.toNat + pol.toNat) (hov_eq : ov.toNat = ot.toNat / 2)
    (hiov : iov < nv.toNat)
    (htca : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi.toNat + 1))
    (hwca : (st.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat)
    (htov : st.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = BitVec.ofNat 32 (iov + 1))
    (hwov : (st.scratch.work_stk1[iov]?.getD 0#32).toNat = ov.toNat) :
    let l0 := (((st.scratch.tarjan_mark[cv.toNat]?.getD 0#32) - 1#32) <<< (1 : Nat)) ||| pol
    let l1 := (((st.scratch.tarjan_mark[ov.toNat]?.getD 0#32) - 1#32) <<< (1 : Nat)) |||
      (ot &&& 1#32)
    l0.toNat < 2 * nv.toNat ∧ l1.toNat < 2 * nv.toNat ∧
    fullSweepGlobalLit st l0.toNat = lit.toNat ∧
    fullSweepGlobalLit st l1.toNat = ot.toNat := by
  intro l0 l1
  have hm0 : BitVec.ofNat 32 (qi.toNat + 1) - 1#32 = BitVec.ofNat 32 qi.toNat := by bv_omega
  have hm1 : BitVec.ofNat 32 (iov + 1) - 1#32 = BitVec.ofNat 32 iov := by bv_omega
  have hl0 : l0.toNat = 2 * qi.toNat + pol.toNat := by
    dsimp only [l0]; rw [htca, hm0]
    have := FullSweepVarHelpers.bv32_shl1_or_pol (BitVec.ofNat 32 qi.toNat) pol
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) hpol_lt
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qi.toNat < 2 ^ 32)] using this
  have hl1 : l1.toNat = 2 * iov + ot.toNat % 2 := by
    dsimp only [l1]; rw [htov, hm1]
    have := bv32_shl1_or_and1 (BitVec.ofNat 32 iov) ot
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : iov < 2 ^ 32)] using this
  rw [fullSweepGlobalLit_eq_coneLift']
  refine ⟨by omega, by omega, ?_, by rw [hl1]; exact coneLift_of_tmk_pair hwov hov_eq.symm⟩
  rw [hl0]; simpa [show lit.toNat % 2 = pol.toNat by omega] using
    coneLift_of_tmk_pair (wk := st.scratch.work_stk1) (idx := qi.toNat) (v := cv.toNat)
      (l := lit.toNat) hwca (by omega)

/-! ## 2. `full_sweep_refine_kitten_wp` (`FullDefSweep` #7) -/

theorem full_sweep_refine_kitten_wp (Γ : Env) :
    ∀ args m Q X, fullSweepRefineKittenSpec args m Q X →
      Func.wp Γ full_sweep_refine_kitten_body args m Q X := by
  rintro ⟨h, nv, bit_idx, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcap, hnv128, hnv_mx, hcone, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hws_len := hlen.scratch_ok.work_stk1_len
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  unfold Func.wp full_sweep_refine_kitten_body
  ds_steps
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) ml => i.toNat ≤ nv.toNat ∧ ∃ sig : List (BitVec 64),
      sig.length = c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig } } ⋆ R) ml)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun _ hJ_lp => by
      ds_steps
      exact hJ_lp (0#32, ()) m ⟨Nat.zero_le _, s.scratch.sim_sig, hlen.scratch_ok.sim_sig_len, hm⟩)
    (fun _ (i, ()) ml ⟨hi_le, sig, hsig_len, hml⟩ hJ_lp => by
      ds_split
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
        have hk_bd : 256 + ((928 + (i <<< (1 : Nat))).setWidth 64).toNat <
            st.scratch.scratch_buf.length := by
          rw [hscr_st, bv_c0_zext32_64]
          have hshl : (i <<< (1 : Nat)).toNat = 2 * i.toNat := bv32_shl1_toNat i (by omega)
          have hadd : (928 + (i <<< (1 : Nat))).toNat = 928 + 2 * i.toNat := by
            rw [BitVec.toNat_add, show (928 : BitVec 32).toNat = 928 from rfl, hshl,
              Nat.mod_eq_of_lt (by omega)]
          rw [hadd]; omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := dsSweep_bv32_add1_lt (by omega)
        ds_to_group; refine wp_unroll_group fun _ _ => ?_; ds_split
        all_goals
          ds_csteps!; subst hst_eq
          refine hJ_lp (i + 1#32, ()) _ (by dsimp only; omega) ⟨by omega, _, ?_, by assumption⟩
          simp [hsig_len]
      · ds_steps; exact hQ sig ml hsig_len hml)

/-! ## 3. `full_sweep_cone_wp` (`FullDefSweep` #6) -/

private theorem sweep_cone_call_add_clause {Γ : Env}
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hAddCl : EnvSpec Γ "full_kitten_add_clause" (fullKittenAddClauseSpec KInv))
    {c : FullCfg} {F_cur : List (List Nat)} {s0 st : FullState}
    {root_v nv nc sz : BitVec 32} {cls : List (Nat × List Nat)} {aSz : Arg Val i32}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {k : Tup Val [.bool] → Expr Val Cont [i64]}
    (haSz : aSz.val = sz) (hlen : st.LengthsOk c) (hag : AgreesExcept coneKMask s0 st)
    (hcap : 10240 ≤ c.scratch_cap)
    (hcone : SweepKittenConeOk KInv F_cur st root_v.toNat nv.toNat nc.toNat cls)
    (hnc : nc.toNat < 512) (hsz1 : 1 ≤ sz.toNat) (hsz16 : sz.toNat < 2 ^ 16)
    (hsz_tmp : sz.toNat ≤ st.core.tmp.length)
    (hlts : ∀ j < sz.toNat, (st.core.tmp[j]?.getD 0#32).toNat < 2 * nv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((st.core.tmp.take sz.toNat).map (fun x => fullSweepGlobalLit st x.toNat))))
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ (ok : Bool) (cls' : List (Nat × List Nat)) (st' : FullState) (m' : Mem 64),
      (if ok then nc + 1#32 else nc).toNat = cls'.length →
      (if ok then nc + 1#32 else nc).toNat ≤ 512 →
      st'.LengthsOk c → AgreesExcept coneKMask s0 st' →
      SweepKittenConeOk KInv F_cur st' root_v.toNat nv.toNat
        (if ok then nc + 1#32 else nc).toNat cls' →
      st'.scratch.tarjan_mark = st.scratch.tarjan_mark →
      st'.scratch.work_stk1 = st.scratch.work_stk1 →
      (FullMem c st' ⋆ R) m' →
      wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i64, i32]) (bs := [.bool])
      "full_kitten_add_clause" (Arg.var c.hdr, Arg.var nc, Arg.var c.pTmp, aSz, ()) k) m := by
  have hnv128 : nv.toNat ≤ 128 := hcone.2.1
  have hlts128 : ∀ j < sz.toNat, (st.core.tmp[j]?.getD 0#32).toNat < 2 * 128 :=
    fun j hj => Nat.lt_of_lt_of_le (hlts j hj) (by omega)
  refine wp_call_of_spec _ k ?_
  simp only [vals, Arg.val_var, haSz]
  refine hAddCl (c.hdr, nc, c.pTmp, sz, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, st, 128, cls, false, st.core.tmp, fullSweepAddRestTmp c st ⋆ R,
      rfl, hlen, hcap, hcone.2.2.2.2.2.1, hsz1, hsz16, hsz_tmp, hlts128,
      fullMem_focus_addCl_tmp hm, fun ok scr' m' hsl h256 h18 hKt hKf hm' => ?_⟩
  let st' : FullState := { st with scratch := { st.scratch with scratch_buf := scr' } }
  have hlen' : st'.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hsl }⟩
  have hag' : AgreesExcept coneKMask s0 st' := hag.update _ (fun _ => rfl)
  have hscr18 : scr'[256 + 18]? = some 0#32 := by rw [h18]; exact hcone.2.2.2.2.2.2.1
  have hhdr : Full.hdrTailWords c st' = Full.hdrTailWords c
      { st with scratch := { st.scratch with scratch_buf := scr', res_sz := st.scratch.res_sz } } :=
    rfl
  rw [hhdr] at hm'
  have hm_un := fullMem_unfocus_addCl_tmp hm'
  cases ok
  · obtain ⟨hnv1, _, hnv_cv, hnc_len, hcls512, _, _, hroot, hfwd, hrev, hcls⟩ := hcone
    exact hk false cls st' m'
      (by simp [hnc_len]) (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
      hlen' hag'
      (by simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨hnv1, hnv128, hnv_cv, hnc_len, hcls512, hKf rfl, hscr18, hroot, hfwd, hrev, hcls⟩)
      rfl rfl hm_un
  · have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := dsSweep_bv32_add1_lt (by omega)
    have hc' := sweepKittenConeOk_add_cl hcone hnc hsz_tmp hlts hent hscr18 (hKt rfl)
    exact hk true
      (cls ++ [(nc.toNat, (st.core.tmp.take sz.toNat).map BitVec.toNat)]) st' m'
      (by simp [hnc1, hcone.2.2.2.1]) (by simp only [↓reduceIte]; omega)
      hlen' hag' (by simp only [↓reduceIte, hnc1]; exact hc') rfl rfl hm_un

private theorem sweep_cone_bin_store1_add_clause {Γ : Env}
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hAddCl : EnvSpec Γ "full_kitten_add_clause" (fullKittenAddClauseSpec KInv))
    {c : FullCfg} {F_cur : List (List Nat)} {s0 st : FullState}
    {root_v nv nc l0 l1 : BitVec 32} {cls : List (Nat × List Nat)}
    {aVal : Arg Val i32} {aPtr : Arg Val i64} {aHdr aTmp : Arg Val i64}
    {aNc aTwo : Arg Val i32} {ts_g : List Ty}
    {bodies : Tup Cont [ts_g] → Blocks Val Cont [i64] [ts_g]}
    {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {k : Tup Cont [ts_g] → Tup Val [.bool] → Expr Val Cont [i64]}
    (haVal : aVal.val = l1) (haPtr : aPtr.val = c.pTmp + 4#64)
    (haHdr : aHdr.val = c.hdr) (haNc : aNc.val = nc)
    (haTmp : aTmp.val = c.pTmp) (haTwo : aTwo.val = 2#32)
    (hlen : st.LengthsOk c) (hag : AgreesExcept coneKMask s0 st) (hcap : 10240 ≤ c.scratch_cap)
    (hcone : SweepKittenConeOk KInv F_cur st root_v.toNat nv.toNat nc.toNat cls)
    (hnc : nc.toNat < 512) (ht0 : st.core.tmp[0]? = some l0)
    (hl0 : l0.toNat < 2 * nv.toNat) (hl1 : l1.toNat < 2 * nv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [fullSweepGlobalLit st l0.toNat, fullSweepGlobalLit st l1.toNat]))
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ (J_g : Cont ts_g),
      (∀ xs m', wp Γ Q X (Blocks.get (bodies (J_g, ())) .here xs) m' → J_g xs m') →
      ∀ (ok : Bool) (cls' : List (Nat × List Nat)) (st' : FullState) (m' : Mem 64),
      (if ok then nc + 1#32 else nc).toNat = cls'.length →
      (if ok then nc + 1#32 else nc).toNat ≤ 512 →
      st'.LengthsOk c → AgreesExcept coneKMask s0 st' →
      SweepKittenConeOk KInv F_cur st' root_v.toNat nv.toNat
        (if ok then nc + 1#32 else nc).toNat cls' →
      st'.scratch.tarjan_mark = st.scratch.tarjan_mark →
      st'.scratch.work_stk1 = st.scratch.work_stk1 →
      (FullMem c st' ⋆ R) m' →
      wp Γ Q X (k (J_g, ()) (ok, ())) m') :
    wp Γ Q X (Expr.store (t := i32) aVal aPtr
      (Expr.group (sig := [ts_g]) bodies fun Js =>
        Expr.call (as := [i64, i32, i64, i32]) (bs := [.bool]) "full_kitten_add_clause"
          (aHdr, aNc, aTmp, aTwo, ()) (k Js))) m := by
  have htmp_len := hlen.core_ok.tmp_len_arr
  have hmv_pos : 1 ≤ c.max_vars := by
    have := hcone.1; have := hcone.2.2.1; have := hlen.core_ok.cur_vars_le; omega
  by_cases hmv2 : 2 ≤ c.max_vars
  · have hst1 := store_full_tmp (c := c) (s := st) (i := 1) l1 (by omega) hm
    rw [← haVal, ← show aPtr.val = c.pTmp + 4#64 from haPtr] at hst1
    refine wp_store_sep hst1 fun m2 hm2 => ?_; rw [haVal] at hm2
    refine wp_unroll_group fun J_g hJ_g => ?_
    let st2 : FullState := { st with core := { st.core with tmp := st.core.tmp.set 1 l1 } }
    have h0 : st.core.tmp[0]'(by omega) = l0 := by
      rw [List.getElem?_eq_getElem (by omega)] at ht0; exact Option.some.inj ht0
    have htmp0 : st2.core.tmp[0]'(by simp [st2, htmp_len]; omega) = l0 := by
      simp [st2, List.getElem_set_ne, h0]
    have htmp1 : st2.core.tmp[1]'(by simp [st2, htmp_len]; omega) = l1 := by
      simp [st2, List.getElem_set_self]
    have htk : st2.core.tmp.take 2 = [l0, l1] := List.ext_getElem
      (by simp [st2, htmp_len]; omega) fun j _ hj2 => by
        rcases (by simp at hj2; omega : j = 0 ∨ j = 1) with rfl | rfl <;>
          simpa [List.getElem_take] using (by first | exact htmp0 | exact htmp1)
    have hent2 : (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((st2.core.tmp.take (2#32 : BitVec 32).toNat).map
          (fun x => fullSweepGlobalLit st2 x.toNat))) := by
      have hfg : ∀ x, fullSweepGlobalLit st2 x = fullSweepGlobalLit st x := fun _ => rfl
      rw [show (2#32 : BitVec 32).toNat = 2 from rfl, htk]
      simpa only [List.map_cons, List.map_nil, hfg] using hent
    have hnv128 : nv.toNat ≤ 128 := hcone.2.1
    have hlts128 : ∀ j < (2#32 : BitVec 32).toNat, (st2.core.tmp[j]?.getD 0#32).toNat < 2 * 128 :=
      fun j hj => by
        have hj2 : j < 2 := by simpa [show (2#32 : BitVec 32).toNat = 2 from rfl] using hj
        rw [List.getElem?_eq_getElem (by simp [st2, htmp_len]; omega), Option.getD_some]
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · rw [htmp0]; exact Nat.lt_of_lt_of_le hl0 (by omega)
        · rw [htmp1]; exact Nat.lt_of_lt_of_le hl1 (by omega)
    refine wp_call_of_spec _ (k (J_g, ())) ?_
    simp only [vals, haHdr, haNc, haTmp, haTwo]
    refine hAddCl (c.hdr, nc, c.pTmp, 2#32, ()) m2 (fun r m' => wp Γ Q X (k (J_g, ()) r) m') X
      ⟨c, st2, 128, cls, false, st2.core.tmp, fullSweepAddRestTmp c st2 ⋆ R,
        rfl, ⟨{ hlen.core_ok with tmp_len_arr := by simp [st2, htmp_len] }, hlen.scratch_ok⟩,
        hcap, hcone.2.2.2.2.2.1, by decide, by decide,
        by simp [st2, htmp_len, show (2#32).toNat = 2 from rfl]; omega, hlts128,
        fullMem_focus_addCl_tmp hm2, fun ok scr' m' hsl h256 h18 hKt hKf hm' => ?_⟩
    let st' : FullState := { st2 with scratch := { st2.scratch with scratch_buf := scr' } }
    have hlen' : st'.LengthsOk c :=
      ⟨{ hlen.core_ok with tmp_len_arr := by simp [st', st2, htmp_len] },
       { hlen.scratch_ok with scratch_buf_len := hsl }⟩
    have hag' : AgreesExcept coneKMask s0 st' := (hag.update _ fun _ => rfl).update _ fun _ => rfl
    have hscr18 : scr'[256 + 18]? = some 0#32 := by rw [h18]; exact hcone.2.2.2.2.2.2.1
    have hhdr : Full.hdrTailWords c st' = Full.hdrTailWords c { st2 with
        scratch := { st2.scratch with scratch_buf := scr', res_sz := st2.scratch.res_sz } } :=
      rfl
    rw [hhdr] at hm'
    have hm_un := fullMem_unfocus_addCl_tmp hm'
    have hcone2 : SweepKittenConeOk KInv F_cur st2 root_v.toNat nv.toNat nc.toNat cls :=
      sweepKittenConeOk_tmp_irrel hcone
    cases ok
    · obtain ⟨hnv1, _, hnv_cv, hnc_len, hcls512, _, _, hroot, hfwd, hrev, hcls⟩ := hcone2
      exact hk J_g hJ_g false cls st' m'
        (by simp [hnc_len]) (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
        hlen' hag'
        (by simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨hnv1, hnv128, hnv_cv, hnc_len, hcls512, hKf rfl, hscr18, hroot, hfwd, hrev,
              hcls⟩)
        rfl rfl hm_un
    · have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := dsSweep_bv32_add1_lt (by omega)
      have hc' := sweepKittenConeOk_add_cl hcone2 hnc
        (by simp [st2, htmp_len, show (2#32).toNat = 2 from rfl]; omega)
        (fun j hj => by
          have hj2 : j < 2 := by simpa [show (2#32 : BitVec 32).toNat = 2 from rfl] using hj
          rw [List.getElem?_eq_getElem (by simp [st2, htmp_len]; omega), Option.getD_some]
          rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
          · rw [htmp0]; exact hl0
          · rw [htmp1]; exact hl1)
        hent2 hscr18 (hKt rfl)
      exact hk J_g hJ_g true
        (cls ++ [(nc.toNat, (st2.core.tmp.take (2#32 : BitVec 32).toNat).map BitVec.toNat)])
        st' m' (by simp [hnc1, hcone.2.2.2.1]) (by simp only [↓reduceIte]; omega)
        hlen' hag' (by simp only [↓reduceIte, hnc1]; exact hc') rfl rfl hm_un
  · have hmv1 : c.max_vars = 1 := by omega
    have ht_eq : st.core.tmp = [l0] := match h : st.core.tmp with
      | [] => by rw [h] at htmp_len; simp at htmp_len; omega
      | [x] => by rw [h] at ht0; simp at ht0; rw [ht0]
      | _ :: _ :: _ => by rw [h] at htmp_len; simp at htmp_len; omega
    obtain ⟨w1, hmem⟩ := fullMem_focus_tmp2_of_mv1 hmv1 ht_eq hm
    have hsep_tmp : ∀ {A B C D : Mem 64 → Prop} {k : Mem 64},
        (A ⋆ B ⋆ C ⋆ D) k → (C ⋆ (A ⋆ B ⋆ D)) k := fun h => by ecancel
    have hsep_untmp : ∀ {A B C D : Mem 64 → Prop} {k : Mem 64},
        (C ⋆ (A ⋆ B ⋆ D)) k → (A ⋆ B ⋆ C ⋆ D) k := fun h => by ecancel
    have hst1 : storeOk m i32 (c.pTmp + 4#64) ∧
        (array (t := i32) c.pTmp [l0, l1] ⋆ (array64 (c.hdr + 32) (Full.hdrTailWords c st) ⋆
          array (t := i32) c.pScratchBuf st.scratch.scratch_buf ⋆
          (fullSweepAddRestTmp1 c st ⋆ R))) (storeMem m i32 (c.pTmp + 4#64) l1) := by
      simpa [show i32.bytes = 4 from rfl] using
        store_array (t := i32) (i := 1) l1 (by decide) (by simp) (hsep_tmp hmem)
    rw [← haVal, ← haPtr] at hst1
    refine wp_store_sep hst1 fun m2 hm2 => ?_; rw [haVal] at hm2
    refine wp_unroll_group fun J_g hJ_g => ?_
    have hnv128 : nv.toNat ≤ 128 := hcone.2.1
    have hlts128 : ∀ k < (2#32 : BitVec 32).toNat, ([l0, l1][k]?.getD 0#32).toNat < 2 * 128 :=
      fun k hk => by
        rcases (by simp [show (2#32).toNat = 2 from rfl] at hk; omega : k = 0 ∨ k = 1) with
          rfl | rfl <;> exact Nat.lt_of_lt_of_le (by first | exact hl0 | exact hl1) (by omega)
    refine wp_call_of_spec _ (k (J_g, ())) ?_
    simp only [vals, haHdr, haNc, haTmp, haTwo]
    refine hAddCl (c.hdr, nc, c.pTmp, 2#32, ()) m2 (fun r m' => wp Γ Q X (k (J_g, ()) r) m') X
      ⟨c, st, 128, cls, false, [l0, l1], fullSweepAddRestTmp1 c st ⋆ R,
        rfl, hlen, hcap, hcone.2.2.2.2.2.1, by decide, by decide, by simp, hlts128,
        hsep_untmp hm2, fun ok scr' m' hsl h256 h18 hKt hKf hm' => ?_⟩
    let st' : FullState := { st with scratch := { st.scratch with scratch_buf := scr' } }
    have hlen' : st'.LengthsOk c :=
      ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hsl }⟩
    have hag' : AgreesExcept coneKMask s0 st' := hag.update _ (fun _ => rfl)
    have hscr18 : scr'[256 + 18]? = some 0#32 := by rw [h18]; exact hcone.2.2.2.2.2.2.1
    have hhdr : Full.hdrTailWords c st' = Full.hdrTailWords c { st with
        scratch := { st.scratch with scratch_buf := scr', res_sz := st.scratch.res_sz } } :=
      rfl
    rw [hhdr] at hm'
    have hcore_l0 : ({ st.core with tmp := [l0] } : FullCoreState) = st.core := by
      cases h : st.core; simp [h] at ht_eq; simp [ht_eq]
    have hm_un : (FullMem c st' ⋆ R) m' := by
      have hm1 := fullMem_unfocus_tmp2_of_mv1 hmv1 hm'
      simpa only [st', hcore_l0] using hm1
    cases ok
    · obtain ⟨hnv1, _, hnv_cv, hnc_len, hcls512, _, _, hroot, hfwd, hrev, hcls⟩ := hcone
      exact hk J_g hJ_g false cls st' m'
        (by simp [hnc_len]) (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
        hlen' hag'
        (by simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨hnv1, hnv128, hnv_cv, hnc_len, hcls512, hKf rfl, hscr18, hroot, hfwd, hrev,
              hcls⟩)
        rfl rfl hm_un
    · have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := dsSweep_bv32_add1_lt (by omega)
      have hK_new : KInv 128 (cls ++ [(nc.toNat, [l0.toNat, l1.toNat])]) false .fresh scr' := by
        simpa [show (2#32).toNat = 2 from rfl] using hKt rfl
      have hc' : SweepKittenConeOk KInv F_cur st' root_v.toNat nv.toNat (nc.toNat + 1)
          (cls ++ [(nc.toNat, [l0.toNat, l1.toNat])]) := by
        have ht := sweepKittenConeOk_add_cl (xs := [l0, l1]) (sz := 2) hcone hnc (by simp)
          (fun j hj => by rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [hl0, hl1])
          (by simpa using hent) hscr18 (by simpa using hK_new)
        simpa using ht
      exact hk J_g hJ_g true (cls ++ [(nc.toNat, [l0.toNat, l1.toNat])]) st' m'
        (by simp [hnc1, hcone.2.2.2.1]) (by simp only [↓reduceIte]; omega)
        hlen' hag' (by simp only [↓reduceIte, hnc1]; exact hc') rfl rfl hm_un

private theorem sweep_cone_k_unassigned_step {c : FullCfg}
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    {F_cur : List (List Nat)} {s st_k st_u : FullState}
    {root_v cr sz k cnt nv_k nv_u lit_k : BitVec 32} {nc_w ilv : Nat}
    {cls_w : List (Nat × List Nat)}
    (hlu : st_u.LengthsOk c) (htmpu_eq : st_u.core.tmp = st_k.core.tmp)
    (hwku_eq : ∀ j < nv_k.toNat, st_u.scratch.work_stk1[j]? = st_k.scratch.work_stk1[j]?)
    (hnvku : nv_k.toNat ≤ nv_u.toNat) (hnvu128 : nv_u.toNat ≤ 128)
    (hk_lt : k.toNat < sz.toNat) (hsz_le8 : sz.toNat ≤ 8) (hsz_cv : sz.toNat ≤ s.core.cur_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcnt_le : cnt.toNat ≤ k.toNat)
    (hlit_ar : (s.core.arena[cr.toNat + 3 + k.toNat]?.getD 0#32).toNat = lit_k.toNat)
    (hilv : ilv < nv_u.toNat)
    (hwlv : (st_u.scratch.work_stk1[ilv]?.getD 0#32).toNat = lit_k.toNat / 2)
    (htlv_v : st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 = BitVec.ofNat 32 (ilv + 1))
    (hlts_k : ∀ j < cnt.toNat, (st_k.core.tmp[j]?.getD 0#32).toNat < 2 * nv_k.toNat)
    (hcov_k : ∀ i < k.toNat,
      let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
      l ∈ (st_k.core.tmp.take cnt.toNat).map (fun x => fullSweepGlobalLit st_k x.toNat))
    (_hc_u : SweepKittenConeOk KInv F_cur st_u root_v.toNat nv_u.toNat nc_w cls_w) :
    let new_l : BitVec 32 :=
      (((st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32) - 1#32) <<< (1 : Nat)) |||
        (lit_k &&& 1#32)
    let st_u' : FullState :=
      { st_u with core := { st_u.core with tmp := st_u.core.tmp.set cnt.toNat new_l } }
    (cnt + 1#32).toNat = cnt.toNat + 1 ∧ st_u'.LengthsOk c ∧
    (∀ j < (cnt + 1#32).toNat, (st_u'.core.tmp[j]?.getD 0#32).toNat < 2 * nv_u.toNat) ∧
    (∀ i < (k + 1#32).toNat,
      let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
      l ∈ (st_u'.core.tmp.take (cnt + 1#32).toNat).map
        (fun x => fullSweepGlobalLit st_u' x.toNat)) := by
  intro new_l st_u'
  have htmp_u := hlu.core_ok.tmp_len_arr
  have htmp_k : st_k.core.tmp.length = c.max_vars := htmpu_eq ▸ htmp_u
  have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by bv_omega
  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
  have hm1 : BitVec.ofNat 32 (ilv + 1) - 1#32 = BitVec.ofNat 32 ilv := by bv_omega
  have hnew_n : new_l.toNat = 2 * ilv + lit_k.toNat % 2 := by
    simp only [new_l, htlv_v, hm1]
    have := bv32_shl1_or_and1 (BitVec.ofNat 32 ilv) lit_k
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ilv < 2 ^ 32)] using this
  have hnew_lift : fullSweepGlobalLit st_u' new_l.toNat = lit_k.toNat := by
    rw [fullSweepGlobalLit_eq_coneLift', hnew_n]
    exact coneLift_of_tmk_pair hwlv rfl
  have htake_u' : st_u'.core.tmp.take (cnt + 1#32).toNat =
      st_u.core.tmp.take cnt.toNat ++ [new_l] := by
    have hlen_tk : (st_u.core.tmp.take cnt.toNat).length = cnt.toNat := by simp [htmp_u]; omega
    rw [hcnt1]; dsimp only [st_u']; apply List.ext_getElem; · simp [htmp_u]; omega
    intro j hj1 _; have hj : j < cnt.toNat + 1 := by simp [htmp_u] at hj1; omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [List.getElem_take, List.getElem_set_ne (by omega : cnt.toNat ≠ j),
        List.getElem_append_left (by omega), List.getElem_take]
    · simp [List.getElem_take, List.getElem_set_self, List.getElem_append_right, hlen_tk]
  refine ⟨hcnt1, ⟨{ hlu.core_ok with tmp_len_arr := by simp [st_u', htmp_u] }, hlu.scratch_ok⟩,
    fun j hj => ?_, fun i hi => ?_⟩
  · rw [hcnt1] at hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · dsimp only [st_u']; rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j), htmpu_eq]
      exact Nat.lt_of_lt_of_le (hlts_k j hlt) (by omega)
    · dsimp only [st_u']; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
  · rw [hk1] at hi; rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · rcases hcov_k i hlt with hfals | hmem
      · exact Or.inl hfals
      · right; rw [htake_u', List.map_append]; apply List.mem_append_left
        rcases List.mem_map.mp hmem with ⟨x, hx, heq_l⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        have hj_cnt : j < cnt.toNat := by simp at hj; omega
        have hx_lt := hlts_k j hj_cnt
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx_lt
        have hwk_eq_x : st_u.scratch.work_stk1[(st_k.core.tmp[j]'(by omega)).toNat / 2]? =
            st_k.scratch.work_stk1[(st_k.core.tmp[j]'(by omega)).toNat / 2]? :=
          hwku_eq _ (by omega)
        refine List.mem_map.mpr ⟨st_u.core.tmp[j]'(by omega), ?_, ?_⟩
        · have hmem' : (st_u.core.tmp.take cnt.toNat)[j]'(by simp [htmp_u]; omega) ∈
              st_u.core.tmp.take cnt.toNat := List.getElem_mem _
          simpa [List.getElem_take] using hmem'
        · rw [← heq_l]; simp only [List.getElem_take, fullSweepGlobalLit, st_u', htmpu_eq, hwk_eq_x]
    · right; rw [htake_u', List.map_append]
      exact List.mem_append_right _ (by simp [hlit_ar, hnew_lift])

private noncomputable def coneOccClauseExpr (J_w : Cont [i32, i32, i64])
    (hPtr tmpPtr arPtr valsPtr tmkPtr ws1Ptr : Val i64)
    (nv_w nc_w crLd szLd : Val i32) (pNext : Val i64) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i32, .bool, i32, i32]])
    (fun Js => Blocks.cons (fun (p_70 : Tup Val [i32, .bool, i32, i32]) =>
      Expr.group (sig := [[i32]])
        (fun Js => Blocks.cons (fun (p : Tup Val [i32]) =>
          Expr.jump J_w (Arg.var p_70.fst, Arg.var p.fst, Arg.var pNext, ())) Blocks.nil)
        (fun Js => Expr.jnz (Arg.var p_70.snd.fst)
          (Expr.jump Js.fst (Arg.var nc_w, ()))
          (Expr.let_ (Op.mk (OpCode.cmp CmpOp.uge i32 .bool (by decide))
            (Arg.var p_70.snd.snd.fst, Arg.imm 2, ())) fun p_71 =>
            Expr.jnz (Arg.var p_71.fst)
              (Expr.call (as := [i64, i32, i64, i32]) (bs := [.bool])
                "full_kitten_add_clause"
                (Arg.var hPtr, Arg.var nc_w, Arg.var tmpPtr, Arg.var p_70.snd.snd.fst, ())
                fun p => Expr.jnz (Arg.var p.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nc_w, Arg.imm 1, ())) fun p =>
                    Expr.jump Js.fst (Arg.var p.fst, ()))
                  (Expr.jump Js.fst (Arg.var nc_w, ())))
              (Expr.jump Js.fst (Arg.var nc_w, ()))))) Blocks.nil)
    (fun Js => Expr.group (sig := [[i32, i32, i32]])
      (fun Js_4 => Blocks.cons (fun (p : Tup Val [i32, i32, i32]) =>
        Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32 .bool (by decide))
          (Arg.var p.snd.snd.fst, Arg.var szLd, ())) fun p_70 =>
          Expr.jnz (Arg.var p_70.fst)
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var crLd, ())) fun p_71 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_71.fst, Arg.imm 3, ())) fun p_72 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.snd.snd.fst, ())) fun p_73 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_72.fst, Arg.var p_73.fst, ())) fun p_74 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_74.fst, Arg.imm 4, ())) fun p_75 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var arPtr, Arg.var p_75.fst, ())) fun p_76 =>
            Expr.load i32 (Arg.var p_76.fst) fun ld_15 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_15, ())) fun p_77 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var valsPtr, Arg.var p_77.fst, ())) fun p_78 =>
            Expr.load i8 (Arg.var p_78.fst) fun ld_16 =>
            Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_79 =>
            Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_16, ())) fun p_80 =>
            Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_79.fst, ())) fun p_81 =>
            Expr.let_ (Op.mk (OpCode.cmp CmpOp.sgt i32 .bool (by decide))
              (Arg.var p_80.fst, Arg.var p_81.fst, ())) fun p_82 =>
              Expr.jnz (Arg.var p_82.fst)
                (Expr.jump Js.fst (Arg.var p.fst, Arg.imm true, Arg.var p.snd.fst,
                  Arg.var p.snd.snd.fst, ()))
                (Expr.group (sig := [[i32, .bool, i32]]) (fun Js_g => Blocks.cons
                  (fun (p_83 : Tup Val [i32, .bool, i32]) =>
                    Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.snd.snd.fst, Arg.imm 1, ()))
                      fun p_1 => Expr.jump Js_4.fst (Arg.var p_83.fst, Arg.var p_83.snd.snd.fst,
                        Arg.var p_1.fst, ())) Blocks.nil)
                  (fun Js_5 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_15, ())) fun p_83 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var valsPtr, Arg.var p_83.fst, ()))
                      fun p_84 => Expr.load i8 (Arg.var p_84.fst) fun ld_17 =>
                    Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_85 =>
                    Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_17, ())) fun p_86 =>
                    Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_85.fst, ())) fun p_87 =>
                    Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32 .bool (by decide))
                      (Arg.var p_86.fst, Arg.var p_87.fst, ())) fun p_88 =>
                      Expr.jnz (Arg.var p_88.fst)
                        (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld_15, Arg.imm 1, ()))
                          fun p_89 => Expr.group (sig := [[i32]])
                            (fun Js_6 => Blocks.cons (fun p_90 =>
                              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_89.fst, ()))
                                fun p_91 =>
                              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_91.fst, Arg.imm 4, ()))
                                fun p_92 =>
                              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var tmkPtr, Arg.var p_92.fst,
                                ())) fun p_93 =>
                              Expr.load i32 (Arg.var p_93.fst) fun ld =>
                              Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32 .bool (by decide))
                                (Arg.var ld, Arg.imm 0, ())) fun p_94 =>
                              Expr.jnz (Arg.var p_94.fst)
                                (Expr.jump Js.fst (Arg.var p_90.fst, Arg.imm true,
                                  Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
                                (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.snd.fst, ()))
                                  fun p_95 =>
                                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_95.fst, Arg.imm 4, ()))
                                  fun p_96 =>
                                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var tmpPtr, Arg.var p_96.fst,
                                  ())) fun p_97 =>
                                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_89.fst, ()))
                                  fun p_98 =>
                                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_98.fst, Arg.imm 4, ()))
                                  fun p_99 =>
                                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var tmkPtr, Arg.var p_99.fst,
                                  ())) fun p_100 =>
                                Expr.load i32 (Arg.var p_100.fst) fun ld =>
                                Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var ld, Arg.imm 1, ()))
                                  fun p_101 =>
                                Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var p_101.fst, Arg.imm 1,
                                  ())) fun p_102 =>
                                Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld_15, Arg.imm 1, ()))
                                  fun p_103 =>
                                Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p_102.fst,
                                  Arg.var p_103.fst, ())) fun p_104 =>
                                Expr.store (t := i32) (Arg.var p_104.fst) (Arg.var p_97.fst)
                                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.snd.fst, Arg.imm 1,
                                    ())) fun p_1 =>
                                    Expr.jump Js_5.fst (Arg.var p_90.fst, Arg.imm false,
                                      Arg.var p_1.fst, ()))))
                              Blocks.nil)
                            (fun Js_t =>
                              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_89.fst, ()))
                                fun p_90 =>
                              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_90.fst, Arg.imm 4, ()))
                                fun p_91 =>
                              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var tmkPtr, Arg.var p_91.fst,
                                ())) fun p_92 =>
                              Expr.load i32 (Arg.var p_92.fst) fun ld_18 =>
                              Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32 .bool (by decide))
                                (Arg.var ld_18, Arg.imm 0, ())) fun p_93 =>
                              Expr.jnz (Arg.var p_93.fst)
                                (Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32 .bool (by decide))
                                  (Arg.var p.fst, Arg.imm 128, ())) fun p_94 =>
                                  Expr.jnz (Arg.var p_94.fst)
                                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1,
                                      ())) fun p_1 =>
                                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_89.fst, ()))
                                      fun p_95 =>
                                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_95.fst, Arg.imm 4,
                                      ())) fun p_96 =>
                                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var tmkPtr,
                                      Arg.var p_96.fst, ())) fun p_97 =>
                                    Expr.store (t := i32) (Arg.var p_1.fst) (Arg.var p_97.fst)
                                      (Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var p_1.fst,
                                        Arg.imm 1, ())) fun p_98 =>
                                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_98.fst, ()))
                                        fun p_99 =>
                                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_99.fst,
                                        Arg.imm 4, ())) fun p_100 =>
                                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ws1Ptr,
                                        Arg.var p_100.fst, ())) fun p_101 =>
                                      Expr.store (t := i32) (Arg.var p_89.fst) (Arg.var p_101.fst)
                                        (Expr.jump Js_t.fst (Arg.var p_1.fst, ()))))
                                    (Expr.jump Js_t.fst (Arg.var p.fst, ())))
                                (Expr.jump Js_t.fst (Arg.var p.fst, ()))))
                        (Expr.jump Js_5.fst (Arg.var p.fst, Arg.imm false,
                          Arg.var p.snd.fst, ())))))
            (Expr.jump Js.fst (Arg.var p.fst, Arg.imm false, Arg.var p.snd.fst,
              Arg.var p.snd.snd.fst, ())))
        Blocks.nil)
      (fun Js => Expr.jump Js.fst (Arg.var nv_w, Arg.imm 0, Arg.imm 0, ())))

private theorem sweep_cone_occ_clause_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {J_w : Cont [i32, i32, i64]}
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hAddCl : EnvSpec Γ "full_kitten_add_clause" (fullKittenAddClauseSpec KInv))
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st_w : FullState}
    {R : Mem 64 → Prop} {mw : Mem 64} {root_v nv nv_w nc_w cr crLd sz szLd cv qi : BitVec 32}
    {pNext hPtr tmpPtr arPtr valsPtr tmkPtr ws1Ptr : BitVec 64} {cls_w : List (Nat × List Nat)}
    (hh : hPtr = c.hdr) (htmp : tmpPtr = c.pTmp) (har : arPtr = c.pArena)
    (hvals : valsPtr = c.pVals) (htmkp : tmkPtr = c.pTarjanMark) (hws1p : ws1Ptr = c.pWorkStk1)
    (hcrEq : crLd = cr) (hszEq : szLd = sz)
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core) (_hnd : FullArenaVarsNodup s)
    (hcl0 : s.core.cur_level = 0) (h10240 : 10240 ≤ c.scratch_cap)
    (hqi_lt : qi.toNat < nv.toNat) (hncw_lt : nc_w.toNat < 512)
    (hnv_w_mono : nv.toNat ≤ nv_w.toNat)
    (hlen_w : st_w.LengthsOk c) (hag_w : AgreesExcept coneKMask s st_w)
    (hcone_w : SweepKittenConeOk KInv F_cur st_w root_v.toNat nv_w.toNat nc_w.toNat cls_w)
    (htmk_w : st_w.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi.toNat + 1))
    (hwk_w : (st_w.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng : fullArenaClauseGarbCore s.core cr.toNat = false)
    (hsz_core : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (hsz_ge3 : 3 ≤ sz.toNat) (hsz_le8 : sz.toNat ≤ 8)
    (_hcr_sz_le : cr.toNat + 3 + sz.toNat ≤ s.core.arena_len)
    (hsz_cv : sz.toNat ≤ s.core.cur_vars)
    (hcr3_bd : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hmw : (FullMem c st_w ⋆ R) mw)
    (hstep_occ : ∀ (nv_x nc_x : BitVec 32) (cls_x : List (Nat × List Nat)) (st_x : FullState)
        (mx : Mem 64),
        nv.toNat ≤ nv_x.toNat → st_x.LengthsOk c → AgreesExcept coneKMask s st_x →
        SweepKittenConeOk KInv F_cur st_x root_v.toNat nv_x.toNat nc_x.toNat cls_x →
        st_x.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi.toNat + 1) →
        (st_x.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat →
        (FullMem c st_x ⋆ R) mx → J_w (nv_x, nc_x, pNext, ()) mx) :
    wp Γ Q X
      (coneOccClauseExpr J_w hPtr tmpPtr arPtr valsPtr tmkPtr ws1Ptr nv_w nc_w crLd szLd pNext)
      mw := by
  subst hPtr tmpPtr arPtr valsPtr tmkPtr ws1Ptr crLd szLd
  have hacap_lt := c.harena; have hcv_le := hlen.core_ok.cur_vars_le
  have har_s := hlen.core_ok.arena_len_arr; have hal_le := hlen.core_ok.arena_len_le
  have hsz_ar : (s.core.arena[cr.toNat + 2]?.getD 0#32).toNat = sz.toNat := hsz_core.symm
  unfold coneOccClauseExpr
  refine wp_unroll_group fun _ _ => ?_
  ds_to_group
  refine wp_loop_inv (ts := [i32, i32, i32])
    (fun (nv_k, cnt, idx, ()) mk =>
      idx.toNat ≤ sz.toNat ∧ cnt.toNat ≤ idx.toNat ∧ nv.toNat ≤ nv_k.toNat ∧
      ∃ st_k : FullState,
        st_k.LengthsOk c ∧ AgreesExcept coneKMask s st_k ∧
        SweepKittenConeOk KInv F_cur st_k root_v.toNat nv_k.toNat nc_w.toNat cls_w ∧
        st_k.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi.toNat + 1) ∧
        (st_k.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
        (∀ j < cnt.toNat, (st_k.core.tmp[j]?.getD 0#32).toNat < 2 * nv_k.toNat) ∧
        (∀ i < idx.toNat,
          let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
          s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
          l ∈ (st_k.core.tmp.take cnt.toNat).map (fun x => fullSweepGlobalLit st_k x.toNat)) ∧
        (FullMem c st_k ⋆ R) mk)
    (fun (_, _, idx, ()) _ => sz.toNat - idx.toNat)
    (fun _ hJ_k => by
      ds_steps
      exact hJ_k (nv_w, 0#32, 0#32, ()) mw
        ⟨Nat.zero_le _, Nat.zero_le _, hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w,
         fun _ hj => by simp at hj, fun _ hi => by simp at hi, hmw⟩)
    (fun _ (nv_k, cnt, idx, ()) mk
        ⟨hk_le, hcnt_le, hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k, hwk_k, hlts_k, hcov_k,
         hmk⟩ hJ_k => by
      ds_split; rotate_left
      · have hidx_ge : sz.toNat ≤ idx.toNat := by bv_omega
        have hk_eq : idx.toNat = sz.toNat := Nat.le_antisymm hk_le hidx_ge
        ds_steps
        ds_split; rotate_left
        · ds_steps
          exact hstep_occ nv_k nc_w cls_w st_k mk hnv_k_mono hlen_k hag_k hcone_k htmk_k hwk_k hmk
        have hcnt_ge2 : 2 ≤ cnt.toNat := by simpa using hc
        have hcnt_le8 : cnt.toNat ≤ 8 := Nat.le_trans hcnt_le (Nat.le_trans hk_le hsz_le8)
        have hcnt_tmp : cnt.toNat ≤ st_k.core.tmp.length := by
          rw [hlen_k.core_ok.tmp_len_arr]
          exact Nat.le_trans hcnt_le (Nat.le_trans hk_le (Nat.le_trans hsz_cv hcv_le))
        have hent_ke : (cnfOfClauses F_cur).EntailsClause (cnfClause
            ((st_k.core.tmp.take cnt.toNat).map (fun x => fullSweepGlobalLit st_k x.toNat))) := by
          refine cone_clause_entails_of_filtered hw hcl0 hcr_ref hng fun l hl => ?_
          obtain ⟨i, hi, rfl⟩ :=
            (fullArenaClauseLitsCore_mem_iff (by rw [hsz_ar]; exact hcr3_bd)).mp hl
          rw [hsz_ar] at hi
          exact hcov_k i (hk_eq.symm ▸ hi)
        ds_steps
        refine sweep_cone_call_add_clause hAddCl (aSz := Arg.var cnt) rfl hlen_k hag_k h10240
          hcone_k hncw_lt (Nat.le_trans (by decide) hcnt_ge2)
          (Nat.lt_of_le_of_lt hcnt_le8 (by decide)) hcnt_tmp hlts_k hent_ke hmk ?_
        · intro ok cls' st' m' _ _ hl' ha' hc' ht_eq hw_eq hm'
          ds_split
          · ds_steps
            exact hstep_occ nv_k _ cls' st' m' hnv_k_mono hl' ha'
              (by simpa only [hc, ↓reduceIte, show (1#32 : BitVec 32) = 1 from rfl] using hc')
              (ht_eq ▸ htmk_k) (hw_eq ▸ hwk_k) hm'
          · ds_steps
            exact hstep_occ nv_k _ cls' st' m' hnv_k_mono hl' ha'
              (by simpa only [hc, Bool.false_eq_true, ↓reduceIte] using hc')
              (ht_eq ▸ htmk_k) (hw_eq ▸ hwk_k) hm'
      · have hk_lt : idx.toNat < sz.toNat := by bv_omega
        have hae_k := hag_k.get (·.core.arena)
        have hve_k := hag_k.get (·.core.vals)
        have har_k := hlen_k.core_ok.arena_len_arr
        have hvals_k := hlen_k.core_ok.vals_len
        have hidx_k : (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 idx).toNat =
            cr.toNat + 3 + idx.toNat := by
          unfold dimacsBound at hacap_lt
          simp only [bv_c0_zext32_64, BitVec.toNat_add,
            show (3#64 : BitVec 64).toNat = 3 from rfl]
          omega
        have hidx_bd : (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 idx).toNat <
            st_k.core.arena.length := by
          rw [har_k, hidx_k]; omega
        have hl_in_cl :
            (st_k.core.arena[cr.toNat + 3 + idx.toNat]'(by rw [har_k]; omega)).toNat ∈
              fullArenaClauseLitsCore s.core cr.toNat := by
          rw [fullArenaClauseLitsCore_mem_iff (by rw [hsz_ar]; exact hcr3_bd)]
          refine ⟨idx.toNat, by rw [hsz_ar]; exact hk_lt, ?_⟩
          rw [List.getElem?_eq_getElem (by rw [← hae_k, har_k]; omega), Option.getD_some]
          simp [hae_k]
        have hl_lt_s :
            (st_k.core.arena[(BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 idx).toNat]'
                hidx_bd).toNat < 2 * s.core.cur_vars := by
          simpa only [hidx_k] using hw.arena.lits_lt cr.toNat hcr_ref hng _ hl_in_cl
        let lit_k : BitVec 32 :=
          st_k.core.arena[(BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 idx).toNat]'hidx_bd
        have hval_bd : lit_k.toNat < st_k.core.vals.length := by
          rw [hvals_k]; dsimp only [lit_k]; omega
        have hval_k_eq : st_k.core.vals[lit_k.toNat]'hval_bd =
            s.core.vals[lit_k.toNat]?.getD 0#8 := by
          rw [List.getElem?_eq_getElem (by rw [← hve_k]; exact hval_bd), Option.getD_some]
          simp [hve_k]
        have hk1 : (idx + 1#32).toNat = idx.toNat + 1 := dsSweep_bv32_add1_lt (by omega)
        have hlit_ar : (s.core.arena[cr.toNat + 3 + idx.toNat]?.getD 0#32).toNat = lit_k.toNat := by
          rw [List.getElem?_eq_getElem (by rw [← hae_k, har_k]; omega), Option.getD_some]
          simp only [lit_k, hidx_k, hae_k]
        have h_ar_lk : ∀ {pf},
            st_k.core.arena[(BitVec.setWidth 64 cr + (3 : BitVec 64) +
              BitVec.setWidth 64 idx).toNat]'pf = lit_k := fun {_} => rfl
        have har_hc_idx :
            (BitVec.toNat (BitVec.setWidth 64 cr + (3 : BitVec 64)) + BitVec.toNat idx) %
              2 ^ 64 = cr.toNat + 3 + idx.toNat := by
          rw [← bv_c0_zext32_64 idx, ← BitVec.toNat_add, show (3 : BitVec 64) = 3#64 from rfl]
          exact hidx_k
        ds_split
        · ds_steps <;> first
            | contradiction
            | exact hstep_occ nv_k nc_w cls_w st_k mk hnv_k_mono hlen_k hag_k hcone_k
                htmk_k hwk_k hmk
        have hnot_pos : s.core.vals[lit_k.toNat]?.getD 0#8 ≠ 1#8 := fun h1 => by
          dsimp only [LeanQbe.T.lift2, Arg.val_var, Arg.val_imm] at hc
          rw [getElem_eq_getElem?_getD st_k.core.vals (d := 0#8),
            getElem_eq_getElem?_getD st_k.core.arena (d := 0#32),
            har_hc_idx, hae_k, hlit_ar, hve_k, h1] at hc
          exact absurd hc (by decide)
        ds_to_group; refine wp_unroll_group fun _ _ => ?_; ds_split
        · have hl_zero : s.core.vals[lit_k.toNat]?.getD 0#8 = 0#8 := by
            rcases hw.vals_domain lit_k.toNat hl_lt_s with h0 | h1 | hf
            · exact h0
            · exact absurd h1 hnot_pos
            · dsimp only [LeanQbe.T.lift2, Arg.val_var, Arg.val_imm] at hc
              rw [getElem_eq_getElem?_getD st_k.core.vals (d := 0#8),
                getElem_eq_getElem?_getD st_k.core.arena (d := 0#32),
                har_hc_idx, hae_k, hlit_ar, hve_k, hf] at hc
              exact absurd hc (by decide)
          have hlv_eq : (lit_k >>> (1 : Nat)).toNat = lit_k.toNat / 2 := bv32_shr1_toNat lit_k
          have hlit_lt_s : lit_k.toNat < 2 * s.core.cur_vars := hl_lt_s
          have hlv_lt : (lit_k >>> (1 : Nat)).toNat < s.core.cur_vars := by omega
          have hlv_tm_k :
              (BitVec.setWidth 64 (lit_k >>> (1 : Nat))).toNat <
                st_k.scratch.tarjan_mark.length := by
            rw [hlen_k.scratch_ok.tarjan_mark_len, bv_c0_zext32_64]; omega
          ds_to_group
          refine wp_join_group (ts := [i32])
            (fun (nv_u, ()) m_u =>
              nv.toNat ≤ nv_u.toNat ∧ ∃ st_u : FullState,
                st_u.LengthsOk c ∧ AgreesExcept coneKMask s st_u ∧
                SweepKittenConeOk KInv F_cur st_u root_v.toNat nv_u.toNat nc_w.toNat cls_w ∧
                st_u.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                  BitVec.ofNat 32 (qi.toNat + 1) ∧
                (st_u.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                st_u.core.tmp = st_k.core.tmp ∧
                (∀ j < nv_k.toNat, st_u.scratch.work_stk1[j]? = st_k.scratch.work_stk1[j]?) ∧
                nv_k.toNat ≤ nv_u.toNat ∧ (FullMem c st_u ⋆ R) m_u)
            (fun _ (nv_u, ()) m_u
                ⟨hnvu, st_u, hlu, hau, hcu, htu, hwu, htmpu_eq, hwku_eq, hnvku, hmu⟩ => by
              have htm_u := hlu.scratch_ok.tarjan_mark_len
              have htmp_u := hlu.core_ok.tmp_len_arr
              have hcv_u := hau.get (·.core.cur_vars)
              have hlv_tm_u :
                  (BitVec.setWidth 64 (lit_k >>> (1 : Nat))).toNat <
                    st_u.scratch.tarjan_mark.length := by
                rw [htm_u, bv_c0_zext32_64]; omega
              ds_split
              · ds_steps <;> first
                  | contradiction
                  | exact hstep_occ nv_u nc_w cls_w st_u m_u hnvu hlu hau hcu htu hwu hmu
              have hne_lv :
                  st_u.scratch.tarjan_mark[(lit_k >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32 := by
                dsimp only [LeanQbe.T.lift2, Arg.val_var, Arg.val_imm] at hc
                rw [getElem_eq_getElem?_getD st_u.scratch.tarjan_mark (d := 0#32),
                  getElem_eq_getElem?_getD st_k.core.arena (d := 0#32),
                  har_hc_idx, hae_k, hlit_ar, ← hlv_eq] at hc
                exact hc
              rcases hcu.2.2.2.2.2.2.2.2.2.1 (lit_k >>> (1 : Nat)).toNat
                  (by rw [hcv_u]; exact hlv_lt) with hz | ⟨ilv, hilv, hwlv, htlv⟩
              · exact absurd hz hne_lv
              obtain ⟨hcnt1, hlen_u', hlts_u', hcov_u'⟩ :=
                sweep_cone_k_unassigned_step hlu htmpu_eq hwku_eq hnvku hcu.2.1 hk_lt hsz_le8
                  hsz_cv hcv_le hcnt_le hlit_ar hilv (hlv_eq ▸ hwlv) (hlv_eq ▸ htlv) hlts_k hcov_k
                  hcu
              have hcnt_tmp : (BitVec.setWidth 64 cnt).toNat < st_u.core.tmp.length := by
                rw [htmp_u, bv_c0_zext32_64]; omega
              clear hne_lv hc hlts_k hcov_k htmpu_eq hwku_eq
              c0_hsteps!
              have htmp_val :
                  ((st_u.scratch.tarjan_mark[(BitVec.setWidth 64
                    (st_k.core.arena[(BitVec.setWidth 64 cr + (3 : BitVec 64) +
                      BitVec.setWidth 64 idx).toNat]'hidx_bd >>>
                      (OfNat.ofNat 1 : Nat))).toNat]'hlv_tm_u - (1 : BitVec 32)) <<<
                      (OfNat.ofNat 1 : Nat) |||
                    st_k.core.arena[(BitVec.setWidth 64 cr + (3 : BitVec 64) +
                      BitVec.setWidth 64 idx).toNat]'hidx_bd &&& (1 : BitVec 32)) =
                  ((st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 - 1#32) <<<
                    (1 : Nat)) ||| (lit_k &&& 1#32) := by
                have h1 :
                    st_u.scratch.tarjan_mark[(BitVec.setWidth 64
                      (lit_k >>> (1 : Nat))).toNat]'hlv_tm_u =
                      st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 := by
                  have hlen_t : lit_k.toNat / 2 < st_u.scratch.tarjan_mark.length := by
                    rw [htm_u]; omega
                  rw [List.getElem?_eq_getElem hlen_t, Option.getD_some]
                  exact list_getElem_congr (by rw [bv_c0_zext32_64]; exact hlv_eq) _ _
                exact congrArg (fun t => ((t - 1#32) <<< (1 : Nat)) ||| (lit_k &&& 1#32)) h1
              have hcnt_n : (BitVec.setWidth 64 cnt).toNat = cnt.toNat := bv_c0_zext32_64 cnt
              have hm_u' : (FullMem c { st_u with
                  core := { st_u.core with tmp :=
                    (st_u.core.tmp.set cnt.toNat
                      (((st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 - 1#32) <<<
                        (1 : Nat)) ||| (lit_k &&& 1#32))) } } ⋆ R) m := by
                have hm' := hm
                dsimp only [LeanQbe.T.lift2, Arg.val_var, Arg.val_imm, Prod.fst] at hm'
                rwa [hcnt_n, htmp_val] at hm'
              exact hJ_k (nv_u, cnt + 1#32, idx + 1#32, ()) m (by dsimp only; omega)
                ⟨by omega, by omega, hnvu, _, hlen_u', hau.update _ fun _ => rfl, hcu, htu, hwu,
                 hlts_u', hcov_u', hm_u'⟩)
            (fun _ hJ_u => by
              have htm_k := hlen_k.scratch_ok.tarjan_mark_len
              have hwk_k_len := hlen_k.scratch_ok.work_stk1_len
              ds_split
              · have hc_tmk := hc
                ds_split
                · have hmiss :
                      st_k.scratch.tarjan_mark[(lit_k >>> (1 : Nat)).toNat]?.getD 0#32 = 0#32 := by
                    dsimp only [LeanQbe.T.lift2, Arg.val_var, Arg.val_imm] at hc_tmk
                    rw [getElem_eq_getElem?_getD st_k.scratch.tarjan_mark (d := 0#32),
                      getElem_eq_getElem?_getD st_k.core.arena (d := 0#32),
                      har_hc_idx, hae_k, hlit_ar, ← hlv_eq] at hc_tmk
                    exact hc_tmk
                  have hnv_k_128 : nv_k.toNat < 128 := by simpa using (hc : nv_k < 128#32)
                  have hcv_k := hag_k.get (·.core.cur_vars)
                  have hnv_k_lt : nv_k.toNat < s.core.cur_vars := by
                    rw [← hcv_k]
                    exact (sweepKittenConeOk_push_var hlen_k hcone_k hnv_k_128
                      (by rw [hcv_k]; exact hlv_lt) hmiss).1
                  have hnv1 : (nv_k + 1#32).toNat = nv_k.toNat + 1 :=
                    dsSweep_bv32_add1_lt (by omega)
                  have hnv_ws :
                      (BitVec.setWidth 64 ((nv_k + 1#32) - 1#32)).toNat <
                        st_k.scratch.work_stk1.length := by
                    rw [hwk_k_len, bv_c0_zext32_64, bv32_add1_sub1_small]; omega
                  c0_hsteps!
                  have hpush := sweepKittenConeOk_push_var hlen_k hcone_k hnv_k_128
                    (by rw [hcv_k]; exact hlv_lt) hmiss
                  obtain ⟨st_u, hst_u⟩ : ∃ st_u : FullState, st_u =
                    { st_k with scratch :=
                      { st_k.scratch with
                        tarjan_mark := st_k.scratch.tarjan_mark.set
                          (lit_k >>> (1 : Nat)).toNat (nv_k + 1#32)
                        work_stk1 := st_k.scratch.work_stk1.set
                          nv_k.toNat (lit_k >>> (1 : Nat)) } } := ⟨_, rfl⟩
                  have hne_cv : cv.toNat ≠ (lit_k >>> (1 : Nat)).toNat := fun heq => by
                    rw [← heq, htmk_k] at hmiss
                    have := congrArg BitVec.toNat hmiss
                    simp [BitVec.toNat_ofNat] at this; omega
                  have hne_nv_qi : nv_k.toNat ≠ qi.toNat := by omega
                  have h2 : (BitVec.setWidth 64 (nv_k + (1 : BitVec 32) - (1 : BitVec 32))).toNat =
                      nv_k.toNat := by
                    rw [bv_c0_zext32_64]
                    exact bv32_add1_sub1_small nv_k
                  have htm_idx : (BitVec.setWidth 64 (lit_k >>> (OfNat.ofNat 1 : Nat))).toNat =
                      (lit_k >>> (1 : Nat)).toNat := bv_c0_zext32_64 _
                  have hm_u : (FullMem c st_u ⋆ R) m := by
                    have hm' := hm
                    dsimp only [LeanQbe.T.lift2, Arg.val_var, Arg.val_imm, Prod.fst] at hm'
                    rw [h_ar_lk, htm_idx, h2] at hm'
                    exact (congrArg (fun stx => (FullMem c stx ⋆ R) m) (by rw [hst_u]; rfl)).mp hm'
                  refine hJ_u (nv_k + 1#32, ()) m
                    ⟨by omega, st_u,
                      by rw [hst_u]; exact ⟨hlen_k.core_ok, { hlen_k.scratch_ok with
                        tarjan_mark_len := by simp [htm_k]
                        work_stk1_len := by simp [hwk_k_len] }⟩,
                      hst_u ▸ hag_k.update _ fun _ => rfl,
                      by rw [hnv1, hst_u]
                         rw [bv32_ofNat_add1_small nv_k] at hpush; exact hpush.2,
                      by rw [hst_u, List.getElem?_set_ne (Ne.symm hne_cv)]; exact htmk_k,
                      by rw [hst_u, List.getElem?_set_ne hne_nv_qi]; exact hwk_k,
                      by rw [hst_u],
                      fun j hj => by rw [hst_u]; exact List.getElem?_set_ne (by omega),
                      by omega, hm_u⟩
                · ds_steps; exact hJ_u (nv_k, ()) mk
                    ⟨hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k, hwk_k, rfl,
                     fun _ _ => rfl, le_refl _, hmk⟩
              · ds_steps; exact hJ_u (nv_k, ()) mk
                  ⟨hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k, hwk_k, rfl,
                   fun _ _ => rfl, le_refl _, hmk⟩)
        · have hne0 : s.core.vals[lit_k.toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
            dsimp only [LeanQbe.T.lift2, Arg.val_var, Arg.val_imm] at hc
            rw [getElem_eq_getElem?_getD st_k.core.vals (d := 0#8),
              getElem_eq_getElem?_getD st_k.core.arena (d := 0#32),
              har_hc_idx, hae_k, hlit_ar, hve_k, h0] at hc
            exact absurd (by decide) hc
          have hfals_k : s.core.vals[lit_k.toNat]?.getD 0#8 = 0xFF#8 :=
            (hw.vals_domain lit_k.toNat hl_lt_s).elim
              (absurd · hne0) (·.elim (absurd · hnot_pos) id)
          ds_steps
          refine hJ_k (nv_k, cnt, idx + 1#32, ()) mk (by dsimp only; omega)
            ⟨by omega, by omega, hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k, hwk_k,
             hlts_k, fun i hi => ?_, hmk⟩
          rw [hk1] at hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
          · exact hcov_k i hlt
          · left; rwa [hlit_ar])

/-- **`full_sweep_cone`**: BFS up to `K_MAX_V = 128` variables and `K_MAX_ORIG = 512` clauses,
extracting entailed clauses into `kitten` and tracking `KInv nv cls false .fresh scr'`. -/
theorem full_sweep_cone_wp (Γ : Env)
    {KInv : Nat → List (Nat × List Nat) → Bool → KittenPhase → List (BitVec 32) → Prop}
    (hLaws : KittenInvLaws KInv)
    (hInit : EnvSpec Γ "full_kitten_init" (fullKittenInitSpec KInv))
    (hAddCl : EnvSpec Γ "full_kitten_add_clause" (fullKittenAddClauseSpec KInv)) :
    ∀ args m Q X, fullSweepConeKittenSpec KInv args m Q X →
      Func.wp Γ full_sweep_cone_body args m Q X := by
  rintro ⟨h, root_v, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdw, h10240, hroot, htmk, hm, hQ⟩
  have hlen := hdw.1; have hw := hdw.2.1; have hnd := hdw.2.2.2.1
  have hcl0 := hdw.2.2.2.2.2.1; have hdm := hdw.2.2.2.2.2.2
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwk_len := hlen.scratch_ok.work_stk1_len; have htm_len := hlen.scratch_ok.tarjan_mark_len
  have hdwatches : DenseWatchesInv F_cur s.core := by
    have hmw := hw.watches; unfold ModeWatchesInv at hmw; simp only [hdm, ↓reduceIte] at hmw
    exact hmw
  unfold Func.wp full_sweep_cone_body
  ds_steps
  refine LeanQbe.T.wp_call_of_spec _ _ (hInit _ _ _ _ ?_)
  refine ⟨c, s, R, rfl, hlen, h10240, by decide, by decide, hm,
    fun scr0 m0 hscr0 h256_0 h18_0 hK0 hm0 => ?_⟩
  let s0 : FullState := { s with scratch := { s.scratch with scratch_buf := scr0 } }
  have hlen0 : s0.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr0 }⟩
  change (FullMem c s0 ⋆ R) m0 at hm0
  have h0_wk0 : (BitVec.signExtend 64 (0 : BitVec 32)).toNat < s0.scratch.work_stk1.length := by
    rw [hlen0.scratch_ok.work_stk1_len,
      show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl]; omega
  let s0w : FullState :=
    { s0 with scratch := { s0.scratch with
        work_stk1 :=
          s0.scratch.work_stk1.set (BitVec.signExtend 64 (0 : BitVec 32)).toNat root_v } }
  have hrt_tm0 : (BitVec.setWidth 64 root_v).toNat < s0w.scratch.tarjan_mark.length := by
    rw [hlen0.scratch_ok.tarjan_mark_len, bv_c0_zext32_64]; omega
  obtain ⟨hlen1, hag1, hcone1⟩ :=
    sweepKittenConeOk_init (F_cur := F_cur) hlen (by simpa using hroot) htmk hscr0 h18_0 hK0
  ds_steps
  -- Outer loop: `while (qi < nv && nv < 128u && nc < 512u)` with `(nv, nc, qi)`
  refine wp_loop_inv (ts := [i32, i32, i32])
    (fun (nv, nc, qi, ()) mo =>
      qi.toNat ≤ nv.toNat ∧ ∃ (cls : List (Nat × List Nat)) (st : FullState),
        st.LengthsOk c ∧ AgreesExcept coneKMask s st ∧
        SweepKittenConeOk KInv F_cur st root_v.toNat nv.toNat nc.toNat cls ∧
        (FullMem c st ⋆ R) mo)
    (fun (_, _, qi, ()) _ => 128 - qi.toNat)
    (fun _ hJ_out => by
      ds_steps
      refine hJ_out (1#32, 0#32, 0#32, ()) _
        ⟨Nat.zero_le _, [], _, hlen1, hag1, hcone1, ?_⟩
      rw [show (1 : BitVec 32) = 1#32 from rfl] at hm
      simpa only [s0w, s0, show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl,
        bv_c0_zext32_64] using hm)
    (fun _ (nv, nc, qi, ()) mo ⟨hqi_le, cls, st, hlen_st, hag_st, hcone_st, hmo⟩ hJ_out => by
      clear hm m hcone1 hag1 hlen1 hrt_tm0 s0w h0_wk0 hlen0 s0 hK0 h18_0 h256_0 hscr0 scr0
      ds_to_group
      refine wp_join_group (ts := [])
        (fun () m_ex => ∃ (cls_e : List (Nat × List Nat)) (st_e : FullState),
          st_e.LengthsOk c ∧ AgreesExcept coneKMask s st_e ∧
          SweepKittenConeOk KInv F_cur st_e root_v.toNat nv.toNat nc.toNat cls_e ∧
          (FullMem c st_e ⋆ R) m_ex)
        (fun _ () m_ex ⟨cls_e, st_e, hlen_e, hag_e, hcone_e, hm_e⟩ => by
          have hscr_e := hlen_e.scratch_ok.scratch_buf_len
          have hcap_e := (hLaws.cap_ok hcone_e.2.2.2.2.2.1).1
          have hi256 : 256 < st_e.scratch.scratch_buf.length := by omega
          have hi262 : 262 < st_e.scratch.scratch_buf.length := by omega
          ds_steps
          obtain ⟨hlen_f, hfull_f, hK_f, hws0_f, hrev_f⟩ :=
            sweepKittenConeOk_to_spec hLaws hlen_e hcone_e
          have hnv128 := hcone_e.2.1; have hnc512 := hcone_e.2.2.2.2.1
          have hnv_bv : BitVec.ofNat 32 nv.toNat = nv := bv_ofNat_toNat_eq nv
          let scr_f := (st_e.scratch.scratch_buf.set 256 nv).set 262 nv
          let s_f : FullState := { st_e with scratch := { st_e.scratch with scratch_buf := scr_f } }
          have hag_f : AgreesExcept coneKMask s s_f := hag_e.update _ (fun _ => rfl)
          have hdw_f :=
            coneKMask_preserves_dense hag_f (by simpa [scr_f, hnv_bv] using hlen_f) hdw
          have hpk := cone_pack_nv_nc nv nc hnv128 (by rw [hcone_e.2.2.2.1]; exact hnc512)
          have hnv_pk :
              ((nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat))) &&& 0xFFFF#64).toNat =
                nv.toNat :=
            hpk.1
          have hnc_pk :
              ((nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat))) >>> 16).toNat = nc.toNat :=
            hpk.2
          have hQ' := fun m' =>
            hQ (nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat))) st_e.core.tmp
              st_e.scratch.work_stk1 st_e.scratch.tarjan_mark scr_f m' cls_e
          rw [← coneKMask_state_eq hag_f, hnv_pk, hnc_pk] at hQ'
          refine hQ' _ hdw_f
            (hag_e.get (·.core.cur_vars))
            (hag_e.get (·.core.fuel))
            (hag_e.get (·.core.vals))
            (hag_e.get (·.core.inconsistent))
            (by simpa [scr_f, hnv_bv] using hfull_f)
            (by simpa [scr_f, hnv_bv] using hK_f)
            hws0_f
            (by rw [hag_e.get (·.core.cur_vars)] at hrev_f; exact hrev_f)
            ?_
          · have hnv0 : 256 = 256 + (BitVec.ofNat 64 0).toNat := rfl
            have hnv6 : 262 = 256 + (BitVec.ofNat 64 6).toNat := rfl
            dsimp only [s_f, scr_f]; rw [hnv0, hnv6]; assumption)
        (fun _ hJ_ex => by
          clear hQ hInit
          ds_split
          · have hqi_lt : qi.toNat < nv.toNat := by bv_omega
            ds_split; rotate_left
            · ds_steps; exact hJ_ex () mo ⟨cls, st, hlen_st, hag_st, hcone_st, hmo⟩
            have hnv_lt128 : nv.toNat < 128 := by bv_omega
            ds_split; rotate_left
            · ds_steps; exact hJ_ex () mo ⟨cls, st, hlen_st, hag_st, hcone_st, hmo⟩
            have hnc_lt512 : nc.toNat < 512 := by bv_omega
            have hwk_st := hlen_st.scratch_ok.work_stk1_len
            have htm_st := hlen_st.scratch_ok.tarjan_mark_len
            have hnv_cv : nv.toNat ≤ s.core.cur_vars := by
              rw [← hag_st.get (·.core.cur_vars)]; exact hcone_st.2.2.1
            have hqi_z : (BitVec.setWidth 64 qi).toNat = qi.toNat := bv_c0_zext32_64 qi
            have hqi_ws : (BitVec.setWidth 64 qi).toNat < st.scratch.work_stk1.length := by
              rw [hqi_z, hwk_st]; omega
            let cv := st.scratch.work_stk1[(BitVec.setWidth 64 qi).toNat]'hqi_ws
            have hwk_qi : st.scratch.work_stk1[qi.toNat]?.getD 0#32 = cv := by
              rw [List.getElem?_eq_getElem (by rw [hwk_st]; omega), Option.getD_some]
              simp [cv, hqi_z]
            have hcv_lt_s : cv.toNat < s.core.cur_vars := by
              have hf := (hcone_st.2.2.2.2.2.2.2.2.1 qi.toNat hqi_lt).1
              rw [hwk_qi, hag_st.get (·.core.cur_vars)] at hf; exact hf
            have hcv_idx : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                BitVec.ofNat 32 (qi.toNat + 1) := by
              have hf := (hcone_st.2.2.2.2.2.2.2.2.1 qi.toNat hqi_lt).2
              rw [hwk_qi] at hf; exact hf
            have hcv_tmk : (BitVec.setWidth 64 cv).toNat < st.scratch.tarjan_mark.length := by
              rw [htm_st, bv_c0_zext32_64]; omega
            have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 := by bv_omega
            ds_steps
            have hmap_c : ((st.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tmk) - 1#32) =
                qi := by
              have htm_cv :
                  st.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tmk =
                    BitVec.ofNat 32 (qi.toNat + 1) := by
                rw [← Option.getD_some (a :=
                    st.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tmk),
                  ← List.getElem?_eq_getElem hcv_tmk, bv_c0_zext32_64, hcv_idx]
              rw [htm_cv]; bv_omega
            -- `pol` loop: `while (pol < 2u && nc < 512u)`
            refine wp_loop_inv (ts := [i32, i32, i32])
              (fun (nv_p, nc_p, pol, ()) mp =>
                pol.toNat ≤ 2 ∧ nv.toNat ≤ nv_p.toNat ∧
                ∃ (cls_p : List (Nat × List Nat)) (st_p : FullState),
                  st_p.LengthsOk c ∧ AgreesExcept coneKMask s st_p ∧
                  SweepKittenConeOk KInv F_cur st_p root_v.toNat nv_p.toNat nc_p.toNat cls_p ∧
                  st_p.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi.toNat + 1) ∧
                  (st_p.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                  (FullMem c st_p ⋆ R) mp)
              (fun (_, _, pol, ()) _ => 2 - pol.toNat)
              (fun _ hJ_pol => by
                ds_steps
                exact hJ_pol (nv, nc, 0#32, ()) mo ⟨Nat.zero_le _, Nat.le_refl _, cls, st,
                  hlen_st, hag_st, hcone_st, hcv_idx, by rw [hwk_qi], hmo⟩)
              (fun _ (nv_p, nc_p, pol, ()) mp
                  ⟨hpol_le, hnv_mono, cls_p, st_p, hlen_p, hag_p, hcone_p, htmk_cv, hwk_cv,
                   hmp⟩ hJ_pol => by
                ds_split; rotate_left
                · ds_steps; exact hJ_out (nv_p, nc_p, qi + 1#32, ()) mp (by dsimp only; omega)
                    ⟨by omega, cls_p, st_p, hlen_p, hag_p, hcone_p, hmp⟩
                have hpol_lt : pol.toNat < 2 := by bv_omega
                ds_split; rotate_left
                · ds_steps; exact hJ_out (nv_p, nc_p, qi + 1#32, ()) mp (by dsimp only; omega)
                    ⟨by omega, cls_p, st_p, hlen_p, hag_p, hcone_p, hmp⟩
                have hncp_lt : nc_p.toNat < 512 := by bv_omega
                let lit : BitVec 32 := (cv <<< (1 : Nat)) ||| pol
                have hlit_eq : lit.toNat = 2 * cv.toNat + pol.toNat :=
                  FullSweepFwdHelpers.bv32_shl1_or_pol cv pol
                    (by have := c.hmaxv; unfold dimacsBound at this; omega) hpol_lt
                have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
                have hwvec_p := hlen_p.core_ok.wvec_len
                have h2lit : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat = 2 * lit.toNat :=
                  bv64_shl1_toNat _
                have h2lit1 : ((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat =
                    2 * lit.toNat + 1 := bv64_shl1_add1_toNat _
                have hwvec_eq : st_p.core.wvec = s.core.wvec := hag_p.get (·.core.wvec)
                have hbounds := hdwatches.layout.bounds lit.toNat hlit_lt
                have hwlen_le := hlen.core_ok.wlen_le; have hwcap_lt := c.hwcap
                have h2l_bd : (BitVec.setWidth 64 ((cv <<< (1 : Nat)) ||| pol) <<<
                    (OfNat.ofNat 1 : Nat)).toNat < st_p.core.wvec.length := by
                  rw [hwvec_p, h2lit]; unfold dimacsBound at *; omega
                have h2l1_bd : ((BitVec.setWidth 64 ((cv <<< (1 : Nat)) ||| pol) <<<
                    (OfNat.ofNat 1 : Nat)) + 1#64).toNat < st_p.core.wvec.length := by
                  rw [hwvec_p, h2lit1]; unfold dimacsBound at *; omega
                let wOff := (st_p.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'(
                  by rw [hwvec_p, h2lit]; omega)).setWidth 64
                let wSz := (st_p.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat]'(
                  by rw [hwvec_p, h2lit1]; omega)).setWidth 64
                have hwOff_n : wOff.toNat = fullWatchOffCore s.core lit.toNat := by
                  dsimp only [wOff]; unfold fullWatchOffCore
                  rw [bv_c0_zext32_64, List.getElem?_eq_getElem (by rw [← hwvec_eq]; omega),
                    Option.getD_some]
                  simp [hwvec_eq, h2lit]
                have hwSz_n : wSz.toNat = fullWatchSizeCore s.core lit.toNat := by
                  dsimp only [wSz]; unfold fullWatchSizeCore
                  rw [bv_c0_zext32_64, List.getElem?_eq_getElem (by rw [← hwvec_eq]; omega),
                    Option.getD_some]
                  simp [hwvec_eq, h2lit1]
                let wEnd := wOff + wSz
                have hend_eq : wEnd.toNat =
                    fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat := by
                  unfold dimacsBound at hwcap_lt; dsimp only [wEnd]
                  rw [BitVec.toNat_add, hwOff_n, hwSz_n, Nat.mod_eq_of_lt (by omega)]
                have hpol1 : (pol + 1#32).toNat = pol.toNat + 1 := by bv_omega
                ds_to_group
                refine wp_join_group (ts := [i32, i32, i64])
                  (fun (nv_e, nc_e, _, ()) m_we =>
                    nv.toNat ≤ nv_e.toNat ∧ ∃ (cls_e : List (Nat × List Nat)) (st_we : FullState),
                      st_we.LengthsOk c ∧ AgreesExcept coneKMask s st_we ∧
                      SweepKittenConeOk KInv F_cur st_we root_v.toNat nv_e.toNat nc_e.toNat cls_e ∧
                      st_we.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                        BitVec.ofNat 32 (qi.toNat + 1) ∧
                      (st_we.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                      (FullMem c st_we ⋆ R) m_we)
                  (fun _ (nv_e, nc_e, _, ()) m_we
                      ⟨hnve, cls_e, st_we, hl_e, ha_e, hc_e, ht_e, hw_e, hm_e⟩ => by
                    ds_steps
                    exact hJ_pol (nv_e, nc_e, pol + 1#32, ()) m_we (by dsimp only; omega)
                      ⟨by omega, hnve, cls_e, st_we, hl_e, ha_e, hc_e, ht_e, hw_e, hm_e⟩)
                  (fun _ hJ_we => by
                    ds_steps
                    -- Watch loop: `while (p < end && nc < 512u)` with `(nv, nc, p)`
                    refine wp_loop_inv (ts := [i32, i32, i64])
                      (fun (nv_w, nc_w, p, ()) mw =>
                        p.toNat ≤ wEnd.toNat ∧ nv.toNat ≤ nv_w.toNat ∧
                        DenseWatchSliceOk F_cur s.core lit.toNat p.toNat (wEnd.toNat - p.toNat) ∧
                        ∃ (cls_w : List (Nat × List Nat)) (st_w : FullState),
                          st_w.LengthsOk c ∧ AgreesExcept coneKMask s st_w ∧
                          SweepKittenConeOk KInv F_cur st_w root_v.toNat nv_w.toNat nc_w.toNat
                            cls_w ∧
                          st_w.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                            BitVec.ofNat 32 (qi.toNat + 1) ∧
                          (st_w.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                          (FullMem c st_w ⋆ R) mw)
                      (fun (_, _, p, ()) _ => wEnd.toNat - p.toNat)
                      (fun _ hJ_w => by
                        ds_steps
                        refine hJ_w (nv_p, nc_p, wOff, ()) mp ⟨by omega, hnv_mono, ?_,
                          cls_p, st_p, hlen_p, hag_p, hcone_p, htmk_cv, hwk_cv, hmp⟩
                        rw [hwOff_n, show wEnd.toNat - fullWatchOffCore s.core lit.toNat =
                          fullWatchSizeCore s.core lit.toNat by omega]
                        exact hdwatches.slices lit.toNat hlit_lt)
                      (fun J_w (nv_w, nc_w, p, ()) mw
                          ⟨hp_le, hnv_w_mono, hslice, cls_w, st_w, hlen_w, hag_w, hcone_w,
                           htmk_w, hwk_w, hmw⟩ hJ_w => by
                        clear hJ_out hJ_ex hJ_pol hmp hlen_p hag_p hcone_p htmk_cv hwk_cv hmo
                          hlen_st hag_st hcone_st hwk_qi hcv_idx
                        ds_split; rotate_left
                        · ds_steps; exact hJ_we (nv_w, nc_w, p, ()) mw
                            ⟨hnv_w_mono, cls_w, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w, hmw⟩
                        have hcv_qi : ∀ (h : qi.toNat < st.scratch.work_stk1.length),
                            st.scratch.work_stk1[qi.toNat]'h = cv := fun h =>
                          Option.some.inj (by
                            dsimp only [cv]
                            rw [← List.getElem?_eq_getElem h,
                              ← List.getElem?_eq_getElem hqi_ws, hqi_z])
                        have h2l_mod : (2 * lit.toNat) % 2 ^ 64 =
                            (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat := by
                          rw [h2lit, Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
                        have h2l1_mod : (2 * lit.toNat + 1) % 2 ^ 64 =
                            ((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat := by
                          rw [h2lit1, Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
                        have hwv0_eq : ∀ (h : (2 * lit.toNat) % 2 ^ 64 < st_p.core.wvec.length),
                            st_p.core.wvec[(2 * lit.toNat) % 2 ^ 64]'h =
                              st_p.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'
                                h2l_bd := fun h => Option.some.inj (by
                          rw [← List.getElem?_eq_getElem h,
                            ← List.getElem?_eq_getElem h2l_bd, h2l_mod])
                        have hwv1_eq :
                            ∀ (h : (2 * lit.toNat + BitVec.toNat 1) % 2 ^ 64 <
                                st_p.core.wvec.length),
                              st_p.core.wvec[(2 * lit.toNat + BitVec.toNat 1) % 2 ^ 64]'h =
                                st_p.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                                    1#64).toNat]'h2l1_bd := fun h => Option.some.inj (by
                          rw [← List.getElem?_eq_getElem h, ← List.getElem?_eq_getElem h2l1_bd,
                            show BitVec.toNat (1 : BitVec 64) = 1 from rfl, h2l1_mod])
                        have hshl_1 : ∀ x : BitVec 32,
                            (x <<< (BitVec.toNat (1 : BitVec 32) % 32)) = x <<< (1 : Nat) :=
                          fun _ => rfl
                        have hp_lt : p.toNat < wEnd.toNat := by
                          simp only [LeanQbe.T.lift2, Arg.val_var, Arg.val_imm, hcv_qi, hshl_1]
                            at hc
                          change BitVec.toNat p < _ at hc
                          rw [hwv0_eq, hwv1_eq] at hc
                          change BitVec.toNat p < (wOff.toNat + wSz.toNat) % 2 ^ 64 at hc
                          simpa only [wEnd, BitVec.toNat_add] using hc
                        ds_split; rotate_left
                        · ds_steps; exact hJ_we (nv_w, nc_w, p, ()) mw
                            ⟨hnv_w_mono, cls_w, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w, hmw⟩
                        have hncw_lt : nc_w.toNat < 512 := by bv_omega
                        have hwstk_eq : st_w.core.wstk = s.core.wstk := hag_w.get (·.core.wstk)
                        have hcv_w : st_w.core.cur_vars = s.core.cur_vars :=
                          hag_w.get (·.core.cur_vars)
                        have hwstk_w := hlen_w.core_ok.wstk_len_arr
                        have hp_wcap : p.toNat < c.wcap := by omega
                        have hp1 : (p + 1#64).toNat = p.toNat + 1 := by
                          unfold dimacsBound at hwcap_lt
                          rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl,
                            Nat.mod_eq_of_lt (by omega)]
                        let w0 := st_w.core.wstk[p.toNat]'(by omega)
                        have hw0_s : s.core.wstk[p.toNat]? = some w0 := by
                          rw [List.getElem?_eq_getElem (by rw [← hwstk_eq]; omega)]
                          exact congrArg some (by simp [w0, hwstk_eq])
                        ds_split
                        · -- Binary watch branch
                          have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                            dsimp only [w0]; bv_omega
                          obtain ⟨_, hot_lt, hent_bin, hslice1⟩ :=
                            denseWatchSlice_step_bin hslice (by omega) hw0_s hbin
                          let ot : BitVec 32 := w0 &&& 0x7FFFFFFF#32
                          have hot_lt' : ot.toNat < 2 * s.core.cur_vars := hot_lt
                          let ov : BitVec 32 := ot >>> (1 : Nat)
                          have hov_eq : ov.toNat = ot.toNat / 2 := bv32_shr1_toNat ot
                          have hov_lt : ov.toNat < s.core.cur_vars := by omega
                          have hvals_w := hlen_w.core_ok.vals_len
                          have htm_w := hlen_w.scratch_ok.tarjan_mark_len
                          have hwk_w_len := hlen_w.scratch_ok.work_stk1_len
                          have hot_vals :
                              (BitVec.setWidth 64 ot).toNat < st_w.core.vals.length := by
                            rw [hvals_w, bv_c0_zext32_64]; omega
                          ds_to_group
                          refine wp_join_group (ts := [i32, i32])
                            (fun (nv_b, nc_b, ()) m_b =>
                              nv.toNat ≤ nv_b.toNat ∧
                              ∃ (cls_b : List (Nat × List Nat)) (st_b : FullState),
                                st_b.LengthsOk c ∧ AgreesExcept coneKMask s st_b ∧
                                SweepKittenConeOk KInv F_cur st_b root_v.toNat nv_b.toNat nc_b.toNat
                                  cls_b ∧
                                st_b.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                                  BitVec.ofNat 32 (qi.toNat + 1) ∧
                                (st_b.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                                (FullMem c st_b ⋆ R) m_b)
                            (fun _ (nv_b, nc_b, ()) m_b
                                ⟨hnvb, cls_b, st_b, hlb, hab, hcb, htb, hwb, hmb⟩ => by
                              ds_steps
                              exact hJ_w (nv_b, nc_b, p + 1#64, ()) m_b (by dsimp only; omega)
                                ⟨by omega, hnvb, by rw [hp1, show wEnd.toNat - (p.toNat + 1) =
                                    wEnd.toNat - p.toNat - 1 by omega]; exact hslice1,
                                  cls_b, st_b, hlb, hab, hcb, htb, hwb, hmb⟩)
                            (fun _ hJ_bin => by
                              ds_split; rotate_left
                              · ds_steps; exact hJ_bin (nv_w, nc_w, ()) mw
                                  ⟨hnv_w_mono, cls_w, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w,
                                   hmw⟩
                              have hov_tmk : (BitVec.setWidth 64 ov).toNat <
                                  st_w.scratch.tarjan_mark.length := by
                                rw [htm_w, bv_c0_zext32_64]; omega
                              have htm_w_idx :
                                  ∀ {j : Nat} (hj : j < st_w.scratch.tarjan_mark.length),
                                    j = ov.toNat →
                                    st_w.scratch.tarjan_mark[j]'hj =
                                      st_w.scratch.tarjan_mark[ov.toNat]'(by omega) :=
                                fun _ hij => Option.some.inj (by subst hij; rfl)
                              ds_to_group
                              refine wp_join_group (ts := [])
                                (fun () m_or => m_or = mw ∧
                                  (st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0#32 ∨
                                    nv_w.toNat < 128))
                                (fun _ () m_or ⟨hmor, hor⟩ => by
                                  subst m_or
                                  refine wp_join_group (ts := [i32])
                                    (fun (nv_a, ()) m_a =>
                                      nv.toNat ≤ nv_a.toNat ∧
                                      ∃ st_a : FullState,
                                        st_a.LengthsOk c ∧ AgreesExcept coneKMask s st_a ∧
                                        SweepKittenConeOk KInv F_cur st_a root_v.toNat nv_a.toNat
                                          nc_w.toNat cls_w ∧
                                        st_a.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                                          BitVec.ofNat 32 (qi.toNat + 1) ∧
                                        (st_a.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat =
                                          cv.toNat ∧
                                        st_a.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0#32 ∧
                                        (FullMem c st_a ⋆ R) m_a)
                                    (fun _ (nv_a, ()) m_a
                                        ⟨hnva, st_a, hla, haa, hca, htca, hwca, htoa, hma⟩ => by
                                      ds_to_group; refine wp_unroll_group fun _ _ => ?_
                                      ds_split; rotate_left
                                      · ds_steps; exact hJ_bin (nv_a, nc_w, ()) m_a
                                          ⟨hnva, cls_w, st_a, hla, haa, hca, htca, hwca, hma⟩
                                      have htm_a := hla.scratch_ok.tarjan_mark_len
                                      have htmp_a := hla.core_ok.tmp_len_arr
                                      have hcv_a := haa.get (·.core.cur_vars)
                                      rcases hca.2.2.2.2.2.2.2.2.2.1 ov.toNat
                                          (by rw [hcv_a]; exact hov_lt) with
                                        hz | ⟨iov, hiov, hwov, htov⟩
                                      · exact absurd hz htoa
                                      obtain ⟨hl0_lt, hl1_lt, hlift0, hlift1⟩ :=
                                        cone_bin_lits_ok (Nat.lt_of_lt_of_le hqi_lt hnva) hca.2.1
                                          hpol_lt hlit_eq hov_eq hiov htca hwca htov hwov
                                      have hcv_tm : cv.toNat < st_a.scratch.tarjan_mark.length := by
                                        omega
                                      have hov_tm : ov.toNat < st_a.scratch.tarjan_mark.length := by
                                        omega
                                      rw [List.getElem?_eq_getElem hcv_tm, Option.getD_some]
                                        at hl0_lt hlift0
                                      rw [List.getElem?_eq_getElem hov_tm, Option.getD_some]
                                        at hl1_lt hlift1
                                      have htm_cv_s_eq_a :
                                          st.scratch.tarjan_mark[
                                              (BitVec.setWidth 64 cv).toNat]'hcv_tmk =
                                            st_a.scratch.tarjan_mark[cv.toNat]'hcv_tm := by
                                        have hs1 := bv32_eq_add1_of_sub1 hmap_c
                                        have ha : st_a.scratch.tarjan_mark[cv.toNat]'hcv_tm =
                                            BitVec.ofNat 32 (qi.toNat + 1) := by
                                          simpa only [List.getElem?_eq_getElem hcv_tm,
                                            Option.getD_some] using htca
                                        rw [hs1, ha]
                                        exact BitVec.eq_of_toNat_eq (by
                                          rw [hqi1, BitVec.toNat_ofNat,
                                            Nat.mod_eq_of_lt (by omega)])
                                      let l0_b :=
                                        ((st.scratch.tarjan_mark[
                                            (BitVec.setWidth 64 cv).toNat]'hcv_tmk - 1#32) <<<
                                          (1 : Nat)) ||| pol
                                      have hl0_lt' : l0_b.toNat < 2 * nv_a.toNat := by
                                        dsimp only [l0_b]; rw [htm_cv_s_eq_a]; exact hl0_lt
                                      have hlift0' : fullSweepGlobalLit st_a l0_b.toNat =
                                          lit.toNat := by
                                        dsimp only [l0_b]; rw [htm_cv_s_eq_a]; exact hlift0
                                      have htm_a_ov : (BitVec.setWidth 64 ov).toNat <
                                          st_a.scratch.tarjan_mark.length := by
                                        rw [htm_a, bv_c0_zext32_64]; omega
                                      let l1_b :=
                                        ((st_a.scratch.tarjan_mark[(BitVec.setWidth 64 ov).toNat]'
                                            htm_a_ov - 1#32) <<< (1 : Nat)) ||| (ot &&& 1#32)
                                      have htm_a_ov_eq :
                                          st_a.scratch.tarjan_mark[(BitVec.setWidth 64 ov).toNat]'
                                              htm_a_ov =
                                            st_a.scratch.tarjan_mark[ov.toNat]'hov_tm := by
                                        simp only [bv_c0_zext32_64]
                                      have htmp_a0 : 0 < st_a.core.tmp.length := by
                                        have := hca.1; have := hca.2.2.1
                                        have := hla.core_ok.cur_vars_le; omega
                                      ds_steps_soft
                                      let st_a1 : FullState :=
                                        { st_a with core := { st_a.core with
                                            tmp := st_a.core.tmp.set 0 l0_b } }
                                      refine sweep_cone_bin_store1_add_clause hAddCl (st := st_a1)
                                        (nc := nc_w) (l0 := l0_b) (l1 := l1_b) (R := R)
                                        ?_ ?_ ?_ ?_ ?_ ?_
                                        ⟨{ hla.core_ok with
                                            tmp_len_arr := by simp [st_a1, htmp_a] },
                                          hla.scratch_ok⟩
                                        (haa.update _ fun _ => rfl) h10240
                                        (sweepKittenConeOk_tmp_irrel hca) hncw_lt
                                        (by
                                          dsimp only [st_a1]
                                          exact List.getElem?_set_self (by omega))
                                        hl0_lt' (by simpa only [l1_b, htm_a_ov_eq] using hl1_lt)
                                        (by
                                          have hfg_a : ∀ x,
                                              fullSweepGlobalLit st_a1 x =
                                                fullSweepGlobalLit st_a x :=
                                            fun _ => rfl
                                          have heq1 : (w0 &&& 0x7FFFFFFF#32).toNat =
                                              fullSweepGlobalLit st_a
                                                (((st_a.scratch.tarjan_mark[ov.toNat]'hov_tm -
                                                  1#32) <<< (1 : Nat) ||| (ot &&& 1#32)).toNat) :=
                                            hlift1.symm
                                          simpa only [hfg_a, l1_b, htm_a_ov_eq, ← hlift0', ← heq1]
                                            using hent_bin)
                                        ?_ ?_
                                      · rfl
                                      · rfl
                                      · rfl
                                      · rfl
                                      · rfl
                                      · rfl
                                      · dsimp only [st_a1, l0_b]
                                        simpa only [show (BitVec.signExtend 64
                                            (0 : BitVec 32)).toNat = 0 from rfl] using
                                          ‹(FullMem c _ ⋆ R) _›
                                      · intro J_g hJ_g ok cls' st' m' _ _ hl' ha' hc' ht' hw' hm'
                                        ds_split
                                        · ds_steps
                                          exact hJ_bin (nv_a, _, ()) m' ⟨hnva, cls', st', hl', ha',
                                            by simpa only [hc, ↓reduceIte,
                                              show (1#32 : BitVec 32) = 1 from rfl] using hc',
                                            ht' ▸ htca, hw' ▸ hwca, hm'⟩
                                        · ds_steps
                                          exact hJ_bin (nv_a, _, ()) m' ⟨hnva, cls', st', hl', ha',
                                            by simpa only [hc, Bool.false_eq_true, ↓reduceIte]
                                              using hc',
                                            ht' ▸ htca, hw' ▸ hwca, hm'⟩)
                                    (fun _ hJ_a => by
                                      ds_split
                                      · have hmiss : st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 =
                                            0#32 := by
                                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                          rw [htm_w_idx _ (by rw [hov_eq]; rfl)] at hc
                                          exact hc
                                        have hnv_lt128_w : nv_w.toNat < 128 :=
                                          hor.elim (absurd hmiss) id
                                        have hnv_w_lt : nv_w.toNat < s.core.cur_vars := by
                                          rw [← hcv_w]
                                          exact (sweepKittenConeOk_push_var hlen_w hcone_w
                                            hnv_lt128_w (by rw [hcv_w]; exact hov_lt) hmiss).1
                                        have hnv1 : (nv_w + 1#32).toNat = nv_w.toNat + 1 := by
                                          bv_omega
                                        have hnv_ws : (BitVec.setWidth 64 ((nv_w + 1#32) -
                                            1#32)).toNat < st_w.scratch.work_stk1.length := by
                                          rw [hwk_w_len, bv_c0_zext32_64,
                                            show nv_w + 1#32 - 1#32 = nv_w from by bv_omega]; omega
                                        ds_steps
                                        have hpush := sweepKittenConeOk_push_var hlen_w hcone_w
                                          hnv_lt128_w (by rw [hcv_w]; exact hov_lt) hmiss
                                        let st_a : FullState :=
                                          { st_w with scratch :=
                                            { st_w.scratch with
                                              tarjan_mark := st_w.scratch.tarjan_mark.set ov.toNat
                                                (nv_w + 1#32)
                                              work_stk1 := st_w.scratch.work_stk1.set nv_w.toNat
                                                ov } }
                                        have hne_cv : cv.toNat ≠ ov.toNat := fun heq => by
                                          rw [← heq, htmk_w] at hmiss
                                          have := congrArg BitVec.toNat hmiss
                                          simp [BitVec.toNat_ofNat] at this; omega
                                        have hne_nv_qi : nv_w.toNat ≠ qi.toNat := by omega
                                        have hm_a : (FullMem c st_a ⋆ R) m := by
                                          have h2 : (nv_w + 1 - 1 : BitVec 32).toNat =
                                              nv_w.toNat := by bv_omega
                                          have h3 : (nv_w + 1 : BitVec 32) = nv_w + 1#32 := rfl
                                          have hw0' : (st_w.core.wstk[p.toNat]'(by omega) &&&
                                              2147483647) >>> OfNat.ofNat 1 = ov := rfl
                                          dsimp only [LeanQbe.T.lift2, Arg.val_var, Arg.val_imm]
                                            at hm
                                          rw [bv_c0_zext32_64, h2, hw0', bv_c0_zext32_64, h3] at hm
                                          exact hm
                                        exact hJ_a (nv_w + 1#32, ()) m
                                          ⟨by omega, st_a,
                                            ⟨hlen_w.core_ok, { hlen_w.scratch_ok with
                                              tarjan_mark_len := by simp [st_a, htm_w]
                                              work_stk1_len := by simp [st_a, hwk_w_len] }⟩,
                                            hag_w.update _ (fun _ => rfl),
                                            by rw [hnv1]; simpa [st_a, show BitVec.ofNat 32
                                                (nv_w.toNat + 1) = nv_w + 1#32 from by bv_omega]
                                              using hpush.2,
                                            by dsimp only [st_a]
                                               rw [List.getElem?_set_ne (Ne.symm hne_cv)]
                                               exact htmk_w,
                                            by dsimp only [st_a]
                                               rw [List.getElem?_set_ne hne_nv_qi]
                                               exact hwk_w,
                                            by dsimp only [st_a]
                                               rw [List.getElem?_set_self (by omega),
                                                 Option.getD_some]
                                               intro h; have := congrArg BitVec.toNat h
                                               simp [hnv1] at this,
                                            hm_a⟩
                                      · have hne_ov :
                                            st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠
                                              0#32 := by
                                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                          rw [htm_w_idx _ (by rw [hov_eq]; rfl)] at hc
                                          exact hc
                                        ds_steps
                                        exact hJ_a (nv_w, ()) mw
                                          ⟨hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w,
                                           hne_ov, hmw⟩))
                                (fun _ hJ_or => by
                                  ds_split
                                  · have hne :
                                        st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0#32 := by
                                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                      rw [htm_w_idx _ (by rw [hov_eq]; rfl)] at hc
                                      exact hc
                                    ds_steps; exact hJ_or () mw ⟨rfl, Or.inl hne⟩
                                  · ds_split
                                    · have hlt : nv_w.toNat < 128 := by bv_omega
                                      ds_steps; exact hJ_or () mw ⟨rfl, Or.inr hlt⟩
                                    · ds_steps; exact hJ_bin (nv_w, nc_w, ()) mw
                                        ⟨hnv_w_mono, cls_w, st_w, hlen_w, hag_w, hcone_w, htmk_w,
                                         hwk_w, hmw⟩))
                        · -- Occurrence watch branch
                          have hocc : (w0 &&& 0x80000000#32) = 0#32 := by
                            dsimp only [w0]; bv_omega
                          obtain ⟨hrem2, _, cr, hcr_s, hcr_lt, hcr_ref, hslice2⟩ :=
                            denseWatchSlice_step_occ hslice (by omega) hw0_s hocc
                          ds_split
                          · exfalso
                            simp only [LeanQbe.T.lift2, Arg.val_var, Arg.val_imm, hcv_qi, hshl_1]
                              at hc
                            rw [hwv0_eq, hwv1_eq] at hc
                            have hge : wEnd.toNat ≤ (p + 1#64).toNat := by
                              dsimp only [wEnd]; rw [BitVec.toNat_add, BitVec.toNat_add]; exact hc
                            omega
                          have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
                            unfold dimacsBound at hwcap_lt
                            rw [BitVec.toNat_add, hp1, show (1#64).toNat = 1 from rfl,
                              Nat.mod_eq_of_lt (by omega)]
                          have har_w := hlen_w.core_ok.arena_len_arr
                          have har_s := hlen.core_ok.arena_len_arr
                          have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
                          have hacap_lt := c.harena; have hal_le := hlen.core_ok.arena_len_le
                          have hcr_eq : st_w.core.wstk[p.toNat + 1]'(by omega) = cr := by
                            rw [List.getElem?_eq_getElem (by rw [← hwstk_eq]; omega)] at hcr_s
                            simpa [hwstk_eq] using Option.some.inj hcr_s
                          have hcr_eq' : st_w.core.wstk[(p + 1#64).toNat]'(by omega) = cr := by
                            simpa [hp1] using hcr_eq
                          have hcr_idx :
                              ∀ {j : Nat} (hj : j < st_w.core.wstk.length), j = p.toNat + 1 →
                                st_w.core.wstk[j]'hj = cr := fun _ hij =>
                            Option.some.inj (by subst hij; exact congrArg some hcr_eq)
                          have hcr2_lt : (BitVec.setWidth 64 cr + 2#64).toNat = cr.toNat + 2 := by
                            unfold dimacsBound at hacap_lt
                            simp only [BitVec.toNat_add, bv_c0_zext32_64,
                              show (2#64 : BitVec 64).toNat = 2 from rfl]
                            omega
                          have har_eq : st_w.core.arena = s.core.arena := hag_w.get (·.core.arena)
                          have har_cr_bd : cr.toNat < st_w.core.arena.length := by
                            rw [har_eq, har_s]; omega
                          have har_cr2_bd : (BitVec.setWidth 64 cr + 2#64).toNat <
                              st_w.core.arena.length := by
                            rw [har_eq, har_s, hcr2_lt]; omega
                          let sz : BitVec 32 :=
                            st_w.core.arena[(BitVec.setWidth 64 cr + 2#64).toNat]'har_cr2_bd
                          have har_cr_idx :
                              ∀ {k : Nat} (hk : k < st_w.core.arena.length), k = cr.toNat →
                                st_w.core.arena[k]'hk = st_w.core.arena[cr.toNat]'har_cr_bd :=
                            fun _ hkeq => Option.some.inj (by subst hkeq; rfl)
                          have har_sz_idx :
                              ∀ {k : Nat} (hk : k < st_w.core.arena.length),
                                k = (BitVec.setWidth 64 cr + 2#64).toNat →
                                st_w.core.arena[k]'hk = sz :=
                            fun _ hkeq => Option.some.inj (by subst hkeq; rfl)
                          have hsz_core : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                            unfold fullArenaClauseSizeCore; dsimp only [sz]
                            rw [List.getElem?_eq_getElem (by rw [har_s]; omega), Option.getD_some]
                            simp only [har_eq, hcr2_lt]
                          have hstep_occ : ∀ (nv_x nc_x : BitVec 32) (cls_x : List (Nat × List Nat))
                              (st_x : FullState) (mx : Mem 64),
                              nv.toNat ≤ nv_x.toNat → st_x.LengthsOk c →
                              AgreesExcept coneKMask s st_x →
                              SweepKittenConeOk KInv F_cur st_x root_v.toNat nv_x.toNat
                                nc_x.toNat cls_x →
                              st_x.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                                BitVec.ofNat 32 (qi.toNat + 1) →
                              (st_x.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat →
                              (FullMem c st_x ⋆ R) mx →
                              J_w (nv_x, nc_x, p + 1#64 + 1#64, ()) mx :=
                            fun nv_x nc_x cls_x st_x mx hnvx hlx hax hcx htx hwx hmx =>
                              hJ_w (nv_x, nc_x, p + 1#64 + 1#64, ()) mx (by dsimp only; omega)
                                ⟨by omega, hnvx, by rw [hp2, show wEnd.toNat - (p.toNat + 2) =
                                    wEnd.toNat - p.toNat - 2 by omega]; exact hslice2,
                                  cls_x, st_x, hlx, hax, hcx, htx, hwx, hmx⟩
                          have hocc_done : J_w (nv_w, nc_w, p + 1#64 + 1#64, ()) mw :=
                            hstep_occ nv_w nc_w cls_w st_w mw hnv_w_mono hlen_w hag_w hcone_w
                              htmk_w hwk_w hmw
                          have hp_mod :
                              (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
                            unfold dimacsBound at hwcap_lt
                            rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                              Nat.mod_eq_of_lt (by omega)]
                          ds_split; · ds_steps; exact hocc_done
                          have hgr0 : (st_w.core.arena[cr.toNat]'(by omega) &&&
                              (0x00080000#32 ||| 0x00400000#32)) = 0#32 := by
                            rw [har_cr_idx] at hc
                            · exact hc
                            · rw [hcr_idx _ hp_mod]
                          ds_split; · ds_steps; exact hocc_done
                          have hsz_ge3 : 3 ≤ sz.toNat := by
                            rw [har_sz_idx] at hc
                            · exact Nat.le_of_not_lt hc
                            · rw [hcr_idx]
                              · rw [hcr2_lt, show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                                  Nat.mod_eq_of_lt (by unfold dimacsBound at hacap_lt; omega)]
                              · exact hp_mod
                          ds_split; · ds_steps; exact hocc_done
                          have hsz_le8 : sz.toNat ≤ 8 := by
                            rw [har_sz_idx] at hc
                            · exact Nat.le_of_not_lt hc
                            · rw [hcr_idx]
                              · rw [hcr2_lt, show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                                  Nat.mod_eq_of_lt (by unfold dimacsBound at hacap_lt; omega)]
                              · exact hp_mod
                          obtain ⟨hng, hcr_sz_le, hsz_cv, hcr3_bd⟩ :=
                            cone_occ_hdr_ok hlen hw hnd har_eq hcr_ref hsz_core hgr0
                          have hsz_ar : (s.core.arena[cr.toNat + 2]?.getD 0#32).toNat = sz.toNat :=
                            hsz_core.symm
                          ds_to_group
                          refine sweep_cone_occ_clause_wp hAddCl rfl rfl rfl rfl rfl rfl
                            ?_ ?_ hlen hw hnd hcl0 h10240 hqi_lt hncw_lt hnv_w_mono hlen_w
                            hag_w hcone_w htmk_w hwk_w hcr_ref hng hsz_core hsz_ge3 hsz_le8
                            hcr_sz_le hsz_cv hcr3_bd hmw hstep_occ
                          · exact hcr_idx _ (by
                              rw [show (1 : BitVec 64) = 1#64 from rfl]; exact hp1)
                          · exact har_sz_idx _ (by
                              rw [hcr_idx _ (by
                                rw [show (1 : BitVec 64) = 1#64 from rfl]; exact hp1)]
                              rfl)
                  )))
          · ds_steps; exact hJ_ex () mo ⟨cls, st, hlen_st, hag_st, hcone_st, hmo⟩))

end LeanQbe.T.Examples.Kissat.FullDefSweep
