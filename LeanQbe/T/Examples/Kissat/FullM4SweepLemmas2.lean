module

public import LeanQbe.T.Examples.Kissat.FullM4SweepCone

/-!
# Kissat `D-Full` M4b — Units, Partition Classes, Variable, Dense, & Sparse Sweeping (`20..24/24`)

Completes all remaining `5/24` parametric `(Γ : Env)` `Func.wp` proofs:
- `20/24`: `full_m4_sweep_units_wp`
- `21/24`: `full_m4_sweep_classes_wp`
- `22/24`: `full_m4_sweep_var_wp`
- `23/24`: `full_m4_sweep_dense_wp`
- `24/24`: `full_m4_sweep_sat_wp` (`FullSparseInv` → `FullSparseInv`, `r = 20#64 → F0.Unsat`)
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
open scoped FullArenaTactics M4SweepTactics

/-! ## 1. Shared Semantic & Preservation Helpers -/

private theorem m4_list_getElem_congr {α : Type} {l : List α} {i j : Nat}
    (h : i = j) {hi : i < l.length} {hj : j < l.length} : l[i]'hi = l[j]'hj := by
  subst h; rfl

private theorem m4_tmkZero_congr {s s' : FullState} (h : M4TmkZero s)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (ht : s'.scratch.tarjan_mark = s.scratch.tarjan_mark) : M4TmkZero s' := by
  intro v hv; rw [ht]; exact h v (hcv ▸ hv)

private theorem m4_phtOk_congr_512 {nv : Nat} {scr scr' : List (BitVec 32)}
    (hnv : nv ≤ 512) (h : PhtOk nv scr) (heq : ∀ j < phtMerged, scr'[j]? = scr[j]?) :
    PhtOk nv scr' := by
  unfold phtMerged at heq; unfold PhtOk phtHead phtSz phtNext at h ⊢
  refine ⟨fun b hb => ?_, fun i hi => ?_⟩
  · rw [heq (256 + b) (by omega)]; exact h.1 b hb
  · rw [heq (1280 + i) (by omega)]; exact h.2 i hi

private theorem m4_k5ScratchInv_of_drop_eq {P : (Nat → Bool) → Prop} {scr scr' : List (BitVec 32)}
    (hlen : scr'.length = scr.length) (hge : ∀ i < scr.length, k5Base ≤ i → scr'[i]? = scr[i]?)
    (h : K512ScratchInv P scr) :
    K512ScratchInv P scr' ∧ k5StateOfScratch scr' = k5StateOfScratch scr := by
  have hdrop : scr'.drop k5Base = scr.drop k5Base := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j hj1 _
      have hj : k5Base + j < scr.length := by simp [hlen] at hj1; omega
      have hget := hge (k5Base + j) hj (by omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hj] at hget
      simpa [List.getElem_drop] using Option.some.inj hget
  have hst : k5StateOfScratch scr' = k5StateOfScratch scr := by
    unfold k5StateOfScratch; rw [hdrop]
  exact ⟨⟨hlen ▸ h.1, hlen ▸ h.2.1, by rw [hlen, hst]; exact h.2.2⟩, hst⟩

private theorem m4_fullDenseInvW_with_tmk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {tmk' : List (BitVec 32)}
    (ht : tmk'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with tarjan_mark := tmk' } } :=
  fullDenseInvW_with_fuel_scratch h { h.1.scratch_ok with tarjan_mark_len := ht } rfl rfl

private theorem m4_fullDenseInvW_with_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    (hu : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } :=
  fullDenseInvW_with_inconsistent h hu

private theorem m4_fullDenseInvW_after_addUnit {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' unfl' inc' ta' ba' qsi' qss' : BitVec 64}
    {phases' pt' pb' : List (BitVec 8)} {hp' ps' : List (BitVec 32)} {hl' : Nat}
    (s' : FullState)
    (hs'_def : s' =
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              cur_level := cl', unassigned := unass', unflushed := unfl',
                              inconsistent := inc' }
        scratch := { s.scratch with phases := phases', target_assigned := ta',
                                    best_assigned := ba', phases_target := pt',
                                    phases_best := pb', heap := hp', pos := ps',
                                    heap_len := hl', q_search_idx := qsi',
                                    q_search_stamp := qss' } })
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core) (hcl0 : cl' = 0) :
    FullDenseInvW c F0 F_cur s' :=
  fullDenseInvW_after_addUnit h s' hs'_def hlen' hw'
    ⟨⟨by rw [hs'_def], by rw [hs'_def]⟩, by rw [hs'_def], by rw [hs'_def], by rw [hs'_def],
      by rw [hs'_def], by rw [hs'_def], by rw [hs'_def], by rw [hs'_def]⟩ hcl0

private theorem m4_fullSparseInv_after_propagate {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)}
    {flags' lvl' rsns' trl' tp' wvec' arena' wstk' : List (BitVec 32)}
    {te' prop' wlen' : Nat}
    {unass' unfl' wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)}
    (s' : FullState)
    (hs'_def : s' =
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } })
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm : FullArenaPermEq s.core s'.core) :
    FullSparseInv c F0 s' := by
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hng
    dsimp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseLits] at hr hng ⊢
    rw [hperm.2.1] at hr
    have hpe := hperm.2.2 r hr
    rw [hpe.2.1] at hng
    have hnd0 := h.2.2.2.1 r hr hng
    exact (List.Perm.nodup_iff (hpe.2.2.map (· / 2))).mpr hnd0
  have hpres : FullProbeScratchPres s s' :=
    ⟨⟨by rw [hs'_def], by rw [hs'_def]⟩, by rw [hs'_def], by rw [hs'_def], by rw [hs'_def],
      by rw [hs'_def], by rw [hs'_def], by rw [hs'_def], by rw [hs'_def]⟩
  have hsub : ∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s' := fun ref href => by
    dsimp only [fullArenaClauseRefs] at href ⊢; rw [hperm.2.1]; exact href
  exact fullSparseInv_after_propagate h s' hs'_def hlen' hw' hnd' hpres hsub

private theorem m4_unit_lit_align {ws1 : List (BitVec 32)} {i gv wf : BitVec 32}
    (hi : i.toNat < 512) (hgv : gv.toNat < 2 ^ 31)
    (hws : (ws1[i.toNat]?.getD 0#32).toNat = gv.toNat) (hwf : wf = 0#32 ∨ wf = 1#32) :
    let test_lit := (i <<< (1 : Nat)) ||| wf
    let gl := (gv <<< (1 : Nat)) ||| (1#32 - wf)
    test_lit.toNat = 2 * i.toNat + wf.toNat ∧
    (test_lit ^^^ 1#32).toNat < 2 * 512 ∧
    gl.toNat = FullSweepFwdSpecs.coneLift ws1 (test_lit.toNat ^^^ 1) ∧
    gl.toNat = 2 * gv.toNat + (1 - wf.toNat) := by
  intro test_lit gl
  have hwf_lt : wf.toNat < 2 := by rcases hwf with rfl | rfl <;> decide
  have h1w_lt : (1#32 - wf).toNat < 2 := by rcases hwf with rfl | rfl <;> decide
  have htl : test_lit.toNat = 2 * i.toNat + wf.toNat :=
    FullSweepVarHelpers.bv32_shl1_or_pol i wf (by omega) hwf_lt
  have hgl : gl.toNat = 2 * gv.toNat + (1 - wf.toNat) := by
    rw [FullSweepVarHelpers.bv32_shl1_or_pol gv (1#32 - wf) hgv h1w_lt]
    rcases hwf with rfl | rfl <;> rfl
  have hlift : FullSweepFwdSpecs.coneLift ws1 (test_lit.toNat ^^^ 1) =
      2 * gv.toNat + (1 - wf.toNat) := by
    unfold FullSweepFwdSpecs.coneLift; rw [htl]
    rcases hwf with rfl | rfl
    · have hx : (2 * i.toNat + 0) ^^^ 1 = 2 * i.toNat + 1 := (nat_2x_xor1 i.toNat).1
      rw [show (0#32).toNat = 0 from rfl, hx]
      simp [show (2 * i.toNat + 1) / 2 = i.toNat by omega,
        show (2 * i.toNat + 1) % 2 = 1 by omega, hws]; omega
    · have hx : (2 * i.toNat + 1) ^^^ 1 = 2 * i.toNat := (nat_2x_xor1 i.toNat).2
      rw [show (1#32).toNat = 1 from rfl, hx]
      simp [hws]; omega
  refine ⟨htl, ?_, hgl.trans hlift.symm, hgl⟩
  have := (k5_bv32_xor1_lt (nv := 512) (l := test_lit) (by omega)).2; exact this

private theorem m4_bin_lits_align {ws1 : List (BitVec 32)} {a c gv_a gv_c pol : BitVec 32}
    (ha : a.toNat < 512) (hc : c.toNat < 512)
    (hgva : gv_a.toNat < 2 ^ 31) (hgvc : gv_c.toNat < 2 ^ 31)
    (hwsa : (ws1[a.toNat]?.getD 0#32).toNat = gv_a.toNat)
    (hwsc : (ws1[c.toNat]?.getD 0#32).toNat = gv_c.toNat)
    (hpol : pol = 0#32 ∨ pol = 1#32) :
    let la := gv_a <<< (1 : Nat)
    let lc := (gv_c <<< (1 : Nat)) ||| pol
    let a0_1 := a <<< (1 : Nat)
    let a1_1 := (c <<< (1 : Nat)) ||| (1#32 ^^^ pol)
    let a0_2 := (a <<< (1 : Nat)) ||| 1#32
    let a1_2 := (c <<< (1 : Nat)) ||| pol
    a0_1.toNat = 2 * a.toNat ∧ a1_1.toNat = 2 * c.toNat + (1#32 ^^^ pol).toNat ∧
    a0_2.toNat = 2 * a.toNat + 1 ∧ a1_2.toNat = 2 * c.toNat + pol.toNat ∧
    ((a <<< (1 : Nat)) ^^^ 1#32).toNat = a0_1.toNat ^^^ 1 ∧
    ((c <<< (1 : Nat)) ||| pol).toNat = a1_1.toNat ^^^ 1 ∧
    (a <<< (1 : Nat)).toNat = a0_2.toNat ^^^ 1 ∧
    (((c <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat = a1_2.toNat ^^^ 1 ∧
    (la ^^^ 1#32).toNat = FullSweepFwdSpecs.coneLift ws1 (a0_1.toNat ^^^ 1) ∧
    lc.toNat = FullSweepFwdSpecs.coneLift ws1 (a1_1.toNat ^^^ 1) ∧
    la.toNat = FullSweepFwdSpecs.coneLift ws1 (a0_2.toNat ^^^ 1) ∧
    (lc ^^^ 1#32).toNat = FullSweepFwdSpecs.coneLift ws1 (a1_2.toNat ^^^ 1) := by
  intro la lc a0_1 a1_1 a0_2 a1_2
  have hp_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have hxp_lt : (1#32 ^^^ pol).toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have ha01 : a0_1.toNat = 2 * a.toNat := by dsimp [a0_1]; bv_omega
  have ha11 : a1_1.toNat = 2 * c.toNat + (1#32 ^^^ pol).toNat :=
    FullSweepVarHelpers.bv32_shl1_or_pol c (1#32 ^^^ pol) (by omega) hxp_lt
  have ha02 : a0_2.toNat = 2 * a.toNat + 1 :=
    FullSweepVarHelpers.bv32_shl1_or_pol a 1#32 (by omega) (by decide)
  have ha12 : a1_2.toNat = 2 * c.toNat + pol.toNat :=
    FullSweepVarHelpers.bv32_shl1_or_pol c pol (by omega) hp_lt
  have hla : la.toNat = 2 * gv_a.toNat := by dsimp [la]; bv_omega
  have hlc : lc.toNat = 2 * gv_c.toNat + pol.toNat :=
    FullSweepVarHelpers.bv32_shl1_or_pol gv_c pol hgvc hp_lt
  refine ⟨ha01, ha11, ha02, ha12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl]
  · rw [ha12, ha11]
    rcases hpol with rfl | rfl
    · simpa [show (0#32).toNat = 0 from rfl, show (1#32 ^^^ 0#32).toNat = 1 from rfl] using
        (nat_2x_xor1 c.toNat).2.symm
    · simpa [show (1#32).toNat = 1 from rfl, show (1#32 ^^^ 1#32).toNat = 0 from rfl] using
        (nat_2x_xor1 c.toNat).1.symm
  · rw [ha01, ha02]; exact (nat_2x_xor1 a.toNat).2.symm
  · rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl]
  · unfold FullSweepFwdSpecs.coneLift
    rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, hla, ha01, (nat_2x_xor1 gv_a.toNat).1,
      (nat_2x_xor1 a.toNat).1]
    simp [show (2 * a.toNat + 1) / 2 = a.toNat by omega,
      show (2 * a.toNat + 1) % 2 = 1 by omega, hwsa]; omega
  · unfold FullSweepFwdSpecs.coneLift; rw [hlc, ha11]
    rcases hpol with rfl | rfl
    · rw [show (0#32).toNat = 0 from rfl, show (1#32 ^^^ 0#32).toNat = 1 from rfl,
        (nat_2x_xor1 c.toNat).2]; simp [hwsc]; omega
    · simp only [show (1#32).toNat = 1 from rfl, show (1#32 ^^^ 1#32).toNat = 0 from rfl,
        Nat.add_zero, (nat_2x_xor1 c.toNat).1]
      simp [show (2 * c.toNat + 1) / 2 = c.toNat by omega,
        show (2 * c.toNat + 1) % 2 = 1 by omega, hwsc]; omega
  · unfold FullSweepFwdSpecs.coneLift; rw [hla, ha02, (nat_2x_xor1 a.toNat).2]; simp [hwsa]; omega
  · unfold FullSweepFwdSpecs.coneLift
    rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, hlc, ha12]
    rcases hpol with rfl | rfl
    · rw [show (0#32).toNat = 0 from rfl, Nat.add_zero, Nat.add_zero,
        (nat_2x_xor1 gv_c.toNat).1, (nat_2x_xor1 c.toNat).1]
      simp [show (2 * c.toNat + 1) / 2 = c.toNat by omega,
        show (2 * c.toNat + 1) % 2 = 1 by omega, hwsc]; omega
    · rw [show (1#32).toNat = 1 from rfl, (nat_2x_xor1 gv_c.toNat).2, (nat_2x_xor1 c.toNat).2]
      simp [hwsc]; omega

/-! ## 2. `full_m4_sweep_units_wp` (`20/24`) -/

theorem full_m4_sweep_units_wp (Γ : Env)
    (hFlip : M4EnvSpec Γ "full_k512_flip" k5FlipSpec)
    (hRef : M4EnvSpec Γ "full_m4_sweep_refine_sig" m4SweepRefineSigSpec)
    (hSolve : M4EnvSpec Γ "full_k512_solve" k5SolveSpec)
    (hAddU : M4EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hLive : M4EnvSpec Γ "full_k512_add_live" k5AddLiveSpec)
    (hRearm : M4EnvSpec Γ "full_m4_sweep_rearm" m4SweepRearmSpec) :
    ∀ args m Q X, m4SweepUnitsSpec args m Q X →
      Func.wp Γ full_m4_sweep_units_body args m Q X := by
  rintro ⟨h, nv, rbit_in, tick_lim, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcone, hrb_in, hm, hQ⟩
  obtain ⟨hnv1, hnv512, hnv_cv, hws_lt, hK0, hnv_eq⟩ := hcone
  have hlen := hinv.1
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hcap : k5MinScr ≤ c.scratch_cap := hscr_len ▸ hK0.1
  have hnv_mx : nv.toNat ≤ 2 * c.max_vars := by omega
  let ws1 := s.scratch.work_stk1
  let tmk := s.scratch.tarjan_mark
  let P := ConeModelSet F_cur ws1 nv.toNat
  have hnv_bv : (k5StateOfScratch s.scratch.scratch_buf).nv = nv := by
    rw [hnv_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold Func.wp full_m4_sweep_units_body
  m4_to_group
  -- Loop 1: zero `scr[PHT_MERGED + i] = 0u` for `i < nv`
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) m1 => i.toNat ≤ nv.toNat ∧ ∃ scr1 : List (BitVec 32),
      scr1.length = c.scratch_cap ∧ K512ScratchInv P scr1 ∧ (k5StateOfScratch scr1).nv = nv ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R) m1)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun _ hJ0 => by
      m4_steps
      exact hJ0 (0#32, ()) m ⟨Nat.zero_le _, s.scratch.scratch_buf, hscr_len, hK0, hnv_bv, hm⟩)
    (fun _ (i, ()) m1 ⟨hi_le, scr1, hsl1, hK1, hnv1_eq, hm1⟩ hJ0 => by
      m4_split
      · have hi_lt : i.toNat < nv.toNat := by bv_omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
          m4_bv32_add1 (by unfold k5MaxV at hnv512; omega)
        have hmg_eq : ((1792 + i).setWidth 64).toNat = 1792 + i.toNat := by
          rw [bv_c0_zext32_64]; unfold k5MaxV at hnv512; bv_omega
        have hmg_bd : ((1792 + i).setWidth 64).toNat < scr1.length := by
          rw [hsl1, hmg_eq]; unfold k5MinScr at hcap; unfold k5MaxV at hnv512; omega
        have hmg_lt_k5 : ((1792 + i).setWidth 64).toNat < k5Base := by
          rw [hmg_eq]; unfold k5Base; unfold k5MaxV at hnv512; omega
        m4_steps
        exact hJ0 (i + 1#32, ()) _ (by dsimp only; omega)
          ⟨by omega, _, List.length_set.trans hsl1, k5ScratchInv_set_lt 0#32 hmg_lt_k5 hK1,
           by rw [k5StateOfScratch_set_lt 0#32 hmg_lt_k5, hnv1_eq], by assumption⟩
      · -- Compute `smask`
        let s1 : FullState := { s with scratch := { s.scratch with scratch_buf := scr1 } }
        have hinv1 : FullDenseInvW c F0 F_cur s1 :=
          fullDenseInvW_with_fuel_scratch hinv { hlen.scratch_ok with scratch_buf_len := hsl1 }
            rfl rfl
        have hcone1 : M4SweepConeOk F_cur s1 nv.toNat :=
          ⟨hnv1, hnv512, hnv_cv, hws_lt, hK1,
           by rw [hnv1_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
        m4_to_group
        refine wp_join_group (ts := [i64])
          (fun (smask0, ()) ms => ms = m1)
          (fun _ (smask0, ()) ms hms => by
            subst ms
            m4_to_group
            -- Main loop 2: `while (i < nv && h->inconsistent == 0 && h->fuel > 0)`
            let UState (rbit : BitVec 32) (mU : Mem 64) : Prop :=
              rbit.toNat ≤ 64 ∧ ∃ sU : FullState,
                FullDenseInvW c F0 F_cur sU ∧ sU.core.cur_vars = s.core.cur_vars ∧
                sU.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                sU.scratch.work_stk1 = ws1 ∧ sU.scratch.tarjan_mark = tmk ∧
                M4SweepConeOk F_cur sU nv.toNat ∧ (FullMem c sU ⋆ R) mU
            refine wp_loop_inv (ts := [i32, i32, i64])
              (fun (i, rbit, _smask, ()) ml => i.toNat ≤ nv.toNat ∧ UState rbit ml)
              (fun (i, _, _, ()) _ => nv.toNat - i.toNat)
              (fun _ hJu => by
                m4_steps
                exact hJu (0#32, rbit_in, smask0, ()) m1
                  ⟨Nat.zero_le _, hrb_in, s1, hinv1, rfl, le_refl _, rfl, rfl, hcone1, hm1⟩)
              (fun _ (i, rbit, smask, ()) ml
                  ⟨hi_le, hrb_le, sL, hinvL, hcvL, hfuelL, hwsL, htmkL, hconeL, hml⟩ hJu => by
                m4_to_group
                refine wp_join_group (ts := [])
                  (fun () m_ex => m_ex = ml)
                  (fun _ () m_ex hm_ex => by
                    subst m_ex
                    -- Exit: `return (h->inconsistent != 0ULL) ? -1ULL : (u64)rbit`
                    m4_to_group; refine wp_unroll_group fun _ _ => ?_
                    m4_split
                    · have hinc : sL.core.inconsistent ≠ 0#64 := by bv_omega
                      have huns : F0.Unsat :=
                        hinvL.2.1.ext_sound.2 (hinvL.2.1.inconsistent_sound hinc)
                      m4_steps
                      exact hQ 0xFFFFFFFFFFFFFFFF#64 sL ml hinvL hcvL hfuelL hwsL htmkL hconeL
                        (fun _ => huns) (fun h => absurd rfl h) hml
                    · m4_steps
                      have hrb64 : (rbit.setWidth 64).toNat ≤ 64 := by
                        rw [bv_c0_zext32_64]; exact hrb_le
                      have hne_ff : rbit.setWidth 64 ≠ 0xFFFFFFFFFFFFFFFF#64 := by
                        intro h; rw [h] at hrb64; revert hrb64; decide
                      exact hQ (rbit.setWidth 64) sL ml hinvL hcvL hfuelL hwsL htmkL hconeL
                        (fun h => absurd h hne_ff) (fun _ => hrb64) hml)
                  (fun _ hJex => by
                    have hk11L : 2304 + (BitVec.ofNat 64 11).toNat <
                        sL.scratch.scratch_buf.length := by
                      rw [hinvL.1.scratch_ok.scratch_buf_len]; unfold k5MinScr at hcap; simp; omega
                    m4_split; rotate_left; · m4_steps; exact hJex () ml rfl
                    m4_split; rotate_left; · m4_steps; exact hJex () ml rfl
                    m4_split; rotate_left; · m4_steps; exact hJex () ml rfl
                    m4_split; rotate_left; · m4_steps; exact hJex () ml rfl
                    have hi_lt : i.toNat < nv.toNat := by bv_omega
                    have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
                      m4_bv32_add1 (by unfold k5MaxV at hnv512; omega)
                    have hlenL := hinvL.1
                    have hwsL_len := hlenL.scratch_ok.work_stk1_len
                    have hvalL_len := hlenL.core_ok.vals_len
                    have hsigL_len := hlenL.scratch_ok.sim_sig_len
                    have hscrL_len := hlenL.scratch_ok.scratch_buf_len
                    have hKL : K512ScratchInv P sL.scratch.scratch_buf := by
                      dsimp only [P]; rw [← hwsL]; exact hconeL.2.2.2.2.1
                    have hnvL : (k5StateOfScratch sL.scratch.scratch_buf).nv = nv := by
                      rw [hconeL.2.2.2.2.2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
                    have hi_ws : (i.setWidth 64).toNat < sL.scratch.work_stk1.length := by
                      rw [hwsL_len, bv_c0_zext32_64]; omega
                    let gv := sL.scratch.work_stk1[(i.setWidth 64).toNat]'hi_ws
                    have hgv_eq_ws : (ws1[i.toNat]?.getD 0#32).toNat = gv.toNat := by
                      dsimp only [gv]
                      rw [← hwsL, List.getElem?_eq_getElem (by rw [hwsL_len]; omega),
                        Option.getD_some]
                      exact congrArg BitVec.toNat (m4_list_getElem_congr (bv_c0_zext32_64 i).symm)
                    have hgv_lt : gv.toNat < s.core.cur_vars := by
                      rw [← hgv_eq_ws]; exact hws_lt i.toNat hi_lt
                    have hgv_ltL : gv.toNat < sL.core.cur_vars := hcvL ▸ hgv_lt
                    have h2gv_lt : ((gv <<< (1 : Nat)).setWidth 64).toNat < sL.core.vals.length :=
                      by
                      rw [hvalL_len, bv_c0_zext32_64]; bv_omega
                    have hmg_eq : ((1792 + i).setWidth 64).toNat = 1792 + i.toNat := by
                      rw [bv_c0_zext32_64]; unfold k5MaxV at hnv512; bv_omega
                    have hmg_bd : ((1792 + i).setWidth 64).toNat < sL.scratch.scratch_buf.length :=
                      by
                      rw [hscrL_len, hmg_eq]; unfold k5MinScr at hcap; unfold k5MaxV at hnv512
                      omega
                    have hmg_lt_k5 : ((1792 + i).setWidth 64).toNat < k5Base := by
                      rw [hmg_eq]; unfold k5Base; unfold k5MaxV at hnv512; omega
                    m4_split
                    · -- Already assigned (`vals[gv << 1] != 0`): mark merged and continue
                      m4_steps
                      let scrM := sL.scratch.scratch_buf.set ((1792 + i).setWidth 64).toNat 1#32
                      let sM : FullState :=
                        { sL with scratch := { sL.scratch with scratch_buf := scrM } }
                      have hinvM : FullDenseInvW c F0 F_cur sM :=
                        fullDenseInvW_with_fuel_scratch hinvL
                          { hlenL.scratch_ok with
                            scratch_buf_len := List.length_set.trans hscrL_len }
                          rfl rfl
                      have hKM := k5ScratchInv_set_lt 1#32 hmg_lt_k5 hKL
                      have hnvM : (k5StateOfScratch scrM).nv = nv := by
                        rw [k5StateOfScratch_set_lt 1#32 hmg_lt_k5, hnvL]
                      exact hJu (i + 1#32, rbit, smask, ()) _ (by dsimp only; omega)
                        ⟨by omega, hrb_le, sM, hinvM, hcvL, hfuelL, hwsL, htmkL,
                         ⟨hnv1, hnv512, hcvL.symm ▸ hnv_cv,
                          fun j hj => by rw [hwsL, hcvL]; exact hws_lt j hj,
                          by rw [hwsL]; exact hKM,
                          by rw [hnvM, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩, by assumption⟩
                    · -- Unassigned `gv`: inspect `s0 = sig[gv] & smask`
                      have hgv_sig : (gv.setWidth 64).toNat < sL.scratch.sim_sig.length := by
                        rw [hsigL_len, bv_c0_zext32_64]; omega
                      m4_to_group
                      refine wp_join_group (ts := [i32, i64])
                        (fun (rbitN, _smaskN, ()) mN => UState rbitN mN)
                        (fun _ (rbitN, smaskN, ()) mN hN => by
                          m4_steps
                          exact hJu (i + 1#32, rbitN, smaskN, ()) mN (by dsimp only; omega)
                            ⟨by omega, hN⟩)
                        (fun _ hJif => by
                          refine wp_join_group (ts := [])
                            (fun () mdo => mdo = ml)
                            (fun _ () mdo hmdo => by
                              subst mdo
                              m4_to_group
                              refine wp_join_group (ts := [i32])
                                (fun (wf, ()) mwf => mwf = ml ∧ (wf = 0#32 ∨ wf = 1#32))
                                (fun _ (wf, ()) mwf ⟨hmwf, hwf⟩ => by
                                  subst mwf
                                  let test_lit : BitVec 32 := (i <<< (1 : Nat)) ||| wf
                                  obtain ⟨htl_eq, htl_x_512, hgl_lift, hgl_eq⟩ :=
                                    m4_unit_lit_align (by unfold k5MaxV at hnv512; omega) (by omega)
                                      hgv_eq_ws hwf
                                  have hwf_lt : wf.toNat < 2 := by
                                    rcases hwf with rfl | rfl <;> decide
                                  have htl_lt : test_lit.toNat < 2 * nv.toNat := by
                                    dsimp only [test_lit]; omega
                                  have htl_x_lt : (test_lit ^^^ 1#32).toNat < 2 * nv.toNat :=
                                    (k5_bv32_xor1_lt htl_lt).2
                                  m4_steps
                                  m4_call hFlip
                                  refine ⟨c, sL, P, R, rfl, hlenL, hKL,
                                    by rw [hnvL]; exact htl_x_lt,
                                    hml, fun okF scrF mF hlenF _ hKF hnvF _ _ hmF => ?_⟩
                                  let sF : FullState :=
                                    { sL with scratch := { sL.scratch with scratch_buf := scrF } }
                                  have hscrF_len := hlenF.scratch_ok.scratch_buf_len
                                  have hinvF : FullDenseInvW c F0 F_cur sF :=
                                    fullDenseInvW_with_fuel_scratch hinvL hlenF.scratch_ok rfl rfl
                                  have hnvF' : (k5StateOfScratch scrF).nv = nv := hnvF.trans hnvL
                                  have hconeF : M4SweepConeOk F_cur sF nv.toNat :=
                                    ⟨hnv1, hnv512, hcvL.symm ▸ hnv_cv,
                                     fun j hj => by rw [hwsL, hcvL]; exact hws_lt j hj,
                                     by rw [hwsL]; exact hKF,
                                     by rw [hnvF', BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
                                  m4_split
                                  · -- `flip` succeeded: refine if `rbit < 64`
                                    m4_to_group; refine wp_unroll_group fun _ _ => ?_
                                    m4_split; rotate_left
                                    · m4_steps
                                      exact hJif (rbit, smask, ()) mF
                                        ⟨hrb_le, sF, hinvF, hcvL, hfuelL, hwsL, htmkL, hconeF, hmF⟩
                                    have hrb_lt : rbit.toNat < 64 := by bv_omega
                                    have hrb1 : (rbit + 1#32).toNat = rbit.toNat + 1 :=
                                      m4_bv32_add1 (by omega)
                                    m4_call hRef
                                    refine ⟨c, sF, R, rfl, hlenF, hcap, hnv512, hnv_mx,
                                      fun j hj => by rw [hwsL, hcvL]; exact hws_lt j hj,
                                      hmF, fun sigR mR hsigR hmR => ?_⟩
                                    let sR : FullState :=
                                      { sF with scratch := { sF.scratch with sim_sig := sigR } }
                                    m4_steps
                                    exact hJif (rbit + 1#32, _, ())
                                      mR ⟨by omega, sR, fullDenseInvW_after_refine hinvF hsigR,
                                        hcvL,
                                        hfuelL, hwsL, htmkL, hconeF, hmR⟩
                                  · -- `flip` failed: solve under `[test_lit]`
                                    have hk11F : 2304 + (BitVec.ofNat 64 11).toNat < scrF.length :=
                                      by
                                      rw [hscrF_len]; unfold k5MinScr at hcap; simp; omega
                                    have hk15 : 2304 + (BitVec.ofNat 64 15).toNat < scrF.length :=
                                      by
                                      rw [hscrF_len]; unfold k5MinScr at hcap; simp; omega
                                    have hk4640 :
                                        2304 + (BitVec.ofNat 64 4640).toNat < scrF.length := by
                                      rw [hscrF_len]; unfold k5MinScr at hcap; simp; omega
                                    have h15_eq :
                                        2304 + (BitVec.ofNat 64 15).toNat = k5Base + 15 := by decide
                                    have h4640_eq :
                                        2304 + (BitVec.ofNat 64 4640).toNat = k5Base + 4640 := by
                                      decide
                                    obtain ⟨hKA, hnvA, hassA⟩ :=
                                      k5ScratchInv_set_assump1 (a0 := test_lit)
                                        (by rw [hnvF']; exact htl_lt) hKF
                                    m4_steps
                                    let scrA :=
                                      (scrF.set (k5Base + 15) 1#32).set (k5Base + 4640) test_lit
                                    let sA : FullState :=
                                      { sF with scratch := { sF.scratch with scratch_buf := scrA } }
                                    have hlenA : sA.LengthsOk c :=
                                      ⟨hlenF.core_ok, { hlenF.scratch_ok with
                                        scratch_buf_len :=
                                          List.length_set.trans
                                            (List.length_set.trans hscrF_len) }⟩
                                    m4_call hSolve
                                    refine ⟨c, sA, P, R, rfl, hlenA, hKA,
                                      by simpa only [sA, scrA, h15_eq, h4640_eq] using
                                        ‹(FullMem c _ ⋆ R) _›,
                                      fun d fuelS scrS mS hlenS hfuelS _ hKS hnvS _ hassS _ hunsS
                                        hmS => ?_⟩
                                    let sS : FullState :=
                                      { sA with
                                        core := { sA.core with fuel := fuelS }
                                        scratch := { sA.scratch with scratch_buf := scrS } }
                                    have hscrS_len := hlenS.scratch_ok.scratch_buf_len
                                    have hinvS : FullDenseInvW c F0 F_cur sS :=
                                      fullDenseInvW_with_fuel_scratch hinvF hlenS.scratch_ok rfl rfl
                                    have hfuelS0 : fuelS.toNat ≤ s.core.fuel.toNat :=
                                      Nat.le_trans hfuelS hfuelL
                                    have hnvS' : (k5StateOfScratch scrS).nv = nv :=
                                      hnvS.trans (hnvA.trans hnvF')
                                    have hconeS : M4SweepConeOk F_cur sS nv.toNat :=
                                      ⟨hnv1, hnv512, hcvL.symm ▸ hnv_cv,
                                       fun j hj => by rw [hwsL, hcvL]; exact hws_lt j hj,
                                       by rw [hwsL]; exact hKS,
                                       by rw [hnvS', BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
                                    m4_to_group; refine wp_unroll_group fun _ _ => ?_
                                    m4_split
                                    · -- `d == 20ULL`: add global unit, mark merged, add live, rearm
                                      have hd20 : d = 20#64 := by bv_omega
                                      have huns_t :
                                          ∀ β, P β → ¬ (unitsCnf [test_lit.toNat]).Sat β := by
                                        intro β hβ; have := hunsS hd20 β hβ
                                        rwa [hassS, hassA] at this
                                      obtain ⟨hsem_u, hent_u⟩ :=
                                        coneModelSet_unsat_unit htl_lt huns_t
                                      let gl : BitVec 32 := (gv <<< (1 : Nat)) ||| (1#32 - wf)
                                      have hgl_lt : gl.toNat < 2 * sS.core.cur_vars := by
                                        change gl.toNat < 2 * sL.core.cur_vars
                                        dsimp only [gl]; omega
                                      m4_steps
                                      m4_call hAddU
                                      refine ⟨c, F0, F_cur, sS, R, rfl, hlenS, hinvS.2.1,
                                        fun _ => by
                                          dsimp only [Arg.val]
                                          change (cnfOfClauses F_cur).EntailsClause
                                            (cnfClause [gl.toNat])
                                          rw [hgl_lift]; exact hent_u,
                                        hmS, ?_⟩
                                      intro okU valsU flagsU lvlU rsnsU trlU tpU teU propU clU
                                        unassU
                                        unflU incU phasesU taU baU ptU pbU hpU psU hlU qsiU qssU mU
                                          _
                                        hlenU hwU hclU hokF _ hmU
                                      obtain ⟨sU, hsU⟩ : ∃ sU : FullState, sU =
                                        { sS with
                                          core := { sS.core with
                                            vals := valsU, flags := flagsU, lvl := lvlU,
                                            rsns := rsnsU, trl := trlU, trail_pos := tpU,
                                            trail_end := teU, propagated := propU, cur_level := clU,
                                            unassigned := unassU, unflushed := unflU,
                                            inconsistent := incU }
                                          scratch := { sS.scratch with
                                            phases := phasesU, target_assigned := taU,
                                            best_assigned := baU, phases_target := ptU,
                                            phases_best := pbU, heap := hpU, pos := psU,
                                            heap_len := hlU, q_search_idx := qsiU,
                                            q_search_stamp := qssU } } := ⟨_, rfl⟩
                                      have hinvU := m4_fullDenseInvW_after_addUnit hinvS sU hsU
                                        (hsU ▸ hlenU) (hsU ▸ hwU) hclU
                                      have hcvU : sU.core.cur_vars = s.core.cur_vars := by
                                        rw [hsU]; exact hcvL
                                      have hfuelU : sU.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                        rw [hsU]; exact hfuelS0
                                      have hwsU : sU.scratch.work_stk1 = ws1 := by
                                        rw [hsU]; exact hwsL
                                      have htmkU : sU.scratch.tarjan_mark = tmk := by
                                        rw [hsU]; exact htmkL
                                      have hscrU : sU.scratch.scratch_buf = scrS := by rw [hsU]
                                      have hconeU : M4SweepConeOk F_cur sU nv.toNat :=
                                        ⟨hnv1, hnv512, hcvU.symm ▸ hnv_cv,
                                         fun j hj => by rw [hwsU, hcvU]; exact hws_lt j hj,
                                         by rw [hwsU, hscrU]; exact hKS,
                                         by rw [hscrU, hnvS', BitVec.ofNat_toNat,
                                           BitVec.setWidth_eq]⟩
                                      have hmU' : (FullMem c sU ⋆ R) mU := hsU ▸ hmU
                                      m4_split; rotate_left
                                      · have hok_f : okU = false := by cases okU <;> simp at hc ⊢
                                        m4_steps
                                        exact hQ 0xFFFFFFFFFFFFFFFF#64 sU mU hinvU hcvU hfuelU hwsU
                                          htmkU hconeU (fun _ => (hokF hgl_lt hok_f).1)
                                          (fun h => absurd rfl h) hmU'
                                      have hmgU_bd : ((1792 + i).setWidth 64).toNat <
                                          sU.scratch.scratch_buf.length := by
                                        rw [hscrU, hscrS_len, hmg_eq]
                                        unfold k5MinScr at hcap; unfold k5MaxV at hnv512; omega
                                      m4_steps
                                      let scrM2 := sU.scratch.scratch_buf.set
                                        ((1792 + i).setWidth 64).toNat 1#32
                                      let sM2 : FullState :=
                                        { sU with scratch := { sU.scratch with
                                          scratch_buf := scrM2 } }
                                      have hlenM2 : sM2.LengthsOk c :=
                                        ⟨hinvU.1.core_ok, { hinvU.1.scratch_ok with
                                          scratch_buf_len :=
                                            List.length_set.trans (hscrU ▸ hscrS_len) }⟩
                                      have hinvM2 : FullDenseInvW c F0 F_cur sM2 :=
                                        fullDenseInvW_with_fuel_scratch hinvU hlenM2.scratch_ok
                                          rfl rfl
                                      have hKM2 : K512ScratchInv P scrM2 :=
                                        k5ScratchInv_set_lt 1#32 hmg_lt_k5 (hscrU.symm ▸ hKS)
                                      have hnvM2 : (k5StateOfScratch scrM2).nv = nv := by
                                        rw [k5StateOfScratch_set_lt 1#32 hmg_lt_k5, hscrU, hnvS']
                                      have hsem_u' : SemEntails P [(test_lit ^^^ 1#32).toNat] := by
                                        rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl]
                                        exact hsem_u
                                      m4_call hLive
                                      refine ⟨c, sM2, P, R, rfl, hlenM2, hKM2,
                                        by dsimp only [Arg.val]
                                           change (test_lit ^^^ 1#32).toNat <
                                             2 * (k5StateOfScratch scrM2).nv.toNat
                                           rw [hnvM2]; exact htl_x_lt,
                                        fun _ => by
                                          dsimp only [Arg.val]
                                          change SemEntails P [(test_lit ^^^ 1#32).toNat]
                                          exact hsem_u',
                                        fun h => absurd rfl h, by assumption,
                                        fun scrL2 mL2 hlenL2 _ hKL2 _ hnvL2 _ _ hmL2 => ?_⟩
                                      let sL2 : FullState :=
                                        { sM2 with scratch := { sM2.scratch with
                                          scratch_buf := scrL2 } }
                                      have hinvL2 : FullDenseInvW c F0 F_cur sL2 :=
                                        fullDenseInvW_with_fuel_scratch hinvM2 hlenL2.scratch_ok
                                          rfl rfl
                                      have hnvL2' : (k5StateOfScratch scrL2).nv = nv :=
                                        hnvL2.trans hnvM2
                                      m4_call hRearm
                                      refine ⟨c, F0, F_cur, sL2, R, rfl, hinvL2, hmL2,
                                        fun flR mR hflR hinvR hmR => ?_⟩
                                      let sR2 : FullState :=
                                        { sL2 with core := { sL2.core with flags := flR } }
                                      m4_steps
                                      let sC2 : FullState :=
                                        { sR2 with scratch := { sR2.scratch with
                                          sweep_cnt := sR2.scratch.sweep_cnt + 1#64 } }
                                      have hinvC2 :=
                                        fullDenseInvW_with_sweep_cnt hinvR
                                          (sR2.scratch.sweep_cnt + 1#64)
                                      exact hJif (rbit, smask, ()) _
                                        ⟨hrb_le, sC2, hinvC2, hcvU, hfuelU, hwsU, htmkU,
                                         ⟨hnv1, hnv512, hcvU.symm ▸ hnv_cv,
                                          fun j hj => by rw [hwsU, hcvU]; exact hws_lt j hj,
                                          by rw [hwsU]; exact hKL2,
                                          by rw [hnvL2', BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩,
                                         by assumption⟩
                                    · -- `d != 20ULL`: refine if `d == 10ULL && rbit < 64u`
                                      m4_to_group; refine wp_unroll_group fun _ _ => ?_
                                      m4_split; rotate_left
                                      · m4_steps
                                        exact hJif (rbit, smask, ()) mS
                                          ⟨hrb_le, sS, hinvS, hcvL, hfuelS0, hwsL, htmkL,
                                           hconeS, hmS⟩
                                      m4_split; rotate_left
                                      · m4_steps
                                        exact hJif (rbit, smask, ()) mS
                                          ⟨hrb_le, sS, hinvS, hcvL, hfuelS0, hwsL, htmkL,
                                           hconeS, hmS⟩
                                      have hrb_lt : rbit.toNat < 64 := by bv_omega
                                      have hrb1 : (rbit + 1#32).toNat = rbit.toNat + 1 :=
                                        m4_bv32_add1 (by omega)
                                      m4_call hRef
                                      refine ⟨c, sS, R, rfl, hlenS, hcap, hnv512, hnv_mx,
                                        fun j hj => by rw [hwsL, hcvL]; exact hws_lt j hj,
                                        hmS, fun sigR mR hsigR hmR => ?_⟩
                                      let sR : FullState :=
                                        { sS with scratch := { sS.scratch with sim_sig := sigR } }
                                      m4_steps
                                      exact hJif (rbit + 1#32, _, ())
                                        mR ⟨by omega, sR, fullDenseInvW_after_refine hinvS hsigR,
                                          hcvL, hfuelS0, hwsL, htmkL, hconeS, hmR⟩)
                                (fun _ hJwf => by
                                  m4_split
                                  · m4_steps; exact hJwf (0#32, ()) ml ⟨rfl, Or.inl rfl⟩
                                  · m4_steps; exact hJwf (1#32, ()) ml ⟨rfl, Or.inr rfl⟩))
                            (fun _ hJdo => by
                              m4_split; · m4_steps; exact hJdo () ml rfl
                              m4_split; · m4_steps; exact hJdo () ml rfl
                              m4_steps
                              exact hJif (rbit, smask, ()) ml
                                ⟨hrb_le, sL, hinvL, hcvL, hfuelL, hwsL, htmkL, hconeL, hml⟩)))))
          (fun _ hJsm => by
            m4_split
            · m4_steps; exact hJsm _ m1 rfl
            · m4_steps; exact hJsm _ m1 rfl))

/-! ## 3. `full_m4_sweep_classes_wp` (`21/24`) -/

private structure M4ClassData (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (nv : BitVec 32) (rbit : BitVec 32) (R : Mem 64 → Prop)
    (m : Mem 64) where
  rbit_le : rbit.toNat ≤ 64
  st : FullState
  inv : FullDenseInvW c F0 F_cur st
  cv : st.core.cur_vars = s0.core.cur_vars
  fuel : st.core.fuel.toNat ≤ s0.core.fuel.toNat
  ws : st.scratch.work_stk1 = s0.scratch.work_stk1
  tmk : st.scratch.tarjan_mark = s0.scratch.tarjan_mark
  k5 : K512ScratchInv (ConeModelSet F_cur s0.scratch.work_stk1 nv.toNat) st.scratch.scratch_buf
  nv_eq : (k5StateOfScratch st.scratch.scratch_buf).nv = nv
  pht : PhtOk nv.toNat st.scratch.scratch_buf
  mem : (FullMem c st ⋆ R) m

private abbrev M4ClassState (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (nv : BitVec 32) (rbit : BitVec 32) (R : Mem 64 → Prop)
    (m : Mem 64) : Prop :=
  Nonempty (M4ClassData c F0 F_cur s0 nv rbit R m)

theorem full_m4_sweep_classes_wp (Γ : Env)
    (hPht : M4EnvSpec Γ "full_m4_sweep_build_pht" m4SweepBuildPhtSpec)
    (hFlip : M4EnvSpec Γ "full_k512_flip" k5FlipSpec)
    (hSolve : M4EnvSpec Γ "full_k512_solve" k5SolveSpec)
    (hRef : M4EnvSpec Γ "full_m4_sweep_refine_sig" m4SweepRefineSigSpec)
    (hAddB : M4EnvSpec Γ "full_add_bin" Full.fullAddBinSpec)
    (hLive : M4EnvSpec Γ "full_k512_add_live" k5AddLiveSpec)
    (hRearm : M4EnvSpec Γ "full_m4_sweep_rearm" m4SweepRearmSpec) :
    ∀ args m Q X, m4SweepClassesSpec args m Q X →
      Func.wp Γ full_m4_sweep_classes_body args m Q X := by
  rintro ⟨h, nv, rbit_in, tick_lim, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcone, hrb_in, hm, hQ⟩
  obtain ⟨hnv1, hnv512, hnv_cv, hws_lt, hK0, hnv_eq⟩ := hcone
  have hlen := hinv.1
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hcap : k5MinScr ≤ c.scratch_cap := hscr_len ▸ hK0.1
  have hnv_mx : nv.toNat ≤ 2 * c.max_vars := by omega
  let P := ConeModelSet F_cur s.scratch.work_stk1 nv.toNat
  have hnv_bv : (k5StateOfScratch s.scratch.scratch_buf).nv = nv := by
    rw [hnv_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold Func.wp full_m4_sweep_classes_body
  m4_to_group
  refine wp_join_group (ts := [i64])
    (fun (smask0, ()) ms => ms = m)
    (fun _ (smask0, ()) ms hms => by
      subst ms
      m4_call hPht
      refine ⟨c, s, R, rfl, hlen, hcap, hnv512, hnv_mx, hws_lt, hm,
        fun scr0 m0 hsl0 hpre0 hpht0 hm0 => ?_⟩
      obtain ⟨hK_pht, hst_pht⟩ := m4_k5ScratchInv_of_drop_eq
        (hsl0.trans hscr_len.symm)
        (fun i hi hge => hpre0 i (hscr_len ▸ hi) (Or.inr
          (by unfold phtMerged; unfold k5Base at hge; omega)))
        hK0
      let s0 : FullState := { s with scratch := { s.scratch with scratch_buf := scr0 } }
      have hinv0 : FullDenseInvW c F0 F_cur s0 :=
        fullDenseInvW_with_fuel_scratch hinv { hlen.scratch_ok with scratch_buf_len := hsl0 }
          rfl rfl
      have hcs0 : M4ClassState c F0 F_cur s nv rbit_in R m0 :=
        ⟨⟨hrb_in, s0, hinv0, rfl, le_refl _, rfl, rfl, hK_pht, by rw [hst_pht, hnv_bv], hpht0, hm0⟩⟩
      m4_to_group
      -- Outer loop: `b < PHT_SZ (1024)`
      refine wp_loop_inv (ts := [i32, i64, i32])
        (fun (rbitB, _smaskB, b,
          ()) mb => b.toNat ≤ phtSz ∧ M4ClassState c F0 F_cur s nv rbitB R mb)
        (fun (_, _, b, ()) _ => phtSz - b.toNat)
        (fun _ hJb => by m4_steps; exact hJb (rbit_in, smask0, 0#32, ()) m0 ⟨Nat.zero_le _, hcs0⟩)
        (fun _ (rbitB, smaskB, b, ()) mb ⟨hb_le, ⟨csB⟩⟩ hJb => by
          have hmb := csB.mem
          m4_to_group
          refine wp_join_group (ts := [])
            (fun () m_ex => m_ex = mb)
            (fun _ () m_ex hm_ex => by
              subst m_ex
              m4_to_group; refine wp_unroll_group fun _ _ => ?_
              m4_split
              · have hinc : csB.st.core.inconsistent ≠ 0#64 := by bv_omega
                have huns := csB.inv.2.1.ext_sound.2 (csB.inv.2.1.inconsistent_sound hinc)
                m4_steps
                exact hQ 20#64 csB.st mb csB.inv csB.cv csB.fuel csB.ws csB.tmk (Or.inr rfl)
                  (fun _ => huns) csB.mem
              · m4_steps
                exact hQ 1#64 csB.st mb csB.inv csB.cv csB.fuel csB.ws csB.tmk (Or.inl rfl)
                  (fun h => by cases h) csB.mem)
            (fun _ hJexB => by
              have hk11B : 2304 + (BitVec.ofNat 64 11).toNat <
                  csB.st.scratch.scratch_buf.length := by
                rw [csB.inv.1.scratch_ok.scratch_buf_len]; unfold k5MinScr at hcap; simp; omega
              m4_split; rotate_left; · m4_steps; exact hJexB () mb rfl
              m4_split; rotate_left; · m4_steps; exact hJexB () mb rfl
              m4_split; rotate_left; · m4_steps; exact hJexB () mb rfl
              m4_split; rotate_left; · m4_steps; exact hJexB () mb rfl
              have hb_lt : b.toNat < phtSz := by unfold phtSz; bv_omega
              have hb1 : (b + 1#32).toNat = b.toNat + 1 :=
                m4_bv32_add1 (by unfold phtSz at hb_lt; omega)
              have hhb_bd : ((256 + b).setWidth 64).toNat < csB.st.scratch.scratch_buf.length := by
                rw [csB.inv.1.scratch_ok.scratch_buf_len, bv_c0_zext32_64]
                have : (256 + b).toNat = 256 + b.toNat := by unfold phtSz at hb_lt; bv_omega
                rw [this]; unfold phtSz at hb_lt; unfold k5MinScr at hcap; omega
              m4_to_group
              -- Middle loop: `a = scr[PHT_HEAD + b]; while (a < nv && ...)`
              refine wp_loop_inv (ts := [i32, i64, i32])
                (fun (rbitA, _smaskA, a, ()) ma => M4ClassState c F0 F_cur s nv rbitA R ma)
                (fun (_, _, a, ()) _ => if a.toNat < nv.toNat then a.toNat + 1 else 0)
                (fun _ hJa => by m4_steps; exact hJa (rbitB, smaskB, _, ()) mb ⟨csB⟩)
                (fun _ (rbitA, smaskA, a, ()) ma ⟨csA⟩ hJa => by
                  have hma := csA.mem
                  m4_to_group
                  refine wp_join_group (ts := [])
                    (fun () m_nx => m_nx = ma)
                    (fun _ () m_nx hm_nx => by
                      subst m_nx
                      m4_steps
                      exact hJb (rbitA, smaskA, b + 1#32, ()) ma (by dsimp only; omega)
                        ⟨by omega, ⟨csA⟩⟩)
                    (fun _ hJnextB => by
                      have hk11A : 2304 + (BitVec.ofNat 64 11).toNat <
                          csA.st.scratch.scratch_buf.length := by
                        rw [csA.inv.1.scratch_ok.scratch_buf_len]; unfold k5MinScr at hcap; simp
                        omega
                      m4_split; rotate_left; · m4_steps; exact hJnextB () ma rfl
                      m4_split; rotate_left; · m4_steps; exact hJnextB () ma rfl
                      m4_split; rotate_left; · m4_steps; exact hJnextB () ma rfl
                      m4_split; rotate_left; · m4_steps; exact hJnextB () ma rfl
                      have ha_lt : a.toNat < nv.toNat := by bv_omega
                      have hlenA := csA.inv.1
                      have hscrA_len := hlenA.scratch_ok.scratch_buf_len
                      have hwsA_len := hlenA.scratch_ok.work_stk1_len
                      have ha_mg_eq : ((1792 + a).setWidth 64).toNat = 1792 + a.toNat := by
                        rw [bv_c0_zext32_64]; unfold k5MaxV at hnv512; bv_omega
                      have ha_mg_bd : ((1792 + a).setWidth 64).toNat <
                          csA.st.scratch.scratch_buf.length := by
                        rw [hscrA_len, ha_mg_eq]; unfold k5MinScr at hcap; unfold k5MaxV at hnv512
                        omega
                      have ha_nx_eq : ((1280 + a).setWidth 64).toNat = 1280 + a.toNat := by
                        rw [bv_c0_zext32_64]; unfold k5MaxV at hnv512; bv_omega
                      have ha_nx_bd : ((1280 + a).setWidth 64).toNat <
                          csA.st.scratch.scratch_buf.length := by
                        rw [hscrA_len, ha_nx_eq]; unfold k5MinScr at hcap; unfold k5MaxV at hnv512
                        omega
                      m4_to_group
                      refine wp_join_group (ts := [i32, i64])
                        (fun (rbitA', _smaskA',
                          ()) ma' => M4ClassState c F0 F_cur s nv rbitA' R ma')
                        (fun _ (rbitA', smaskA', ()) ma' ⟨csA'⟩ => by
                          have hma' := csA'.mem
                          have hlenA' := csA'.inv.1
                          have hnx_bd' : ((1280 + a).setWidth 64).toNat <
                              csA'.st.scratch.scratch_buf.length := by
                            rw [hlenA'.scratch_ok.scratch_buf_len, ha_nx_eq]
                            unfold k5MinScr at hcap; unfold k5MaxV at hnv512; omega
                          m4_steps
                          have hp_a := csA'.pht.2 a.toNat ha_lt
                          have hget_nx : csA'.st.scratch.scratch_buf[
                              ((1280 + a).setWidth 64).toNat]'hnx_bd' =
                              csA'.st.scratch.scratch_buf[phtNext + a.toNat]?.getD
                                0xFFFFFFFF#32 := by
                            rw [List.getElem?_eq_getElem
                                (by unfold phtNext; rw [← ha_nx_eq]; exact hnx_bd'),
                              Option.getD_some]
                            exact m4_list_getElem_congr (by unfold phtNext; exact ha_nx_eq)
                          refine hJa (rbitA', smaskA', _, ()) ma' ?_ ⟨csA'⟩
                          dsimp only
                          rw [hget_nx]
                          rcases hp_a with hff | hlt
                          · have hge : ¬ (0xFFFFFFFF#32).toNat < nv.toNat := by
                              unfold k5MaxV at hnv512; simp; omega
                            simp only [hff, ha_lt, hge, ↓reduceIte]; omega
                          · have hlt' : (csA'.st.scratch.scratch_buf[phtNext + a.toNat]?.getD
                                0xFFFFFFFF#32).toNat < nv.toNat := by omega
                            simp only [ha_lt, hlt', ↓reduceIte]; omega)
                        (fun _ hJifA => by
                          m4_split; rotate_left
                          · m4_steps; exact hJifA (rbitA, smaskA, ()) ma ⟨csA⟩
                          have ha_ws : (a.setWidth 64).toNat < csA.st.scratch.work_stk1.length := by
                            rw [hwsA_len, bv_c0_zext32_64]; omega
                          let gv_a := csA.st.scratch.work_stk1[(a.setWidth 64).toNat]'ha_ws
                          have hgva_ws : (s.scratch.work_stk1[a.toNat]?.getD 0#32).toNat =
                              gv_a.toNat := by
                            dsimp only [gv_a]
                            rw [← csA.ws, List.getElem?_eq_getElem (by rw [hwsA_len]; omega),
                              Option.getD_some]
                            exact congrArg BitVec.toNat
                              (m4_list_getElem_congr (bv_c0_zext32_64 a).symm)
                          have hgva_lt : gv_a.toNat < s.core.cur_vars := by
                            rw [← hgva_ws]; exact hws_lt a.toNat ha_lt
                          m4_to_group
                          -- Inner loop: `c = scr[PHT_NEXT + a]; while (c < nv && ...)`
                          refine wp_loop_inv (ts := [i32, i64, i32])
                            (fun (rbitC, _smaskC, cc, ()) mc =>
                              M4ClassState c F0 F_cur s nv rbitC R mc)
                            (fun (_, _, cc,
                              ()) _ => if cc.toNat < nv.toNat then cc.toNat + 1 else 0)
                            (fun _ hJc => by m4_steps; exact hJc (rbitA, smaskA, _, ()) ma ⟨csA⟩)
                            (fun _ (rbitC, smaskC, cc, ()) mc ⟨csC⟩ hJc => by
                              have hmc := csC.mem
                              have hk11C : 2304 + (BitVec.ofNat 64 11).toNat <
                                  csC.st.scratch.scratch_buf.length := by
                                rw [csC.inv.1.scratch_ok.scratch_buf_len]; unfold k5MinScr at hcap
                                simp; omega
                              m4_split; rotate_left
                              · m4_steps; exact hJifA (rbitC, smaskC, ()) mc ⟨csC⟩
                              m4_split; rotate_left
                              · m4_steps; exact hJifA (rbitC, smaskC, ()) mc ⟨csC⟩
                              m4_split; rotate_left
                              · m4_steps; exact hJifA (rbitC, smaskC, ()) mc ⟨csC⟩
                              m4_split; rotate_left
                              · m4_steps; exact hJifA (rbitC, smaskC, ()) mc ⟨csC⟩
                              have hc_lt : cc.toNat < nv.toNat := by bv_omega
                              have hlenC := csC.inv.1
                              have hscrC_len := hlenC.scratch_ok.scratch_buf_len
                              have hwsC_len := hlenC.scratch_ok.work_stk1_len
                              have hsigC_len := hlenC.scratch_ok.sim_sig_len
                              have hc_mg_eq : ((1792 + cc).setWidth 64).toNat = 1792 + cc.toNat :=
                                by
                                rw [bv_c0_zext32_64]; unfold k5MaxV at hnv512; bv_omega
                              have hc_mg_bd : ((1792 + cc).setWidth 64).toNat <
                                  csC.st.scratch.scratch_buf.length := by
                                rw [hscrC_len, hc_mg_eq]; unfold k5MinScr at hcap
                                unfold k5MaxV at hnv512; omega
                              have hc_nx_eq : ((1280 + cc).setWidth 64).toNat = 1280 + cc.toNat :=
                                by
                                rw [bv_c0_zext32_64]; unfold k5MaxV at hnv512; bv_omega
                              m4_to_group
                              refine wp_join_group (ts := [i32, i64])
                                (fun (rbitC', _smaskC', ()) mc' =>
                                  M4ClassState c F0 F_cur s nv rbitC' R mc')
                                (fun _ (rbitC', smaskC', ()) mc' ⟨csC'⟩ => by
                                  have hmc' := csC'.mem
                                  have hnxC_bd : ((1280 + cc).setWidth 64).toNat <
                                      csC'.st.scratch.scratch_buf.length := by
                                    rw [csC'.inv.1.scratch_ok.scratch_buf_len, hc_nx_eq]
                                    unfold k5MinScr at hcap; unfold k5MaxV at hnv512; omega
                                  m4_steps
                                  have hp_c := csC'.pht.2 cc.toNat hc_lt
                                  have hget_nx : csC'.st.scratch.scratch_buf[
                                      ((1280 + cc).setWidth 64).toNat]'hnxC_bd =
                                      csC'.st.scratch.scratch_buf[phtNext + cc.toNat]?.getD
                                        0xFFFFFFFF#32 := by
                                    rw [List.getElem?_eq_getElem
                                        (by unfold phtNext; rw [← hc_nx_eq]; exact hnxC_bd),
                                      Option.getD_some]
                                    exact m4_list_getElem_congr (by unfold phtNext; exact hc_nx_eq)
                                  refine hJc (rbitC', smaskC', _, ()) mc' ?_ ⟨csC'⟩
                                  dsimp only
                                  rw [hget_nx]
                                  rcases hp_c with hff | hlt
                                  · have hge : ¬ (0xFFFFFFFF#32).toNat < nv.toNat := by
                                      unfold k5MaxV at hnv512; simp; omega
                                    simp only [hff, hc_lt, hge, ↓reduceIte]; omega
                                  · have hlt' : (csC'.st.scratch.scratch_buf[phtNext +
                                    cc.toNat]?.getD
                                        0xFFFFFFFF#32).toNat < nv.toNat := by omega
                                    simp only [hc_lt, hlt', ↓reduceIte]; omega)
                                (fun _ hJifC => by
                                  m4_split; rotate_left
                                  · m4_steps; exact hJifC (rbitC, smaskC, ()) mc ⟨csC⟩
                                  have hc_ws : (cc.setWidth 64).toNat <
                                      csC.st.scratch.work_stk1.length := by
                                    rw [hwsC_len, bv_c0_zext32_64]; omega
                                  let gv_c := csC.st.scratch.work_stk1[(cc.setWidth 64).toNat]'hc_ws
                                  have hgvc_ws : (s.scratch.work_stk1[cc.toNat]?.getD 0#32).toNat =
                                      gv_c.toNat := by
                                    dsimp only [gv_c]
                                    rw [← csC.ws,
                                      List.getElem?_eq_getElem (by rw [hwsC_len]; omega),
                                      Option.getD_some]
                                    exact congrArg BitVec.toNat
                                      (m4_list_getElem_congr (bv_c0_zext32_64 cc).symm)
                                  have hgvc_lt : gv_c.toNat < s.core.cur_vars := by
                                    rw [← hgvc_ws]; exact hws_lt cc.toNat hc_lt
                                  have hgva_sig : (gv_a.setWidth 64).toNat <
                                      csC.st.scratch.sim_sig.length := by
                                    rw [hsigC_len, bv_c0_zext32_64]; omega
                                  have hgvc_sig : (gv_c.setWidth 64).toNat <
                                      csC.st.scratch.sim_sig.length := by
                                    rw [hsigC_len, bv_c0_zext32_64]; omega
                                  m4_to_group; refine wp_unroll_group fun _ _ => ?_
                                  m4_to_group
                                  refine wp_join_group (ts := [])
                                    (fun () mdo => mdo = mc)
                                    (fun _ () mdo hmdo => by
                                      subst mdo
                                      m4_to_group
                                      refine wp_join_group (ts := [i32])
                                        (fun (pol,
                                          ()) mpol => mpol = mc ∧ (pol = 0#32 ∨ pol = 1#32))
                                        (fun _ (pol, ()) mpol ⟨hmpol, hpol⟩ => by
                                          subst mpol
                                          obtain ⟨ha01, ha11, ha02, ha12, hll1_0, hll1_1, hll2_0,
                                            hll2_1, hgl1_0, hgl1_1, hgl2_0, hgl2_1⟩ :=
                                            m4_bin_lits_align (by unfold k5MaxV at hnv512; omega)
                                              (by unfold k5MaxV at hnv512; omega) (by omega)
                                              (by omega) hgva_ws hgvc_ws hpol
                                          have hp_lt : pol.toNat < 2 := by
                                            rcases hpol with rfl | rfl <;> decide
                                          have hxp_lt : (1#32 ^^^ pol).toNat < 2 := by
                                            rcases hpol with rfl | rfl <;> decide
                                          have hka_v :
                                              2304 + ((5152 +
                                                (a <<< (1 : Nat))).setWidth 64).toNat <
                                                csC.st.scratch.scratch_buf.length := by
                                            rw [hscrC_len, bv_c0_zext32_64]
                                            unfold k5MinScr at hcap; unfold k5MaxV at hnv512
                                            bv_omega
                                          have hkc_v :
                                              2304 + ((5152 +
                                                (cc <<< (1 : Nat))).setWidth 64).toNat <
                                                csC.st.scratch.scratch_buf.length := by
                                            rw [hscrC_len, bv_c0_zext32_64]
                                            unfold k5MinScr at hcap; unfold k5MaxV at hnv512
                                            bv_omega
                                          -- Compute `fa`, `fc`, then try `flip(fa) || flip(fc)`
                                          m4_to_group
                                          refine wp_join_group (ts := [i32])
                                            (fun (fa, ()) mfa => mfa = mc ∧ fa.toNat < 2 * nv.toNat)
                                            (fun _ (fa, ()) mfa ⟨hmfa, hfa_lt⟩ => by
                                              subst mfa
                                              m4_to_group
                                              refine wp_join_group (ts := [i32])
                                                (fun (fc, ()) mfc =>
                                                  mfc = mc ∧ fc.toNat < 2 * nv.toNat)
                                                (fun _ (fc, ()) mfc ⟨hmfc, hfc_lt⟩ => by
                                                  subst mfc
                                                  m4_to_group; refine wp_unroll_group fun _ _ => ?_
                                                  m4_to_group
                                                  refine wp_join_group (ts := [])
                                                    (fun () mFl =>
                                                      M4ClassState c F0 F_cur s nv rbitC R mFl)
                                                    (fun _ () mFl ⟨csFl⟩ => by
                                                      -- Flip succeeded: refine sig if `rbitC < 64`
                                                      m4_to_group
                                                      refine wp_unroll_group fun _ _ => ?_
                                                      m4_split; rotate_left
                                                      · m4_steps
                                                        exact hJifC (rbitC, smaskC, ()) mFl ⟨csFl⟩
                                                      have hrb_lt : rbitC.toNat < 64 := by bv_omega
                                                      have hrb1 : (rbitC + 1#32).toNat =
                                                          rbitC.toNat + 1 := m4_bv32_add1 (by omega)
                                                      m4_call hRef
                                                      refine ⟨c, csFl.st, R, rfl, csFl.inv.1, hcap,
                                                        hnv512, hnv_mx,
                                                        fun j hj => by
                                                          rw [csFl.ws, csFl.cv]; exact hws_lt j hj,
                                                        csFl.mem, fun sigR mR hsigR hmR => ?_⟩
                                                      m4_steps
                                                      exact hJifC (rbitC + 1#32, _, ()) mR
                                                        ⟨⟨by omega, _,
                                                          fullDenseInvW_after_refine csFl.inv hsigR,
                                                          csFl.cv, csFl.fuel, csFl.ws, csFl.tmk,
                                                          csFl.k5, csFl.nv_eq, csFl.pht, hmR⟩⟩)
                                                    (fun _ hJfl => by
                                                      -- Call `full_k512_flip(h, fa)`
                                                      m4_call hFlip
                                                      refine ⟨c, csC.st, P, R, rfl, hlenC, csC.k5,
                                                        by rw [csC.nv_eq]; exact hfa_lt, csC.mem,
                                                        fun okFa scrFa mFa hlenFa hpreFa hKFa hnvFa
                                                          _ _ hmFa => ?_⟩
                                                      let sFa : FullState :=
                                                        { csC.st with scratch :=
                                                          { csC.st.scratch with
                                                            scratch_buf := scrFa } }
                                                      have hinvFa : FullDenseInvW c F0 F_cur sFa :=
                                                        fullDenseInvW_with_fuel_scratch csC.inv
                                                          hlenFa.scratch_ok rfl rfl
                                                      have hnvFa' :
                                                          (k5StateOfScratch scrFa).nv = nv :=
                                                        hnvFa.trans csC.nv_eq
                                                      have hphtFa : PhtOk nv.toNat scrFa :=
                                                        m4_phtOk_congr_512 hnv512 csC.pht
                                                          fun j hj => hpreFa j
                                                            (by
                                                              unfold phtMerged at hj
                                                              unfold k5Base; omega)
                                                      have csFa :
                                                          M4ClassState c F0 F_cur s nv rbitC R mFa
                                                            :=
                                                        ⟨⟨csC.rbit_le, sFa, hinvFa, csC.cv,
                                                          csC.fuel, csC.ws, csC.tmk, hKFa, hnvFa',
                                                          hphtFa, hmFa⟩⟩
                                                      m4_split; · m4_steps; exact hJfl () mFa csFa
                                                      -- Call `full_k512_flip(h, fc)`
                                                      m4_call hFlip
                                                      refine ⟨c, sFa, P, R, rfl, hlenFa, hKFa,
                                                        by rw [hnvFa']; exact hfc_lt, hmFa,
                                                        fun okFc scrFc mFc hlenFc hpreFc hKFc hnvFc
                                                          _ _ hmFc => ?_⟩
                                                      let sFc : FullState :=
                                                        { sFa with scratch :=
                                                          { sFa.scratch with
                                                            scratch_buf := scrFc } }
                                                      have hscrFc_len :=
                                                        hlenFc.scratch_ok.scratch_buf_len
                                                      have hinvFc : FullDenseInvW c F0 F_cur sFc :=
                                                        fullDenseInvW_with_fuel_scratch hinvFa
                                                          hlenFc.scratch_ok rfl rfl
                                                      have hnvFc' :
                                                          (k5StateOfScratch scrFc).nv = nv :=
                                                        hnvFc.trans hnvFa'
                                                      have hphtFc : PhtOk nv.toNat scrFc :=
                                                        m4_phtOk_congr_512 hnv512 hphtFa
                                                          fun j hj => hpreFc j
                                                            (by
                                                              unfold phtMerged at hj
                                                              unfold k5Base; omega)
                                                      have csFc :
                                                          M4ClassState c F0 F_cur s nv rbitC R mFc
                                                            :=
                                                        ⟨⟨csC.rbit_le, sFc, hinvFc, csC.cv,
                                                          csC.fuel, csC.ws, csC.tmk, hKFc, hnvFc',
                                                          hphtFc, hmFc⟩⟩
                                                      m4_split; · m4_steps; exact hJfl () mFc csFc
                                                      -- Both flips failed: solve `d1`
                                                      have hk11Fc :
                                                          2304 + (BitVec.ofNat 64 11).toNat <
                                                          scrFc.length := by
                                                        rw [hscrFc_len]; unfold k5MinScr at hcap
                                                        simp; omega
                                                      have hk15 :
                                                          2304 + (BitVec.ofNat 64 15).toNat <
                                                          scrFc.length := by
                                                        rw [hscrFc_len]; unfold k5MinScr at hcap
                                                        simp; omega
                                                      have hk4640 :
                                                          2304 + (BitVec.ofNat 64 4640).toNat <
                                                            scrFc.length := by
                                                        rw [hscrFc_len]; unfold k5MinScr at hcap
                                                        simp; omega
                                                      have hk4641 :
                                                          2304 + (BitVec.ofNat 64 4641).toNat <
                                                            scrFc.length := by
                                                        rw [hscrFc_len]; unfold k5MinScr at hcap
                                                        simp; omega
                                                      have h15_eq :
                                                          2304 + (BitVec.ofNat 64 15).toNat =
                                                          k5Base + 15 := by decide
                                                      have h4640_eq :
                                                          2304 + (BitVec.ofNat 64 4640).toNat =
                                                            k5Base + 4640 := by decide
                                                      have h4641_eq :
                                                          2304 + (BitVec.ofNat 64 4641).toNat =
                                                            k5Base + 4641 := by decide
                                                      let a0_1 := a <<< (1 : Nat)
                                                      let a1_1 :=
                                                        (cc <<< (1 : Nat)) ||| (1#32 ^^^ pol)
                                                      obtain ⟨hK1, hnv1_s, hass1⟩ :=
                                                        k5ScratchInv_set_assump2
                                                          (a0 := a0_1) (a1 := a1_1)
                                                          (by rw [hnvFc', ha01]; omega)
                                                          (by rw [hnvFc', ha11]; omega) hKFc
                                                      m4_steps
                                                      let scr1 :=
                                                        ((scrFc.set (k5Base + 15) 2#32).set
                                                        (k5Base + 4640) a0_1).set
                                                        (k5Base + 4641) a1_1
                                                      let s1 : FullState :=
                                                        { sFc with scratch :=
                                                          { sFc.scratch with scratch_buf := scr1 } }
                                                      have hlen1 : s1.LengthsOk c :=
                                                        ⟨hlenFc.core_ok, { hlenFc.scratch_ok with
                                                          scratch_buf_len :=
                                                            List.length_set.trans
                                                              (List.length_set.trans
                                                                (List.length_set.trans
                                                                  hscrFc_len)) }⟩
                                                      have hpht1 : PhtOk nv.toNat scr1 :=
                                                        m4_phtOk_congr_512 hnv512 hphtFc
                                                          fun j hj => by
                                                            dsimp only [scr1]
                                                            unfold phtMerged at hj; unfold k5Base
                                                            rw [List.getElem?_set_ne (by omega),
                                                              List.getElem?_set_ne (by omega),
                                                              List.getElem?_set_ne (by omega)]
                                                      m4_call hSolve
                                                      refine ⟨c, s1, P, R, rfl, hlen1, hK1,
                                                        by simpa only [s1, scr1, a0_1, a1_1, h15_eq,
                                                          h4640_eq, h4641_eq] using
                                                          ‹(FullMem c _ ⋆ R) _›,
                                                        fun d1 fuel1 scrS1 mS1 hlenS1 hfuel1 hpreS1
                                                          hKS1 hnvS1 _ hassS1 _ hunsS1 hmS1 => ?_⟩
                                                      let sS1 : FullState :=
                                                        { s1 with
                                                          core := { s1.core with fuel := fuel1 }
                                                          scratch :=
                                                            { s1.scratch with scratch_buf :=
                                                              scrS1 } }
                                                      have hscrS1_len :=
                                                        hlenS1.scratch_ok.scratch_buf_len
                                                      have hinvS1 : FullDenseInvW c F0 F_cur sS1 :=
                                                        fullDenseInvW_with_fuel_scratch hinvFc
                                                          hlenS1.scratch_ok rfl rfl
                                                      have hfuel1_0 :
                                                          fuel1.toNat ≤ s.core.fuel.toNat :=
                                                        Nat.le_trans hfuel1 csC.fuel
                                                      have hnvS1' :
                                                          (k5StateOfScratch scrS1).nv = nv :=
                                                        hnvS1.trans (hnv1_s.trans hnvFc')
                                                      have hphtS1 : PhtOk nv.toNat scrS1 :=
                                                        m4_phtOk_congr_512 hnv512 hpht1
                                                          fun j hj => hpreS1 j
                                                            (by
                                                              unfold phtMerged at hj
                                                              unfold k5Base; omega)
                                                      have csS1 :
                                                          M4ClassState c F0 F_cur s nv rbitC R mS1
                                                            :=
                                                        ⟨⟨csC.rbit_le, sS1, hinvS1, csC.cv,
                                                          hfuel1_0, csC.ws, csC.tmk, hKS1, hnvS1',
                                                          hphtS1, hmS1⟩⟩
                                                      m4_to_group
                                                      refine wp_unroll_group fun _ _ => ?_
                                                      m4_to_group
                                                      refine wp_join_group (ts := [])
                                                        (fun () m_e1 => m_e1 = mS1)
                                                        (fun _ () m_e1 hm_e1 => by
                                                          subst m_e1
                                                          m4_to_group
                                                          refine wp_unroll_group fun _ _ => ?_
                                                          have hk11_S1 :
                                                              2304 + (BitVec.ofNat 64 11).toNat <
                                                                scrS1.length := by
                                                            rw [hscrS1_len]; unfold k5MinScr at hcap
                                                            simp; omega
                                                          m4_split; rotate_left
                                                          · m4_steps
                                                            exact hJifC (rbitC, smaskC, ()) mS1 csS1
                                                          m4_split; rotate_left
                                                          · m4_steps
                                                            exact hJifC (rbitC, smaskC, ()) mS1 csS1
                                                          -- `d1 == 20 && ticks < tick_lim`: 2nd
                                                          -- solve
                                                          have hd1_20 : d1 = 20#64 := by bv_omega
                                                          have huns1 : ∀ β, P β →
                                                              ¬ (unitsCnf [a0_1.toNat,
                                                                a1_1.toNat]).Sat β := by
                                                            intro β hβ; have := hunsS1 hd1_20 β hβ
                                                            rwa [hassS1, hass1] at this
                                                          obtain ⟨hsem1, hent1⟩ :=
                                                            coneModelSet_unsat_bin
                                                              (by dsimp only [a0_1]; omega)
                                                              (by dsimp only [a1_1]; omega) huns1
                                                          let a0_2 := (a <<< (1 : Nat)) ||| 1#32
                                                          let a1_2 := (cc <<< (1 : Nat)) ||| pol
                                                          have hk15_2 :
                                                              2304 + (BitVec.ofNat 64 15).toNat <
                                                                scrS1.length := by
                                                            rw [hscrS1_len]; unfold k5MinScr at hcap
                                                            simp; omega
                                                          have hk4640_2 :
                                                              2304 + (BitVec.ofNat 64 4640).toNat <
                                                                scrS1.length := by
                                                            rw [hscrS1_len]; unfold k5MinScr at hcap
                                                            simp; omega
                                                          have hk4641_2 :
                                                              2304 + (BitVec.ofNat 64 4641).toNat <
                                                                scrS1.length := by
                                                            rw [hscrS1_len]; unfold k5MinScr at hcap
                                                            simp; omega
                                                          obtain ⟨hK2, hnv2_s, hass2⟩ :=
                                                            k5ScratchInv_set_assump2
                                                              (a0 := a0_2) (a1 := a1_2)
                                                              (by rw [hnvS1', ha02]; omega)
                                                              (by rw [hnvS1', ha12]; omega) hKS1
                                                          m4_steps
                                                          let scr2 := ((scrS1.set (k5Base + 15)
                                                            2#32).set (k5Base + 4640) a0_2).set
                                                            (k5Base + 4641) a1_2
                                                          let s2 : FullState :=
                                                            { sS1 with scratch :=
                                                              { sS1.scratch with
                                                                scratch_buf := scr2 } }
                                                          have hlen2 : s2.LengthsOk c :=
                                                            ⟨hlenS1.core_ok,
                                                              { hlenS1.scratch_ok with
                                                              scratch_buf_len :=
                                                                List.length_set.trans
                                                                  (List.length_set.trans
                                                                    (List.length_set.trans
                                                                      hscrS1_len)) }⟩
                                                          have hpht2 : PhtOk nv.toNat scr2 :=
                                                            m4_phtOk_congr_512 hnv512 hphtS1
                                                              fun j hj => by
                                                                dsimp only [scr2]
                                                                unfold phtMerged at hj
                                                                unfold k5Base
                                                                rw [List.getElem?_set_ne (by omega),
                                                                  List.getElem?_set_ne (by omega),
                                                                  List.getElem?_set_ne (by omega)]
                                                          m4_call hSolve
                                                          refine ⟨c, s2, P, R, rfl, hlen2, hK2,
                                                            by simpa only [s2, scr2, a0_2, a1_2,
                                                              h15_eq, h4640_eq, h4641_eq] using
                                                              ‹(FullMem c _ ⋆ R) _›,
                                                            fun d2 fuel2 scrS2 mS2 hlenS2 hfuel2
                                                              hpreS2 hKS2 hnvS2 _ hassS2 _ hunsS2
                                                              hmS2 => ?_⟩
                                                          let sS2 : FullState :=
                                                            { s2 with
                                                              core := { s2.core with fuel := fuel2 }
                                                              scratch :=
                                                                { s2.scratch with
                                                                  scratch_buf := scrS2 } }
                                                          have hscrS2_len :=
                                                            hlenS2.scratch_ok.scratch_buf_len
                                                          have hinvS2 :
                                                              FullDenseInvW c F0 F_cur sS2 :=
                                                            fullDenseInvW_with_fuel_scratch hinvS1
                                                              hlenS2.scratch_ok rfl rfl
                                                          have hfuel2_0 :
                                                              fuel2.toNat ≤ s.core.fuel.toNat :=
                                                            Nat.le_trans hfuel2 hfuel1_0
                                                          have hnvS2' :
                                                              (k5StateOfScratch scrS2).nv = nv :=
                                                            hnvS2.trans (hnv2_s.trans hnvS1')
                                                          have hphtS2 : PhtOk nv.toNat scrS2 :=
                                                            m4_phtOk_congr_512 hnv512 hpht2
                                                              fun j hj => hpreS2 j
                                                                (by
                                                                  unfold phtMerged at hj
                                                                  unfold k5Base; omega)
                                                          have csS2 :
                                                              M4ClassState c F0 F_cur s nv rbitC R
                                                                mS2 :=
                                                            ⟨⟨csC.rbit_le, sS2, hinvS2, csC.cv,
                                                              hfuel2_0, csC.ws, csC.tmk, hKS2,
                                                              hnvS2', hphtS2, hmS2⟩⟩
                                                          m4_to_group
                                                          refine wp_unroll_group fun _ _ => ?_
                                                          m4_to_group
                                                          refine wp_join_group (ts := [])
                                                            (fun () m_e2 => m_e2 = mS2)
                                                            (fun _ () m_e2 hm_e2 => by
                                                              subst m_e2
                                                              m4_to_group
                                                              refine wp_unroll_group fun _ _ => ?_
                                                              m4_split; rotate_left
                                                              · m4_steps
                                                                exact hJifC (rbitC, smaskC, ())
                                                                  mS2 csS2
                                                              -- `d2 == 20`: equivalence proved
                                                              have hd2_20 : d2 = 20#64 := by
                                                                bv_omega
                                                              have huns2 : ∀ β, P β →
                                                                  ¬ (unitsCnf [a0_2.toNat,
                                                                    a1_2.toNat]).Sat β := by
                                                                intro β hβ
                                                                have := hunsS2 hd2_20 β hβ
                                                                rwa [hassS2, hass2] at this
                                                              obtain ⟨hsem2, hent2⟩ :=
                                                                coneModelSet_unsat_bin
                                                                  (by dsimp only [a0_2]; omega)
                                                                  (by dsimp only [a1_2]; omega)
                                                                  huns2
                                                              let la := gv_a <<< (1 : Nat)
                                                              let lc := (gv_c <<< (1 : Nat)) ||| pol
                                                              m4_steps
                                                              m4_call hAddB
                                                              refine ⟨c, F0, F_cur, sS2, R, rfl,
                                                                hlenS2, hinvS2.2.1,
                                                                hinvS2.2.2.2.2.2.1,
                                                                fun _ _ => by
                                                                  dsimp only [Arg.val]
                                                                  change (cnfOfClauses
                                                                    F_cur).EntailsClause
                                                                    (cnfClause [(la ^^^ 1#32).toNat,
                                                                      lc.toNat])
                                                                  rw [hgl1_0, hgl1_1]; exact hent1,
                                                                hmS2, ?_⟩
                                                              intro rb1 v1 f1 l1 rs1 tr1 tp1 te1 ua1
                                                                uf1 wv1 ws1 wl1 wu1 nb1 oo1 in1 ph1
                                                                wso1 mB1 _ hlenB1 hwB1 _ hrb1_uns _
                                                                hmB1
                                                              obtain ⟨sB1, hsB1⟩ :
                                                                  ∃ sB1 : FullState, sB1 =
                                                                { sS2 with
                                                                  core := { sS2.core with
                                                                    vals := v1, flags := f1,
                                                                    lvl := l1, rsns := rs1,
                                                                    trl := tr1, trail_pos := tp1,
                                                                    trail_end := te1,
                                                                    unassigned := ua1,
                                                                    unflushed := uf1, wvec := wv1,
                                                                    wstk := ws1, wlen := wl1,
                                                                    wusable := wu1,
                                                                    num_binary := nb1, oom := oo1,
                                                                    inconsistent := in1 }
                                                                  scratch := { sS2.scratch with
                                                                    phases := ph1,
                                                                    wsort := wso1 } } := ⟨_, rfl⟩
                                                              have hinvB1 :=
                                                                fullDenseInvW_after_addBin hinvS2
                                                                  sB1 hsB1 (hsB1 ▸ hlenB1)
                                                                  (hsB1 ▸ hwB1)
                                                              have hmB1' :
                                                                  (FullMem c sB1 ⋆ R) mB1 :=
                                                                hsB1 ▸ hmB1
                                                              m4_split
                                                              · have hrb20 : rb1 = 20#64 := by
                                                                  bv_omega
                                                                m4_steps
                                                                exact hQ 20#64 sB1 mB1 hinvB1
                                                                  (by rw [hsB1]; exact csC.cv)
                                                                  (by rw [hsB1]; exact hfuel2_0)
                                                                  (by rw [hsB1]; exact csC.ws)
                                                                  (by rw [hsB1]; exact csC.tmk)
                                                                  (Or.inr rfl)
                                                                  (fun _ =>
                                                                    (hrb1_uns hrb20).1) hmB1'
                                                              m4_steps
                                                              m4_call hAddB
                                                              refine ⟨c, F0, F_cur, sB1, R, rfl,
                                                                hinvB1.1, hinvB1.2.1,
                                                                hinvB1.2.2.2.2.2.1,
                                                                fun _ _ => by
                                                                  dsimp only [Arg.val]
                                                                  change (cnfOfClauses
                                                                    F_cur).EntailsClause
                                                                    (cnfClause [la.toNat,
                                                                      (lc ^^^ 1#32).toNat])
                                                                  rw [hgl2_0, hgl2_1]; exact hent2,
                                                                hmB1', ?_⟩
                                                              intro rb2 v2 f2 l2 rs2 tr2 tp2 te2 ua2
                                                                uf2 wv2 ws2 wl2 wu2 nb2 oo2 in2 ph2
                                                                wso2 mB2 _ hlenB2 hwB2 _ hrb2_uns _
                                                                hmB2
                                                              obtain ⟨sB2, hsB2⟩ :
                                                                  ∃ sB2 : FullState, sB2 =
                                                                { sB1 with
                                                                  core := { sB1.core with
                                                                    vals := v2, flags := f2,
                                                                    lvl := l2, rsns := rs2,
                                                                    trl := tr2, trail_pos := tp2,
                                                                    trail_end := te2,
                                                                    unassigned := ua2,
                                                                    unflushed := uf2, wvec := wv2,
                                                                    wstk := ws2, wlen := wl2,
                                                                    wusable := wu2,
                                                                    num_binary := nb2, oom := oo2,
                                                                    inconsistent := in2 }
                                                                  scratch := { sB1.scratch with
                                                                    phases := ph2,
                                                                    wsort := wso2 } } := ⟨_, rfl⟩
                                                              have hinvB2 :=
                                                                fullDenseInvW_after_addBin hinvB1
                                                                  sB2 hsB2 (hsB2 ▸ hlenB2)
                                                                  (hsB2 ▸ hwB2)
                                                              have hcvB2 :
                                                                  sB2.core.cur_vars =
                                                                    s.core.cur_vars := by
                                                                rw [hsB2, hsB1]; exact csC.cv
                                                              have hfuelB2 :
                                                                  sB2.core.fuel.toNat ≤
                                                                    s.core.fuel.toNat := by
                                                                rw [hsB2, hsB1]; exact hfuel2_0
                                                              have hwsB2 :
                                                                  sB2.scratch.work_stk1 =
                                                                    s.scratch.work_stk1 := by
                                                                rw [hsB2, hsB1]; exact csC.ws
                                                              have htmkB2 :
                                                                  sB2.scratch.tarjan_mark =
                                                                    s.scratch.tarjan_mark := by
                                                                rw [hsB2, hsB1]; exact csC.tmk
                                                              have hscrB2 :
                                                                  sB2.scratch.scratch_buf = scrS2 :=
                                                                    by
                                                                rw [hsB2, hsB1]
                                                              have hmB2' :
                                                                  (FullMem c sB2 ⋆ R) mB2 :=
                                                                hsB2 ▸ hmB2
                                                              m4_split
                                                              · have hrb20 : rb2 = 20#64 := by
                                                                  bv_omega
                                                                m4_steps
                                                                exact hQ 20#64 sB2 mB2 hinvB2 hcvB2
                                                                  hfuelB2 hwsB2 htmkB2 (Or.inr rfl)
                                                                  (fun _ =>
                                                                    (hrb2_uns hrb20).1) hmB2'
                                                              -- Mark merged & clear `FL_SWEEP`
                                                              have hmgB2_bd :
                                                                  ((1792 + cc).setWidth 64).toNat <
                                                                    sB2.scratch.scratch_buf.length
                                                                      := by
                                                                rw [hscrB2, hscrS2_len, hc_mg_eq]
                                                                unfold k5MinScr at hcap
                                                                unfold k5MaxV at hnv512; omega
                                                              have hmgB2_lt :
                                                                  ((1792 + cc).setWidth 64).toNat <
                                                                    k5Base := by
                                                                rw [hc_mg_eq]; unfold k5Base
                                                                unfold k5MaxV at hnv512; omega
                                                              have hflB2_len :=
                                                                hinvB2.1.core_ok.flags_len
                                                              have hgvc_fl :
                                                                  (gv_c.setWidth 64).toNat <
                                                                    sB2.core.flags.length := by
                                                                rw [hflB2_len, bv_c0_zext32_64]
                                                                omega
                                                              m4_steps
                                                              let scrM :=
                                                                sB2.scratch.scratch_buf.set
                                                                  ((1792 + cc).setWidth 64).toNat
                                                                  1#32
                                                              let flM :=
                                                                sB2.core.flags.set
                                                                  (gv_c.setWidth 64).toNat
                                                                  ((sB2.core.flags[
                                                                    (gv_c.setWidth
                                                                      64).toNat]'hgvc_fl)
                                                                    &&& ~~~1024#32)
                                                              let sM0 : FullState :=
                                                                { sB2 with scratch :=
                                                                  { sB2.scratch with
                                                                    scratch_buf := scrM } }
                                                              let sM : FullState :=
                                                                { sM0 with core :=
                                                                  { sM0.core with flags := flM } }
                                                              have hlenM0 : sM0.LengthsOk c :=
                                                                ⟨hinvB2.1.core_ok,
                                                                 { hinvB2.1.scratch_ok with
                                                                   scratch_buf_len :=
                                                                     List.length_set.trans
                                                                       (hscrB2 ▸ hscrS2_len) }⟩
                                                              have hinvM0 :
                                                                  FullDenseInvW c F0 F_cur sM0 :=
                                                                fullDenseInvW_with_fuel_scratch
                                                                  hinvB2 hlenM0.scratch_ok rfl rfl
                                                              have hinvM :
                                                                  FullDenseInvW c F0 F_cur sM :=
                                                                m4_fullDenseInvW_with_flags hinvM0
                                                                  (List.length_set.trans hflB2_len)
                                                              have hlenM : sM.LengthsOk c := hinvM.1
                                                              have hKM := k5ScratchInv_set_lt 1#32
                                                                hmgB2_lt (hscrB2.symm ▸ hKS2)
                                                              have hnvM :
                                                                  (k5StateOfScratch scrM).nv = nv :=
                                                                    by
                                                                rw [k5StateOfScratch_set_lt 1#32
                                                                  hmgB2_lt, hscrB2, hnvS2']
                                                              have hphtM : PhtOk nv.toNat scrM :=
                                                                m4_phtOk_congr_512 hnv512
                                                                  (hscrB2.symm ▸ hphtS2)
                                                                  fun j hj => by
                                                                    dsimp only [scrM]
                                                                    rw [List.getElem?_set_ne (by
                                                                      rw [hc_mg_eq]
                                                                      unfold phtMerged at hj
                                                                      omega)]
                                                              m4_call hLive
                                                              refine ⟨c, sM, P, R, rfl, hlenM, hKM,
                                                                by dsimp only [Arg.val]
                                                                   change ((a <<< (1 : Nat)) ^^^
                                                                     1#32).toNat <
                                                                     2 * (k5StateOfScratch
                                                                       scrM).nv.toNat
                                                                   rw [hnvM, hll1_0]
                                                                   exact (k5_bv32_xor1_lt
                                                                     (by dsimp only [a0_1]
                                                                         omega :
                                                                       a0_1.toNat <
                                                                         2 * nv.toNat)).2,
                                                                fun h => by
                                                                  dsimp only [Arg.val] at h
                                                                  have := congrArg BitVec.toNat h
                                                                  change ((cc <<< (1 : Nat)) |||
                                                                    pol).toNat =
                                                                    (0xFFFFFFFF#32).toNat at this
                                                                  rw [ha12] at this
                                                                  unfold k5MaxV at hnv512
                                                                  simp at this; omega,
                                                                fun _ => ⟨by
                                                                  dsimp only [Arg.val]
                                                                  change ((cc <<< (1 : Nat)) |||
                                                                    pol).toNat <
                                                                    2 * (k5StateOfScratch
                                                                      scrM).nv.toNat
                                                                  rw [hnvM, ha12]; omega,
                                                                  by dsimp only [Arg.val]
                                                                     change SemEntails P
                                                                       [((a <<< (1 : Nat)) ^^^
                                                                         1#32).toNat,
                                                                        ((cc <<< (1 : Nat)) |||
                                                                         pol).toNat]
                                                                     rw [hll1_0, hll1_1]
                                                                     exact hsem1⟩,
                                                                by assumption,
                                                                fun scrL1 mL1 hlenL1 hpreL1 hKL1 _
                                                                  hnvL1 _ _ hmL1 => ?_⟩
                                                              let sL1 : FullState :=
                                                                { sM with scratch :=
                                                                  { sM.scratch with
                                                                    scratch_buf := scrL1 } }
                                                              have hinvL1 :
                                                                  FullDenseInvW c F0 F_cur sL1 :=
                                                                fullDenseInvW_with_fuel_scratch
                                                                  hinvM hlenL1.scratch_ok rfl rfl
                                                              have hnvL1' :
                                                                  (k5StateOfScratch scrL1).nv =
                                                                    nv :=
                                                                hnvL1.trans hnvM
                                                              have hphtL1 : PhtOk nv.toNat scrL1 :=
                                                                m4_phtOk_congr_512 hnv512 hphtM
                                                                  fun j hj => hpreL1 j
                                                                    (by
                                                                      unfold phtMerged at hj
                                                                      unfold k5Base; omega)
                                                              m4_steps
                                                              m4_call hLive
                                                              refine ⟨c, sL1, P, R, rfl, hlenL1,
                                                                hKL1,
                                                                by dsimp only [Arg.val]
                                                                   change (a <<< (1 : Nat)).toNat <
                                                                     2 * (k5StateOfScratch
                                                                       scrL1).nv.toNat
                                                                   rw [hnvL1', ha01]; omega,
                                                                fun h => by
                                                                  dsimp only [Arg.val] at h
                                                                  have := congrArg BitVec.toNat h
                                                                  change (((cc <<< (1 : Nat)) |||
                                                                    pol) ^^^ 1#32).toNat =
                                                                    (0xFFFFFFFF#32).toNat at this
                                                                  have hlt := (k5_bv32_xor1_lt
                                                                    (by dsimp only [a1_2]
                                                                        omega :
                                                                      a1_2.toNat <
                                                                        2 * nv.toNat)).2
                                                                  rw [show (a1_2 ^^^ 1#32).toNat =
                                                                      (0xFFFFFFFF#32).toNat from
                                                                    this] at hlt
                                                                  unfold k5MaxV at hnv512
                                                                  simp at hlt; omega,
                                                                fun _ => ⟨by
                                                                  dsimp only [Arg.val]
                                                                  change (((cc <<< (1 : Nat)) |||
                                                                    pol) ^^^ 1#32).toNat <
                                                                    2 * (k5StateOfScratch
                                                                      scrL1).nv.toNat
                                                                  rw [hnvL1', hll2_1]
                                                                  exact (k5_bv32_xor1_lt
                                                                    (by dsimp only [a1_2]
                                                                        omega :
                                                                      a1_2.toNat <
                                                                        2 * nv.toNat)).2,
                                                                  by dsimp only [Arg.val]
                                                                     change SemEntails P
                                                                       [(a <<< (1 : Nat)).toNat,
                                                                        (((cc <<< (1 : Nat)) |||
                                                                         pol) ^^^ 1#32).toNat]
                                                                     rw [hll2_0, hll2_1]
                                                                     exact hsem2⟩,
                                                                hmL1,
                                                                fun scrL2 mL2 hlenL2 hpreL2 hKL2 _
                                                                  hnvL2 _ _ hmL2 => ?_⟩
                                                              let sL2 : FullState :=
                                                                { sL1 with scratch :=
                                                                  { sL1.scratch with
                                                                    scratch_buf := scrL2 } }
                                                              have hinvL2 :
                                                                  FullDenseInvW c F0 F_cur sL2 :=
                                                                fullDenseInvW_with_fuel_scratch
                                                                  hinvL1 hlenL2.scratch_ok rfl rfl
                                                              have hnvL2' :
                                                                  (k5StateOfScratch scrL2).nv =
                                                                    nv :=
                                                                hnvL2.trans hnvL1'
                                                              have hphtL2 : PhtOk nv.toNat scrL2 :=
                                                                m4_phtOk_congr_512 hnv512 hphtL1
                                                                  fun j hj => hpreL2 j
                                                                    (by
                                                                      unfold phtMerged at hj
                                                                      unfold k5Base; omega)
                                                              m4_call hRearm
                                                              refine ⟨c, F0, F_cur, sL2, R, rfl,
                                                                hinvL2, hmL2,
                                                                fun fl1 mR1 _ hinvR1 hmR1 => ?_⟩
                                                              let sR1 : FullState :=
                                                                { sL2 with core :=
                                                                  { sL2.core with flags := fl1 } }
                                                              m4_call hRearm
                                                              refine ⟨c, F0, F_cur, sR1, R, rfl,
                                                                hinvR1, hmR1,
                                                                fun fl2 mR2 _ hinvR2 hmR2 => ?_⟩
                                                              let sR2 : FullState :=
                                                                { sR1 with core :=
                                                                  { sR1.core with flags := fl2 } }
                                                              m4_steps
                                                              let sFin : FullState :=
                                                                { sR2 with scratch :=
                                                                  { sR2.scratch with
                                                                    sweep_cnt :=
                                                                      sR2.scratch.sweep_cnt +
                                                                        1#64 } }
                                                              exact hJifC (rbitC, smaskC, ()) _
                                                                ⟨⟨csC.rbit_le, sFin,
                                                                  fullDenseInvW_with_sweep_cnt
                                                                    hinvR2
                                                                    (sR2.scratch.sweep_cnt + 1#64),
                                                                  hcvB2, hfuelB2, hwsB2, htmkB2,
                                                                  hKL2, hnvL2', hphtL2,
                                                                  by assumption⟩⟩)
                                                            (fun _ hJe2 => by
                                                              m4_split; rotate_left
                                                              · m4_steps; exact hJe2 () mS2 rfl
                                                              m4_split; rotate_left
                                                              · m4_steps; exact hJe2 () mS2 rfl
                                                              have hrb_lt : rbitC.toNat < 64 := by
                                                                bv_omega
                                                              have hrb1 : (rbitC + 1#32).toNat =
                                                                  rbitC.toNat + 1 :=
                                                                m4_bv32_add1 (by omega)
                                                              m4_call hRef
                                                              refine ⟨c, sS2, R, rfl, hlenS2, hcap,
                                                                hnv512, hnv_mx,
                                                                fun j hj => by
                                                                  rw [csC.ws, csC.cv]
                                                                  exact hws_lt j hj,
                                                                hmS2,
                                                                fun sigR mR hsigR hmR => ?_⟩
                                                              m4_steps
                                                              exact hJifC (rbitC + 1#32, _, ()) mR
                                                                ⟨⟨by omega, _,
                                                                  fullDenseInvW_after_refine hinvS2
                                                                    hsigR,
                                                                  csC.cv, hfuel2_0, csC.ws,
                                                                  csC.tmk, hKS2, hnvS2', hphtS2,
                                                                  hmR⟩⟩))
                                                        (fun _ hJe1 => by
                                                          m4_split; rotate_left
                                                          · m4_steps; exact hJe1 () mS1 rfl
                                                          m4_split; rotate_left
                                                          · m4_steps; exact hJe1 () mS1 rfl
                                                          have hrb_lt : rbitC.toNat < 64 := by
                                                            bv_omega
                                                          have hrb1 : (rbitC + 1#32).toNat =
                                                              rbitC.toNat + 1 :=
                                                            m4_bv32_add1 (by omega)
                                                          m4_call hRef
                                                          refine ⟨c, sS1, R, rfl, hlenS1, hcap,
                                                            hnv512, hnv_mx,
                                                            fun j hj => by
                                                              rw [csC.ws, csC.cv]
                                                              exact hws_lt j hj,
                                                            hmS1, fun sigR mR hsigR hmR => ?_⟩
                                                          m4_steps
                                                          exact hJifC (rbitC + 1#32, _, ()) mR
                                                            ⟨⟨by omega, _,
                                                              fullDenseInvW_after_refine hinvS1
                                                                hsigR,
                                                              csC.cv, hfuel1_0, csC.ws, csC.tmk,
                                                              hKS1, hnvS1', hphtS1, hmR⟩⟩)))
                                                (fun _ hJfc => by
                                                  m4_split
                                                  · m4_steps; exact hJfc (cc <<< (1 : Nat), ()) mc
                                                      ⟨rfl, by unfold k5MaxV at hnv512; bv_omega⟩
                                                  · m4_steps
                                                    have hcc1 :
                                                        ((cc <<< (1 : Nat)) ||| 1#32).toNat =
                                                          2 * cc.toNat + 1 :=
                                                      FullSweepVarHelpers.bv32_shl1_or_pol cc 1#32
                                                        (by unfold k5MaxV at hnv512; omega)
                                                        (by decide)
                                                    exact hJfc ((cc <<< (1 : Nat)) ||| 1#32, ()) mc
                                                      ⟨rfl, by omega⟩))
                                            (fun _ hJfa => by
                                              m4_split
                                              · m4_steps; exact hJfa (a <<< (1 : Nat), ()) mc
                                                  ⟨rfl, by unfold k5MaxV at hnv512; bv_omega⟩
                                              · m4_steps
                                                have ha1 :
                                                    ((a <<< (1 : Nat)) ||| 1#32).toNat =
                                                      2 * a.toNat + 1 :=
                                                  FullSweepVarHelpers.bv32_shl1_or_pol a 1#32
                                                    (by unfold k5MaxV at hnv512; omega)
                                                    (by decide)
                                                exact hJfa ((a <<< (1 : Nat)) ||| 1#32, ()) mc
                                                  ⟨rfl, by omega⟩))
                                        (fun _ hJpol => by
                                          m4_split
                                          · m4_steps; exact hJpol (0#32, ()) mc ⟨rfl, Or.inl rfl⟩
                                          · m4_steps; exact hJpol (1#32, ()) mc ⟨rfl, Or.inr rfl⟩))
                                    (fun _ hJdo => by
                                      m4_split; · m4_steps; exact hJdo () mc rfl
                                      m4_split; · m4_steps; exact hJdo () mc rfl
                                      m4_steps; exact hJifC (rbitC, smaskC, ()) mc ⟨csC⟩)))))))))
    (fun _ hJsm => by
      m4_split
      · m4_steps; exact hJsm _ m rfl
      · m4_steps; exact hJsm _ m rfl)

/-! ## 4. `full_m4_sweep_var_wp` (`22/24`) -/

private theorem m4_sweep_tmk_clear_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {sX : FullState}
    {R : Mem 64 → Prop} {nv : BitVec 32} {ws1' tmk' : List (BitVec 32)}
    {pWorkStk1 pTarjanMark : BitVec 64} {mX : Mem 64} {cont : Expr Val Cont rs}
    (hpws : pWorkStk1 = c.pWorkStk1) (hptmk : pTarjanMark = c.pTarjanMark)
    (hnv_mx : nv.toNat ≤ 2 * c.max_vars) (hinvX : FullDenseInvW c F0 F_cur sX)
    (hwsX : sX.scratch.work_stk1 = ws1') (htmkX : sX.scratch.tarjan_mark = tmk')
    (hconeX : ∀ i < nv.toNat, (sX.scratch.work_stk1[i]?.getD 0#32).toNat < sX.core.cur_vars)
    (htmk1' : ∀ u < sX.core.cur_vars, tmk'[u]?.getD 0#32 ≠ 0#32 →
      ∃ k < nv.toNat, (ws1'[k]?.getD 0#32).toNat = u)
    (hmX : (FullMem c sX ⋆ R) mX)
    (hcont : ∀ (tmk_c : List (BitVec 32)) m_end,
      tmk_c.length = 2 * c.max_vars →
      M4TmkZero { sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } →
      (FullMem c { sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } ⋆ R) m_end →
      wp Γ Q X cont m_end) :
    wp Γ Q X
      (Expr.group (sig := [[i32]])
        (fun Js =>
          Blocks.cons
            (fun (p : Tup Val [i32]) =>
              Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var p.fst, Arg.var nv, ()))
                fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ()))
                    fun p_2 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_2.fst, Arg.imm 4, ()))
                      fun p_3 =>
                      Expr.let_
                        (Op.mk (OpCode.add i64) (Arg.var pWorkStk1, Arg.var p_3.fst, ()))
                        fun p_4 =>
                        Expr.load i32 (Arg.var p_4.fst) fun ld =>
                          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ()))
                            fun p_5 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ()))
                              fun p_6 =>
                              Expr.let_
                                (Op.mk (OpCode.add i64)
                                  (Arg.var pTarjanMark, Arg.var p_6.fst, ()))
                                fun p_7 =>
                                Expr.store (t := i32) (Arg.imm 0) (Arg.var p_7.fst)
                                  (Expr.let_
                                    (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ()))
                                    fun p => Expr.jump Js.fst (Arg.var p.fst, ())))
                  cont)
            Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))
      mX := by
  subst hpws hptmk
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hws_len := hinvX.1.scratch_ok.work_stk1_len
  have hcvX_le := hinvX.1.core_ok.cur_vars_le
  have htmkX_sym : tmk' = sX.scratch.tarjan_mark := htmkX.symm
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) mi => i.toNat ≤ nv.toNat ∧ ∃ tmk_c : List (BitVec 32),
      tmk_c.length = 2 * c.max_vars ∧
      (∀ u < sX.core.cur_vars, tmk_c[u]?.getD 0#32 ≠ 0#32 →
        ∃ k, i.toNat ≤ k ∧ k < nv.toNat ∧ (ws1'[k]?.getD 0#32).toNat = u) ∧
      (FullMem c { sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } ⋆ R) mi)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun _ hLc => by
      m4_steps
      exact hLc (0#32, ()) mX ⟨Nat.zero_le _, tmk',
        htmkX ▸ hinvX.1.scratch_ok.tarjan_mark_len,
        fun u hu hne => let ⟨k, hk, hwk⟩ := htmk1' u hu hne; ⟨k, Nat.zero_le _, hk, hwk⟩,
        htmkX_sym ▸ hmX⟩)
    (fun _ (i, ()) mi ⟨hi_le, tmk_c, ht_len, ht_inv, hmi⟩ hLc => by
      m4_split
      · have hi_lt : i.toNat < nv.toNat := by bv_omega
        have hv_lt : (ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega)).toNat <
            2 * c.max_vars := by
          have := hconeX i.toNat hi_lt
          rw [hwsX, List.getElem?_eq_getElem (by rw [← hwsX, hws_len]; omega),
            Option.getD_some] at this; omega
        have hi_ws : (BitVec.setWidth 64 i).toNat <
            ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
              FullState).scratch.work_stk1.length := by
          change (BitVec.setWidth 64 i).toNat < sX.scratch.work_stk1.length
          rw [hws_len, bv_c0_zext32_64]; omega
        have hwsX_eq : ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1 = ws1' := hwsX
        have hgv_tmk : (BitVec.setWidth 64 (({ sX with scratch :=
            { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws)).toNat <
            ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
              FullState).scratch.tarjan_mark.length :=
          tmk_idx_lt hwsX_eq (by rw [← hwsX, hws_len]; omega) (by rw [ht_len]; exact hv_lt) hi_ws
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := m4_bv32_add1 (by omega)
        m4_steps
        refine hLc (i + 1#32, ()) _ (by dsimp only; omega)
          ⟨by omega, _, List.length_set.trans ht_len, fun u hu hne => ?_, by assumption⟩
        have h64_i : (BitVec.setWidth 64 i).toNat = i.toNat := bv_c0_zext32_64 i
        have hcur1 : sX.scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws =
            sX.scratch.work_stk1[i.toNat]'(by rw [hws_len]; omega) := Option.some.inj (by
          rw [← List.getElem?_eq_getElem hi_ws,
            ← List.getElem?_eq_getElem (by rw [hws_len]; omega), h64_i])
        have hcur2 : sX.scratch.work_stk1[i.toNat]'(by rw [hws_len]; omega) =
            ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega) := by cases hwsX; rfl
        have hcur_eq : ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws =
            ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega) := hcur1.trans hcur2
        rw [hcur_eq, bv_c0_zext32_64] at hne
        by_cases huv : u = (ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega)).toNat
        · rw [huv] at hne
          rw [List.getElem?_set_self (by rw [ht_len]; exact hv_lt)] at hne
          exact absurd rfl hne
        · rw [List.getElem?_set_ne (Ne.symm huv)] at hne
          obtain ⟨k, hk1, hk2, hwk⟩ := ht_inv u hu hne
          have hkne : k ≠ i.toNat := by
            rintro rfl
            rw [List.getElem?_eq_getElem (by rw [← hwsX, hws_len]; omega), Option.getD_some] at hwk
            exact huv hwk.symm
          exact ⟨k, by omega, hk2, hwk⟩
      · have hge : ¬ i.toNat < nv.toNat := by bv_omega
        refine hcont tmk_c mi ht_len (fun u hu => ?_) hmi
        exact Classical.byContradiction fun hne => by
          obtain ⟨k, hk1, hk2, _⟩ := ht_inv u hu hne; omega)

theorem full_m4_sweep_var_wp (Γ : Env)
    (hCone : M4EnvSpec Γ "full_m4_sweep_cone" m4SweepConeSpec)
    (hSim : M4EnvSpec Γ "full_m4_sweep_sim" m4SweepSimSpec)
    (hUnits : M4EnvSpec Γ "full_m4_sweep_units" m4SweepUnitsSpec)
    (hClasses : M4EnvSpec Γ "full_m4_sweep_classes" m4SweepClassesSpec) :
    ∀ args m Q X, m4SweepVarSpec args m Q X →
      Func.wp Γ full_m4_sweep_var_body args m Q X := by
  rintro ⟨h, root_v, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hcap, hroot, htmk, hm, hQ⟩
  have hcv_le := hinv.1.core_ok.cur_vars_le
  unfold Func.wp full_m4_sweep_var_body
  m4_steps
  m4_call hCone
  refine ⟨c, F0, F_cur, s, R, rfl, hinv, hcap, hroot, htmk, hm,
    fun pk tmp' ws1' tmk' scr' m1 hinv1 hcv1 hfuel1 _ _ hcone1 htmk1 hm1 => ?_⟩
  let s1 : FullState :=
    { s with
      core := { s.core with tmp := tmp' }
      scratch := { s.scratch with work_stk1 := ws1', tarjan_mark := tmk', scratch_buf := scr' } }
  let nv : BitVec 32 := (pk &&& 0xFFFF#64).setWidth 32
  have hnv_eq : nv.toNat = (pk &&& 0xFFFF#64).toNat :=
    bv64_to32_toNat _ (by have := hcone1.2.1; unfold k5MaxV at this; omega)
  have hcone1' : M4SweepConeOk F_cur s1 nv.toNat := by rw [hnv_eq]; exact hcone1
  have hnv_mx : nv.toNat ≤ 2 * c.max_vars := by
    have hcv1' : s1.core.cur_vars = s.core.cur_vars := rfl
    have := hcone1'.2.2.1; omega
  have htmk1' : ∀ u < s.core.cur_vars, tmk'[u]?.getD 0#32 ≠ 0#32 →
      ∃ k < nv.toNat, (ws1'[k]?.getD 0#32).toNat = u := fun u hu hne =>
    let ⟨k, hk, hwk⟩ := htmk1 u hu hne; ⟨k, hnv_eq ▸ hk, hwk⟩
  have hws_ok1 : ∀ i < nv.toNat, (s1.scratch.work_stk1[i]?.getD 0#32).toNat < s1.core.cur_vars :=
    hcone1'.2.2.2.1
  m4_to_group
  -- Early exit: `if (nv < 2u || nc == 0u)`
  refine wp_join_group (ts := [])
    (fun () mJ => mJ = m1)
    (fun _ () mJ hmJ => by
      subst hmJ
      m4_to_group
      refine m4_sweep_tmk_clear_wp rfl rfl hnv_mx hinv1 rfl rfl hws_ok1 htmk1' hm1
        fun tmk_c m_end ht_len ht_done hm_end => by
          m4_steps
          exact hQ 1#64 _ m_end (m4_fullDenseInvW_with_tmk hinv1 ht_len) hcv1
            (hfuel1 ▸ le_refl _) ht_done (Or.inl rfl) (fun h => by cases h) hm_end)
    (fun _ hJearly => by
      m4_split; · m4_steps; exact hJearly () m1 rfl
      m4_split; · m4_steps; exact hJearly () m1 rfl
      -- Simulation: `rbit = full_m4_sweep_sim(h, nv, tick_lim)`
      m4_call hSim
      refine ⟨c, F0, F_cur, s1, R, rfl, hinv1, hcone1', hm1,
        fun rbit fuel2 rng2 sig2 scr2 m2 hinv2 hfuel2 hcone2 huns2 hrb_le2 hm2 => ?_⟩
      let s2 : FullState :=
        { s1 with
          core := { s1.core with fuel := fuel2 }
          scratch := { s1.scratch with rng_state := rng2, sim_sig := sig2, scratch_buf := scr2 } }
      have hfuel2_0 : fuel2.toNat ≤ s.core.fuel.toNat := hfuel1 ▸ hfuel2
      m4_split
      · -- `rbit == 0xFFFFFFFFu`: UNSAT; clear `tmk`, set `inconsistent = 1`, return 20
        have hrb_ff : rbit = 0xFFFFFFFF#32 := by bv_omega
        have huns_cur := huns2 hrb_ff
        have huns_f0 : F0.Unsat := hinv2.2.1.ext_sound.2 huns_cur
        m4_to_group
        refine m4_sweep_tmk_clear_wp rfl rfl hnv_mx hinv2 rfl rfl hcone2.2.2.2.1 htmk1' hm2
          fun tmk_c m_end ht_len ht_done hm_end => by
            m4_steps
            exact hQ 20#64 _ _ (m4_fullDenseInvW_with_inconsistent
              (m4_fullDenseInvW_with_tmk hinv2 ht_len) huns_cur) hcv1 hfuel2_0 ht_done
              (Or.inr rfl) (fun _ => huns_f0) (by assumption)
      have hrb_ne_ff : rbit ≠ 0xFFFFFFFF#32 := by bv_omega
      have hrb_64 : rbit.toNat ≤ 64 := hrb_le2 hrb_ne_ff
      m4_split
      · -- `rbit == 0u`: clear `tmk`, return 1
        m4_to_group
        refine m4_sweep_tmk_clear_wp rfl rfl hnv_mx hinv2 rfl rfl hcone2.2.2.2.1 htmk1' hm2
          fun tmk_c m_end ht_len ht_done hm_end => by
            m4_steps
            exact hQ 1#64 _ m_end (m4_fullDenseInvW_with_tmk hinv2 ht_len) hcv1 hfuel2_0 ht_done
              (Or.inl rfl) (fun h => by cases h) hm_end
      -- Units phase: `ur = full_m4_sweep_units(h, nv, rbit, tick_lim)`
      m4_call hUnits
      refine ⟨c, F0, F_cur, s2, R, rfl, hinv2, hcone2, hrb_64, hm2,
        fun ur s3 m3 hinv3 hcv3 hfuel3 hws3 htmk3 hcone3 huns3 hur_le3 hm3 => ?_⟩
      have hfuel3_0 : s3.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuel3 hfuel2_0
      have hcv3_0 : s3.core.cur_vars = s.core.cur_vars := hcv3.trans hcv1
      m4_split
      · -- `ur == 0xFFFFFFFFFFFFFFFFULL`: UNSAT; clear `tmk`, return 20
        have hur_ff : ur = 0xFFFFFFFFFFFFFFFF#64 := by bv_omega
        m4_to_group
        refine m4_sweep_tmk_clear_wp rfl rfl hnv_mx hinv3 hws3 htmk3 hcone3.2.2.2.1
          (fun u hu => htmk1' u (hcv3_0 ▸ hu)) hm3 fun tmk_c m_end ht_len ht_done hm_end => by
            m4_steps
            exact hQ 20#64 _ m_end (m4_fullDenseInvW_with_tmk hinv3 ht_len) hcv3_0 hfuel3_0
              ht_done (Or.inr rfl) (fun _ => huns3 hur_ff) hm_end
      have hur_ne_ff : ur ≠ 0xFFFFFFFFFFFFFFFF#64 := by bv_omega
      have hur_64 : (ur.setWidth 32).toNat ≤ 64 := by
        have h1 := hur_le3 hur_ne_ff
        rw [bv64_to32_toNat ur (by omega)]; exact h1
      -- Classes phase: `cr = full_m4_sweep_classes(h, nv, (u32)ur, tick_lim)`
      m4_steps
      m4_call hClasses
      refine ⟨c, F0, F_cur, s3, R, rfl, hinv3, hcone3, hur_64, hm3,
        fun cr s4 m4 hinv4 hcv4 hfuel4 hws4 htmk4 hcr_dom hcr_uns hm4 => ?_⟩
      have hfuel4_0 : s4.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuel4 hfuel3_0
      have hcv4_0 : s4.core.cur_vars = s.core.cur_vars := hcv4.trans hcv3_0
      have hws4_0 : s4.scratch.work_stk1 = ws1' := hws4.trans hws3
      have htmk4_0 : s4.scratch.tarjan_mark = tmk' := htmk4.trans htmk3
      have hws_ok4 : ∀ i < nv.toNat, (s4.scratch.work_stk1[i]?.getD 0#32).toNat <
          s4.core.cur_vars := fun i hi => by
        rw [hws4_0, hcv4_0]; exact hws_ok1 i hi
      m4_to_group
      refine m4_sweep_tmk_clear_wp rfl rfl hnv_mx hinv4 hws4_0 htmk4_0 hws_ok4
        (fun u hu => htmk1' u (hcv4_0 ▸ hu)) hm4 fun tmk_c m_end ht_len ht_done hm_end => by
          let sF : FullState := { s4 with scratch := { s4.scratch with tarjan_mark := tmk_c } }
          have hinvF := m4_fullDenseInvW_with_tmk hinv4 ht_len
          m4_to_group; refine wp_unroll_group fun _ _ => ?_
          m4_split
          · have hcr20 : cr = 20#64 := by bv_omega
            m4_steps
            exact hQ 20#64 sF m_end hinvF hcv4_0 hfuel4_0 ht_done (Or.inr rfl)
              (fun _ => hcr_uns hcr20) hm_end
          m4_split
          · have hinc : s4.core.inconsistent ≠ 0#64 := by bv_omega
            have huns_f0 := hinv4.2.1.ext_sound.2 (hinv4.2.1.inconsistent_sound hinc)
            m4_steps
            exact hQ 20#64 sF m_end hinvF hcv4_0 hfuel4_0 ht_done (Or.inr rfl)
              (fun _ => huns_f0) hm_end
          · m4_steps
            exact hQ 1#64 sF m_end hinvF hcv4_0 hfuel4_0 ht_done (Or.inl rfl)
              (fun h => by cases h) hm_end)

/-! ## 5. `full_m4_sweep_dense_wp` (`23/24`) -/

theorem full_m4_sweep_dense_wp (Γ : Env)
    (hVar : M4EnvSpec Γ "full_m4_sweep_var" m4SweepVarSpec) :
    ∀ args m Q X, m4SweepDenseSpec args m Q X →
      Func.wp Γ full_m4_sweep_dense_body args m Q X := by
  rintro ⟨h, budget, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hinv.lengths.core_ok.cur_vars_le
  have htmk_len := hinv.lengths.scratch_ok.tarjan_mark_len
  unfold Func.wp full_m4_sweep_dense_body; m4_steps
  m4_split
  · m4_steps; exact hQ 1#64 s m hinv rfl (le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  m4_split
  · m4_steps; exact hQ 1#64 s m hinv rfl (le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  m4_split
  · m4_steps; exact hQ 1#64 s m hinv rfl (le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  have hcap : k5MinScr ≤ c.scratch_cap := by unfold k5MinScr; bv_omega
  m4_to_group
  -- Zero `tarjan_mark[0 ..< cur_vars)`
  refine wp_loop_inv (ts := [i64])
    (fun (i, ()) m0 => i.toNat ≤ s.core.cur_vars ∧ ∃ tmk0 : List (BitVec 32),
      tmk0.length = 2 * c.max_vars ∧ (∀ u < i.toNat, tmk0[u]?.getD 0#32 = 0#32) ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_mark := tmk0 } } ⋆ R) m0)
    (fun (i, ()) _ => s.core.cur_vars - i.toNat)
    (fun _ hLi => by
      m4_steps
      exact hLi (0#64, ()) m
        ⟨Nat.zero_le _, s.scratch.tarjan_mark, htmk_len, fun _ hu => by simp at hu, hm⟩)
    (fun _ (i, ()) m0 ⟨hi_le, tmk0, ht0_len, ht0_cov, hm0⟩ hLi => by
      m4_split
      · have hi_lt : i.toNat < s.core.cur_vars := by bv_omega
        have hi_bd : i.toNat < tmk0.length := by omega
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := m4_bv64_add1 (by omega)
        m4_steps; refine hLi (i + 1#64, ()) _ (by dsimp only; omega)
          ⟨by omega, tmk0.set i.toNat 0#32, List.length_set.trans ht0_len, fun u hu => ?_,
           by assumption⟩
        by_cases hui : u = i.toNat
        · subst hui; rw [List.getElem?_set_self (by omega)]; rfl
        · rw [List.getElem?_set_ne (Ne.symm hui)]; exact ht0_cov u (by omega)
      · have hi_eq : i.toNat = s.core.cur_vars := by
          have hlt : ¬ i.toNat < s.core.cur_vars := by
            rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
          omega
        let s0 : FullState := { s with scratch := { s.scratch with tarjan_mark := tmk0 } }
        have hinv0 : FullDenseInv c F0 s0 := fullDenseInv_with_tmk hinv ht0_len
        have ht0_zero : M4TmkZero s0 := fun u hu => ht0_cov u (hi_eq ▸ hu)
        -- Compute `rem_ticks = (tick_lim > 16384ULL) ? 16384ULL : tick_lim;`
        m4_to_group
        refine wp_join_group (ts := [i64])
          (fun (_rem0, ()) mrm => mrm = m0)
          (fun _ (rem0, ()) mrm hmrm => by
            subst mrm
            m4_to_group
            -- Variable loop: `while (v < cv && budget > 0 && rem_ticks > 0 && oom == 0 && fuel >
            -- 0)`
            refine wp_join_group (ts := [i64, i64, i64, i64])
              (fun (_bB, _rB, _vB, resB, ()) mB => ∃ sB, FullDenseInv c F0 sB ∧
                sB.core.cur_vars = s.core.cur_vars ∧ sB.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (resB = 1#64 ∨ resB = 20#64) ∧ (resB = 20#64 → F0.Unsat) ∧ (FullMem c sB ⋆ R) mB)
              (fun _ (_bB, _rB, _vB, resB, ()) mB ⟨sB, hinvB, hcvB, hfuelB, hresB, hunsB, hmB⟩ => by
                m4_to_group; refine wp_unroll_group fun _ _ => ?_
                m4_split
                · have hr20 : resB = 20#64 := by bv_omega
                  m4_steps; exact hQ 20#64 sB mB hinvB hcvB hfuelB (Or.inr rfl)
                    (fun _ => hunsB hr20) hmB
                m4_split
                · have hinc : sB.core.inconsistent ≠ 0#64 := by bv_omega
                  obtain ⟨F_curB, hwB⟩ := hinvB.exists_witness
                  have huns := hwB.2.1.ext_sound.2 (hwB.2.1.inconsistent_sound hinc)
                  m4_steps; exact hQ 20#64 sB mB hinvB hcvB hfuelB (Or.inr rfl) (fun _ => huns) hmB
                · m4_steps; exact hQ 1#64 sB mB hinvB hcvB hfuelB (Or.inl rfl)
                    (fun h => by cases h) hmB)
              (fun _ hJbrk => by
                refine wp_loop_inv (ts := [i64, i64, i64])
                  (fun (budgetL, remL, vL, ()) ml => vL.toNat ≤ s.core.cur_vars ∧
                    ∃ sL, FullDenseInv c F0 sL ∧ sL.core.cur_vars = s.core.cur_vars ∧
                      sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ M4TmkZero sL ∧
                      (FullMem c sL ⋆ R) ml)
                  (fun (_, _, vL, ()) _ => s.core.cur_vars - vL.toNat)
                  (fun _ hLv => by
                    m4_steps
                    exact hLv (budget, rem0, 0#64, ()) m0
                      ⟨Nat.zero_le _, s0, hinv0, rfl, le_refl _, ht0_zero, hm0⟩)
                  (fun _ (budgetL, remL, vL, ()) ml
                      ⟨hv_le, sL, hinvL, hcvL, hfuelL, htmkL, hml⟩ hLv => by
                    have hbrk := hJbrk (budgetL, remL, vL, 1#64, ()) ml
                      ⟨sL, hinvL, hcvL, hfuelL, Or.inl rfl, (fun h => by cases h), hml⟩
                    m4_split; rotate_left; · m4_steps; exact hbrk
                    m4_split; rotate_left; · m4_steps; exact hbrk
                    m4_split; rotate_left; · m4_steps; exact hbrk
                    m4_split; rotate_left; · m4_steps; exact hbrk
                    m4_split; rotate_left; · m4_steps; exact hbrk
                    have hcvL_le := hinvL.lengths.core_ok.cur_vars_le
                    have hv_lt : vL.toNat < sL.core.cur_vars := by
                      have : vL.toNat < s.core.cur_vars % 2 ^ 64 := by bv_omega
                      omega
                    have hfl_len := hinvL.lengths.core_ok.flags_len
                    have hval_len := hinvL.lengths.core_ok.vals_len
                    have hv_fl : vL.toNat < sL.core.flags.length := by omega
                    have h2v_shl : (vL <<< (1 : Nat)).toNat = 2 * vL.toNat := by
                      simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                        Nat.mod_eq_of_lt (by omega : vL.toNat * 2 < 2 ^ 64)]; omega
                    have h2v_vals : (vL <<< (1 : Nat)).toNat < sL.core.vals.length := by omega
                    have hv1 : (vL + 1#64).toNat = vL.toNat + 1 := m4_bv64_add1 (by omega)
                    m4_to_group; refine wp_unroll_group fun _ _ => ?_
                    m4_split; rotate_left
                    · m4_steps; exact hLv (budgetL, remL, vL + 1#64, ()) ml (by dsimp only; omega)
                        ⟨by omega, sL, hinvL, hcvL, hfuelL, htmkL, hml⟩
                    m4_split; rotate_left
                    · m4_steps; exact hLv (budgetL, remL, vL + 1#64, ()) ml (by dsimp only; omega)
                        ⟨by omega, sL, hinvL, hcvL, hfuelL, htmkL, hml⟩
                    -- Eligible variable `vL`: clear `FL_SWEEP`, compute `vlim`, call `sweep_var`
                    m4_to_group
                    let flL' := sL.core.flags.set vL.toNat
                      ((sL.core.flags[vL.toNat]'hv_fl) &&& ~~~1024#32)
                    let sL' : FullState := { sL with core := { sL.core with flags := flL' } }
                    have hinvL' : FullDenseInv c F0 sL' :=
                      fullDenseInv_with_flags hinvL (List.length_set.trans hfl_len)
                    have htmkL' : M4TmkZero sL' := m4_tmkZero_congr htmkL rfl rfl
                    obtain ⟨F_curL, hwL⟩ := hinvL'.exists_witness
                    have hv32 : (vL.setWidth 32).toNat < sL'.core.cur_vars := by
                      rw [bv64_to32_toNat vL (by omega)]; exact hv_lt
                    refine wp_join_group (ts := [i64])
                      (fun (_vlim, ()) mv => (FullMem c sL' ⋆ R) mv)
                      (fun _ (vlim, ()) mv hmv => by
                        m4_steps
                        m4_call hVar
                        refine ⟨c, F0, F_curL, sL', R, rfl, hwL, hcap, hv32, htmkL', hmv,
                          fun rV sV mV hwV hcvV hfuelV htmkV _ hrV_uns hmV => ?_⟩
                        have hfuelV0 := Nat.le_trans hfuelV hfuelL
                        m4_split
                        · have hrV20 : rV = 20#64 := by bv_omega
                          m4_steps; exact hJbrk (budgetL - 1#64, remL, vL, 20#64, ()) mV
                            ⟨sV, hwV.toDense, hcvV.trans hcvL, hfuelV0, Or.inr rfl,
                             (fun _ => hrV_uns hrV20), hmV⟩
                        · have hk11V : 2304 + (BitVec.ofNat 64 11).toNat <
                              sV.scratch.scratch_buf.length := by
                            rw [hwV.1.scratch_ok.scratch_buf_len]; unfold k5MinScr at hcap; simp
                            omega
                          m4_to_group
                          refine wp_join_group (ts := [i64])
                            (fun (_remN, ()) mrN => mrN = mV)
                            (fun _ (remN, ()) mrN hmrN => by
                              subst mrN; m4_steps
                              exact hLv (budgetL - 1#64, remN, vL + 1#64, ()) mV
                                (by dsimp only; omega)
                                ⟨by omega, sV, hwV.toDense, hcvV.trans hcvL, hfuelV0, htmkV, hmV⟩)
                            (fun _ hJrn => by
                              m4_split <;> (m4_steps; exact hJrn _ mV rfl)))
                      (fun _ hJvl => by
                        m4_split <;> (m4_steps; exact hJvl _ _ (by assumption))))))
          (fun _ hJrm => by
            m4_split <;> (m4_steps; exact hJrm _ m0 rfl)))

/-! ## 6. `full_m4_sweep_sat_wp` (`24/24`) -/

theorem full_m4_sweep_sat_wp (Γ : Env)
    (hBt : M4EnvSpec Γ "full_backtrack" Full.fullBacktrackSpec)
    (hEnter : M4EnvSpec Γ "full_enter_dense" Full.fullEnterDenseSpec)
    (hDense : M4EnvSpec Γ "full_m4_sweep_dense" m4SweepDenseSpec)
    (hReb : M4EnvSpec Γ "full_rebuild_watches" Full.fullRebuildWatchesSpec)
    (hProp : M4EnvSpec Γ "full_propagate" Full.fullPropagateSpec) :
    ∀ args m Q X, m4SweepSatSpec args m Q X →
      Func.wp Γ full_m4_sweep_sat_body args m Q X := by
  rintro ⟨h, budget, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_m4_sweep_sat_body
  m4_to_group
  -- 1. `if (h->cur_level != 0) full_backtrack(h, 0);`
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel = s.core.fuel ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ () m1 ⟨s1, hinv1, hlvl1, hfuel1, hm1⟩ => by
      -- 2. `if (h->scratch_cap < K512_MIN_SCR || budget == 0) return 1;`
      m4_split
      · m4_steps
        exact hQ 1#64 s1 m1 hinv1 hlvl1 (hfuel1 ▸ le_refl _) (Or.inl rfl)
          (fun h => by cases h) hm1
      m4_split
      · m4_steps
        exact hQ 1#64 s1 m1 hinv1 hlvl1 (hfuel1 ▸ le_refl _) (Or.inl rfl)
          (fun h => by cases h) hm1
      -- 3. `if (!full_enter_dense(h)) return (h->inconsistent != 0) ? 20 : 1;`
      m4_call hEnter
      refine ⟨c, F0, s1, R, rfl, hinv1, hm1,
        fun ok2 s2 m2 hlvl2 hfuel2 hdense2 hsparse2 hm2 => ?_⟩
      m4_split; rotate_left
      · have hok2_f : ok2 = false := by cases ok2 <;> simp at hc ⊢
        have hsp2 := hsparse2 hok2_f
        have hfl2_0 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by
          rw [hfuel2, hfuel1]; exact le_refl _
        m4_to_group; refine wp_unroll_group fun _ _ => ?_
        m4_split
        · have hinc : s2.core.inconsistent ≠ 0#64 := by bv_omega
          obtain ⟨F_cur2, hw2⟩ := hsp2.exists_witness
          have huns := hw2.2.1.ext_sound.2 (hw2.2.1.inconsistent_sound hinc)
          m4_steps
          exact hQ 20#64 s2 m2 hsp2 hlvl2 hfl2_0 (Or.inr rfl) (fun _ => huns) hm2
        · m4_steps
          exact hQ 1#64 s2 m2 hsp2 hlvl2 hfl2_0 (Or.inl rfl) (fun h => by cases h) hm2
      -- 4. `res = full_m4_sweep_dense(h, budget, tick_lim); rr = full_rebuild_watches(h);`
      have hok2_t : ok2 = true := by cases ok2 <;> simp at hc ⊢
      m4_call hDense
      refine ⟨c, F0, s2, R, rfl, hdense2 hok2_t, hm2,
        fun res s3 m3 hd3 _ hfuel3 _ hres_uns hm3 => ?_⟩
      have hfl3_0 : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by
        rw [← hfuel1, ← hfuel2]; exact hfuel3
      m4_call hReb
      refine ⟨c, F0, s3, R, rfl, hd3, hm3,
        fun rr sR mR hspR hlvlR hfuelR _ hrr_uns hmR => ?_⟩
      have hflR_0 : sR.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuelR hfl3_0
      m4_split
      · have hr20 : res = 20#64 := by bv_omega
        m4_steps; exact hQ 20#64 sR mR hspR hlvlR hflR_0 (Or.inr rfl)
          (fun _ => hres_uns hr20) hmR
      m4_split
      · have hrr20 : rr = 20#64 := by bv_omega
        m4_steps; exact hQ 20#64 sR mR hspR hlvlR hflR_0 (Or.inr rfl)
          (fun _ => hrr_uns hrr20) hmR
      m4_split
      · have hinc : sR.core.inconsistent ≠ 0#64 := by bv_omega
        obtain ⟨F_curR, hwR⟩ := hspR.exists_witness
        have huns := hwR.2.1.ext_sound.2 (hwR.2.1.inconsistent_sound hinc)
        m4_steps; exact hQ 20#64 sR mR hspR hlvlR hflR_0 (Or.inr rfl) (fun _ => huns) hmR
      -- 5. `if (full_propagate(h) == 1ULL) return 20ULL; return 1ULL;`
      obtain ⟨F_curR, hwR⟩ := hspR.exists_witness
      m4_call hProp
      refine ⟨c, F0, F_curR, sR, R, rfl, hwR.1, hwR.2.1, hwR.2.2.2.2.2, hmR, ?_⟩
      intro pr vP fP lP rsP trP tpP teP prP uaP ufP wvP arP wsP wlP wuP flP ctP crP c0P c1P
        ooP tkP wsoP phP mP _ hlenP hwP _ hpermP hfuelP _ _ hpr1 _ _ hmP
      let sP : FullState :=
        { sR with
          core := { sR.core with
            vals := vP, flags := fP, lvl := lP, rsns := rsP, trl := trP, trail_pos := tpP,
            trail_end := teP, propagated := prP, unassigned := uaP, unflushed := ufP,
            wvec := wvP, arena := arP, wstk := wsP, wlen := wlP, wusable := wuP, fuel := flP,
            confl_type := ctP, confl_ref := crP, confl_lit0 := c0P, confl_lit1 := c1P, oom := ooP }
          scratch := { sR.scratch with search_ticks := tkP, wsort := wsoP, phases := phP } }
      have hspP := m4_fullSparseInv_after_propagate hwR sP rfl hlenP hwP hpermP
      have hflP_0 : sP.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuelP hflR_0
      m4_split
      · have hpr_1 : pr = 1#64 := by bv_omega
        m4_steps
        exact hQ 20#64 sP mP hspP hlvlR hflP_0 (Or.inr rfl)
          (fun _ => level0_unsat_of_conflict_okW hwP hlvlR (hpr1 hpr_1).2.2) hmP
      · m4_steps
        exact hQ 1#64 sP mP hspP hlvlR hflP_0 (Or.inl rfl) (fun h => by cases h) hmP)
    (fun _ hJu => by
      m4_split
      · obtain ⟨F_cur, hspw⟩ := hinv.exists_witness
        have hcv_le := hinv.lengths.core_ok.cur_vars_le
        have hcl_lt : s.core.cur_level < 2 ^ 64 := by
          have := hspw.2.1.cur_level_le; have := hinv.lengths.core_ok.trail_end_le; omega
        have hbt_lvl : 0 < c.max_vars := by
          have : s.core.cur_level ≠ 0 := by bv_omega
          have := hspw.2.1.cur_level_le; have := hinv.lengths.core_ok.trail_end_le; omega
        m4_call hBt
        refine ⟨c, s, R, rfl, hinv.lengths, hcl_lt, fun _ => hbt_lvl,
          hspw.2.1.trail_lits_lt, hm, ?_⟩
        intro vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1 _ hlen1 _ _ hcl1 hpres1 _ _
          _ hwinv1 _ hm1
        let s1 : FullState :=
          { s with
            core := { s.core with
              vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1, trail_pos := tp1,
              trail_end := te1, propagated := prop1, cur_level := cl1, unassigned := unass1 }
            scratch := sc1 }
        have hcl1_0 : cl1 = 0 := by simpa using hcl1
        have hw1 := hwinv1 F0 F_cur hspw.2.1 (Nat.zero_le _)
        have hsp1 := fullSparseInv_after_backtrack hspw s1 rfl hlen1 hpres1 hw1
        m4_steps; exact hJu () m1 ⟨s1, hsp1, hcl1_0, rfl, hm1⟩
      · have hl0 : s.core.cur_level = 0 := by
          obtain ⟨_, hspw⟩ := hinv.exists_witness
          have hcv_le := hinv.lengths.core_ok.cur_vars_le
          have := hspw.2.1.cur_level_le; have := hinv.lengths.core_ok.trail_end_le
          have h := congrArg BitVec.toNat (by bv_omega : BitVec.ofNat 64 s.core.cur_level = 0)
          simp [Nat.mod_eq_of_lt (by omega : s.core.cur_level < 2 ^ 64)] at h; exact h
        m4_steps; exact hJu () m ⟨s, hinv, hl0, rfl, hm⟩)

end LeanQbe.T.Examples.Kissat.FullM4Sweep
