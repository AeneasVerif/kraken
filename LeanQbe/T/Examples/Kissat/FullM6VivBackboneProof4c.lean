module

public import LeanQbe.T.Examples.Kissat.FullM6VivBackbone
public import LeanQbe.T.Examples.Kissat.FullProbeTransLemmas5

/-!
# Kissat Wave-2 PR-W2C — `full_probe_assume_pair_m6` OOM-Safe Proof (`Proof4c`)

Certifies UNSAT-sound `Func.wp` (`XPost := False`, `0` SAT model proofs) for
`full_probe_assume_pair_m6` against the exact canonical drop-in specification
`Full.fullProbeAssumePairSpec` (`FullProbeTransSpecs.fullProbeAssumePairSpec`), handling the
added `RC-20` OOM guards (`pp == 2ULL`, `pr2 == 2ULL`, direct `full_probe_flush_hbr` return).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6VivBackbone

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullProbeTransSpecs FullProbeTransHelpers
open scoped FullArenaTactics FullProbeTransTactics

section LocalHelpers

private theorem m6p_hbrBufOkW_zero (F_cur : List (List Nat)) (s : FullState) :
    FullHbrBufOkW F_cur s 0 := ⟨Nat.zero_le _, fun _ hi => by omega⟩

private theorem m6p_hbrBufOkW_congr_vars {F_cur : List (List Nat)} {s s' : FullState} {n : Nat}
    (h : FullHbrBufOkW F_cur s n) (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hws2 : s'.scratch.work_stk2 = s.scratch.work_stk2) : FullHbrBufOkW F_cur s' n :=
  ⟨hcv ▸ h.1, fun i hi => by have h2 := h.2 i hi; simp only [hcv, hws2]; exact h2⟩

private theorem m6p_extScratchOk_of_pres_eq {c : FullCfg} {s s' : FullState}
    (h : FullExtScratchOk c s) (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hex : s'.scratch.extend_len = s.scratch.extend_len)
    (href : fullArenaClauseRefs s' = fullArenaClauseRefs s) : FullExtScratchOk c s' :=
  ⟨fullLastLearnedWf_of_refs_eq h.1 hll href, by simpa [hex] using h.2⟩

private theorem m6p_mrkZero_of_eq {c : FullCfg} {s s' : FullState}
    (h : FullMrkZero c s) (hmrk : s'.core.mrk = s.core.mrk) : FullMrkZero c s' :=
  fun v hv => by rw [hmrk]; exact h v hv

private theorem m6p_litMarksClear_of_eq {c : FullCfg} {s s' : FullState}
    (h : FullLitMarksClear c s) (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) : FullLitMarksClear c s' :=
  ⟨m6p_mrkZero_of_eq h.1 hmrk, fun l hl => by rw [hlm]; exact h.2 l hl⟩

private theorem m6p_witnessInv_with_ctrl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hlen' : s'.core.LengthsOk c)
    (hcv : s'.core.cur_vars = s.core.cur_vars := by rfl)
    (har : s'.core.arena = s.core.arena := by rfl)
    (hal : s'.core.arena_len = s.core.arena_len := by rfl)
    (hcl : s'.core.cur_level = s.core.cur_level := by rfl)
    (hte : s'.core.trail_end = s.core.trail_end := by rfl)
    (htrl : s'.core.trl = s.core.trl := by rfl) (hval : s'.core.vals = s.core.vals := by rfl)
    (hlvl : s'.core.lvl = s.core.lvl := by rfl) (hrsn : s'.core.rsns = s.core.rsns := by rfl)
    (htp : s'.core.trail_pos = s.core.trail_pos := by rfl)
    (hft : s'.core.frame_trail = s.core.frame_trail := by rfl)
    (hfd : s'.core.frame_dec = s.core.frame_dec := by rfl)
    (hinc : s'.core.inconsistent = s.core.inconsistent := by rfl)
    (hwv : s'.core.wvec = s.core.wvec := by rfl) (hws : s'.core.wstk = s.core.wstk := by rfl)
    (hwl : s'.core.wlen = s.core.wlen := by rfl)
    (hdm : s'.core.dense_mode = s.core.dense_mode := by rfl) :
    FullWitnessInv c F0 F_cur s'.core :=
  fullWitnessInv_congr_ctrl hw hlen' hcv har hal hcl hte htrl hval hlvl hrsn htp hft hfd hinc
    hwv hws hwl hdm

private theorem m6p_sparseInvW_set_litMark {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {lm : List (BitVec 8)}
    (hlen' : ({ s with core := { s.core with lit_mark := lm } } : FullState).LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core)
    (hclr : FullLitMarksClear c { s with core := { s.core with lit_mark := lm } })
    (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hdm : s.core.dense_mode = 0#64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with lit_mark := lm } } :=
  ⟨hlen', m6p_witnessInv_with_ctrl hw hlen'.core_ok, hclr,
    fullArenaVarsNodup_of_arena_eq hnd rfl rfl,
    m6p_extScratchOk_of_pres_eq hext rfl rfl rfl, hdm⟩

private abbrev m6p_btState (s : FullState) (vals' : List (BitVec 8))
    (lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' cl' : Nat) (unass' : BitVec 64)
    (sc' : FullScratch) : FullState :=
  { s with
    core := { s.core with
      vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
    scratch := sc' }

private theorem m6p_btState_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' : BitVec 64} {sc' : FullScratch}
    (hlen' : (m6p_btState s vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc').LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      (m6p_btState s vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc').core)
    (hlm : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hdm : s.core.dense_mode = 0#64) (hpres : FullExtScratchPres s { s with scratch := sc' }) :
    FullSparseInv c F0 (m6p_btState s vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc') :=
  ⟨⟨hlen', F_cur, hw'⟩, m6p_litMarksClear_of_eq hlm rfl rfl,
    fullArenaVarsNodup_of_arena_eq hnd rfl rfl,
    m6p_extScratchOk_of_pres_eq hext hpres.1 hpres.2 rfl, hdm⟩

private theorem m6p_bv8_sext32_eq0 {x : BitVec 8} (h : x.signExtend 32 = 0#32) : x = 0#8 := by
  revert x h; decide

private theorem m6p_vals_eq_0_of_sext {vals : List (BitVec 8)} {i : Nat} (hi : i < vals.length)
    (heq : (vals[i]'hi).signExtend 32 = 0#32) : vals[i]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some, m6p_bv8_sext32_eq0 heq]

private theorem m6p_bv64_setWidth32 {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  have hn64 : n < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat hn64, bv32_ofNat_toNat hn, Nat.mod_eq_of_lt hn]

private abbrev m6p_lvl1DecState (s : FullState) (lit : BitVec 32) (flags' : List (BitVec 32))
    (phases' : List (BitVec 8)) (unass' : BitVec 64) : FullState :=
  let v := lit.toNat / 2
  { s with
    core := { s.core with
      vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
      flags := flags', lvl := s.core.lvl.set v 1#32
      rsns := s.core.rsns.set v 0xFFFFFFFF#32, trl := s.core.trl.set s.core.trail_end lit
      trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
      trail_end := s.core.trail_end + 1, cur_level := 1, unassigned := unass'
      frame_trail := s.core.frame_trail.set 1 (BitVec.ofNat 32 s.core.trail_end)
      frame_dec := s.core.frame_dec.set 1 lit }
    scratch := { s.scratch with phases := phases' } }

private theorem m6p_level1Decide_preserves_witness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    {lit : BitVec 32} (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    {flags' : List (BitVec 32)} {phases' : List (BitVec 8)} {unass' : BitVec 64}
    (hfll : flags'.length = c.max_vars) (hph : phases'.length = c.max_vars) :
    let s' := m6p_lvl1DecState s lit flags' phases' unass'
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core ∧
      s.core.trail_end < s'.core.trail_end ∧ s'.core.trl[s.core.trail_end]? = some lit ∧
      s'.core.lvl[lit.toNat / 2]? = some 1#32 ∧
      s'.core.rsns[lit.toNat / 2]? = some 0xFFFFFFFF#32 := by
  let v := lit.toNat / 2
  intro s'; have hcl := hlen.core_ok; have hmv := fullInv_max_vars_lt32 c
  have hte_lt := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var := (hw.vals_zero_iff hlit).mp hun
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hcv_le := hcl.cur_vars_le; have hv_lt : v < c.max_vars := by omega
  have hte_max : s.core.trail_end < c.max_vars := by omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by omega
  have h1_ft : 1 < s.core.frame_trail.length := by rw [hcl.frame_trail_len]; omega
  have h1_fd : 1 < s.core.frame_dec.length := by rw [hcl.frame_dec_len]; omega
  have htv : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
    fun i hi => by have := hw.trail_lits_lt i hi; omega
  have hlen' : s'.LengthsOk c := ⟨{ hcl with
    vals_len := by simp [s', hcl.vals_len], flags_len := by simp [s', hfll]
    lvl_len := by simp [s', hcl.lvl_len], rsns_len := by simp [s', hcl.rsns_len]
    trl_len := by simp [s', hcl.trl_len], trail_pos_len := by simp [s', hcl.trail_pos_len]
    frame_trail_len := by simp [s', hcl.frame_trail_len]
    frame_dec_len := by simp [s', hcl.frame_dec_len], trail_end_le := by simp [s']; omega
    propagated_le := by simp [s']; have := hcl.propagated_le; omega },
    { hlen.scratch_ok with phases_len := by simp [s', hph] }⟩
  have htrl_get : ∀ i < s.core.trail_end + 1, (s'.core.trl[i]?.getD 0#32).toNat =
      if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat := fun i _ => by
    by_cases he : i = s.core.trail_end
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars, (s'.core.lvl[w]?.getD 0#32).toNat =
      if w = v then 1 else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; dsimp only [s', m6p_lvl1DecState]; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt), Option.getD_some]; rfl
    · dsimp only [s', m6p_lvl1DecState]; rw [ite_eq_right he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars, s'.core.vals[l]?.getD 0#8 =
      if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
      else s.core.vals[l]?.getD 0#8 := fun l _ => by
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; simp only [s', ↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · simp only [s', h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < s.core.cur_vars, s'.core.rsns[w]?.getD 0xFFFFFFFF#32 =
      if w = v then 0xFFFFFFFF#32 else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; dsimp only [s', m6p_lvl1DecState]; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt), Option.getD_some]
    · dsimp only [s', m6p_lvl1DecState]; rw [ite_eq_right he, List.getElem?_set_ne (Ne.symm he)]
  have hno_rsn : ∀ idx < s.core.trail_end + 1, s'.core.rsns[
      (s'.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 → False := by
    intro idx hidx hne; rw [htrl_get idx hidx] at hne; by_cases hie : idx = s.core.trail_end
    · simp only [hie, ↓reduceIte] at hne; rw [hrsn_get v (by omega)] at hne; simp at hne
    · have hilt : idx < s.core.trail_end := by omega
      simp only [hie, ↓reduceIte] at hne
      rw [hrsn_get _ (htv idx hilt), ite_eq_right (hnot_var idx hilt)] at hne
      exact absurd (hw.level0_rsn_none idx hilt (by have := hw.lvl_le idx hilt; omega)) hne
  have hw' : FullWitnessInv c F0 F_cur s'.core := by
    refine ⟨hw.ext_sound, hw.inconsistent_sound, { hw.arena with len_ok := hw.arena.len_ok },
      hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr, by dsimp [s']; omega,
      fun i hi => by
        dsimp [s'] at hi ⊢; rw [htrl_get i hi]; split
        exact hlit; exact hw.trail_lits_lt i (by omega),
      fun i j hi hj hveq => by
        dsimp [s'] at hi hj; rw [htrl_get i hi, htrl_get j hj] at hveq
        split at hveq <;> split at hveq
        · omega
        · exact absurd hveq.symm (hnot_var j (by omega))
        · exact absurd hveq (hnot_var i (by omega))
        · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq,
      fun l hl => by
        dsimp [s'] at hl; rw [hvals_get l hl]; split
        · exact Or.inr (Or.inr rfl)
        · split; exact Or.inr (Or.inl rfl); exact hw.vals_domain l hl,
      fun l hl => by
        dsimp [s'] at hl; rw [hvals_get l hl]; show _ ↔ ∃ i < s.core.trail_end + 1, _
        constructor
        · intro h1; by_cases hn : l = lit.toNat ^^^ 1; · simp [hn] at h1
          simp only [hn, ↓reduceIte] at h1; by_cases hp : l = lit.toNat
          · exact ⟨s.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hp]⟩
          · simp only [hp, ↓reduceIte] at h1; obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
            exact ⟨i, by omega, by
              rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq; by_cases hie : i = s.core.trail_end
          · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩,
      fun l hl => by
        dsimp [s'] at hl; rw [hvals_get l hl]; show _ ↔ ∃ i < s.core.trail_end + 1, _
        constructor
        · intro h1; by_cases hn : l = lit.toNat ^^^ 1
          · exact ⟨s.core.trail_end, by omega, by
              rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hn]; exact (litNeg_litNeg _).symm⟩
          · simp only [hn, ↓reduceIte] at h1; by_cases hp : l = lit.toNat; · simp [hp] at h1
            simp only [hp, ↓reduceIte] at h1; obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
            exact ⟨i, by omega, by
              rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq; by_cases hie : i = s.core.trail_end
          · simp only [hie, ↓reduceIte] at heq
            have h : lit.toNat ^^^ 1 = l := (congrArg litNeg heq).trans (litNeg_litNeg l)
            simp [← h]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by
              have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩,
      fun i hi => by
        dsimp [s'] at hi ⊢; rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
        · have hilt : i < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte]; rw [hlvl_get _ (htv i hilt), ite_eq_right (hnot_var i hilt)]
          have := hw.lvl_le i hilt; omega,
      fun i j hi hj hleq hdec => by
        dsimp [s'] at hi hj hleq hdec; rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
        by_cases hje : j = s.core.trail_end
        · by_cases hie : i = s.core.trail_end; · omega
          have hilt : i < s.core.trail_end := by omega
          simp only [hie, hje, ↓reduceIte] at hleq
          rw [hlvl_get _ (htv i hilt), hlvl_get v (by omega),
            ite_eq_right (hnot_var i hilt), ite_eq_left rfl] at hleq
          have := hw.lvl_le i hilt; omega
        · have hjlt : j < s.core.trail_end := by omega
          simp only [hje, ↓reduceIte] at hdec
          rw [hlvl_get _ (htv j hjlt), ite_eq_right (hnot_var j hjlt)] at hdec
          have := hw.lvl_le j hjlt; omega,
      fun L hL1 hLle => by
        dsimp [s'] at hLle; have hLeq : L = 1 := by omega
        subst hLeq; refine ⟨s.core.trail_end, by dsimp [s']; omega, ?_⟩
        rw [htrl_get _ (by omega)]; simp only [↓reduceIte]; rw [hlvl_get v (by omega)]; simp,
      fun i hi hli => by
        dsimp [s'] at hi hli ⊢; rw [htrl_get i hi] at hli ⊢; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at hli; rw [hlvl_get v (by omega)] at hli; simp at hli
        · have hilt : i < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte] at hli ⊢
          rw [hlvl_get _ (htv i hilt), ite_eq_right (hnot_var i hilt)] at hli
          exact hw.level0_sound i hilt hli,
      fun i hi => by
        dsimp [s'] at hi; rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
        · subst hie; simp only [↓reduceIte, s']
          rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]
        · have hilt : i < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte, s']
          rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]; exact hw.trail_pos_inv i hilt,
      fun idx hidx hli => by
        dsimp [s'] at hidx hli ⊢; rw [htrl_get idx hidx] at hli ⊢
        by_cases hie : idx = s.core.trail_end
        · simp only [hie, ↓reduceIte] at hli; rw [hlvl_get v (by omega)] at hli; simp at hli
        · have hilt : idx < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte] at hli ⊢; have hnv := hnot_var idx hilt
          rw [hlvl_get _ (htv idx hilt), ite_eq_right hnv] at hli
          rw [hrsn_get _ (htv idx hilt), ite_eq_right hnv]; exact hw.level0_rsn_none idx hilt hli,
      fun L hL => by
        dsimp [s'] at hL ⊢
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ (Nat.lt_succ_of_le hL)) with rfl | hL0
        · rw [List.getElem?_set_self h1_ft, Option.getD_some, bv32_ofNat_toNat hte_lt32]; omega
        · have : L = 0 := by omega
          subst this; rw [List.getElem?_set_ne (by omega)]
          have := hw.frame_trail_lt 0 (Nat.zero_le _); omega,
      fun L1 L2 h1 h2 => by
        dsimp [s'] at h2 ⊢; by_cases h2z : L2 = 0
        · subst h2z; have h1z : L1 = 0 := by omega
          subst h1z; exact Nat.le_refl _
        · have h2one : L2 = 1 := by omega
          subst h2one; rw [List.getElem?_set_self h1_ft, Option.getD_some,
            bv32_ofNat_toNat hte_lt32]
          rcases Nat.eq_or_lt_of_le h1 with rfl | h1z
          · rw [List.getElem?_set_self h1_ft, Option.getD_some, bv32_ofNat_toNat hte_lt32]
            exact Nat.le_refl _
          · have h1z' : L1 = 0 := by omega
            subst h1z'; rw [List.getElem?_set_ne (by omega)]
            exact hw.frame_trail_lt 0 (Nat.zero_le _),
      fun L hL1 hLle i hi => by
        dsimp [s'] at hLle hi ⊢; have hLeq : L = 1 := by omega
        subst hLeq; rw [List.getElem?_set_self h1_ft, Option.getD_some,
          bv32_ofNat_toNat hte_lt32] at hi
        rw [htrl_get i (by omega)]; simp only [show i ≠ s.core.trail_end by omega, ↓reduceIte]
        rw [hlvl_get _ (htv i hi), ite_eq_right (hnot_var i hi)]; have := hw.lvl_le i hi; omega,
      fun L hL1 hLle => by
        dsimp [s'] at hLle ⊢; have : L = 1 := by omega
        subst this; rw [List.getElem?_set_self h1_fd, Option.getD_some]; exact hlit,
      fun idx hidx hne => False.elim (hno_rsn idx (by simpa [s'] using hidx) hne),
      fun idx hidx hne _ => False.elim (hno_rsn idx (by simpa [s'] using hidx) hne)⟩
  exact ⟨hlen', hw', by dsimp [s']; omega,
    List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max),
    List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt),
    List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)⟩

private theorem m6p_litSat_neg_iff (α : Nat → Bool) (l : Nat) :
    (α (litVar (l ^^^ 1)) = !(litSign (l ^^^ 1))) ↔ α (litVar l) = litSign l := by
  change (α (litVar (litNeg l)) = !(litSign (litNeg l))) ↔ _
  rw [litVar_litNeg, litSign_litNeg, Bool.not_not]

private theorem m6p_trail_entails_of_level1_dec {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hcl1 : k.cur_level = 1) {t0 : Nat} {dec : BitVec 32} (ht0 : t0 < k.trail_end)
    (htrl0 : k.trl[t0]? = some dec) (hlvl0 : k.lvl[dec.toNat / 2]? = some 1#32)
    (hrsn0 : k.rsns[dec.toNat / 2]? = some 0xFFFFFFFF#32) :
    ∀ idx < k.trail_end, (cnfOfClauses F_cur).EntailsClause
      (cnfClause [dec.toNat ^^^ 1, (k.trl[idx]?.getD 0#32).toNat]) := by
  have htrl0_nat : (k.trl[t0]?.getD 0#32).toNat = dec.toNat := by rw [htrl0, Option.getD_some]
  have hlvl0_nat : (k.lvl[dec.toNat / 2]?.getD 0#32).toNat = 1 := by
    rw [hlvl0, Option.getD_some]; rfl
  have hrsn0_get : k.rsns[dec.toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
    rw [hrsn0, Option.getD_some]
  have hsuff : ∀ idx, idx < k.trail_end → ∀ α, (cnfOfClauses F_cur).Sat α →
      α (litVar dec.toNat) = !(litSign dec.toNat) →
      α (litVar (k.trl[idx]?.getD 0#32).toNat) = !(litSign (k.trl[idx]?.getD 0#32).toNat) := by
    intro idx; induction idx using Nat.strongRecOn with
    | ind idx ih =>
      intro hi α hα hdec
      by_cases hlv0 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0
      · obtain ⟨q, hqm, hqs⟩ := (clause_sat_cnfClause_iff α _).mp
          (CNF.entails_clause_def.mp (hw.level0_sound idx hi hlv0) α hα)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hqm; subst hqm; exact hqs
      · have hlv1 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 1 := by
          have := hw.lvl_le idx hi; omega
        by_cases hrsn : k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
            0xFFFFFFFF#32
        · have := hw.dec_earliest t0 idx ht0 hi (by rw [htrl0_nat, hlvl0_nat, hlv1])
            ⟨by omega, hrsn⟩
          have := hw.dec_earliest idx t0 hi ht0 (by rw [htrl0_nat, hlvl0_nat, hlv1])
            ⟨by rw [htrl0_nat, hlvl0_nat]; omega, by rw [htrl0_nat]; exact hrsn0_get⟩
          rw [show idx = t0 by omega, htrl0_nat]; exact hdec
        · have hri := hw.reason_inv idx hi hrsn
          change (if (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then _ else _) at hri
          by_cases hbin : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
              0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
          · rw [ite_eq_left hbin] at hri; obtain ⟨_, hent_b, m, hm, hmeq, _⟩ := hri
            have ihm := ih m hm (by omega) α hα hdec; rw [hmeq, m6p_litSat_neg_iff] at ihm
            obtain ⟨q, hqm, hqs⟩ := (clause_sat_cnfClause_iff α _).mp
              (CNF.entails_clause_def.mp hent_b α hα)
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hqm
            rcases hqm with rfl | rfl; exact hqs
            exfalso; rw [ihm] at hqs; revert hqs; cases litSign _ <;> decide
          · rw [ite_eq_right hbin] at hri; obtain ⟨href, hng, hall⟩ := hri
            obtain ⟨q, hqm, hqs⟩ := (clause_sat_cnfClause_iff α _).mp
              (CNF.entails_clause_def.mp (hw.arena.entails _ href hng) α hα)
            rcases hall q hqm with rfl | ⟨m, hm, hmeq, _⟩
            · exact hqs
            · exfalso; have ihm := ih m hm (by omega) α hα hdec
              rw [hmeq, m6p_litSat_neg_iff] at ihm
              rw [ihm] at hqs; revert hqs; cases litSign q <;> decide
  intro idx hi; rw [CNF.entails_clause_def]; intro α hα
  by_cases hsdec : α (litVar dec.toNat) = !(litSign dec.toNat)
  · exact (clause_sat_cnfClause_iff α _).mpr ⟨_, by simp, hsuff idx hi α hα hsdec⟩
  · have hdf : α (litVar dec.toNat) = litSign dec.toNat := by
      revert hsdec; cases litSign dec.toNat <;> cases α (litVar dec.toNat) <;> decide
    exact (clause_sat_cnfClause_iff α _).mpr
      ⟨dec.toNat ^^^ 1, by simp, (m6p_litSat_neg_iff α dec.toNat).mpr hdf⟩

private theorem m6p_level1Decide_after_prop {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_a s_p : FullState} (hw_p : FullWitnessInv c F0 F_cur s_p.core)
    (hcl1_p : s_p.core.cur_level = 1) {te0 : Nat} {dec : BitVec 32}
    (hte_a : te0 < s_a.core.trail_end) (htrl_a : s_a.core.trl[te0]? = some dec)
    (hlvl_a : s_a.core.lvl[dec.toNat / 2]? = some 1#32)
    (hrsn_a : s_a.core.rsns[dec.toNat / 2]? = some 0xFFFFFFFF#32)
    (htr : (s_a.core.trail_end ≤ s_p.core.trail_end ∧
      (∀ i < s_a.core.trail_end, s_p.core.trl[i]? = s_a.core.trl[i]?) ∧
      (∀ i < s_a.core.trail_end, s_p.core.lvl[(s_a.core.trl[i]?.getD 0#32).toNat / 2]? =
        s_a.core.lvl[(s_a.core.trl[i]?.getD 0#32).toNat / 2]?)) ∧
      (∀ i < s_a.core.trail_end, s_p.core.rsns[(s_a.core.trl[i]?.getD 0#32).toNat / 2]? =
        s_a.core.rsns[(s_a.core.trl[i]?.getD 0#32).toNat / 2]?)) :
    te0 < s_p.core.trail_end ∧ ∀ idx < s_p.core.trail_end, (cnfOfClauses F_cur).EntailsClause
      (cnfClause [dec.toNat ^^^ 1, (s_p.core.trl[idx]?.getD 0#32).toNat]) := by
  have hp_te := Nat.lt_of_lt_of_le hte_a htr.1.1
  have hp_trl := (htr.1.2.1 te0 hte_a).trans htrl_a
  have h1l := htr.1.2.2 te0 hte_a; have h1r := htr.2 te0 hte_a
  simp only [htrl_a, Option.getD_some] at h1l h1r
  exact ⟨hp_te, m6p_trail_entails_of_level1_dec hw_p hcl1_p hp_te hp_trl
    (h1l.trans hlvl_a) (h1r.trans hrsn_a)⟩

private theorem m6p_resolve_pair_unit {F_cur : List (List Nat)} {a b : Nat}
    (h1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [a ^^^ 1, b]))
    (h2 : (cnfOfClauses F_cur).EntailsClause (cnfClause [a, b])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [b]) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢; intro α hα
  by_cases ha : α (litVar a) = !(litSign a)
  · obtain ⟨q, hqm, hqs⟩ := (clause_sat_cnfClause_iff α _).mp (h1 α hα)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hqm
    rcases hqm with rfl | rfl
    · exfalso; rw [m6p_litSat_neg_iff, ha] at hqs; revert hqs; cases litSign a <;> decide
    · exact (clause_sat_cnfClause_iff α _).mpr ⟨q, by simp, hqs⟩
  · have haf : α (litVar a) = litSign a := by
      revert ha; cases litSign a <;> cases α (litVar a) <;> decide
    obtain ⟨q, hqm, hqs⟩ := (clause_sat_cnfClause_iff α _).mp (h2 α hα)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hqm
    rcases hqm with rfl | rfl
    · exfalso; rw [haf] at hqs; revert hqs; cases litSign q <;> decide
    · exact (clause_sat_cnfClause_iff α _).mpr ⟨q, by simp, hqs⟩

private def M6pSavedMarksInv (c : FullCfg) (s : FullState) (sn : Nat) : Prop :=
  sn ≤ s.core.cur_vars ∧
  (∀ j < sn, (s.scratch.work_stk1[j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 ≠ 0#8 →
    ∃ j < sn, (s.scratch.work_stk1[j]?.getD 0#32).toNat = l)

private def M6pMarkedLitsEntailed (F_cur : List (List Nat)) (lit : Nat) (s : FullState) : Prop :=
  ∀ l < 2 * s.core.cur_vars, s.core.lit_mark[l]?.getD 0#8 ≠ 0#8 →
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit ^^^ 1, l])

private theorem m6p_savedMarksInv_congr {c : FullCfg} {s s' : FullState} {sn : Nat}
    (h : M6pSavedMarksInv c s sn) (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hws1 : s'.scratch.work_stk1 = s.scratch.work_stk1) : M6pSavedMarksInv c s' sn :=
  ⟨hcv ▸ h.1, fun j hj => by simpa [hcv, hws1] using h.2.1 j hj,
   fun l hl hne => by simpa [hlm, hws1] using h.2.2 l hl (by simpa [hlm] using hne)⟩

private theorem m6p_markedLitsEntailed_congr {F_cur : List (List Nat)} {lit : Nat}
    {s s' : FullState} (h : M6pMarkedLitsEntailed F_cur lit s)
    (hcv : s'.core.cur_vars = s.core.cur_vars) (hlm : s'.core.lit_mark = s.core.lit_mark) :
    M6pMarkedLitsEntailed F_cur lit s' :=
  fun l hl hne => h l (hcv ▸ hl) (hlm ▸ hne)

private def M6pBonesUnitInv (F_cur : List (List Nat)) (s : FullState) (bn : Nat) : Prop :=
  bn ≤ s.core.cur_vars ∧ ∀ i < bn, let u := (s.core.tmp[i]?.getD 0#32).toNat
    u < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [u])

private theorem m6p_bonesUnitInv_congr {F_cur : List (List Nat)} {s s' : FullState} {bn : Nat}
    (h : M6pBonesUnitInv F_cur s bn) (hcv : s'.core.cur_vars = s.core.cur_vars)
    (htmp : s'.core.tmp = s.core.tmp) : M6pBonesUnitInv F_cur s' bn :=
  ⟨hcv ▸ h.1, fun i hi => by have := h.2 i hi; simp only [hcv, htmp]; exact this⟩

private def m6p_clearLmLoopExpr {rs : List Ty} (pWstk1 pLitMark sn_v : Val i64)
    (k_after : Expr Val Cont rs) : Expr Val Cont rs :=
  Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun p =>
    Expr.let_ ⟨.cmp .ult i64, (.var p.fst, .var sn_v, ())⟩ fun p_lt =>
    Expr.jnz (.var p_lt.fst)
      (Expr.let_ ⟨.mul i64, (.var p.fst, .imm 4, ())⟩ fun p_off =>
       Expr.let_ ⟨.add i64, (.var pWstk1, .var p_off.fst, ())⟩ fun p_addr =>
       Expr.load i32 (.var p_addr.fst) fun ld =>
       Expr.let_ ⟨.zext 32 64, (.var ld, ())⟩ fun p_l =>
       Expr.let_ ⟨.add i64, (.var pLitMark, .var p_l.fst, ())⟩ fun p_dst =>
       Expr.let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p_z =>
       Expr.store (.var p_z.fst) (.var p_dst.fst)
         (Expr.let_ ⟨.add i64, (.var p.fst, .imm 1, ())⟩ fun p_next =>
          Expr.jump Js.fst (.var p_next.fst, ())))
      k_after) Blocks.nil) (fun Js => Expr.jump Js.fst (.imm 0, ()))

private theorem m6p_clearLmLoop_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {st : FullState} {R : Mem 64 → Prop} {sn_v : Val i64} {ml : Mem 64}
    {k_after : Expr Val Cont rs} (hlen : st.LengthsOk c) (hmrk : FullMrkZero c st)
    (hsav : M6pSavedMarksInv c st sn_v.toNat) (hm : (FullMem c st ⋆ R) ml)
    (hk : ∀ lm' m', lm'.length = 2 * c.max_vars →
      let st' : FullState := { st with core := { st.core with lit_mark := lm' } }
      st'.LengthsOk c → FullLitMarksClear c st' → (FullMem c st' ⋆ R) m' →
      wp Γ Q X k_after m') :
    wp Γ Q X (m6p_clearLmLoopExpr c.pWorkStk1 c.pLitMark sn_v k_after) ml := by
  have hcl := hlen.core_ok; have hcv_le := hcl.cur_vars_le
  have hws1_len := hlen.scratch_ok.work_stk1_len; have hlm_len := hcl.lit_mark_len
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  let loopInv : Tup Val [i64] → Mem 64 → Prop := fun (k_v, ()) m_k =>
    k_v.toNat ≤ sn_v.toNat ∧ ∃ lm : List (BitVec 8), lm.length = 2 * c.max_vars ∧
      (∀ l < 2 * c.max_vars, lm[l]?.getD 0#8 ≠ 0#8 →
        ∃ j, k_v.toNat ≤ j ∧ j < sn_v.toNat ∧ (st.scratch.work_stk1[j]?.getD 0#32).toNat = l) ∧
      (FullMem c { st with core := { st.core with lit_mark := lm } } ⋆ R) m_k
  let meas : Tup Val [i64] → Mem 64 → Nat := fun (k_v, ()) _ => sn_v.toNat - k_v.toNat
  unfold m6p_clearLmLoopExpr
  refine wp_loop_inv loopInv meas (fun Js hJs => ?_)
    (fun Js (k_v, ()) m_k ⟨hk_le, lm, hlen_lm, hcov, hm_k⟩ hJs => ?_)
  · pt_steps_nogrp
    exact hJs (0#64, ()) ml ⟨Nat.zero_le _, st.core.lit_mark, hlm_len, fun l hl hne =>
      let ⟨j, hj1, hj2⟩ := hsav.2.2 l hl hne; ⟨j, Nat.zero_le _, hj1, hj2⟩, hm⟩
  · pt_steps_nogrp
    · have hk_lt : k_v.toNat < sn_v.toNat := by pt_bound
      have hk_ws : k_v.toNat < st.scratch.work_stk1.length := by have := hsav.1; omega
      have htl_lt : (st.scratch.work_stk1[k_v.toNat]'hk_ws).toNat < 2 * st.core.cur_vars := by
        simpa [List.getElem?_eq_getElem hk_ws] using hsav.2.1 k_v.toNat hk_lt
      have htl_lm : ((st.scratch.work_stk1[k_v.toNat]'hk_ws).setWidth 64).toNat < lm.length := by
        rw [bv_c0_zext32_64, hlen_lm]; omega
      have hk1_eq := bv64_add1_toNat (by have := hsav.1; omega : k_v.toNat + 1 < 2 ^ 64)
      pt_steps_nogrp
      let tl_v := st.scratch.work_stk1[k_v.toNat]'hk_ws; let lm' := lm.set tl_v.toNat 0#8
      have hcov' : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 ≠ 0#8 →
          ∃ j, k_v.toNat + 1 ≤ j ∧ j < sn_v.toNat ∧
            (st.scratch.work_stk1[j]?.getD 0#32).toNat = l := by
        intro l hl hne; by_cases hle : l = tl_v.toNat
        · subst hle; rw [List.getElem?_set_self (by rw [hlen_lm]; omega), Option.getD_some] at hne
          exact absurd rfl hne
        · rw [List.getElem?_set_ne (Ne.symm hle)] at hne
          obtain ⟨j, hj1, hj2, hjeq⟩ := hcov l hl hne
          have hne_j : j ≠ k_v.toNat := fun hjk => by
            subst hjk; rw [List.getElem?_eq_getElem hk_ws, Option.getD_some] at hjeq
            exact hle hjeq.symm
          exact ⟨j, by omega, hj2, hjeq⟩
      refine hJs (k_v + 1#64, ()) m (by dsimp only [meas]; rw [hk1_eq]; omega)
        ⟨by rw [hk1_eq]; omega, lm', by simp [lm', hlen_lm], by simpa only [hk1_eq] using hcov', ?_⟩
      simpa only [lm', tl_v, bv_c0_zext32_64] using hm
    · have hk_eq : k_v.toNat = sn_v.toNat := by pt_bound
      let st' : FullState := { st with core := { st.core with lit_mark := lm } }
      refine hk lm m_k hlen_lm ⟨{ hcl with lit_mark_len := hlen_lm }, hlen.scratch_ok⟩
        ⟨m6p_mrkZero_of_eq hmrk rfl, fun l hl => ?_⟩ hm_k
      by_cases hz : st'.core.lit_mark[l]?.getD 0#8 = 0#8; exact hz
      exfalso; obtain ⟨j, hj1, hj2, _⟩ := hcov l hl hz; omega

private def m6p_analyzeBranchExpr (h_arg hbr_v : Val i64) : Expr Val Cont [i64] :=
  Expr.call "full_analyze" (as := [i64]) (bs := [i64]) (.var h_arg, ()) fun p_ast =>
  Expr.let_ ⟨.cmp .eq i64, (.var p_ast.fst, .imm 20, ())⟩ fun p_is20 =>
  Expr.jnz (.var p_is20.fst) (Expr.ret (.imm 20, ()))
    (Expr.let_ ⟨.cmp .ne i64, (.var p_ast.fst, .imm 1, ())⟩ fun p_ne1 =>
     Expr.jnz (.var p_ne1.fst)
       (Expr.call "full_backtrack" (as := [i64, i64]) (bs := []) (.var h_arg, .imm 0, ())
         fun _ => Expr.ret (.imm 2, ()))
       (Expr.call "full_propagate" (as := [i64]) (bs := [i64]) (.var h_arg, ()) fun p_pr =>
        Expr.let_ ⟨.cmp .eq i64, (.var p_pr.fst, .imm 1, ())⟩ fun p_is1 =>
        Expr.jnz (.var p_is1.fst) (Expr.ret (.imm 20, ()))
          (Expr.let_ ⟨.cmp .eq i64, (.var p_pr.fst, .imm 2, ())⟩ fun p_is2 =>
           Expr.jnz (.var p_is2.fst) (Expr.ret (.imm 2, ()))
             (Expr.call "full_probe_flush_hbr" (as := [i64, i64]) (bs := [i64])
               (.var h_arg, .var hbr_v, ()) fun p_r => Expr.ret (.var p_r.fst, ())))))

private theorem m6p_analyzeBranch_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st : FullState}
    {R : Mem 64 → Prop} {hbr_v : Val i64} {ml : Mem 64}
    (hAnalyze : ∀ args m Q X, fullAnalyze20Spec args m Q X →
      Γ "full_analyze" [i64] [i64] args m Q X)
    (hBacktrack : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hPropagate : ∀ args m Q X, fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hFlushHbr : ∀ args m Q X, fullProbeFlushHbrSpec args m Q X →
      Γ "full_probe_flush_hbr" [i64, i64] [i64] args m Q X)
    (hsparse : FullSparseInvW c F0 F_cur st) (hconfl : FullConflictOkW F_cur st)
    (hcl1 : st.core.cur_level = 1) (hhbr : FullHbrBufOkW F_cur st hbr_v.toNat)
    (hcv : st.core.cur_vars = s.core.cur_vars) (hfu : st.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hpos_mv : 0 < c.max_vars) (hm : (FullMem c st ⋆ R) ml)
    (hQ : ∀ r s' m',
      (r = 1#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 20#64 → F0.Unsat ∧ ∃ F_cur', FullOtfsInvW c F0 F_cur' s') →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (m6p_analyzeBranchExpr c.hdr hbr_v) ml := by
  unfold m6p_analyzeBranchExpr; pt_steps_nogrp; c0_call hAnalyze
  refine ⟨c, F0, F_cur, st, R, rfl, hsparse, hconfl, hm, ?_⟩; dsimp only
  intro ast st1 m1 hlen1 har_dom hcv1 hfu1 hws2_1 har20 har0 har1 hm1
  have hcv1s := hcv1.trans hcv; have hfu1s := Nat.le_trans hfu1 hfu
  have hhbr1 := m6p_hbrBufOkW_congr_vars hhbr hcv1 hws2_1; pt_steps_nogrp
  · have hast : ast = 20#64 := by pt_clear_big; exact hc
    obtain ⟨hunsat, hot⟩ := har20 hast
    simpa only [show (20#64 : BitVec 64) = 20 from rfl] using hQ 20#64 st1 m1
      (fun h => by rcases h with h | h <;> exact absurd h (by decide))
      (fun _ => ⟨hunsat, F_cur, hot⟩) hcv1s hfu1s (Or.inr (Or.inr rfl)) hm1
  · have hast0 : ast = 0#64 := by
      pt_clear_big
      rcases har_dom with rfl | rfl | rfl
      · rfl
      · exact absurd rfl hc
      · exact absurd rfl (by assumption)
    have hot1 := har0 hast0
    have hcl_64 : st1.core.cur_level < 2 ^ 64 := by
      have := hot1.2.1.cur_level_le; have := hlen1.core_ok.trail_end_le
      have := hlen1.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at this; omega
    pt_steps_nogrp; c0_call hBacktrack
    refine ⟨c, st1, R, rfl, hlen1, hcl_64, fun _ => hpos_mv, hot1.2.1.trail_lits_lt, hm1, ?_⟩
    dsimp only; intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m2 hlen2 _ _ hcl2
      hpres _ _ _ hbt_w hbt_o hm2
    let st2 := m6p_btState st1 vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc'
    have hw2 : FullWitnessInv c F0 F_cur st2.core := by
      by_cases hcz : st1.core.cur_level = 0
      · exact hbt_w F0 F_cur (hot1.2.1.toWitness_of_level0 hcz) (Nat.zero_le _)
      · exact hbt_o F0 F_cur hot1.2.1 (Nat.pos_of_ne_zero hcz)
    have hsp2 := m6p_btState_sparse hlen2 hw2 hot1.2.2.1 hot1.2.2.2.1 hot1.2.2.2.2.1
      hot1.2.2.2.2.2 hpres.1
    simpa only [show (2#64 : BitVec 64) = 2 from rfl] using hQ 2#64 st2 m2
      (fun _ => ⟨hsp2, by simp [st2, hcl2]⟩) (fun h => absurd h (by decide))
      hcv1s hfu1s (Or.inr (Or.inl rfl)) hm2
  · have hast1 : ast = 1#64 := by
      pt_clear_big
      rcases har_dom with rfl | rfl | rfl
      · exact absurd hc (by decide)
      · rfl
      · exact absurd rfl (by assumption)
    obtain ⟨hsp1, hlt1⟩ := har1 hast1; have hcl1_0 : st1.core.cur_level = 0 := by omega
    pt_steps_nogrp; c0_call hPropagate
    refine ⟨c, F0, F_cur, st1, R, rfl, hsp1.1, hsp1.2.1, hsp1.2.2.2.2.2, hm1, ?_⟩; dsimp only
    intro pr vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m2 hlen2 hw2 htr2 hperm2 hfu2 hpr_dom _
      hp1 _ _ hm2
    let st2 : FullState := { st1 with
      core := { st1.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
        trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
        unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
        wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
        confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { st1.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
    have hlm2 := m6p_litMarksClear_of_eq hsp1.2.2.1 rfl rfl
    have hnd2 := fullArenaVarsNodup_of_permEq hsp1.2.2.2.1 (s' := st2) hperm2
    have hext2 := m6p_extScratchOk_of_pres_eq (s' := st2) hsp1.2.2.2.2.1 rfl rfl hperm2.2.1
    have hdm2 := hsp1.2.2.2.2.2; have hfu2s := Nat.le_trans hfu2 hfu1s; pt_steps_nogrp
    · have hp_eq1 : pr = 1#64 := by pt_clear_big; exact hc
      have hunsat : F0.Unsat := level0_unsat_of_conflict_okW (s := st2) hw2 hcl1_0 (hp1 hp_eq1).2.2
      simpa only [show (20#64 : BitVec 64) = 20 from rfl] using hQ 20#64 st2 m2
        (fun h => by rcases h with h | h <;> exact absurd h (by decide))
        (fun _ => ⟨hunsat, F_cur,
          ⟨hlen2, FullProbeTransSpecs.FullWitnessInv.toOtfs hw2, hlm2, hnd2, hext2, hdm2⟩⟩)
        hcv1s hfu2s (Or.inr (Or.inr rfl)) hm2
    · -- `pp == 2ULL`: return `2ULL`
      simpa only [show (2#64 : BitVec 64) = 2 from rfl] using hQ 2#64 st2 m2
        (fun _ => ⟨⟨⟨hlen2, F_cur, hw2⟩, hlm2, hnd2, hext2, hdm2⟩, hcl1_0⟩)
        (fun h => absurd h (by decide)) hcv1s hfu2s (Or.inr (Or.inl rfl)) hm2
    · c0_call hFlushHbr
      refine ⟨c, F0, F_cur, st2, R, rfl, hlen2, hw2, hlm2.1, hnd2, hext2, hdm2, hcl1_0,
        m6p_hbrBufOkW_congr_vars hhbr1 rfl rfl, hm2, ?_⟩; dsimp only
      intro r st3 m3 hlen3 hw3 hmrk3 hnd3 hext3 hdm3 hcl3 hcv3 hfu3 hlm3 _ hr_dom hr20 hm3
      have hcv3s := hcv3.trans hcv1s; have hfu3s := Nat.le_trans hfu3 hfu2s
      have hcl3_clr : FullLitMarksClear c st3 :=
        ⟨hmrk3, fun l hl => by rw [hlm3]; exact hlm2.2 l hl⟩; pt_steps_nogrp
      exact hQ r st3 m3 (fun _ => ⟨⟨⟨hlen3, F_cur, hw3⟩, hcl3_clr, hnd3, hext3, hdm3⟩, hcl3⟩)
        (fun h20 => ⟨hr20 h20, F_cur, hlen3, FullProbeTransSpecs.FullWitnessInv.toOtfs hw3,
          hcl3_clr, hnd3, hext3, hdm3⟩) hcv3s hfu3s hr_dom hm3

private def m6p_addUnitsAndFlushExpr (h_arg pTmp bn_v hbr_v : Val i64) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun p =>
    Expr.let_ ⟨.cmp .ult i64, (.var p.fst, .var bn_v, ())⟩ fun p_lt =>
    Expr.jnz (.var p_lt.fst)
      (Expr.let_ ⟨.mul i64, (.var p.fst, .imm 4, ())⟩ fun p_off =>
       Expr.let_ ⟨.add i64, (.var pTmp, .var p_off.fst, ())⟩ fun p_addr =>
       Expr.load i32 (.var p_addr.fst) fun ld_u =>
       Expr.call "full_add_unit" (as := [i64, i32]) (bs := [.bool]) (.var h_arg, .var ld_u, ())
         fun p_ok => Expr.jnz (.var p_ok.fst)
         (Expr.let_ ⟨.add i64, (.var p.fst, .imm 1, ())⟩ fun p_next =>
          Expr.jump Js.fst (.var p_next.fst, ())) (Expr.ret (.imm 20, ())))
      (Expr.call "full_probe_flush_hbr" (as := [i64, i64]) (bs := [i64])
        (.var h_arg, .var hbr_v, ()) fun p_r => Expr.ret (.var p_r.fst, ())))
    Blocks.nil) (fun Js => Expr.jump Js.fst (.imm 0, ()))

private theorem m6p_addUnitsAndFlush_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st : FullState}
    {R : Mem 64 → Prop} {bn_v hbr_v : Val i64} {ml : Mem 64}
    (hFlushHbr : ∀ args m Q X, fullProbeFlushHbrSpec args m Q X →
      Γ "full_probe_flush_hbr" [i64, i64] [i64] args m Q X)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hsp : FullSparseInvW c F0 F_cur st) (hcl0 : st.core.cur_level = 0)
    (hhbr : FullHbrBufOkW F_cur st hbr_v.toNat) (hbones : M6pBonesUnitInv F_cur st bn_v.toNat)
    (hcv : st.core.cur_vars = s.core.cur_vars) (hfu : st.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm : (FullMem c st ⋆ R) ml)
    (hQ : ∀ r s' m',
      (r = 1#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 20#64 → F0.Unsat ∧ ∃ F_cur', FullOtfsInvW c F0 F_cur' s') →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (m6p_addUnitsAndFlushExpr c.hdr c.pTmp bn_v hbr_v) ml := by
  let loopInv : Tup Val [i64] → Mem 64 → Prop := fun (k_v, ()) mk =>
    k_v.toNat ≤ bn_v.toNat ∧ ∃ st_k : FullState, FullSparseInvW c F0 F_cur st_k ∧
      st_k.core.cur_level = 0 ∧ FullHbrBufOkW F_cur st_k hbr_v.toNat ∧
      M6pBonesUnitInv F_cur st_k bn_v.toNat ∧ st_k.core.cur_vars = s.core.cur_vars ∧
      st_k.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st_k ⋆ R) mk
  let meas : Tup Val [i64] → Mem 64 → Nat := fun (k_v, ()) _ => bn_v.toNat - k_v.toNat
  unfold m6p_addUnitsAndFlushExpr
  refine wp_loop_inv loopInv meas (fun Js hJs => ?_)
    (fun Js (k_v, ()) mk ⟨hk_le, st_k, hsp_k, hcl_k, hhbr_k, hbn_k, hcv_k, hfu_k, hm_k⟩ hJs => ?_)
  · pt_steps_nogrp
    exact hJs (0#64, ()) ml ⟨Nat.zero_le _, st, hsp, hcl0, hhbr, hbones, hcv, hfu, hm⟩
  · have hcl_ko := hsp_k.1.core_ok; have hmv := c.hmaxv; unfold dimacsBound at hmv
    have hcv_le := hcl_ko.cur_vars_le; pt_steps_nogrp
    · have hk_lt : k_v.toNat < bn_v.toNat := by pt_bound
      have hk_tmp : k_v.toNat < st_k.core.tmp.length := by
        have := hcl_ko.tmp_len_arr; have := hbn_k.1; omega
      obtain ⟨hu_lt, hu_ent⟩ := hbn_k.2 k_v.toNat hk_lt
      have hu_eq : (st_k.core.tmp[k_v.toNat]'hk_tmp).toNat =
          (st_k.core.tmp[k_v.toNat]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem hk_tmp, Option.getD_some]
      pt_steps_nogrp; c0_call hAddUnit
      refine ⟨c, F0, F_cur, st_k, R, rfl, hsp_k.1, hsp_k.2.1, fun _ => hu_eq ▸ hu_ent, hm_k, ?_⟩
      dsimp only; intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
        phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' ma hlen_a hw_a hcl_a hok_f _ hm_a
      let st_a : FullState := { st_k with
        core := { st_k.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', cur_level := cl',
          unassigned := unass', unflushed := unfl', inconsistent := inc' }
        scratch := { st_k.scratch with
          phases := phases', target_assigned := ta', best_assigned := ba',
          phases_target := pt', phases_best := pb', heap := hp', pos := ps',
          heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } }
      have hsp_a : FullSparseInvW c F0 F_cur st_a :=
        ⟨hlen_a, hw_a, m6p_litMarksClear_of_eq hsp_k.2.2.1 rfl rfl,
          fullArenaVarsNodup_of_arena_eq hsp_k.2.2.2.1 rfl rfl,
          m6p_extScratchOk_of_pres_eq hsp_k.2.2.2.2.1 rfl rfl rfl, hsp_k.2.2.2.2.2⟩
      pt_steps_nogrp
      · have hk1_eq := bv64_add1_toNat (f := k_v) (by have := hbn_k.1; omega)
        exact hJs (k_v + 1#64, ()) ma (by dsimp only [meas]; rw [hk1_eq]; omega)
          ⟨by rw [hk1_eq]; omega, st_a, hsp_a, hcl_a,
            m6p_hbrBufOkW_congr_vars hhbr_k rfl rfl, m6p_bonesUnitInv_congr hbn_k rfl rfl,
            hcv_k, hfu_k, hm_a⟩
      · have hok_ff : ok = false := by pt_clear_big; revert hc; cases ok <;> decide
        have hunsat : F0.Unsat := (hok_f (hu_eq ▸ hu_lt) hok_ff).1
        simpa only [show (20#64 : BitVec 64) = 20 from rfl] using hQ 20#64 st_a ma
          (fun h => by rcases h with h | h <;> exact absurd h (by decide))
          (fun _ => ⟨hunsat, F_cur,
            ⟨hlen_a, FullProbeTransSpecs.FullWitnessInv.toOtfs hw_a, hsp_a.2.2.1,
              hsp_a.2.2.2.1, hsp_a.2.2.2.2.1, hsp_a.2.2.2.2.2⟩⟩)
          hcv_k hfu_k (Or.inr (Or.inr rfl)) hm_a
    · c0_call hFlushHbr
      refine ⟨c, F0, F_cur, st_k, R, rfl, hsp_k.1, hsp_k.2.1, hsp_k.2.2.1.1, hsp_k.2.2.2.1,
        hsp_k.2.2.2.2.1, hsp_k.2.2.2.2.2, hcl_k, hhbr_k, hm_k, ?_⟩; dsimp only
      intro r st_f m_f hlen_f hw_f hmrk_f hnd_f hext_f hdm_f hcl_f hcv_f hfu_f hlm_f _
        hr_dom hr20 hm_f
      have hclr_f : FullLitMarksClear c st_f :=
        ⟨hmrk_f, fun l hl => by rw [hlm_f]; exact hsp_k.2.2.1.2 l hl⟩
      have hcv_fs := hcv_f.trans hcv_k; have hfu_fs := Nat.le_trans hfu_f hfu_k
      pt_steps_nogrp
      exact hQ r st_f m_f (fun _ => ⟨⟨⟨hlen_f, F_cur, hw_f⟩, hclr_f, hnd_f, hext_f, hdm_f⟩, hcl_f⟩)
        (fun h20 => ⟨hr20 h20, F_cur,
          ⟨hlen_f, FullProbeTransSpecs.FullWitnessInv.toOtfs hw_f, hclr_f, hnd_f, hext_f,
            hdm_f⟩⟩) hcv_fs hfu_fs hr_dom hm_f

private theorem m6p_collectBonesLoop_step {F_cur : List (List Nat)} {c : FullCfg} {lit : Nat}
    {st : FullState} {bn_v : BitVec 64} {tl_v : BitVec 32} (hlen : st.LengthsOk c)
    (hm_ent : M6pMarkedLitsEntailed F_cur lit st) (hbn_inv : M6pBonesUnitInv F_cur st bn_v.toNat)
    (hent_k : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, tl_v.toNat]))
    (hk_bd : bn_v.toNat < st.core.cur_vars) (htl_lt : tl_v.toNat < 2 * st.core.cur_vars)
    (hlm_ne : st.core.lit_mark[tl_v.toNat]?.getD 0#8 ≠ 0#8) :
    let st' : FullState :=
      { st with core := { st.core with tmp := st.core.tmp.set bn_v.toNat tl_v } }
    st'.LengthsOk c ∧ M6pBonesUnitInv F_cur st' (bn_v.toNat + 1) := by
  intro st'; have hcl := hlen.core_ok; have hcv_le := hcl.cur_vars_le
  have htmp_lt : bn_v.toNat < st.core.tmp.length := by rw [hcl.tmp_len_arr]; omega
  have hunit := m6p_resolve_pair_unit (hm_ent tl_v.toNat htl_lt hlm_ne) hent_k
  refine ⟨⟨{ hcl with tmp_len_arr := by simp [st', hcl.tmp_len_arr] }, hlen.scratch_ok⟩,
    by dsimp [st']; omega, fun i hi => ?_⟩
  dsimp only [st']; by_cases hbi : i = bn_v.toNat
  · subst hbi; rw [List.getElem?_set_self htmp_lt, Option.getD_some]; exact ⟨htl_lt, hunit⟩
  · rw [List.getElem?_set_ne (Ne.symm hbi)]; exact hbn_inv.2 i (by omega)

end LocalHelpers

/-! ## `full_probe_assume_pair_m6_wp` (Canonical `Full.fullProbeAssumePairSpec`) -/

section ProbeAssumePairM6Proof

theorem full_probe_assume_pair_m6_wp (Γ : Env)
    (hAssign : ∀ args m Q X, fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hProbeProp : ∀ args m Q X, fullProbePropExtSpec args m Q X →
      Γ "full_probe_prop" [i64] [i64] args m Q X)
    (hBacktrack : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAnalyze : ∀ args m Q X, fullAnalyze20Spec args m Q X →
      Γ "full_analyze" [i64] [i64] args m Q X)
    (hPropagate : ∀ args m Q X, fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hFlushHbr : ∀ args m Q X, fullProbeFlushHbrSpec args m Q X →
      Γ "full_probe_flush_hbr" [i64, i64] [i64] args m Q X)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullProbeAssumePairSpec args m Q X →
      Func.wp Γ full_probe_assume_pair_m6_body args m Q X := by
  rintro ⟨h_arg, lit, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp0, hcl0, hlit_lt, hun0, hm0, hQ⟩
  obtain ⟨⟨hlen0, F_cur, hw0⟩, hlm0, hnd0, hext0, hdm0⟩ := hsp0
  have hcl0_ok := hlen0.core_ok; have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv_le := hcl0_ok.cur_vars_le; have hpos_mv : 0 < c.max_vars := by omega
  have ht0 := hw0.trail_end_lt_of_unassigned hlit_lt hun0
  have hte_lt64 : s.core.trail_end < 2 ^ 64 := by omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by omega
  have hft_1 : 1 < s.core.frame_trail.length := by rw [hcl0_ok.frame_trail_len]; omega
  have hfd_1 : 1 < s.core.frame_dec.length := by rw [hcl0_ok.frame_dec_len]; omega
  have ht0_trunc := m6p_bv64_setWidth32 hte_lt32
  have h4eq : (4#64 : BitVec 64) = BitVec.ofNat 64 (4 * 1) := rfl
  unfold Func.wp full_probe_assume_pair_m6_body
  pt_steps_nogrp
  let st_d0 : FullState := { s with core := { s.core with tmp_cnt := 0 } }
  have hm_d0 : (FullMem c st_d0 ⋆ R) m := by simpa only [st_d0,
    show (BitVec.ofNat 64 0).toNat = 0 from rfl, show (0 : BitVec 64).toNat = 0 from rfl] using hm
  have hlen_d0 : st_d0.LengthsOk c := ⟨{ hcl0_ok with }, hlen0.scratch_ok⟩
  have hw_d0 := m6p_witnessInv_with_ctrl hw0 hlen_d0.core_ok
  refine wp_store_sep (by
    simpa only [Arg.val_var, h4eq, ht0_trunc] using FullArenaTactics.store_full_frame_trail
      (s := st_d0) (R := R) (i := 1) _ (by exact hft_1) hm_d0) fun m_ft h_ft => ?_
  pt_steps_nogrp
  refine wp_store_sep (by
    simpa only [Arg.val_var, h4eq] using FullArenaTactics.store_full_frame_dec
      (R := R) (i := 1) lit (by simpa [st_d0] using hfd_1) h_ft) fun m_fd h_fd => ?_
  pt_steps_nogrp; c0_call hAssign
  let s_d1 : FullState := { st_d0 with core := { st_d0.core with
    cur_level := 1
    frame_trail := st_d0.core.frame_trail.set 1 (BitVec.ofNat 32 st_d0.core.trail_end)
    frame_dec := st_d0.core.frame_dec.set 1 lit } }
  have hlen_d1 : s_d1.LengthsOk c := ⟨{ hlen_d0.core_ok with
    frame_trail_len := by simp [s_d1, hlen_d0.core_ok.frame_trail_len]
    frame_dec_len := by simp [s_d1, hlen_d0.core_ok.frame_dec_len] }, hlen_d0.scratch_ok⟩
  have hno_a1 : ¬ (s_d1.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s_d1.core.trail_end ∨
      s_d1.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
    intro hb; dsimp only [s_d1, st_d0] at hb
    rcases hb with h1 | h2 | h3; omega; omega; exact h3 hun0
  have hm_d1 : (FullMem c s_d1 ⋆ R) m := by
    simpa only [s_d1, st_d0, show (1 : BitVec 64).toNat = 1 from rfl,
      show (BitVec.ofNat 64 1).toNat = 1 from rfl] using hm
  refine ⟨c, s_d1, R, rfl, hlen_d1, by simp [s_d1], hm_d1, ?_⟩
  rw [ite_eq_right hno_a1]; dsimp only
  intro flags1 unass1 phases1 m_a1 hfll1 hph1 hm_a1
  obtain ⟨hlen_a1, hw_a1, hte_a1, htrl_a1, hlvl_a1, hrsn_a1⟩ :=
    m6p_level1Decide_preserves_witness hlen_d0 hw_d0 hcl0 hlit_lt hun0 hfll1 hph1
  let s_a1 := m6p_lvl1DecState st_d0 lit flags1 phases1 unass1
  have hm_a1' : (FullMem c s_a1 ⋆ R) m_a1 := by
    simpa only [m6p_lvl1DecState, s_a1, s_d1, st_d0, ite_eq_right (by decide : (1 : Nat) ≠ 0),
      show (4294967295 : BitVec 32) = 0xFFFFFFFF#32 from rfl] using hm_a1
  pt_steps_nogrp; c0_call hProbeProp
  refine ⟨c, F0, F_cur, s_a1, R, rfl, hlen_a1, hw_a1, m6p_mrkZero_of_eq hlm0.1 rfl,
    fullArenaVarsNodup_of_arena_eq hnd0 rfl rfl, m6p_extScratchOk_of_pres_eq hext0 rfl rfl rfl,
    hdm0, rfl, m6p_hbrBufOkW_zero F_cur s_a1, hm_a1', ?_⟩; dsimp only
  intro pr s_pp m_pp hlen_pp hw_pp hmrk_pp hnd_pp hext_pp hdm_pp hcl1_pp hcv_pp hfu_pp
    hlm_pp hws1_pp htr_pp hhbr_pp hpr_dom hpr1 _ hm_pp
  have hfu_pps : s_pp.core.fuel.toNat ≤ s.core.fuel.toNat := hfu_pp
  have hlm_pp_clr : FullLitMarksClear c s_pp :=
    ⟨hmrk_pp, fun l hl => by rw [hlm_pp]; exact hlm0.2 l hl⟩
  have hsp_pp : FullSparseInvW c F0 F_cur s_pp :=
    ⟨hlen_pp, hw_pp, hlm_pp_clr, hnd_pp, hext_pp, hdm_pp⟩
  have hhbr_pp' : FullHbrBufOkW F_cur s_pp (BitVec.ofNat 64 s_pp.core.tmp_cnt).toNat := by
    have := hhbr_pp.1; have := hlen_pp.core_ok.cur_vars_le; rwa [bv64_ofNat_toNat (by omega)]
  pt_steps_nogrp
  · c0_call hBacktrack
    refine ⟨c, s_pp, R, rfl, hlen_pp, by rw [hcl1_pp]; decide, fun _ => hpos_mv,
      hw_pp.trail_lits_lt, hm_pp, ?_⟩; dsimp only
    intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt hlen_bt _ _ hcl_bt hpres
      _ _ _ hbt_w _ hm_bt
    let st_bt := m6p_btState s_pp vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc'
    have hsp_bt := m6p_btState_sparse hlen_bt (hbt_w F0 F_cur hw_pp (Nat.zero_le _))
      hlm_pp_clr hnd_pp hext_pp hdm_pp hpres.1
    pt_steps_nogrp
    simpa only [show (2#64 : BitVec 64) = 2 from rfl] using hQ 2#64 st_bt m_bt
      (fun _ => ⟨hsp_bt, by simp [st_bt, hcl_bt]⟩) (fun h => absurd h (by decide))
      hcv_pp hfu_pps (Or.inr (Or.inl rfl)) hm_bt
  · have hpr_eq : pr = 1#64 := by pt_clear_big; exact hc
    exact m6p_analyzeBranch_wp hAnalyze hBacktrack hPropagate hFlushHbr hsp_pp (hpr1 hpr_eq) hcl1_pp
      hhbr_pp' hcv_pp hfu_pps hpos_mv hm_pp hQ
  · obtain ⟨hpp_te, hent_p1⟩ :=
      m6p_level1Decide_after_prop hw_pp hcl1_pp hte_a1 htrl_a1 hlvl_a1 hrsn_a1 htr_pp
    have hte_pp_le := hlen_pp.core_ok.trail_end_le; have hcv_pp_le := hlen_pp.core_ok.cur_vars_le
    let saveInv : Tup Val [i64, i64] → Mem 64 → Prop := fun (sn_v, k_v, ()) ms =>
      s.core.trail_end ≤ k_v.toNat ∧ k_v.toNat ≤ s_pp.core.trail_end ∧
      sn_v.toNat = k_v.toNat - s.core.trail_end ∧
      ∃ lm ws1, lm.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
        let st_s : FullState := { s_pp with core := { s_pp.core with lit_mark := lm }
                                            scratch := { s_pp.scratch with work_stk1 := ws1 } }
        M6pSavedMarksInv c st_s sn_v.toNat ∧ M6pMarkedLitsEntailed F_cur lit.toNat st_s ∧
        (FullMem c st_s ⋆ R) ms
    let smeas : Tup Val [i64, i64] → Mem 64 → Nat := fun (_, k_v, ()) _ =>
      s_pp.core.trail_end - k_v.toNat
    refine wp_loop_inv saveInv smeas ?_ ?_
    · intro Js_sv hJs_sv; pt_steps_nogrp
      exact hJs_sv (0#64, BitVec.ofNat 64 s.core.trail_end, ()) m_pp
        ⟨by rw [bv64_ofNat_toNat hte_lt64]; exact Nat.le_refl _,
          by rw [bv64_ofNat_toNat hte_lt64]; exact Nat.le_of_lt hpp_te,
          by simp [bv64_ofNat_toNat hte_lt64], s_pp.core.lit_mark, s_pp.scratch.work_stk1,
          hlen_pp.core_ok.lit_mark_len, hlen_pp.scratch_ok.work_stk1_len,
          ⟨Nat.zero_le _, fun _ hi => by simp at hi,
            fun l hl hne => absurd (hlm_pp_clr.2 l hl) hne⟩,
          fun l hl hne => by dsimp only at hl; exact absurd (hlm_pp_clr.2 l (by omega)) hne, hm_pp⟩
    · rintro Js_sv ⟨sn_v, k_v, ⟨⟩⟩ ms
        ⟨hk_ge, hk_le, hsn_eq, lm, ws1, hlm_l, hws1_l, hsav_s, hment_s, hm_s⟩ ih
      let st_s : FullState := { s_pp with core := { s_pp.core with lit_mark := lm }
                                          scratch := { s_pp.scratch with work_stk1 := ws1 } }
      have hlen_s : st_s.LengthsOk c :=
        ⟨{ hlen_pp.core_ok with lit_mark_len := hlm_l },
         { hlen_pp.scratch_ok with work_stk1_len := hws1_l }⟩
      have hw_s := m6p_witnessInv_with_ctrl hw_pp hlen_s.core_ok
      refine wp_unroll_group fun J_exit hJ_exit => ?_
      have h_exit_wp : ∀ _ : k_v.toNat = s_pp.core.trail_end,
          wp Γ Q X (Expr.jump J_exit ()) ms := by
        intro _; pt_steps_nogrp; clear hJ_exit ih; c0_call hBacktrack
        refine ⟨c, st_s, R, rfl, hlen_s, by simp [st_s, hcl1_pp], fun _ => hpos_mv,
          hw_s.trail_lits_lt, hm_s, ?_⟩; dsimp only
        intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt hlen_bt _ _ hcl_bt hpres
          _ _ _ hbt_w _ hm_bt
        let st_bt := m6p_btState st_s vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc'
        have hhbr_bt : FullHbrBufOkW F_cur st_bt (BitVec.ofNat 64 s_pp.core.tmp_cnt).toNat := by
          have := hhbr_pp.1; rw [bv64_ofNat_toNat (by omega)]
          exact m6p_hbrBufOkW_congr_vars hhbr_pp rfl hpres.2.2.1
        pt_steps_nogrp; c0_call hFlushHbr
        refine ⟨c, F0, F_cur, st_bt, R, rfl, hlen_bt, hbt_w F0 F_cur hw_s (Nat.zero_le _),
          m6p_mrkZero_of_eq hmrk_pp rfl, fullArenaVarsNodup_of_arena_eq hnd_pp rfl rfl,
          m6p_extScratchOk_of_pres_eq hext_pp hpres.1.1 hpres.1.2 rfl, hdm_pp,
          by simp [st_bt, hcl_bt], hhbr_bt, hm_bt, ?_⟩; dsimp only
        intro fh st_fh m_fh hlen_fh hw_fh hmrk_fh hnd_fh hext_fh hdm_fh hcl_fh hcv_fh hfu_fh
          hlm_fh hws1_fh hfh_dom hfh20 hm_fh
        have hcv_fhs := hcv_fh.trans hcv_pp; have hfu_fhs := Nat.le_trans hfu_fh hfu_pps
        have hsav_fh := m6p_savedMarksInv_congr
          (m6p_savedMarksInv_congr (s' := st_bt) hsav_s rfl rfl (by exact hpres.2.1))
          hcv_fh hlm_fh hws1_fh
        have hment_fh := m6p_markedLitsEntailed_congr
          (m6p_markedLitsEntailed_congr (s' := st_bt) hment_s rfl rfl) hcv_fh hlm_fh
        pt_steps_nogrp
        · refine m6p_clearLmLoop_wp hlen_fh hmrk_fh hsav_fh hm_fh fun lm_c m_c hlm_c hlen_c hclr_c
              hm_c => by
            pt_steps_nogrp
            have hsp_c := m6p_sparseInvW_set_litMark hlen_c hw_fh hclr_c hnd_fh hext_fh hdm_fh
            let st_c : FullState := { st_fh with core := { st_fh.core with lit_mark := lm_c } }
            exact hQ fh st_c m_c (fun _ => ⟨fullSparseInvW_toSparse hsp_c, hcl_fh⟩)
              (fun h20 => ⟨hfh20 h20, F_cur,
                ⟨hlen_c, FullProbeTransSpecs.FullWitnessInv.toOtfs hsp_c.2.1, hclr_c,
                  hsp_c.2.2.2.1, hsp_c.2.2.2.2.1, hdm_fh⟩⟩) hcv_fhs hfu_fhs hfh_dom hm_c
        · have hcv_fhl : st_fh.core.cur_vars = s_pp.core.cur_vars := hcv_fh
          let postPhase2Inv : Tup Val [i64, i64] → Mem 64 → Prop := fun (_u, bn_v, ()) mj =>
            ∃ st_p : FullState, st_p.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_p.core ∧
              FullMrkZero c st_p ∧ FullArenaVarsNodup st_p ∧ FullExtScratchOk c st_p ∧
              st_p.core.dense_mode = 0#64 ∧ st_p.core.cur_level = 0 ∧
              M6pSavedMarksInv c st_p sn_v.toNat ∧ M6pBonesUnitInv F_cur st_p bn_v.toNat ∧
              FullHbrBufOkW F_cur st_p st_p.core.tmp_cnt ∧
              st_p.core.cur_vars = s.core.cur_vars ∧ st_p.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c st_p ⋆ R) mj
          refine wp_join_group postPhase2Inv (fun _ (_u, bn_v, ()) mj ⟨st_p, hlen_p, hw_p,
              hmrk_p, hnd_p, hext_p, hdm_p, hcl_p, hsav_p, hbn_p, hhbr_p, hcv_p, hfu_p, hm_p⟩ => by
            pt_steps_nogrp
            refine m6p_clearLmLoop_wp hlen_p hmrk_p hsav_p hm_p fun lm_c m_c hlm_c hlen_c hclr_c
                hm_c => by
              have hsp_c := m6p_sparseInvW_set_litMark hlen_c hw_p hclr_c hnd_p hext_p hdm_p
              let st_c : FullState := { st_p with core := { st_p.core with lit_mark := lm_c } }
              have hhbr_c : FullHbrBufOkW F_cur st_c (BitVec.ofNat 64 st_p.core.tmp_cnt).toNat := by
                have htc_p : st_p.core.tmp_cnt < 2 ^ 64 := by
                  have := hhbr_p.1; have := hlen_p.core_ok.cur_vars_le; omega
                rw [bv64_ofNat_toNat htc_p]; exact m6p_hbrBufOkW_congr_vars hhbr_p rfl rfl
              exact m6p_addUnitsAndFlush_wp (X := X) (hbr_v := BitVec.ofNat 64 st_p.core.tmp_cnt)
                hFlushHbr hAddUnit hsp_c hcl_p hhbr_c (m6p_bonesUnitInv_congr hbn_p rfl rfl)
                hcv_p hfu_p hm_c hQ) (fun Jpost hJpost => ?_)
          have hnot_lt_fh : (lit ^^^ 1#32).toNat < 2 * st_fh.core.cur_vars := by
            rw [hcv_fhl, hcv_pp]; exact litNeg_lt_two_mul hlit_lt
          have hnot_v_fh : (lit ^^^ 1#32).toNat < st_fh.core.vals.length := by
            rw [hlen_fh.core_ok.vals_len]; have := hlen_fh.core_ok.cur_vars_le; omega
          let st_p0 : FullState := { st_fh with core := { st_fh.core with tmp_cnt := 0 } }
          have hlen_p0 : st_p0.LengthsOk c := ⟨{ hlen_fh.core_ok with }, hlen_fh.scratch_ok⟩
          have hw_p0 := m6p_witnessInv_with_ctrl hw_fh hlen_p0.core_ok
          have hmrk_p0 := m6p_mrkZero_of_eq hmrk_fh rfl
          have hnd_p0 := fullArenaVarsNodup_of_arena_eq hnd_fh rfl rfl
          have hext_p0 := m6p_extScratchOk_of_pres_eq hext_fh rfl rfl rfl
          have hsav_p0 := m6p_savedMarksInv_congr hsav_fh rfl rfl rfl
          have hment_p0 := m6p_markedLitsEntailed_congr hment_fh rfl rfl
          pt_steps_nogrp
          · have hxor : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := bv32_toNat_xor1 lit
            have hun2_raw : (st_p0.core.vals[lit.toNat ^^^ 1]'(by
                rw [← hxor]; exact hnot_v_fh)).signExtend 32 = 0#32 := by
              pt_clear_big
              simpa only [st_p0, show (BitVec.truncate 8 (0 : BitVec 32)).signExtend 32 =
                0#32 from rfl] using hc
            have hun2 : st_p0.core.vals[(lit ^^^ 1#32).toNat]?.getD 0#8 = 0#8 :=
              m6p_vals_eq_0_of_sext hnot_v_fh (by simpa only [hxor] using hun2_raw)
            have ht1_lt := hw_p0.trail_end_lt_of_unassigned hnot_lt_fh hun2
            have hcv_p0_le := hlen_p0.core_ok.cur_vars_le
            dsimp only [st_p0] at ht1_lt hcv_p0_le
            have ht1_64 : st_p0.core.trail_end < 2 ^ 64 := by dsimp only [st_p0]; omega
            have ht1_32 : st_p0.core.trail_end < 2 ^ 32 := by dsimp only [st_p0]; omega
            have ht1_trunc := m6p_bv64_setWidth32 ht1_32
            have ht1_trunc_fh : (BitVec.ofNat 64 st_fh.core.trail_end).setWidth 32 =
                BitVec.ofNat 32 st_fh.core.trail_end := ht1_trunc
            have hft1_p0 : 1 < st_p0.core.frame_trail.length := by
              rw [hlen_p0.core_ok.frame_trail_len]; omega
            have hfd1_p0 : 1 < st_p0.core.frame_dec.length := by
              rw [hlen_p0.core_ok.frame_dec_len]; omega
            have hm_p0' : (FullMem c st_p0 ⋆ R) m := by
              simpa only [st_p0, show (BitVec.ofNat 64 0).toNat = 0 from rfl,
                show (0 : BitVec 64).toNat = 0 from rfl] using hm
            pt_steps_nogrp
            refine wp_store_sep (by
              simpa only [Arg.val_var, h4eq, ht1_trunc] using
                FullArenaTactics.store_full_frame_trail (s := st_p0) (R := R) (i := 1) _
                  (by exact hft1_p0) hm_p0') fun m_ft2 h_ft2 => ?_
            pt_steps_nogrp
            refine wp_store_sep (by
              simpa only [Arg.val_var, h4eq,
                  show lit ^^^ (1 : BitVec 32) = lit ^^^ 1#32 from rfl] using
                FullArenaTactics.store_full_frame_dec (R := R) (i := 1) (lit ^^^ 1#32)
                  (by simpa [st_p0] using hfd1_p0) h_ft2) fun m_fd2 h_fd2 => ?_
            pt_steps_nogrp; c0_call hAssign
            let s_d2 : FullState := { st_p0 with core := { st_p0.core with
              cur_level := 1
              frame_trail := st_p0.core.frame_trail.set 1 (BitVec.ofNat 32 st_p0.core.trail_end)
              frame_dec := st_p0.core.frame_dec.set 1 (lit ^^^ 1#32) } }
            have hlen_d2 : s_d2.LengthsOk c := ⟨{ hlen_p0.core_ok with
              frame_trail_len := by simp [s_d2, hlen_p0.core_ok.frame_trail_len]
              frame_dec_len := by simp [s_d2, hlen_p0.core_ok.frame_dec_len] }, hlen_p0.scratch_ok⟩
            have hno_a2 : ¬ (s_d2.core.cur_vars ≤ (lit ^^^ 1#32).toNat / 2 ∨
                c.max_vars ≤ s_d2.core.trail_end ∨
                s_d2.core.vals[(lit ^^^ 1#32).toNat]?.getD 0#8 ≠ 0#8) := by
              intro hb; dsimp only [s_d2, st_p0] at hb
              rcases hb with h1 | h2 | h3; omega; omega; exact h3 hun2
            have hm_d2 : (FullMem c s_d2 ⋆ R) m := by
              simpa only [s_d2, st_p0, ht1_trunc_fh, show (1 : BitVec 64).toNat = 1 from rfl,
                show (BitVec.ofNat 64 1).toNat = 1 from rfl] using hm
            refine ⟨c, s_d2, R, rfl, hlen_d2, by simp [s_d2], hm_d2, ?_⟩
            rw [show lit ^^^ (1 : BitVec 32) = lit ^^^ 1#32 from rfl, ite_eq_right hno_a2]
            dsimp only; intro flags2 unass2 phases2 m_a2 hfll2 hph2 hm_a2
            obtain ⟨hlen_a2, hw_a2, hte_a2, htrl_a2, hlvl_a2, hrsn_a2⟩ :=
              m6p_level1Decide_preserves_witness hlen_p0 hw_p0 hcl_fh hnot_lt_fh hun2 hfll2 hph2
            let s_a2 := m6p_lvl1DecState st_p0 (lit ^^^ 1#32) flags2 phases2 unass2
            have hm_a2' : (FullMem c s_a2 ⋆ R) m_a2 := by
              simpa only [m6p_lvl1DecState, s_a2, s_d2, ite_eq_right (by decide : (1 : Nat) ≠ 0),
                show lit ^^^ (1 : BitVec 32) = lit ^^^ 1#32 from rfl,
                show (4294967295 : BitVec 32) = 0xFFFFFFFF#32 from rfl] using hm_a2
            pt_steps_nogrp; c0_call hProbeProp
            refine ⟨c, F0, F_cur, s_a2, R, rfl, hlen_a2, hw_a2,
              m6p_mrkZero_of_eq hmrk_p0 rfl, fullArenaVarsNodup_of_arena_eq hnd_p0 rfl rfl,
              m6p_extScratchOk_of_pres_eq hext_p0 rfl rfl rfl, hdm_fh, rfl,
              m6p_hbrBufOkW_zero F_cur s_a2, hm_a2', ?_⟩; dsimp only
            intro pr2 s_p2 m_p2 hlen_p2 hw_p2 hmrk_p2 hnd_p2 hext_p2 hdm_p2 hcl1_p2 hcv_p2 hfu_p2
              hlm_p2 hws1_p2 htr_p2 hhbr_p2 _ hpr2_1 _ hm_p2
            have hcv_p2s := hcv_p2.trans hcv_fhs; have hfu_p2s := Nat.le_trans hfu_p2 hfu_fhs
            have hsav_p2 := m6p_savedMarksInv_congr hsav_p0 hcv_p2 hlm_p2 hws1_p2
            have hment_p2 := m6p_markedLitsEntailed_congr hment_p0 hcv_p2 hlm_p2
            have hhbr_p2' : FullHbrBufOkW F_cur s_p2 (BitVec.ofNat 64 s_p2.core.tmp_cnt).toNat := by
              have := hhbr_p2.1; have := hlen_p2.core_ok.cur_vars_le
              rwa [bv64_ofNat_toNat (by omega)]
            pt_steps_nogrp
            · -- `pr2 == 2ULL`: clear `lit_mark`, backtrack to 0, return `2ULL`
              refine m6p_clearLmLoop_wp hlen_p2 hmrk_p2 hsav_p2 hm_p2
                fun lm_c m_c hlm_c hlen_c hclr_c hm_c => ?_
              let st_c : FullState := { s_p2 with core := { s_p2.core with lit_mark := lm_c } }
              have hw_c := m6p_witnessInv_with_ctrl hw_p2 hlen_c.core_ok
              pt_steps_nogrp; c0_call hBacktrack
              refine ⟨c, st_c, R, rfl, hlen_c, by simp [st_c, hcl1_p2], fun _ => hpos_mv,
                hw_c.trail_lits_lt, hm_c, ?_⟩; dsimp only
              intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt hlen_bt _ _ hcl_bt
                hpres _ _ _ hbt_w _ hm_bt
              let st_bt := m6p_btState st_c vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc'
              have hsp_bt := m6p_btState_sparse hlen_bt (hbt_w F0 F_cur hw_c (Nat.zero_le _))
                hclr_c (fullArenaVarsNodup_of_arena_eq hnd_p2 rfl rfl)
                (m6p_extScratchOk_of_pres_eq hext_p2 rfl rfl rfl) hdm_p2 hpres.1
              pt_steps_nogrp
              simpa only [show (2#64 : BitVec 64) = 2 from rfl] using hQ 2#64 st_bt m_bt
                (fun _ => ⟨hsp_bt, by simp [st_bt, hcl_bt]⟩) (fun h => absurd h (by decide))
                hcv_p2s hfu_p2s (Or.inr (Or.inl rfl)) hm_bt
            · have hpr2_eq : pr2 = 1#64 := by pt_clear_big; exact hc
              refine m6p_clearLmLoop_wp hlen_p2 hmrk_p2 hsav_p2 hm_p2
                fun lm_c m_c hlm_c hlen_c hclr_c hm_c => ?_
              have hsp_c := m6p_sparseInvW_set_litMark hlen_c hw_p2 hclr_c hnd_p2 hext_p2 hdm_p2
              exact m6p_analyzeBranch_wp hAnalyze hBacktrack hPropagate hFlushHbr hsp_c
                (hpr2_1 hpr2_eq) hcl1_p2 hhbr_p2' hcv_p2s hfu_p2s hpos_mv hm_c hQ
            · let j1Inv : Tup Val [i64, i64] → Mem 64 → Prop := fun (_u, bn_v, ()) mj =>
                ∃ st_j : FullState, st_j.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_j.core ∧
                  FullMrkZero c st_j ∧ FullArenaVarsNodup st_j ∧ FullExtScratchOk c st_j ∧
                  st_j.core.dense_mode = 0#64 ∧ st_j.core.cur_level = 1 ∧
                  M6pSavedMarksInv c st_j sn_v.toNat ∧ M6pBonesUnitInv F_cur st_j bn_v.toNat ∧
                  FullHbrBufOkW F_cur st_j s_p2.core.tmp_cnt ∧
                  st_j.core.cur_vars = s.core.cur_vars ∧
                  st_j.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st_j ⋆ R) mj
              refine wp_join_group j1Inv (fun _ (_u, bn_v, ()) mj ⟨st_j, hlen_j, hw_j, hmrk_j,
                  hnd_j, hext_j, hdm_j, hcl1_j, hsav_j, hbn_j, hhbr_j, hcv_j, hfu_j, hm_j⟩ => by
                pt_steps_nogrp; c0_call hBacktrack
                refine ⟨c, st_j, R, rfl, hlen_j, by rw [hcl1_j]; decide, fun _ => hpos_mv,
                  hw_j.trail_lits_lt, hm_j, ?_⟩; dsimp only
                intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt hlen_bt _ _ hcl_bt
                  hpres _ _ _ hbt_w _ hm_bt
                let st_bt := m6p_btState st_j vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc'
                have hw_bt := hbt_w F0 F_cur hw_j (Nat.zero_le _)
                have htc_lt64 : s_p2.core.tmp_cnt < 2 ^ 64 := by
                  have := hhbr_p2.1; have := hlen_p2.core_ok.cur_vars_le; omega
                pt_steps_nogrp
                let st_bt' : FullState :=
                  { st_bt with core := { st_bt.core with tmp_cnt := s_p2.core.tmp_cnt } }
                have hlen_bt' : st_bt'.LengthsOk c := ⟨{ hlen_bt.core_ok with }, hlen_bt.scratch_ok⟩
                have hw_bt' := m6p_witnessInv_with_ctrl (s := st_bt) hw_bt hlen_bt'.core_ok
                exact hJpost (_u, bn_v, ()) m ⟨st_bt', hlen_bt', hw_bt',
                  m6p_mrkZero_of_eq hmrk_j rfl, fullArenaVarsNodup_of_arena_eq hnd_j rfl rfl,
                  m6p_extScratchOk_of_pres_eq hext_j hpres.1.1 hpres.1.2 rfl, hdm_j,
                  by simp [st_bt', st_bt, hcl_bt],
                  m6p_savedMarksInv_congr (s' := st_bt') hsav_j rfl rfl (by exact hpres.2.1),
                  m6p_bonesUnitInv_congr hbn_j rfl rfl,
                  m6p_hbrBufOkW_congr_vars hhbr_j rfl hpres.2.2.1, hcv_j, hfu_j,
                  by simpa only [st_bt', bv64_ofNat_toNat htc_lt64] using hm⟩) (fun Js1 hJs1 => ?_)
              pt_steps_nogrp
              · obtain ⟨hp2_te, hent_p2_raw⟩ := m6p_level1Decide_after_prop hw_p2 hcl1_p2
                  hte_a2 htrl_a2 hlvl_a2 hrsn_a2 htr_p2
                have hent_p2 : ∀ idx < s_p2.core.trail_end, (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [lit.toNat, (s_p2.core.trl[idx]?.getD 0#32).toNat]) :=
                  fun idx hi => by
                    have h := hent_p2_raw idx hi; rw [bv32_toNat_xor1] at h
                    rwa [show lit.toNat ^^^ 1 ^^^ 1 = litNeg (litNeg lit.toNat) from rfl,
                      litNeg_litNeg] at h
                let boneInv : Tup Val [i64, i64] → Mem 64 → Prop := fun (k2_v, bn_v, ()) mk =>
                  k2_v.toNat ≤ s_p2.core.trail_end ∧ bn_v.toNat ≤ s_p2.core.cur_vars ∧
                  ∃ tmp', tmp'.length = c.max_vars ∧
                    let st_b : FullState := { s_p2 with core := { s_p2.core with tmp := tmp' } }
                    st_b.LengthsOk c ∧ M6pBonesUnitInv F_cur st_b bn_v.toNat ∧
                    (FullMem c st_b ⋆ R) mk
                let bmeas : Tup Val [i64, i64] → Mem 64 → Nat :=
                  fun (k2_v, _, ()) _ => s_p2.core.trail_end - k2_v.toNat
                refine wp_loop_inv boneInv bmeas (fun Js2 hJs2 => ?_)
                  (fun Js2 (k2_v, bn_v, ()) mk ⟨hk2_le, hbn_le, tmp', htmp_l, hlen_b, hbn_b, hm_b⟩
                    hJs2 => ?_)
                · pt_steps_nogrp
                  exact hJs2 (BitVec.ofNat 64 st_p0.core.trail_end, 0#64, ()) m_p2
                    ⟨by rw [bv64_ofNat_toNat ht1_64]; exact Nat.le_of_lt hp2_te, Nat.zero_le _,
                      s_p2.core.tmp, hlen_p2.core_ok.tmp_len_arr, hlen_p2,
                      ⟨Nat.zero_le _, fun _ hi => by simp at hi⟩, hm_p2⟩
                · let st_b : FullState := { s_p2 with core := { s_p2.core with tmp := tmp' } }
                  have hcl_b := hlen_b.core_ok; have hcv_p2_le := hlen_p2.core_ok.cur_vars_le
                  have hte_p2_64 : s_p2.core.trail_end < 2 ^ 64 := by
                    have := hlen_p2.core_ok.trail_end_le; omega
                  have hcv_p2_64 : s_p2.core.cur_vars < 2 ^ 64 := by omega
                  have hfin : j1Inv (k2_v, bn_v, ()) mk := ⟨st_b, hlen_b,
                    m6p_witnessInv_with_ctrl hw_p2 hcl_b,
                    m6p_mrkZero_of_eq hmrk_p2 rfl, fullArenaVarsNodup_of_arena_eq hnd_p2 rfl rfl,
                    m6p_extScratchOk_of_pres_eq hext_p2 rfl rfl rfl, hdm_p2, hcl1_p2,
                    m6p_savedMarksInv_congr hsav_p2 rfl rfl rfl, hbn_b,
                    m6p_hbrBufOkW_congr_vars hhbr_p2 rfl rfl, hcv_p2s, hfu_p2s, hm_b⟩
                  pt_steps_nogrp
                  · have hk2_lt : k2_v.toNat < s_p2.core.trail_end := by pt_bound
                    have hk2_trl : k2_v.toNat < st_b.core.trl.length := by
                      rw [hcl_b.trl_len]; have := hlen_p2.core_ok.trail_end_le; omega
                    have hbn_lt : bn_v.toNat < s_p2.core.cur_vars := by
                      rw [hcv_p2s]; have hcv_s64 : s.core.cur_vars < 2 ^ 64 := by omega
                      pt_clear_big; rw [Nat.mod_eq_of_lt hcv_s64] at hc; exact hc
                    pt_steps_nogrp
                    let tl_v := st_b.core.trl[k2_v.toNat]'hk2_trl
                    have htl_lt : tl_v.toNat < 2 * s_p2.core.cur_vars := by
                      simpa [tl_v, st_b, List.getElem?_eq_getElem hk2_trl] using
                        hw_p2.trail_lits_lt k2_v.toNat hk2_lt
                    have htl_lm : (tl_v.setWidth 64).toNat < st_b.core.lit_mark.length := by
                      rw [bv_c0_zext32_64, hcl_b.lit_mark_len]; omega
                    have hbn_tmp : bn_v.toNat < st_b.core.tmp.length := by
                      rw [hcl_b.tmp_len_arr]; omega
                    have hent_k := hent_p2 k2_v.toNat hk2_lt
                    rw [List.getElem?_eq_getElem hk2_trl, Option.getD_some] at hent_k
                    let bnStepInv : Tup Val [i64] → Mem 64 → Prop := fun (bn_n, ()) mb =>
                      bn_n.toNat ≤ s_p2.core.cur_vars ∧ ∃ tmp_n, tmp_n.length = c.max_vars ∧
                        let st_n : FullState :=
                          { s_p2 with core := { s_p2.core with tmp := tmp_n } }
                        st_n.LengthsOk c ∧ M6pBonesUnitInv F_cur st_n bn_n.toNat ∧
                        (FullMem c st_n ⋆ R) mb
                    refine wp_join_group bnStepInv (fun _ (bn_n, ()) mb
                        ⟨hbn_n, tmp_n, htmp_n, hlen_n, hbu_n, hm_n⟩ => by
                      have hk2_s := bv64_add1_toNat (by omega : k2_v.toNat + 1 < 2 ^ 64)
                      pt_steps_nogrp
                      exact hJs2 (k2_v + 1#64, bn_n, ()) mb
                        (by dsimp only [bmeas]; rw [hk2_s]; omega)
                        ⟨by rw [hk2_s]; omega, hbn_n, tmp_n, htmp_n, hlen_n, hbu_n, hm_n⟩)
                      (fun Js3 hJs3 => ?_)
                    pt_steps_nogrp
                    · have hne0 : st_b.core.lit_mark[tl_v.toNat]?.getD 0#8 ≠ 0#8 := by
                        rw [List.getElem?_eq_getElem (by rw [hcl_b.lit_mark_len]; omega),
                          Option.getD_some]
                        intro hz; apply hc; simp only [tl_v] at hz ⊢; rw [hz]; rfl
                      obtain ⟨hlen_st, hbu_st⟩ := m6p_collectBonesLoop_step hlen_b
                        (m6p_markedLitsEntailed_congr hment_p2 rfl rfl) hbn_b hent_k hbn_lt
                        htl_lt hne0
                      have hbn1_eq := bv64_add1_toNat (by omega : bn_v.toNat + 1 < 2 ^ 64)
                      exact hJs3 (bn_v + 1#64, ()) m
                        ⟨by rw [hbn1_eq]; omega, tmp'.set bn_v.toNat tl_v,
                          by simp [htmp_l], hlen_st, by rw [hbn1_eq]; exact hbu_st, hm⟩
                    · exact hJs3 (bn_v, ()) mk ⟨hbn_le, tmp', htmp_l, hlen_b, hbn_b, hm_b⟩
                  all_goals exact hJs1 (k2_v, bn_v, ()) mk hfin
              · exact hJs1 (k_v, 0#64, ()) m_p2
                  ⟨s_p2, hlen_p2, hw_p2, hmrk_p2, hnd_p2, hext_p2, hdm_p2, hcl1_p2, hsav_p2,
                    ⟨Nat.zero_le _, fun _ hi => by simp at hi⟩, hhbr_p2, hcv_p2s, hfu_p2s, hm_p2⟩
          · exact hJpost (k_v, 0#64, ()) m
              ⟨st_p0, hlen_p0, hw_p0, hmrk_p0, hnd_p0, hext_p0, hdm_fh, hcl_fh, hsav_p0,
                ⟨Nat.zero_le _, fun _ hi => by simp at hi⟩, m6p_hbrBufOkW_zero F_cur st_p0,
                hcv_fhs, hfu_fhs, by
                  simpa only [st_p0, show (BitVec.ofNat 64 0).toNat = 0 from rfl,
                    show (0 : BitVec 64).toNat = 0 from rfl] using hm⟩
      clear hJ_exit; pt_steps_nogrp
      · have hk_lt : k_v.toNat < s_pp.core.trail_end := by pt_bound
        have hcv_s_eq : s_pp.core.cur_vars = s.core.cur_vars := hcv_pp
        have hsn_lt : sn_v.toNat < s.core.cur_vars := by omega
        have hsn1_le : sn_v.toNat + 1 ≤ s_pp.core.cur_vars := by omega
        have hk_trl : k_v.toNat < st_s.core.trl.length := by rw [hlen_s.core_ok.trl_len]; omega
        let tl_v := st_s.core.trl[k_v.toNat]'hk_trl
        have htl_lt : tl_v.toNat < 2 * s_pp.core.cur_vars := by
          simpa [tl_v, st_s, List.getElem?_eq_getElem hk_trl] using
            hw_pp.trail_lits_lt k_v.toNat hk_lt
        have htl_lm : (tl_v.setWidth 64).toNat < st_s.core.lit_mark.length := by
          rw [bv_c0_zext32_64, hlen_s.core_ok.lit_mark_len]; omega
        have hsn_ws : sn_v.toNat < st_s.scratch.work_stk1.length := by
          rw [hlen_s.scratch_ok.work_stk1_len]; omega
        pt_steps_nogrp
        have hk1_eq := bv64_add1_toNat (by omega : k_v.toNat + 1 < 2 ^ 64)
        have hsn1_eq := bv64_add1_toNat (by omega : sn_v.toNat + 1 < 2 ^ 64)
        let lm' := lm.set tl_v.toNat 1#8; let ws1' := ws1.set sn_v.toNat tl_v
        have hlm'_len : lm'.length = 2 * c.max_vars := by simp [lm', hlm_l]
        have hws1'_len : ws1'.length = 2 * c.max_vars := by simp [ws1', hws1_l]
        have hsav' : M6pSavedMarksInv c
            { s_pp with core := { s_pp.core with lit_mark := lm' }
                        scratch := { s_pp.scratch with work_stk1 := ws1' } }
            (sn_v + 1#64).toNat := by
          rw [hsn1_eq]; refine ⟨hsn1_le, fun j hj => ?_, fun l hl hne => ?_⟩
          · dsimp only [ws1']; by_cases hjs : j = sn_v.toNat
            · subst hjs; rw [List.getElem?_set_self hsn_ws, Option.getD_some]; exact htl_lt
            · rw [List.getElem?_set_ne (Ne.symm hjs)]; exact hsav_s.2.1 j (by omega)
          · dsimp only [lm'] at hne; dsimp only [ws1']; by_cases hltl : l = tl_v.toNat
            · subst hltl
              exact ⟨sn_v.toNat, by omega, by rw [List.getElem?_set_self hsn_ws, Option.getD_some]⟩
            · rw [List.getElem?_set_ne (Ne.symm hltl)] at hne
              obtain ⟨j, hj, hjeq⟩ := hsav_s.2.2 l hl hne
              exact ⟨j, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hjeq⟩
        have hment' : M6pMarkedLitsEntailed F_cur lit.toNat
            { s_pp with core := { s_pp.core with lit_mark := lm' }
                        scratch := { s_pp.scratch with work_stk1 := ws1' } } := by
          intro l hl hne; dsimp only [lm'] at hne; by_cases hltl : l = tl_v.toNat
          · subst hltl
            simpa [tl_v, st_s, List.getElem?_eq_getElem hk_trl] using hent_p1 k_v.toNat hk_lt
          · rw [List.getElem?_set_ne (Ne.symm hltl)] at hne; exact hment_s l hl hne
        refine ih (sn_v + 1#64, k_v + 1#64, ()) m (by dsimp only [smeas]; rw [hk1_eq]; omega)
          ⟨by rw [hk1_eq]; omega, by rw [hk1_eq]; omega,
            by rw [hsn1_eq, hk1_eq]; omega, lm', ws1', hlm'_len, hws1'_len, hsav', hment', ?_⟩
        simpa only [lm', ws1', tl_v, st_s, bv_c0_zext32_64] using hm
      · exfalso; have hk_lt : k_v.toNat < s_pp.core.trail_end := by pt_bound
        have hcv_64 : s.core.cur_vars < 2 ^ 64 := by omega
        have hsn_lt : sn_v.toNat < s.core.cur_vars := by rw [← hcv_pp]; omega
        pt_clear_big; rw [Nat.mod_eq_of_lt hcv_64] at hc; exact hc hsn_lt
      · exact h_exit_wp (by pt_bound)

end ProbeAssumePairM6Proof

end LeanQbe.T.Examples.Kissat.FullM6VivBackbone
