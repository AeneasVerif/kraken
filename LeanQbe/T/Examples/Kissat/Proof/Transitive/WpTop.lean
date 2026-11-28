/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Transitive.UnrollInv
public import LeanQbe.T.Examples.Kissat.Proof.Transitive.WpSort
public import LeanQbe.T.Examples.Kissat.Proof.Transitive.WpLit
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Src.Transitive

/-!
# Weakest-Precondition Proof for `full_transitive_m6` (`Proof.Transitive.WpTop`)

Verifies `fullTransitiveM6Spec` for `Src.Transitive.full_transitive_m6_body` using
`full_backtrack`, `full_prioritize_binaries_m6`, `full_trans_sort_m6`,
`full_trans_lit_m6`, `full_propagate`, and `full_wstack_defrag`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Transitive

open Std.Sat
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private theorem tr_top_set_probing {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    (pr' : BitVec 64) :
    let s' := { s with core := { s.core with probing := pr' } }
    FullSparseInv c F0 s' ∧ FullWitnessInv c F0 F_cur s'.core := by
  intro s'
  have hw' := fullWitnessInv_with_flags_probing hw s.core.flags pr'
  have hc := hsp.1.lengths.core_ok
  have hl' : s'.LengthsOk c :=
    ⟨{ hc with vals_len := hc.vals_len }, hsp.1.lengths.scratch_ok⟩
  exact ⟨fullSparseInv_frame hsp hl' hw' rfl rfl rfl rfl hsp.2.2.2.2 rfl rfl fun _ h => h, hw'⟩

private theorem tr_top_set_ant_sz {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) (as' : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with ant_sz := as' } } := by
  obtain ⟨F_cur, hw⟩ := hsp.1.witness
  have hs := hsp.1.lengths.scratch_ok
  have hl' :
      ({ s with scratch := { s.scratch with ant_sz := as' } } : FullState).LengthsOk c :=
    ⟨hsp.1.lengths.core_ok, { hs with walk_vals_len := hs.walk_vals_len }⟩
  exact fullSparseInv_frame hsp hl' hw rfl rfl rfl rfl hsp.2.2.2.2 rfl rfl fun _ h => h

private theorem tr_top_clear_flag512_mem {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R' : Mem 64 → Prop} {m : Mem 64} (hsp : FullSparseInv c F0 s) {v : Nat} {fv : BitVec 32}
    (hm : (FullMem c { s with core := { s.core with flags := s.core.flags.set v fv } } ⋆ R') m) :
    ∃ s', FullSparseInv c F0 s' ∧ s'.core.cur_level = s.core.cur_level ∧
      s'.core.cur_vars = s.core.cur_vars ∧ s'.core.fuel = s.core.fuel ∧
      s'.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c s' ⋆ R') m :=
  ⟨_, fullSparseInv_clear_fl_trans hsp, rfl, rfl, rfl, rfl, hm⟩

private theorem tr_top_bt_sparse {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)} {te' prop' cl' : Nat}
    {unass' : BitVec 64} {sc' : FullScratch}
    (hsp : FullSparseInv c F0 s)
    (heq : s' =
      { core :=
          { s.core with
            unassigned := unass', trail_end := te', propagated := prop', cur_level := cl',
            vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp' },
        scratch := sc' })
    (hl' : s'.LengthsOk c) (hprs : FullProbeScratchPres s s') (hcl' : cl' = min s.core.cur_level 0)
    (hwf : ∀ F0' F_cur', FullWitnessInv c F0' F_cur' s.core →
      0 ≤ s.core.cur_level → FullWitnessInv c F0' F_cur' s'.core) :
    FullSparseInv c F0 s' ∧ s'.core.cur_level = 0 ∧
    s'.core.probing = s.core.probing ∧ s'.core.fuel = s.core.fuel := by
  have hsp' := fullBacktrack_sparse hsp heq hl' hprs hwf
  have hcl0' : s'.core.cur_level = 0 := by rw [heq]; dsimp only; omega
  have hpr' : s'.core.probing = s.core.probing := by rw [heq]
  have hfl' : s'.core.fuel = s.core.fuel := by rw [heq]
  exact ⟨hsp', hcl0', hpr', hfl'⟩

private theorem tr_ext_trans {e0 e1 e2 : List (BitVec 64)}
    (h01 : M6HdrExtInitOk e0 → M6HdrExtInitOk e1 ∧ M6ExtW2bPres e0 e1)
    (h12 : M6HdrExtInitOk e1 → M6HdrExtInitOk e2 ∧ M6ExtW2bPres e1 e2) :
    M6HdrExtInitOk e0 → M6HdrExtInitOk e2 ∧ M6ExtW2bPres e0 e2 := fun h0 =>
  let ⟨hi1, hw01⟩ := h01 h0
  let ⟨hi2, hw12⟩ := h12 hi1
  ⟨hi2, M6ExtW2bPres.trans hw01 hw12⟩

private def TrLoopInv (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s0 : FullState)
    (R : Mem 64 → Prop) (n_nat : Nat) (s_k : FullState) (ext_k : List (BitVec 64))
    (m_k : Mem 64) : Prop :=
  M6HdrExtOk ext_k ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext_k ∧ M6ExtW2bPres ext ext_k) ∧
  FullSparseInv c F0 s_k ∧ s_k.core.cur_level = 0 ∧ s_k.core.cur_vars = s0.core.cur_vars ∧
  s_k.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
  (∀ idx < n_nat, (s_k.scratch.work_stk1[idx]?.getD 0#32).toNat < s_k.core.cur_vars) ∧
  (FullMem c s_k ⋆ (array64 (c.hdr - 2304) ext_k ⋆ R)) m_k

private theorem tr_top_prop_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {r : BitVec 64} {n_nat : Nat}
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch}
    (hsp : FullSparseInv c F0 s) (hcl0 : s.core.cur_level = 0)
    (hlt : ∀ idx < n_nat, (s.scratch.work_stk1[idx]?.getD 0#32).toNat < s.core.cur_vars)
    (heq : s' =
      { core :=
          { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
            unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
            wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
            confl_lit0 := c0', confl_lit1 := c1', oom := oom' },
        scratch := sc' })
    (hl' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hp' : FullArenaPermEq s.core s'.core)
    (hprs : FullProbeScratchPres { s with scratch := { s.scratch with
      search_ticks := sc'.search_ticks, wsort := sc'.wsort,
      phases := sc'.phases, delayed := sc'.delayed } } s')
    (hfuel : fuel'.toNat ≤ s.core.fuel.toNat)
    (hr1 : r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') :
    FullSparseInv c F0 s' ∧ s'.core.cur_level = 0 ∧ s'.core.cur_vars = s.core.cur_vars ∧
    s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
    (∀ idx < n_nat, (s'.scratch.work_stk1[idx]?.getD 0#32).toNat < s'.core.cur_vars) ∧
    (r = 1#64 → F0.Unsat) := by
  have hesp : FullExtScratchPres s s' := hprs.1
  have hsp' := fullPropagate_sparse hsp heq hesp hl' hw' hp'
  have hcl0' : s'.core.cur_level = 0 := by rw [heq]; exact hcl0
  have hcv' : s'.core.cur_vars = s.core.cur_vars := by rw [heq]
  have hws1' : s'.scratch.work_stk1 = s.scratch.work_stk1 := hprs.2.1
  have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [heq]; exact hfuel
  have hlt' : ∀ idx < n_nat,
      (s'.scratch.work_stk1[idx]?.getD 0#32).toNat < s'.core.cur_vars := by
    rw [hws1', hcv']; exact hlt
  refine ⟨hsp', hcl0', hcv', hfl', hlt', fun h1 => ?_⟩
  exact level0_unsat_of_conflict_okW hw' hcl0' (hr1 h1).2.2

private theorem tr_top_defrag_post {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wsort' : List (BitVec 32)}
    (hsp : FullSparseInv c F0 s)
    (heq : s' =
      { core := { s.core with wlen := wlen', wusable := 0#64, wvec := wvec', wstk := wstk' },
        scratch := { s.scratch with wsort := wsort' } })
    (hl' : s'.LengthsOk c) (hws' : WatchStackLayout s'.core)
    (hslice : ∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) :
    FullSparseInv c F0 s' ∧ s'.core.cur_level = s.core.cur_level ∧
    s'.core.probing = s.core.probing ∧ s'.core.fuel = s.core.fuel := by
  have hsp' := fullWstackDefrag_sparse hsp heq hl' hws' hslice
  have hcl' : s'.core.cur_level = s.core.cur_level := by rw [heq]
  have hpr' : s'.core.probing = s.core.probing := by rw [heq]
  have hfl' : s'.core.fuel = s.core.fuel := by rw [heq]
  exact ⟨hsp', hcl', hpr', hfl'⟩

private theorem tr_top_watch_layout {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) : WatchStackLayout s.core := by
  obtain ⟨F_cur, hw⟩ := hsp.1.witness
  have hmw : WatchesInv F_cur s.core := by
    simpa only [ModeWatchesInv, hsp.2.2.2.2, ↓reduceIte] using hw.watches
  exact hmw.layout

private theorem tr_top_lit2_lt {v : BitVec 32} {cv : Nat} (hv : v.toNat < cv)
    (hcv : 2 * cv < 2 ^ 32) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
    ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 ∧
    (v <<< (1 : Nat)).toNat < 2 * cv ∧ ((v <<< (1 : Nat)) ||| 1#32).toNat < 2 * cv := by
  have hsh : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]
    omega
  have hor : ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := by
    rw [BitVec.toNat_or, hsh, show (1#32 : BitVec 32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_or]
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ j => simp [Nat.testBit_succ, show (2 * v.toNat + 1) / 2 = v.toNat by omega,
        Nat.div_eq_of_lt]
  exact ⟨hsh, hor, by omega, by omega⟩

private theorem tr_top_bit32_bv {x : BitVec 32} :
    (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem full_transitive_m6_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hPri : Γ.Has "full_prioritize_binaries_m6"
      LeanQbe.T.Examples.Kissat.Proof.Watch.Spec.fullPrioritizeBinariesM6Spec)
    (hSort : Γ.Has "full_trans_sort_m6" fullTransSortM6Spec)
    (hLit : Γ.Has "full_trans_lit_m6" fullTransLitM6Spec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hDefrag : Γ.Has "full_wstack_defrag" fullWstackDefragSpec)
    (a : Tup Val [i64, i64]) (m0 : Mem 64) (Q : Post [i64]) (X : XPost)
    (hspec : fullTransitiveM6Spec a m0 Q X) :
    Func.wp Γ Src.Transitive.full_transitive_m6_body a m0 Q X := by
  rcases a with ⟨h_arg, tlim, ⟨⟩⟩
  obtain ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hm0, hQ⟩ := hspec
  let R' := array64 (c.hdr - 2304) ext ⋆ R
  rw [fullM6HdrMem_iff] at hm0
  have hext_pres : M6HdrExtOk ext ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext ∧
      M6ExtW2bPres ext ext) :=
    ⟨hext, fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩⟩
  have hQ_m : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.probing = s.core.probing →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → r = 1#64 ∨ r = 20#64 →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ (array64 (c.hdr - 2304) ext' ⋆ R)) m' →
      Q (r, ()) m' :=
    fun r ext' s' m' hex' hsp' hcl' hpr' hfl' hr hu hm' =>
      hQ r ext' s' m' hex' hsp' (fun _ => hcl') hpr' ⟨hcl', hpr'⟩ hfl' hr hu
        ((fullM6HdrMem_iff c ext' s' R m').mpr hm')
  have hcl_bv : s.core.cur_level < 2 ^ 64 := by
    obtain ⟨_, hw⟩ := hsp.1.witness
    have := hw.cur_level_le; have := hsp.1.lengths.core_ok.trail_end_le
    have := hsp.1.lengths.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at *; omega
  unfold Src.Transitive.full_transitive_m6_body
  c0_hfast_nogrp
  refine wp_join_group (ts := []) (fun () m_bt =>
    ∃ s0, FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧ s0.core.probing = s.core.probing ∧
      s0.core.fuel = s.core.fuel ∧ (FullMem c s0 ⋆ R') m_bt) ?_ ?_
  · rintro _ ⟨⟩ m_bt ⟨s0, hsp0, hcl0, hpr0, hfl0, hm_bt⟩
    have hnb0_bv : s0.core.num_binary.toNat < 2 ^ 64 := s0.core.num_binary.isLt
    have hcv0_bv : s0.core.cur_vars < 2 ^ 64 := by
      have := hsp0.1.lengths.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at *; omega
    c0_hfast_nogrp
    · c0_hfast
      exact hQ_m 1#64 ext s0 m_bt hext_pres hsp0 hcl0 hpr0 (hfl0 ▸ Nat.le_refl _) (Or.inl rfl)
        (fun h => by cases h) hm_bt
    · c0_hfast
      exact hQ_m 1#64 ext s0 m_bt hext_pres hsp0 hcl0 hpr0 (hfl0 ▸ Nat.le_refl _) (Or.inl rfl)
        (fun h => by cases h) hm_bt
    · c0_hfast
      exact hQ_m 1#64 ext s0 m_bt hext_pres hsp0 hcl0 hpr0 (hfl0 ▸ Nat.le_refl _) (Or.inl rfl)
        (fun h => by cases h) hm_bt
    · obtain ⟨F_cur0, hw0⟩ := hsp0.1.witness
      obtain ⟨hsp1, hw1⟩ := tr_top_set_probing hsp0 hw0 1#64
      have hspW1 : FullSparseInvW c F0 F_cur0
          { s0 with core := { s0.core with probing := 1#64 } } :=
        ⟨hsp1.1.lengths, hw1, hsp1.2.1, hsp1.2.2.1, hsp1.2.2.2.1, hsp1.2.2.2.2⟩
      refine wp_call_of_spec _ _ (hPri _ _ _ _ ⟨c, F0, F_cur0, _, R', rfl, hspW1,
        by assumption, fun stop_early wstk2 scr2 m2 hspW2 hm2 => ?_⟩)
      let s2 : FullState := {
        core := { s0.core with probing := 1#64, wstk := wstk2 },
        scratch := { s0.scratch with scratch_buf := scr2 } }
      have hsp2 : FullSparseInv c F0 s2 :=
        ⟨⟨hspW2.1, F_cur0, hspW2.2.1⟩, hspW2.2.2.1, hspW2.2.2.2.1, hspW2.2.2.2.2.1,
          hspW2.2.2.2.2.2⟩
      have hcv2 : s2.core.cur_vars = s0.core.cur_vars := rfl
      c0_hfast_nogrp
      refine wp_loop_inv (ts := [i64, i64])
        (fun (n_v, i_v, ()) ml => ∃ n_nat ws1, n_v = BitVec.ofNat 64 n_nat ∧
          i_v.toNat ≤ s2.core.cur_vars ∧ n_nat ≤ i_v.toNat ∧ ws1.length = 2 * c.max_vars ∧
          (∀ idx < n_nat, (ws1[idx]?.getD 0#32).toNat < s2.core.cur_vars) ∧
          (FullMem c { s2 with scratch := { s2.scratch with work_stk1 := ws1 } } ⋆ R') ml)
        (fun (_, i_v, ()) _ => s2.core.cur_vars - i_v.toNat) ?_ ?_
      · intro Jc hJc
        c0_hfast
        exact hJc (0#64, 0#64, ()) m2 ⟨0, s2.scratch.work_stk1, rfl, Nat.zero_le _, Nat.zero_le _,
          hsp2.1.lengths.scratch_ok.work_stk1_len, fun _ h => by omega, hm2⟩
      · rintro Jc ⟨n_v, i_v, ⟨⟩⟩ ml ⟨n_nat, ws1, rfl, hi_le, hn_le, hlen_ws1, hws1_lt, hml⟩ hJc
        c0_hsplit
        · have hi_lt : i_v.toNat < s2.core.cur_vars := by
            have := hc; rw [Nat.mod_eq_of_lt (by omega)] at this; exact this
          have hcv_max := hsp2.1.lengths.core_ok.cur_vars_le
          have hcmv := c.hmaxv; unfold dimacsBound at hcmv
          have hi_flen : i_v.toNat < s2.core.flags.length := by
            rw [hsp2.1.lengths.core_ok.flags_len]; omega
          have hi2_vlen : 2 * i_v.toNat < s2.core.vals.length := by
            rw [hsp2.1.lengths.core_ok.vals_len]; omega
          have hn_ws1 : n_nat < ws1.length := by omega
          have hn64 : (BitVec.ofNat 64 n_nat).toNat = n_nat := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hn164 : (BitVec.ofNat 64 n_nat + 1#64).toNat = n_nat + 1 := by bv_omega
          have hi1_lt : (i_v + 1#64).toNat = i_v.toNat + 1 := tr_bv64_add1 (by omega)
          refine wp_join_group (ts := [i64]) (fun (n'_v, ()) ml' => ∃ n' ws1',
            n'_v = BitVec.ofNat 64 n' ∧ n' ≤ i_v.toNat + 1 ∧ ws1'.length = 2 * c.max_vars ∧
            (∀ idx < n', (ws1'[idx]?.getD 0#32).toNat < s2.core.cur_vars) ∧
            (FullMem c { s2 with scratch := { s2.scratch with work_stk1 := ws1' } } ⋆ R') ml')
            ?_ ?_
          · rintro _ ⟨n'_v, ⟨⟩⟩ ml' ⟨n', ws1', rfl, hn'_le, hlen', hlt', hml'⟩
            c0_hfast
            exact hJc (BitVec.ofNat 64 n', i_v + 1#64, ()) ml' (by dsimp only; rw [hi1_lt]; omega)
              ⟨n', ws1', rfl, by rw [hi1_lt]; omega, by rw [hi1_lt]; exact hn'_le,
                hlen', hlt', hml'⟩
          · intro Jnext hJnext
            c0_hfast_nogrp
            · c0_hfast
              have hiv32 : (BitVec.setWidth 32 i_v).toNat = i_v.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              rw [hn64] at hm
              refine hJnext (BitVec.ofNat 64 n_nat + 1#64, ()) _
                ⟨n_nat + 1, ws1.set n_nat (BitVec.setWidth 32 i_v), by bv_omega, by omega,
                  by rw [List.length_set, hlen_ws1], fun idx hidx => ?_, hm⟩
              by_cases hq : idx = n_nat
              · subst hq
                simpa only [List.getElem?_set_self hn_ws1, Option.getD_some, hiv32] using hi_lt
              · rw [List.getElem?_set_ne (Ne.symm hq)]
                exact hws1_lt idx (by omega)
            · exact hJnext (BitVec.ofNat 64 n_nat, ()) ml
                ⟨n_nat, ws1, rfl, by omega, hlen_ws1, hws1_lt, hml⟩
            · exact hJnext (BitVec.ofNat 64 n_nat, ()) ml
                ⟨n_nat, ws1, rfl, by omega, hlen_ws1, hws1_lt, hml⟩
        · have hi_eq : i_v.toNat = s2.core.cur_vars := by
            have := hc; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
          have hn_le_cv : n_nat ≤ s2.core.cur_vars := hi_eq ▸ hn_le
          have hn64 : (BitVec.ofNat 64 n_nat).toNat = n_nat := by
            have := hsp2.1.lengths.core_ok.cur_vars_le; have := c.hmaxv
            unfold dimacsBound at *; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          let s3 : FullState := { s2 with scratch := { s2.scratch with work_stk1 := ws1 } }
          have hsp3 : FullSparseInv c F0 s3 := tr_sparse_with_ws1 hsp2 hlen_ws1
          refine wp_join_group (ts := []) (fun () ml' => ∃ ws1_s,
            ws1_s.length = 2 * c.max_vars ∧
            FullSparseInv c F0 { s3 with scratch := { s3.scratch with work_stk1 := ws1_s } } ∧
            (∀ idx < n_nat, (ws1_s[idx]?.getD 0#32).toNat < s3.core.cur_vars) ∧
            (FullMem c { s3 with scratch := { s3.scratch with work_stk1 := ws1_s } } ⋆ R') ml')
            ?_ ?_
          · rintro _ ⟨⟩ ml' ⟨ws1_s, hlen_s, hsp_s, hlt_s, hm_s⟩
            c0_hfast_nogrp
            let s4 : FullState := { s3 with scratch := { s3.scratch with work_stk1 := ws1_s } }
            let s5 : FullState := { s4 with scratch := { s4.scratch with ant_sz := tlim } }
            have hsp5 : FullSparseInv c F0 s5 := tr_top_set_ant_sz hsp_s tlim
            refine wp_join_group (ts := [i64, i64]) (fun (res, _, ()) m_ex =>
              ∃ ext_ex s_ex, M6HdrExtOk ext_ex ∧
                (M6HdrExtInitOk ext → M6HdrExtInitOk ext_ex ∧ M6ExtW2bPres ext ext_ex) ∧
                FullSparseInv c F0 s_ex ∧ s_ex.core.cur_level = 0 ∧
                s_ex.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (res = 1#64 ∨ res = 20#64) ∧
                (res = 20#64 → F0.Unsat) ∧
                (FullMem c s_ex ⋆ (array64 (c.hdr - 2304) ext_ex ⋆ R)) m_ex) ?_ ?_
            · rintro _ ⟨res, _, ⟨⟩⟩ m_ex
                ⟨ext_ex, s_ex, hext_ex, hpext_ex, hsp_ex, hcl_ex, hfl_ex, hres, hu_ex, hm_ex⟩
              c0_hfast_nogrp
              refine wp_join_group (ts := []) (fun () m_out =>
                ∃ s_out, FullSparseInv c F0 s_out ∧ s_out.core.cur_level = 0 ∧
                  s_out.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                  (FullMem c s_out ⋆ (array64 (c.hdr - 2304) ext_ex ⋆ R)) m_out) ?_ ?_
              · rintro _ ⟨⟩ m_out ⟨s_out, hsp_o, hcl_o, hfl_o, hm_o⟩
                obtain ⟨F_o, hw_o⟩ := hsp_o.1.witness
                obtain ⟨hsp_pr, _⟩ := tr_top_set_probing hsp_o hw_o s0.core.probing
                c0_hfast
                exact hQ_m res ext_ex _ _ ⟨hext_ex, hpext_ex⟩ hsp_pr hcl_o hpr0 (hfl0 ▸ hfl_o)
                  hres hu_ex hm
              · intro Jdf hJdf
                c0_hfast_nogrp
                · refine wp_call_of_spec _ _ (hDefrag _ _ _ _ ⟨c, s_ex,
                    array64 (c.hdr - 2304) ext_ex ⋆ R, rfl, hsp_ex.1.lengths,
                    tr_top_watch_layout hsp_ex, hm_ex,
                    fun wvec' wstk' wlen' wsort' m_df hl_df hws_df _ hslice_df hm_df => by
                      obtain ⟨hsp_df, hcl_df, _, hfl_df⟩ :=
                        tr_top_defrag_post hsp_ex rfl hl_df hws_df hslice_df
                      rw [wp_jump]
                      exact hJdf () m_df ⟨_, hsp_df, hcl_df ▸ hcl_ex, hfl_df ▸ hfl_ex, hm_df⟩⟩)
                · exact hJdf () m_ex ⟨s_ex, hsp_ex, hcl_ex, hfl_ex, hm_ex⟩
            · intro Jb hJb
              c0_hfast_nogrp
              refine wp_loop_inv (ts := [i64])
                (fun (k_v, ()) m_k => ∃ ext_k s_k,
                  k_v.toNat ≤ n_nat ∧ TrLoopInv c F0 ext s0 R n_nat s_k ext_k m_k)
                (fun (k_v, ()) _ => n_nat - k_v.toNat) ?_ ?_
              · intro Jk hJk
                c0_hfast
                exact hJk (0#64, ()) _ ⟨ext, s5, Nat.zero_le _, hext, hext_pres.2, hsp5, hcl0,
                  rfl, hfl0 ▸ Nat.le_refl _, hlt_s,
                  show (FullMem c s5 ⋆ R') _ from by dsimp only [s5, s4]; exact hm⟩
              · rintro Jk ⟨k_v, ⟨⟩⟩ m_k
                  ⟨ext_k, s_k, hk_le, hext_k, hpext_k, hsp_k, hcl_k, hcv_k, hfl_k, hlt_k, hm_k⟩ hJk
                have hcv_k_bv : s_k.core.cur_vars < 2 ^ 64 := by
                  have := hsp_k.1.lengths.core_ok.cur_vars_le; have := c.hmaxv
                  unfold dimacsBound at *; omega
                have hcv_max_k := hsp_k.1.lengths.core_ok.cur_vars_le
                have hcmv := c.hmaxv; unfold dimacsBound at hcmv
                c0_hsplit
                · have hk_lt : k_v.toNat < n_nat := by
                    have := hc; rwa [Nat.mod_eq_of_lt (by omega)] at this
                  have hk1_eq : (k_v + 1#64).toNat = k_v.toNat + 1 := tr_bv64_add1 (by omega)
                  have hk_ws1 : k_v.toNat < s_k.scratch.work_stk1.length := by
                    rw [hsp_k.1.lengths.scratch_ok.work_stk1_len]; omega
                  let v := s_k.scratch.work_stk1[k_v.toNat]'hk_ws1
                  have hv_lt : v.toNat < s_k.core.cur_vars := by
                    simpa only [List.getElem?_eq_getElem hk_ws1, Option.getD_some] using
                      hlt_k k_v.toNat hk_lt
                  have hv_flen : v.toNat < s_k.core.flags.length := by
                    rw [hsp_k.1.lengths.core_ok.flags_len]; omega
                  obtain ⟨hsh_v, hor_v, hv2_lt, hv21_lt⟩ := tr_top_lit2_lt hv_lt (by omega)
                  have hv2_vlen : (v <<< (1 : Nat)).toNat < s_k.core.vals.length := by
                    rw [hsp_k.1.lengths.core_ok.vals_len]; omega
                  have hv64_vlen :
                      (BitVec.setWidth 64 v <<< (1 : Nat)).toNat < s_k.core.vals.length := by
                    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, tr_top_bit32_bv,
                      Nat.mod_eq_of_lt (by omega), hsp_k.1.lengths.core_ok.vals_len]
                    omega
                  c0_hfast_nogrp
                  · refine wp_join_group (ts := [i64]) (fun (_, ()) m_67 =>
                      ∃ ext_67 s_67, TrLoopInv c F0 ext s0 R n_nat s_67 ext_67 m_67) ?_ ?_
                    · rintro _ ⟨_, ⟨⟩⟩ m_67 ⟨ext_67, s_67, h67⟩
                      c0_hfast
                      exact hJk (k_v + 1#64, ()) m_67 (by dsimp only; rw [hk1_eq]; omega)
                        ⟨ext_67, s_67, by rw [hk1_eq]; exact hk_lt, h67⟩
                    · intro J67 hJ67
                      refine wp_join_group (ts := []) (fun () m_69 =>
                          (FullMem c s_k ⋆ (array64 (c.hdr - 2304) ext_k ⋆ R)) m_69) ?_ ?_
                      · rintro _ ⟨⟩ m_69 hm_69
                        c0_hfast
                        obtain ⟨s_67, hsp_67, hcl_67, hcv_67, hfl_67, hws1_67, hm_67⟩ :=
                          tr_top_clear_flag512_mem hsp_k hm
                        have hlt_67 : ∀ idx < n_nat,
                            (s_67.scratch.work_stk1[idx]?.getD 0#32).toNat <
                              s_67.core.cur_vars := by
                          rw [hws1_67, hcv_67]; exact hlt_k
                        exact hJ67 (1#64, ()) _ ⟨ext_k, s_67, hext_k, hpext_k, hsp_67,
                          hcl_67 ▸ hcl_k, hcv_67 ▸ hcv_k, hfl_67 ▸ hfl_k, hlt_67, hm_67⟩
                      · intro J69 hJ69
                        c0_hfast_nogrp
                        · refine wp_call_of_spec _ _ (hLit _ _ _ _ ⟨c, F0, s_k,
                              array64 (c.hdr - 2304) ext_k ⋆ R, rfl, hsp_k,
                              hcl_k, by simp only [Arg.val]; exact hv2_lt, hm_k,
                              fun ok1 s_l1 m_l1 hsp_l1 hcl_l1 hcv_l1 hfl_l1 hws1_l1 hu1 hm_l1 => by
                                have hlt_l1 : ∀ idx < n_nat,
                                    (s_l1.scratch.work_stk1[idx]?.getD 0#32).toNat <
                                      s_l1.core.cur_vars := by
                                  rw [hws1_l1, hcv_l1]; exact hlt_k
                                c0_hfast_nogrp
                                · obtain ⟨F_l1, hw_l1⟩ := hsp_l1.1.witness
                                  refine wp_call_of_spec _ _ (hProp _ _ _ _ ⟨c, F0, F_l1, ext_k,
                                    s_l1, R, rfl, hcfg, hext_k, hsp_l1.1.lengths, hw_l1,
                                    hsp_l1.2.2.2.2,
                                    (fullM6HdrMem_iff c ext_k s_l1 R m_l1).mpr hm_l1,
                                    fun r1 ext1 vals1 flags1 lvl1 rsns1 trl1 tp1 te1 prop1 unass1
                                      unfl1 wvec1 arena1 wstk1 wlen1 wu1 fuel1 ctype1 cref1
                                      c0_1 c1_1 oom1 sc1 m_p1 hext1_ok hext1_pres
                                      hl_p1 hw_p1 _ _ hp_p1 hprs_p1 _ _ _ _ hfl_p1
                                      hr_p1 hr0_p1 hr1_p1 _ _ hm_p1 => by
                                      obtain ⟨hsp_p1, hcl_p1, hcv_p1, hfl_p1', hlt_p1, hu_p1⟩ :=
                                        tr_top_prop_post hsp_l1 hcl_l1 hlt_l1 rfl hl_p1 hw_p1
                                          hp_p1 hprs_p1 hfl_p1 hr1_p1
                                      have hpext1 := tr_ext_trans hpext_k hext1_pres
                                      have hm_p1' := (fullM6HdrMem_iff c ext1 _ R m_p1).mp hm_p1
                                      have hcv_p1_0 := (hcv_p1.trans hcv_l1).trans hcv_k
                                      c0_hfast_nogrp
                                      · exact hJb (20#64, k_v, ()) m_p1
                                          ⟨ext1, _, hext1_ok, hpext1, hsp_p1, hcl_p1,
                                            Nat.le_trans hfl_p1' (hfl_l1 ▸ hfl_k), Or.inr rfl,
                                            fun _ => hu_p1 (by cases r1 <;> simp_all), hm_p1'⟩
                                      · exact hJb (1#64, k_v, ()) m_p1
                                          ⟨ext1, _, hext1_ok, hpext1, hsp_p1, hcl_p1,
                                            Nat.le_trans hfl_p1' (hfl_l1 ▸ hfl_k), Or.inl rfl,
                                            (fun h => by cases h), hm_p1'⟩
                                      · exact hJb (1#64, k_v, ()) m_p1
                                          ⟨ext1, _, hext1_ok, hpext1, hsp_p1, hcl_p1,
                                            Nat.le_trans hfl_p1' (hfl_l1 ▸ hfl_k), Or.inl rfl,
                                            (fun h => by cases h), hm_p1'⟩
                                      · exact hJb (1#64, k_v, ()) m_p1
                                          ⟨ext1, _, hext1_ok, hpext1, hsp_p1, hcl_p1,
                                            Nat.le_trans hfl_p1' (hfl_l1 ▸ hfl_k), Or.inl rfl,
                                            (fun h => by cases h), hm_p1'⟩
                                      · exact hJb (1#64, k_v, ()) m_p1
                                          ⟨ext1, _, hext1_ok, hpext1, hsp_p1, hcl_p1,
                                            Nat.le_trans hfl_p1' (hfl_l1 ▸ hfl_k), Or.inl rfl,
                                            (fun h => by cases h), hm_p1'⟩
                                      · refine wp_call_of_spec _ _ (hLit _ _ _ _ ⟨c, F0, _,
                                          array64 (c.hdr - 2304) ext1 ⋆ R, rfl,
                                          hsp_p1, hcl_p1, by
                                            simp only [Arg.val]; rw [hcv_p1, hcv_l1]; exact hv21_lt,
                                          hm_p1', fun ok2 s_l2 m_l2 hsp_l2 hcl_l2 hcv_l2 hfl_l2
                                            hws1_l2 hu2 hm_l2 => by
                                          have hlt_l2 : ∀ idx < n_nat,
                                              (s_l2.scratch.work_stk1[idx]?.getD 0#32).toNat <
                                                s_l2.core.cur_vars := by
                                            rw [hws1_l2, hcv_l2]; exact hlt_p1
                                          c0_hfast_nogrp
                                          · obtain ⟨F_l2, hw_l2⟩ := hsp_l2.1.witness
                                            refine wp_call_of_spec _ _ (hProp _ _ _ _ ⟨c, F0,
                                              F_l2, ext1, s_l2, R, rfl, hcfg, hext1_ok,
                                              hsp_l2.1.lengths, hw_l2, hsp_l2.2.2.2.2,
                                              (fullM6HdrMem_iff c ext1 s_l2 R m_l2).mpr hm_l2,
                                              fun r2 ext2 vals2 flags2 lvl2 rsns2 trl2 tp2 te2 prop2
                                                unass2 unfl2 wvec2 arena2 wstk2 wlen2 wu2 fuel2
                                                ctype2 cref2 c0_2 c1_2 oom2 sc2 m_p2
                                                hext2_ok hext2_pres hl_p2 hw_p2 _ _ hp_p2 hprs_p2
                                                _ _ _ _ hfl_p2 hr_p2 hr0_p2 hr1_p2 _ _ hm_p2 => by
                                                obtain ⟨hsp_p2, hcl_p2, hcv_p2, hfl_p2', hlt_p2,
                                                  hu_p2⟩ := tr_top_prop_post hsp_l2 hcl_l2 hlt_l2
                                                    rfl hl_p2 hw_p2 hp_p2 hprs_p2 hfl_p2 hr1_p2
                                                have hpext2 := tr_ext_trans hpext1 hext2_pres
                                                have hm_p2' :=
                                                  (fullM6HdrMem_iff c ext2 _ R m_p2).mp hm_p2
                                                have hcv_p2_0 :=
                                                  (hcv_p2.trans hcv_l2).trans hcv_p1_0
                                                have hfl_p2_0 := Nat.le_trans hfl_p2'
                                                  (hfl_l2 ▸ Nat.le_trans hfl_p1' (hfl_l1 ▸ hfl_k))
                                                c0_hfast_nogrp
                                                · exact hJb (20#64, k_v, ()) m_p2
                                                    ⟨ext2, _, hext2_ok, hpext2, hsp_p2, hcl_p2,
                                                      hfl_p2_0, Or.inr rfl,
                                                      fun _ => hu_p2 (by cases r2 <;> simp_all),
                                                      hm_p2'⟩
                                                · exact hJb (1#64, k_v, ()) m_p2
                                                    ⟨ext2, _, hext2_ok, hpext2, hsp_p2, hcl_p2,
                                                      hfl_p2_0, Or.inl rfl,
                                                      (fun h => by cases h), hm_p2'⟩
                                                · refine wp_join_group (ts := []) (fun () m_114 =>
                                                    ∃ ext_114 s_114,
                                                      TrLoopInv c F0 ext s0 R n_nat s_114 ext_114
                                                        m_114) ?_ ?_
                                                  · rintro _ ⟨⟩ m_114 ⟨ext_114, s_114, h114⟩
                                                    c0_hfast
                                                    exact hJ67 (1#64, ()) m_114
                                                      ⟨ext_114, s_114, h114⟩
                                                  · intro J114 hJ114
                                                    have hv_flen2 : v.toNat < flags2.length := by
                                                      rw [hl_p2.core_ok.flags_len]
                                                      have := hl_p2.core_ok.cur_vars_le; omega
                                                    c0_hfast_nogrp
                                                    · c0_hfast
                                                      obtain ⟨s_114, hsp_114, hcl_114, hcv_114,
                                                        hfl_114, hws1_114, hm_114⟩ :=
                                                        tr_top_clear_flag512_mem hsp_p2 hm
                                                      have hlt_114 : ∀ idx < n_nat,
                                                          (s_114.scratch.work_stk1[idx]?.getD
                                                            0#32).toNat < s_114.core.cur_vars := by
                                                        rw [hws1_114, hcv_114]; exact hlt_p2
                                                      exact hJ114 () _ ⟨ext2, s_114, hext2_ok,
                                                        hpext2, hsp_114, hcl_114 ▸ hcl_p2,
                                                        hcv_114 ▸ hcv_p2_0, hfl_114 ▸ hfl_p2_0,
                                                        hlt_114, hm_114⟩
                                                    · exact hJ114 () m_p2 ⟨ext2, _, hext2_ok,
                                                        hpext2, hsp_p2, hcl_p2, hcv_p2_0, hfl_p2_0,
                                                        hlt_p2, hm_p2'⟩
                                                    · exact hJ114 () m_p2 ⟨ext2, _, hext2_ok,
                                                        hpext2, hsp_p2, hcl_p2, hcv_p2_0, hfl_p2_0,
                                                        hlt_p2, hm_p2'⟩
                                                    · exact hJ114 () m_p2 ⟨ext2, _, hext2_ok,
                                                        hpext2, hsp_p2, hcl_p2, hcv_p2_0, hfl_p2_0,
                                                        hlt_p2, hm_p2'⟩⟩)
                                          · exact hJb (20#64, k_v, ()) m_l2 ⟨ext1, s_l2, hext1_ok,
                                              hpext1, hsp_l2, hcl_l2,
                                              hfl_l2 ▸ Nat.le_trans hfl_p1' (hfl_l1 ▸ hfl_k),
                                              Or.inr rfl,
                                              fun _ => hu2 (by cases ok2 <;> simp_all), hm_l2⟩⟩)⟩)
                                · exact hJb (20#64, k_v, ()) m_l1 ⟨ext_k, s_l1, hext_k, hpext_k,
                                    hsp_l1, hcl_l1, hfl_l1 ▸ hfl_k, Or.inr rfl,
                                    fun _ => hu1 (by cases ok1 <;> simp_all), hm_l1⟩⟩)
                        · exact hJ69 () m_k hm_k
                        · exact hJ69 () m_k hm_k
                  · exact hJb (1#64, k_v, ()) m_k ⟨ext_k, s_k, hext_k, hpext_k, hsp_k, hcl_k,
                      hfl_k, Or.inl rfl, (fun h => by cases h), hm_k⟩
                  · exact hJb (1#64, k_v, ()) m_k ⟨ext_k, s_k, hext_k, hpext_k, hsp_k, hcl_k,
                      hfl_k, Or.inl rfl, (fun h => by cases h), hm_k⟩
                  · exact hJb (1#64, k_v, ()) m_k ⟨ext_k, s_k, hext_k, hpext_k, hsp_k, hcl_k,
                      hfl_k, Or.inl rfl, (fun h => by cases h), hm_k⟩
                · exact hJb (1#64, k_v, ()) m_k ⟨ext_k, s_k, hext_k, hpext_k, hsp_k, hcl_k,
                    hfl_k, Or.inl rfl, (fun h => by cases h), hm_k⟩
          · intro Jsr hJsr
            c0_hsplit
            · refine wp_call_of_spec _ _ (hSort _ _ _ _ ⟨c, F0, s3, R', rfl, hsp3,
                by simp only [Arg.val, hn64]; exact hn_le_cv,
                by simp only [Arg.val, hn64]; exact hws1_lt, hml,
                fun ws1_s m_s hlen_s hsp_s hlt_s hm_s => by
                  dsimp only; rw [wp_jump]
                  exact hJsr () m_s ⟨ws1_s, hlen_s, hsp_s,
                    by simp only [Arg.val, hn64] at hlt_s; exact hlt_s, hm_s⟩⟩)
            · exact hJsr () ml ⟨ws1, hlen_ws1, hsp3, hws1_lt, hml⟩
  · intro J0 hJ0
    c0_hfast_nogrp
    · refine wp_call_of_spec _ _ (hBt _ _ _ _ ⟨c, s, R', rfl, hsp.1.lengths, hcl_bv,
        fun h0 => by
          have := hsp.1.lengths.core_ok.cur_vars_le
          obtain ⟨_, hw⟩ := hsp.1.witness
          have := hw.cur_level_le; have := hsp.1.lengths.core_ok.trail_end_le; omega,
        fun i hi => by obtain ⟨_, hw⟩ := hsp.1.witness; exact hw.trail_lits_lt i hi,
        hm0, fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
          hl' _ _ hcl' hprs' _ _ _ hwf' _ hm_bt => by
          obtain ⟨hsp_bt, hcl0_bt, hpr_bt, hfl_bt⟩ :=
            tr_top_bt_sparse hsp rfl hl' hprs' hcl' hwf'
          dsimp only; rw [wp_jump]
          exact hJ0 () m_bt ⟨_, hsp_bt, hcl0_bt, hpr_bt, hfl_bt, hm_bt⟩⟩)
    · have hcl0 : s.core.cur_level = 0 := by
        have := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_bv] at this
        exact this
      exact hJ0 () m0 ⟨s, hsp, hcl0, rfl, rfl, hm0⟩

end LeanQbe.T.Examples.Kissat.Proof.Transitive
