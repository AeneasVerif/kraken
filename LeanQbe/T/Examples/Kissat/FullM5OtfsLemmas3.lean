/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM5Otfs
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas1
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
public import LeanQbe.T.Logic.C0HeadStep
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M5 `Func.wp` Proofs — Part 3 (`full_otfs_bin_m5`, `full_deduce_1uip_m5`)

Zero `import all LeanQbe.*`. Proves canonical `FullSpec2` contracts (`XPost := False`, UNSAT-only)
for:
1. `full_otfs_bin_m5_wp` (`Full.fullOtfsBinSpec`): read-only watch-slice `has_bin` deduplication,
   headroom pre-check (`wcap - wlen >= 2ULL` + `full_wstack_defrag`) before `full_watch_push`,
   backward `full_unwatch_large`, and `full_arena_next(h, cref) - cref` garbage accounting.
2. `full_deduce_1uip_m5_wp` (`Full.fullDeduce1uipSpec`): entry `h->oom != 0ULL` exit, OTFS via
   `full_otfs_bin_m5` and `full_otfs_large` with clean OOM aborts, and `res_sz = min_clr_len`
   transfer before `full_clear_ana`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5Otfs

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding
  full_unwatch_large_body full_unwatch_large_wf
  full_otfs_large_body full_otfs_large_wf full_otfs_large_wp full_otfs_large_wp_weak
  full_prop_lit_body full_prop_lit_wf
  full_propagate_ignore_body full_propagate_ignore_wf
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open scoped LeanQbe.T.Examples.Kissat.Full.Deduce1UipTactics

/-! ## 1. `full_otfs_bin_m5_wp` (`Full.fullOtfsBinSpec`) -/

section OtfsBinM5Proof

private theorem m5_bv64_shl_sext1 (x : BitVec 64) (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< BitVec.signExtend 64 1#32).toNat = 2 * x.toNat := by
  have hs : BitVec.signExtend 64 1#32 = (1 : BitVec 64) := by decide
  have hsh : x <<< (1 : BitVec 64) = x <<< (1 : Nat) := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hs, hsh]
  exact m5_bv64_shl1_nat x h

private theorem m5_bv64_shl_sext1_add1 (x : BitVec 64) (h : 2 * x.toNat + 1 < 2 ^ 64) :
    ((x <<< BitVec.signExtend 64 1#32) + 1#64).toNat = 2 * x.toNat + 1 := by
  have hs := m5_bv64_shl_sext1 x (by omega)
  rw [BitVec.toNat_add, hs, show (1#64 : BitVec 64).toNat = 1 from rfl]
  exact Nat.mod_eq_of_lt h

private theorem m5_watchSlice_bin_tail {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len : Nat} (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len) :
    (∃ w0, k.wstk[p]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧
      w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      WatchSliceOk F_cur k lit (p + 1) (len - 1)) ∨
    (2 ≤ len ∧ ∃ w0 cr, k.wstk[p]? = some w0 ∧ k.wstk[p + 1]? = some cr ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧ WatchSliceOk F_cur k lit (p + 2) (len - 2)) := by
  cases h with
  | empty => omega
  | bin hp hflag hne hlt hent hrest =>
    exact Or.inl ⟨_, hp, hflag, hne, hlt, hent, by simpa using hrest⟩
  | large hp hp1 hflag hlt href hrest =>
    exact Or.inr ⟨Nat.le_add_left 2 _, _, _, hp, hp1, hflag, hlt, href, by simpa using hrest⟩

private theorem m5_otfs_bin_oom_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]}
    {wv ws : List (BitVec 32)} {wl : Nat} {wu : BitVec 64} {wso : List (BitVec 32)}
    {m' : Mem 64} (hiu : idx_u < cut) (hnd : Full.FullArenaVarsNodup s)
    (hlen_in : ({ s with
      core := { s.core with wvec := wv, wstk := ws, wlen := wl, wusable := wu },
      scratch := { s.scratch with wsort := wso } } : FullState).LengthsOk c)
    (hw_in : Full.FullWitnessCutInv c F0 F_cur cut
      { s.core with wvec := wv, wstk := ws, wlen := wl, wusable := wu })
    (hm' : (FullMem c { s with
      core := { s.core with wvec := wv, wstk := ws, wlen := wl, wusable := wu, oom := 1#64 },
      scratch := { s.scratch with wsort := wso } } ⋆ R) m')
    (hQ : ∀ (ok : Bool) arena' ag' wvec' wstk' wlen' wu' nb' ct' cr' c0' c1' oom' sc' m'',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_garbage := ag', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                confl_type := ct', confl_ref := cr', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → Full.FullWitnessCutInv c F0 F_cur idx_u s'.core →
      Full.FullArenaVarsNodup s' → Full.FullExtScratchPres s s' →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
      sc'.res_sz = s.scratch.res_sz → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → ct' = 1#64 ∧ Full.FullConflictOkCut F_cur idx_u s') →
      (FullMem c s' ⋆ R) m'' → Q (ok, ()) m'') :
    Q (false, ()) m' :=
  hQ false s.core.arena s.core.arena_garbage wv ws wl wu s.core.num_binary
    s.core.confl_type s.core.confl_ref s.core.confl_lit0 s.core.confl_lit1 1#64
    { s.scratch with wsort := wso } m' ⟨{ hlen_in.core_ok with }, hlen_in.scratch_ok⟩
    (m5_canonCut_shrink_cut (m5_canonCut_with_oom hw_in 1#64) (Nat.le_of_lt hiu))
    (by unfold Full.FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb
          fullArenaClauseLits
        exact hnd)
    ⟨rfl, rfl⟩ rfl rfl rfl rfl (fun hc => by cases hc) hm'

private theorem m5_otfs_bin_mark_fin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]}
    {wv4 ws4 : List (BitVec 32)} {wl4 : Nat} {wu4 nb4 : BitVec 64} {wso4 : List (BitVec 32)}
    {gsz : BitVec 64} {m' : Mem 64} (hw : Full.FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : Full.FullArenaVarsNodup s)
    {cref uip f0 f1 : BitVec 32} (hcref : cref.toNat ∈ fullArenaClauseRefs s)
    (_hng : fullArenaClauseGarb s cref.toNat = false)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlev_u : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hf0_m : f0.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hf1_m : f1.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hf0_u : f0 ≠ uip) (hf1_u : f1 ≠ uip)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars) (hf1_lt : f1.toNat < 2 * s.core.cur_vars)
    (hent_f : (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, f1.toNat]))
    (har_len : s.core.arena.length = c.arena_cap) (_h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1)
    (hcr0_bd : (cref.setWidth 64).toNat < s.core.arena.length)
    (hlen4 : ({ s with
      core := { s.core with num_binary := nb4, wvec := wv4, wstk := ws4,
                            wlen := wl4, wusable := wu4 }
      scratch := { s.scratch with wsort := wso4 } } : FullState).LengthsOk c)
    (hw4 : Full.FullWitnessCutInv c F0 F_cur cut
      { s.core with num_binary := nb4, wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4 })
    (hm' : (FullMem c { s with
      core := { s.core with
        num_binary := nb4, wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4,
        arena := s.core.arena.set (cref.setWidth 64).toNat
          (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bd ||| 0x00080000#32),
        arena_garbage := s.core.arena_garbage + gsz,
        confl_type := 1#64, confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64,
        confl_ref := 0xFFFFFFFF#64 },
      scratch := { s.scratch with wsort := wso4, otfs_cnt := s.scratch.otfs_cnt + 1#64 } } ⋆ R) m')
    (hQ : ∀ (ok : Bool) arena' ag' wvec' wstk' wlen' wu' nb' ct' cr' c0' c1' oom' sc' m'',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_garbage := ag', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                confl_type := ct', confl_ref := cr', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → Full.FullWitnessCutInv c F0 F_cur idx_u s'.core →
      Full.FullArenaVarsNodup s' → Full.FullExtScratchPres s s' →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
      sc'.res_sz = s.scratch.res_sz → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → ct' = 1#64 ∧ Full.FullConflictOkCut F_cur idx_u s') →
      (FullMem c s' ⋆ R) m'' → Q (ok, ()) m'') :
    Q (true, ()) m' := by
  let s4 : FullState :=
    { s with
      core := { s.core with num_binary := nb4, wvec := wv4, wstk := ws4,
                            wlen := wl4, wusable := wu4 }
      scratch := { s.scratch with wsort := wso4 } }
  have hw4_ana := m5_canonCut_to_anaCut hw4
  have hna := otfs_nonactive_on_trail hw4_ana hlen4.core_ok hiu_cut hiu_te ht_u hr_u hlev_u hcref
  obtain ⟨arena5, h_arena5⟩ : ∃ xs, xs = s4.core.arena.set cref.toNat
      (fullArenaHdrCore s4.core cref.toNat ||| 0x00080000#32) := ⟨_, rfl⟩
  let ag5 := s.core.arena_garbage + gsz
  have hcr_toNat : (cref.setWidth 64).toNat = cref.toNat := zext_toNat cref (by decide)
  have hcr_lt_len : cref.toNat < s.core.arena.length := hcr_toNat ▸ hcr0_bd
  have hd_c : fullArenaHdrCore s4.core cref.toNat =
      s.core.arena[cref.toNat]'hcr_lt_len := by
    unfold fullArenaHdrCore; dsimp only [s4]
    rw [List.getElem?_eq_getElem hcr_lt_len, Option.getD_some]
  have hmg5 := markGarb_preserves_fullWitnessCut hlen4.core_ok hw4_ana (Nat.le_of_lt hiu_cut)
    hcref ag5 fun idx hidx hc => hna idx hidx
      (hc.elim (fun h => Or.inl (Nat.lt_min.mpr ⟨Nat.lt_trans h hiu_cut, h⟩)) Or.inr)
  rw [← h_arena5] at hmg5
  obtain ⟨hw5_a, hrefs5, hprops5⟩ := hmg5
  have hgarb5 : fullArenaClauseGarbCore
      { s4.core with arena := arena5, arena_garbage := ag5 } cref.toNat = true := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore
    rw [h_arena5]; dsimp only [s4]
    rw [List.getElem?_set_self (by simpa [har_len] using hcr_lt_len), Option.getD_some]
    simp [bv32_or_garb_garb]
  let s5_pre : FullState :=
    { s4 with core := { s4.core with arena := arena5, arena_garbage := ag5 } }
  have hnd4_ana : Full.FullAnalyzeSpecs.FullArenaVarsNodup s4 := fun r hr hgr =>
    hnd r (by change r ∈ fullArenaClauseRefsCore s.core
              simpa [fullArenaClauseRefsCore, s4] using hr)
      (by change fullArenaClauseGarbCore s.core r = false
          simpa [fullArenaClauseGarbCore, fullArenaHdrCore, s4] using hgr)
  have hnd5_pre : Full.FullArenaVarsNodup s5_pre := fullArenaVarsNodup_markGarb
    hnd4_ana hrefs5 hgarb5 fun r hr hne => ⟨(hprops5 r hr).2.1, (hprops5 r hr).2.2 hne⟩
  have hw_fin : Full.FullWitnessCutInv c F0 F_cur idx_u
      { s.core with
        arena := arena5, arena_garbage := ag5, num_binary := nb4,
        wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4, confl_type := 1#64,
        confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64, confl_ref := 0xFFFFFFFF#64 } :=
    m5_anaCut_to_canonCut
      (hw5_a.with_confl 1#64 (f0.setWidth 64) (f1.setWidth 64) 0xFFFFFFFF#64)
      (by
        change idx_u ≤ s4.core.trail_end
        exact Nat.le_of_lt (Nat.lt_of_lt_of_le hiu_cut hw4.cut_le))
  let s_fin : FullState :=
    { s with
      core :=
        { s.core with
          arena := arena5, arena_garbage := ag5, num_binary := nb4,
          wvec := wv4, wstk := ws4, wlen := wl4, wusable := wu4, confl_type := 1#64,
          confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64, confl_ref := 0xFFFFFFFF#64 },
      scratch := { s.scratch with wsort := wso4, otfs_cnt := s.scratch.otfs_cnt + 1#64 } }
  have harena := c.harena; unfold dimacsBound at harena
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have har_le := hlen4.core_ok.arena_len_le
  have hcr_lt : cref.toNat < 2 ^ 31 - 1 := by
    have := hwf.2.2.1; have := hwf.2.2.2.1; omega
  have hcref_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hcr_lt
  have hcref_lg : (cref &&& 0x80000000#32) = 0#32 :=
    (bv32_lit_lo31_props (Nat.lt_trans hcr_lt (by omega))).2.2
  have hri := hw.reason_inv_cut idx_u hiu_cut
  dsimp only at hri; rw [ht_u, hr_u] at hri
  have hri := hri hcref_ne
  rw [ite_eq_right (fun h => absurd hcref_lg h)] at hri
  have hconfl_ok : Full.FullConflictOkCut F_cur idx_u s_fin := by
    simp only [Full.FullConflictOkCut, Full.FullConflictOkW, s_fin, ↓reduceIte]
    have hto0 : (f0.setWidth 64).toNat = f0.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    have hto1 : (f1.setWidth 64).toNat = f1.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    rw [hto0, hto1]
    have hm_ex (f : BitVec 32) (hfm : f.toNat ∈ fullArenaClauseLits s cref.toNat)
        (hfu : f ≠ uip) (hflt : f.toNat < 2 * s.core.cur_vars) :
        s.core.vals[f.toNat]?.getD 0#8 = 0xFF#8 ∧
        ((s.core.lvl[f.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
          ∃ m < idx_u, (s.core.trl[m]?.getD 0#32).toNat = f.toNat ^^^ 1) := by
      have hneq : f.toNat ≠ uip.toNat := fun he => hfu (BitVec.eq_of_toNat_eq he)
      obtain ⟨m0, hm0, hm0_eq, _⟩ := (hri.2.2 f.toNat hfm).resolve_left hneq
      exact ⟨(hw.vals_false_iff f.toNat hflt).mpr ⟨m0, Nat.lt_trans hm0 hiu_te, hm0_eq⟩,
        fun _ => ⟨m0, hm0, hm0_eq⟩⟩
    have p0 := hm_ex f0 hf0_m hf0_u hf0_lt
    have p1 := hm_ex f1 hf1_m hf1_u hf1_lt
    refine ⟨Or.inl ⟨trivial, hf0_lt, hf1_lt, p0.1, p1.1, hent_f⟩, ?_⟩
    exact ⟨p0.2, p1.2⟩
  have hlen_fin : s_fin.LengthsOk c :=
    ⟨{ hlen4.core_ok with arena_len_arr :=
        (by dsimp [s_fin]; rw [h_arena5]; dsimp [s4]; simp [har_len]) },
      { hlen4.scratch_ok with }⟩
  have hnd_fin : Full.FullArenaVarsNodup s_fin := by
    unfold Full.FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    exact hnd5_pre
  have har5_eq : s.core.arena.set (cref.setWidth 64).toNat
      (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bd ||| 0x00080000#32) = arena5 := by
    rw [h_arena5]; dsimp only [s4]
    exact list_set_congr hcr_toNat
      (by rw [hd_c, m5_list_getElem_of_idx hcr_toNat])
  exact hQ true arena5 ag5 wv4 ws4 wl4 wu4 nb4 1#64 0xFFFFFFFF#64
    (f0.setWidth 64) (f1.setWidth 64) s.core.oom s_fin.scratch m' hlen_fin hw_fin hnd_fin
    ⟨rfl, rfl⟩ rfl rfl rfl hrefs5 (fun _ => ⟨rfl, hconfl_ok⟩)
    (m5_fullMem_of_eq hm' (by dsimp [s_fin, ag5]; rw [har5_eq]) rfl)

private theorem otfs_bin_m5_tail_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut idx_u : Nat} {s s2 : FullState}
    {wv2 ws2 : List (BitVec 32)} {wl2 : Nat} {wu2 nb2 : BitVec 64} {wso2 : List (BitVec 32)}
    {cref uip f0 f1 : BitVec 32} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    {m2 : Mem 64}
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hw : Full.FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : Full.FullArenaVarsNodup s) (hdm : s.core.dense_mode = 0#64)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref.toNat = false)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlev_u : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hf0_m : f0.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hf1_m : f1.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hf0_u : f0 ≠ uip) (hf1_u : f1 ≠ uip)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars) (hf1_lt : f1.toNat < 2 * s.core.cur_vars)
    (hent_f : (cnfOfClauses F_cur).EntailsClause (cnfClause [f0.toNat, f1.toNat]))
    (har_len : s.core.arena.length = c.arena_cap) (h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1)
    (hs2_c : s2.core = { s.core with
      wvec := wv2, wstk := ws2, wlen := wl2, wusable := wu2, num_binary := nb2 })
    (hs2_sc : s2.scratch = { s.scratch with wsort := wso2 })
    (hlen2 : s2.LengthsOk c) (hw2 : Full.FullWitnessCutInv c F0 F_cur cut s2.core)
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : ∀ (ok : Bool) arena' ag' wvec' wstk' wlen' wu' nb' ct' cr' c0' c1' oom' sc' m'',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_garbage := ag', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                confl_type := ct', confl_ref := cr', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → Full.FullWitnessCutInv c F0 F_cur idx_u s'.core →
      Full.FullArenaVarsNodup s' → Full.FullExtScratchPres s s' →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
      sc'.res_sz = s.scratch.res_sz → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (ok = true → ct' = 1#64 ∧ Full.FullConflictOkCut F_cur idx_u s') →
      (FullMem c s' ⋆ R) m'' → Q (ok, ()) m'') :
    wp Γ Q X
      (.let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_44 =>
       .let_ (Op.mk (.add i64) (Arg.var p_44.fst, Arg.imm 3, ())) fun p_45 =>
       .let_ (Op.mk (.mul i64) (Arg.var p_45.fst, Arg.imm 4, ())) fun p_46 =>
       .let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_46.fst, ())) fun p_47 =>
       .load i32 (Arg.var p_47.fst) fun ld_9 =>
       .call (as := [i64, i32, i32]) (bs := []) "full_unwatch_large"
         (Arg.var c.hdr, Arg.var ld_9, Arg.var cref, ()) fun _ =>
       .let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_49 =>
       .let_ (Op.mk (.add i64) (Arg.var p_49.fst, Arg.imm 4, ())) fun p_50 =>
       .let_ (Op.mk (.mul i64) (Arg.var p_50.fst, Arg.imm 4, ())) fun p_51 =>
       .let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_51.fst, ())) fun p_52 =>
       .load i32 (Arg.var p_52.fst) fun ld_10 =>
       .call (as := [i64, i32, i32]) (bs := []) "full_unwatch_large"
         (Arg.var c.hdr, Arg.var ld_10, Arg.var cref, ()) fun _ =>
       .call (as := [i64, i32]) (bs := [i32]) "full_arena_next"
         (Arg.var c.hdr, Arg.var cref, ()) fun p_54 =>
       .let_ (Op.mk (.zext 32 64) (Arg.var p_54.fst, ())) fun p_55 =>
       .let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_56 =>
       .let_ (Op.mk (.sub i64) (Arg.var p_55.fst, Arg.var p_56.fst, ())) fun p_57 =>
       .let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_58 =>
       .let_ (Op.mk (.mul i64) (Arg.var p_58.fst, Arg.imm 4, ())) fun p_59 =>
       .let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_59.fst, ())) fun p_60 =>
       .let_ (Op.mk (.zext 32 64) (Arg.var cref, ())) fun p_61 =>
       .let_ (Op.mk (.mul i64) (Arg.var p_61.fst, Arg.imm 4, ())) fun p_62 =>
       .let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_62.fst, ())) fun p_63 =>
       .load i32 (Arg.var p_63.fst) fun ld =>
       .let_ (Op.mk (.or i32) (Arg.var ld, Arg.imm 524288#32, ())) fun p_64 =>
       .store (Arg.var p_64.fst) (Arg.var p_60.fst)
       (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 472, ())) fun p_65 =>
        .load i64 (Arg.var p_65.fst) fun ld =>
        .let_ (Op.mk (.add i64) (Arg.var ld, Arg.var p_57.fst, ())) fun p_66 =>
        .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 472, ())) fun p_67 =>
        .store (Arg.var p_66.fst) (Arg.var p_67.fst)
        (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 528, ())) fun p_68 =>
         .store (Arg.imm (t := i64) 1#64) (Arg.var p_68.fst)
         (.let_ (Op.mk (.zext 32 64) (Arg.var f0, ())) fun p_69 =>
          .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 536, ())) fun p_70 =>
          .store (Arg.var p_69.fst) (Arg.var p_70.fst)
          (.let_ (Op.mk (.zext 32 64) (Arg.var f1, ())) fun p_71 =>
           .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 544, ())) fun p_72 =>
           .store (Arg.var p_71.fst) (Arg.var p_72.fst)
           (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 176, ())) fun p_73 =>
            .store (Arg.imm (t := i64) 0xFFFFFFFF#64) (Arg.var p_73.fst)
            (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 960, ())) fun p_74 =>
             .load i64 (Arg.var p_74.fst) fun ld =>
             .let_ (Op.mk (.add i64) (Arg.var ld, Arg.imm 1#64, ())) fun p_75 =>
             .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 960, ())) fun p =>
             .store (Arg.var p_75.fst) (Arg.var p.fst)
             (.ret (Arg.imm true, ()))))))))) m2 := by
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have harena := c.harena; unfold dimacsBound at harena
  have har_le : s.core.arena_len ≤ c.arena_cap := by
    have h := hlen2.core_ok.arena_len_le; rwa [hs2_c] at h
  have hcr3_bd : (cref.setWidth 64 + 3#64).toNat < s2.core.arena.length := by
    rw [BitVec.toNat_add, zext_toNat cref (by decide), show (3#64 : BitVec 64).toNat = 3 from rfl,
      Nat.mod_eq_of_lt (by omega), hs2_c]; dsimp only
    rw [har_len]; omega
  have hlay2 : Full.WatchStackLayout s2.core := by
    have h := hw2.watches; unfold ModeWatchesInv at h
    rw [ite_eq_left (show s2.core.dense_mode = 0#64 by rw [hs2_c]; exact hdm)] at h
    exact h.layout
  fa_fast_steps_nogrp
  c0_call hUnw
  refine ⟨c, s2, R, rfl, hlen2, hlay2, hm2, fun wv3 ws3 wu3 m3 hlen3 hlay3 hmw3 hm3 => ?_⟩
  clear hm2
  obtain ⟨s3, hs3_c, hs3_sc, hm3'⟩ :=
    m5_otfs_opaque_state (s_old := { s2 with
      core := { s2.core with wvec := wv3, wstk := ws3, wusable := wu3 } })
      { s2.core with wvec := wv3, wstk := ws3, wusable := wu3 } s2.scratch hm3 rfl rfl
  have hs3_base : s3.core = { s.core with
      wvec := wv3, wstk := ws3, wlen := wl2, wusable := wu3, num_binary := nb2 } := by
    rw [hs3_c, hs2_c]
  have hs3_sc' : s3.scratch = { s.scratch with wsort := wso2 } := hs3_sc.trans hs2_sc
  have hw3 : Full.FullWitnessCutInv c F0 F_cur cut s3.core := by
    rw [hs3_c]; exact m5_canonCut_with_watches hw2 (hmw3 F_cur hw2.watches)
  have hlen3' : s3.LengthsOk c :=
    ⟨by rw [hs3_c]; exact hlen3.core_ok, by rw [hs3_sc]; exact hlen3.scratch_ok⟩
  have hcr4_bd : (cref.setWidth 64 + 4#64).toNat < s3.core.arena.length := by
    rw [BitVec.toNat_add, zext_toNat cref (by decide), show (4#64 : BitVec 64).toNat = 4 from rfl,
      Nat.mod_eq_of_lt (by omega), hs3_base]; dsimp only; rw [har_len]; omega
  fa_fast_steps_nogrp
  c0_call hUnw
  refine ⟨c, s3, R, rfl, hlen3', by rw [hs3_c]; exact hlay3, hm3',
    fun wv4 ws4 wu4 m4 hlen4 _ hmw4 hm4 => ?_⟩
  clear hm3'
  obtain ⟨s4, hs4_c, hs4_sc, hm4'⟩ :=
    m5_otfs_opaque_state (s_old := { s3 with
      core := { s3.core with wvec := wv4, wstk := ws4, wusable := wu4 } })
      { s3.core with wvec := wv4, wstk := ws4, wusable := wu4 } s3.scratch hm4 rfl rfl
  have hs4_base : s4.core = { s.core with
      wvec := wv4, wstk := ws4, wlen := wl2, wusable := wu4, num_binary := nb2 } := by
    rw [hs4_c, hs3_base]
  have hs4_sc' : s4.scratch = { s.scratch with wsort := wso2 } := hs4_sc.trans hs3_sc'
  have hw4 : Full.FullWitnessCutInv c F0 F_cur cut s4.core := by
    rw [hs4_c]; exact m5_canonCut_with_watches hw3 (hmw4 F_cur hw3.watches)
  have hlen4' : s4.LengthsOk c :=
    ⟨by rw [hs4_c]; exact hlen4.core_ok, by rw [hs4_sc]; exact hlen4.scratch_ok⟩
  c0_call hNext
  refine ⟨c, s4, R, rfl, hlen4', hm4', ?_⟩
  let nxt := BitVec.ofNat 32 (fullArenaNextOff s4.core.arena s4.core.arena_len cref.toNat)
  let gsz := nxt.setWidth 64 - cref.setWidth 64
  have hcr0_bd : (cref.setWidth 64).toNat < s4.core.arena.length := by
    rw [zext_toNat cref (by decide), hs4_base]; dsimp only; rw [har_len]; omega
  have hcr0_s : (cref.setWidth 64).toNat < s.core.arena.length := by
    rw [zext_toNat cref (by decide), har_len]; omega
  fa_fast_steps
  let s_lfin : FullState :=
    { s4 with
      core := { s4.core with
        arena := s4.core.arena.set (cref.setWidth 64).toNat
          (s4.core.arena[(cref.setWidth 64).toNat]'hcr0_bd ||| 0x00080000#32),
        arena_garbage := s4.core.arena_garbage + gsz,
        confl_type := 1#64, confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64,
        confl_ref := 0xFFFFFFFF#64 }
      scratch := { s4.scratch with otfs_cnt := s4.scratch.otfs_cnt + 1#64 } }
  let s_rfin : FullState :=
    { s with
      core := { s.core with
        num_binary := nb2, wvec := wv4, wstk := ws4, wlen := wl2, wusable := wu4,
        arena := s.core.arena.set (cref.setWidth 64).toNat
          (s.core.arena[(cref.setWidth 64).toNat]'hcr0_s ||| 0x00080000#32),
        arena_garbage := s.core.arena_garbage + gsz,
        confl_type := 1#64, confl_lit0 := f0.setWidth 64, confl_lit1 := f1.setWidth 64,
        confl_ref := 0xFFFFFFFF#64 }
      scratch := { s.scratch with wsort := wso2, otfs_cnt := s.scratch.otfs_cnt + 1#64 } }
  have hhar : s4.core.arena = s.core.arena := by rw [hs4_base]
  have har_set_eq : s4.core.arena.set (cref.setWidth 64).toNat
      (s4.core.arena[(cref.setWidth 64).toNat]'hcr0_bd ||| 0x00080000#32) =
      s.core.arena.set (cref.setWidth 64).toNat
      (s.core.arena[(cref.setWidth 64).toNat]'hcr0_s ||| 0x00080000#32) := by
    have hval : s4.core.arena[(cref.setWidth 64).toNat]'hcr0_bd =
        s.core.arena[(cref.setWidth 64).toNat]'hcr0_s := m5_list_getElem_of_list_idx hhar rfl
    rw [hval, hhar]
  have hfin_c : s_lfin.core = s_rfin.core := by
    dsimp only [s_lfin, s_rfin]; rw [har_set_eq, hs4_base]
  have hfin_sc : s_lfin.scratch = s_rfin.scratch := by
    dsimp only [s_lfin, s_rfin]; rw [hs4_sc']
  refine m5_otfs_bin_mark_fin hw hnd hcref hng hiu_cut hiu_te ht_u hr_u hlev_u
    hf0_m hf1_m hf0_u hf1_u hf0_lt hf1_lt hent_f har_len h2cv_lt hcr0_s
    (by rw [← hs4_base, ← hs4_sc']; exact hlen4')
    (by rw [← hs4_base]; exact hw4)
    (m5_fullMem_of_eq (by assumption) hfin_c hfin_sc) hQ

theorem full_otfs_bin_m5_wp (Γ : Env)
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ args m Q X, Full.fullOtfsBinSpec args m Q X →
      Func.wp Γ full_otfs_bin_m5_body args m Q X := by
  rintro ⟨h, cref, uip, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, idx_u, s, R, rfl, hlen, hw, hnd, hdm, hcref, hng, huip_lt,
      hiu_cut, ht_u, hr_u, hlev_u, hent, hm, hQ⟩
  have hiu_te : idx_u < s.core.trail_end := Nat.lt_of_lt_of_le hiu_cut hw.cut_le
  have hwf := hw.arena.refs_wf cref.toNat hcref
  have hcv_le := hlen.core_ok.cur_vars_le; have hmaxv := c.hmaxv; have harena := c.harena
  have hwcap := c.hwcap; unfold dimacsBound at hmaxv harena hwcap
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hlvl_len := hlen.core_ok.lvl_len
  have hwvec_len := hlen.core_ok.wvec_len; have hwstk_len := hlen.core_ok.wstk_len_arr
  have hwl_le := hlen.core_ok.wlen_le
  have h2cv_lt : 2 * s.core.cur_vars < 2 ^ 31 - 1 := by omega
  obtain ⟨old_sz, h_old_sz⟩ : ∃ n, n = fullArenaClauseSizeCore s.core cref.toNat := ⟨_, rfl⟩
  have hsz_lt_ar : cref.toNat + 3 + old_sz ≤ s.core.arena.length := by rw [h_old_sz]; omega
  have hcref_bd : cref.toNat + 2 < s.core.arena.length := by omega
  have hsz_get : s.core.arena[cref.toNat + 2]'(by omega) = BitVec.ofNat 32 old_sz := by
    apply BitVec.eq_of_toNat_eq
    have hlt32 : old_sz < 2 ^ 32 := by
      rw [h_old_sz]; exact (s.core.arena[cref.toNat + 2]?.getD 0#32).isLt
    rw [bv32_ofNat_toNat hlt32, h_old_sz]
    unfold fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hlits_info : ∀ j (hj : j < old_sz),
      let ot := s.core.arena[cref.toNat + 3 + j]'(by omega)
      ot.toNat ∈ fullArenaClauseLits s cref.toNat ∧ ot.toNat < 2 * s.core.cur_vars ∧
      ot ≠ 0xFFFFFFFF#32 := fun j hj => by
    have hmem : (s.core.arena[cref.toNat + 3 + j]'(by omega)).toNat ∈
        fullArenaClauseLitsCore s.core cref.toNat :=
      (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨j, h_old_sz ▸ hj, rfl⟩
    have hlt := hw.arena.lits_lt cref.toNat hcref hng _ hmem
    exact ⟨hmem, hlt, bv32_lit_neq_ff (by omega)⟩
  have hnodup_j : ∀ j1 j2 (h1 : j1 < old_sz) (h2 : j2 < old_sz), j1 ≠ j2 →
      s.core.arena[cref.toNat + 3 + j1]'(by omega) ≠
      s.core.arena[cref.toNat + 3 + j2]'(by omega) :=
    fun j1 j2 h1 h2 hne heq => by
      have hndc := hnd cref.toNat hcref hng
      let raw := (s.core.arena.drop (cref.toNat + 3)).take old_sz
      have hraw_len : raw.length = old_sz := by
        simp [raw, List.length_take, List.length_drop]; omega
      have hnd_raw : (raw.map fun l : BitVec 32 => l.toNat / 2).Nodup := by
        simpa [fullArenaClauseLits, fullArenaClauseLitsCore, h_old_sz, raw, List.map_map,
          Function.comp_def] using hndc
      have hraw_eq : ∀ j (hj : j < old_sz),
          raw[j]'(hraw_len ▸ hj) = s.core.arena[cref.toNat + 3 + j]'(by omega) :=
        fun j hj => by simp [raw, List.getElem_take, List.getElem_drop]
      have hij := nodup_map_getElem_inj (fun l : BitVec 32 => l.toNat / 2)
        (hraw_len ▸ h1) (hraw_len ▸ h2) hnd_raw (by rw [hraw_eq j1 h1, hraw_eq j2 h2, heq])
      exact hne hij
  have hret_same : Q (false, ()) m :=
    hQ false s.core.arena s.core.arena_garbage s.core.wvec s.core.wstk s.core.wlen s.core.wusable
      s.core.num_binary s.core.confl_type s.core.confl_ref s.core.confl_lit0 s.core.confl_lit1
      s.core.oom s.scratch m hlen (m5_canonCut_shrink_cut hw (Nat.le_of_lt hiu_cut)) hnd
      ⟨rfl, rfl⟩ rfl rfl rfl rfl (fun hc => by cases hc) hm
  unfold Func.wp full_otfs_bin_m5_body
  fa_fast_steps_nogrp
  refine wp_join_group (ts := [i32, i32, i32]) (fun p ml =>
      let f0 := p.1; let f1 := p.2.1
      ml = m ∧ ((f0 = 0xFFFFFFFF#32 ∨ f1 = 0xFFFFFFFF#32) ∨
        (f0.toNat ∈ fullArenaClauseLits s cref.toNat ∧
         f1.toNat ∈ fullArenaClauseLits s cref.toNat ∧
         f0 ≠ uip ∧ f1 ≠ uip ∧ f0 ≠ f1 ∧
         0 < (s.core.lvl[f0.toNat / 2]?.getD 0#32).toNat ∧
         0 < (s.core.lvl[f1.toNat / 2]?.getD 0#32).toNat))) ?_ ?_
  · rintro _ ⟨f0, f1, _iv, ⟨⟩⟩ ml ⟨hml, hpost⟩
    subst ml
    dsimp only at hpost
    rcases hpost with hf_eq | ⟨hf0_m, hf1_m, hf0_u, hf1_u, hf_ne, hl0_pos, hl1_pos⟩
    · c0_let_simp
      refine wp_jnz_of (fun _ => hret_same) (fun hne0 => ?_)
      c0_let_simp
      refine wp_jnz_of (fun _ => hret_same) (fun hne1 => ?_)
      rcases hf_eq with h0 | h1
      · exact absurd h0 (by simpa using hne0)
      · exact absurd h1 (by simpa using hne1)
    · have hf0_lt : f0.toNat < 2 * s.core.cur_vars := hw.arena.lits_lt cref.toNat hcref hng _ hf0_m
      have hf1_lt : f1.toNat < 2 * s.core.cur_vars := hw.arena.lits_lt cref.toNat hcref hng _ hf1_m
      have hf0_31 : f0.toNat < 2 ^ 31 - 1 := Nat.lt_trans hf0_lt h2cv_lt
      have hf1_31 : f1.toNat < 2 ^ 31 - 1 := Nat.lt_trans hf1_lt h2cv_lt
      have hf0_ff : f0 ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hf0_31
      have hf1_ff : f1 ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hf1_31
      have hf0_2l1 : ((f0.setWidth 64 <<< BitVec.signExtend 64 1#32) + 1#64).toNat =
          2 * f0.toNat + 1 := by
        rw [m5_bv64_shl_sext1_add1 _ (by rw [zext_toNat f0 (by decide)]; omega),
          zext_toNat f0 (by decide)]
      have hf1_2l1 : ((f1.setWidth 64 <<< BitVec.signExtend 64 1#32) + 1#64).toNat =
          2 * f1.toNat + 1 := by
        rw [m5_bv64_shl_sext1_add1 _ (by rw [zext_toNat f1 (by decide)]; omega),
          zext_toNat f1 (by decide)]
      have hf0_bd1 : ((f0.setWidth 64 <<< BitVec.signExtend 64 1#32) + 1#64).toNat <
          s.core.wvec.length := by rw [hf0_2l1, hwvec_len]; omega
      have hf1_bd1 : ((f1.setWidth 64 <<< BitVec.signExtend 64 1#32) + 1#64).toNat <
          s.core.wvec.length := by rw [hf1_2l1, hwvec_len]; omega
      have hlay0 : Full.WatchStackLayout s.core := by
        have h := hw.watches; unfold ModeWatchesInv at h; rw [ite_eq_left hdm] at h; exact h.layout
      have hmw0 : Full.WatchesInv F_cur s.core := by
        have h := hw.watches; unfold ModeWatchesInv at h; rwa [ite_eq_left hdm] at h
      fa_fast_steps_nogrp
      · exfalso; exact hf0_ff ‹_›
      · exfalso; exact hf1_ff ‹_›
      · refine wp_join_group (ts := [i32]) (fun (src, ()) ml =>
            ml = m ∧ (src = f0 ∨ src = f1)) ?_ ?_
        · rintro _ ⟨src, ⟨⟩⟩ ml ⟨hml_s, hsrc_or⟩; subst ml
          have hsrc_lt : src.toNat < 2 * s.core.cur_vars :=
            hsrc_or.elim (fun h => h ▸ hf0_lt) (fun h => h ▸ hf1_lt)
          have hsrc_2l : (src.setWidth 64 <<< BitVec.signExtend 64 1#32).toNat =
              2 * src.toNat := by
            rw [m5_bv64_shl_sext1 _ (by rw [zext_toNat src (by decide)]; omega),
              zext_toNat src (by decide)]
          have hsrc_2l1 : ((src.setWidth 64 <<< BitVec.signExtend 64 1#32) + 1#64).toNat =
              2 * src.toNat + 1 := by
            rw [m5_bv64_shl_sext1_add1 _ (by rw [zext_toNat src (by decide)]; omega),
              zext_toNat src (by decide)]
          have hsrc_bd0 : (src.setWidth 64 <<< BitVec.signExtend 64 1#32).toNat <
              s.core.wvec.length := by rw [hsrc_2l, hwvec_len]; omega
          have hsrc_bd1 : ((src.setWidth 64 <<< BitVec.signExtend 64 1#32) + 1#64).toNat <
              s.core.wvec.length := by rw [hsrc_2l1, hwvec_len]; omega
          refine wp_join_group (ts := [i32]) (fun (tgt, ()) ml =>
              ml = m ∧ (tgt = f0 ∨ tgt = f1)) ?_ ?_
          · rintro _ ⟨tgt, ⟨⟩⟩ ml ⟨hml_t, _htgt⟩; subst ml
            fa_fast_steps_nogrp
            let off_s := fullWatchOffCore s.core src.toNat
            let sz_s := fullWatchSizeCore s.core src.toNat
            let pend_s := off_s + sz_s
            have hbnd_s := hlay0.bounds src.toNat hsrc_lt
            have hoff_eq : (s.core.wvec[(src.setWidth 64 <<< BitVec.signExtend 64
                1#32).toNat]'hsrc_bd0).toNat = off_s := by
              unfold off_s fullWatchOffCore
              rw [List.getElem?_eq_getElem (by rw [hwvec_len]; omega), Option.getD_some]
              exact congrArg BitVec.toNat (m5_list_getElem_of_idx hsrc_2l)
            have hsz_eq : (s.core.wvec[((src.setWidth 64 <<< BitVec.signExtend 64
                1#32) + 1#64).toNat]'hsrc_bd1).toNat = sz_s := by
              unfold sz_s fullWatchSizeCore
              rw [List.getElem?_eq_getElem (by rw [hwvec_len]; omega), Option.getD_some]
              exact congrArg BitVec.toNat (m5_list_getElem_of_idx hsrc_2l1)
            have hoff64 : (BitVec.setWidth 64 (s.core.wvec[(src.setWidth 64 <<<
                BitVec.signExtend 64 1#32).toNat]'hsrc_bd0)).toNat = off_s := by
              rw [zext_toNat _ (by decide), hoff_eq]
            have hsz64 : (BitVec.setWidth 64 (s.core.wvec[((src.setWidth 64 <<<
                BitVec.signExtend 64 1#32) + 1#64).toNat]'hsrc_bd1)).toNat = sz_s := by
              rw [zext_toNat _ (by decide), hsz_eq]
            have hpend64 : (BitVec.setWidth 64 (s.core.wvec[(src.setWidth 64 <<<
                  BitVec.signExtend 64 1#32).toNat]'hsrc_bd0) +
                BitVec.setWidth 64 (s.core.wvec[((src.setWidth 64 <<<
                  BitVec.signExtend 64 1#32) + 1#64).toNat]'hsrc_bd1)).toNat = pend_s := by
              rw [BitVec.toNat_add, hoff64, hsz64]; exact Nat.mod_eq_of_lt (by omega)
            refine wp_join_group (ts := [.bool, i64])
                (fun (_res, _p, ()) ml => ml = m) ?_ ?_
            · rintro _ ⟨has_bin, _pfin, ⟨⟩⟩ ml hml_hb; subst ml
              fa_fast_steps_nogrp
              have hent_f := hent f0 f1 hf0_m hf1_m hf0_u hf1_u hf_ne hl0_pos hl1_pos
              refine wp_join_group (ts := []) (fun _ ml => ∃ s2 : FullState,
                ∃ (wv2 ws2 : List (BitVec 32)) (wl2 : Nat) (wu2 nb2 : BitVec 64)
                  (wso2 : List (BitVec 32)),
                  s2.core = { s.core with wvec := wv2, wstk := ws2, wlen := wl2,
                                          wusable := wu2, num_binary := nb2 } ∧
                  s2.scratch = { s.scratch with wsort := wso2 } ∧
                  s2.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut s2.core ∧
                  (FullMem c s2 ⋆ R) ml) ?_ ?_
              · rintro _ ⟨⟩ ml ⟨s2, wv2, ws2, wl2, wu2, nb2, wso2, hs2_c, hs2_sc, hlen2, hw2, hm2⟩
                exact otfs_bin_m5_tail_wp hNext hUnw hw hnd hdm hcref hng hiu_cut hiu_te ht_u
                  hr_u hlev_u hf0_m hf1_m hf0_u hf1_u hf0_lt hf1_lt hent_f har_len h2cv_lt
                  hs2_c hs2_sc hlen2 hw2 hm2 hQ
              · intro Jw hJw
                fa_fast_steps_nogrp
                · exact hJw () m ⟨s, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable,
                    s.core.num_binary, s.scratch.wsort, rfl, rfl, hlen, hw, hm⟩
                · -- `!has_bin` headroom pre-check: `m5_wstack_ensure2_ret_false_wp`
                  refine wp_join_group (ts := []) (fun _ ml_d =>
                    ∃ (s_d : FullState) (wv_d ws_d : List (BitVec 32)) (wl_d : Nat)
                      (wu_d : BitVec 64) (wso_d : List (BitVec 32)),
                      s_d.core = { s.core with wvec := wv_d, wstk := ws_d, wlen := wl_d,
                                               wusable := wu_d } ∧
                      s_d.scratch = { s.scratch with wsort := wso_d } ∧
                      s_d.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut s_d.core ∧
                      (FullMem c s_d ⋆ R) ml_d) ?_ ?_
                  · rintro _ ⟨⟩ ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc,
                      hlen_d, hw_d, hm_d⟩
                    clear hm
                    have hb0_p := bin_rsn_mask_props (l := f1) hf1_31
                    have hb1_p := bin_rsn_mask_props (l := f0) hf0_31
                    let b0 := (f1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
                    let b1 := (f0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
                    have hent_sym :
                        (cnfOfClauses F_cur).EntailsClause (cnfClause [f1.toNat, f0.toNat]) :=
                      entails_of_mem_or_false hent_f fun l hl => by
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
                        exact Or.inl (by rcases hl with rfl | rfl <;> simp)
                    have hsd_dm : s_d.core.dense_mode = 0#64 := by rw [hsd_c]; exact hdm
                    have hlay_d : Full.WatchStackLayout s_d.core := by
                      have h := hw_d.watches; unfold ModeWatchesInv at h
                      rw [ite_eq_left hsd_dm] at h; exact h.layout
                    fa_fast_steps_nogrp
                    refine wp_join_group (ts := []) (fun _ ml_o =>
                      ∃ (wv_o ws_o : List (BitVec 32)) (wl_o : Nat)
                        (wu_o : BitVec 64) (wso_o : List (BitVec 32)),
                        let s_o : FullState :=
                          { s with
                            core := { s.core with wvec := wv_o, wstk := ws_o, wlen := wl_o,
                                                  wusable := wu_o }
                            scratch := { s.scratch with wsort := wso_o } }
                        s_o.LengthsOk c ∧
                        Full.FullWitnessCutInv c F0 F_cur cut s_o.core ∧
                        (FullMem c s_o ⋆ R) ml_o)
                      (fun _ ⟨⟩ ml_o ⟨wv_o, ws_o, wl_o, wu_o, wso_o, hlen_o, hw_o, hm_o⟩ => by
                        fa_fast_steps
                        exact m5_otfs_bin_oom_exit (wv := wv_o) (ws := ws_o) (wl := wl_o)
                          (wu := wu_o) (wso := wso_o) hiu_cut hnd hlen_o hw_o
                          (by assumption) hQ) ?_
                    intro J_oom hJoom
                    c0_call hPush
                    refine ⟨c, s_d, R, rfl, hlen_d, hlay_d,
                      (fun _ => hb0_p.1), (fun hk => by cases hk), hm_d,
                      fun ok1 wv1 ws1 wl1 wu1 wso1 m1 hlen1 hlay1 hother1 hok1t hok1f hm1 => ?_⟩
                    clear hm_d
                    let s1 : FullState :=
                      { s_d with
                        core := { s_d.core with wvec := wv1, wstk := ws1, wlen := wl1,
                                                wusable := wu1 }
                        scratch := { s_d.scratch with wsort := wso1 } }
                    have hs1_c : s1.core = { s.core with
                        wvec := wv1, wstk := ws1, wlen := wl1, wusable := wu1 } := by
                      dsimp only [s1]; rw [hsd_c]
                    have hs1_sc : s1.scratch = { s.scratch with wsort := wso1 } := by
                      dsimp only [s1]; rw [hsd_sc]
                    have hw_k1 : ModeWatchesInv F_cur s1.core := by
                      by_cases hok1 : ok1 = true
                      · subst hok1; obtain ⟨_, _, hsz1, hsame1, hw01, _⟩ := hok1t rfl
                        exact fa_watchPush_bin_preserves hsd_dm hw_d.watches (lit := f0.toNat)
                          (w0 := b0) (nb' := s_d.core.num_binary) (oom' := s_d.core.oom)
                          (by rw [hsd_c]; exact hf0_lt) hlay1 hother1 hsz1 hsame1 hw01
                          hb0_p.2.1 hb0_p.1 (by rw [hb0_p.2.2, hsd_c]; exact hf1_lt)
                          (by rw [hb0_p.2.2]; exact hent_f)
                      · have hokf : ok1 = false := Bool.eq_false_iff.mpr hok1
                        obtain ⟨hsame_f, _⟩ := hok1f hokf
                        exact fa_watchPush_fail_preserves hsd_dm hw_d.watches hlay1 fun l hl =>
                          if hle : l = f0.toNat then
                            by subst l; exact hsame_f (by rw [hsd_c]; exact hf0_lt)
                          else hother1 l hl hle
                    have hw1 : Full.FullWitnessCutInv c F0 F_cur cut s1.core :=
                      m5_canonCut_with_watches hw_d hw_k1
                    have hs1_dm : s1.core.dense_mode = 0#64 := by rw [hs1_c]; exact hdm
                    by_cases hok1 : ok1 = true
                    · subst hok1; clear hok1t hok1f
                      fa_fast_steps_nogrp
                      c0_call hPush
                      refine ⟨c, s1, R, rfl, hlen1, hlay1,
                        (fun _ => hb1_p.1), (fun hk => by cases hk), hm1,
                        fun ok2 wv2 ws2 wl2 wu2 wso2 m2 hlen2 hlay2 hother2 hok2t hok2f hm2 => ?_⟩
                      clear hm1
                      let s2 : FullState :=
                        { s1 with
                          core := { s1.core with wvec := wv2, wstk := ws2, wlen := wl2,
                                                 wusable := wu2 }
                          scratch := { s1.scratch with wsort := wso2 } }
                      have hs2_c : s2.core = { s.core with
                          wvec := wv2, wstk := ws2, wlen := wl2, wusable := wu2 } := by
                        dsimp only [s2]; rw [hs1_c]
                      have hs2_sc : s2.scratch = { s.scratch with wsort := wso2 } := by
                        dsimp only [s2]; rw [hs1_sc]
                      have hw_k2 : ModeWatchesInv F_cur s2.core := by
                        by_cases hok2 : ok2 = true
                        · subst hok2; obtain ⟨_, _, hsz2, hsame2, hw02, _⟩ := hok2t rfl
                          exact fa_watchPush_bin_preserves hs1_dm hw1.watches (lit := f1.toNat)
                            (w0 := b1) (nb' := s1.core.num_binary) (oom' := s1.core.oom)
                            (by rw [hs1_c]; exact hf1_lt) hlay2 hother2 hsz2 hsame2 hw02
                            hb1_p.2.1 hb1_p.1 (by rw [hb1_p.2.2, hs1_c]; exact hf0_lt)
                            (by rw [hb1_p.2.2]; exact hent_sym)
                        · have hokf : ok2 = false := Bool.eq_false_iff.mpr hok2
                          obtain ⟨hsame_f, _⟩ := hok2f hokf
                          exact fa_watchPush_fail_preserves hs1_dm hw1.watches hlay2 fun l hl =>
                            if hle : l = f1.toNat then
                              by subst l; exact hsame_f (by rw [hs1_c]; exact hf1_lt)
                            else hother2 l hl hle
                      have hw2 : Full.FullWitnessCutInv c F0 F_cur cut s2.core :=
                        m5_canonCut_with_watches hw1 hw_k2
                      by_cases hok2 : ok2 = true
                      · subst hok2
                        fa_fast_steps
                        let s2_nb : FullState :=
                          { s2 with
                            core := { s2.core with num_binary := s2.core.num_binary + 1#64 } }
                        have hnb_c : s2_nb.core = { s.core with
                            wvec := wv2, wstk := ws2, wlen := wl2, wusable := wu2,
                            num_binary := s.core.num_binary + 1#64 } := by
                          dsimp only [s2_nb]; rw [hs2_c]
                        have hnb_len : s2_nb.LengthsOk c :=
                          ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩
                        have hw2' : Full.FullWitnessCutInv c F0 F_cur cut
                            { s.core with wvec := wv2, wstk := ws2, wlen := wl2,
                                          wusable := wu2 } := hs2_c ▸ hw2
                        have hnb_hw : Full.FullWitnessCutInv c F0 F_cur cut s2_nb.core := by
                          rw [hnb_c]
                          exact { hw2' with
                            arena := { hw2'.arena with len_ok := hw2'.arena.len_ok }
                            watches := hw2'.watches.with_wstk rfl rfl rfl rfl rfl
                              fun _ hr => hr }
                        exact hJw () _ ⟨s2_nb, wv2, ws2, wl2, wu2, s.core.num_binary + 1#64, wso2,
                          hnb_c, hs2_sc, hnb_len, hnb_hw, by assumption⟩
                      · have hok2f : ok2 = false := Bool.eq_false_iff.mpr hok2
                        subst hok2f
                        fa_fast_steps
                        have h2_len : ({ s with
                            core := { s.core with wvec := wv2, wstk := ws2, wlen := wl2,
                                                  wusable := wu2 }
                            scratch := { s.scratch with wsort := wso2 } } : FullState).LengthsOk
                            c := by
                          rw [← hs2_c, ← hs2_sc]; exact hlen2
                        have hw2_o : Full.FullWitnessCutInv c F0 F_cur cut
                            { s.core with wvec := wv2, wstk := ws2, wlen := wl2,
                                          wusable := wu2 } := hs2_c ▸ hw2
                        exact hJoom () _ ⟨wv2, ws2, wl2, wu2, wso2, h2_len, hw2_o,
                          m5_fullMem_of_eq hm2 hs2_c hs2_sc⟩
                    · have hok1f : ok1 = false := Bool.eq_false_iff.mpr hok1
                      subst hok1f
                      fa_fast_steps
                      have h1_len : ({ s with
                          core := { s.core with wvec := wv1, wstk := ws1, wlen := wl1,
                                                wusable := wu1 }
                          scratch := { s.scratch with wsort := wso1 } } : FullState).LengthsOk
                          c := by
                        rw [← hs1_c, ← hs1_sc]; exact hlen1
                      have hw1_o : Full.FullWitnessCutInv c F0 F_cur cut
                          { s.core with wvec := wv1, wstk := ws1, wlen := wl1,
                                        wusable := wu1 } := hs1_c ▸ hw1
                      exact hJoom () _ ⟨wv1, ws1, wl1, wu1, wso1, h1_len, hw1_o,
                        m5_fullMem_of_eq hm1 hs1_c hs1_sc⟩
                  · intro Jd hJd
                    exact m5_wstack_ensure2_ret_false_wp hDefrag hlen hdm hw.watches hm
                      (fun s_i wv_i ws_i wl_i wu_i wso_i ml_o hsi_c hsi_sc hlen_i hmw_i hm_o =>
                        m5_otfs_bin_oom_exit (wv := wv_i) (ws := ws_i) (wl := wl_i) (wu := wu_i)
                          (wso := wso_i) hiu_cut hnd
                          ⟨by have h := hlen_i.core_ok; rw [hsi_c] at h; exact h,
                           by have h := hlen_i.scratch_ok; rw [hsi_sc] at h; exact h⟩
                          (by rw [hsi_c] at hmw_i; exact m5_canonCut_with_watches hw hmw_i)
                          (m5_fullMem_of_eq hm_o (by dsimp only; rw [hsi_c])
                            (by dsimp only; exact hsi_sc))
                          hQ)
                      (fun xs ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc,
                          hlen_d, hmw_d, hm_d⟩ =>
                        hJd xs ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc,
                          hlen_d, by
                            rw [hsd_c] at hmw_d ⊢; exact m5_canonCut_with_watches hw hmw_d, hm_d⟩)
            · intro Jb hJb
              refine wp_loop_group (fun r (pv, ()) ml =>
                  ml = m ∧ r = pend_s - pv.toNat ∧
                  off_s ≤ pv.toNat ∧ pv.toNat ≤ pend_s ∧
                  Full.WatchSliceOk F_cur s.core src.toNat pv.toNat
                    (pend_s - pv.toNat)) ?_ ?_
              · rintro L r ⟨pv, ⟨⟩⟩ ml ih ⟨hml_l, rfl, hlo, hhi, hsl⟩; subst ml
                fa_fast_steps_nogrp
                · have hp_lt : pv.toNat < pend_s := by
                    have hbd0' : 2 * src.toNat % 2 ^ 64 < s.core.wvec.length := by
                      rw [Nat.mod_eq_of_lt (by omega), hwvec_len]; omega
                    have hbd1' : (2 * src.toNat + 1) % 2 ^ 64 < s.core.wvec.length := by
                      rw [Nat.mod_eq_of_lt (by omega), hwvec_len]; omega
                    have hc0 : pv.toNat < (s.core.wvec[2 * src.toNat % 2 ^ 64]'hbd0').toNat +
                        (s.core.wvec[(2 * src.toNat + 1) % 2 ^ 64]'hbd1').toNat :=
                      Nat.lt_of_lt_of_le (‹pv.toNat < _› : pv.toNat <
                        ((s.core.wvec[2 * src.toNat % 2 ^ 64]'hbd0').toNat +
                          (s.core.wvec[(2 * src.toNat + 1) % 2 ^ 64]'hbd1').toNat) % 2 ^ 64)
                        (Nat.mod_le _ _)
                    have he0 : s.core.wvec[2 * src.toNat % 2 ^ 64]'hbd0' =
                        s.core.wvec[(src.setWidth 64 <<<
                          BitVec.signExtend 64 1#32).toNat]'hsrc_bd0 :=
                      getElem_eq_of_idx (by rw [hsrc_2l, Nat.mod_eq_of_lt (by omega)])
                    have he1 : s.core.wvec[(2 * src.toNat + 1) % 2 ^ 64]'hbd1' =
                        s.core.wvec[((src.setWidth 64 <<<
                          BitVec.signExtend 64 1#32) + 1#64).toNat]'hsrc_bd1 :=
                      getElem_eq_of_idx (by rw [hsrc_2l1, Nat.mod_eq_of_lt (by omega)])
                    rw [he0, he1, hoff_eq, hsz_eq] at hc0; exact hc0
                  have hpw : pv.toNat < s.core.wstk.length := by rw [hwstk_len]; omega
                  let w0 := s.core.wstk[pv.toNat]'hpw
                  fa_fast_steps_nogrp
                  refine wp_join_group (ts := [.bool, i64])
                      (fun (br, pv', ()) ml' =>
                        ml' = m ∧ br = false ∧ pend_s - pv'.toNat < pend_s - pv.toNat ∧
                        off_s ≤ pv'.toNat ∧ pv'.toNat ≤ pend_s ∧
                        Full.WatchSliceOk F_cur s.core src.toNat pv'.toNat
                          (pend_s - pv'.toNat))
                      ?_ ?_
                  · rintro _ ⟨br, pv', ⟨⟩⟩ ml' ⟨hml', hbr, hdec', hlo', hhi', hsl'⟩
                    subst ml'; subst br
                    fa_fast_steps
                    exact ih (pend_s - pv'.toNat) (pv', ()) m hdec' ⟨rfl, rfl, hlo', hhi', hsl'⟩
                  · intro J_s hJs
                    fa_fast_steps
                    · exact hJb (true, pv, ()) m rfl
                    · have hfl : (w0 &&& 0x80000000#32) ≠ 0#32 := by assumption
                      rcases m5_watchSlice_bin_tail hsl (by omega) with
                        ⟨w', hw', _, _, _, _, hrest⟩ |
                        ⟨_, w', _, hw', _, hfl0, _, _, _⟩
                      · rw [List.getElem?_eq_getElem hpw, Option.some.injEq] at hw'
                        subst w'
                        have hp1 : (pv + 1#64).toNat = pv.toNat + 1 :=
                          m5_bv64_add1_nat pv (by omega)
                        exact hJs (false, pv + 1#64, ()) m
                          ⟨rfl, rfl, by rw [hp1]; omega, by rw [hp1]; omega,
                           by rw [hp1]; omega,
                           by rw [hp1, show pend_s - (pv.toNat + 1) =
                               pend_s - pv.toNat - 1 by omega]
                              exact hrest⟩
                      · rw [List.getElem?_eq_getElem hpw, Option.some.injEq] at hw'
                        subst w'; exact absurd hfl0 hfl
                    · have hfl0 : (w0 &&& 0x80000000#32) = 0#32 := by assumption
                      rcases m5_watchSlice_bin_tail hsl (by omega) with
                        ⟨w', hw', hfl, _⟩ |
                        ⟨h2le, w', _, hw', _, _, _, _, hrest⟩
                      · rw [List.getElem?_eq_getElem hpw, Option.some.injEq] at hw'
                        subst w'; exact absurd hfl0 hfl
                      · have hp2 : (pv + 2#64).toNat = pv.toNat + 2 := by
                          rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]
                          exact Nat.mod_eq_of_lt (by omega)
                        exact hJs (false, pv + 2#64, ()) m
                          ⟨rfl, rfl, by rw [hp2]; omega, by rw [hp2]; omega,
                           by rw [hp2]; omega,
                           by rw [hp2, show pend_s - (pv.toNat + 2) =
                               pend_s - pv.toNat - 2 by omega]
                              exact hrest⟩
                · fa_fast_steps; exact hJb (false, pv, ()) m rfl
              · intro L hL; fa_fast_steps
                have hshl1_n : (src.setWidth 64 <<< BitVec.signExtend 64 1#32) =
                    src.setWidth 64 <<< (1 : Nat) := by
                  apply BitVec.eq_of_toNat_eq
                  rw [hsrc_2l, m5_bv64_shl1_nat _ (by rw [zext_toNat src (by decide)]; omega),
                    zext_toNat src (by decide)]
                have hsrc_bd0_n : (src.setWidth 64 <<< (1 : Nat)).toNat < s.core.wvec.length := by
                  rw [← hshl1_n]; exact hsrc_bd0
                have hoff64_1 : (BitVec.setWidth 64 (s.core.wvec[(src.setWidth 64 <<<
                    (1 : Nat)).toNat]'hsrc_bd0_n)).toNat = off_s := by
                  simpa only [← hshl1_n] using hoff64
                exact hL sz_s (BitVec.setWidth 64 (s.core.wvec[(src.setWidth 64 <<<
                    (1 : Nat)).toNat]'hsrc_bd0_n), ()) m
                  ⟨rfl, by rw [hoff64_1]; unfold pend_s; omega,
                   by rw [hoff64_1]; exact Nat.le_refl _,
                   by rw [hoff64_1]; unfold pend_s; omega,
                   by rw [hoff64_1, show pend_s - off_s = sz_s by unfold pend_s; omega]
                      exact hmw0.slices src.toNat hsrc_lt⟩
          · intro Jt hJt; fa_fast_steps
            · exact hJt _ _ ⟨rfl, Or.inr rfl⟩
            · exact hJt _ _ ⟨rfl, Or.inl rfl⟩
        · intro Js hJs; fa_fast_steps
          · exact hJs _ _ ⟨rfl, Or.inl rfl⟩
          · exact hJs _ _ ⟨rfl, Or.inr rfl⟩
  · intro J hJ; fa_fast_steps_nogrp
    refine wp_loop_group (fun r (f0, iv, ()) ml => ∃ i : Nat,
      ml = m ∧ r = old_sz - i ∧ i ≤ old_sz ∧ iv = BitVec.ofNat 32 i ∧
      (f0 = 0xFFFFFFFF#32 ∨ ∃ j < i,
        f0 = s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ∧
        f0 ≠ uip ∧ 0 < (s.core.lvl[f0.toNat / 2]?.getD 0#32).toNat)) ?_ ?_
    · rintro L r ⟨f0, iv, ⟨⟩⟩ ml ih ⟨i, rfl, rfl, hile, rfl, hf0⟩
      fa_fast_steps_nogrp
      · have hcr2_z : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by
          rw [BitVec.toNat_add, zext_toNat cref (by decide)]; simp; omega
        have hcr2_bd : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by
          rw [hcr2_z]; omega
        have hilt : i < old_sz := by
          have hb : (BitVec.ofNat 32 i).toNat <
              (s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bd).toNat := ‹_›
          rw [bv32_ofNat_toNat (by omega)] at hb
          rwa [m5_list_getElem_of_idx (hj := by omega) hcr2_z, hsz_get,
            bv32_ofNat_toNat (by omega)] at hb
        obtain ⟨hot_mem, hot_lt, _hot_ff⟩ := hlits_info i hilt
        let ot := s.core.arena[cref.toNat + 3 + i]'(by omega)
        have hot_get : ot = s.core.arena[cref.toNat + 3 + i]?.getD 0#32 := by
          dsimp only [ot]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        have hcr_i_z : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat =
            cref.toNat + 3 + i := by
          rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cref (by decide),
            zext_toNat _ (by decide), bv32_ofNat_toNat (by omega)]
          simp only [BitVec.reduceToNat]; omega
        have hcr_i_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 i).setWidth 64).toNat <
            s.core.arena.length := by rw [hcr_i_z]; omega
        have hot_idx_eq : s.core.arena[(cref.setWidth 64 + 3#64 +
            (BitVec.ofNat 32 i).setWidth 64).toNat]'hcr_i_bd = ot :=
          m5_list_getElem_of_idx hcr_i_z
        have hot_lvl_lt : (s.core.arena[(cref.setWidth 64 + 3#64 +
            (BitVec.ofNat 32 i).setWidth 64).toNat]'hcr_i_bd).toNat / 2 < s.core.cur_vars := by
          rw [hot_idx_eq]; exact Nat.div_lt_of_lt_mul hot_lt
        have hc_idx : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i % 2 ^ 32) % 2 ^ 64 =
            cref.toNat + 3 + i := by
          simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
        have hot_c0_eq : s.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
            i % 2 ^ 32) % 2 ^ 64]'(by rw [hc_idx]; omega) = ot :=
          m5_list_getElem_of_idx hc_idx
        have hot_lvl_c0 : (s.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
            i % 2 ^ 32) % 2 ^ 64]'(by rw [hc_idx]; omega)).toNat / 2 < s.core.cur_vars := by
          rw [hot_c0_eq]; exact Nat.div_lt_of_lt_mul hot_lt
        fa_fast_steps_nogrp
        refine wp_join_group (ts := [i32, i32]) (fun p ml_post =>
            let f0' := p.1
            ml_post = ml ∧
            (f0' = 0xFFFFFFFF#32 ∨ ∃ j < i + 1,
              f0' = s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ∧
              f0' ≠ uip ∧ 0 < (s.core.lvl[f0'.toNat / 2]?.getD 0#32).toNat)) ?_ ?_
        · rintro _ ⟨f0', _f1, ⟨⟩⟩ ml_post ⟨rfl, hf0'⟩
          fa_fast_steps
          rw [m5_bv32_ofNat_add1]
          exact ih (old_sz - (i + 1)) _ ml_post (by omega) ⟨i + 1, rfl, rfl, by omega, rfl, hf0'⟩
        · intro J2 hJ2; fa_fast_steps
          · have hot_v_lvl : ot.toNat / 2 < s.core.lvl.length := by
              rw [hlvl_len]; exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hot_lt) hcv_le
            have hpos_ot : 0 < (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat := by
              rw [List.getElem?_eq_getElem hot_v_lvl, Option.getD_some]
              exact Nat.lt_of_lt_of_eq ‹BitVec.toNat 0 < _› (congrArg BitVec.toNat
                (m5_list_getElem_of_idx (congrArg (fun x : BitVec 32 => x.toNat / 2)
                  (m5_list_getElem_of_idx hc_idx))))
            have hot_ne_uip : ot ≠ uip := fun he =>
              ‹¬ _ = uip› ((m5_list_getElem_of_idx hc_idx).trans he)
            have h_ot_g (pf) : s.core.arena[(cref.setWidth 64 + 3 +
                (BitVec.ofNat 32 i).setWidth 64).toNat]'pf = ot := m5_list_getElem_of_idx hcr_i_z
            rw [h_ot_g]
            exact hJ2 (ot, 0xFFFFFFFF#32, ()) ml
              ⟨rfl, Or.inr ⟨i, Nat.lt_succ_self i, hot_get, hot_ne_uip, hpos_ot⟩⟩
          · have hot_v_lvl : ot.toNat / 2 < s.core.lvl.length := by
              rw [hlvl_len]; exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul hot_lt) hcv_le
            have hpos_ot : 0 < (s.core.lvl[ot.toNat / 2]?.getD 0#32).toNat := by
              rw [List.getElem?_eq_getElem hot_v_lvl, Option.getD_some]
              exact Nat.lt_of_lt_of_eq ‹BitVec.toNat 0 < _› (congrArg BitVec.toNat
                (m5_list_getElem_of_idx (congrArg (fun x : BitVec 32 => x.toNat / 2)
                  (m5_list_getElem_of_idx hc_idx))))
            have hot_ne_uip : ot ≠ uip := fun he =>
              ‹¬ _ = uip› ((m5_list_getElem_of_idx hc_idx).trans he)
            have h_ot_g (pf) : s.core.arena[(cref.setWidth 64 + 3 +
                (BitVec.ofNat 32 i).setWidth 64).toNat]'pf = ot := m5_list_getElem_of_idx hcr_i_z
            rcases hf0 with rfl | ⟨j, hj, rfl, hju, hjl⟩
            · exfalso; exact ‹¬ (0xFFFFFFFF#32 = 0xFFFFFFFF#32)› rfl
            · have hj_get : s.core.arena[cref.toNat + 3 + j]?.getD 0#32 =
                  s.core.arena[cref.toNat + 3 + j]'(by omega) := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hf_ne : s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ ot := by
                rw [hj_get]; exact hnodup_j j i (by omega) hilt (by omega)
              have hj_info := hlits_info j (by omega)
              rw [← hj_get] at hj_info
              rw [h_ot_g]
              exact hJ (s.core.arena[cref.toNat + 3 + j]?.getD 0#32, ot, BitVec.ofNat 32 i, ()) ml
                ⟨rfl, Or.inr ⟨hj_info.1, hot_mem, hju, hot_ne_uip, hf_ne, hjl, hpos_ot⟩⟩
          · exact hJ2 _ _ ⟨rfl, hf0.imp_right fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩⟩
          · exact hJ2 _ _ ⟨rfl, hf0.imp_right fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩⟩
      · fa_fast_steps; exact hJ _ _ ⟨rfl, Or.inl (Or.inr rfl)⟩
    · intro L hL; fa_fast_steps
      exact hL old_sz (0xFFFFFFFF#32, 0#32, ()) m
        ⟨0, rfl, rfl, Nat.zero_le _, rfl, Or.inl rfl⟩

end OtfsBinM5Proof

/-! ## 2. `full_deduce_1uip_m5_wp` (`Full.fullDeduce1uipSpec`) -/

section Deduce1UipM5Proof

private theorem m5_deduce_seed_wp {Γ : Env}
    (hAlit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, Full.fullAnalyzeRsnSpec a m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {s : FullState} {R : Mem 64 → Prop} {X : XPost} {m0 : Mem 64}
    {Js : Tup Cont [[.bool]]}
    (hinv : Full.FullCutInvW c F0 F_cur cut s) (hcur_pos : 0 < s.core.cur_level)
    (hconfl : Full.FullConflictOkCut F_cur cut s)
    (hm0 : (FullMem c { s with
      core := { s.core with tmp_cnt := 0, tmp_len := 1, min_clr_len := 0 },
      scratch := { s.scratch with ant_sz := 0#64, res_sz := 0#64 } } ⋆ R) m0)
    (hJsd : ∀ seed_ok m_sd,
      (∃ s1 : FullState,
        s1.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut s1.core ∧
        Full.FullAnaMarksCov c s1 ∧ Full.FullExtScratchPres s s1 ∧
        s1.scratch.work_stk2 = s.scratch.work_stk2 ∧ Full.FullArenaVarsNodup s1 ∧
        fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧ Full.FullDeduceStaticEq s.core s1.core ∧
        1 ≤ s1.core.tmp_len ∧ s1.core.tmp_len ≤ s1.core.cur_vars ∧
        s1.core.confl_type = s.core.confl_type ∧ s1.core.confl_ref = s.core.confl_ref ∧
        (seed_ok = true → Full.FullDeduceStateInv c F0 F_cur cut s1.core.trail_end s s1) ∧
        (FullMem c s1 ⋆ R) m_sd) →
      Js.fst (seed_ok, ()) m_sd) :
    wp (rs := [i64]) Γ (fun _ _ => False) X
      (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 528, ())) fun p6 =>
        .load i64 (Arg.var p6.fst) fun ld =>
          .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var ld, Arg.imm 1#64, ())) fun p7 =>
            .jnz (Arg.var p7.fst)
              (.group (sig := [[.bool]])
                (fun _Js1 => .cons (fun p => .jump Js.fst (Arg.var p.fst, ())) .nil)
                fun Js1 => .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 536, ())) fun p8 =>
                  .load i64 (Arg.var p8.fst) fun ld =>
                    .let_ (Op.mk (.trunc 64 32) (Arg.var ld, ())) fun p9 =>
                      .call (as := [i64, i32, i32]) (bs := [.bool]) "full_analyze_lit"
                        (Arg.var c.hdr, Arg.var p9.fst, Arg.imm 0xFFFFFFFF#32, ()) fun p10 =>
                        .jnz (Arg.var p10.fst)
                          (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 544, ())) fun p11 =>
                            .load i64 (Arg.var p11.fst) fun ld =>
                              .let_ (Op.mk (.trunc 64 32) (Arg.var ld, ())) fun p12 =>
                                .call (as := [i64, i32, i32]) (bs := [.bool]) "full_analyze_lit"
                                  (Arg.var c.hdr, Arg.var p12.fst, Arg.imm 0xFFFFFFFF#32, ())
                                  fun p => .jnz (Arg.var p.fst) (.jump Js1.fst (Arg.imm true, ()))
                                    (.jump Js1.fst (Arg.imm false, ())))
                          (.jump Js1.fst (Arg.imm false, ())))
              (.group (sig := [[.bool]])
                (fun _Js1 => .cons (fun p => .jump Js.fst (Arg.var p.fst, ())) .nil)
                fun Js1 => .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 176, ())) fun p8 =>
                  .load i64 (Arg.var p8.fst) fun ld =>
                    .let_ (Op.mk (.add i64) (Arg.var ld, Arg.imm 3#64, ())) fun p9 =>
                      .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 48, ())) fun p10 =>
                        .load i64 (Arg.var p10.fst) fun ld =>
                          .let_ (Op.mk (.cmp .ule i64 .bool rfl)
                              (Arg.var p9.fst, Arg.var ld, ())) fun p11 =>
                            .jnz (Arg.var p11.fst)
                              (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 176, ()))
                                fun p12 => .load i64 (Arg.var p12.fst) fun ld =>
                                  .let_ (Op.mk (.trunc 64 32) (Arg.var ld, ())) fun p13 =>
                                    .call (as := [i64, i32, i32]) (bs := [.bool])
                                      "full_analyze_rsn" (Arg.var c.hdr, Arg.var p13.fst,
                                        Arg.imm 0xFFFFFFFF#32, ())
                                      fun p => .jump Js1.fst (Arg.var p.fst, ()))
                              (.jump Js1.fst (Arg.imm false, ())))) m0 := by
  obtain ⟨hlen, hw, hlm, hnd, _hext0, _hdm⟩ := hinv
  have hmaxv := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmaxv har_cap
  have hcv_le := hlen.core_ok.cur_vars_le; have hal_le := hlen.core_ok.arena_len_le
  have hcur_le := hw.cur_level_le; have hte_le := hlen.core_ok.trail_end_le
  have hcur32 : s.core.cur_level < 2 ^ 32 := by omega
  have hcv_pos : 1 ≤ s.core.cur_vars := by omega
  let s0 : FullState :=
    { s with core := { s.core with tmp_cnt := 0, tmp_len := 1, min_clr_len := 0 },
             scratch := { s.scratch with ant_sz := 0#64, res_sz := 0#64 } }
  have hs0_len : s0.LengthsOk c :=
    ⟨{ hlen.core_ok with tmp_len_le := by dsimp [s0]; omega, min_clr_len_le := Nat.zero_le _ },
     { hlen.scratch_ok with }⟩
  have hs0_hw : Full.FullWitnessCutInv c F0 F_cur cut s0.core :=
    Full.deduce_same_core_cut hw s.core.mrk s.core.tmp 0 1 0
  have hs0_cov : Full.FullAnaMarksCov c s0 := Full.fullAnaMarksCov_of_clear hlm.1 rfl
  have hs0_nd : Full.FullArenaVarsNodup s0 := hnd
  have hs0_refs : fullArenaClauseRefs s0 = fullArenaClauseRefs s := rfl
  have hs0_ext : Full.FullExtScratchPres s s0 := ⟨rfl, rfl⟩
  have hs0_st : Full.FullDeduceStaticEq s.core s0.core :=
    (Full.fullDeduceStaticEq_refl s.core).repack
  fa_fast_steps_nogrp
  · have hct1 : s.core.confl_type = 1#64 := by assumption
    rcases hconfl.1 with ⟨_, hl0_lt, hl1_lt, hf0, hf1, hent_bin⟩ | ⟨hne, _⟩
    · refine wp_join_group (ts := [.bool]) (fun p ml => Js.fst p ml)
        (fun _ ⟨_, ⟨⟩⟩ ml hb => fa_wp_jump1 hb) ?_
      intro J1 hJ1; fa_fast_steps
      have hconfl2 := hconfl.2
      simp only [hct1, ↓reduceIte] at hconfl2
      have hl0_tr : (s.core.confl_lit0.setWidth 32).toNat = s.core.confl_lit0.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      have hl1_tr : (s.core.confl_lit1.setWidth 32).toNat = s.core.confl_lit1.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      have hm0_all : ∀ v < s0.core.cur_vars, s0.core.mrk[v]?.getD 0#8 = 0#8 :=
        fun v hv => hlm.1 v (Nat.lt_of_lt_of_le (by dsimp [s0] at hv; exact hv) hcv_le)
      have hct0 : (Full.fullCurTrailIdxs s0.core s0.core.mrk s0.core.trail_end).length = 0 := by
        rw [Full.fullCurTrailIdxs, List.filter_eq_nil_iff.mpr fun j hj => by
          rw [List.mem_range] at hj
          have hv := hs0_hw.trail_lits_lt j hj
          have hcv0 : s0.core.cur_vars = s.core.cur_vars := rfl
          simp [hm0_all ((s0.core.trl[j]?.getD 0#32).toNat / 2) (by omega)]]
        rfl
      refine wp_call_of_spec _ _ (hAlit (c.hdr, s.core.confl_lit0.setWidth 32, 0xFFFFFFFF#32, ())
        _ _ _ ⟨c, s0, R, rfl, hs0_len, hcur32, by dsimp [s0]; omega,
          by dsimp [s0]; decide, hs0_cov, hm0, ?_⟩)
      intro ok_a mrk_a tmp_a tc_a tl_a mcl_a ws1_a ant_a res_a m_a _
        hlen_a hcov_a htla_ge htla_inc htla_cv htca_ge hant_a hres_a htca_eq
        hmpa htpa hnma hnta hok_a hm_a
      dsimp only [s0] at hlen_a hcov_a htla_ge htla_inc htla_cv htca_ge hant_a hres_a htca_eq
      dsimp only [s0] at hmpa htpa hnma hnta hok_a hm_a
      let sa : FullState :=
        { s0 with core := { s0.core with mrk := mrk_a, tmp := tmp_a, tmp_cnt := tc_a,
                                         tmp_len := tl_a, min_clr_len := mcl_a },
                  scratch := { s0.scratch with work_stk1 := ws1_a, ant_sz := ant_a,
                                               res_sz := res_a } }
      have hwa : Full.FullWitnessCutInv c F0 F_cur cut sa.core :=
        Full.deduce_same_core_cut hs0_hw mrk_a tmp_a tc_a tl_a mcl_a
      have hnda : Full.FullArenaVarsNodup sa := hs0_nd
      have hrefsa : fullArenaClauseRefs sa = fullArenaClauseRefs s := rfl
      have hstata : Full.FullDeduceStaticEq s.core sa.core :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hexta : Full.FullExtScratchPres s sa := ⟨rfl, rfl⟩
      cases ok_a with
      | false =>
        fa_fast_steps
        exact hJ1 (false, ()) m_a (hJsd false m_a ⟨sa, hlen_a, hwa, hcov_a, hexta, rfl, hnda,
          hrefsa, hstata, by dsimp [sa]; omega, by dsimp [sa]; exact htla_cv, rfl, rfl,
          (fun hc => by cases hc), hm_a⟩)
      | true =>
        fa_fast_steps
        have hlow0 : Full.FullLowerInv c s0.core s0.core.tmp s0.core.mrk 1 :=
          ⟨fun _ h1 h2 => by omega, fun _ _ h1 _ h2 => by omega⟩
        have hcov0_m : Full.FullMarksCov s0.core s0.core.tmp s0.core.mrk 1 :=
          fun v hv hnz => absurd (hm0_all v hv) hnz
        have hcm0 : Full.FullCurMarksBelow s0.core.trail_end s0.core s0.core.mrk cut := by
          intro j hj hnz _; have hv := hs0_hw.trail_lits_lt j hj
          exact absurd (hm0_all _ (by omega)) hnz
        have hsa_sem := Full.deduce_seed_lit_step (cut := cut) (s := s) (sa := s0)
          (lit := s.core.confl_lit0.setWidth 32) hs0_len hs0_hw hs0_nd hs0_refs hs0_st
          (Nat.le_refl _) hct0.symm hlow0 hcov0_m hcm0 (by dsimp [s0])
          (by simpa [hl0_tr, s0] using hl0_lt) (by simpa [hl0_tr, s0] using hf0)
          (by simpa [hl0_tr, s0] using hconfl2.1) hlen_a hcov_a htla_cv htla_ge htca_ge
          (fun w hw hnz => hmpa w (Nat.lt_of_lt_of_le hw (by dsimp [s0] at *; exact hcv_le)) hnz)
          htpa
          (fun w hw h0 hnz =>
            let ⟨he, _, hsk, hpos, hle⟩ := hnma w
              (Nat.lt_of_lt_of_le hw (by dsimp [s0] at *; exact hcv_le)) h0 hnz
            ⟨he, hsk, hpos, hle⟩)
          hnta hres_a htca_eq (hok_a rfl) hs0_ext rfl
        obtain ⟨_, _, _, _, _, _, _, _, htla1, _, htca_eq', hlowa, hmcova, hcma, _, hl0_res,
          hres_a_eq⟩ := hsa_sem
        refine wp_call_of_spec _ _ (hAlit (c.hdr, s.core.confl_lit1.setWidth 32, 0xFFFFFFFF#32, ())
          _ _ _ ⟨c, sa, R, rfl, hlen_a, hcur32, htla_cv,
            by dsimp only [sa]; rw [htca_eq]; split <;> omega, hcov_a, hm_a, ?_⟩)
        intro ok_b mrk_b tmp_b tc_b tl_b mcl_b ws1_b ant_b res_b m_b _
          hlen_b hcov_b htlb_ge _ htlb_cv htcb_ge _ hres_b htcb_eq hmpb htpb hnmb hntb hok_b hm_b
        dsimp only [sa] at hlen_b hcov_b htlb_ge htlb_cv htcb_ge hres_b htcb_eq hmpb htpb hnmb hntb
        dsimp only [sa] at hok_b hm_b
        let sb : FullState :=
          { sa with core := { sa.core with mrk := mrk_b, tmp := tmp_b, tmp_cnt := tc_b,
                                           tmp_len := tl_b, min_clr_len := mcl_b },
                    scratch := { sa.scratch with work_stk1 := ws1_b, ant_sz := ant_b,
                                                 res_sz := res_b } }
        have hwb : Full.FullWitnessCutInv c F0 F_cur cut sb.core :=
          Full.deduce_same_core_cut hwa mrk_b tmp_b tc_b tl_b mcl_b
        have hndb : Full.FullArenaVarsNodup sb := hnda
        have hrefsb : fullArenaClauseRefs sb = fullArenaClauseRefs s := rfl
        have hstatb : Full.FullDeduceStaticEq s.core sb.core :=
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        have hextb : Full.FullExtScratchPres s sb := ⟨rfl, rfl⟩
        cases ok_b with
        | false =>
          fa_fast_steps
          exact hJ1 (false, ()) m_b (hJsd false m_b ⟨sb, hlen_b, hwb, hcov_b, hextb, rfl, hndb,
            hrefsb, hstatb, by dsimp [sb, sa]; omega, by dsimp [sb]; exact htlb_cv, rfl, rfl,
            (fun hc => by cases hc), hm_b⟩)
        | true =>
          fa_fast_steps
          have hsb_sem := Full.deduce_seed_lit_step (cut := cut) (s := s) (sa := sa)
            (lit := s.core.confl_lit1.setWidth 32) hlen_a hwa hnda hrefsa hstata htla1
            htca_eq' hlowa hmcova hcma hres_a_eq (by simpa [hl1_tr, sa, s0] using hl1_lt)
            (by simpa [hl1_tr, sa, s0] using hf1) (by simpa [hl1_tr, sa, s0] using hconfl2.2)
            hlen_b hcov_b htlb_cv htlb_ge htcb_ge
            (fun w hw hnz => hmpb w (Nat.lt_of_lt_of_le hw (by dsimp [sa, s0] at *; exact hcv_le))
              hnz)
            htpb
            (fun w hw h0 hnz =>
              let ⟨he, _, hsk, hpos, hle⟩ := hnmb w
                (Nat.lt_of_lt_of_le hw (by dsimp [sa, s0] at *; exact hcv_le)) h0 hnz
              ⟨he, hsk, hpos, hle⟩)
            hntb hres_b htcb_eq (hok_b rfl) hexta rfl
          obtain ⟨hlen_sb, hw_sb, hcov_sb, hext_sb, hws2_sb, hnd_sb, hrefs_sb, hstat_sb, htlb1,
            htlb_cv', htcb_eq', hlowb, hmcovb, hcmb, hsub_ab, hl1_res, hres_b_eq⟩ := hsb_sem
          exact hJ1 (true, ()) m_b (hJsd true m_b ⟨sb, hlen_sb, hw_sb, hcov_sb, hext_sb, hws2_sb,
            hnd_sb, hrefs_sb, hstat_sb, htlb1, htlb_cv', rfl, rfl, fun _ =>
              Full.deduce_seed_bin_sem hl0_lt hl1_lt hent_bin hsub_ab hl0_res hl1_res hlen_sb hw_sb
                hcov_sb hext_sb hws2_sb hnd_sb hrefs_sb hstat_sb htlb1 htlb_cv' htcb_eq' hlowb
                hmcovb hcmb hres_b_eq rfl rfl,
            hm_b⟩)
    · exact absurd (hct1.symm.trans hne) (by decide)
  · have hct_ne : s.core.confl_type ≠ 1#64 := by assumption
    rcases hconfl.1 with ⟨h1, _⟩ | ⟨hct2, href, _, _⟩
    · exact absurd h1 hct_ne
    · refine wp_join_group (ts := [.bool]) (fun p ml => Js.fst p ml)
        (fun _ ⟨_, ⟨⟩⟩ ml hb => fa_wp_jump1 hb) ?_
      intro J1 hJ1
      have hwf := (hw.arena.refs_wf _ href).1
      have hcr_lt : s.core.confl_ref.toNat < 2 ^ 31 - 1 := by omega
      fa_fast_steps
      · obtain ⟨hcr_tr, _, _⟩ := bv64_confl_ref_u32 hcr_lt
        refine wp_call_of_spec _ _ (hArsn (c.hdr, s.core.confl_ref.setWidth 32, 0xFFFFFFFF#32, ())
          _ _ _ ⟨c, F0, F_cur, cut, s0, R, rfl, hs0_len, hs0_hw, hs0_cov,
            by dsimp [s0]; omega, by dsimp [s0]; omega,
            fun _ _ => by rw [hcr_tr]; exact hs0_refs ▸ href, hm0, ?_⟩)
        intro ok1 mrk1 tmp1 tc1 tl1 mcl1 arena1 sc1 m1 _ hlen1 hw1 hcov1 hext1 hws2_1
          htl1_ge htl1_cv htc1_ge hrefs1 hprops1 hmp1 htp1 hnm1 hnt1 hnd1_t hcnt1 hres1 hok1 hm1
        dsimp only [s0] at hlen1 hw1 hcov1 hext1 hws2_1 htl1_ge htl1_cv htc1_ge hrefs1 hprops1 hm1
        let s1 : FullState :=
          { s0 with core := { s0.core with mrk := mrk1, tmp := tmp1, tmp_cnt := tc1,
                                           tmp_len := tl1, min_clr_len := mcl1, arena := arena1 },
                    scratch := sc1 }
        have hnd1 : Full.FullArenaVarsNodup s1 := fun r hr hngr => by
          change r ∈ fullArenaClauseRefs s1 at hr; rw [hrefs1] at hr
          have hll := hprops1 r hr
          change ((fullArenaClauseLits s1 r).map (· / 2)).Nodup
          rw [hll.2.2]; refine hnd r hr ?_
          unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hll hngr ⊢
          rw [← hll.2.1]; exact hngr
        have hs1_st : Full.FullDeduceStaticEq s.core s1.core :=
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        cases ok1 with
        | false =>
          fa_fast_steps
          exact hJ1 (false, ()) m1 (hJsd false m1 ⟨s1, hlen1, hw1, hcov1,
            Full.fullExtScratchPres_trans hs0_ext hext1, hws2_1, hnd1, hrefs1.trans hs0_refs,
            hs1_st, by dsimp [s1]; omega, by dsimp [s1]; exact htl1_cv, rfl, rfl,
            (fun hc => by cases hc), hm1⟩)
        | true =>
          fa_fast_steps
          have hsem := Full.deduce_seed_rsn_sem hs0_len hs0_hw hs0_st rfl rfl rfl
            (fun v hv => hlm.1 v hv) rfl rfl hct2 hconfl hw1 hlen1 hcov1 hext1 hws2_1
            htl1_ge htl1_cv htc1_ge hrefs1 hnd1
            (fun w hw hnz => hmp1 w (Nat.lt_of_lt_of_le hw hcv_le) hnz)
            htp1
            (fun w hw h0 hnz =>
              let ⟨l, hl, h1, _, h2, h3, h4⟩ := hnm1 w (Nat.lt_of_lt_of_le hw hcv_le) h0 hnz
              ⟨l, hl, h1, h2, h3, h4⟩)
            hnt1 hnd1_t hcnt1 hres1 ⟨(hok1 rfl).1, (hok1 rfl).2.2⟩ hs0_ext rfl hs0_refs
          exact hJ1 (true, ()) m1 (hJsd true m1 ⟨s1, hlen1, hw1, hcov1, hsem.ext, hsem.ws2, hnd1,
            hrefs1.trans hs0_refs, hs1_st, hsem.tl_ge, hsem.tl_cv, rfl, rfl, fun _ => hsem, hm1⟩)
      · have h_not : ¬(s.core.confl_ref.toNat + 3) % 2 ^ 64 ≤ s.core.arena_len % 2 ^ 64 := by
          assumption
        exact absurd (by
          rw [Nat.mod_eq_of_lt (by omega : s.core.confl_ref.toNat + 3 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)]
          exact hwf) h_not

private theorem m5_deduce_clear_ana_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {K : Tup Val [] → Expr Val Cont [i64]}
    {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (hlen1 : s1.LengthsOk c) (hw1 : Full.FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : Full.FullAnaMarksCov c s1) (hext0 : Full.FullExtScratchOk c s)
    (hext1 : Full.FullExtScratchPres s s1) (hnd1 : Full.FullArenaVarsNodup s1)
    (hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s)
    (hlm1 : s1.core.lit_mark = s.core.lit_mark) (hdm1 : s1.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hK : ∀ mrk' m_clr,
      let s_clr : FullState := { s1 with core := { s1.core with mrk := mrk', min_clr_len := 0 } }
      s_clr.LengthsOk c → Full.FullOtfsInvW c F0 F_cur s_clr →
      Full.FullWitnessCutInv c F0 F_cur cut' s_clr.core →
      (FullMem c s_clr ⋆ R) m_clr → wp Γ Q X (K ()) m_clr) :
    wp Γ Q X (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) K)
      m1 := by
  refine wp_call_of_spec _ _ (hClear (c.hdr, ()) _ _ _ ⟨c, s1, R, rfl, hlen1, hm1, ?_⟩)
  intro mrk' m_c hm'_len _ _ hm'_cov hm_c
  let s_c : FullState := { s1 with core := { s1.core with mrk := mrk', min_clr_len := 0 } }
  have hlen_c : s_c.LengthsOk c :=
    ⟨{ hlen1.core_ok with mrk_len := hm'_len, min_clr_len_le := Nat.zero_le _ }, hlen1.scratch_ok⟩
  have hw_c : Full.FullWitnessCutInv c F0 F_cur cut' s_c.core :=
    Full.deduce_same_core_cut hw1 mrk' s1.core.tmp s1.core.tmp_cnt s1.core.tmp_len 0
  have hlm_c : Full.FullLitMarksClear c s_c :=
    ⟨hm'_cov hcov1, fun l hl => by
      change s1.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hlm1]; exact hm0_lm.2 l hl⟩
  have hotfs_c : Full.FullOtfsInvW c F0 F_cur s_c :=
    ⟨hlen_c, hw_c.toFullOtfsWitnessInv, hlm_c, hnd1,
     ⟨fun i hi => by
        change (let cr := s_c.scratch.last_learned[i]?.getD 0xFFFFFFFF#32; _); rw [hext1.1]
        rcases hext0.1 i hi with h | h
        · exact Or.inl h
        · exact Or.inr (hrefs1 ▸ h),
      by rw [hext1.2]; exact hext0.2⟩,
     hdm1⟩
  exact hK mrk' m_c hlen_c hotfs_c hw_c hm_c

private theorem m5_deduce_anaMarksCov_of_same {c : FullCfg} {s1 s2 : FullState}
    (hcov : Full.FullAnaMarksCov c s1) (hcv : s2.core.cur_vars = s1.core.cur_vars)
    (hmcl : s2.core.min_clr_len = s1.core.min_clr_len) (hmrk : s2.core.mrk = s1.core.mrk)
    (hws1 : s2.scratch.work_stk1 = s1.scratch.work_stk1) : Full.FullAnaMarksCov c s2 :=
  ⟨by rw [hcv, hmcl]; exact hcov.1, by rw [hmcl, hws1]; exact hcov.2.1,
   fun k hk => by rw [hws1, hcv, hmrk]; exact hcov.2.2.1 k (hmcl ▸ hk),
   fun v hv hnz => by
     rw [hmrk] at hnz
     obtain ⟨k, hk, hget⟩ := hcov.2.2.2 v hv hnz
     exact ⟨k, by rw [hmcl]; exact hk, by rw [hws1]; exact hget⟩⟩

private theorem m5_deduce_res_clear_ret_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (retv : BitVec 64)
    (hlen1 : s1.LengthsOk c) (hw1 : Full.FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : Full.FullAnaMarksCov c s1) (hext0 : Full.FullExtScratchOk c s)
    (hext1 : Full.FullExtScratchPres s s1) (hws2 : s1.scratch.work_stk2 = s.scratch.work_stk2)
    (hnd1 : Full.FullArenaVarsNodup s1) (hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s)
    (hstat1 : Full.FullDeduceStaticEq s.core s1.core) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hK : ∀ mrk_c m_c,
      let s_c : FullState :=
        { s1 with
          core := { s1.core with mrk := mrk_c, min_clr_len := 0 }
          scratch := { s1.scratch with res_sz := BitVec.ofNat 64 s1.core.min_clr_len } }
      s_c.LengthsOk c → Full.FullOtfsInvW c F0 F_cur s_c →
      Full.FullWitnessCutInv c F0 F_cur cut' s_c.core → Full.FullCutInvW c F0 F_cur cut' s_c →
      s_c.core.cur_vars = s.core.cur_vars → s_c.core.cur_level = s.core.cur_level →
      s_c.core.fuel = s.core.fuel → s_c.scratch.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s_c ⋆ R) m_c → Q (retv, ()) m_c) :
    wp Γ Q X
      (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272, ())) fun p1 =>
        .load i64 (Arg.var p1.fst) fun ld =>
          .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p2 =>
            .store (Arg.var ld) (Arg.var p2.fst)
              (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
                (fun _ => .ret (Arg.imm retv, ())))) m1 := by
  fa_fast_steps_nogrp
  let s_r : FullState :=
    { s1 with scratch := { s1.scratch with res_sz := BitVec.ofNat 64 s1.core.min_clr_len } }
  have hlen_r : s_r.LengthsOk c := ⟨hlen1.core_ok, { hlen1.scratch_ok with }⟩
  have hcov_r : Full.FullAnaMarksCov c s_r := m5_deduce_anaMarksCov_of_same hcov1 rfl rfl rfl rfl
  have hw_r : Full.FullWitnessCutInv c F0 F_cur cut' s_r.core := hw1
  have hext_r : Full.FullExtScratchPres s s_r := hext1
  have hnd_r : Full.FullArenaVarsNodup s_r := hnd1
  have hrefs_r : fullArenaClauseRefs s_r = fullArenaClauseRefs s := hrefs1
  refine m5_deduce_clear_ana_wp hClear hlen_r hw_r hcov_r hext0 hext_r hnd_r hrefs_r
    hstat1.lm (hstat1.dm.trans hdm0) hm0_lm (by assumption)
    fun mrk_c m_c hlen_c hotfs_c hw_c hm_c => ?_
  fa_fast_steps
  let s_c : FullState := { s_r with core := { s_r.core with mrk := mrk_c, min_clr_len := 0 } }
  have hcutw : Full.FullCutInvW c F0 F_cur cut' s_c :=
    ⟨hlen_c, hw_c, hotfs_c.2.2.1, hotfs_c.2.2.2.1, hotfs_c.2.2.2.2.1, hotfs_c.2.2.2.2.2⟩
  exact hK mrk_c m_c hlen_c hotfs_c hw_c hcutw hstat1.cv hstat1.cl hstat1.fuel hws2 hm_c

private theorem m5_deduce_cut_with_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut' : Nat} {k : FullCoreState} (hw : Full.FullWitnessCutInv c F0 F_cur cut' k)
    (ct' cr' : BitVec 64) :
    Full.FullWitnessCutInv c F0 F_cur cut' { k with confl_type := ct', confl_ref := cr' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }

private theorem m5_bv64_setWidth32_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), bv32_ofNat_toNat hn,
    Nat.mod_eq_of_lt hn]

private theorem m5_deduce_otfs_ret2_subsume_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut idx' resolved : Nat}
    {s s_ot : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m_ot : Mem 64}
    {init_res_sz old_ct old_cr : BitVec 64} {p rsn : BitVec 32}
    {new_confl_arg : Arg Val i32} {to_bin : Bool}
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → Full.FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        Full.FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        Full.FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hw0 : Full.FullWitnessCutInv c F0 F_cur cut s.core)
    (hconfl0 : Full.FullConflictOkCut F_cur cut s)
    (hext0 : Full.FullExtScratchOk c s) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s)
    (hlen_ot : s_ot.LengthsOk c) (hw_ot : Full.FullWitnessCutInv c F0 F_cur idx' s_ot.core)
    (hcov_ot : Full.FullAnaMarksCov c s_ot) (hext_ot : Full.FullExtScratchPres s s_ot)
    (hws2_ot : s_ot.scratch.work_stk2 = s.scratch.work_stk2) (hnd_ot : Full.FullArenaVarsNodup s_ot)
    (hrefs_ot : fullArenaClauseRefs s_ot = fullArenaClauseRefs s)
    (hstat_ot : Full.FullDeduceStaticEq s.core s_ot.core)
    (hconfl_ot : Full.FullConflictOkCut F_cur idx' s_ot)
    (hiu_te : idx' < s_ot.core.trail_end) (hres_lt : resolved + 1 < 2 ^ 64)
    (hbin_ct : to_bin = true → s_ot.core.confl_type = 1#64)
    (hzero_cond : resolved = 0 →
      cut = cut ∧ idx' < cut ∧
      (s.core.trl[idx']?.getD 0#32).toNat = p.toNat ∧
      s.core.rsns[p.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn ∧
      rsn ≠ 0xFFFFFFFF#32 ∧ (rsn &&& 0x80000000#32) = 0#32 ∧
      old_ct = s.core.confl_type ∧ old_cr = s.core.confl_ref ∧
      (to_bin = false → new_confl_arg.val.toNat ∈ fullArenaClauseRefs s_ot ∧
        new_confl_arg.val.toNat = rsn.toNat ∧ s_ot.core.confl_ref.toNat = rsn.toNat))
    (hm_ot : (FullMem c s_ot ⋆ R) m_ot) :
    wp Γ Q X (.group (sig := [[]]) (fun _Js => .cons (fun _ =>
      .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272, ())) fun p1 =>
        .load i64 (Arg.var p1.fst) fun ld =>
          .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p2 =>
            .store (Arg.var ld) (Arg.var p2.fst)
              (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
                fun _ => .ret (Arg.imm 2#64, ()))) .nil)
      fun Js => .let_ (Op.mk (.cmp .eq i64 .bool rfl)
          (Arg.var (BitVec.ofNat 64 resolved + 1#64), Arg.imm 1#64, ()))
        fun p66 => .jnz (Arg.var p66.fst)
          (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p67 =>
            .load i64 (Arg.var p67.fst) fun ld23 =>
              .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                  (Arg.var ld23, Arg.var init_res_sz, ()))
                fun p68 => .jnz (Arg.var p68.fst)
                  (.call (rs := [i64]) (as := [i64, i32, i64, i64, .bool]) (bs := [])
                    "full_otfs_subsume"
                    (Arg.var c.hdr, new_confl_arg, Arg.var old_ct, Arg.var old_cr,
                      Arg.imm to_bin, ())
                    fun _ => .jump Js.fst ())
                  (.jump Js.fst ()))
          (.jump Js.fst ())) m_ot := by
  fa_fast_steps_nogrp
  refine wp_join_group (ts := []) (fun () ml => ∃ s_j : FullState,
      s_j.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur idx' s_j.core ∧
      Full.FullAnaMarksCov c s_j ∧ Full.FullExtScratchPres s s_j ∧
      s_j.scratch.work_stk2 = s.scratch.work_stk2 ∧ Full.FullArenaVarsNodup s_j ∧
      fullArenaClauseRefs s_j = fullArenaClauseRefs s ∧ Full.FullDeduceStaticEq s.core s_j.core ∧
      Full.FullConflictOkCut F_cur idx' s_j ∧ (FullMem c s_j ⋆ R) ml) ?_ ?_
  · rintro _ ⟨⟩ ml ⟨s_j, hlen_j, hw_j, hcov_j, hext_j, hws2_j, hnd_j, hrefs_j, hstat_j,
      hconfl_j, hml⟩
    refine m5_deduce_res_clear_ret_wp hClear 2#64 hlen_j hw_j hcov_j hext0 hext_j hws2_j
      hnd_j hrefs_j hstat_j hdm0 hm0_lm hml fun mrk_c m_c hlen_c _ hw_c hcut_c hcv_c
        hcl_c hfuel_c hws2_c hm_c => ?_
    let s_c : FullState :=
      { s_j with
        core := { s_j.core with mrk := mrk_c, min_clr_len := 0 }
        scratch := { s_j.scratch with res_sz := BitVec.ofNat 64 s_j.core.min_clr_len } }
    have hte_eq : s_c.core.trail_end = s_j.core.trail_end := rfl
    have hte_j : s_j.core.trail_end = s_ot.core.trail_end := by rw [hstat_j.te, hstat_ot.te]
    have hconfl_c := Full.deduce_conflOk_same_of_clear hconfl_j rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl
    exact Full.deduce_otfs_ret2_post hQ hlen_c (by rw [hte_eq, hte_j]; exact Nat.le_of_lt hiu_te)
      hcut_c hconfl_c hcv_c hcl_c hfuel_c hws2_c hm_c
  · intro Jsub hJsub
    fa_fast_steps
    · have hres0 : resolved = 0 := by
        have heq : BitVec.ofNat 64 resolved + 1#64 = 1#64 := by assumption
        have hnat := congrArg BitVec.toNat heq
        simp only [bv_c0, show (1#64 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega : resolved < 2 ^ 64),
          Nat.mod_eq_of_lt hres_lt] at hnat
        omega
      obtain ⟨_, hiu_cut0, hp0, hr0, hrsn_ne0, hrsn_lg0, hct0, hcr0, hnew0⟩ := hzero_cond hres0
      have hnonact := Full.deduce_otfs_old_cr_nonactive hw0 hconfl0 hiu_cut0
        (by rw [← hstat_ot.te]; exact hiu_te) hp0 hr0 hrsn_ne0 hrsn_lg0 hct0 hcr0 hstat_ot
      refine wp_call_of_spec _ _ (hOtfsSub (c.hdr, new_confl_arg.val, old_ct, old_cr, to_bin, ())
        _ _ _ ⟨c, F0, F_cur, idx', s_ot, R, rfl, hlen_ot, hw_ot, hnd_ot, fun hct2 hcr_ne => ?_,
          hm_ot, ?_⟩)
      · obtain ⟨hne_rsn, hna⟩ := hnonact hct2 hcr_ne
        refine ⟨?_, fun hf => (hnew0 hf).1, fun idx hidx hcond hne hlg =>
          hna idx hidx hcond hne hlg⟩
        rw [hrefs_ot, hcr0]
        rcases hconfl0.1 with ⟨h1, _⟩ | ⟨_, href0, _⟩
        · exact absurd (hct0.symm.trans hct2) (by rw [h1]; decide)
        · exact href0
      · intro arena_s ag_s ni_s nr_s m_s _ hlen_s hw_s hnd_s hrefs_s hkeep_s hm_s
        let s_s : FullState :=
          { s_ot with core := { s_ot.core with arena := arena_s, arena_garbage := ag_s,
                                               num_irred := ni_s, num_redundant := nr_s } }
        have hcov_s : Full.FullAnaMarksCov c s_s := hcov_ot
        have hext_s : Full.FullExtScratchPres s s_s := hext_ot
        have hstat_s : Full.FullDeduceStaticEq s.core s_s.core :=
          ⟨hstat_ot.1, hstat_ot.2, hstat_ot.3, hstat_ot.4, hstat_ot.5, hstat_ot.6, hstat_ot.7,
           hstat_ot.8, hstat_ot.9, hstat_ot.10⟩
        have hconfl_s : Full.FullConflictOkCut F_cur idx' s_s := by
          refine Full.deduce_conflOk_of_subsume hconfl_ot rfl rfl rfl rfl rfl rfl rfl rfl rfl
            hrefs_s fun r hr => ?_
          refine ⟨(hkeep_s r hr).1, fun hct2 r_eq => ?_⟩
          rcases (hkeep_s r hr) with ⟨_, hgr⟩
          by_cases hct_old : old_ct = 2#64 ∧ old_cr ≠ 0xFFFFFFFF#64
          · have ⟨hne_rsn, _⟩ := hnonact hct_old.1 hct_old.2
            refine hgr fun _ => ?_
            cases to_bin with
            | true => exact absurd (hct2.symm.trans (hbin_ct rfl)) (by decide)
            | false =>
              obtain ⟨_, _, hcr_sot⟩ := hnew0 rfl
              rw [r_eq, hcr_sot]; exact hne_rsn
          · by_cases hct_old2 : old_ct = 2#64
            · have heqff : old_cr = 0xFFFFFFFF#64 :=
                Classical.byContradiction fun hne => hct_old ⟨hct_old2, hne⟩
              have hwf := (hw_ot.arena.refs_wf r hr).1
              have har_le := hlen_ot.core_ok.arena_len_le
              have hcap31 := c.harena; unfold dimacsBound at hcap31
              refine hgr (fun _ => ?_)
              rw [heqff]
              have hff : (0xFFFFFFFF#64 : BitVec 64).toNat = 4294967295 := rfl
              omega
            · exact hgr (fun h => absurd h hct_old2)
        fa_fast_steps
        exact hJsub () m_s ⟨s_s, hlen_s, hw_s, hcov_s, hext_s, hws2_ot, hnd_s,
          hrefs_s.trans hrefs_ot, hstat_s, hconfl_s, hm_s⟩
    · exact hJsub () m_ot ⟨s_ot, hlen_ot, hw_ot, hcov_ot, hext_ot, hws2_ot, hnd_ot, hrefs_ot,
        hstat_ot, hconfl_ot, hm_ot⟩
    · exact hJsub () m_ot ⟨s_ot, hlen_ot, hw_ot, hcov_ot, hext_ot, hws2_ot, hnd_ot, hrefs_ot,
        hstat_ot, hconfl_ot, hm_ot⟩

private theorem m5_deduce_loop_step_wp {Γ : Env}
    (hArsn : ∀ a m Q X, Full.fullAnalyzeRsnSpec a m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin_m5" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {init_res_sz : BitVec 64}
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → Full.FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        Full.FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        Full.FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hw0 : Full.FullWitnessCutInv c F0 F_cur cut s.core) (hcur_pos : 0 < s.core.cur_level)
    (hconfl0 : Full.FullConflictOkCut F_cur cut s) (hext0 : Full.FullExtScratchOk c s)
    (hdm0 : s.core.dense_mode = 0#64) (hm0_lm : Full.FullLitMarksClear c s)
    {J_uip : Cont [i64, i32, i64]}
    (hJuip : ∀ (idx'_bv : BitVec 64) (uip_bv : BitVec 32) (res'_bv : BitVec 64) m_u,
      (∃ (cut_u idx_u : Nat) (su : FullState) (p_u : BitVec 32),
        su.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut_u su.core ∧
        Full.FullAnaMarksCov c su ∧ Full.FullExtScratchPres s su ∧
        su.scratch.work_stk2 = s.scratch.work_stk2 ∧ Full.FullArenaVarsNodup su ∧
        fullArenaClauseRefs su = fullArenaClauseRefs s ∧
        Full.FullDeduceStaticEq s.core su.core ∧ 1 ≤ su.core.tmp_len ∧
        su.core.tmp_len ≤ su.core.cur_vars ∧
        Full.FullLowerInv c su.core su.core.tmp su.core.mrk su.core.tmp_len ∧
        idx_u < su.core.trail_end ∧ (su.core.trl[idx_u]?.getD 0#32).toNat = p_u.toNat ∧
        (su.core.lvl[p_u.toNat / 2]?.getD 0#32).toNat = su.core.cur_level ∧
        uip_bv = p_u ^^^ 1#32 ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((p_u ^^^ 1#32).toNat :: Full.fullLowerLits su.core.tmp su.core.tmp_len)) ∧
        (FullMem c su ⋆ R) m_u) →
      J_uip (idx'_bv, uip_bv, res'_bv, ()) m_u)
    {p_18 : Tup Val [i64, i64]} {m_l : Mem 64}
    {J_loop : Cont [i64, i64]}
    (hJloop : ∀ ys m', ys.1.toNat < p_18.1.toNat →
      (∃ (cut_n idx_n res_n : Nat) (sn : FullState),
        ys = (BitVec.ofNat 64 idx_n, BitVec.ofNat 64 res_n, ()) ∧
        idx_n + res_n ≤ sn.core.trail_end ∧
        Full.FullDeduceStateInv c F0 F_cur cut_n idx_n s sn ∧
        0 < sn.core.tmp_cnt ∧
        (res_n = 0 → cut_n = cut ∧
          sn.core.confl_type = s.core.confl_type ∧ sn.core.confl_ref = s.core.confl_ref) ∧
        (FullMem c sn ⋆ R) m') →
      J_loop ys m')
    (hinv_l : ∃ (cut_cur idx resolved : Nat) (sl : FullState),
      p_18 = (BitVec.ofNat 64 idx, BitVec.ofNat 64 resolved, ()) ∧
      idx + resolved ≤ sl.core.trail_end ∧
      Full.FullDeduceStateInv c F0 F_cur cut_cur idx s sl ∧
      0 < sl.core.tmp_cnt ∧
      (resolved = 0 → cut_cur = cut ∧
        sl.core.confl_type = s.core.confl_type ∧ sl.core.confl_ref = s.core.confl_ref) ∧
      (FullMem c sl ⋆ R) m_l) :
    wp (rs := [i64]) Γ Q X
      (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 184, ())) fun p19 =>
      .load i64 (Arg.var p19.fst) fun ld9 =>
      .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld9, Arg.imm 0#64, ())) fun p20 =>
      .jnz (Arg.var p20.fst)
        (.let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var p_18.fst, Arg.imm 0#64, ())) fun p21 =>
        .jnz (Arg.var p21.fst)
          (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana"
            (Arg.var c.hdr, ()) fun _ => .ret (Arg.imm 0#64, ()))
          (.let_ (Op.mk (.sub i64) (Arg.var p_18.fst, Arg.imm 1#64, ())) fun p22 =>
          .let_ (Op.mk (.mul i64) (Arg.var p22.fst, Arg.imm 4#64, ())) fun p23 =>
          .let_ (Op.mk (.add i64) (Arg.var c.pTrail, Arg.var p23.fst, ())) fun p24 =>
          .load i32 (Arg.var p24.fst) fun ld10 =>
          .let_ (Op.mk (.lshr i32) (Arg.var ld10, Arg.imm 1#32, ())) fun p25 =>
          .let_ (Op.mk (.zext 32 64) (Arg.var p25.fst, ())) fun p26 =>
          .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p27 =>
          .load i64 (Arg.var p27.fst) fun ld11 =>
          .let_ (Op.mk (.cmp .uge i64 .bool rfl) (Arg.var p26.fst, Arg.var ld11, ())) fun p28 =>
          .jnz (Arg.var p28.fst)
            (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana"
              (Arg.var c.hdr, ()) fun _ => .ret (Arg.imm 0#64, ()))
            (.group (sig := [[i32, i64]])
              (fun _ => .cons (fun p => .jump J_loop (Arg.var p22.fst, Arg.var p.snd.fst, ()))
                .nil)
              fun Js2 =>
              .let_ (Op.mk (.zext 32 64) (Arg.var p25.fst, ())) fun p29 =>
              .let_ (Op.mk (.add i64) (Arg.var c.pMark, Arg.var p29.fst, ())) fun p30 =>
              .load i8 (Arg.var p30.fst) fun ld12 =>
              .let_ (Op.mk (.trunc 32 8) (Arg.imm 0#32, ())) fun p31 =>
              .let_ (Op.mk (.zext 8 32) (Arg.var ld12, ())) fun p32 =>
              .let_ (Op.mk (.zext 8 32) (Arg.var p31.fst, ())) fun p33 =>
              .let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var p32.fst, Arg.var p33.fst, ()))
                fun p34 =>
              .jnz (Arg.var p34.fst)
                (.let_ (Op.mk (.zext 32 64) (Arg.var p25.fst, ())) fun p35 =>
                .let_ (Op.mk (.mul i64) (Arg.var p35.fst, Arg.imm 4#64, ())) fun p36 =>
                .let_ (Op.mk (.add i64) (Arg.var c.pLevel, Arg.var p36.fst, ())) fun p37 =>
                .load i32 (Arg.var p37.fst) fun ld13 =>
                .let_ (Op.mk (.cmp .eq i32 .bool rfl)
                    (Arg.var ld13, Arg.imm (BitVec.ofNat 32 s.core.cur_level), ())) fun p38 =>
                .jnz (Arg.var p38.fst)
                  (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 184, ())) fun p39 =>
                  .load i64 (Arg.var p39.fst) fun ld14 =>
                  .let_ (Op.mk (.sub i64) (Arg.var ld14, Arg.imm 1#64, ())) fun p40 =>
                  .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 184, ())) fun p41 =>
                  .store (Arg.var p40.fst) (Arg.var p41.fst)
                    (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 184, ())) fun p42 =>
                    .load i64 (Arg.var p42.fst) fun ld15 =>
                    .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var ld15, Arg.imm 0#64, ()))
                      fun p43 =>
                    .jnz (Arg.var p43.fst)
                      (.let_ (Op.mk (.xor i32) (Arg.var ld10, Arg.imm 1#32, ())) fun p =>
                      .jump J_uip (Arg.var p22.fst, Arg.var p.fst, Arg.var p_18.snd.fst, ()))
                      (.let_ (Op.mk (.zext 32 64) (Arg.var p25.fst, ())) fun p44 =>
                      .let_ (Op.mk (.mul i64) (Arg.var p44.fst, Arg.imm 4#64, ())) fun p45 =>
                      .let_ (Op.mk (.add i64) (Arg.var c.pReason, Arg.var p45.fst, ())) fun p46 =>
                      .load i32 (Arg.var p46.fst) fun ld16 =>
                      .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1136, ())) fun p47 =>
                      .store (Arg.imm (t := i64) 0#64) (Arg.var p47.fst)
                        (.let_ (Op.mk (.add i64) (Arg.var p_18.snd.fst, Arg.imm 1#64, ()))
                            fun p48 =>
                        .call (rs := [i64]) (as := [i64, i32, i32]) (bs := [.bool])
                          "full_analyze_rsn"
                          (Arg.var c.hdr, Arg.var ld16, Arg.var p25.fst, ()) fun p49 =>
                        .jnz (Arg.var p49.fst)
                          (.group (sig := [[]])
                            (fun _Js => .cons (fun _ =>
                              .group (sig := [[]])
                                (fun _Js => .cons (fun _ =>
                                  .jump Js2.fst (Arg.imm 0xFFFFFFFF#32, Arg.var p48.fst, ()))
                                  .nil)
                                fun Js =>
                                .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1136, ()))
                                    fun p51 =>
                                .load i64 (Arg.var p51.fst) fun ld17 =>
                                .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                                    (Arg.var ld17, Arg.imm 3#64, ())) fun p52 =>
                                .jnz (Arg.var p52.fst)
                                  (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ()))
                                    fun p53 =>
                                  .load i64 (Arg.var p53.fst) fun ld18 =>
                                  .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1136, ()))
                                    fun p54 =>
                                  .load i64 (Arg.var p54.fst) fun ld19 =>
                                  .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                      (Arg.var ld18, Arg.var ld19, ())) fun p55 =>
                                  .jnz (Arg.var p55.fst)
                                    (.let_ (Op.mk (.and i32)
                                        (Arg.var ld16, Arg.imm 0x80000000#32, ())) fun p56 =>
                                    .let_ (Op.mk (.cmp .eq i32 .bool rfl)
                                        (Arg.var p56.fst, Arg.imm 0#32, ())) fun p57 =>
                                    .jnz (Arg.var p57.fst)
                                      (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 528, ()))
                                        fun p58 =>
                                      .load i64 (Arg.var p58.fst) fun ld20 =>
                                      .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 176, ()))
                                        fun p59 =>
                                      .load i64 (Arg.var p59.fst) fun ld21 =>
                                      .group (sig := [[]])
                                        (fun _Js3 => .cons (fun _ => .jump Js.fst ()) .nil)
                                        fun Js =>
                                        .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1136, ()))
                                          fun p60 =>
                                        .load i64 (Arg.var p60.fst) fun ld22 =>
                                        .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                            (Arg.var ld22, Arg.imm 3#64, ())) fun p61 =>
                                        .jnz (Arg.var p61.fst)
                                          (.call (rs := [i64]) (as := [i64, i32, i32])
                                            (bs := [.bool]) "full_otfs_bin_m5"
                                            (Arg.var c.hdr, Arg.var ld16, Arg.var ld10, ())
                                            fun p62 =>
                                          .jnz (Arg.var p62.fst)
                                            (.group (sig := [[]])
                                              (fun _Js4 => .cons (fun _ =>
                                                .let_ (Op.mk (.add i64)
                                                  (Arg.var c.hdr, Arg.imm 272, ())) fun p65 =>
                                                .load i64 (Arg.var p65.fst) fun ld =>
                                                .let_ (Op.mk (.add i64)
                                                  (Arg.var c.hdr, Arg.imm 1144, ())) fun p66 =>
                                                .store (Arg.var ld) (Arg.var p66.fst)
                                                (.call (rs := [i64]) (as := [i64]) (bs := [])
                                                  "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
                                                  .ret (Arg.imm 2#64, ()))) .nil)
                                              fun Js =>
                                              .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                                  (Arg.var p48.fst, Arg.imm 1#64, ())) fun p66 =>
                                              .jnz (Arg.var p66.fst)
                                                (.let_ (Op.mk (.add i64)
                                                    (Arg.var c.hdr, Arg.imm 1144, ())) fun p67 =>
                                                .load i64 (Arg.var p67.fst) fun ld23 =>
                                                .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                                    (Arg.var ld23, Arg.var init_res_sz, ()))
                                                  fun p68 =>
                                                .jnz (Arg.var p68.fst)
                                                  (.call (rs := [i64])
                                                    (as := [i64, i32, i64, i64, .bool]) (bs := [])
                                                    "full_otfs_subsume"
                                                    (Arg.var c.hdr, Arg.imm 0#32, Arg.var ld20,
                                                     Arg.var ld21, Arg.imm true, ())
                                                    fun _ => .jump Js.fst ())
                                                  (.jump Js.fst ()))
                                                (.jump Js.fst ()))
                                            (.let_ (Op.mk (.add i64)
                                                (Arg.var c.hdr, Arg.imm 760, ())) fun p65 =>
                                             .load i64 (Arg.var p65.fst) fun ld =>
                                             .let_ (Op.mk (.cmp .ne i64 .bool rfl)
                                                 (Arg.var ld, Arg.imm 0#64, ())) fun p66 =>
                                             .jnz (Arg.var p66.fst)
                                               (.call (rs := [i64]) (as := [i64]) (bs := [])
                                                 "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
                                                 .ret (Arg.imm 0#64, ()))
                                               (.jump Js.fst ())))
                                          (.call (rs := [i64]) (as := [i64, i32, i32])
                                            (bs := [.bool]) "full_otfs_large"
                                            (Arg.var c.hdr, Arg.var ld16, Arg.var ld10, ())
                                            fun p62 =>
                                          .jnz (Arg.var p62.fst)
                                            (.let_ (Op.mk (.add i64)
                                                (Arg.var c.hdr, Arg.imm 528, ())) fun p63 =>
                                            .store (Arg.imm (t := i64) 2#64) (Arg.var p63.fst)
                                              (.let_ (Op.mk (.zext 32 64) (Arg.var ld16, ()))
                                                fun p64 =>
                                              .let_ (Op.mk (.add i64)
                                                  (Arg.var c.hdr, Arg.imm 176, ())) fun p65 =>
                                              .store (Arg.var p64.fst) (Arg.var p65.fst)
                                                (.group (sig := [[]])
                                                  (fun _Js4 => .cons (fun _ =>
                                                    .let_ (Op.mk (.add i64)
                                                      (Arg.var c.hdr, Arg.imm 272, ())) fun p68 =>
                                                    .load i64 (Arg.var p68.fst) fun ld =>
                                                    .let_ (Op.mk (.add i64)
                                                      (Arg.var c.hdr, Arg.imm 1144, ())) fun p69 =>
                                                    .store (Arg.var ld) (Arg.var p69.fst)
                                                    (.call (rs := [i64]) (as := [i64]) (bs := [])
                                                      "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
                                                      .ret (Arg.imm 2#64, ()))) .nil)
                                                  fun Js =>
                                                  .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                                                      (Arg.var p48.fst, Arg.imm 1#64, ()))
                                                      fun p66 =>
                                                  .jnz (Arg.var p66.fst)
                                                    (.let_ (Op.mk (.add i64)
                                                        (Arg.var c.hdr, Arg.imm 1144, ()))
                                                        fun p67 =>
                                                    .load i64 (Arg.var p67.fst) fun ld23 =>
                                                    .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                                        (Arg.var ld23, Arg.var init_res_sz, ()))
                                                      fun p68 =>
                                                    .jnz (Arg.var p68.fst)
                                                      (.call (rs := [i64])
                                                        (as := [i64, i32, i64, i64, .bool])
                                                        (bs := []) "full_otfs_subsume"
                                                        (Arg.var c.hdr, Arg.var ld16, Arg.var ld20,
                                                         Arg.var ld21, Arg.imm false, ())
                                                        fun _ => .jump Js.fst ())
                                                      (.jump Js.fst ()))
                                                    (.jump Js.fst ()))))
                                            (.let_ (Op.mk (.add i64)
                                                (Arg.var c.hdr, Arg.imm 760, ())) fun p65 =>
                                             .load i64 (Arg.var p65.fst) fun ld =>
                                             .let_ (Op.mk (.cmp .ne i64 .bool rfl)
                                                 (Arg.var ld, Arg.imm 0#64, ())) fun p66 =>
                                             .jnz (Arg.var p66.fst)
                                               (.call (rs := [i64]) (as := [i64]) (bs := [])
                                                 "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
                                                 .ret (Arg.imm 0#64, ()))
                                               (.jump Js.fst ()))))
                                      (.jump Js.fst ()))
                                    (.jump Js.fst ()))
                                  (.jump Js.fst ()))
                              .nil)
                            fun Js =>
                            .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p50 =>
                            .load i64 (Arg.var p50.fst) fun ld =>
                            .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0#64, ()))
                              fun p51 =>
                            .jnz (Arg.var p51.fst)
                              (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p52 =>
                              .load i64 (Arg.var p52.fst) fun ld =>
                              .let_ (Op.mk (.sub i64) (Arg.var ld, Arg.imm 1#64, ())) fun p53 =>
                              .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p =>
                              .store (Arg.var p53.fst) (Arg.var p.fst) (.jump Js.fst ()))
                              (.jump Js.fst ()))
                          (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana"
                            (Arg.var c.hdr, ()) fun _ => .ret (Arg.imm 0#64, ()))))))
                  (.jump Js2.fst (Arg.imm 0xFFFFFFFF#32, Arg.var p_18.snd.fst, ())))
                (.jump Js2.fst (Arg.imm 0xFFFFFFFF#32, Arg.var p_18.snd.fst, ())))))
        (.jump J_uip (Arg.var p_18.fst, Arg.imm 0xFFFFFFFF#32, Arg.var p_18.snd.fst, ()))) m_l := by
  obtain ⟨cut_cur, idx, resolved, sl, rfl, hidx_res, hstate, htc_pos, hzero, hml⟩ := hinv_l
  obtain ⟨hlen_l, hw_l, hcov_l, hext_l, hws2_l, hnd_l, hrefs_l, hstat_l, htl_ge, htl_cv, htc_eq,
    hlow_l, hmcov_l, hcm_l, hent_l, hres_l⟩ := hstate
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hlen_l.core_ok.cur_vars_le
  have hte_le := hlen_l.core_ok.trail_end_le
  have htrl_len := hlen_l.core_ok.trl_len
  have hmrk_len := hlen_l.core_ok.mrk_len
  have hlvl_len := hlen_l.core_ok.lvl_len
  have hrsns_len := hlen_l.core_ok.rsns_len
  have htmp_len := hlen_l.core_ok.tmp_len_arr
  have hact_le : (sl.core.tmp_len - 1) + sl.core.tmp_cnt ≤ sl.core.cur_vars := by
    have := Full.fullActiveResolvent_le_cur_vars (by omega : idx ≤ sl.core.trail_end)
      htl_ge (by omega) hlow_l hw_l.trail_lits_lt hw_l.trail_vars_nodup
    rwa [← htc_eq] at this
  have htc_lt64 : sl.core.tmp_cnt < 2 ^ 64 := by omega
  have hidx_lt64 : idx < 2 ^ 64 := by omega
  have hres_lt64 : resolved < 2 ^ 64 := by omega
  have hres1_lt64 : resolved + 1 < 2 ^ 64 := by omega
  fa_fast_steps_nogrp
  · have hidx_eq0 : idx = 0 := by
      have h0 : BitVec.ofNat 64 idx = 0#64 := by assumption
      have h := congrArg BitVec.toNat h0
      rw [bv64_ofNat_toNat hidx_lt64] at h; exact h
    subst hidx_eq0
    have htc0 : sl.core.tmp_cnt = 0 := by
      have h : Full.fullCurTrailIdxs sl.core sl.core.mrk 0 = [] := rfl
      rw [htc_eq, h]; rfl
    omega
  · have hidx_pos : 0 < idx := by
      rcases Nat.eq_zero_or_pos idx with rfl | hpos
      · exact absurd rfl (by assumption : BitVec.ofNat 64 0 ≠ 0#64)
      · exact hpos
    let idx' := idx - 1
    have hiu_te : idx' < sl.core.trail_end := by omega
    have hidx'_bv : BitVec.ofNat 64 idx - 1#64 = BitVec.ofNat 64 idx' := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, bv64_ofNat_toNat hidx_lt64,
        show (1#64 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat]
      omega
    have hidx'_lt : (BitVec.ofNat 64 idx - 1#64).toNat < (BitVec.ofNat 64 idx).toNat := by
      rw [hidx'_bv, bv64_ofNat_toNat hidx_lt64, bv64_ofNat_toNat (by omega : idx' < 2 ^ 64)]
      omega
    have hidx'_nat : (BitVec.ofNat 64 idx - 1#64).toNat = idx' := by
      rw [hidx'_bv, bv64_ofNat_toNat (by omega : idx' < 2 ^ 64)]
    have hidx'_arr : (BitVec.ofNat 64 idx - 1#64).toNat < sl.core.trl.length := by
      rw [hidx'_nat]; omega
    let p_bv : BitVec 32 := sl.core.trl[idx']'(by omega)
    have hp_get : (sl.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hp_lt : p_bv.toNat < 2 * sl.core.cur_vars := hp_get ▸ hw_l.trail_lits_lt idx' hiu_te
    have hpv_lt : p_bv.toNat / 2 < sl.core.cur_vars := by omega
    have htrl_eq : sl.core.trl[(BitVec.ofNat 64 idx - 1#64).toNat] = p_bv := by
      simp only [p_bv, hidx'_nat]
    have hlt_pow : p_bv.toNat / 2 < 2 ^ 64 := by omega
    have hpv_lt_bv : ((p_bv >>> 1#32).setWidth 64).toNat = p_bv.toNat / 2 := by
      rw [BitVec.toNat_setWidth, Deduce1UipTactics.d1_bv32_lshr_1, Nat.mod_eq_of_lt hlt_pow]
    have hpv_lt_p : ((p_bv >>> 1#32).setWidth 64).toNat < sl.core.cur_vars :=
      hpv_lt_bv.symm ▸ hpv_lt
    have hpv_mrk : ((p_bv >>> 1#32).setWidth 64).toNat < sl.core.mrk.length := by
      rw [hpv_lt_bv]; omega
    have hpv_lvl : ((p_bv >>> 1#32).setWidth 64).toNat < sl.core.lvl.length := by
      rw [hpv_lt_bv]; omega
    have hpv_rsns : ((p_bv >>> 1#32).setWidth 64).toNat < sl.core.rsns.length := by
      rw [hpv_lt_bv]; omega
    refine wp_load_of (FullArenaTactics.c0_load_full_trl hidx'_arr hml) ?_
    rw [htrl_eq]
    fa_fast_steps_nogrp
    · have hge : sl.core.cur_vars % 2 ^ 64 ≤ p_bv.toNat / 2 := by assumption
      rw [Nat.mod_eq_of_lt (by omega : sl.core.cur_vars < 2 ^ 64)] at hge
      omega
    · refine wp_join_group (ts := [i32, i64]) (fun ys ml =>
        ∃ (cut_n res_n : Nat) (sn : FullState),
          ys.2.1 = BitVec.ofNat 64 res_n ∧ idx' + res_n ≤ sn.core.trail_end ∧
          Full.FullDeduceStateInv c F0 F_cur cut_n idx' s sn ∧ 0 < sn.core.tmp_cnt ∧
          (res_n = 0 → cut_n = cut ∧
            sn.core.confl_type = s.core.confl_type ∧ sn.core.confl_ref = s.core.confl_ref) ∧
          (FullMem c sn ⋆ R) ml)
        (fun _ ys _ml ⟨cut_n, res_n, sn, hys2, hir, hst, htc, hz, hmn⟩ => by
          fa_fast_steps
          exact hJloop (BitVec.ofNat 64 idx - 1#64, ys.2.1, ()) _ hidx'_lt
            ⟨cut_n, idx', res_n, sn, by rw [hidx'_bv, hys2], hir, hst, htc, hz, hmn⟩) ?_
      intro J2 hJ2
      fa_fast_steps_nogrp
      · have hmnz : sl.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 := by
          have hm1 : sl.core.mrk[p_bv.toNat / 2] ≠ 0#8 := by assumption
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact hm1
        have hcl_eq : BitVec.ofNat 32 sl.core.cur_level = BitVec.ofNat 32 s.core.cur_level := by
          rw [hstat_l.cl]
        have hpv_nat : (BitVec.setWidth 64 (p_bv >>> 1)).toNat = p_bv.toNat / 2 := by
          rw [BitVec.toNat_setWidth, bv32_lshr_1, Nat.mod_eq_of_lt hlt_pow]
        have hpv_lvl' : (BitVec.setWidth 64 (p_bv >>> 1)).toNat < sl.core.lvl.length := by
          rw [hpv_nat]; omega
        refine wp_load_of (FullArenaTactics.c0_load_full_lvl hpv_lvl' hml) ?_
        rw [m5_list_getElem_of_idx (hi := hpv_lvl') (hj := by omega) hpv_nat]
        c0_let_simp
        refine wp_jnz_of (fun hl1 => ?_) (fun hne => ?_)
        · have hpl_eq : sl.core.lvl[p_bv.toNat / 2] = BitVec.ofNat 32 s.core.cur_level :=
            beq_iff_eq.mp hl1
          have hpl_cl : (sl.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = sl.core.cur_level := by
            have hcl32 : sl.core.cur_level < 2 ^ 32 := by have := hw_l.cur_level_le; omega
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hpl_eq, ← hstat_l.cl,
              bv32_ofNat_toNat hcl32]
          have hmnz_tr : sl.core.mrk[(sl.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 := by
            rwa [hp_get]
          have hpl_tr : (sl.core.lvl[(sl.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
              sl.core.cur_level := by
            rwa [hp_get]
          have htc1_bv : (BitVec.ofNat 64 sl.core.tmp_cnt - 1#64).toNat = sl.core.tmp_cnt - 1 := by
            rw [BitVec.toNat_sub, bv64_ofNat_toNat htc_lt64,
              show (1#64 : BitVec 64).toNat = 1 from rfl]
            omega
          let sl1 : FullState :=
            { sl with core := { sl.core with tmp_cnt := sl.core.tmp_cnt - 1 } }
          have hw_1 : Full.FullWitnessCutInv c F0 F_cur cut_cur sl1.core :=
            Full.deduce_same_core_cut hw_l sl.core.mrk sl.core.tmp (sl.core.tmp_cnt - 1)
              sl.core.tmp_len sl.core.min_clr_len
          have hlen_1 : sl1.LengthsOk c :=
            ⟨{ hlen_l.core_ok with }, { hlen_l.scratch_ok with }⟩
          have hcov_1 : Full.FullAnaMarksCov c sl1 := hcov_l
          have hext_1 : Full.FullExtScratchPres s sl1 := hext_l
          have hstat_1 : Full.FullDeduceStaticEq s.core sl1.core :=
            ⟨hstat_l.1, hstat_l.2, hstat_l.3, hstat_l.4, hstat_l.5, hstat_l.6, hstat_l.7,
             hstat_l.8, hstat_l.9, hstat_l.10⟩
          fa_fast_steps_nogrp
          · have htc1 : sl.core.tmp_cnt = 1 := by
              have heq :
                  BitVec.ofNat 64 ((2 ^ 64 - 1 % 2 ^ 64 + sl.core.tmp_cnt) % 2 ^ 64) = 0#64 := by
                assumption
              have hn := congrArg BitVec.toNat heq
              simp only [BitVec.toNat_ofNat, Nat.mod_mod] at hn
              omega
            have hsucc := Full.fullCurTrailIdxs_succ_true hmnz_tr hpl_tr
            have hct0 : (Full.fullCurTrailIdxs sl1.core sl1.core.mrk idx').length = 0 := by
              have hl := congrArg List.length hsucc
              simp only [List.length_append, List.length_singleton] at hl
              have hi' : idx' + 1 = idx := by omega
              change (Full.fullCurTrailIdxs sl.core sl.core.mrk idx').length = 0
              rw [hi', ← htc_eq, htc1] at hl; omega
            have hcl_s := Full.fullCurLits_succ_true hmnz_tr hpl_tr
            rw [hp_get] at hcl_s
            have hent_uip := Full.fullDeduce_uip_entails hct0 hcl_s
              (by simpa only [Full.fullActiveResolvent, Full.fullCurLits, Full.fullCurTrailIdxs,
                sl1, show idx' + 1 = idx by omega] using hent_l)
            fa_fast_steps_nogrp
            refine hJuip (BitVec.ofNat 64 idx - 1#64) (p_bv ^^^ 1#32) (BitVec.ofNat 64 resolved) _
              ⟨cut_cur, idx', sl1, p_bv, hlen_1, hw_1, hcov_1, hext_1, hws2_l, hnd_l, hrefs_l,
               hstat_1, htl_ge, htl_cv, hlow_l, hiu_te, hp_get, hpl_cl, rfl,
               hent_uip, ?_⟩
            simpa only [sl1, htc1_bv] using hm
          · have htc1_pos : 0 < sl.core.tmp_cnt - 1 := by
              have hne :
                  BitVec.ofNat 64 ((2 ^ 64 - 1 % 2 ^ 64 + sl.core.tmp_cnt) % 2 ^ 64) ≠ 0#64 := by
                assumption
              rcases Nat.eq_zero_or_pos (sl.core.tmp_cnt - 1) with h0 | hpos
              · have h1 : sl.core.tmp_cnt = 1 := by omega
                exact absurd (by rw [h1]) hne
              · exact hpos
            let rsn : BitVec 32 := sl.core.rsns[p_bv.toNat / 2]'(by omega)
            have hiu_cut : idx' < cut_cur := hcm_l idx' (by omega) hmnz_tr hpl_tr
            have hr_get : sl.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hri := hw_l.reason_inv_cut idx' hiu_cut
            dsimp only at hri; rw [hp_get, hr_get] at hri
            let sl2 : FullState :=
              { sl1 with scratch := { sl1.scratch with ant_sz := 0#64 } }
            have hlen_2 : sl2.LengthsOk c :=
              ⟨hlen_1.core_ok, { hlen_1.scratch_ok with }⟩
            have hw_2 : Full.FullWitnessCutInv c F0 F_cur cut_cur sl2.core := hw_1
            have hcov_2 : Full.FullAnaMarksCov c sl2 := hcov_1
            have hext_2 : Full.FullExtScratchPres s sl2 := hext_1
            have hstat_2 : Full.FullDeduceStaticEq s.core sl2.core := hstat_1
            have hrsn_ref : rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
                rsn.toNat ∈ fullArenaClauseRefs sl2 := fun hne hlg => by
              have hri' := hri hne
              rw [ite_eq_right (fun h => absurd hlg h)] at hri'
              exact hri'.1
            have hres_add1 : BitVec.ofNat 64 resolved + 1#64 = BitVec.ofNat 64 (resolved + 1) := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_add, bv64_ofNat_toNat hres_lt64,
                show (1#64 : BitVec 64).toNat = 1 from rfl, bv64_ofNat_toNat hres1_lt64,
                Nat.mod_eq_of_lt hres1_lt64]
            have htc2_eq : sl2.core.tmp_cnt =
                (Full.fullCurTrailIdxs sl2.core sl2.core.mrk idx').length := by
              have hsucc := Full.fullCurTrailIdxs_succ_true hmnz_tr hpl_tr
              have hl := congrArg List.length hsucc
              simp only [List.length_append, List.length_singleton] at hl
              have hi' : idx' + 1 = idx := by omega
              change sl.core.tmp_cnt - 1 = (Full.fullCurTrailIdxs sl.core sl.core.mrk idx').length
              rw [hi', ← htc_eq] at hl; omega
            have hent_2 : (cnfOfClauses F_cur).EntailsClause
                (cnfClause (Full.fullActiveResolvent sl2.core sl2.core.tmp sl2.core.mrk
                  sl2.core.tmp_len (idx' + 1))) := by
              simpa only [Full.fullActiveResolvent, Full.fullCurLits, Full.fullCurTrailIdxs,
                sl2, sl1, show idx' + 1 = idx by omega] using hent_l
            have hsl2_res : sl2.scratch.res_sz =
                BitVec.ofNat 64 ((sl2.core.tmp_len - 1) + sl2.core.tmp_cnt + 1) := by
              change sl.scratch.res_sz =
                BitVec.ofNat 64 ((sl.core.tmp_len - 1) + (sl.core.tmp_cnt - 1) + 1)
              rw [hres_l, show (sl.core.tmp_len - 1) + (sl.core.tmp_cnt - 1) + 1 =
                (sl.core.tmp_len - 1) + sl.core.tmp_cnt by omega]
            have hm1 : (FullMem c sl1 ⋆ R) m := by simpa only [sl1, htc1_bv] using hm
            have hpv_rsns1 : (BitVec.setWidth 64 (p_bv >>> 1)).toNat < sl1.core.rsns.length := by
              have := hlen_1.core_ok.rsns_len; have := hlen_1.core_ok.cur_vars_le
              dsimp only [sl1]; rw [hpv_nat]; omega
            fa_fast_steps_nogrp
            refine wp_load_of (FullArenaTactics.c0_load_full_rsns hpv_rsns1 hm1) ?_
            rw [m5_list_getElem_of_idx (hi := hpv_rsns1) (hj := by omega) hpv_nat]
            fa_fast_steps_nogrp
            refine wp_call_of_spec _ _ (hArsn (c.hdr, rsn, p_bv >>> 1#32, ()) _ _ _
              ⟨c, F0, F_cur, cut_cur, sl2, R, rfl, hlen_2, hw_2, hcov_2, htl_cv,
               by dsimp [sl2, sl1]; omega, fun hne hlg => hrsn_ref hne hlg, ?_, ?_⟩)
            · simpa only [sl2, sl1] using (by assumption : (FullMem c _ ⋆ R) _)
            intro ok2 mrk2 tmp2 tc2 tl2 mcl2 arena2 sc2 m2 _ hlen2 hw2 hcov2 hext2 hws2_2
            intro htl2_ge htl2_cv htc2_ge hrefs2 hprops2 hmp2 htp2 hnm2 hnt2 hnd2_t hcnt2 hres2
            intro hok2 hm2
            dsimp only [sl2, sl1] at hlen2 hw2 hcov2 hext2 hws2_2 htl2_ge htl2_cv htc2_ge
            dsimp only [sl2, sl1] at hrefs2 hprops2 hmp2 htp2 hnm2 hnt2 hnd2_t hcnt2 hres2
            dsimp only [sl2, sl1] at hok2 hm2
            let s2 : FullState :=
              { sl2 with
                core := { sl2.core with mrk := mrk2, tmp := tmp2, tmp_cnt := tc2,
                                        tmp_len := tl2, min_clr_len := mcl2, arena := arena2 }
                scratch := sc2 }
            have hnd2 : Full.FullArenaVarsNodup s2 := fun r hr hngr => by
              change r ∈ fullArenaClauseRefs s2 at hr; rw [hrefs2] at hr
              have hll := hprops2 r hr
              change ((fullArenaClauseLits s2 r).map (· / 2)).Nodup
              rw [hll.2.2]; refine hnd_l r hr ?_
              unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hll hngr ⊢
              rw [← hll.2.1]; exact hngr
            have hext_s2 : Full.FullExtScratchPres s s2 :=
              Full.fullExtScratchPres_trans hext_2 hext2
            have hrefs_s2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s :=
              hrefs2.trans hrefs_l
            have hstat_s2 : Full.FullDeduceStaticEq s.core s2.core :=
              ⟨hstat_2.1, hstat_2.2, hstat_2.3, hstat_2.4, hstat_2.5, hstat_2.6, hstat_2.7,
               hstat_2.8, hstat_2.9, hstat_2.10⟩
            cases ok2 with
            | false =>
              fa_fast_steps
              exact Full.deduce_clear_ret0_wp hClear hQ hlen2 hw2 hcov2 hext0 hext_s2
                (hws2_2.trans hws2_l) hnd2 hrefs_s2 hstat_s2 hdm0 hm0_lm hm2
            | true =>
              have hskip_pv : (p_bv >>> 1#32).toNat = p_bv.toNat / 2 := bv32_lshr_1 p_bv
              obtain ⟨hok_ne, hok_ant, hok_lits⟩ := hok2 rfl
              have hsem2 := Full.deduce_loop_rsn_sem hlen_2 hw_2 hstat_2 hsl2_res htl_ge htc2_eq
                hlow_l hmcov_l (fun j hj => hcm_l j (by omega)) hent_2 hiu_cut hiu_te hp_get
                hr_get hmnz hpl_cl hw2 hlen2 hcov2 hext2 hws2_2 htl2_ge htl2_cv htc2_ge
                hrefs2 hnd2
                (fun w hw hnz => hmp2 w (Nat.lt_of_lt_of_le hw hcv_le) hnz) htp2
                (fun w hw h0 hnz => by
                  obtain ⟨l, hl, h1, _, hsk, h3, h4⟩ := hnm2 w
                    (Nat.lt_of_lt_of_le hw hcv_le) h0 hnz
                  exact ⟨l, hl, h1, hskip_pv ▸ hsk, h3, h4⟩)
                (fun j hj1 hj2 => by
                  obtain ⟨h1, h2, hsk, h4⟩ := hnt2 j hj1 hj2
                  exact ⟨h1, h2, hskip_pv ▸ hsk, h4⟩)
                hnd2_t hcnt2 hres2
                ⟨hok_ne, fun l hl => by
                  obtain ⟨hl_lt, hl_r⟩ := hok_lits l hl
                  exact ⟨hl_lt, fun hne => hl_r (hskip_pv ▸ hne)⟩⟩
                hext_2 hws2_l hrefs_l
              obtain ⟨hlen_s2, hw_s2, hcov_s2, hext_s2', hws2_s2, hnd_s2, hrefs_s2',
                hstat_s2', htl2_1, htl2_cv', htc2_eq', hlow2, hmcov2, hcm2, hent2, hres2_eq,
                hall_mrk⟩ := hsem2
              have htc2_pos : 0 < tc2 := Nat.lt_of_lt_of_le htc1_pos htc2_ge
              have htc2_eq_sl : tc2 = (Full.fullCurTrailIdxs sl.core mrk2 idx').length := htc2_eq'
              have hres2_sum : (tl2 - 1) + tc2 + 1 < 2 ^ 64 := by
                have := Full.fullActiveResolvent_le_cur_vars (Nat.le_of_lt hiu_te) htl2_1
                  (by rw [hlen_s2.core_ok.tmp_len_arr]; exact Nat.le_trans htl2_cv' hcv_le)
                  hlow2 hw_s2.trail_lits_lt hw_s2.trail_vars_nodup
                rw [← htc2_eq_sl] at this; omega
              have hres2_pos : (0#64 : BitVec 64).ult sc2.res_sz = true := by
                rw [hres2_eq]
                simp only [BitVec.ult, decide_eq_true_eq,
                  show (0#64 : BitVec 64).toNat = 0 from rfl, bv64_ofNat_toNat hres2_sum]
                omega
              let s3 : FullState :=
                { s2 with
                  scratch := { s2.scratch with res_sz := BitVec.ofNat 64 ((tl2 - 1) + tc2) } }
              have hs3_res_bv : sc2.res_sz - 1#64 = BitVec.ofNat 64 ((tl2 - 1) + tc2) := by
                rw [hres2_eq]; apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_sub, bv64_ofNat_toNat hres2_sum,
                  show (1#64 : BitVec 64).toNat = 1 from rfl,
                  bv64_ofNat_toNat (by omega : (tl2 - 1) + tc2 < 2 ^ 64)]
                omega
              have hlen_s3 : s3.LengthsOk c := ⟨hlen_s2.core_ok, { hlen_s2.scratch_ok with }⟩
              have hcov_s3 : Full.FullAnaMarksCov c s3 := hcov_s2
              have hext_s3 : Full.FullExtScratchPres s s3 := hext_s2'
              have hrefs_s3 : fullArenaClauseRefs s3 = fullArenaClauseRefs s := hrefs_s2'
              have hstat_s3 : Full.FullDeduceStaticEq s.core s3.core := hstat_s2'
              have hst_s3 : Full.FullDeduceStateInv c F0 F_cur cut_cur idx' s s3 :=
                ⟨hlen_s3, hw_s2, hcov_s3, hext_s3, hws2_s2, hnd_s2, hrefs_s3, hstat_s3,
                 htl2_1, htl2_cv', htc2_eq', hlow2, hmcov2, hcm2, hent2, rfl⟩
              fa_fast_steps_nogrp
              refine wp_join_group (ts := []) (fun _ ml => (FullMem c s3 ⋆ R) ml)
                (fun _ ⟨⟩ ml hm3 => ?_) ?_
              · refine wp_join_group (ts := []) (fun _ ml =>
                  ∃ (cut_n : Nat) (s_n : FullState),
                    idx' + (resolved + 1) ≤ s_n.core.trail_end ∧
                    Full.FullDeduceStateInv c F0 F_cur cut_n idx' s s_n ∧
                    0 < s_n.core.tmp_cnt ∧ (FullMem c s_n ⋆ R) ml)
                  (fun _ ⟨⟩ ml ⟨cut_n, s_n, hir_n, hst_n, htc_n, hmn⟩ => by
                    fa_fast_steps
                    exact hJ2 (0xFFFFFFFF#32, BitVec.ofNat 64 resolved + 1#64, ()) _
                      ⟨cut_n, resolved + 1, s_n, hres_add1, hir_n, hst_n, htc_n,
                       fun h => by omega, hmn⟩) ?_
                intro J_ot hJot
                have hir3 : idx' + (resolved + 1) ≤ s3.core.trail_end := by
                  rw [hstat_s3.te, ← hstat_l.te]; omega
                fa_fast_steps_nogrp
                · have hrsn_lg : (rsn &&& 0x80000000#32) = 0#32 := by assumption
                  have hant_pos_nat : 3 ≤ sc2.ant_sz.toNat := by
                    have h0 : 3 % 2 ^ 64 ≤ s3.scratch.ant_sz.toNat := by assumption
                    simpa [s3] using h0
                  have hres_ult : s3.scratch.res_sz.ult sc2.ant_sz = true := by
                    have h0 : s3.scratch.res_sz.toNat < s3.scratch.ant_sz.toNat := by assumption
                    simpa only [BitVec.ult, decide_eq_true_eq, s3] using h0
                  refine wp_join_group (ts := []) (fun _ ml =>
                    ∃ (cut_n : Nat) (s_n : FullState),
                      idx' + (resolved + 1) ≤ s_n.core.trail_end ∧
                      Full.FullDeduceStateInv c F0 F_cur cut_n idx' s s_n ∧
                      0 < s_n.core.tmp_cnt ∧ (FullMem c s_n ⋆ R) ml)
                    (fun _ ⟨⟩ ml h => hJot () ml h) ?_
                  intro J_in hJin
                  have hri2 := hw_s2.reason_inv_cut idx' hiu_cut
                  dsimp only at hri2
                  have hp_get_s2 : (s2.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat := by
                    rw [hstat_s2'.trl, ← hstat_l.trl, hp_get]
                  have hr_get_s2 : s2.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn := by
                    rw [hstat_s2'.rsns, ← hstat_l.rsns, hr_get]
                  rw [hp_get_s2, hr_get_s2] at hri2
                  have hri2 := hri2 hok_ne
                  rw [ite_eq_right (fun h => absurd hrsn_lg h)] at hri2
                  obtain ⟨href_s2, hng_s2, _⟩ := hri2
                  have hte_s3 : idx' < s3.core.trail_end := by
                    rw [hstat_s3.te, ← hstat_l.te]; exact hiu_te
                  have hpl_s3 : (s3.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat =
                      s3.core.cur_level := by
                    rw [hstat_s3.lvl, hstat_s3.cl, ← hstat_l.lvl, ← hstat_l.cl, hpl_cl]
                  have hcl_s3_pos : 0 < s3.core.cur_level := by
                    rw [hstat_s3.cl]; exact hcur_pos
                  have hp_lt_s3 : p_bv.toNat < 2 * s3.core.cur_vars := by
                    rw [hstat_s3.cv, ← hstat_l.cv]; exact hp_lt
                  have heq_s2 : fullArenaClauseLits s2 rsn.toNat = fullRsnLits sl2 rsn := by
                    have hll :=
                      (hprops2 rsn.toNat (hrefs_l ▸ (hrsn_ref hok_ne hrsn_lg))).2.2
                    change fullArenaClauseLits s2 rsn.toNat =
                      fullArenaClauseLits sl2 rsn.toNat at hll
                    unfold fullRsnLits
                    rw [ite_eq_right (fun h => hok_ne h),
                      ite_eq_right (fun h => absurd hrsn_lg h)]
                    exact hll
                  have hant_s2 : sc2.ant_sz = BitVec.ofNat 64 ((fullRsnLits s2 rsn).countP fun l =>
                      decide (l / 2 < s2.core.cur_vars ∧
                        0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat ∧
                        (s2.core.lvl[l / 2]?.getD 0#32).toNat ≤ s2.core.cur_level)) := by
                    have heq_r : fullRsnLits s2 rsn = fullRsnLits sl2 rsn := by
                      unfold fullRsnLits
                      rw [ite_eq_right (fun h => hok_ne h),
                        ite_eq_right (fun h => absurd hrsn_lg h)]
                      exact heq_s2
                    simpa only [heq_r, BitVec.zero_add] using hok_ant
                  have hall_s3 : ∀ l ∈ fullArenaClauseLitsCore s3.core rsn.toNat,
                      l / 2 ≠ p_bv.toNat / 2 → 0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat →
                      mrk2[l / 2]?.getD 0#8 ≠ 0#8 := by
                    intro l hl hne hpos
                    have hl_sl2 : l ∈ fullRsnLits sl2 rsn := heq_s2 ▸ hl
                    have hpos' : 0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat := by
                      simpa [s3] using hpos
                    exact hall_mrk l hl_sl2 hne hpos'
                  have hzero_b : resolved = 0 →
                      cut = cut ∧ idx' < cut ∧
                      (s.core.trl[idx']?.getD 0#32).toNat = p_bv.toNat ∧
                      s.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn ∧
                      rsn ≠ 0xFFFFFFFF#32 ∧ (rsn &&& 0x80000000#32) = 0#32 ∧
                      sl.core.confl_type = s.core.confl_type ∧
                      sl.core.confl_ref = s.core.confl_ref := by
                    intro hr0; obtain ⟨hc_eq, hct_eq, hcr_eq⟩ := hzero hr0
                    refine ⟨rfl, hc_eq ▸ hiu_cut, ?_, ?_, hok_ne, hrsn_lg, hct_eq, hcr_eq⟩
                    · rw [← hstat_l.trl, hp_get]
                    · rw [← hstat_l.rsns, hr_get]
                  fa_fast_steps_nogrp
                  · have hant3 : sc2.ant_sz = 3#64 := by assumption
                    have hbin_ent := otfs_entails_bin_of_res_lt_ant hw_s2 hnd_s2 hlen2
                      htl2_1 htl2_cv'
                      (by rw [hlen_s2.core_ok.tmp_len_arr]; exact Nat.le_trans htl2_cv' hcv_le)
                      hlow2 hmcov2 htc2_eq' hent2 hiu_cut hte_s3 hp_get_s2 hr_get_s2
                      hpl_s3 hcl_s3_pos hok_ne hrsn_lg hall_s3 rfl hant_s2 hres_ult
                      (by rw [hant3])
                    refine wp_call_of_spec _ _ (hOtfsBin (c.hdr, rsn, p_bv, ()) _ _ _
                      ⟨c, F0, F_cur, cut_cur, idx', s3, R, rfl, hlen_s3, hw_s2, hnd_s2,
                       hstat_s3.dm.trans hdm0, href_s2, hng_s2, hp_lt_s3, hiu_cut, hp_get_s2,
                       hr_get_s2, hpl_s3, hbin_ent, hm3, ?_⟩)
                    intro ok_b ar_b ag_b wv_b ws_b wl_b wu_b nb_b ct_b cr_b c0_b c1_b oom_b
                      sc_b m_b _ hlen_b hw_b hnd_b hext_b hws1_b hws2_b hres_b hrefs_b hok_b hm_b
                    dsimp only [s3, s2] at hlen_b hw_b hnd_b hext_b hws1_b hws2_b hres_b
                    dsimp only [s3, s2] at hrefs_b hok_b hm_b
                    let s_b : FullState :=
                      { s3 with
                        core := { s3.core with arena := ar_b, arena_garbage := ag_b,
                                               wvec := wv_b, wstk := ws_b, wlen := wl_b,
                                               wusable := wu_b, num_binary := nb_b,
                                               confl_type := ct_b, confl_ref := cr_b,
                                               confl_lit0 := c0_b, confl_lit1 := c1_b,
                                               oom := oom_b }
                        scratch := sc_b }
                    have hcov_b :=
                      m5_deduce_anaMarksCov_of_same (s2 := s_b) hcov_s3 rfl rfl rfl hws1_b
                    have hext_sb := Full.fullExtScratchPres_trans hext_s3 hext_b
                    have hrefs_sb : fullArenaClauseRefs s_b = fullArenaClauseRefs s :=
                      hrefs_b.trans hrefs_s3
                    cases ok_b with
                    | true =>
                      obtain ⟨hct_b, hconfl_b⟩ := hok_b rfl
                      fa_fast_steps_nogrp
                      refine m5_deduce_otfs_ret2_subsume_wp (init_res_sz := init_res_sz)
                        (p := p_bv) (rsn := rsn) (new_confl_arg := Arg.imm 0#32)
                        (to_bin := true) hClear hOtfsSub hQ hw0 hconfl0 hext0 hdm0
                        hm0_lm hlen_b hw_b hcov_b hext_sb (hws2_b.trans hws2_s2) hnd_b hrefs_sb
                        hstat_s3.repack hconfl_b hte_s3 hres1_lt64 (fun _ => hct_b)
                        (fun hr0 => by
                          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hzero_b hr0
                          exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun hc => by cases hc⟩)
                        hm_b
                    | false =>
                      fa_fast_steps_nogrp
                      · exact Full.deduce_clear_ret0_wp hClear hQ hlen_b hw_b hcov_b hext0 hext_sb
                          (hws2_b.trans hws2_s2) hnd_b hrefs_sb hstat_s3.repack hdm0 hm0_lm hm_b
                      · exact hJin () m_b ⟨idx', s_b, hir3,
                          ⟨hlen_b, hw_b, hcov_b, hext_sb, hws2_b.trans hws2_s2, hnd_b, hrefs_sb,
                           hstat_s3.repack, htl2_1, htl2_cv', htc2_eq', hlow2, hmcov2,
                           fun j hj _ _ => hj, hent2, hres_b⟩,
                          htc2_pos, hm_b⟩
                  · have hlarge_ent := otfs_entails_large_of_res_lt_ant hw_s2 hnd_s2 hlen2
                      htl2_1
                      (by rw [hlen_s2.core_ok.tmp_len_arr]; exact Nat.le_trans htl2_cv' hcv_le)
                      hlow2 hmcov2 htc2_eq' hent2 hiu_cut hte_s3 hp_get_s2 hr_get_s2 hpl_s3
                      hcl_s3_pos hok_ne hrsn_lg hall_s3 rfl hant_s2 hres_ult
                    refine wp_call_of_spec _ _ (hOtfsLarge (c.hdr, rsn, p_bv, ()) _ _ _
                      ⟨c, F0, F_cur, cut_cur, idx', s3, R, rfl, hlen_s3, hw_s2, hnd_s2,
                       hstat_s3.dm.trans hdm0, href_s2, hng_s2, hp_lt_s3, hiu_cut, hp_get_s2,
                       hr_get_s2, hpl_s3, hlarge_ent, hm3, ?_⟩)
                    intro ok_l ar_l wv_l ws_l wl_l wu_l oom_l sc_l m_l _ hlen_l hw_l hnd_l
                    intro hext_l hws1_l hws2_l hres_l hrefs_l hok_l hm_l
                    dsimp only [s3, s2] at hlen_l hw_l hnd_l hext_l hws1_l hws2_l hres_l
                    dsimp only [s3, s2] at hrefs_l hok_l hm_l
                    let s_l : FullState :=
                      { s3 with
                        core := { s3.core with arena := ar_l, wvec := wv_l, wstk := ws_l,
                                               wlen := wl_l, wusable := wu_l, oom := oom_l }
                        scratch := sc_l }
                    have hcov_l' :=
                      m5_deduce_anaMarksCov_of_same (s2 := s_l) hcov_s3 rfl rfl rfl hws1_l
                    have hext_sl := Full.fullExtScratchPres_trans hext_s3 hext_l
                    have hrefs_sl : fullArenaClauseRefs s_l = fullArenaClauseRefs s :=
                      hrefs_l.trans hrefs_s3
                    cases ok_l with
                    | true =>
                      obtain ⟨href_l, hng_l, hlits_l⟩ := hok_l rfl
                      fa_fast_steps_nogrp
                      let s_ot : FullState :=
                        { s_l with core := { s_l.core with confl_type := 2#64,
                                                           confl_ref := rsn.setWidth 64 } }
                      have hlen_ot : s_ot.LengthsOk c :=
                        ⟨{ hlen_l.core_ok with }, hlen_l.scratch_ok⟩
                      have hw_ot : Full.FullWitnessCutInv c F0 F_cur idx' s_ot.core :=
                        m5_deduce_cut_with_confl hw_l 2#64 (rsn.setWidth 64)
                      have hconfl_ot : Full.FullConflictOkCut F_cur idx' s_ot :=
                        Full.deduce_large_conflOk_of href_l hng_l hlits_l
                      refine m5_deduce_otfs_ret2_subsume_wp (init_res_sz := init_res_sz)
                        (p := p_bv) (rsn := rsn)
                        (new_confl_arg := Arg.var sl1.core.rsns[p_bv.toNat / 2])
                        (to_bin := false) hClear hOtfsSub hQ hw0
                        hconfl0 hext0 hdm0 hm0_lm hlen_ot hw_ot hcov_l' hext_sl
                        (hws2_l.trans hws2_s2) hnd_l hrefs_sl hstat_s3.repack hconfl_ot hte_s3
                        hres1_lt64 (fun h => by cases h) (fun hr0 => by
                          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hzero_b hr0
                          have hz : (rsn.setWidth 64).toNat = rsn.toNat := by
                            rw [BitVec.toNat_setWidth,
                              Nat.mod_eq_of_lt (Nat.lt_trans rsn.isLt (by decide))]
                          exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun _ => ⟨href_l, rfl, hz⟩⟩)
                        ?_
                      exact (by assumption : (FullMem c s_ot ⋆ R) _)
                    | false =>
                      fa_fast_steps_nogrp
                      · exact Full.deduce_clear_ret0_wp hClear hQ hlen_l hw_l hcov_l' hext0 hext_sl
                          (hws2_l.trans hws2_s2) hnd_l hrefs_sl hstat_s3.repack hdm0 hm0_lm hm_l
                      · exact hJin () m_l ⟨idx', s_l, hir3,
                          ⟨hlen_l, hw_l, hcov_l', hext_sl, hws2_l.trans hws2_s2, hnd_l, hrefs_sl,
                           hstat_s3.repack, htl2_1, htl2_cv', htc2_eq', hlow2, hmcov2,
                           fun j hj _ _ => hj, hent2, hres_l⟩,
                          htc2_pos, hm_l⟩
                · fa_fast_steps; exact hJot () ml ⟨cut_cur, s3, hir3, hst_s3, htc2_pos, hm3⟩
                · fa_fast_steps; exact hJot () ml ⟨cut_cur, s3, hir3, hst_s3, htc2_pos, hm3⟩
                · fa_fast_steps; exact hJot () ml ⟨cut_cur, s3, hir3, hst_s3, htc2_pos, hm3⟩
              · intro J_res hJres
                fa_fast_steps
                · refine hJres () _ ?_
                  dsimp only [s3]
                  rw [← hs3_res_bv]
                  exact (by assumption)
                · exfalso
                  have hbad : ¬ 0 % 2 ^ 64 < sc2.res_sz.toNat := by assumption
                  have hlt : (0#64 : BitVec 64).toNat < sc2.res_sz.toNat := by
                    simpa only [BitVec.ult, decide_eq_true_eq] using hres2_pos
                  exact hbad (by simpa using hlt)
        · fa_fast_steps
          have hnot : ¬ (sl.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
              (sl.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = sl.core.cur_level) := by
            intro ⟨_, hcl⟩
            have hl_eq : sl.core.lvl[p_bv.toNat / 2] = BitVec.ofNat 32 s.core.cur_level := by
              apply BitVec.eq_of_toNat_eq
              have hcl32' : sl.core.cur_level < 2 ^ 32 := by have := hw_l.cur_level_le; omega
              rw [bv32_ofNat_toNat (hstat_l.cl ▸ hcl32'), ← hstat_l.cl]
              simpa [List.getElem?_eq_getElem (by omega : p_bv.toNat / 2 < sl.core.lvl.length)]
                using hcl
            rw [beq_iff_eq.mpr hl_eq] at hne
            cases hne
          have hnot' : ¬ (sl.core.mrk[(sl.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
              (sl.core.lvl[(sl.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                sl.core.cur_level) := by rwa [hp_get]
          exact hJ2 (0xFFFFFFFF#32, BitVec.ofNat 64 resolved, ()) m_l
            ⟨cut_cur, resolved, sl, rfl, by omega,
             ⟨hlen_l, hw_l, hcov_l, hext_l, hws2_l, hnd_l, hrefs_l, hstat_l, htl_ge, htl_cv,
              by
                rw [htc_eq, show idx = idx' + 1 by omega, Full.fullCurTrailIdxs_succ_eq_self hnot'],
              hlow_l, hmcov_l, fun j hj => hcm_l j (by omega),
              by simpa only [Full.fullActiveResolvent, show idx = idx' + 1 by omega,
                Full.fullCurLits_succ_eq_self hnot'] using hent_l,
              hres_l⟩,
             htc_pos, hzero, hml⟩
      · fa_fast_steps
        have hnot : ¬ (sl.core.mrk[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
            (sl.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = sl.core.cur_level) := by
          intro ⟨hm, _⟩
          have hm0 : sl.core.mrk[p_bv.toNat / 2] = 0#8 := by assumption
          apply hm; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hm0
        have hnot' : ¬ (sl.core.mrk[(sl.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
            (sl.core.lvl[(sl.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
              sl.core.cur_level) := by rwa [hp_get]
        exact hJ2 (0xFFFFFFFF#32, BitVec.ofNat 64 resolved, ()) m_l
          ⟨cut_cur, resolved, sl, rfl, by omega,
           ⟨hlen_l, hw_l, hcov_l, hext_l, hws2_l, hnd_l, hrefs_l, hstat_l, htl_ge, htl_cv,
            by rw [htc_eq, show idx = idx' + 1 by omega, Full.fullCurTrailIdxs_succ_eq_self hnot'],
            hlow_l, hmcov_l, fun j hj => hcm_l j (by omega),
            by simpa only [Full.fullActiveResolvent, show idx = idx' + 1 by omega,
              Full.fullCurLits_succ_eq_self hnot'] using hent_l,
            hres_l⟩,
           htc_pos, hzero, hml⟩
  · exfalso
    have hbad : ¬ 0 % 2 ^ 64 < sl.core.tmp_cnt % 2 ^ 64 := by assumption
    rw [Nat.zero_mod, Nat.mod_eq_of_lt htc_lt64] at hbad
    exact hbad htc_pos

private theorem m5_deduce_uip_exit_body_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut_b idx_u : Nat}
    {s sb : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mb : Mem 64}
    {p_bv : BitVec 32}
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ Full.FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → Full.FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → Full.FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
        Full.FullCutInvW c F0 F_cur cut' s' ∧ s'.core.cur_level = s.core.cur_level ∧
        Full.FullConflictOkCut F_cur cut' s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hext0 : Full.FullExtScratchOk c s) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s)
    (hlen_b : sb.LengthsOk c) (hw_b : Full.FullWitnessCutInv c F0 F_cur cut_b sb.core)
    (hcov_b : Full.FullAnaMarksCov c sb) (hext_b : Full.FullExtScratchPres s sb)
    (hws2_b : sb.scratch.work_stk2 = s.scratch.work_stk2) (hnd_b : Full.FullArenaVarsNodup sb)
    (hrefs_b : fullArenaClauseRefs sb = fullArenaClauseRefs s)
    (hstat_b : Full.FullDeduceStaticEq s.core sb.core)
    (htl1 : 1 ≤ sb.core.tmp_len) (htl_cv : sb.core.tmp_len ≤ sb.core.cur_vars)
    (hlow_b : Full.FullLowerInv c sb.core sb.core.tmp sb.core.mrk sb.core.tmp_len)
    (hiu_te : idx_u < sb.core.trail_end)
    (hp_get : (sb.core.trl[idx_u]?.getD 0#32).toNat = p_bv.toNat)
    (hpl_cl : (sb.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = sb.core.cur_level)
    (hent_b : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((p_bv ^^^ 1#32).toNat :: Full.fullLowerLits sb.core.tmp sb.core.tmp_len)))
    (hmb : (FullMem c sb ⋆ R) mb) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i32 .bool rfl)
        (Arg.var (p_bv ^^^ 1#32), Arg.imm 0xFFFFFFFF#32, ())) fun p19 =>
      .jnz (Arg.var p19.fst)
        (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
          fun _ => .ret (Arg.imm 0#64, ()))
        (.let_ (Op.mk (.sext 32 64) (Arg.imm 0#32, ())) fun p20 =>
          .let_ (Op.mk (.mul i64) (Arg.var p20.fst, Arg.imm 4#64, ())) fun p21 =>
            .let_ (Op.mk (.add i64) (Arg.var c.pTmp, Arg.var p21.fst, ())) fun p22 =>
              .store (Arg.var (t := i32) (p_bv ^^^ 1#32)) (Arg.var p22.fst)
                (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272, ())) fun p23 =>
                  .load i64 (Arg.var p23.fst) fun ld =>
                    .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p24 =>
                      .store (Arg.var ld) (Arg.var p24.fst)
                        (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana"
                          (Arg.var c.hdr, ()) fun _ => .ret (Arg.imm 1#64, ()))))) mb := by
  let uip := p_bv ^^^ 1#32
  have hmaxv := c.hmaxv; have hcv_le := hlen_b.core_ok.cur_vars_le; unfold dimacsBound at hmaxv
  have hp_lt : p_bv.toNat < 2 * sb.core.cur_vars := hp_get ▸ hw_b.trail_lits_lt idx_u hiu_te
  have huip_nat : uip.toNat = p_bv.toNat ^^^ 1 := bv32_xor_1 p_bv
  have huip_lt : uip.toNat < 2 * sb.core.cur_vars := huip_nat ▸ litNeg_lt_two_mul hp_lt
  have huip_ne : uip ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff (by omega)
  have htb_len : sb.core.tmp.length = c.max_vars := hlen_b.core_ok.tmp_len_arr
  have h0_tb : 0 < sb.core.tmp.length := by have := hw_b.cur_level_le; omega
  let tmp0 := sb.core.tmp.set 0 uip
  have htmp0_len : tmp0.length = c.max_vars := by rw [List.length_set, htb_len]
  let s0 : FullState := { sb with core := { sb.core with tmp := tmp0 } }
  have htmp0_gt0 : ∀ j, 1 ≤ j → tmp0[j]? = sb.core.tmp[j]? := fun _ _ =>
    List.getElem?_set_ne (by omega)
  have htmp0_0 : tmp0[0]? = some uip := List.getElem?_set_self h0_tb
  have hlow0 : Full.FullLowerInv c s0.core tmp0 sb.core.mrk sb.core.tmp_len :=
    ⟨fun j h1 h2 => htmp0_gt0 j h1 ▸ hlow_b.1 j h1 h2,
     fun j1 j2 h1 h12 h2 => by
       have := hlow_b.2 j1 j2 h1 h12 h2
       rwa [htmp0_gt0 j1 h1, htmp0_gt0 j2 (by omega)]⟩
  have hlowLits0 : Full.fullLowerLits tmp0 sb.core.tmp_len =
      Full.fullLowerLits sb.core.tmp sb.core.tmp_len := by
    change Full.fullLowerLits (sb.core.tmp.set 0 uip) sb.core.tmp_len =
      Full.fullLowerLits sb.core.tmp sb.core.tmp_len
    unfold Full.fullLowerLits; cases sb.core.tmp <;> rfl
  have htmp_take : (tmp0.take sb.core.tmp_len).map BitVec.toNat =
      uip.toNat :: Full.fullLowerLits tmp0 sb.core.tmp_len := by
    have h_eq : tmp0 = uip :: sb.core.tmp.tail := by
      cases h_sb : sb.core.tmp with
      | nil => rw [h_sb] at h0_tb; simp at h0_tb
      | cons x xs => simp [tmp0, h_sb]
    rw [h_eq]
    cases htl : sb.core.tmp_len with
    | zero => omega
    | succ n => simp [Full.fullLowerLits]
  have hs0_len : s0.LengthsOk c :=
    ⟨{ hlen_b.core_ok with tmp_len_arr := by dsimp [s0, tmp0]; simp [htb_len] }, hlen_b.scratch_ok⟩
  have hw0 : Full.FullWitnessCutInv c F0 F_cur cut_b s0.core :=
    Full.deduce_same_core_cut hw_b sb.core.mrk tmp0 sb.core.tmp_cnt sb.core.tmp_len
      sb.core.min_clr_len
  have hcov0 : Full.FullAnaMarksCov c s0 :=
    m5_deduce_anaMarksCov_of_same (s2 := s0) hcov_b rfl rfl rfl rfl
  have hnd0 : Full.FullArenaVarsNodup s0 := hnd_b
  have hrefs0 : fullArenaClauseRefs s0 = fullArenaClauseRefs s := hrefs_b
  have hstat0 : Full.FullDeduceStaticEq s.core s0.core :=
    ⟨hstat_b.1, hstat_b.2, hstat_b.3, hstat_b.4, hstat_b.5, hstat_b.6, hstat_b.7, hstat_b.8,
     hstat_b.9, hstat_b.10⟩
  have huip_fals : sb.core.vals[uip.toNat]?.getD 0#8 = 0xFF#8 :=
    (hw_b.vals_false_iff uip.toNat huip_lt).mpr ⟨idx_u, hiu_te, by
      rw [hp_get, huip_nat]; exact (litNeg_litNeg _).symm⟩
  have huip_cl : (sb.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = sb.core.cur_level := by
    rwa [huip_nat, fullInv_var_xor1]
  c0_let_simp
  refine wp_jnz_of (fun hc => absurd (by simpa [uip] using hc) huip_ne) (fun _ => ?_)
  c0_let_simp
  refine wp_store_sep (Deduce1UipTactics.d1_store_full_tmp0_mul uip h0_tb hmb)
    (fun m_st hm_st => ?_)
  refine m5_deduce_res_clear_ret_wp hClear 1#64 hs0_len hw0 hcov0 hext0 hext_b hws2_b
    hnd0 hrefs0 hstat0 hdm0 hm0_lm hm_st
    fun mrk_c m_c hlen_c hotfs_c _ _ hcv_c hcl_c hfuel_c hws2_c hm_c => by
      let s_c : FullState :=
        { s0 with
          core := { s0.core with mrk := mrk_c, min_clr_len := 0 }
          scratch := { s0.scratch with res_sz := BitVec.ofNat 64 s0.core.min_clr_len } }
      have hnd_uip := Full.fullTmpTake_uip_nodup htl1 (by omega) htmp0_0 hlow0 huip_cl
      refine hQ 1#64 s_c m_c hlen_c (Or.inr (Or.inl rfl)) hcv_c hfuel_c hws2_c
        (fun h => by cases h) (fun h => by cases h) (fun _ => ?_) (fun h => by cases h) hm_c
      refine ⟨hotfs_c, hcl_c, htl1, htl_cv, hnd_uip, fun k hk => ?_, fun k hk1 hk2 => ?_, ?_, ?_⟩
      · cases k with
        | zero => rw [htmp0_0, Option.getD_some]; exact ⟨huip_lt, huip_fals⟩
        | succ k' => let hlk := hlow0.1 (k' + 1) (by omega) hk; exact ⟨hlk.1, hlk.2.1⟩
      · let hlk := hlow0.1 k hk1 hk2; exact ⟨hlk.2.2.1, hlk.2.2.2.1⟩
      · rw [htmp0_0, Option.getD_some]; exact huip_cl
      · rw [htmp_take, hlowLits0]; exact hent_b

theorem full_deduce_1uip_m5_wp (Γ : Env)
    (hAlit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, Full.fullAnalyzeRsnSpec a m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin_m5" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X) :
    ∀ a m Q X, Full.fullDeduce1uipSpec a m Q X →
      Func.wp Γ full_deduce_1uip_m5_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, cut, s, R, rfl, hinv, hcur_pos, hconfl, hm0, hQ⟩
  unfold Func.wp full_deduce_1uip_m5_body
  have ⟨hlen0, hw0, hlm0, hnd0, hext0, hdm0⟩ := hinv
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hte_le := hlen0.core_ok.trail_end_le
  have hotfs0 : Full.FullOtfsInvW c F0 F_cur s :=
    ⟨hlen0, hw0.toFullOtfsWitnessInv, hlm0, hnd0, hext0, hdm0⟩
  fa_fast_steps_nogrp
  · exact hQ 0#64 s m0 hlen0 (Or.inl rfl) rfl rfl rfl (fun h => by cases h)
      (fun _ => hotfs0) (fun h => by cases h) (fun h => by cases h) hm0
  · refine wp_join_group (ts := [.bool]) (fun ys m_sd =>
      ∃ s1 : FullState,
        s1.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut s1.core ∧
        Full.FullAnaMarksCov c s1 ∧ Full.FullExtScratchPres s s1 ∧
        s1.scratch.work_stk2 = s.scratch.work_stk2 ∧ Full.FullArenaVarsNodup s1 ∧
        fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
        Full.FullDeduceStaticEq s.core s1.core ∧ 1 ≤ s1.core.tmp_len ∧
        s1.core.tmp_len ≤ s1.core.cur_vars ∧
        s1.core.confl_type = s.core.confl_type ∧ s1.core.confl_ref = s.core.confl_ref ∧
        (ys.fst = true → Full.FullDeduceStateInv c F0 F_cur cut s1.core.trail_end s s1) ∧
        (FullMem c s1 ⋆ R) m_sd) ?_ ?_
    · rintro _ ⟨seed_ok, ⟨⟩⟩ m_sd ⟨s1, hlen1, hw1, hcov1, hext1, hws2_1, hnd1, hrefs1, hstat1,
        htl1, htl_cv1, hct_s1, hcr_s1, hsd1, hm1⟩
      fa_fast_steps_nogrp
      refine wp_join_group (ts := []) (fun _ m_cl =>
        ∃ s_cl : FullState,
          s_cl.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut s_cl.core ∧
          Full.FullAnaMarksCov c s_cl ∧ Full.FullExtScratchPres s s_cl ∧
          s_cl.scratch.work_stk2 = s.scratch.work_stk2 ∧ Full.FullArenaVarsNodup s_cl ∧
          fullArenaClauseRefs s_cl = fullArenaClauseRefs s ∧
          Full.FullDeduceStaticEq s.core s_cl.core ∧
          (seed_ok = true → s_cl.core.tmp_len = 1 → F0.Unsat) ∧
          (FullMem c s_cl ⋆ R) m_cl)
        (fun _ ⟨⟩ m_cl ⟨s_cl, hlen_cl, hw_cl, hcov_cl, hext_cl, hws2_cl, hnd_cl, hrefs_cl,
            hstat_cl, hunsat, hm_cl⟩ =>
          Full.deduce_clear_unsat_goal_wp hClear hQ hlen_cl hw_cl hcov_cl hext0 hext_cl hws2_cl
            hnd_cl hrefs_cl hstat_cl hdm0 hlm0 hunsat hm_cl) ?_
      intro J_cl hJcl
      fa_fast_steps_nogrp
      · have hso_t : (seed_ok, ()).fst = true := by assumption
        have hst1 := hsd1 hso_t
        have htc_lt : s1.core.tmp_cnt < 2 ^ 64 := by
          have := Full.fullActiveResolvent_le_cur_vars (le_refl _) htl1
            (by rw [hlen1.core_ok.tmp_len_arr]
                exact Nat.le_trans htl_cv1 (by rw [hstat1.cv]; exact hcv_le))
            hst1.low hw1.trail_lits_lt hw1.trail_vars_nodup
          rw [← hst1.tc_eq] at this; have := hstat1.cv; omega
        exact hJcl () m_sd ⟨s1, hlen1, hw1, hcov1, hext1, hws2_1, hnd1, hrefs1, hstat1,
          fun _ htl_eq => by
            have htc0 : s1.core.tmp_cnt = 0 := by
              have h :=
                congrArg BitVec.toNat (by assumption : BitVec.ofNat 64 s1.core.tmp_cnt = 0#64)
              rw [bv64_ofNat_toNat htc_lt] at h; exact h
            have hcur0 : Full.fullCurLits s1.core s1.core.mrk s1.core.trail_end = [] := by
              have hnil : Full.fullCurTrailIdxs s1.core s1.core.mrk s1.core.trail_end = [] :=
                List.eq_nil_of_length_eq_zero (by rw [← hst1.tc_eq, htc0])
              unfold Full.fullCurLits; rw [hnil]; rfl
            have hlow0 : Full.fullLowerLits s1.core.tmp 1 = [] := by
              unfold Full.fullLowerLits; cases s1.core.tmp <;> rfl
            have hent_nil : (cnfOfClauses F_cur).EntailsClause (cnfClause []) := by
              simpa [Full.fullActiveResolvent, htl_eq, hlow0, hcur0] using hst1.ent
            exact hw1.ext_sound.2 (unsat_of_entails_nil hent_nil), hm1⟩
      · have hso_t : (seed_ok, ()).fst = true := by assumption
        have hst1 := hsd1 hso_t
        have htc_pos : 0 < s1.core.tmp_cnt := by
          rcases Nat.eq_zero_or_pos s1.core.tmp_cnt with h0 | hp
          · exfalso; apply (by assumption : BitVec.ofNat 64 s1.core.tmp_cnt ≠ 0#64)
            rw [h0]; rfl
          · exact hp
        have hcl32 : s.core.cur_level < 2 ^ 32 := by have := hw0.cur_level_le; omega
        have hcl_bv32 :
            (BitVec.ofNat 64 s1.core.cur_level).setWidth 32 =
              BitVec.ofNat 32 s.core.cur_level := by
          rw [hstat1.cl]; exact m5_bv64_setWidth32_ofNat hcl32
        refine wp_join_group (ts := [i64, i32, i64]) (fun ys m_u =>
          ∃ (cut_u idx_u : Nat) (su : FullState) (p_u : BitVec 32),
            su.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut_u su.core ∧
            Full.FullAnaMarksCov c su ∧ Full.FullExtScratchPres s su ∧
            su.scratch.work_stk2 = s.scratch.work_stk2 ∧ Full.FullArenaVarsNodup su ∧
            fullArenaClauseRefs su = fullArenaClauseRefs s ∧
            Full.FullDeduceStaticEq s.core su.core ∧ 1 ≤ su.core.tmp_len ∧
            su.core.tmp_len ≤ su.core.cur_vars ∧
            Full.FullLowerInv c su.core su.core.tmp su.core.mrk su.core.tmp_len ∧
            idx_u < su.core.trail_end ∧ (su.core.trl[idx_u]?.getD 0#32).toNat = p_u.toNat ∧
            (su.core.lvl[p_u.toNat / 2]?.getD 0#32).toNat = su.core.cur_level ∧
            ys.2.1 = p_u ^^^ 1#32 ∧
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((p_u ^^^ 1#32).toNat :: Full.fullLowerLits su.core.tmp su.core.tmp_len)) ∧
            (FullMem c su ⋆ R) m_u)
          (fun _ ⟨idx_u_bv, uip_bv, res_u_bv, ⟨⟩⟩ _m_u ⟨cut_u, idx_u, su, p_u, hlu, hwu, hcu,
              heu, hwu2, hndu, hru, hsu, htl_u1, htl_ucv, hlowu, hiu_te, hpu_get, hplu, hys_u,
              hentu, hmu⟩ => by
            dsimp only at hys_u; subst uip_bv
            simp only [Blocks.get]
            exact m5_deduce_uip_exit_body_wp hClear hQ hext0 hdm0 hlm0 hlu hwu hcu heu hwu2
              hndu hru hsu htl_u1 htl_ucv hlowu hiu_te hpu_get hplu hentu hmu) ?_
        intro J_uip hJuip
        rw [hcl_bv32]
        refine wp_loop_inv (ts := [i64, i64])
          (fun ys ml =>
            ∃ (cut_n idx_n res_n : Nat) (sn : FullState),
              ys = (BitVec.ofNat 64 idx_n, BitVec.ofNat 64 res_n, ()) ∧
              idx_n + res_n ≤ sn.core.trail_end ∧
              Full.FullDeduceStateInv c F0 F_cur cut_n idx_n s sn ∧ 0 < sn.core.tmp_cnt ∧
              (res_n = 0 → cut_n = cut ∧
                sn.core.confl_type = s.core.confl_type ∧ sn.core.confl_ref = s.core.confl_ref) ∧
              (FullMem c sn ⋆ R) ml)
          (fun ys _ => ys.1.toNat) ?_ ?_
        · intro J_loop hJloop
          fa_fast_steps
          exact hJloop (BitVec.ofNat 64 s1.core.trail_end, 0#64, ()) m_sd
            ⟨cut, s1.core.trail_end, 0, s1, rfl, by omega, hst1, htc_pos,
             fun _ => ⟨rfl, hct_s1, hcr_s1⟩, hm1⟩
        · intro J_loop ys ml hinv_l hJloop
          simp only [Blocks.get]
          exact m5_deduce_loop_step_wp hArsn hClear hOtfsLarge hOtfsBin hOtfsSub hQ hw0
            hcur_pos hconfl hext0 hdm0 hlm0 (fun idx' uip res' mu h =>
              hJuip (idx', uip, res', ()) mu h) hJloop hinv_l
      · exact hJcl () m_sd ⟨s1, hlen1, hw1, hcov1, hext1, hws2_1, hnd1, hrefs1, hstat1,
          (fun h => by
            have hf : seed_ok = false := by assumption
            exact absurd (h.symm.trans hf) (by decide)), hm1⟩
    · intro J hJ
      exact wp_mono (fun _ _ h => h.elim) (fun _ _ _ _ h => h) _ _
        (m5_deduce_seed_wp hAlit hArsn hinv hcur_pos hconfl (by assumption) fun seed_ok m_sd h =>
          hJ (seed_ok, ()) m_sd h)

end Deduce1UipM5Proof

end LeanQbe.T.Examples.Kissat.FullM5Otfs
