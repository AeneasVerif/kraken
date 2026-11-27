module

public import LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
public import LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCsProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep11ProofAnalyze
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof0
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas2
import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Flat
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4F Step-13 Callee-Parametric WP Lifts — Part 3c0 (`FullFidelityStep13S6aProof3c0`)

Helper shard for `FullFidelityStep13S6aProof3c` adapting `FullFidelityBacktrackCsProof`
Section 1 helpers with `min_clr`-updating `s6aFidAnalyzeRsnSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.FullM6Hdr LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullFidelityBacktrackCs
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open scoped LeanQbe.T.Examples.Kissat.Full.Deduce1UipTactics
open Kraken.Bedrock2.Test

def s6aFidAnalyzeRsnSpec : Spec [i64, i32, i32] [.bool] := fun (h, rsn, skip_var, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    FullWitnessCutInv c F0 F_cur cut s.core ∧ FullAnaMarksCov c s ∧
    s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64 ∧
    (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      rsn.toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' tc' tl' (mclr' : List (BitVec 32)) mcl' arena' sc' m',
      let s' : FullState := { s with
        core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                              min_clr := mclr', min_clr_len := mcl', arena := arena' }
        scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullAnaMarksCov c s' →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
        (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
      (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
      (sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64
        ((List.range s.core.cur_vars).filter fun w =>
          decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
          (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
              (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
              ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem s6aFidAnalyzeRsnSpec_intro {h : BitVec 64} {rsn skip_var : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {s : FullState} {R : Mem 64 → Prop}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hcov : FullAnaMarksCov c s) (htl : s.core.tmp_len ≤ s.core.cur_vars)
    (htc : s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64)
    (href : rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      rsn.toNat ∈ fullArenaClauseRefs s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) mrk' tmp' tc' tl' (mclr' : List (BitVec 32)) mcl' arena' sc' m',
      let s' : FullState := { s with
        core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                              min_clr := mclr', min_clr_len := mcl', arena := arena' }
        scratch := sc' }
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullAnaMarksCov c s' →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
        (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
      (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
      (sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64
        ((List.range s.core.cur_vars).filter fun w =>
          decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
          (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
              (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
              ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    s6aFidAnalyzeRsnSpec (h, rsn, skip_var, ()) m Q X :=
  ⟨c, F0, F_cur, cut, s, R, hh, hlen, hw, hcov, htl, htc, href, hm, hQ⟩

theorem s6aFidAnalyzeRsnSpec_elim {a m Q X} (h : s6aFidAnalyzeRsnSpec a m Q X) :
    let (h_ptr, rsn, skip_var, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
      (s : FullState) (R : Mem 64 → Prop),
      h_ptr = c.hdr ∧ s.LengthsOk c ∧
      FullWitnessCutInv c F0 F_cur cut s.core ∧ FullAnaMarksCov c s ∧
      s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64 ∧
      (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
        rsn.toNat ∈ fullArenaClauseRefs s) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) mrk' tmp' tc' tl' (mclr' : List (BitVec 32)) mcl' arena' sc' m',
        let s' : FullState := { s with
          core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr := mclr', min_clr_len := mcl', arena := arena' }
          scratch := sc' }
        s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullAnaMarksCov c s' →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
          fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
          fullArenaClauseLits s' r = fullArenaClauseLits s r) →
        (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
          mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
        (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
        (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
          ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
            0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
            (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
        (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
          l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
          s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
        (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
          (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
        (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
          decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
          decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
        (sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64
          ((List.range s.core.cur_vars).filter fun w =>
            decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
        (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
          sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
            decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
          ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
            (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
              (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨h_ptr, rsn, skip_var, ⟨⟩⟩; exact h

theorem s6a_fid_witness_with_min_clr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState}
    (hw : FullWitnessCutInv c F0 F_cur cut k) (mclr' : List (BitVec 32)) :
    FullWitnessCutInv c F0 F_cur cut { k with min_clr := mclr' } :=
  ⟨{ hw.1 with
     arena := { len_ok := hw.arena.len_ok, refs_wf := hw.arena.refs_wf,
                shrk_term := hw.arena.shrk_term, lits_lt := hw.arena.lits_lt,
                entails := hw.arena.entails },
     watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   hw.cut_le, hw.reason_inv_cut, hw.reason_lit_mem_cut⟩

theorem s6a_fid_state_with_min_clr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut idx : Nat} {s s0 s1 : FullState}
    (hs0 : FullDeduceStateInv c F0 F_cur cut idx s s0)
    (hlen1 : s1.LengthsOk c) (hw1 : FullWitnessCutInv c F0 F_cur cut s1.core)
    (hcov1 : FullAnaMarksCov c s1)
    (hcore : s1.core = { s0.core with min_clr := s1.core.min_clr })
    (hscr : s1.scratch = s0.scratch) : FullDeduceStateInv c F0 F_cur cut idx s s1 := by
  have heq_f : s1.core.cur_vars = s0.core.cur_vars ∧ s1.core.cur_level = s0.core.cur_level ∧
      s1.core.trail_end = s0.core.trail_end ∧ s1.core.trl = s0.core.trl ∧
      s1.core.lvl = s0.core.lvl ∧ s1.core.rsns = s0.core.rsns ∧
      s1.core.vals = s0.core.vals ∧ s1.core.fuel = s0.core.fuel ∧
      s1.core.dense_mode = s0.core.dense_mode ∧ s1.core.lit_mark = s0.core.lit_mark ∧
      s1.core.tmp_cnt = s0.core.tmp_cnt ∧ s1.core.tmp_len = s0.core.tmp_len ∧
      s1.core.mrk = s0.core.mrk ∧ s1.core.tmp = s0.core.tmp ∧
      s1.core.arena = s0.core.arena ∧ s1.core.arena_len = s0.core.arena_len := by
    rw [hcore]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hcv, hcl, hte, htrl, hlvl, hrsns, hvals, hfu, hdm, hlm, htc, htl, hmrk, htmp, har, hal⟩ :=
    heq_f
  refine ⟨hlen1, hw1, hcov1, ⟨hscr ▸ hs0.ext.1, hscr ▸ hs0.ext.2⟩,
    by rw [hscr]; exact hs0.ws2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hnd := hs0.nd
    unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore
      fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore fullArenaClauseLits
      fullArenaClauseLitsCore fullArenaClauseSizeCore at hnd ⊢
    rw [har, hal]; exact hnd
  · unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]; exact hs0.hrefs
  · exact hs0.stat.repack hcv hcl hte htrl hlvl hrsns hvals hfu hdm hlm
  · rw [htl]; exact hs0.tl_ge
  · rw [htl, hcv]; exact hs0.tl_cv
  · rw [htc]; unfold fullCurTrailIdxs; rw [htrl, hmrk, hlvl, hcl]; exact hs0.tc_eq
  · unfold FullLowerInv; rw [hcv, hvals, hlvl, hcl, htmp, hmrk, htl]; exact hs0.low
  · unfold FullMarksCov; rw [hcv, hte, htrl, hlvl, hcl, htmp, hmrk, htl]; exact hs0.mcov
  · unfold FullCurMarksBelow; rw [hmrk, htrl, hlvl, hcl]; exact hs0.cmcut
  · unfold fullActiveResolvent fullLowerLits fullCurLits fullCurTrailIdxs
    rw [htmp, htl, htrl, hlvl, hcl, hmrk]; exact hs0.ent
  · rw [hscr, htl, htc]; exact hs0.res_eq


theorem bv32_setWidth64_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem fid_xor1_div2 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := by
  simpa [litVar, litNeg] using litVar_litNeg l

theorem fid_litMarksClear_of_mrk {c : FullCfg} {s s' : FullState}
    (h0 : Full.FullLitMarksClear c s) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hmrk : ∀ v < c.max_vars, s'.core.mrk[v]?.getD 0#8 = 0#8) :
    Full.FullLitMarksClear c s' :=
  ⟨hmrk, fun l hl => by rw [hlm]; exact h0.2 l hl⟩

theorem fid_otfsInvW_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut' : Nat} {s s' : FullState}
    (hlen : s'.LengthsOk c) (hw : Full.FullWitnessCutInv c F0 F_cur cut' s'.core)
    (hmrk : Full.FullLitMarksClear c s') (hnd : Full.FullArenaVarsNodup s')
    (hext0 : Full.FullExtScratchOk c s) (hext : Full.FullExtScratchPres s s')
    (hrefs : Full.fullArenaClauseRefs s' = Full.fullArenaClauseRefs s)
    (hdm : s'.core.dense_mode = 0#64) : Full.FullOtfsInvW c F0 F_cur s' :=
  ⟨hlen, hw.toFullOtfsWitnessInv, hmrk, hnd,
   ⟨fun i hi => by
      change (let cr := s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32; _); rw [hext.1]
      rcases hext0.1 i hi with h | h
      · exact Or.inl h
      · exact Or.inr (hrefs ▸ h),
    by rw [hext.2]; exact hext0.2⟩,
   hdm⟩

theorem fid_lowerLits_tmp_take {tmp : List (BitVec 32)} {tl : Nat} {uip : BitVec 32}
    (h1 : 1 ≤ tl) (_htl : tl ≤ tmp.length) (h0 : tmp[0]? = some uip) :
    (tmp.take tl).map BitVec.toNat = uip.toNat :: Full.fullLowerLits tmp tl := by
  cases tmp with
  | nil => simp at h0
  | cons x xs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0
    cases tl with
    | zero => omega
    | succ n => simp [Full.fullLowerLits]

theorem fid_anaMarksCov_of_same {c : FullCfg} {s1 s2 : FullState}
    (hcov : Full.FullAnaMarksCov c s1) (hcv : s2.core.cur_vars = s1.core.cur_vars)
    (hmcl : s2.core.min_clr_len = s1.core.min_clr_len) (hmrk : s2.core.mrk = s1.core.mrk)
    (hws1 : s2.scratch.work_stk1 = s1.scratch.work_stk1) : Full.FullAnaMarksCov c s2 :=
  ⟨by rw [hcv, hmcl]; exact hcov.1, by rw [hmcl, hws1]; exact hcov.2.1,
   fun k hk => by rw [hws1, hcv, hmrk]; exact hcov.2.2.1 k (hmcl ▸ hk),
   fun v hv hnz => by
     rw [hmrk] at hnz
     obtain ⟨k, hk, hget⟩ := hcov.2.2.2 v hv hnz
     exact ⟨k, by rw [hmcl]; exact hk, by rw [hws1]; exact hget⟩⟩

theorem fid_cut_with_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut' : Nat} {k : FullCoreState} (hw : Full.FullWitnessCutInv c F0 F_cur cut' k)
    (ct' cr' : BitVec 64) :
    Full.FullWitnessCutInv c F0 F_cur cut' { k with confl_type := ct', confl_ref := cr' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }

theorem fid_bv64_setWidth32_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), bv32_ofNat_toNat hn,
    Nat.mod_eq_of_lt hn]

private theorem fid_deduce_clear_ana_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {K : Tup Val [] → Expr Val Cont [i64]}
    {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (hlen1 : s1.LengthsOk c) (hw1 : Full.FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : Full.FullAnaMarksCov c s1) (hext0 : Full.FullExtScratchOk c s)
    (hext1 : Full.FullExtScratchPres s s1) (hnd1 : Full.FullArenaVarsNodup s1)
    (hrefs1 : Full.fullArenaClauseRefs s1 = Full.fullArenaClauseRefs s)
    (hlm1 : s1.core.lit_mark = s.core.lit_mark) (hdm1 : s1.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hK : ∀ mrk' m_clr,
      let s_clr : FullState := { s1 with core := { s1.core with mrk := mrk', min_clr_len := 0 } }
      s_clr.LengthsOk c →
      Full.FullOtfsInvW c F0 F_cur s_clr →
      Full.FullWitnessCutInv c F0 F_cur cut' s_clr.core →
      (FullMem c s_clr ⋆ R) m_clr →
      wp Γ Q X (K ()) m_clr) :
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
    fid_litMarksClear_of_mrk hm0_lm hlm1 (hm'_cov hcov1)
  have hotfs_c := fid_otfsInvW_of hlen_c hw_c hlm_c hnd1 hext0 hext1 hrefs1 hdm1
  exact hK mrk' m_c hlen_c hotfs_c hw_c hm_c

private theorem fid_deduce_clear_unsat_ret_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {K : Tup Val [] → Expr Val Cont [i64]}
    {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (hlen1 : s1.LengthsOk c) (hw1 : Full.FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : Full.FullAnaMarksCov c s1) (hext0 : Full.FullExtScratchOk c s)
    (hext1 : Full.FullExtScratchPres s s1) (hnd1 : Full.FullArenaVarsNodup s1)
    (hrefs1 : Full.fullArenaClauseRefs s1 = Full.fullArenaClauseRefs s)
    (hstat1 : Full.FullDeduceStaticEq s.core s1.core) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hK : ∀ mrk' m_clr,
      let s_clr : FullState := { s1 with core := { s1.core with mrk := mrk', min_clr_len := 0 } }
      s_clr.LengthsOk c →
      Full.FullOtfsInvW c F0 F_cur s_clr →
      s_clr.core.cur_vars = s.core.cur_vars →
      s_clr.core.fuel = s.core.fuel →
      s_clr.core.cur_level = s.core.cur_level →
      s_clr.core.dense_mode = 0#64 →
      (FullMem c s_clr ⋆ R) m_clr →
      wp Γ Q X (K ()) m_clr) :
    wp Γ Q X (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) K)
      m1 := by
  have hdm1 : s1.core.dense_mode = 0#64 := hstat1.dm.trans hdm0
  refine fid_deduce_clear_ana_wp hClear hlen1 hw1 hcov1 hext0 hext1 hnd1 hrefs1 hstat1.lm hdm1
    hm0_lm hm1 fun mrk' m_clr hlen_c hotfs_c _ hm_c =>
    hK mrk' m_clr hlen_c hotfs_c hstat1.cv hstat1.fuel hstat1.cl hdm1 hm_c

private theorem fid_deduce_res_clear_ret_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (retv : BitVec 64)
    (hlen1 : s1.LengthsOk c) (hw1 : Full.FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : Full.FullAnaMarksCov c s1) (hext0 : Full.FullExtScratchOk c s)
    (hext1 : Full.FullExtScratchPres s s1) (hws2 : s1.scratch.work_stk2 = s.scratch.work_stk2)
    (hnd1 : Full.FullArenaVarsNodup s1)
    (hrefs1 : Full.fullArenaClauseRefs s1 = Full.fullArenaClauseRefs s)
    (hstat1 : Full.FullDeduceStaticEq s.core s1.core) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hK : ∀ mrk_c m_c,
      let s_c : FullState :=
        { s1 with
          core := { s1.core with mrk := mrk_c, min_clr_len := 0 },
          scratch := { s1.scratch with res_sz := BitVec.ofNat 64 s1.core.min_clr_len } }
      s_c.LengthsOk c → Full.FullOtfsInvW c F0 F_cur s_c →
      Full.FullWitnessCutInv c F0 F_cur cut' s_c.core → Full.FullCutInvW c F0 F_cur cut' s_c →
      s_c.core.cur_vars = s.core.cur_vars → s_c.core.cur_level = s.core.cur_level →
      s_c.core.fuel = s.core.fuel → s_c.scratch.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s_c ⋆ R) m_c → Q (retv, ()) m_c) :
    wp Γ Q X (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272#64, ())) fun p1 =>
      .load i64 (Arg.var p1.fst) fun ld =>
        .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144#64, ())) fun p2 =>
          .store (Arg.var ld) (Arg.var p2.fst)
            (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
              (fun _ => .ret (Arg.imm retv, ())))) m1 := by
  c0_let_simp
  refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm1) ?_
  c0_let_simp
  refine wp_store_sep (FullArenaTactics.store_full_res_sz
    (BitVec.ofNat 64 s1.core.min_clr_len) hm1) (fun m_r hm_r => ?_)
  let s_r : FullState :=
    { s1 with scratch := { s1.scratch with res_sz := BitVec.ofNat 64 s1.core.min_clr_len } }
  have hlen_r : s_r.LengthsOk c := ⟨hlen1.core_ok, { hlen1.scratch_ok with }⟩
  have hdm_r : s_r.core.dense_mode = 0#64 := hstat1.dm.trans hdm0
  refine fid_deduce_clear_ana_wp hClear hlen_r hw1 hcov1 hext0 hext1 hnd1 hrefs1 hstat1.lm
    hdm_r hm0_lm hm_r fun mrk_c m_c hlen_c hotfs_c hw_c hm_c => ?_
  fa_fast_steps
  let s_c : FullState :=
    { s1 with
      core := { s1.core with mrk := mrk_c, min_clr_len := 0 },
      scratch := { s1.scratch with res_sz := BitVec.ofNat 64 s1.core.min_clr_len } }
  have hcutw : Full.FullCutInvW c F0 F_cur cut' s_c :=
    ⟨hlen_c, hw_c, hotfs_c.2.2.1, hotfs_c.2.2.2.1, hotfs_c.2.2.2.2.1, hotfs_c.2.2.2.2.2⟩
  exact hK mrk_c m_c hlen_c hotfs_c hw_c hcutw hstat1.cv hstat1.cl hstat1.fuel hws2 hm_c

theorem fid_deduce_clear_ret0_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
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
    (hlen1 : s1.LengthsOk c) (hw1 : Full.FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : Full.FullAnaMarksCov c s1) (hext0 : Full.FullExtScratchOk c s)
    (hext1 : Full.FullExtScratchPres s s1) (hws2 : s1.scratch.work_stk2 = s.scratch.work_stk2)
    (hnd1 : Full.FullArenaVarsNodup s1)
    (hrefs1 : Full.fullArenaClauseRefs s1 = Full.fullArenaClauseRefs s)
    (hstat1 : Full.FullDeduceStaticEq s.core s1.core) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s) (hm1 : (FullMem c s1 ⋆ R) m1) :
    wp Γ Q X (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
      (fun _ => .ret (Arg.imm 0#64, ()))) m1 := by
  refine fid_deduce_clear_ana_wp hClear hlen1 hw1 hcov1 hext0 hext1 hnd1 hrefs1 hstat1.lm
    (hstat1.dm.trans hdm0) hm0_lm hm1 fun mrk' m_c hlen_c hotfs_c _ hm_c => ?_
  fa_fast_steps
  exact hQ 0#64 _ m_c hlen_c (Or.inl rfl) hstat1.cv hstat1.fuel hws2
    (fun h => by cases h) (fun _ => hotfs_c) (fun h => by cases h) (fun h => by cases h) hm_c

theorem fid_deduce_clear_unsat_goal_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut' : Nat}
    {s s1 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    {seed_ok : Bool}
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
    (hlen1 : s1.LengthsOk c) (hw1 : Full.FullWitnessCutInv c F0 F_cur cut' s1.core)
    (hcov1 : Full.FullAnaMarksCov c s1) (hext0 : Full.FullExtScratchOk c s)
    (hext1 : Full.FullExtScratchPres s s1) (hws2 : s1.scratch.work_stk2 = s.scratch.work_stk2)
    (hnd1 : Full.FullArenaVarsNodup s1)
    (hrefs1 : Full.fullArenaClauseRefs s1 = Full.fullArenaClauseRefs s)
    (hstat1 : Full.FullDeduceStaticEq s.core s1.core) (hdm0 : s.core.dense_mode = 0#64)
    (hm0_lm : Full.FullLitMarksClear c s)
    (hunsat : seed_ok = true → s1.core.tmp_len = 1 → F0.Unsat)
    (hm1 : (FullMem c s1 ⋆ R) m1) :
    wp Γ Q X (.call (rs := [i64]) (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ())
      fun _ => .jnz (Arg.var seed_ok)
        (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 192, ())) fun p =>
          .load i64 (Arg.var p.fst) fun ld =>
            .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var ld, Arg.imm 1#64, ())) fun p =>
              .jnz (Arg.var p.fst) (.ret (Arg.imm 20#64, ())) (.ret (Arg.imm 0#64, ())))
        (.ret (Arg.imm 0#64, ()))) m1 := by
  refine fid_deduce_clear_unsat_ret_wp hClear hlen1 hw1 hcov1 hext0 hext1 hnd1 hrefs1 hstat1 hdm0
    hm0_lm hm1 fun mrk' m_c hlen_c hotfs_c hcv_c hfuel_c hcl_c hdm_c hm_c => ?_
  have hmaxv := c.hmaxv; have hcv_le := hlen1.core_ok.cur_vars_le; unfold dimacsBound at hmaxv
  have htl_lt : s1.core.tmp_len < 2 ^ 64 := by have := hlen1.core_ok.tmp_len_le; omega
  refine wp_jnz_of (fun hso => ?_) (fun _ => ?_)
  · simp only [Arg.val_var] at hso
    fa_fast_steps
    · have htl1 : s1.core.tmp_len = 1 := by
        have heq : BitVec.ofNat 64 s1.core.tmp_len = 1#64 := by assumption
        have := congrArg BitVec.toNat heq; rw [bv64_ofNat_toNat htl_lt] at this
        simpa using this
      exact hQ 20#64 _ m_c hlen_c (Or.inr (Or.inr (Or.inr rfl))) hcv_c hfuel_c hws2
        (fun _ => ⟨hunsat hso htl1, hotfs_c, le_of_eq hcl_c, hdm_c.trans hdm0.symm⟩)
        (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm_c
    · exact hQ 0#64 _ m_c hlen_c (Or.inl rfl) hcv_c hfuel_c hws2
        (fun h => by cases h) (fun _ => hotfs_c) (fun h => by cases h) (fun h => by cases h) hm_c
  · fa_fast_steps
    exact hQ 0#64 _ m_c hlen_c (Or.inl rfl) hcv_c hfuel_c hws2
      (fun h => by cases h) (fun _ => hotfs_c) (fun h => by cases h) (fun h => by cases h) hm_c

theorem fid_deduce_uip_exit_body_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
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
    (hws2_b : sb.scratch.work_stk2 = s.scratch.work_stk2)
    (hnd_b : Full.FullArenaVarsNodup sb)
    (hrefs_b : Full.fullArenaClauseRefs sb = Full.fullArenaClauseRefs s)
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
                (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272#64, ())) fun p23 =>
                  .load i64 (Arg.var p23.fst) fun ld =>
                    .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144#64, ())) fun p24 =>
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
  have hs0_len : s0.LengthsOk c :=
    ⟨{ hlen_b.core_ok with tmp_len_arr := by dsimp [s0, tmp0]; simp [htb_len] }, hlen_b.scratch_ok⟩
  have hw0 : Full.FullWitnessCutInv c F0 F_cur cut_b s0.core :=
    Full.deduce_same_core_cut hw_b sb.core.mrk tmp0 sb.core.tmp_cnt sb.core.tmp_len
      sb.core.min_clr_len
  have hstat0 : Full.FullDeduceStaticEq s.core s0.core :=
    ⟨hstat_b.1, hstat_b.2, hstat_b.3, hstat_b.4, hstat_b.5, hstat_b.6, hstat_b.7, hstat_b.8,
     hstat_b.9, hstat_b.10⟩
  have huip_fals : sb.core.vals[uip.toNat]?.getD 0#8 = 0xFF#8 :=
    (hw_b.vals_false_iff uip.toNat huip_lt).mpr ⟨idx_u, hiu_te, by
      rw [hp_get, huip_nat]; exact (litNeg_litNeg _).symm⟩
  have huip_cl : (sb.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = sb.core.cur_level := by
    rwa [huip_nat, fid_xor1_div2]
  c0_let_simp
  refine wp_jnz_of (fun hc => ?_) (fun _ => ?_)
  · simp only [Arg.val_var] at hc; c0_cond hc; exact absurd hc huip_ne
  · c0_let_simp
    refine wp_store_sep (Full.Deduce1UipTactics.d1_store_full_tmp0_mul uip h0_tb hmb)
      (fun m_st hm_st => ?_)
    refine fid_deduce_res_clear_ret_wp hClear 1#64 hs0_len hw0 hcov_b hext0 hext_b hws2_b
      hnd_b hrefs_b hstat0 hdm0 hm0_lm hm_st
      fun mrk_c m_c hlen_c hotfs_c _ _ hcv_c hcl_c hfuel_c hws2_c hm_c => ?_
    let s_c : FullState :=
      { s0 with
        core := { s0.core with mrk := mrk_c, min_clr_len := 0 },
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
    · rw [fid_lowerLits_tmp_take htl1 (by omega) htmp0_0, hlowLits0]
      exact hent_b

theorem fid_deduce_seed_wp {Γ : Env}
    (hAlit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, s6aFidAnalyzeRsnSpec a m Q X →
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
        Full.fullArenaClauseRefs s1 = Full.fullArenaClauseRefs s ∧
        Full.FullDeduceStaticEq s.core s1.core ∧ 1 ≤ s1.core.tmp_len ∧
        s1.core.tmp_len ≤ s1.core.cur_vars ∧ s1.core.confl_type = s.core.confl_type ∧
        s1.core.confl_ref = s.core.confl_ref ∧
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
  obtain ⟨hlen, hw, hlm, hnd, hext0, hdm⟩ := hinv
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
  have hs0_refs : Full.fullArenaClauseRefs s0 = Full.fullArenaClauseRefs s := rfl
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
      have hrefsa : Full.fullArenaClauseRefs sa = Full.fullArenaClauseRefs s := rfl
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
        have htca_le1 : tc_a ≤ 1 := by split at htca_eq <;> omega
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
          _ _ _ ⟨c, sa, R, rfl, hlen_a, hcur32, htla_cv, by dsimp [sa]; omega, hcov_a, hm_a, ?_⟩)
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
        have hrefsb : Full.fullArenaClauseRefs sb = Full.fullArenaClauseRefs s := rfl
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
          _ _ _ (s6aFidAnalyzeRsnSpec_intro rfl hs0_len hs0_hw hs0_cov
            (by dsimp [s0]; omega) (by dsimp [s0]; omega)
            (fun _ _ => by rw [hcr_tr]; exact hs0_refs ▸ href) hm0 ?_))
        intro ok1 mrk1 tmp1 tc1 tl1 mclr1 mcl1 arena1 sc1 m1 _ hlen1 hw1 hcov1 hext1 hws2_1
          htl1_ge htl1_cv htc1_ge hrefs1 hprops1 hmp1 htp1 hnm1 hnt1 hnd1_t hcnt1 hres1 hok1 hm1
        dsimp only [s0] at hlen1 hw1 hcov1 hext1 hws2_1 htl1_ge htl1_cv htc1_ge hrefs1 hprops1 hm1
        let s1_sem : FullState :=
          { s0 with core := { s0.core with mrk := mrk1, tmp := tmp1, tmp_cnt := tc1,
                                           tmp_len := tl1, min_clr_len := mcl1, arena := arena1 },
                    scratch := sc1 }
        let s1 : FullState := { s1_sem with core := { s1_sem.core with min_clr := mclr1 } }
        have hnd1 : Full.FullArenaVarsNodup s1 := fun r hr hngr => by
          change r ∈ Full.fullArenaClauseRefs s1 at hr; rw [hrefs1] at hr
          have hll := hprops1 r hr
          change ((Full.fullArenaClauseLits s1 r).map (· / 2)).Nodup
          rw [hll.2.2]; refine hnd r hr ?_
          unfold Full.fullArenaClauseGarb Full.fullArenaClauseGarbCore Full.fullArenaHdrCore
            at hll hngr ⊢
          rw [← hll.2.1]; exact hngr
        have hs1_st : Full.FullDeduceStaticEq s.core s1.core :=
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        cases ok1 with
        | false =>
          fa_fast_steps
          exact hJ1 (false, ()) m1 (hJsd false m1 ⟨s1, hlen1, hw1, hcov1,
            Full.fullExtScratchPres_trans hs0_ext hext1, hws2_1, hnd1, hrefs1.trans hs0_refs,
            hs1_st, by dsimp [s1, s1_sem]; omega, by dsimp [s1, s1_sem]; exact htl1_cv, rfl, rfl,
            (fun hc => by cases hc), hm1⟩)
        | true =>
          fa_fast_steps
          have hlen1_s : s1_sem.LengthsOk c :=
            ⟨{ hlen1.core_ok with min_clr_len_arr := hs0_len.core_ok.min_clr_len_arr },
             hlen1.scratch_ok⟩
          have hw1_s : FullWitnessCutInv c F0 F_cur cut s1_sem.core :=
            s6a_fid_witness_with_min_clr hw1 s0.core.min_clr
          have hcov1_s : FullAnaMarksCov c s1_sem := fid_anaMarksCov_of_same hcov1 rfl rfl rfl rfl
          have hnd1_s : Full.FullArenaVarsNodup s1_sem := hnd1
          have hsem := Full.deduce_seed_rsn_sem hs0_len hs0_hw hs0_st rfl rfl rfl
            (fun v hv => hlm.1 v hv) rfl rfl hct2 hconfl hw1_s hlen1_s hcov1_s hext1 hws2_1
            htl1_ge htl1_cv htc1_ge hrefs1 hnd1_s
            (fun w hw hnz => hmp1 w (Nat.lt_of_lt_of_le hw hcv_le) hnz)
            htp1
            (fun w hw h0 hnz =>
              let ⟨l, hl, h1, _, h2, h3, h4⟩ := hnm1 w (Nat.lt_of_lt_of_le hw hcv_le) h0 hnz
              ⟨l, hl, h1, h2, h3, h4⟩)
            hnt1 hnd1_t hcnt1 hres1 ⟨(hok1 rfl).1, (hok1 rfl).2.2⟩ hs0_ext rfl hs0_refs
          have hsem1 := s6a_fid_state_with_min_clr hsem hlen1 hw1 hcov1 rfl rfl
          exact hJ1 (true, ()) m1 (hJsd true m1 ⟨s1, hlen1, hw1, hcov1, hsem1.ext, hsem1.ws2,
            hnd1, hrefs1.trans hs0_refs, hs1_st, hsem1.tl_ge, hsem1.tl_cv, rfl, rfl,
            fun _ => hsem1, hm1⟩)
      · have h_not : ¬(s.core.confl_ref.toNat + 3) % 2 ^ 64 ≤ s.core.arena_len % 2 ^ 64 := by
          assumption
        exact absurd (by
          rw [Nat.mod_eq_of_lt (by omega : s.core.confl_ref.toNat + 3 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)]
          exact hwf) h_not

theorem fid_deduce_otfs_ret2_subsume_wp {Γ : Env}
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
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
    (hws2_ot : s_ot.scratch.work_stk2 = s.scratch.work_stk2)
    (hnd_ot : Full.FullArenaVarsNodup s_ot)
    (hrefs_ot : Full.fullArenaClauseRefs s_ot = Full.fullArenaClauseRefs s)
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
      (to_bin = false → new_confl_arg.val.toNat ∈ Full.fullArenaClauseRefs s_ot ∧
        new_confl_arg.val.toNat = rsn.toNat ∧ s_ot.core.confl_ref.toNat = rsn.toNat))
    (hm_ot : (FullMem c s_ot ⋆ R) m_ot) :
    wp Γ Q X (.group (sig := [[]]) (fun _Js => .cons (fun _ =>
      .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 272#64, ())) fun p1 =>
        .load i64 (Arg.var p1.fst) fun ld =>
          .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1144#64, ())) fun p2 =>
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
      Full.fullArenaClauseRefs s_j = Full.fullArenaClauseRefs s ∧
      Full.FullDeduceStaticEq s.core s_j.core ∧ Full.FullConflictOkCut F_cur idx' s_j ∧
      (FullMem c s_j ⋆ R) ml) ?_ ?_
  · rintro _ ⟨⟩ ml ⟨s_j, hlen_j, hw_j, hcov_j, hext_j, hws2_j, hnd_j, hrefs_j, hstat_j,
      hconfl_j, hml⟩
    fa_fast_steps_nogrp
    refine fid_deduce_res_clear_ret_wp hClear 2#64 hlen_j hw_j hcov_j hext0 hext_j hws2_j
      hnd_j hrefs_j hstat_j hdm0 hm0_lm hml fun mrk_c m_c hlen_c _ hw_c hcut_c hcv_c
        hcl_c hfuel_c hws2_c hm_c => ?_
    let s_c : FullState :=
      { s_j with
        core := { s_j.core with mrk := mrk_c, min_clr_len := 0 },
        scratch := { s_j.scratch with res_sz := BitVec.ofNat 64 s_j.core.min_clr_len } }
    have hte_eq : s_c.core.trail_end = s_j.core.trail_end := rfl
    have hte_j : s_j.core.trail_end = s_ot.core.trail_end := by rw [hstat_j.te, hstat_ot.te]
    have hconfl_c := Full.deduce_conflOk_same_of_clear hconfl_j rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl
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
        exact hJsub () m_s ⟨s_s, hlen_s, hw_s, hcov_ot, hext_ot, hws2_ot, hnd_s,
          hrefs_s.trans hrefs_ot, hstat_s, hconfl_s, hm_s⟩
    · exact hJsub () m_ot ⟨s_ot, hlen_ot, hw_ot, hcov_ot, hext_ot, hws2_ot, hnd_ot, hrefs_ot,
        hstat_ot, hconfl_ot, hm_ot⟩
    · exact hJsub () m_ot ⟨s_ot, hlen_ot, hw_ot, hcov_ot, hext_ot, hws2_ot, hnd_ot, hrefs_ot,
        hstat_ot, hconfl_ot, hm_ot⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
