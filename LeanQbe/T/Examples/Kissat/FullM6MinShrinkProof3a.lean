module

public import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof2c
import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 Minimization/Shrink Proof Shard 3a (`full_deduce_1uip_m6`)

Proves `full_deduce_1uip_m6_wp` establishing canonical `Full.fullDeduce1uipSpec` for
`full_deduce_1uip_m6_body` (`FullM6MinShrink.lean`), reusing resolvent theory and semantic step
lemmas from `FullDeduce1UipLemmas1` and certifying `h->res_sz = h->min_clr_len; full_clear_ana(h);`
on OTFS/UIP exits without `full_bump_analyzed`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6MinShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open scoped LeanQbe.T.Examples.Kissat.Full.Deduce1UipTactics
open Kraken.Bedrock2.Test

/-! ## 1. Local clear / OTFS / UIP exit helpers -/

section Helpers

private theorem m6_xor1_div2 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := by
  simpa [litVar, litNeg] using litVar_litNeg l

private theorem m6_litMarksClear_of_mrk {c : FullCfg} {s s' : FullState}
    (h0 : Full.FullLitMarksClear c s) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hmrk : ∀ v < c.max_vars, s'.core.mrk[v]?.getD 0#8 = 0#8) :
    Full.FullLitMarksClear c s' :=
  ⟨hmrk, fun l hl => by rw [hlm]; exact h0.2 l hl⟩

private theorem m6_otfsInvW_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

private theorem m6_lowerLits_tmp_take {tmp : List (BitVec 32)} {tl : Nat} {uip : BitVec 32}
    (h1 : 1 ≤ tl) (_htl : tl ≤ tmp.length) (h0 : tmp[0]? = some uip) :
    (tmp.take tl).map BitVec.toNat = uip.toNat :: Full.fullLowerLits tmp tl := by
  cases tmp with
  | nil => simp at h0
  | cons x xs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0
    cases tl with
    | zero => omega
    | succ n => simp [Full.fullLowerLits]

private theorem m6_anaMarksCov_of_same {c : FullCfg} {s1 s2 : FullState}
    (hcov : Full.FullAnaMarksCov c s1) (hcv : s2.core.cur_vars = s1.core.cur_vars)
    (hmcl : s2.core.min_clr_len = s1.core.min_clr_len) (hmrk : s2.core.mrk = s1.core.mrk)
    (hws1 : s2.scratch.work_stk1 = s1.scratch.work_stk1) : Full.FullAnaMarksCov c s2 :=
  ⟨by rw [hcv, hmcl]; exact hcov.1, by rw [hmcl, hws1]; exact hcov.2.1,
   fun k hk => by rw [hws1, hcv, hmrk]; exact hcov.2.2.1 k (hmcl ▸ hk),
   fun v hv hnz => by
     rw [hmrk] at hnz
     obtain ⟨k, hk, hget⟩ := hcov.2.2.2 v hv hnz
     exact ⟨k, by rw [hmcl]; exact hk, by rw [hws1]; exact hget⟩⟩

private theorem m6_cut_with_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut' : Nat} {k : FullCoreState} (hw : Full.FullWitnessCutInv c F0 F_cur cut' k)
    (ct' cr' : BitVec 64) :
    Full.FullWitnessCutInv c F0 F_cur cut' { k with confl_type := ct', confl_ref := cr' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }

private theorem m6_bv64_setWidth32_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), bv32_ofNat_toNat hn,
    Nat.mod_eq_of_lt hn]

private theorem m6_deduce_clear_ana_wp {Γ : Env}
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
    m6_litMarksClear_of_mrk hm0_lm hlm1 (hm'_cov hcov1)
  have hotfs_c := m6_otfsInvW_of hlen_c hw_c hlm_c hnd1 hext0 hext1 hrefs1 hdm1
  exact hK mrk' m_c hlen_c hotfs_c hw_c hm_c

private theorem m6_deduce_clear_unsat_ret_wp {Γ : Env}
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
  refine m6_deduce_clear_ana_wp hClear hlen1 hw1 hcov1 hext0 hext1 hnd1 hrefs1 hstat1.lm hdm1
    hm0_lm hm1 fun mrk' m_clr hlen_c hotfs_c _ hm_c =>
    hK mrk' m_clr hlen_c hotfs_c hstat1.cv hstat1.fuel hstat1.cl hdm1 hm_c

private theorem m6_deduce_res_clear_ret_wp {Γ : Env}
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
  have hext_r : Full.FullExtScratchPres s s_r := hext1
  have hcov_r : Full.FullAnaMarksCov c s_r := hcov1
  have hdm_r : s_r.core.dense_mode = 0#64 := hstat1.dm.trans hdm0
  refine m6_deduce_clear_ana_wp hClear hlen_r hw1 hcov_r hext0 hext_r hnd1 hrefs1 hstat1.lm
    hdm_r hm0_lm hm_r fun mrk_c m_c hlen_c hotfs_c hw_c hm_c => ?_
  fa_fast_steps
  let s_c : FullState :=
    { s1 with
      core := { s1.core with mrk := mrk_c, min_clr_len := 0 },
      scratch := { s1.scratch with res_sz := BitVec.ofNat 64 s1.core.min_clr_len } }
  have hcutw : Full.FullCutInvW c F0 F_cur cut' s_c :=
    ⟨hlen_c, hw_c, hotfs_c.2.2.1, hotfs_c.2.2.2.1, hotfs_c.2.2.2.2.1, hotfs_c.2.2.2.2.2⟩
  exact hK mrk_c m_c hlen_c hotfs_c hw_c hcutw hstat1.cv hstat1.cl hstat1.fuel hws2 hm_c

private theorem m6_deduce_clear_ret0_wp {Γ : Env}
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
  refine m6_deduce_clear_ana_wp hClear hlen1 hw1 hcov1 hext0 hext1 hnd1 hrefs1 hstat1.lm
    (hstat1.dm.trans hdm0) hm0_lm hm1 fun mrk' m_c hlen_c hotfs_c _ hm_c => ?_
  fa_fast_steps
  exact hQ 0#64 _ m_c hlen_c (Or.inl rfl) hstat1.cv hstat1.fuel hws2
    (fun h => by cases h) (fun _ => hotfs_c) (fun h => by cases h) (fun h => by cases h) hm_c

private theorem m6_deduce_clear_unsat_goal_wp {Γ : Env}
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
  refine m6_deduce_clear_unsat_ret_wp hClear hlen1 hw1 hcov1 hext0 hext1 hnd1 hrefs1 hstat1 hdm0
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

private theorem m6_deduce_uip_exit_body_wp {Γ : Env}
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
  have hcov0 : Full.FullAnaMarksCov c s0 := hcov_b
  have hnd0 : Full.FullArenaVarsNodup s0 := hnd_b
  have hrefs0 : Full.fullArenaClauseRefs s0 = Full.fullArenaClauseRefs s := hrefs_b
  have hstat0 : Full.FullDeduceStaticEq s.core s0.core :=
    ⟨hstat_b.1, hstat_b.2, hstat_b.3, hstat_b.4, hstat_b.5, hstat_b.6, hstat_b.7, hstat_b.8,
     hstat_b.9, hstat_b.10⟩
  have huip_fals : sb.core.vals[uip.toNat]?.getD 0#8 = 0xFF#8 :=
    (hw_b.vals_false_iff uip.toNat huip_lt).mpr ⟨idx_u, hiu_te, by
      rw [hp_get, huip_nat]; exact (litNeg_litNeg _).symm⟩
  have huip_cl : (sb.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = sb.core.cur_level := by
    rwa [huip_nat, m6_xor1_div2]
  c0_let_simp
  refine wp_jnz_of (fun hc => ?_) (fun _ => ?_)
  · simp only [Arg.val_var] at hc; c0_cond hc; exact absurd hc huip_ne
  · c0_let_simp
    refine wp_store_sep (Full.Deduce1UipTactics.d1_store_full_tmp0_mul uip h0_tb hmb)
      (fun m_st hm_st => ?_)
    refine m6_deduce_res_clear_ret_wp hClear 1#64 hs0_len hw0 hcov0 hext0 hext_b hws2_b
      hnd0 hrefs0 hstat0 hdm0 hm0_lm hm_st
      fun mrk_c m_c hlen_c hotfs_c _ _ hcv_c hcl_c hfuel_c hws2_c hm_c => ?_
    let s_c : FullState :=
      { s0 with
        core := { s0.core with mrk := mrk_c, min_clr_len := 0 },
        scratch := { s0.scratch with res_sz := BitVec.ofNat 64 s0.core.min_clr_len } }
    have _hsc_tl_len : s_c.core.tmp.length = c.max_vars := htmp0_len
    have hnd_uip := Full.fullTmpTake_uip_nodup htl1 (by omega) htmp0_0 hlow0 huip_cl
    refine hQ 1#64 s_c m_c hlen_c (Or.inr (Or.inl rfl)) hcv_c hfuel_c hws2_c
      (fun h => by cases h) (fun h => by cases h) (fun _ => ?_) (fun h => by cases h) hm_c
    refine ⟨hotfs_c, hcl_c, htl1, htl_cv, hnd_uip, fun k hk => ?_, fun k hk1 hk2 => ?_, ?_, ?_⟩
    · cases k with
      | zero => rw [htmp0_0, Option.getD_some]; exact ⟨huip_lt, huip_fals⟩
      | succ k' => let hlk := hlow0.1 (k' + 1) (by omega) hk; exact ⟨hlk.1, hlk.2.1⟩
    · let hlk := hlow0.1 k hk1 hk2; exact ⟨hlk.2.2.1, hlk.2.2.2.1⟩
    · rw [htmp0_0, Option.getD_some]; exact huip_cl
    · rw [m6_lowerLits_tmp_take htl1 (by omega) htmp0_0, hlowLits0]
      exact hent_b

end Helpers

/-! ## 2. Seed, OTFS, Loop Step & `full_deduce_1uip_m6_wp` -/

section Deduce1UipM6

private theorem m6_deduce_seed_wp {Γ : Env}
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
      have hule : (s.core.confl_ref + 3#64).ule (BitVec.ofNat 64 s.core.arena_len) = true := by
        simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat,
          show (3#64 : BitVec 64).toNat = 3 from rfl,
          Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : s.core.confl_ref.toNat + 3 < 2 ^ 64)]
        omega
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

private theorem m6_deduce_otfs_ret2_subsume_wp {Γ : Env}
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
    refine m6_deduce_res_clear_ret_wp hClear 2#64 hlen_j hw_j hcov_j hext0 hext_j hws2_j
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

private theorem m6_deduce_loop_step_wp {Γ : Env}
    (hArsn : ∀ a m Q X, Full.fullAnalyzeRsnSpec a m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X)
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
        Full.fullArenaClauseRefs su = Full.fullArenaClauseRefs s ∧
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
        Full.FullDeduceStateInv c F0 F_cur cut_n idx_n s sn ∧ 0 < sn.core.tmp_cnt ∧
        (res_n = 0 → cut_n = cut ∧
          sn.core.confl_type = s.core.confl_type ∧ sn.core.confl_ref = s.core.confl_ref) ∧
        (FullMem c sn ⋆ R) m') →
      J_loop ys m')
    (hinv_l : ∃ (cut_cur idx resolved : Nat) (sl : FullState),
      p_18 = (BitVec.ofNat 64 idx, BitVec.ofNat 64 resolved, ()) ∧
      idx + resolved ≤ sl.core.trail_end ∧ Full.FullDeduceStateInv c F0 F_cur cut_cur idx s sl ∧
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
                                            (bs := [.bool]) "full_otfs_bin"
                                            (Arg.var c.hdr, Arg.var ld16, Arg.var ld10, ())
                                            fun p62 =>
                                          .jnz (Arg.var p62.fst)
                                            (.group (sig := [[]])
                                              (fun _Js4 => .cons (fun _ =>
                                                .let_ (Op.mk (.add i64)
                                                  (Arg.var c.hdr, Arg.imm 272#64, ())) fun p1 =>
                                                .load i64 (Arg.var p1.fst) fun ld =>
                                                .let_ (Op.mk (.add i64)
                                                  (Arg.var c.hdr, Arg.imm 1144#64, ())) fun p2 =>
                                                .store (Arg.var ld) (Arg.var p2.fst)
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
                                            (.jump Js.fst ()))
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
                                                      (Arg.var c.hdr, Arg.imm 272#64, ()))
                                                      fun p1 =>
                                                    .load i64 (Arg.var p1.fst) fun ld =>
                                                    .let_ (Op.mk (.add i64)
                                                      (Arg.var c.hdr, Arg.imm 1144#64, ()))
                                                      fun p2 =>
                                                    .store (Arg.var ld) (Arg.var p2.fst)
                                                    (.call (rs := [i64]) (as := [i64]) (bs := [])
                                                      "full_clear_ana" (Arg.var c.hdr, ())
                                                      fun _ => .ret (Arg.imm 2#64, ()))) .nil)
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
                                            (.jump Js.fst ())))
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
      rw [BitVec.toNat_setWidth, Full.Deduce1UipTactics.d1_bv32_lshr_1, Nat.mod_eq_of_lt hlt_pow]
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
        have hpv_rsns' : (BitVec.setWidth 64 (p_bv >>> 1)).toNat < sl.core.rsns.length := by
          rw [hpv_nat]; omega
        refine wp_load_of (FullArenaTactics.c0_load_full_lvl hpv_lvl' hml) ?_
        rw [getElem_eq_of_idx (hi := hpv_lvl') (hj := by omega) hpv_nat]
        c0_let_simp
        refine wp_jnz_of (fun hl1 => ?_) (fun hne => ?_)
        · have hpl_eq : sl.core.lvl[p_bv.toNat / 2] = BitVec.ofNat 32 s.core.cur_level :=
            beq_iff_eq.mp hl1
          have hpl_cl : (sl.core.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = sl.core.cur_level := by
            have hcl32 : sl.core.cur_level < 2 ^ 32 := by have := hw_l.cur_level_le; omega
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hpl_eq, ← hstat_l.cl,
              bv32_ofNat_toNat hcl32]
          have hmnz_tr :
              sl.core.mrk[(sl.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 := by
            rwa [hp_get]
          have hpl_tr :
              (sl.core.lvl[(sl.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
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
                rsn.toNat ∈ Full.fullArenaClauseRefs sl2 := fun hne hlg => by
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
            have hpv_rsns1 : (BitVec.setWidth 64 (p_bv >>> 1)).toNat < sl1.core.rsns.length :=
              hpv_rsns'
            fa_fast_steps_nogrp
            refine wp_load_of (FullArenaTactics.c0_load_full_rsns hpv_rsns1 hm1) ?_
            rw [getElem_eq_of_idx (hi := hpv_rsns1) (hj := by omega) hpv_nat]
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
              change r ∈ Full.fullArenaClauseRefs s2 at hr; rw [hrefs2] at hr
              have hll := hprops2 r hr
              change ((Full.fullArenaClauseLits s2 r).map (· / 2)).Nodup
              rw [hll.2.2]; refine hnd_l r hr ?_
              unfold Full.fullArenaClauseGarb Full.fullArenaClauseGarbCore Full.fullArenaHdrCore
                at hll hngr ⊢
              rw [← hll.2.1]; exact hngr
            have hext_s2 : Full.FullExtScratchPres s s2 :=
              Full.fullExtScratchPres_trans hext_2 hext2
            have hrefs_s2 : Full.fullArenaClauseRefs s2 = Full.fullArenaClauseRefs s :=
              hrefs2.trans hrefs_l
            have hstat_s2 : Full.FullDeduceStaticEq s.core s2.core :=
              ⟨hstat_2.1, hstat_2.2, hstat_2.3, hstat_2.4, hstat_2.5, hstat_2.6, hstat_2.7,
               hstat_2.8, hstat_2.9, hstat_2.10⟩
            cases ok2 with
            | false =>
              fa_fast_steps
              exact m6_deduce_clear_ret0_wp hClear hQ hlen2 hw2 hcov2 hext0 hext_s2
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
              have hrefs_s3 : Full.fullArenaClauseRefs s3 = Full.fullArenaClauseRefs s := hrefs_s2'
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
                  have hant_pos : (BitVec.ofNat 64 3).ule sc2.ant_sz = true := by
                    simp only [BitVec.ule, decide_eq_true_eq,
                      bv64_ofNat_toNat (by omega : 3 < 2 ^ 64)]
                    exact hant_pos_nat
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
                  have hr_get_s2 :
                      s2.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn := by
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
                  have heq_s2 : Full.fullArenaClauseLits s2 rsn.toNat =
                      Full.fullRsnLits sl2 rsn := by
                    have hll :=
                      (hprops2 rsn.toNat (hrefs_l ▸ (hrsn_ref hok_ne hrsn_lg))).2.2
                    change Full.fullArenaClauseLits s2 rsn.toNat =
                      Full.fullArenaClauseLits sl2 rsn.toNat at hll
                    unfold Full.fullRsnLits
                    rw [ite_eq_right (fun h => hok_ne h),
                      ite_eq_right (fun h => absurd hrsn_lg h)]
                    exact hll
                  have hant_s2 : sc2.ant_sz = BitVec.ofNat 64
                      ((Full.fullRsnLits s2 rsn).countP fun l =>
                      decide (l / 2 < s2.core.cur_vars ∧
                        0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat ∧
                        (s2.core.lvl[l / 2]?.getD 0#32).toNat ≤ s2.core.cur_level)) := by
                    have heq_r : Full.fullRsnLits s2 rsn = Full.fullRsnLits sl2 rsn := by
                      unfold Full.fullRsnLits
                      rw [ite_eq_right (fun h => hok_ne h),
                        ite_eq_right (fun h => absurd hrsn_lg h)]
                      exact heq_s2
                    simpa only [heq_r, BitVec.zero_add] using hok_ant
                  have hall_s3 : ∀ l ∈ Full.fullArenaClauseLitsCore s3.core rsn.toNat,
                      l / 2 ≠ p_bv.toNat / 2 → 0 < (s3.core.lvl[l / 2]?.getD 0#32).toNat →
                      mrk2[l / 2]?.getD 0#8 ≠ 0#8 := by
                    intro l hl hne hpos
                    have hl_sl2 : l ∈ Full.fullRsnLits sl2 rsn := heq_s2 ▸ hl
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
                    have hbin_ent := Full.otfs_entails_bin_of_res_lt_ant hw_s2 hnd_s2 hlen2
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
                    have hcov_b := m6_anaMarksCov_of_same (s2 := s_b) hcov_s3 rfl rfl rfl hws1_b
                    have hext_sb := Full.fullExtScratchPres_trans hext_s3 hext_b
                    have hrefs_sb : Full.fullArenaClauseRefs s_b = Full.fullArenaClauseRefs s :=
                      hrefs_b.trans hrefs_s3
                    cases ok_b with
                    | true =>
                      obtain ⟨hct_b, hconfl_b⟩ := hok_b rfl
                      fa_fast_steps_nogrp
                      refine m6_deduce_otfs_ret2_subsume_wp (init_res_sz := init_res_sz)
                        (p := p_bv) (rsn := rsn) (new_confl_arg := Arg.imm 0#32)
                        (to_bin := true) hClear hOtfsSub hQ hw0
                        hconfl0 hext0 hdm0 hm0_lm hlen_b hw_b hcov_b hext_sb
                        (hws2_b.trans hws2_s2) hnd_b hrefs_sb hstat_s3.repack hconfl_b hte_s3
                        hres1_lt64 (fun _ => hct_b)
                        (fun hr0 => by
                          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hzero_b hr0
                          exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun hc => by cases hc⟩)
                        hm_b
                    | false =>
                      fa_fast_steps
                      exact hJin () m_b ⟨idx', s_b, hir3,
                        ⟨hlen_b, hw_b, hcov_b, hext_sb, hws2_b.trans hws2_s2, hnd_b, hrefs_sb,
                         hstat_s3.repack, htl2_1, htl2_cv', htc2_eq', hlow2, hmcov2,
                         fun j hj _ _ => hj, hent2, hres_b⟩,
                        htc2_pos, hm_b⟩
                  · have hlarge_ent := Full.otfs_entails_large_of_res_lt_ant hw_s2 hnd_s2 hlen2
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
                      m6_anaMarksCov_of_same (s2 := s_l) hcov_s3 rfl rfl rfl hws1_l
                    have hext_sl := Full.fullExtScratchPres_trans hext_s3 hext_l
                    have hrefs_sl : Full.fullArenaClauseRefs s_l = Full.fullArenaClauseRefs s :=
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
                        m6_cut_with_confl hw_l 2#64 (rsn.setWidth 64)
                      have hconfl_ot : Full.FullConflictOkCut F_cur idx' s_ot :=
                        Full.deduce_large_conflOk_of href_l hng_l hlits_l
                      refine m6_deduce_otfs_ret2_subsume_wp (init_res_sz := init_res_sz)
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
                      fa_fast_steps
                      exact hJin () m_l ⟨idx', s_l, hir3,
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
              by rw [htc_eq, show idx = idx' + 1 by omega,
                Full.fullCurTrailIdxs_succ_eq_self hnot'],
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

/-- Canonical `Full.fullDeduce1uipSpec` proof for `full_deduce_1uip_m6_body`. -/
theorem full_deduce_1uip_m6_wp (Γ : Env)
    (hAlit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, Full.fullAnalyzeRsnSpec a m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X) :
    ∀ a m Q X, Full.fullDeduce1uipSpec a m Q X →
      Func.wp Γ full_deduce_1uip_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, cut, s, R, rfl, hinv, hcur_pos, hconfl, hm0, hQ⟩
  unfold Func.wp full_deduce_1uip_m6_body
  have ⟨hlen0, hw0, hlm0, hnd0, hext0, hdm0⟩ := hinv
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hte_le := hlen0.core_ok.trail_end_le
  fa_fast_steps_nogrp
  refine wp_join_group (ts := [.bool]) (fun ys m_sd =>
    ∃ s1 : FullState,
      s1.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut s1.core ∧
      Full.FullAnaMarksCov c s1 ∧ Full.FullExtScratchPres s s1 ∧
      s1.scratch.work_stk2 = s.scratch.work_stk2 ∧ Full.FullArenaVarsNodup s1 ∧
      Full.fullArenaClauseRefs s1 = Full.fullArenaClauseRefs s ∧
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
        Full.fullArenaClauseRefs s_cl = Full.fullArenaClauseRefs s ∧
        Full.FullDeduceStaticEq s.core s_cl.core ∧
        (seed_ok = true → s_cl.core.tmp_len = 1 → F0.Unsat) ∧
        (FullMem c s_cl ⋆ R) m_cl)
      (fun _ ⟨⟩ m_cl ⟨s_cl, hlen_cl, hw_cl, hcov_cl, hext_cl, hws2_cl, hnd_cl, hrefs_cl, hstat_cl,
          hunsat, hm_cl⟩ =>
        m6_deduce_clear_unsat_goal_wp hClear hQ hlen_cl hw_cl hcov_cl hext0 hext_cl hws2_cl
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
            have h := congrArg BitVec.toNat (by assumption : BitVec.ofNat 64 s1.core.tmp_cnt = 0#64)
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
          (BitVec.ofNat 64 s1.core.cur_level).setWidth 32 = BitVec.ofNat 32 s.core.cur_level := by
        rw [hstat1.cl]; exact m6_bv64_setWidth32_ofNat hcl32
      refine wp_join_group (ts := [i64, i32, i64]) (fun ys m_u =>
        ∃ (cut_u idx_u : Nat) (su : FullState) (p_u : BitVec 32),
          su.LengthsOk c ∧ Full.FullWitnessCutInv c F0 F_cur cut_u su.core ∧
          Full.FullAnaMarksCov c su ∧ Full.FullExtScratchPres s su ∧
          su.scratch.work_stk2 = s.scratch.work_stk2 ∧ Full.FullArenaVarsNodup su ∧
          Full.fullArenaClauseRefs su = Full.fullArenaClauseRefs s ∧
          Full.FullDeduceStaticEq s.core su.core ∧ 1 ≤ su.core.tmp_len ∧
          su.core.tmp_len ≤ su.core.cur_vars ∧
          Full.FullLowerInv c su.core su.core.tmp su.core.mrk su.core.tmp_len ∧
          idx_u < su.core.trail_end ∧ (su.core.trl[idx_u]?.getD 0#32).toNat = p_u.toNat ∧
          (su.core.lvl[p_u.toNat / 2]?.getD 0#32).toNat = su.core.cur_level ∧
          ys.2.1 = p_u ^^^ 1#32 ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((p_u ^^^ 1#32).toNat :: Full.fullLowerLits su.core.tmp su.core.tmp_len)) ∧
          (FullMem c su ⋆ R) m_u)
        (fun _ ⟨idx_u_bv, uip_bv, res_u_bv, ⟨⟩⟩ _m_u ⟨cut_u, idx_u, su, p_u, hlu, hwu, hcu, heu,
            hwu2, hndu, hru, hsu, htl_u1, htl_ucv, hlowu, hiu_te, hpu_get, hplu, hys_u, hentu,
            hmu⟩ => by
          dsimp only at hys_u; subst uip_bv
          rw [Blocks.get_here]; try dsimp only
          exact m6_deduce_uip_exit_body_wp hClear hQ hext0 hdm0 hlm0 hlu hwu hcu heu hwu2
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
        rw [Blocks.get_here]; try dsimp only
        exact m6_deduce_loop_step_wp hArsn hClear hOtfsLarge hOtfsBin hOtfsSub hQ hw0
          hcur_pos hconfl hext0 hdm0 hlm0 (fun idx' uip res' mu h =>
            hJuip (idx', uip, res', ()) mu h) hJloop hinv_l
    · exact hJcl () m_sd ⟨s1, hlen1, hw1, hcov1, hext1, hws2_1, hnd1, hrefs1, hstat1,
        (fun h => by
          have hf : seed_ok = false := by assumption
          exact absurd (h.symm.trans hf) (by decide)), hm1⟩
  · intro J hJ
    exact wp_mono (fun _ _ h => h.elim) (fun _ _ _ _ h => h) _ _
      (m6_deduce_seed_wp hAlit hArsn hinv hcur_pos hconfl (by assumption) fun seed_ok m_sd h =>
        hJ (seed_ok, ()) m_sd h)

end Deduce1UipM6

end LeanQbe.T.Examples.Kissat.FullM6MinShrink
