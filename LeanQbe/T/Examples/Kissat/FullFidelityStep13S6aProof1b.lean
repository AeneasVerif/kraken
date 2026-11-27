/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityVivFlag
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3a
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3b
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Step-13 S6a Unchanged-Caller Lifts — Part 1b (`full_viv_clause_m6`)

100% callee-parametric (`Γ : Env`) Step-13 lift for `FullFidelityVivFlag.fid11_viv_clause_m6_body`
over `step13PropagateIgnoreM6Spec` and `step13VivFinishM6Spec` (`FullM6HdrMem` + `M6HdrExtOk` +
`FullM6HdrInvW` + `M6HdrScratchPres`), certifying `step13VivClauseM6Spec` (`public section`,
`0 @[expose]`, `0` `import all`, `<= std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullVivTopTactics FullVivTop
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullFidelityVivFlag
open scoped FullArenaTactics FullVivTopTactics

private theorem s6a_viv_sparseInvW_of_prop13 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch} :
    let s' : FullState :=
      { core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
          wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
          confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' }
    s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
    FullArenaPermEq s.core s'.core →
    FullProbeScratchPres { core := s.core, scratch :=
      { s.scratch with
        search_ticks := sc'.search_ticks, phases := sc'.phases,
        wsort := sc'.wsort, delayed := sc'.delayed } } s' →
    FullSparseInvW c F0 F_cur s' := by
  intro s' hlen' hw' hperm hsc
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hperm.2.1
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    obtain ⟨_, hgb, hpm⟩ := hperm.2.2 r hr
    change fullArenaClauseGarbCore s'.core r = false at hng; rw [hgb] at hng
    exact (hsp.2.2.2.1 r hr hng).perm (hpm.map (· / 2)).symm
  have hrefs : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s' := fun r hr => by
    change r ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr
  have hext : FullExtScratchOk c s' := hsp.2.2.2.2.1.of_pres hsc.1 hrefs
  exact ⟨hlen', hw', hsp.2.2.1, hnd', hext, hsp.2.2.2.2.2⟩

private theorem s6a_viv_clause_prop_step13 (Γ : Env)
    (hPropIgn : ∀ a m Q X, step13PropagateIgnoreM6Spec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hBestImpl : ∀ a m Q X, fullVivBestImpliedM6Spec a m Q X →
      Γ "full_viv_best_implied_m6" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext_as : List (BitVec 64)} {s s5 sp s_as : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {B : Cont [i32, .bool, i32]} {J_jn : Cont [.bool, i32]}
    {cref i lit sz : BitVec 32} {tmp5 : List (BitVec 32)} {lits2 : List Nat} {m_as : Mem 64}
    (hcfg : FullM6HdrCfgOk c) (hext_as : M6HdrExtOk ext_as)
    (hQ : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext' s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      r = 1#64 ∨ r = 2#64 ∨ r = 20#64 → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m')
    (hB : ∀ (r : Tup Val [i32, .bool, i32]) (m' : Mem 64),
      (match r with
      | (ib, confl, implied, ()) => ∃ (extb : List (BitVec 64)) (sb : FullState),
        M6HdrExtOk extb ∧ FullSparseInvW c F0 F_cur sb ∧
        sb.core.cur_vars = s5.core.cur_vars ∧ sb.core.arena_len = s5.core.arena_len ∧
        sb.core.probing = s5.core.probing ∧ sb.core.tmp = tmp5 ∧
        sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
        sb.scratch.red_refs = s.scratch.red_refs ∧
        cref.toNat ∈ fullArenaClauseRefs sb ∧
        fullArenaClauseGarb sb cref.toNat = false ∧
        fullArenaClauseSize sb cref.toNat = sz.toNat ∧
        (fullArenaClauseLits sb cref.toNat).Perm lits2 ∧
        (confl = true → FullConflictOkW F_cur sb) ∧
        (confl = false → implied ≠ 0xFFFFFFFF#32 →
          implied.toNat < 2 * sb.core.cur_vars ∧
          sb.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
        (confl = false → implied = 0xFFFFFFFF#32 → ib = sz →
          sb.core.confl_type = 0#64 ∧
          ∀ l ∈ fullArenaClauseLits sb cref.toNat, sb.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (FullMem c sb ⋆ (m6ExtMem (m6ExtAddr c.hdr) extb ⋆ R)) m') → B r m')
    (hJ_jn : ∀ (xs : Tup Val [.bool, i32]) (m : Mem 64),
      (∃ (ext_jn : List (BitVec 64)) (s_jn : FullState),
        M6HdrExtOk ext_jn ∧ FullSparseInvW c F0 F_cur s_jn ∧
        s_jn.core.cur_vars = s5.core.cur_vars ∧
        s_jn.core.arena_len = s5.core.arena_len ∧
        s_jn.core.probing = s5.core.probing ∧ s_jn.core.tmp = tmp5 ∧
        s_jn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs s_jn = fullArenaClauseRefs s ∧
        s_jn.scratch.red_refs = s.scratch.red_refs ∧
        cref.toNat ∈ fullArenaClauseRefs s_jn ∧
        fullArenaClauseGarb s_jn cref.toNat = false ∧
        fullArenaClauseSize s_jn cref.toNat = sz.toNat ∧
        (fullArenaClauseLits s_jn cref.toNat).Perm lits2 ∧
        s_jn.core.confl_type = 0#64 ∧
        (∀ k < (i + 1#32).toNat,
          s_jn.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
        (FullMem c s_jn ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext_jn ⋆ R)) m) → J_jn xs m)
    (hsp_as : FullSparseInvW c F0 F_cur s_as) (hsz_le_mv : sz.toNat ≤ c.max_vars)
    (hcvp : sp.core.cur_vars = s5.core.cur_vars) (hcv_as : s_as.core.cur_vars = sp.core.cur_vars)
    (halp : sp.core.arena_len = s5.core.arena_len)
    (hal_as : s_as.core.arena_len = sp.core.arena_len)
    (hprp : sp.core.probing = s5.core.probing) (hpr_as : s_as.core.probing = sp.core.probing)
    (hflp : sp.core.fuel.toNat ≤ s.core.fuel.toNat) (hfl_as : s_as.core.fuel = sp.core.fuel)
    (hal5 : s5.core.arena_len = s.core.arena_len)
    (hrefsp : fullArenaClauseRefs sp = fullArenaClauseRefs s)
    (hrefs_as : fullArenaClauseRefs s_as = fullArenaClauseRefs sp)
    (hrr_as : s_as.scratch.red_refs = s.scratch.red_refs)
    (hrefp : cref.toNat ∈ fullArenaClauseRefs sp)
    (hng_as : fullArenaClauseGarb s_as cref.toNat = false)
    (hsz_as : fullArenaClauseSize s_as cref.toNat = sz.toNat)
    (hpermp : (fullArenaClauseLits sp cref.toNat).Perm lits2)
    (hlits_as : fullArenaClauseLits s_as cref.toNat = fullArenaClauseLits sp cref.toNat)
    (hct_as : s_as.core.confl_type = 0#64) (htmp_as : s_as.core.tmp = tmp5)
    (hlits2_lt : ∀ l ∈ lits2, l < 2 * s5.core.cur_vars)
    (hlits2_mem : ∀ k < sz.toNat, (tmp5[k]?.getD 0#32).toNat ∈ lits2)
    (hi_lt : i.toNat < sz.toNat) (hlit_eq : lit = tmp5[i.toNat]?.getD 0#32)
    (hlit_lt : lit.toNat < 2 * sp.core.cur_vars)
    (hfalp : ∀ k < i.toNat, sp.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (hfal_as : ∀ l < 2 * sp.core.cur_vars,
      sp.core.vals[l]?.getD 0#8 = 0xFF#8 → s_as.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hlit_as_ff : s_as.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8)
    (hm_as : (FullMem c s_as ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext_as ⋆ R)) m_as) :
    wp Γ Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) "full_propagate_ignore"
        (Arg.var c.hdr, Arg.var (cref.setWidth 64), ()) fun p =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
            args := (Arg.var p.fst, Arg.imm 2, ()) }
          fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
            (Arg.var c.hdr, Arg.imm 0, ()) fun _ =>
            Expr.ret (Arg.imm 2, ()))
          (Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
              args := (Arg.var p.fst, Arg.imm 1, ()) }
            fun p =>
            Expr.jnz (Arg.var p.fst)
              (Expr.jump B (Arg.var i, Arg.imm true, Arg.imm 4294967295, ()))
              (Expr.call (as := [i64, i32]) (bs := [i32]) "full_viv_best_implied_m6"
                (Arg.var c.hdr, Arg.var sz, ()) fun p =>
                Expr.let_
                  { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                    args := (Arg.var p.fst, Arg.imm 4294967295, ()) }
                  fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.jump B (Arg.var i, Arg.imm false, Arg.var p.fst, ()))
                  (Expr.jump J_jn (Arg.imm false, Arg.imm 4294967295, ())))))
      m_as := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, ext_as, s_as, R, rfl, hcfg, hext_as, hsp_as.1, hsp_as.2.1,
    hsp_as.2.2.2.2.2, fullM6HdrMem_unfocus_full hm_as, ?_⟩
  intro pr ext_p vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p wvec_p
    arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p sc_p m_p _ hext_p _
    hlen_p hw_p htr_p hperm_p hsc_pres hrr_p _ _ _ hfl_p hpr_disj hpr0 hpr1 _ _ hm_p
  let s_p : FullState :=
    { core := { s_as.core with
        vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
        trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
        unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
        arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
        fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
        confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
      scratch := sc_p }
  have hsp_p : FullSparseInvW c F0 F_cur s_p :=
    s6a_viv_sparseInvW_of_prop13 hsp_as hlen_p hw_p hperm_p hsc_pres
  have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s_as := hperm_p.2.1
  have hcv_p : s_p.core.cur_vars = s5.core.cur_vars := hcv_as.trans hcvp
  have hal_p : s_p.core.arena_len = s5.core.arena_len := hal_as.trans halp
  have hpr_p : s_p.core.probing = s5.core.probing := hpr_as.trans hprp
  have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p (hfl_as ▸ hflp)
  have hrefs_p' : fullArenaClauseRefs s_p = fullArenaClauseRefs s :=
    hrefs_p.trans (hrefs_as.trans hrefsp)
  have hrr_p : s_p.scratch.red_refs = s.scratch.red_refs := hrr_p.trans hrr_as
  have href_p : cref.toNat ∈ fullArenaClauseRefs s_p := hrefs_p ▸ hrefs_as ▸ hrefp
  have hprops_p := hperm_p.2.2 cref.toNat (by
    change cref.toNat ∈ fullArenaClauseRefs s_as; rw [hrefs_as]; exact hrefp)
  have hng_p : fullArenaClauseGarb s_p cref.toNat = false := hprops_p.2.1.trans hng_as
  have hsz_p : fullArenaClauseSize s_p cref.toNat = sz.toNat := hprops_p.1.trans hsz_as
  have hlits_p : (fullArenaClauseLits s_p cref.toNat).Perm lits2 :=
    hprops_p.2.2.trans (by
      change (fullArenaClauseLits s_as cref.toNat).Perm lits2; rw [hlits_as]; exact hpermp)
  have hm_p' : (FullMem c s_p ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext_p ⋆ R)) m_p :=
    fullM6HdrMem_focus_full hm_p
  have hcv_p_as : s_p.core.cur_vars = s_as.core.cur_vars := rfl
  have htmp_p : s_p.core.tmp = tmp5 := htmp_as
  have hte_p' : s_as.core.trail_end ≤ s_p.core.trail_end := htr_p.1
  have htrl_p' : ∀ idx < s_as.core.trail_end, s_p.core.trl[idx]? = s_as.core.trl[idx]? := htr_p.2.1
  have hcok_p_fn : pr = 1#64 → FullConflictOkW F_cur s_p := fun h => (hpr1 h).2.2.1
  have hct_p0_fn : pr = 0#64 → s_p.core.confl_type = 0#64 := fun h => (hpr0 h).2.1.trans hct_as
  clear_value s_p; clear hm_p hm_as hprops_p hperm_p htr_p
  fvt_steps
  · have hp_cl_lt : s_p.core.cur_level < 2 ^ 64 := by
      have := hsp_p.2.1.cur_level_le; have := hsp_p.1.core_ok.trail_end_le
      have := hsp_p.1.core_ok.cur_vars_le; omega
    c0_call hBacktrack
    refine ⟨c, s_p, (m6ExtMem (m6ExtAddr c.hdr) ext_p ⋆ R), rfl, hsp_p.1, hp_cl_lt,
      (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro
          have := hsp_p.2.1.cur_level_le; have := hsp_p.1.core_ok.trail_end_le
          have := hsp_p.1.core_ok.cur_vars_le; omega),
      hsp_p.2.1.trail_lits_lt, hm_p',
      fun vals_b lvl_b rsns_b trl_b tp_b te_b prop_b cl_b unass_b sc_b m_b
        hlen_b _ _ _ hpres_b hsc_b _ _ hw_b _ hm_b => ?_⟩
    have hsp_b : FullSparseInvW c F0 F_cur _ :=
      FullVivTop.FullSparseInvW.of_backtrack hsp_p (Nat.zero_le _) hlen_b hpres_b
        (hw_b F0 F_cur hsp_p.2.1 (Nat.zero_le _))
    rcases hsc_b with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
    fvt_steps
    exact hQ 2#64 ext_p _ m_b (FullM6HdrInvW.mk_inv hcfg hext_p hsp_b) hfl_p' (hal_p.trans hal5)
      hrefs_p' hrr_p (Or.inr (Or.inl rfl)) (fun h => by cases h) (fullM6HdrMem_unfocus_full hm_b)
  · have hpr_eq1 : pr = 1#64 := by c0_bound
    fvt_steps
    exact hB (i, true, 0xFFFFFFFF#32, ()) _ ⟨ext_p, s_p, hext_p, hsp_p, hcv_p, hal_p, hpr_p,
      htmp_p, hfl_p', hrefs_p', hrr_p, href_p, hng_p, hsz_p, hlits_p, fun _ => hcok_p_fn hpr_eq1,
      (fun h => by cases h), (fun h => by cases h), hm_p'⟩
  · have hpr_eq0 : pr = 0#64 := by
      rcases hpr_disj with rfl | rfl | rfl
      · rfl
      · exact absurd rfl (by c0_bound)
      · exact absurd rfl (by c0_bound)
    have hct_p0 : s_p.core.confl_type = 0#64 := hct_p0_fn hpr_eq0
    have htmp_p_lt : ∀ k < sz.toNat, (s_p.core.tmp[k]?.getD 0#32).toNat < 2 * s_p.core.cur_vars :=
      fun k hk => by rw [htmp_p, hcv_p]; exact hlits2_lt _ (hlits2_mem k hk)
    c0_call hBestImpl
    refine ⟨c, F0, F_cur, s_p, (m6ExtMem (m6ExtAddr c.hdr) ext_p ⋆ R), rfl, hsp_p, hsz_le_mv,
      htmp_p_lt, hm_p', fun bi hbi => ?_⟩
    fvt_steps
    · have hbi_ne : bi ≠ 0xFFFFFFFF#32 := by c0_bound
      exact hB (i, false, bi, ()) _ ⟨ext_p, s_p, hext_p, hsp_p, hcv_p, hal_p, hpr_p, htmp_p,
        hfl_p', hrefs_p', hrr_p, href_p, hng_p, hsz_p, hlits_p, (fun h => by cases h),
        fun _ _ => hbi hbi_ne, fun _ h => absurd h hbi_ne, hm_p'⟩
    · have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      have hfal_p1 : ∀ k < (i + 1#32).toNat,
          s_p.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
        intro k hk; rw [hi1_nat] at hk
        rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
        · have hk_lt_sp : (tmp5[k]?.getD 0#32).toNat < 2 * sp.core.cur_vars := by
            rw [hcvp]; exact hlits2_lt _ (hlits2_mem k (by omega))
          exact falsified_preserved_of_trailExt hsp_as.2.1 hsp_p.2.1 hcv_p_as hte_p' htrl_p'
            (hcv_as ▸ hk_lt_sp) (hfal_as _ hk_lt_sp (hfalp k hk'))
        · rw [← hlit_eq]
          exact falsified_preserved_of_trailExt hsp_as.2.1 hsp_p.2.1 hcv_p_as hte_p' htrl_p'
            (hcv_as ▸ hlit_lt) hlit_as_ff
      exact hJ_jn _ _ ⟨ext_p, s_p, hext_p, hsp_p, hcv_p, hal_p, hpr_p, htmp_p, hfl_p', hrefs_p',
        hrr_p, href_p, hng_p, hsz_p, hlits_p, hct_p0, hfal_p1, hm_p'⟩

private theorem s6a_viv_clr_hdr_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext_f : List (BitVec 64)} {s_f : FullState} {cref : BitVec 32}
    (hinv_f : FullM6HdrInvW c F0 F_cur ext_f s_f)
    (href_f : cref.toNat ∈ fullArenaClauseRefs s_f)
    (hcr_f_lt : cref.toNat < s_f.core.arena.length) :
    let hdr_v := (s_f.core.arena[cref.toNat]'hcr_f_lt) &&& ~~~0x00100000#32
    let s_v : FullState :=
      { s_f with core := { s_f.core with arena := s_f.core.arena.set cref.toNat hdr_v } }
    FullM6HdrInvW c F0 F_cur ext_f s_v ∧ fullArenaClauseRefs s_v = fullArenaClauseRefs s_f := by
  have hspf := FullM6HdrInvW.sparseW hinv_f
  let hdr_f := s_f.core.arena[cref.toNat]'hcr_f_lt
  have hhdr_f : fullArenaHdr s_f cref.toNat = hdr_f := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_f_lt, Option.getD_some]
  let hdr_v := hdr_f &&& ~~~0x00100000#32
  obtain ⟨hsp_v, hrefs_v, _⟩ :=
    fullSparseInvW_set_hdr_non_gs hspf href_f hdr_v
      s_f.core.num_irred s_f.core.num_redundant
      (by rw [hhdr_f]; exact bv32_clr_viv_garb hdr_f)
      (by rw [hhdr_f]; exact bv32_clr_viv_shrk hdr_f)
  exact ⟨FullM6HdrInvW.mk_inv hinv_f.cfgOk hinv_f.extOk hsp_v, hrefs_v⟩

private theorem s6a_viv_assign_prep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sp : FullState} {lit : BitVec 32} (hspp : FullSparseInvW c F0 F_cur sp)
    (hlit_lt : lit.toNat < 2 * sp.core.cur_vars)
    (hlv0 : sp.core.vals[lit.toNat]?.getD 0#8 = 0#8) :
    let nlvl := sp.core.cur_level + 1
    let dlit := lit ^^^ 1#32
    let ftrl' := sp.core.frame_trail.set nlvl (BitVec.ofNat 32 sp.core.trail_end)
    let fdec' := sp.core.frame_dec.set nlvl dlit
    let s_pre : FullState :=
      { sp with core :=
        { sp.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl } }
    sp.core.trail_end < c.max_vars ∧ nlvl ≤ c.max_vars ∧
    s_pre.LengthsOk c ∧
    ¬ (s_pre.core.cur_vars ≤ (lit ^^^ 1).toNat / 2 ∨
       c.max_vars ≤ s_pre.core.trail_end ∨
       s_pre.core.vals[(lit ^^^ 1).toNat]?.getD 0#8 ≠ 0#8) := by
  have hsp_len := hspp.1.core_ok
  have hte_lt : sp.core.trail_end < c.max_vars := by
    have := hspp.2.1.trail_end_lt_of_unassigned hlit_lt hlv0
    have := hsp_len.cur_vars_le
    omega
  have hnlvl_le : sp.core.cur_level + 1 ≤ c.max_vars := by
    have := hspp.2.1.cur_level_le; have := hsp_len.cur_vars_le; omega
  let nlvl := sp.core.cur_level + 1
  let dlit := lit ^^^ 1#32
  let ftrl' := sp.core.frame_trail.set nlvl (BitVec.ofNat 32 sp.core.trail_end)
  let fdec' := sp.core.frame_dec.set nlvl dlit
  let s_pre : FullState :=
    { sp with core :=
      { sp.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl } }
  have hlen_pre : s_pre.LengthsOk c :=
    ⟨{ hsp_len with
         frame_trail_len := by simp [s_pre, ftrl', hsp_len.frame_trail_len],
         frame_dec_len := by simp [s_pre, fdec', hsp_len.frame_dec_len] },
     hspp.1.scratch_ok⟩
  have hdlit_nat : dlit.toNat = lit.toNat ^^^ 1 := bv32_xor1_toNat lit
  have hdlit_lt : dlit.toNat < 2 * sp.core.cur_vars :=
    hdlit_nat ▸ bv32_xor1_lt_even hlit_lt
  have hdlit_zero : sp.core.vals[dlit.toNat]?.getD 0#8 = 0#8 :=
    hdlit_nat ▸ vals_xor1_eq_zero hspp.2.1 hlit_lt hlv0
  refine ⟨hte_lt, hnlvl_le, hlen_pre, fun hor => ?_⟩
  have h1xor : (lit ^^^ 1 : BitVec 32).toNat = dlit.toNat := rfl
  rw [h1xor] at hor
  rcases hor with h1 | h2 | h3
  · dsimp only [s_pre] at h1; omega
  · have := hsp_len.cur_vars_le; dsimp only [s_pre] at h2; omega
  · exact h3 hdlit_zero

private theorem s6a_viv_vals_ff_of_ne {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sp : FullState} {lit : BitVec 32} (hspp : FullSparseInvW c F0 F_cur sp)
    (hlit_lt : lit.toNat < 2 * sp.core.cur_vars)
    (hlit_lt_vals : lit.toNat < sp.core.vals.length)
    (hne0_raw : (sp.core.vals[lit.toNat]'hlit_lt_vals).signExtend 32 ≠ 0#32)
    (hflt : (0#32).slt ((sp.core.vals[lit.toNat]'hlit_lt_vals).signExtend 32) = false) :
    sp.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
  have hdom := hspp.2.1.vals_domain lit.toNat hlit_lt
  have hlv_eq : sp.core.vals[lit.toNat]? = some (sp.core.vals[lit.toNat]'hlit_lt_vals) :=
    List.getElem?_eq_getElem hlit_lt_vals
  have hne1 : sp.core.vals[lit.toNat]'hlit_lt_vals ≠ 1#8 := fun heq => by
    have hgt : (0#32).slt ((sp.core.vals[lit.toNat]'hlit_lt_vals).signExtend 32) = true := by
      rw [heq]; decide
    exact Bool.false_ne_true (hflt.symm.trans hgt)
  have hne0 : sp.core.vals[lit.toNat]'hlit_lt_vals ≠ 0#8 := fun heq => by
    have heq0 : (sp.core.vals[lit.toNat]'hlit_lt_vals).signExtend 32 = 0#32 := by
      rw [heq]; decide
    exact hne0_raw heq0
  rw [hlv_eq, Option.getD_some]
  rcases (by simpa [hlv_eq] using hdom) with h | h | h
  · exact absurd h hne0
  · exact absurd h hne1
  · exact h

private theorem s6a_viv_post_reuse_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s2 s4r s5 : FullState} {cref sz : BitVec 32} {lits2 : List Nat}
    (hs5 : s5 = { s4r with core :=
      { s4r.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } })
    (hlits2 : lits2 = fullArenaClauseLits s2 cref.toNat)
    (hsp2 : FullSparseInvW c F0 F_cur s2) (hsp4r : FullSparseInvW c F0 F_cur s4r)
    (hcv4r : s4r.core.cur_vars = s2.core.cur_vars)
    (har4r : s4r.core.arena = s2.core.arena) (hal4r : s4r.core.arena_len = s2.core.arena_len)
    (hfl4r : s4r.core.fuel = s2.core.fuel) (hrr4r : s4r.scratch.red_refs = s2.scratch.red_refs)
    (hfl1 : s2.core.fuel.toNat ≤ s.core.fuel.toNat) (hal1 : s2.core.arena_len = s.core.arena_len)
    (hrefs1 : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hrr1 : s2.scratch.red_refs = s.scratch.red_refs)
    (href2 : cref.toNat ∈ fullArenaClauseRefs s2)
    (hng2 : fullArenaClauseGarb s2 cref.toNat = false)
    (hsz2 : fullArenaClauseSize s2 cref.toNat = sz.toNat) :
    FullSparseInvW c F0 F_cur s5 ∧ s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧
    s5.core.arena_len = s.core.arena_len ∧ fullArenaClauseRefs s5 = fullArenaClauseRefs s ∧
    s5.scratch.red_refs = s.scratch.red_refs ∧ cref.toNat ∈ fullArenaClauseRefs s5 ∧
    fullArenaClauseGarb s5 cref.toNat = false ∧ fullArenaClauseSize s5 cref.toNat = sz.toNat ∧
    (fullArenaClauseLits s5 cref.toNat).Perm lits2 ∧
    ∀ l ∈ lits2, l < 2 * s5.core.cur_vars := by
  subst hs5 hlits2
  have hrefs_eq4r : fullArenaClauseRefs
      { s4r with core := { s4r.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } } =
      fullArenaClauseRefs s2 := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; change _ = _; rw [har4r, hal4r]
  refine ⟨FullVivTop.FullSparseInvW.with_confl hsp4r 0#64 0xFFFFFFFF#64,
    by change s4r.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfl4r]; exact hfl1,
    hal4r.trans hal1, hrefs_eq4r.trans hrefs1, hrr4r.trans hrr1, hrefs_eq4r ▸ href2, ?_, ?_, ?_, ?_⟩
  · unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
    change (s4r.core.arena[cref.toNat]?.getD 0#32 &&& 0x00080000#32 != 0#32) = false
    rw [har4r]; exact hng2
  · unfold fullArenaClauseSize fullArenaClauseSizeCore
    change (s4r.core.arena[cref.toNat + 2]?.getD 0#32).toNat = sz.toNat; rw [har4r]; exact hsz2
  · have heq : fullArenaClauseLits
        { s4r with core := { s4r.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } }
        cref.toNat = fullArenaClauseLits s2 cref.toNat := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
      change ((s4r.core.arena.drop (cref.toNat + 3)).take
        (s4r.core.arena[cref.toNat + 2]?.getD 0#32).toNat).map BitVec.toNat = _
      rw [har4r]
    rw [heq]
  · exact fun l hl => by
      change l < 2 * s4r.core.cur_vars; rw [hcv4r]
      exact hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 l hl

theorem full_viv_clause_m6_step13_wp (Γ : Env)
    (hL0Simp : ∀ a m Q X, fullVivL0SimpM6Spec a m Q X →
      Γ "full_viv_l0_simp_m6" [i64, i32, i32] [i64] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortCountsM6Spec a m Q X →
      Γ "full_viv_sort_counts_m6" [i64, i32] [] a m Q X)
    (hReuse : ∀ a m Q X, fullVivReusePrefixM6Spec a m Q X →
      Γ "full_viv_reuse_prefix_m6" [i64, i32, i32] [] a m Q X)
    (hBestImpl : ∀ a m Q X, fullVivBestImpliedM6Spec a m Q X →
      Γ "full_viv_best_implied_m6" [i64, i32] [i32] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hPropIgn : ∀ a m Q X, step13PropagateIgnoreM6Spec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFinish : ∀ a m Q X, fullVivFinishM6Spec a m Q X →
      Γ "full_viv_finish_m6" [i64, i32, i32, .bool, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, step13VivClauseM6Spec a m Q X →
      Func.wp Γ fid11_viv_clause_m6_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, ext0, s, R, rfl, hinv0, href0, hm0, hQ⟩
  have hcfg := hinv0.cfgOk; have hext0 := hinv0.extOk
  have hsp0 := FullM6HdrInvW.sparseW hinv0
  have hmx := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmx har_cap
  have hwf0 := hsp0.2.1.arena.refs_wf cref.toNat href0
  have hcl0 := hsp0.1.core_ok
  have hcr0_nat : (cref.setWidth 64).toNat = cref.toNat := bv32_setWidth64_toNat cref
  have hcr0_lt0 : cref.toNat < s.core.arena.length := by
    have := hcl0.arena_len_arr; have := hcl0.arena_len_le; omega
  have hcr0_bv0 : (cref.setWidth 64).toNat < s.core.arena.length := by omega
  have hcr2_nat : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
  have hcr2_lt0 : cref.toNat + 2 < s.core.arena.length := by
    have := hcl0.arena_len_arr; have := hcl0.arena_len_le; omega
  have hcr2_bv0 : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by omega
  have hm0_f := fullM6HdrMem_focus_full hm0
  have htriv0 := hQ 1#64 ext0 s m0 hinv0 (Nat.le_refl _) rfl rfl rfl (Or.inl rfl)
    (fun h => by cases h) hm0
  unfold Func.wp fid11_viv_clause_m6_body
  fvt_steps
  · exact htriv0
  · exact htriv0
  · exact htriv0
  · have hgb_eq : (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bv0 &&& 0x00080000#32) = 0#32 := by
      c0_bound
    have hng0 : fullArenaClauseGarb s cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      have hg : s.core.arena[cref.toNat]? =
          some (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bv0) := by
        rw [← hcr0_nat, List.getElem?_eq_getElem hcr0_bv0]
      rw [hg, Option.getD_some, hgb_eq]; rfl
    let sz0 := s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bv0
    have hsz0_eq : sz0 = s.core.arena[cref.toNat + 2]'hcr2_lt0 :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hcr2_bv0, hcr2_nat, List.getElem?_eq_getElem hcr2_lt0])
    have hsz0_nat : sz0.toNat = fullArenaClauseSize s cref.toNat := by
      rw [hsz0_eq]; unfold fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem hcr2_lt0, Option.getD_some]
    c0_call hL0Simp
    refine ⟨c, F0, F_cur, s, (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R), rfl, hsp0, href0, hng0,
      hsz0_nat, hm0_f, fun l0r s1 m1 hsp1 hfl1_eq hal1 hrefs1 hrr1 hl0r h20_1 h0_1 hm1 => ?_⟩
    have hfl1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfl1_eq]; exact Nat.le_refl _
    have hinv1 := FullM6HdrInvW.mk_inv hcfg hext0 hsp1
    by_cases hl0 : l0r ≠ 0#64
    · rcases hl0r with rfl | rfl | rfl | rfl
      · exact absurd rfl hl0
      · fvt_steps
        exact hQ 1#64 ext0 s1 _ hinv1 hfl1 hal1 hrefs1 hrr1 (Or.inl rfl) (fun h => by cases h)
          (fullM6HdrMem_unfocus_full hm1)
      · fvt_steps
        exact hQ 2#64 ext0 s1 _ hinv1 hfl1 hal1 hrefs1 hrr1 (Or.inr (Or.inl rfl))
          (fun h => by cases h) (fullM6HdrMem_unfocus_full hm1)
      · fvt_steps
        exact hQ 20#64 ext0 s1 _ hinv1 hfl1 hal1 hrefs1 hrr1 (Or.inr (Or.inr rfl))
          (fun _ => h20_1 rfl) (fullM6HdrMem_unfocus_full hm1)
    obtain rfl : l0r = 0#64 := Classical.not_not.mp hl0
    fvt_steps
    · contradiction
    obtain ⟨href1, hng1⟩ := h0_1 rfl
    have hwf1 := hsp1.2.1.arena.refs_wf cref.toNat href1
    have hcl1 := hsp1.1.core_ok
    have hcr2_lt1 : cref.toNat + 2 < s1.core.arena.length := by
      have := hcl1.arena_len_arr; have := hcl1.arena_len_le; omega
    have hcr2_bv1 : (cref.setWidth 64 + 2#64).toNat < s1.core.arena.length := by omega
    have htriv1 := hQ 1#64 ext0 s1 _ hinv1 hfl1 hal1 hrefs1 hrr1 (Or.inl rfl)
      (fun h => by cases h) (fullM6HdrMem_unfocus_full hm1)
    fvt_steps
    · exact htriv1
    · exact htriv1
    let sz := s1.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bv1
    have hsz_eq : sz = s1.core.arena[cref.toNat + 2]'hcr2_lt1 :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hcr2_bv1, hcr2_nat, List.getElem?_eq_getElem hcr2_lt1])
    have hsz_nat : sz.toNat = fullArenaClauseSize s1 cref.toNat := by
      rw [hsz_eq]; unfold fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem hcr2_lt1, Option.getD_some]
    have hsz_le_cv : sz.toNat ≤ s1.core.cur_vars := by
      have hcv_lt : s1.core.cur_vars < 2 ^ 64 := by have := hcl1.cur_vars_le; omega
      have hc0 : ¬ (BitVec.ofNat 64 s1.core.cur_vars).toNat < (sz.setWidth 64).toNat := by
        c0_bound
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt, bv32_setWidth64_toNat] at hc0
      omega
    have hsz_le_mv : sz.toNat ≤ c.max_vars := by have := hcl1.cur_vars_le; omega
    let s2 : FullState := s1
    have hsp2 : FullSparseInvW c F0 F_cur s2 := hsp1
    have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s1 := rfl
    have href2 : cref.toNat ∈ fullArenaClauseRefs s2 := href1
    have hng2 : fullArenaClauseGarb s2 cref.toNat = false := hng1
    have hsz2 : fullArenaClauseSize s2 cref.toNat = sz.toNat := hsz_nat.symm
    have har2_len : s2.core.arena.length = c.arena_cap := hsp2.1.core_ok.arena_len_arr
    have htmp2_len : s2.core.tmp.length = c.max_vars := hsp2.1.core_ok.tmp_len_arr
    have hbd2 : cref.toNat + 3 + sz.toNat ≤ s2.core.arena.length := by
      have := hwf1.2.2.1; have := hwf1.2.2.2.1; have := hcl1.arena_len_le
      rw [hsz_nat]
      change cref.toNat + 3 + fullArenaClauseSizeCore s1.core cref.toNat ≤ s2.core.arena.length
      omega
    clear hL0Simp hwf0 hcl0 hcr0_lt0 hgb_eq hfl1_eq h20_1 h0_1 hinv0 hinv1 hm0 hm0_f
    fvt_steps
    refine wp_loop_inv (ts := [i32])
      (fun (i, ()) mc => ∃ tmpc : List (BitVec 32),
        i.toNat ≤ sz.toNat ∧ tmpc.length = c.max_vars ∧
        (∀ k < i.toNat, tmpc[k]? = s2.core.arena[cref.toNat + 3 + k]?) ∧
        (FullMem c { s2 with core := { s2.core with tmp := tmpc } } ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) mc)
      (fun (i, ()) _ => sz.toNat - i.toNat)
      (fun Jc hJc => by
        fvt_steps
        exact hJc (0#32, ()) _ ⟨s2.core.tmp, Nat.zero_le _, htmp2_len,
          fun _ hk => by simp at hk, hm1⟩)
      (fun Jc ⟨i, ⟨⟩⟩ mc ⟨tmpc, hi_le, htc_len, hcp, hmc⟩ ihc => ?_)
    fvt_steps
    · have hi_lt : i.toNat < sz.toNat := by c0_bound
      have hidx_nat : (cref.setWidth 64 + 3 + i.setWidth 64).toNat =
          cref.toNat + 3 + i.toNat := by bv_omega
      have hi64_nat : (i.setWidth 64).toNat = i.toNat := bv32_setWidth64_toNat i
      have hi_lt_ar : (cref.setWidth 64 + 3 + i.setWidth 64).toNat < s2.core.arena.length := by
        omega
      have hi_lt_tmp : i.toNat < tmpc.length := by omega
      have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      fvt_steps
      let tmpc' := tmpc.set i.toNat (s2.core.arena[cref.toNat + 3 + i.toNat]'(by omega))
      have har_eq : s2.core.arena[(cref.setWidth 64 + 3 + i.setWidth 64).toNat]'hi_lt_ar =
          s2.core.arena[cref.toNat + 3 + i.toNat]'(by omega) := Option.some.inj (by
        rw [← List.getElem?_eq_getElem hi_lt_ar, hidx_nat, List.getElem?_eq_getElem (by omega)])
      refine ihc (i + 1#32, ()) _ (by dsimp only; omega)
        ⟨tmpc', by omega, by simp [tmpc', htc_len], fun k hk => ?_, ?_⟩
      · rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
        · dsimp only [tmpc']; rw [List.getElem?_set_ne (by omega)]; exact hcp k hk'
        · dsimp only [tmpc']
          rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · simpa only [tmpc', hi64_nat, har_eq] using hm
    · have hi_eq : i.toNat = sz.toNat := by dsimp only [sz] at hi_le ⊢; c0_bound
      rw [hi_eq] at hcp
      have htmpc_lits_lt : ∀ k < sz.toNat, (tmpc[k]?.getD 0#32).toNat < 2 * c.max_vars := by
        intro k hk
        have hmem : (tmpc[k]?.getD 0#32).toNat ∈ fullArenaClauseLits s2 cref.toNat := by
          have := (vivTmp_mem_of_perm (by omega)
            (vivCopy_perm_lits (by omega) hbd2 hcp
              (List.Perm.refl (tmpc.take sz.toNat)) (by omega))).1 k hk
          simpa [fullArenaClauseLits, fullArenaClauseLitsCore, hsz2] using this
        have := hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 _ hmem
        have := hsp2.1.core_ok.cur_vars_le; omega
      c0_call hSort
      refine ⟨c, { s2 with core := { s2.core with tmp := tmpc } },
        (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R), rfl,
        ⟨{ hsp2.1.core_ok with tmp_len_arr := htc_len }, hsp2.1.scratch_ok⟩,
        hsz_le_mv, htmpc_lits_lt, hmc, fun tmp4 m4 htmp4_len hperm4 _ hm4 => ?_⟩
      have hperm_lits4 : ((tmp4.take sz.toNat).map BitVec.toNat).Perm
          (fullArenaClauseLits s2 cref.toNat) := by
        have := vivCopy_perm_lits (by omega) hbd2 hcp hperm4 (by omega)
        simpa [fullArenaClauseLits, fullArenaClauseLitsCore, hsz2] using this
      let s4 : FullState := { s2 with core := { s2.core with tmp := tmp4 } }
      have hsp4 : FullSparseInvW c F0 F_cur s4 := FullVivTop.FullSparseInvW.with_tmp hsp2 htmp4_len
      have htmp4_lt_cv : ∀ k < sz.toNat, (tmp4[k]?.getD 0#32).toNat < 2 * s4.core.cur_vars := by
        intro k hk
        have hmem := (vivTmp_mem_of_perm (by omega) hperm_lits4).1 k hk
        exact hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 _ hmem
      fvt_steps
      c0_call hReuse
      refine ⟨c, F0, F_cur, s4, (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R), rfl, hsp4,
        hsz_le_mv, htmp4_lt_cv, hm4,
        fun s4r m4r hsp4r hcv4r har4r hal4r hpr4r hfl4r htmp4r hrr4r hm4r => ?_⟩
      let tmp5 := s4r.core.tmp
      let lits2 := fullArenaClauseLits s2 cref.toNat
      have hperm_lits5 : ((tmp5.take sz.toNat).map BitVec.toNat).Perm lits2 := by
        dsimp only [tmp5, lits2]; rw [htmp4r]; exact hperm_lits4
      obtain ⟨htmp5_mem, hlits5_inv⟩ := vivTmp_mem_of_perm
        (by rw [show tmp5.length = c.max_vars from hsp4r.1.core_ok.tmp_len_arr]; omega)
        hperm_lits5
      fvt_to_group
      let s5 : FullState :=
        { s4r with core := { s4r.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } }
      obtain ⟨hsp5, hfl5, hal5, hrefs5, hrr5, href5, hng5, hsz5, hperm5, hlits2_lt⟩ :=
        s6a_viv_post_reuse_facts (s5 := s5) (lits2 := lits2) rfl rfl hsp2 hsp4r
          hcv4r har4r hal4r hfl4r hrr4r hfl1 hal1 hrefs1 hrr1 href2 hng2 hsz2
      have hlits2_mem : ∀ k < sz.toNat, (tmp5[k]?.getD 0#32).toNat ∈ lits2 := htmp5_mem
      have hlits2_inv : ∀ l ∈ lits2, ∃ k < sz.toNat, (tmp5[k]?.getD 0#32).toNat = l := hlits5_inv
      have hct5 : s5.core.confl_type = 0#64 := rfl
      have htmp5 : s5.core.tmp = tmp5 := rfl
      have htmp5_len : tmp5.length = c.max_vars := hsp4r.1.core_ok.tmp_len_arr
      have hm5 : (FullMem c s5 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) m := hm
      clear_value s5 s4 s2 tmp5 lits2
      clear hSort hReuse har_cap hm hwf1 hperm4 hperm_lits4 htmp5_mem hlits5_inv hsp4 hsp2
        s4 hrefs2 href2 hng2 hsz2 har2_len htmp2_len hbd2 htmpc_lits_lt hsp1
        hfl1 hal1 hrefs1 hrr1 href1 hng1 hcl1 hsz_nat hsz_le_cv hsp0 href0
        hng0 hm1 hm4 hsp4r hcv4r har4r hal4r hpr4r hfl4r htmp4r hrr4r htmp4_lt_cv
      try clear hi_eq ihc hmc hcp htc_len hi_le tmpc mc Jc i s2 s4r
      refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32])
        (fun (i, confl, implied, ()) mb => ∃ (extb : List (BitVec 64)) (sb : FullState),
          M6HdrExtOk extb ∧ FullSparseInvW c F0 F_cur sb ∧
          sb.core.cur_vars = s5.core.cur_vars ∧ sb.core.arena_len = s5.core.arena_len ∧
          sb.core.probing = s5.core.probing ∧ sb.core.tmp = tmp5 ∧
          sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
          sb.scratch.red_refs = s.scratch.red_refs ∧
          cref.toNat ∈ fullArenaClauseRefs sb ∧
          fullArenaClauseGarb sb cref.toNat = false ∧
          fullArenaClauseSize sb cref.toNat = sz.toNat ∧
          (fullArenaClauseLits sb cref.toNat).Perm lits2 ∧
          (confl = true → FullConflictOkW F_cur sb) ∧
          (confl = false → implied ≠ 0xFFFFFFFF#32 →
            implied.toNat < 2 * sb.core.cur_vars ∧
            sb.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
          (confl = false → implied = 0xFFFFFFFF#32 → i = sz →
            sb.core.confl_type = 0#64 ∧
            ∀ l ∈ fullArenaClauseLits sb cref.toNat, sb.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
          (FullMem c sb ⋆ (m6ExtMem (m6ExtAddr c.hdr) extb ⋆ R)) mb)
        (fun rem (i, ()) mp => ∃ (extp : List (BitVec 64)) (sp : FullState),
          i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat ∧
          M6HdrExtOk extp ∧ FullSparseInvW c F0 F_cur sp ∧
          sp.core.cur_vars = s5.core.cur_vars ∧ sp.core.arena_len = s5.core.arena_len ∧
          sp.core.probing = s5.core.probing ∧ sp.core.tmp = tmp5 ∧
          sp.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          fullArenaClauseRefs sp = fullArenaClauseRefs s ∧
          sp.scratch.red_refs = s.scratch.red_refs ∧
          cref.toNat ∈ fullArenaClauseRefs sp ∧
          fullArenaClauseGarb sp cref.toNat = false ∧
          fullArenaClauseSize sp cref.toNat = sz.toNat ∧
          (fullArenaClauseLits sp cref.toNat).Perm lits2 ∧
          sp.core.confl_type = 0#64 ∧
          (∀ k < i.toNat, sp.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
          (FullMem c sp ⋆ (m6ExtMem (m6ExtAddr c.hdr) extp ⋆ R)) mp)
        ?_ ?_ ?_
      · rintro _ ⟨i_b, confl_b, impl_b, ⟨⟩⟩ mb
          ⟨extb, sb, hextb, hspb, _, halb, _, htmpb, hflb, hrefsb, hrrb, hrefb, hngb, hszb, hpermb,
           hcokb, himplb, hfalb, hmb⟩
        fvt_steps
        c0_call hFinish
        refine ⟨c, F0, F_cur, sb, (m6ExtMem (m6ExtAddr c.hdr) extb ⋆ R), rfl, hspb, hsz_le_mv,
          hrefb, hngb, hszb, (by rw [htmpb]; exact hperm_lits5.trans hpermb.symm),
          hcokb, himplb,
          fun hc hi hall => hfalb hc hi (by
            revert hall; cases Decidable.em (i_b = sz) <;> simp [*]),
          hmb,
          fun r_f s_f m_f hspf hflf half hrefsf hrrf hrf h20f hm_f => ?_⟩
        clear hFinish hBestImpl hAssign hPropIgn hBacktrack hsz_le_mv hspb hcokb himplb hfalb hmb
        have hinv_f : FullM6HdrInvW c F0 F_cur extb s_f := FullM6HdrInvW.mk_inv hcfg hextb hspf
        have href_f : cref.toNat ∈ fullArenaClauseRefs s_f := hrefsf ▸ hrefb
        have hwf_f := hspf.2.1.arena.refs_wf cref.toNat href_f
        have hcr_f_lt : cref.toNat < s_f.core.arena.length := by
          have := hspf.1.core_ok.arena_len_arr; have := hspf.1.core_ok.arena_len_le; omega
        have hcr_f_bv : (cref.setWidth 64).toNat < s_f.core.arena.length := by omega
        have hm_f_foc := hm_f
        fvt_steps
        · obtain ⟨hinv_v, hrefs_v⟩ := s6a_viv_clr_hdr_ok hinv_f href_f hcr_f_lt
          let hdr_v := (s_f.core.arena[cref.toNat]'hcr_f_lt) &&& ~~~0x00100000#32
          let s_v : FullState :=
            { s_f with core := { s_f.core with arena := s_f.core.arena.set cref.toNat hdr_v } }
          have hm_v : (FullMem c s_v ⋆ (m6ExtMem (m6ExtAddr c.hdr) extb ⋆ R)) m := by
            dsimp only [s_v, hdr_v]
            rw [← show (1048576#32 : BitVec 32) = 0x00100000#32 from rfl,
              ← show (1048576 : BitVec 32) = 1048576#32 from rfl]
            simpa only [hcr0_nat] using hm
          exact hQ r_f extb _ m hinv_v (Nat.le_trans hflf hflb)
            (half.trans (halb.trans hal5)) (hrefs_v.trans (hrefsf.trans hrefsb))
            (hrrf.trans hrrb) hrf h20f (fullM6HdrMem_unfocus_full hm_v)
        all_goals
          exact hQ r_f extb s_f m_f hinv_f (Nat.le_trans hflf hflb)
            (half.trans (halb.trans hal5)) (hrefsf.trans hrefsb) (hrrf.trans hrrb) hrf h20f
            (fullM6HdrMem_unfocus_full hm_f)
      · intro B L rem ⟨i, ⟨⟩⟩ mp hB hL
          ⟨extp, sp, hi_le, hrem, hextp, hspp, hcvp, halp, hprp, htmpp, hflp, hrefsp, hrrp,
           hrefp, hngp, hszp, hpermp, hct0, hfalp, hmp⟩
        clear hFinish
        fvt_steps
        · have hi_lt : i.toNat < sz.toNat := by c0_bound
          have hi_ne_sz : i ≠ sz := fun heq => by rw [heq] at hi_lt; exact Nat.lt_irrefl _ hi_lt
          have hsp_len := hspp.1.core_ok
          have hi_lt_tmp : i.toNat < sp.core.tmp.length := by rw [hsp_len.tmp_len_arr]; omega
          have hlit_lt_cv : (tmp5[i.toNat]?.getD 0#32).toNat < 2 * sp.core.cur_vars := by
            rw [hcvp]; exact hlits2_lt _ (hlits2_mem i.toNat hi_lt)
          have hlit_lt_vals : (tmp5[i.toNat]?.getD 0#32).toNat < sp.core.vals.length := by
            rw [hsp_len.vals_len]; have := hsp_len.cur_vars_le; omega
          have hi64_nat : (i.setWidth 64).toNat = i.toNat := bv32_setWidth64_toNat i
          have hi_lt_tmp64 : (i.setWidth 64).toNat < sp.core.tmp.length := by
            rw [hi64_nat]; exact hi_lt_tmp
          have htmp_i_eq : sp.core.tmp[(i.setWidth 64).toNat]'hi_lt_tmp64 =
              tmp5[i.toNat]?.getD 0#32 := Option.some.inj (by
            rw [← List.getElem?_eq_getElem hi_lt_tmp64, htmpp, hi64_nat,
              List.getElem?_eq_getElem (by omega), Option.getD_some])
          have htmp_i_lt' : (sp.core.tmp[(i.setWidth 64).toNat].setWidth 64).toNat <
              sp.core.vals.length := by rw [bv32_setWidth64_toNat, htmp_i_eq]; exact hlit_lt_vals
          let lit := sp.core.tmp[i.toNat]'hi_lt_tmp
          have hlit_eq : lit = tmp5[i.toNat]?.getD 0#32 := Option.some.inj (by
            dsimp only [lit]
            rw [← List.getElem?_eq_getElem hi_lt_tmp, htmpp,
              List.getElem?_eq_getElem (by omega), Option.getD_some])
          have hlit_i64 : sp.core.tmp[(i.setWidth 64).toNat]'hi_lt_tmp64 = lit := by
            rw [htmp_i_eq, hlit_eq]
          have hlit_lt : lit.toNat < 2 * sp.core.cur_vars := by rw [hlit_eq]; exact hlit_lt_cv
          have hlit_lt_vals' : lit.toNat < sp.core.vals.length := by
            rw [hlit_eq]; exact hlit_lt_vals
          fvt_to_group
          · have htmp_sp_lt : ∀ k < sz.toNat,
                (sp.core.tmp[k]?.getD 0#32).toNat < 2 * sp.core.cur_vars := fun k hk => by
              rw [htmpp, hcvp]; exact hlits2_lt _ (hlits2_mem k hk)
            c0_call hBestImpl
            refine ⟨c, F0, F_cur, sp, (m6ExtMem (m6ExtAddr c.hdr) extp ⋆ R), rfl, hspp,
              hsz_le_mv, htmp_sp_lt, hmp, fun bi hbi => ?_⟩
            fvt_steps
            exact hB (i, false, bi, ()) mp ⟨extp, sp, hextp, hspp, hcvp, halp, hprp, htmpp, hflp,
              hrefsp, hrrp, hrefp, hngp, hszp, hpermp, (fun h => by cases h),
              fun _ hne => hbi hne, fun _ _ heq => absurd heq hi_ne_sz, hmp⟩
          · refine wp_join_group (ts := [.bool, i32])
              (fun (confl_j, _) m_jn => ∃ (ext_jn : List (BitVec 64)) (s_jn : FullState),
                M6HdrExtOk ext_jn ∧ FullSparseInvW c F0 F_cur s_jn ∧
                s_jn.core.cur_vars = s5.core.cur_vars ∧ s_jn.core.arena_len = s5.core.arena_len ∧
                s_jn.core.probing = s5.core.probing ∧ s_jn.core.tmp = tmp5 ∧
                s_jn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                fullArenaClauseRefs s_jn = fullArenaClauseRefs s ∧
                s_jn.scratch.red_refs = s.scratch.red_refs ∧
                cref.toNat ∈ fullArenaClauseRefs s_jn ∧
                fullArenaClauseGarb s_jn cref.toNat = false ∧
                fullArenaClauseSize s_jn cref.toNat = sz.toNat ∧
                (fullArenaClauseLits s_jn cref.toNat).Perm lits2 ∧
                s_jn.core.confl_type = 0#64 ∧
                (∀ k < (i + 1#32).toNat,
                  s_jn.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
                (FullMem c s_jn ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext_jn ⋆ R)) m_jn) ?_ ?_
            · rintro _ ⟨confl_j, impl_j, ⟨⟩⟩ m_jn ⟨ext_jn, s_jn, hext_jn, hsp_jn, hcv_jn, hal_jn,
                hpr_jn, htmp_jn, hfl_jn, hrefs_jn, hrr_jn, href_jn, hng_jn, hsz_jn, hperm_jn,
                hct_jn, hfal_jn, hm_jn⟩
              have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
              fvt_steps
              exact hL (sz.toNat - (i + 1#32).toNat) (i + 1#32, ()) _
                (by (try dsimp only); (try rw [hi1_nat]); omega)
                ⟨ext_jn, s_jn, by omega, rfl, hext_jn, hsp_jn, hcv_jn, hal_jn, hpr_jn, htmp_jn,
                 hfl_jn, hrefs_jn, hrr_jn, href_jn, hng_jn, hsz_jn,
                 hperm_jn, hct_jn, hfal_jn, hm_jn⟩
            · intro J_jn hJ_jn
              fvt_steps
              · exfalso
                have hlv0 : sp.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                  rw [List.getElem?_eq_getElem hlit_lt_vals', Option.getD_some]
                  exact (bv8_sext32_eq0_iff _).mp (by first | assumption | c0_bound)
                have hnlvl_le := (s6a_viv_assign_prep hspp hlit_lt hlv0).2.1
                have hc0 : c.max_vars % 2 ^ 64 <
                    (sp.core.cur_level + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := by assumption
                have h1n : BitVec.toNat (1 : BitVec 64) = 1 := rfl
                rw [h1n] at hc0; omega
              · have hlv0 : sp.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                  rw [List.getElem?_eq_getElem hlit_lt_vals', Option.getD_some]
                  exact (bv8_sext32_eq0_iff _).mp (by first | assumption | c0_bound)
                obtain ⟨hte_lt, hnlvl_le, hlen_pre, hnot_guard⟩ :=
                  s6a_viv_assign_prep hspp hlit_lt hlv0
                have hnlvl_nat : (BitVec.ofNat 64 sp.core.cur_level + 1).toNat =
                    sp.core.cur_level + 1 := by bv_omega
                have hnlvl_lt_ft : (BitVec.ofNat 64 sp.core.cur_level + 1).toNat <
                    sp.core.frame_trail.length := by rw [hnlvl_nat, hsp_len.frame_trail_len]; omega
                have hnlvl_lt_fd : (BitVec.ofNat 64 sp.core.cur_level + 1).toNat <
                    sp.core.frame_dec.length := by rw [hnlvl_nat, hsp_len.frame_dec_len]; omega
                fvt_steps
                let nlvl := sp.core.cur_level + 1
                let dlit := lit ^^^ 1#32
                let ftrl' := sp.core.frame_trail.set nlvl (BitVec.ofNat 32 sp.core.trail_end)
                let fdec' := sp.core.frame_dec.set nlvl dlit
                let s_pre : FullState :=
                  { sp with core :=
                    { sp.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl } }
                have hte_bv : BitVec.setWidth 32 (BitVec.ofNat 64 sp.core.trail_end) =
                    BitVec.ofNat 32 sp.core.trail_end := by apply BitVec.eq_of_toNat_eq; simp
                rw [hlit_i64]
                c0_call hAssign
                refine ⟨c, s_pre, (m6ExtMem (m6ExtAddr c.hdr) extp ⋆ R), rfl, hlen_pre,
                  by dsimp [s_pre, nlvl]; omega,
                  (by simp only [s_pre, nlvl, ftrl', fdec', ← hnlvl_nat, ← hte_bv]
                      exact (by assumption)),
                  ?_⟩
                by_cases hguard : s_pre.core.cur_vars ≤ (lit ^^^ 1).toNat / 2 ∨
                    c.max_vars ≤ s_pre.core.trail_end ∨
                    s_pre.core.vals[(lit ^^^ 1).toNat]?.getD 0#8 ≠ 0#8
                · exact absurd hguard hnot_guard
                simp only [hguard, ↓reduceIte]
                intro flags' unass' phases' m_as hfll' hphl' hm_as
                have hnlvl_ne0 : nlvl ≠ 0 := by omega
                simp only [show s_pre.core.cur_level ≠ 0 from hnlvl_ne0, ↓reduceIte] at hm_as ⊢
                obtain ⟨_, hsp_as, hfal_as, hlit_as_ff⟩ :=
                  vivDecideAssign_preserves_sparseW hspp hlit_lt hlv0 hfll' hphl'
                let s_as : FullState :=
                  { sp with
                    core :=
                      { sp.core with
                        vals := (sp.core.vals.set dlit.toNat 1#8).set (dlit.toNat ^^^ 1) 0xFF#8
                        flags := flags',
                        lvl := sp.core.lvl.set (dlit.toNat / 2) (BitVec.ofNat 32 nlvl),
                        rsns := sp.core.rsns.set (dlit.toNat / 2) 0xFFFFFFFF#32,
                        trl := sp.core.trl.set sp.core.trail_end dlit,
                        trail_pos := sp.core.trail_pos.set (dlit.toNat / 2)
                          (BitVec.ofNat 32 sp.core.trail_end),
                        frame_trail := ftrl', frame_dec := fdec',
                        trail_end := sp.core.trail_end + 1, cur_level := nlvl,
                        unassigned := unass' }
                    scratch := { sp.scratch with phases := phases' } }
                clear_value s_as
                try clear hm_as hlen_pre hguard hnot_guard
                fvt_steps
                exact s6a_viv_clause_prop_step13 Γ hPropIgn hBacktrack hBestImpl hcfg hextp
                  hQ hB hJ_jn hsp_as hsz_le_mv hcvp rfl halp rfl hprp rfl hflp rfl hal5
                  hrefsp rfl hrrp hrefp hngp hszp hpermp rfl hct0 htmpp hlits2_lt hlits2_mem
                  hi_lt hlit_eq hlit_lt hfalp hfal_as hlit_as_ff hm_as
              · have hlv_ff := s6a_viv_vals_ff_of_ne hspp hlit_lt hlit_lt_vals'
                  (by assumption) (by assumption)
                have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                fvt_steps
                exact hJ_jn _ _ ⟨extp, sp, hextp, hspp, hcvp, halp, hprp, htmpp, hflp, hrefsp, hrrp,
                  hrefp, hngp, hszp, hpermp, hct0, fun k hk => by
                    rw [hi1_nat] at hk
                    rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
                    · exact hfalp k hk'
                    · rw [← hlit_eq]; exact hlv_ff,
                  hmp⟩
        · have hi_eq : i.toNat = sz.toNat := by dsimp only [sz] at hi_le ⊢; c0_bound
          have hfal_all : ∀ l ∈ fullArenaClauseLits sp cref.toNat,
              sp.core.vals[l]?.getD 0#8 = 0xFF#8 := by
            intro l hl
            obtain ⟨k, hk, hget⟩ := hlits2_inv l (hpermp.mem_iff.mp hl)
            rw [← hget]; exact hfalp k (by omega)
          fvt_steps
          exact hB (i, false, 0xFFFFFFFF#32, ()) _ ⟨extp, sp, hextp, hspp, hcvp, halp, hprp,
            htmpp, hflp, hrefsp, hrrp, hrefp, hngp, hszp, hpermp, (fun h => by cases h),
            fun _ h => absurd rfl h, fun _ _ _ => ⟨hct0, hfal_all⟩, hmp⟩
      · intro B L _ hL
        fvt_steps
        exact hL sz.toNat (0#32, ()) _ ⟨ext0, s5, Nat.zero_le _,
          by rw [BitVec.toNat_ofNat]; simp, hext0, hsp5, rfl, rfl,
          rfl, htmp5, hfl5, hrefs5, hrr5, href5, hng5, hsz5, hperm5, hct5,
          fun _ hk => by simp at hk, hm5⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
