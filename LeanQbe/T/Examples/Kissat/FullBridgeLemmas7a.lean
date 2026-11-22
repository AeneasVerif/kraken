module

public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Proofs — Vivification Drivers (`Stage 4`, Part 7a)

Bridges the `2` top-level vivification driver functions onto canonical `FullSpec` contracts:
- `full_viv_clause_bridge_wp` (`full_viv_clause`, adapting `full_viv_clause_wp` to canonical
  `fullAssignSpec` which omits the redundant `s'.LengthsOk c` hypothesis on `full_assign`)
- `full_vivify_bridge_wp` (`full_vivify`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

namespace FullVivTopSpecs

section VivClauseCanonAssign

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullVivTopTactics FullVivTop
open scoped FullArenaTactics FullVivTopTactics

private theorem viv_clause_prop_step (Γ : Env)
    (hPropIgn : ∀ args m Q X, fullPropagateIgnoreSpec args m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] args m Q X)
    (hBacktrack : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s5 sp s_as : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {B : Cont [i32, .bool, i32]} {J_jn : Cont [.bool]}
    {cref i lit sz : BitVec 32} {tmp4 : List (BitVec 32)} {lits2 : List Nat} {m_as : Mem 64}
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      r = 1#64 ∨ r = 2#64 ∨ r = 20#64 → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hB : ∀ (r : Tup Val [i32, .bool, i32]) (m' : Mem 64),
      (match r with
      | (ib, confl, implied, ()) => ∃ sb : FullState,
        FullSparseInvW c F0 F_cur sb ∧
        sb.core.cur_vars = s5.core.cur_vars ∧ sb.core.arena_len = s5.core.arena_len ∧
        sb.core.probing = s5.core.probing ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
        cref.toNat ∈ fullArenaClauseRefs sb ∧
        fullArenaClauseGarb sb cref.toNat = false ∧
        fullArenaClauseSize sb cref.toNat = sz.toNat ∧
        (confl = true ∨ implied ≠ 0xFFFFFFFF#32 ∨ ib.toNat = sz.toNat) ∧
        (confl = true → FullConflictOkW F_cur sb) ∧
        (confl = false → implied ≠ 0xFFFFFFFF#32 →
          implied.toNat < 2 * sb.core.cur_vars ∧
          sb.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
        (confl = false → implied = 0xFFFFFFFF#32 →
          sb.core.confl_type = 0#64 ∧
          ∀ l ∈ fullArenaClauseLits sb cref.toNat, sb.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (FullMem c sb ⋆ R) m') → B r m')
    (hJ_jn : ∀ (xs : Tup Val [.bool]) (m : Mem 64),
      (match xs with
      | (_, ()) => ∃ s_jn : FullState,
        FullSparseInvW c F0 F_cur s_jn ∧
        s_jn.core.cur_vars = s5.core.cur_vars ∧
        s_jn.core.arena_len = s5.core.arena_len ∧
        s_jn.core.probing = s5.core.probing ∧ s_jn.core.tmp = tmp4 ∧
        s_jn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs s_jn = fullArenaClauseRefs s ∧
        cref.toNat ∈ fullArenaClauseRefs s_jn ∧
        fullArenaClauseGarb s_jn cref.toNat = false ∧
        fullArenaClauseSize s_jn cref.toNat = sz.toNat ∧
        (fullArenaClauseLits s_jn cref.toNat).Perm lits2 ∧
        s_jn.core.confl_type = 0#64 ∧
        (∀ k < (i + 1#32).toNat,
          s_jn.core.vals[(tmp4[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
        (FullMem c s_jn ⋆ R) m) → J_jn xs m)
    (hsp_as : FullSparseInvW c F0 F_cur s_as)
    (hcvp : sp.core.cur_vars = s5.core.cur_vars)
    (hcv_as : s_as.core.cur_vars = sp.core.cur_vars)
    (halp : sp.core.arena_len = s5.core.arena_len)
    (hal_as : s_as.core.arena_len = sp.core.arena_len)
    (hprp : sp.core.probing = s5.core.probing)
    (hpr_as : s_as.core.probing = sp.core.probing)
    (hflp : sp.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hfl_as : s_as.core.fuel = sp.core.fuel)
    (hal5 : s5.core.arena_len = s.core.arena_len)
    (hrefsp : fullArenaClauseRefs sp = fullArenaClauseRefs s)
    (hrefs_as : fullArenaClauseRefs s_as = fullArenaClauseRefs sp)
    (hrefp : cref.toNat ∈ fullArenaClauseRefs sp)
    (hng_as : fullArenaClauseGarb s_as cref.toNat = false)
    (hsz_as : fullArenaClauseSize s_as cref.toNat = sz.toNat)
    (hpermp : (fullArenaClauseLits sp cref.toNat).Perm lits2)
    (hlits_as : fullArenaClauseLits s_as cref.toNat = fullArenaClauseLits sp cref.toNat)
    (hct_as : s_as.core.confl_type = 0#64)
    (htmp_as : s_as.core.tmp = tmp4)
    (hlits2_lt : ∀ l ∈ lits2, l < 2 * s5.core.cur_vars)
    (hlits2_mem : ∀ k < sz.toNat, (tmp4[k]?.getD 0#32).toNat ∈ lits2)
    (hi_lt : i.toNat < sz.toNat)
    (hlit_eq : lit = tmp4[i.toNat]?.getD 0#32)
    (hlit_lt : lit.toNat < 2 * sp.core.cur_vars)
    (hfalp : ∀ k < i.toNat, sp.core.vals[(tmp4[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (hfal_as : ∀ l < 2 * sp.core.cur_vars,
      sp.core.vals[l]?.getD 0#8 = 0xFF#8 → s_as.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hlit_as_ff : s_as.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8)
    (hm_as : (FullMem c s_as ⋆ R) m_as) :
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
              (Expr.jump J_jn (Arg.imm false, ()))))
      m_as := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s_as, R, rfl, hsp_as.1, hsp_as.2.1, hsp_as.2.2.2.1,
    hsp_as.2.2.2.2.2, hm_as,
    fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
      wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
      sc_p m_p hlen_p hw_p hnd_p hpres_p hte_p hfl_p hrefs_p har_props_p htrl_p
      hpr_disj hpr0 hpr1 hpr2 _ hm_p => ?_⟩
  let s_p : FullState :=
    { s_as with
      core := { s_as.core with
        vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
        trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
        unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
        arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
        fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
        confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
      scratch := sc_p }
  have hsp_p : FullSparseInvW c F0 F_cur s_p :=
    fullSparseInvW_of_prop_state hsp_as hlen_p hw_p hnd_p hpres_p
      (fun r hr => hrefs_p ▸ hr)
  have hcv_p : s_p.core.cur_vars = s5.core.cur_vars := hcv_as.trans hcvp
  have hal_p : s_p.core.arena_len = s5.core.arena_len := hal_as.trans halp
  have hpr_p : s_p.core.probing = s5.core.probing := hpr_as.trans hprp
  have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat :=
    Nat.le_trans hfl_p (hfl_as ▸ hflp)
  have hrefs_p' : fullArenaClauseRefs s_p = fullArenaClauseRefs s :=
    hrefs_p.trans (hrefs_as.trans hrefsp)
  have href_p : cref.toNat ∈ fullArenaClauseRefs s_p := hrefs_p ▸ hrefs_as ▸ hrefp
  have hng_p : fullArenaClauseGarb s_p cref.toNat = false :=
    (har_props_p cref.toNat (hrefs_as ▸ hrefp)).2.1.trans hng_as
  have hsz_p : fullArenaClauseSize s_p cref.toNat = sz.toNat :=
    (har_props_p cref.toNat (hrefs_as ▸ hrefp)).1.trans hsz_as
  have hlits_p : (fullArenaClauseLits s_p cref.toNat).Perm lits2 :=
    (har_props_p cref.toNat (hrefs_as ▸ hrefp)).2.2.trans (hlits_as ▸ hpermp)
  have hm_p' : (FullMem c s_p ⋆ R) m_p := hm_p
  have hcv_p_as : s_p.core.cur_vars = s_as.core.cur_vars := rfl
  have htmp_p : s_p.core.tmp = tmp4 := htmp_as
  have hte_p' : s_as.core.trail_end ≤ s_p.core.trail_end := hte_p
  have htrl_p' : ∀ idx < s_as.core.trail_end, s_p.core.trl[idx]? = s_as.core.trl[idx]? :=
    htrl_p
  have hcok_p_fn : pr = 1#64 → FullConflictOkW F_cur s_p := fun h => (hpr1 h).2.2
  have hct_p0_fn : pr = 0#64 → s_p.core.confl_type = 0#64 :=
    fun h => (hpr0 h).2.2.1.trans hct_as
  clear_value s_p
  clear hm_p hm_as
  fvt_steps
  · -- `pr == 2ULL`: `full_backtrack(h, 0ULL); return 2ULL;`
    have hpr_eq2 : pr = 2#64 := by c0_bound
    have hp_cl_le := hsp_p.2.1.cur_level_le
    have hp_te_le := hsp_p.1.core_ok.trail_end_le
    have hp_cv_le := hsp_p.1.core_ok.cur_vars_le
    have hp_cl_lt : s_p.core.cur_level < 2 ^ 64 := by omega
    c0_call hBacktrack
    refine ⟨c, s_p, R, rfl, hsp_p.1, hp_cl_lt,
      (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro; omega),
      hsp_p.2.1.trail_lits_lt, hm_p',
      fun vals_b lvl_b rsns_b trl_b tp_b te_b prop_b cl_b unass_b sc_b m_b
        hlen_b hte_b hprop_b hcl_b hpres_b htrl_b hw_b _ hm_b => ?_⟩
    have hcl_b0 : cl_b = 0 := by rw [hcl_b]; simp
    have hsp_b : FullSparseInvW c F0 F_cur _ :=
      FullSparseInvW.of_backtrack hsp_p (Nat.zero_le _) hlen_b hpres_b
        (hw_b F0 F_cur hsp_p.2.1 (Nat.zero_le _))
    fvt_steps
    exact hQ 2#64 _ m_b hsp_b hcl_b0 hfl_p' (hal_p.trans hal5) hrefs_p'
      (Or.inr (Or.inl rfl)) (fun h => by cases h) hm_b
  · -- `pr == 1ULL`: conflict! `confl = true; break;`
    have hpr_eq1 : pr = 1#64 := by c0_bound
    have hcok_p := hcok_p_fn hpr_eq1
    fvt_steps
    exact hB (i, true, 0xFFFFFFFF#32, ()) _ ⟨s_p, hsp_p, hcv_p, hal_p, hpr_p,
      hfl_p', hrefs_p', href_p, hng_p, hsz_p, Or.inl rfl, fun _ => hcok_p,
      (fun h => by cases h), (fun h => by cases h), hm_p'⟩
  · -- `pr == 0ULL`: join to `i + 1`
    have hpr_eq0 : pr = 0#64 := by
      rcases hpr_disj with rfl | rfl | rfl
      · rfl
      · exact absurd rfl (by c0_bound)
      · exact absurd rfl (by c0_bound)
    have hct_p0 : s_p.core.confl_type = 0#64 := hct_p0_fn hpr_eq0
    have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
    have hfal_p1 : ∀ k < (i + 1#32).toNat,
        s_p.core.vals[(tmp4[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
      intro k hk
      rw [hi1_nat] at hk
      rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
      · have hk_lt_sp : (tmp4[k]?.getD 0#32).toNat < 2 * sp.core.cur_vars := by
          rw [hcvp]
          exact hlits2_lt _ (hlits2_mem k (by omega))
        have hk_lt_as : (tmp4[k]?.getD 0#32).toNat < 2 * s_as.core.cur_vars := by
          rw [hcv_as]; exact hk_lt_sp
        have hk_as : s_as.core.vals[(tmp4[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 :=
          hfal_as _ hk_lt_sp (hfalp k hk')
        exact falsified_preserved_of_trailExt hsp_as.2.1 hsp_p.2.1 hcv_p_as
          hte_p' htrl_p' hk_lt_as hk_as
      · rw [← hlit_eq]
        have hlit_lt_as : lit.toNat < 2 * s_as.core.cur_vars := by
          rw [hcv_as]; exact hlit_lt
        exact falsified_preserved_of_trailExt hsp_as.2.1 hsp_p.2.1 hcv_p_as
          hte_p' htrl_p' hlit_lt_as hlit_as_ff
    fvt_steps
    exact hJ_jn _ _ ⟨s_p, hsp_p, hcv_p, hal_p, hpr_p, htmp_p, hfl_p', hrefs_p',
      href_p, hng_p, hsz_p, hlits_p, hct_p0, hfal_p1, hm_p'⟩

/-! ## 1. `Func.wp` Proof #1 (`full_viv_clause`) -/

/-- **#1 (`full_viv_clause`)**: vivifies a single non-garbage arena clause `cref` under
`FullSparseInvW`, returning `1` (keep/strengthened), `2` (OOM/fuel exhaustion), or `20`
(`F0.Unsat`), always leaving `cur_level = 0` and preserving `arena_len` and
`fullArenaClauseRefs`. -/
private theorem full_viv_clause_canon_assign_wp (Γ : Env)
    (hSimplify : ∀ args m Q X, fullVivSimplifySpec args m Q X →
      Γ "full_viv_simplify" [i64, i32] [i64] args m Q X)
    (hSort : ∀ args m Q X, fullVivSortLitsSpec args m Q X →
      Γ "full_viv_sort_lits" [i64, i64, i32] [] args m Q X)
    (hAssign : ∀ args m Q X, _root_.LeanQbe.T.Examples.Kissat.Full.fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hPropIgn : ∀ args m Q X, fullPropagateIgnoreSpec args m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] args m Q X)
    (hBacktrack : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hDeduce : ∀ args m Q X, fullVivDeduceSpec args m Q X →
      Γ "full_viv_deduce" [i64, i32, i32, i64] [i32] args m Q X)
    (hCommit : ∀ args m Q X, fullVivCommitSpec args m Q X →
      Γ "full_viv_commit" [i64, i32, i64, i32, .bool] [i64] args m Q X) :
    ∀ args m Q X, fullVivClauseSpec args m Q X →
      Func.wp Γ full_viv_clause_body args m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp0, hl0_0, href0, hng0, hm0, hQ⟩
  have hmx := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmx har_cap
  fvt_steps
  c0_call hSimplify
  refine ⟨c, F0, F_cur, s, R, rfl, hsp0, hl0_0, href0, hng0, hm0,
    fun sr s1 m1 hsp1 hl0_1 hfl1 hal1 hrefs1 hsr h20 h0 hm1 => ?_⟩
  rcases hsr with rfl | rfl | rfl
  · fvt_steps
    · contradiction
    · obtain ⟨href1, hng1⟩ := h0 rfl
      have hwf1 := hsp1.2.1.arena.refs_wf cref.toNat href1
      have hcl1 := hsp1.1.core_ok
      have har_len1 := hcl1.arena_len_arr
      have halen_le1 := hcl1.arena_len_le
      have hcr2_nat : (cref.setWidth 64 + 2).toNat = cref.toNat + 2 := by bv_omega
      have hcr0_lt : cref.toNat < s1.core.arena.length := by omega
      have hcr2_lt : cref.toNat + 2 < s1.core.arena.length := by omega
      have hcr2_bv_lt : (cref.setWidth 64 + 2).toNat < s1.core.arena.length := by omega
      fvt_steps
      { exact hQ 1#64 s1 m1 hsp1 hl0_1 (by rw [hfl1]; exact Nat.le_refl _) hal1 hrefs1
          (Or.inl rfl) (fun h => by cases h) hm1 }
      { exact hQ 1#64 s1 m1 hsp1 hl0_1 (by rw [hfl1]; exact Nat.le_refl _) hal1 hrefs1
          (Or.inl rfl) (fun h => by cases h) hm1 }
      let sz := s1.core.arena[(cref.setWidth 64 + 2).toNat]'(by omega)
      have hsz_eq : sz = s1.core.arena[cref.toNat + 2]'hcr2_lt :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem hcr2_bv_lt, hcr2_nat, List.getElem?_eq_getElem hcr2_lt])
      have hsz_nat : sz.toNat = fullArenaClauseSize s1 cref.toNat := by
        rw [hsz_eq]; unfold fullArenaClauseSize fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem hcr2_lt, Option.getD_some]
      have hsz_ge3 : 3 ≤ sz.toNat := hsz_nat ▸ hwf1.2.1
      have hsz_le_cv : sz.toNat ≤ s1.core.cur_vars := by
        have hcv_lt : s1.core.cur_vars < 2 ^ 64 := by have := hcl1.cur_vars_le; omega
        have h2n : (cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref.toNat + 2 := by
          bv_omega
        have har_eq :
            s1.core.arena[(cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by omega) =
              s1.core.arena[cref.toNat + 2]'hcr2_lt :=
          Option.some.inj (by
            rw [← List.getElem?_eq_getElem (by omega), h2n, List.getElem?_eq_getElem hcr2_lt])
        have hc2 : ¬ s1.core.cur_vars < s1.core.arena[cref.toNat + 2].toNat := by
          simpa only [har_eq, Nat.mod_eq_of_lt hcv_lt] using hc
        rw [hsz_eq]; omega
      have hsz_le_mv : sz.toNat ≤ c.max_vars := by have := hcl1.cur_vars_le; omega
      have hcr0_bv : cref.setWidth 64 = BitVec.ofNat 64 cref.toNat := by
        apply BitVec.eq_of_toNat_eq; simp
      have hcr0_nat : (cref.setWidth 64).toNat = cref.toNat := by bv_omega
      let hdr_orig := s1.core.arena[cref.toNat]'hcr0_lt
      have hhdr_orig : fullArenaHdr s1 cref.toNat = hdr_orig := by
        unfold fullArenaHdr fullArenaHdrCore
        rw [List.getElem?_eq_getElem hcr0_lt, Option.getD_some]
      let hdr2 := hdr_orig ||| 0x00100000#32
      let s2 : FullState :=
        { s1 with core := { s1.core with arena := s1.core.arena.set cref.toNat hdr2 } }
      obtain ⟨(hsp2 : FullSparseInvW c F0 F_cur s2), hrefs2, hprops2⟩ :=
        fullArena_setHdr_preserves_sparseW hsp1 href1
          (hdr' := hdr2) (by rw [hhdr_orig]; exact bv32_or_viv_garb hdr_orig)
          (by rw [hhdr_orig]; exact bv32_or_viv_shrk hdr_orig)
      have href2 : cref.toNat ∈ fullArenaClauseRefs s2 := hrefs2 ▸ href1
      have hng2 : fullArenaClauseGarb s2 cref.toNat = false :=
        (hprops2 cref.toNat href1).2.2.1.trans hng1
      have hsz2 : fullArenaClauseSize s2 cref.toNat = sz.toNat :=
        (hprops2 cref.toNat href1).2.1.trans hsz_nat.symm
      have hlits2 : fullArenaClauseLits s2 cref.toNat = fullArenaClauseLits s1 cref.toNat :=
        (hprops2 cref.toNat href1).2.2.2
      have har2_len : s2.core.arena.length = c.arena_cap := hsp2.1.core_ok.arena_len_arr
      have htmp2_len : s2.core.tmp.length = c.max_vars := hsp2.1.core_ok.tmp_len_arr
      have hbd2 : cref.toNat + 3 + sz.toNat ≤ s2.core.arena.length := by
        have h1 := hwf1.2.2.1; have h2 := hwf1.2.2.2.1; have h3 := hcl1.arena_len_le
        rw [hsz_nat]
        change cref.toNat + 3 + fullArenaClauseSizeCore s1.core cref.toNat ≤ s2.core.arena.length
        omega
      -- Copy `ar[cref + 3 .. cref + 3 + sz)` into `tmp[0 .. sz)`
      refine wp_loop_inv (ts := [i32])
        (fun (i, ()) mc => ∃ tmpc : List (BitVec 32),
          i.toNat ≤ sz.toNat ∧ tmpc.length = c.max_vars ∧
          (∀ k < i.toNat, tmpc[k]? = s2.core.arena[cref.toNat + 3 + k]?) ∧
          (FullMem c { s2 with core := { s2.core with tmp := tmpc } } ⋆ R) mc)
        (fun (i, ()) _ => sz.toNat - i.toNat)
        (fun Jc hJc => by
          fvt_steps
          exact hJc (0#32, ()) _ ⟨s2.core.tmp, Nat.zero_le _, htmp2_len,
            fun _ hk => by simp at hk, hm⟩)
        (fun Jc ys mc hs ihc => ?_)
      rcases ys with ⟨i, ⟨⟩⟩
      rcases hs with ⟨tmpc, hi_le, htc_len, hcp, hmc⟩
      fvt_steps
      · have hi_lt : i.toNat < sz.toNat := by c0_bound
        have hidx_nat : (cref.setWidth 64 + (3 : BitVec 64) + i.setWidth 64).toNat =
            cref.toNat + 3 + i.toNat := by bv_omega
        have hi64_nat : (i.setWidth 64).toNat = i.toNat := by bv_omega
        have hi_lt_ar :
            (cref.setWidth 64 + (3 : BitVec 64) + i.setWidth 64).toNat < s2.core.arena.length := by
          omega
        have hi_lt_tmp : i.toNat < tmpc.length := by omega
        have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        fvt_steps
        let tmpc' := tmpc.set i.toNat (s2.core.arena[cref.toNat + 3 + i.toNat]'(by omega))
        have har_eq :
            s2.core.arena[(cref.setWidth 64 + (3 : BitVec 64) + i.setWidth 64).toNat]'hi_lt_ar =
              s2.core.arena[cref.toNat + 3 + i.toNat]'(by omega) :=
          Option.some.inj (by
            rw [← List.getElem?_eq_getElem hi_lt_ar, hidx_nat,
              List.getElem?_eq_getElem (by omega)])
        refine ihc (i + 1#32, ()) _ (by dsimp only; omega)
          ⟨tmpc', by omega, by simp [tmpc', htc_len], fun k hk => ?_, ?_⟩
        · rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
          · dsimp only [tmpc']; rw [List.getElem?_set_ne (by omega)]; exact hcp k hk'
          · dsimp only [tmpc']
            rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
        · simpa only [tmpc', hi64_nat, har_eq] using hm
      · have hi_eq : i.toNat = sz.toNat := by
          have hcr2_mod2 : (cref.toNat + 2) % 2 ^ 64 = cref.toNat + 2 := by omega
          have hc_i : ¬ i.toNat < s1.core.arena[cref.toNat + 2].toNat := by
            have hc0 : ¬ i.toNat < s1.core.arena[(cref.toNat + 2) % 2 ^ 64].toNat := by assumption
            simpa only [hcr2_mod2] using hc0
          rw [hsz_eq] at hi_le ⊢; omega
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
        refine ⟨c, { s2 with core := { s2.core with tmp := tmpc } }, R,
          rfl, rfl, ⟨{ hsp2.1.core_ok with tmp_len_arr := htc_len }, hsp2.1.scratch_ok⟩,
          hsz_le_mv, htmpc_lits_lt, hmc, fun tmp4 m4 htmp4_len hperm4 hrest4 hm4 => ?_⟩
        have hperm_lits : ((tmp4.take sz.toNat).map BitVec.toNat).Perm
            (fullArenaClauseLits s2 cref.toNat) := by
          have := vivCopy_perm_lits (by omega) hbd2 hcp hperm4 (by omega)
          simpa [fullArenaClauseLits, fullArenaClauseLitsCore, hsz2] using this
        obtain ⟨htmp4_mem, hlits_mem⟩ := vivTmp_mem_of_perm (by omega) hperm_lits
        let s4 : FullState := { s2 with core := { s2.core with tmp := tmp4 } }
        have hsp4 : FullSparseInvW c F0 F_cur s4 := FullSparseInvW.with_tmp hsp2 htmp4_len
        fvt_to_group
        let s5 : FullState :=
          { s4 with core := { s4.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } }
        have hsp5 : FullSparseInvW c F0 F_cur s5 :=
          FullSparseInvW.with_confl hsp4 0#64 0xFFFFFFFF#64
        have hfl5 : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
          change s1.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfl1]; exact Nat.le_refl _
        have hal5 : s5.core.arena_len = s.core.arena_len := hal1
        have hrefs5 : fullArenaClauseRefs s5 = fullArenaClauseRefs s := hrefs2.trans hrefs1
        have href5 : cref.toNat ∈ fullArenaClauseRefs s5 := href2
        have hng5 : fullArenaClauseGarb s5 cref.toNat = false := hng2
        have hsz5 : fullArenaClauseSize s5 cref.toNat = sz.toNat := hsz2
        have hct5 : s5.core.confl_type = 0#64 := rfl
        have htmp5 : s5.core.tmp = tmp4 := rfl
        let lits2 := fullArenaClauseLits s2 cref.toNat
        have hperm5 : (fullArenaClauseLits s5 cref.toNat).Perm lits2 := List.Perm.refl _
        have hlits2_lt : ∀ l ∈ lits2, l < 2 * s5.core.cur_vars :=
          fun l hl => hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 l hl
        have hlits2_mem : ∀ k < sz.toNat, (tmp4[k]?.getD 0#32).toNat ∈ lits2 := htmp4_mem
        have hlits2_inv : ∀ l ∈ lits2, ∃ k < sz.toNat, (tmp4[k]?.getD 0#32).toNat = l :=
          hlits_mem
        have hm5 : (FullMem c s5 ⋆ R) m := hm
        clear_value s5 s4 s2 lits2
        clear hprops2 hwf1 hperm4 htmp4_mem hlits_mem hsp4 hsp2 hdr_orig hdr2
          s4 hrefs2 href2 hng2 hsz2 hlits2 har2_len htmp2_len hbd2 htmpc_lits_lt hsp1
          hl0_1 hfl1 hal1 hrefs1 h20 h0 href1 hng1 hcl1 har_len1 halen_le1 hcr2_nat
          hsz_nat hsz_le_cv hcr0_bv hcr0_nat hhdr_orig hperm_lits hsp0 hl0_0
          href0 hng0 hm0 hm
        clear hi_eq hc hrest4 ihc hmc hcp htc_len hi_le tmpc mc Jc i
        try clear hm
        try clear s2
        -- Inner assumption-propagation loop `while (i < sz)` with `break` and early `return 2`
        refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32])
          (fun (i, confl, implied, ()) mb => ∃ sb : FullState,
            FullSparseInvW c F0 F_cur sb ∧
            sb.core.cur_vars = s5.core.cur_vars ∧ sb.core.arena_len = s5.core.arena_len ∧
            sb.core.probing = s5.core.probing ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
            cref.toNat ∈ fullArenaClauseRefs sb ∧
            fullArenaClauseGarb sb cref.toNat = false ∧
            fullArenaClauseSize sb cref.toNat = sz.toNat ∧
            (confl = true ∨ implied ≠ 0xFFFFFFFF#32 ∨ i.toNat = sz.toNat) ∧
            (confl = true → FullConflictOkW F_cur sb) ∧
            (confl = false → implied ≠ 0xFFFFFFFF#32 →
              implied.toNat < 2 * sb.core.cur_vars ∧
              sb.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
            (confl = false → implied = 0xFFFFFFFF#32 →
              sb.core.confl_type = 0#64 ∧
              ∀ l ∈ fullArenaClauseLits sb cref.toNat, sb.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
            (FullMem c sb ⋆ R) mb)
          (fun rem (i, ()) mp => ∃ sp : FullState,
            i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat ∧
            FullSparseInvW c F0 F_cur sp ∧
            sp.core.cur_vars = s5.core.cur_vars ∧ sp.core.arena_len = s5.core.arena_len ∧
            sp.core.probing = s5.core.probing ∧ sp.core.tmp = tmp4 ∧
            sp.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            fullArenaClauseRefs sp = fullArenaClauseRefs s ∧
            cref.toNat ∈ fullArenaClauseRefs sp ∧
            fullArenaClauseGarb sp cref.toNat = false ∧
            fullArenaClauseSize sp cref.toNat = sz.toNat ∧
            (fullArenaClauseLits sp cref.toNat).Perm lits2 ∧
            sp.core.confl_type = 0#64 ∧
            (∀ k < i.toNat, sp.core.vals[(tmp4[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
            (FullMem c sp ⋆ R) mp)
          ?_ ?_ ?_
        · -- After loop (`@brk`)
          rintro _ ⟨i_b, confl_b, impl_b, ⟨⟩⟩ mb
            ⟨sb, hspb, hcvb, halb, hprb, hflb, hrefsb, hrefb, hngb, hszb,
             hcondb, hcokb, himplb, hfalb, hmb⟩
          fvt_to_group
          let sb1 : FullState := { sb with scratch := { sb.scratch with res_sz := 0#64 } }
          have hspb1 : FullSparseInvW c F0 F_cur sb1 := FullSparseInvW.with_res_sz hspb 0#64
          refine wp_join_group (ts := [i32])
            (fun (olen, ()) md => ∃ sd : FullState,
              FullSparseInvW c F0 F_cur sd ∧
              sd.core.cur_vars = s5.core.cur_vars ∧ sd.core.arena_len = s5.core.arena_len ∧
              sd.core.probing = s5.core.probing ∧ sd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              fullArenaClauseRefs sd = fullArenaClauseRefs s ∧
              cref.toNat ∈ fullArenaClauseRefs sd ∧
              fullArenaClauseGarb sd cref.toNat = false ∧
              fullArenaClauseSize sd cref.toNat = sz.toNat ∧
              olen.toNat ≤ c.max_vars ∧
              (olen.toNat < sz.toNat →
                (∀ k < olen.toNat,
                  (sd.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * sd.core.cur_vars) ∧
                ((sd.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
                (cnfOfClauses F_cur).EntailsClause
                  (cnfClause ((sd.scratch.work_stk2.take olen.toNat).map BitVec.toNat))) ∧
              (FullMem c sd ⋆ R) md)
            ?_ ?_
          · -- After `if (confl || implied != 0xFFFFFFFFu || i == sz)`
            rintro _ ⟨olen, ⟨⟩⟩ md
              ⟨sd, hspd, hcvd, hald, hprd, hfld, hrefsd, hrefd, hngd, hszd,
               hol_le, hol_ok, hmd⟩
            fvt_steps
            have hd_cl_lt : sd.core.cur_level < 2 ^ 64 := by
              have := hspd.2.1.cur_level_le; have := hspd.1.core_ok.trail_end_le
              have := hspd.1.core_ok.cur_vars_le; omega
            have hd_trl : ∀ idx < sd.core.trail_end,
                (sd.core.trl[idx]?.getD 0#32).toNat < 2 * sd.core.cur_vars :=
              hspd.2.1.trail_lits_lt
            c0_call hBacktrack
            refine ⟨c, sd, R, rfl, hspd.1, hd_cl_lt,
              (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; omega),
              hd_trl, hmd,
              fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                hlen_bt hte_bt hprop_bt hcl_bt hpres_bt htrl_bt hw_bt _ hm_bt => ?_⟩
            have hcl_bt0 : cl' = 0 := by rw [hcl_bt]; simp
            have hsp_bt : FullSparseInvW c F0 F_cur _ :=
              FullSparseInvW.of_backtrack hspd (Nat.zero_le _) hlen_bt hpres_bt
                (hw_bt F0 F_cur hspd.2.1 (Nat.zero_le _))
            let s_bt : FullState :=
              { sd with
                core :=
                  { sd.core with
                    vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    cur_level := cl', unassigned := unass' }
                scratch := sc' }
            have hws2_bt : s_bt.scratch.work_stk2 = sd.scratch.work_stk2 := hpres_bt.2.2.1
            fvt_steps
            · have hol_lt : olen.toNat < sz.toNat := by c0_bound
              obtain ⟨hws_lt, hws_nd, hws_ent⟩ := hol_ok hol_lt
              c0_call hCommit
              refine ⟨c, F0, F_cur, s_bt, R, rfl, rfl, hsp_bt, hcl_bt0, hrefd, hngd, hol_le,
                fun _ => ⟨by simpa [hws2_bt] using hws_lt,
                          by simpa [hws2_bt] using hws_nd,
                          by simpa [hws2_bt] using hws_ent⟩,
                hm_bt, fun r_c s_cm m_cm hspc hlc hflc halc hrefsc hrc h20c hm_cm => ?_⟩
              exact hQ r_c s_cm m_cm hspc hlc (hflc ▸ hfld)
                (halc.trans (hald.trans hal5)) (hrefsc.trans hrefsd) hrc h20c hm_cm
            · exact hQ 1#64 s_bt m_bt hsp_bt hcl_bt0 hfld (hald.trans hal5) hrefsd (Or.inl rfl)
                (fun h => by cases h) hm_bt
          · -- `if (confl || implied != 0xFFFFFFFFu || i == sz)` entry
            intro Jif hJif
            fvt_steps
            all_goals try
              have hct : confl_b = true := by assumption
              have hcf : confl_b = false := by assumption
              exact absurd (hct.symm.trans hcf) (by decide)
            · -- `confl = true`
              have hcfl_t : confl_b = true := by first | assumption | c0_bound
              c0_call hDeduce
              refine ⟨c, F0, F_cur, sb1, R, rfl, rfl, hspb1, hrefb, hngb,
                fun _ => Or.inl (hcokb hcfl_t), fun h => absurd rfl h, hm,
                fun olen mrk' ws1' ws2' rsz' md hspd hol_le hol_ok hmd => ?_⟩
              exact hJif (olen, ()) md ⟨_, hspd, hcvb, halb, hprb, hflb, hrefsb, hrefb, hngb, hszb,
                hol_le, fun h => hol_ok (by rw [hszb]; exact h), hmd⟩
            · have hcfl_f : confl_b = false := by first | assumption | c0_bound
              have himpl_ne : impl_b ≠ 0xFFFFFFFF#32 := by first | assumption | c0_bound
              obtain ⟨him_lt, him_val⟩ := himplb hcfl_f himpl_ne
              c0_call hDeduce
              refine ⟨c, F0, F_cur, sb1, R, rfl, rfl, hspb1, hrefb, hngb,
                fun h => absurd h himpl_ne, fun _ => ⟨him_lt, him_val⟩, hm,
                fun olen mrk' ws1' ws2' rsz' md hspd hol_le hol_ok hmd => ?_⟩
              exact hJif (olen, ()) md ⟨_, hspd, hcvb, halb, hprb, hflb, hrefsb, hrefb, hngb, hszb,
                hol_le, fun h => hol_ok (by rw [hszb]; exact h), hmd⟩
            · have hcfl_f : confl_b = false := by first | assumption | c0_bound
              have himpl_eq : impl_b = 0xFFFFFFFF#32 := by first | assumption | c0_bound
              obtain ⟨hct0, hfal⟩ := hfalb hcfl_f himpl_eq
              c0_call hDeduce
              refine ⟨c, F0, F_cur, sb1, R, rfl, rfl, hspb1, hrefb, hngb,
                fun _ => Or.inr ⟨hct0, hfal⟩, fun h => absurd himpl_eq h, hm,
                fun olen mrk' ws1' ws2' rsz' md hspd hol_le hol_ok hmd => ?_⟩
              exact hJif (olen, ()) md ⟨_, hspd, hcvb, halb, hprb, hflb, hrefsb, hrefb, hngb, hszb,
                hol_le, fun h => hol_ok (by rw [hszb]; exact h), hmd⟩
            · exfalso
              have h2n : (cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref.toNat + 2 := by
                bv_omega
              have har_eq :
                  s1.core.arena[(cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by omega) =
                    sz := by
                rw [hsz_eq]
                exact Option.some.inj (by
                  rw [← List.getElem?_eq_getElem (by omega), h2n,
                    List.getElem?_eq_getElem hcr2_lt])
              have hcfl_f : confl_b = false := by assumption
              have himpl_eq : impl_b = 0xFFFFFFFF#32 := by assumption
              have hi_ne_bv : i_b ≠ sz := by
                have hne :
                    ¬ i_b = s1.core.arena[(cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64] :=
                  by assumption
                simpa only [har_eq] using hne
              rcases hcondb with h | h | h
              · exact absurd (hcfl_f.symm.trans h) (by decide)
              · exact absurd himpl_eq h
              · exact hi_ne_bv (BitVec.eq_of_toNat_eq h)
        · -- Inner loop body (`@loop`)
          intro B L rem (i, ⟨⟩) mp hB hL
            ⟨sp, hi_le, hrem, hspp, hcvp, halp, hprp, htmpp, hflp, hrefsp, hrefp, hngp, hszp,
             hpermp, hct0, hfalp, hmp⟩
          fvt_steps
          · -- `i < sz`
            have hi_lt : i.toNat < sz.toNat := by c0_bound
            have hsp_len := hspp.1.core_ok
            have htmp_len : sp.core.tmp.length = c.max_vars := hsp_len.tmp_len_arr
            have hi_lt_tmp : i.toNat < sp.core.tmp.length := by omega
            have hlit_mem2 : (tmp4[i.toNat]?.getD 0#32).toNat ∈ lits2 :=
              hlits2_mem i.toNat hi_lt
            have hlit_lt_cv : (tmp4[i.toNat]?.getD 0#32).toNat < 2 * sp.core.cur_vars := by
              rw [hcvp]; exact hlits2_lt _ hlit_mem2
            have hlit_lt_vals : (tmp4[i.toNat]?.getD 0#32).toNat < sp.core.vals.length := by
              rw [hsp_len.vals_len]; have := hsp_len.cur_vars_le; omega
            have hi64_nat : (i.setWidth 64).toNat = i.toNat := bv32_setWidth64_toNat i
            have hi_lt_tmp64 : (i.setWidth 64).toNat < sp.core.tmp.length := by
              rw [hi64_nat]; exact hi_lt_tmp
            have htmp_i_eq : sp.core.tmp[(i.setWidth 64).toNat]'hi_lt_tmp64 =
                tmp4[i.toNat]?.getD 0#32 := by
              exact Option.some.inj (by
                rw [← List.getElem?_eq_getElem hi_lt_tmp64, htmpp, hi64_nat,
                  List.getElem?_eq_getElem (by omega), Option.getD_some])
            have htmp_i_lt : sp.core.tmp[(i.setWidth 64).toNat].toNat < sp.core.vals.length := by
              rw [htmp_i_eq]; exact hlit_lt_vals
            have htmp_i_lt' : (sp.core.tmp[(i.setWidth 64).toNat].setWidth 64).toNat <
                sp.core.vals.length := by
              rw [bv32_setWidth64_toNat]; exact htmp_i_lt
            fvt_to_group
            · -- `lv > (i8)0`: implied literal -> break!
              let lit := sp.core.tmp[i.toNat]'hi_lt_tmp
              have hlit_eq : lit = tmp4[i.toNat]?.getD 0#32 := by
                simp only [lit, htmpp]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hlit_i64 : sp.core.tmp[(i.setWidth 64).toNat]'hi_lt_tmp64 = lit := by
                rw [htmp_i_eq, hlit_eq]
              have hlit_lt : lit.toNat < 2 * sp.core.cur_vars := hlit_eq ▸ hlit_lt_cv
              have hlit_lt_vals' : lit.toNat < sp.core.vals.length := hlit_eq ▸ hlit_lt_vals
              have hdom := hspp.2.1.vals_domain lit.toNat hlit_lt
              have hlv1 : sp.core.vals[lit.toNat]?.getD 0#8 = 1#8 := by
                rw [List.getElem?_eq_getElem hlit_lt_vals', Option.getD_some]
                exact (bv8_dom_sgt0_iff
                  (by simpa [List.getElem?_eq_getElem hlit_lt_vals'] using hdom)).mp (by c0_bound)
              have hcv_le_mx := hsp_len.cur_vars_le
              have hlit_neff : lit ≠ 0xFFFFFFFF#32 := bv32_ne_sentinel_of_lt (by omega)
              rw [hlit_i64]
              exact hB (i, false, lit, ()) _ ⟨sp, hspp, hcvp, halp, hprp, hflp, hrefsp, hrefp,
                hngp, hszp, Or.inr (Or.inl hlit_neff), (fun h => by cases h),
                fun _ _ => ⟨hlit_lt, hlv1⟩, fun _ h => absurd h hlit_neff, hmp⟩
            · -- `¬ (lv > (i8)0)`: inner `wp_join_group` for `if (lv == (i8)0)` -> `i + 1`
              refine wp_join_group (ts := [.bool])
                (fun (_, ()) m_jn => ∃ s_jn : FullState,
                  FullSparseInvW c F0 F_cur s_jn ∧
                  s_jn.core.cur_vars = s5.core.cur_vars ∧
                  s_jn.core.arena_len = s5.core.arena_len ∧
                  s_jn.core.probing = s5.core.probing ∧ s_jn.core.tmp = tmp4 ∧
                  s_jn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  fullArenaClauseRefs s_jn = fullArenaClauseRefs s ∧
                  cref.toNat ∈ fullArenaClauseRefs s_jn ∧
                  fullArenaClauseGarb s_jn cref.toNat = false ∧
                  fullArenaClauseSize s_jn cref.toNat = sz.toNat ∧
                  (fullArenaClauseLits s_jn cref.toNat).Perm lits2 ∧
                  s_jn.core.confl_type = 0#64 ∧
                  (∀ k < (i + 1#32).toNat,
                    s_jn.core.vals[(tmp4[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
                  (FullMem c s_jn ⋆ R) m_jn)
                ?_ ?_
              · rintro _ ⟨_, ⟨⟩⟩ m_jn ⟨s_jn, hsp_jn, hcv_jn, hal_jn, hpr_jn, htmp_jn, hfl_jn,
                  hrefs_jn, href_jn, hng_jn, hsz_jn, hperm_jn, hct_jn, hfal_jn, hm_jn⟩
                have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                fvt_steps
                exact hL (sz.toNat - (i + 1#32).toNat) (i + 1#32, ()) _
                  (by (try dsimp only); (try rw [hi1_nat]); omega)
                  ⟨s_jn, by omega, rfl, hsp_jn, hcv_jn, hal_jn, hpr_jn, htmp_jn, hfl_jn,
                   hrefs_jn, href_jn, hng_jn, hsz_jn, hperm_jn, hct_jn, hfal_jn, hm_jn⟩
              · intro J_jn hJ_jn
                fvt_steps
                · -- `lv == (i8)0 ∧ max_vars < nlvl`: impossible
                  exfalso
                  let lit := sp.core.tmp[i.toNat]'hi_lt_tmp
                  have hlit_eq : lit = tmp4[i.toNat]?.getD 0#32 := by
                    simp only [lit, htmpp]
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have hlit_lt : lit.toNat < 2 * sp.core.cur_vars := hlit_eq ▸ hlit_lt_cv
                  have hlit_lt_vals' : lit.toNat < sp.core.vals.length := hlit_eq ▸ hlit_lt_vals
                  have hlv0 : sp.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem hlit_lt_vals', Option.getD_some]
                    exact (bv8_sext32_eq0_iff _).mp (by first | assumption | c0_bound)
                  have hte_lt : sp.core.trail_end < sp.core.cur_vars :=
                    hspp.2.1.trail_end_lt_of_unassigned hlit_lt hlv0
                  have hnlvl_le : sp.core.cur_level + 1 ≤ c.max_vars := by
                    have := hspp.2.1.cur_level_le; have := hsp_len.cur_vars_le; omega
                  have hc0 : c.max_vars % 2 ^ 64 <
                      (sp.core.cur_level + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := by
                    assumption
                  have h1n : BitVec.toNat (1 : BitVec 64) = 1 := rfl
                  rw [h1n] at hc0
                  have hmx_lt : c.max_vars < 2 * 2 ^ 28 := hmx
                  omega
                · -- `lv == (i8)0`: decide `lit ^ 1`, `full_assign`, `full_propagate_ignore`
                  let lit := sp.core.tmp[i.toNat]'hi_lt_tmp
                  have hlit_eq : lit = tmp4[i.toNat]?.getD 0#32 := by
                    simp only [lit, htmpp]
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have hlit_lt : lit.toNat < 2 * sp.core.cur_vars := hlit_eq ▸ hlit_lt_cv
                  have hlit_lt_vals' : lit.toNat < sp.core.vals.length := hlit_eq ▸ hlit_lt_vals
                  have hlv0 : sp.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem hlit_lt_vals', Option.getD_some]
                    exact (bv8_sext32_eq0_iff _).mp (by first | assumption | c0_bound)
                  have hte_lt : sp.core.trail_end < sp.core.cur_vars :=
                    hspp.2.1.trail_end_lt_of_unassigned hlit_lt hlv0
                  have hnlvl_le : sp.core.cur_level + 1 ≤ c.max_vars := by
                    have := hspp.2.1.cur_level_le; have := hsp_len.cur_vars_le; omega
                  have hcl_lt32 : sp.core.cur_level < 2 ^ 32 := by
                    have := hspp.2.1.cur_level_le; omega
                  have hnlvl_nat : (BitVec.ofNat 64 sp.core.cur_level + 1#64).toNat =
                      sp.core.cur_level + 1 := by bv_omega
                  have hnlvl_lt_ft : (BitVec.ofNat 64 sp.core.cur_level + 1#64).toNat <
                      sp.core.frame_trail.length := by
                    rw [hnlvl_nat, hsp_len.frame_trail_len]; omega
                  have hnlvl_lt_fd : (BitVec.ofNat 64 sp.core.cur_level + 1#64).toNat <
                      sp.core.frame_dec.length := by
                    rw [hnlvl_nat, hsp_len.frame_dec_len]; omega
                  fvt_steps
                  let nlvl := sp.core.cur_level + 1
                  let dlit := lit ^^^ 1#32
                  let ftrl' := sp.core.frame_trail.set nlvl (BitVec.ofNat 32 sp.core.trail_end)
                  let fdec' := sp.core.frame_dec.set nlvl dlit
                  let s_pre : FullState :=
                    { sp with
                      core :=
                        { sp.core with
                          frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl } }
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
                  have hnot_guard : ¬ (s_pre.core.cur_vars ≤ dlit.toNat / 2 ∨
                      c.max_vars ≤ s_pre.core.trail_end ∨
                      s_pre.core.vals[dlit.toNat]?.getD 0#8 ≠ 0#8) := by
                    intro hor; rcases hor with h1 | h2 | h3
                    · dsimp only [s_pre] at h1; omega
                    · have hcv_le := hsp_len.cur_vars_le
                      dsimp only [s_pre] at h2; omega
                    · exact h3 hdlit_zero
                  have hte_bv : BitVec.setWidth 32 (BitVec.ofNat 64 sp.core.trail_end) =
                      BitVec.ofNat 32 sp.core.trail_end := by
                    apply BitVec.eq_of_toNat_eq; simp
                  have hlit_i64 : sp.core.tmp[(i.setWidth 64).toNat]'hi_lt_tmp64 = lit := by
                    rw [htmp_i_eq, hlit_eq]
                  rw [hlit_i64]
                  c0_call hAssign
                  refine ⟨c, s_pre, R, rfl, hlen_pre, by dsimp [s_pre, nlvl]; omega,
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
                          vals :=
                            (sp.core.vals.set dlit.toNat 1#8).set (dlit.toNat ^^^ 1) 0xFF#8
                          flags := flags',
                          lvl := sp.core.lvl.set (dlit.toNat / 2) (BitVec.ofNat 32 nlvl),
                          rsns := sp.core.rsns.set (dlit.toNat / 2) 0xFFFFFFFF#32,
                          trl := sp.core.trl.set sp.core.trail_end dlit,
                          trail_pos := sp.core.trail_pos.set (dlit.toNat / 2)
                            (BitVec.ofNat 32 sp.core.trail_end),
                          frame_trail := ftrl', frame_dec := fdec',
                          trail_end := sp.core.trail_end + 1,
                          cur_level := nlvl, unassigned := unass' }
                      scratch := { sp.scratch with phases := phases' } }
                  have hsp_as' : FullSparseInvW c F0 F_cur s_as := hsp_as
                  have hrefs_as : fullArenaClauseRefs s_as = fullArenaClauseRefs sp := rfl
                  have hng_as : fullArenaClauseGarb s_as cref.toNat = false := hngp
                  have hsz_as : fullArenaClauseSize s_as cref.toNat = sz.toNat := hszp
                  have hlits_as : fullArenaClauseLits s_as cref.toNat =
                      fullArenaClauseLits sp cref.toNat := rfl
                  have hcv_as : s_as.core.cur_vars = sp.core.cur_vars := rfl
                  have hal_as : s_as.core.arena_len = sp.core.arena_len := rfl
                  have hpr_as : s_as.core.probing = sp.core.probing := rfl
                  have hfl_as : s_as.core.fuel = sp.core.fuel := rfl
                  have hct_as : s_as.core.confl_type = 0#64 := hct0
                  have htmp_as : s_as.core.tmp = tmp4 := htmpp
                  have hfal_as' : ∀ l < 2 * sp.core.cur_vars,
                      sp.core.vals[l]?.getD 0#8 = 0xFF#8 →
                      s_as.core.vals[l]?.getD 0#8 = 0xFF#8 := hfal_as
                  have hlit_as_ff' : s_as.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := hlit_as_ff
                  have hm_as' : (FullMem c s_as ⋆ R) m_as := hm_as
                  clear_value s_as
                  try clear hsp_as hfal_as hlit_as_ff hm_as hlen_pre hguard hnot_guard
                  fvt_steps
                  exact viv_clause_prop_step Γ hPropIgn hBacktrack hQ hB hJ_jn hsp_as'
                    hcvp hcv_as halp hal_as hprp hpr_as hflp hfl_as hal5 hrefsp hrefs_as
                    hrefp hng_as hsz_as hpermp hlits_as hct_as htmp_as
                    hlits2_lt hlits2_mem hi_lt hlit_eq hlit_lt hfalp hfal_as' hlit_as_ff' hm_as'
                · -- `lv ≠ (i8)0`: `lit` already falsified (`0xFF#8`), join to `i + 1`
                  let lit := sp.core.tmp[i.toNat]'hi_lt_tmp
                  have hlit_eq : lit = tmp4[i.toNat]?.getD 0#32 := by
                    simp only [lit, htmpp]
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have hlit_lt : lit.toNat < 2 * sp.core.cur_vars := hlit_eq ▸ hlit_lt_cv
                  have hlit_lt_vals' : lit.toNat < sp.core.vals.length := hlit_eq ▸ hlit_lt_vals
                  have hdom := hspp.2.1.vals_domain lit.toNat hlit_lt
                  have hlv_eq : sp.core.vals[lit.toNat]? =
                      some (sp.core.vals[lit.toNat]'hlit_lt_vals') :=
                    List.getElem?_eq_getElem hlit_lt_vals'
                  have hne1 : sp.core.vals[lit.toNat]'hlit_lt_vals' ≠ 1#8 := by
                    intro heq
                    have hgt : (0#32).slt
                        ((sp.core.vals[lit.toNat]'hlit_lt_vals').signExtend 32) = true := by
                      rw [heq]; decide
                    have hflt : (0#32).slt
                        ((sp.core.vals[lit.toNat]'hlit_lt_vals').signExtend 32) = false := by
                      assumption
                    exact Bool.false_ne_true (hflt.symm.trans hgt)
                  have hne0 : sp.core.vals[lit.toNat]'hlit_lt_vals' ≠ 0#8 := by
                    intro heq
                    have heq0 : (sp.core.vals[lit.toNat]'hlit_lt_vals').signExtend 32 = 0#32 := by
                      rw [heq]; decide
                    have hne0_raw :
                        (sp.core.vals[lit.toNat]'hlit_lt_vals').signExtend 32 ≠ 0#32 := by
                      assumption
                    exact hne0_raw heq0
                  have hlv_ff : sp.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
                    rw [hlv_eq, Option.getD_some]
                    rcases (by simpa [hlv_eq] using hdom) with h | h | h
                    · exact absurd h hne0
                    · exact absurd h hne1
                    · exact h
                  have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                  fvt_steps
                  exact hJ_jn _ _ ⟨sp, hspp, hcvp, halp, hprp, htmpp, hflp, hrefsp, hrefp, hngp,
                    hszp, hpermp, hct0, fun k hk => by
                      rw [hi1_nat] at hk
                      rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
                      · exact hfalp k hk'
                      · rw [← hlit_eq]; exact hlv_ff,
                    hmp⟩
          · -- Loop exit `i == sz` -> `@brk`
            have hi_eq : i.toNat = sz.toNat := by
              have h2n : (cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cref.toNat + 2 := by
                bv_omega
              have har_eq :
                  s1.core.arena[(cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by omega) =
                    sz := by
                rw [hsz_eq]
                exact Option.some.inj (by
                  rw [← List.getElem?_eq_getElem (by omega), h2n,
                    List.getElem?_eq_getElem hcr2_lt])
              have hc_i : ¬ i.toNat < sz.toNat := by
                have hc_raw : ¬ i.toNat <
                    s1.core.arena[(cref.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64].toNat := by
                  assumption
                simpa only [har_eq] using hc_raw
              omega
            have hrefs_eq : fullArenaClauseRefs sp = fullArenaClauseRefs s := hrefsp
            have hfal_all : ∀ l ∈ fullArenaClauseLits sp cref.toNat,
                sp.core.vals[l]?.getD 0#8 = 0xFF#8 := by
              intro l hl
              have hl2 : l ∈ lits2 := hpermp.mem_iff.mp hl
              obtain ⟨k, hk, hget⟩ := hlits2_inv l hl2
              rw [← hget]; exact hfalp k (by omega)
            fvt_steps
            exact hB (i, false, 0xFFFFFFFF#32, ()) _ ⟨sp, hspp, hcvp, halp, hprp, hflp, hrefs_eq,
              hrefp, hngp, hszp, Or.inr (Or.inr hi_eq), (fun h => by cases h),
              fun _ h => absurd rfl h, fun _ _ => ⟨hct0, hfal_all⟩, hmp⟩
        · -- Inner loop entry
          intro B L hB hL
          fvt_steps
          exact hL sz.toNat (0#32, ()) _ ⟨s5, Nat.zero_le _, by simp, hsp5, rfl, rfl, rfl,
            htmp5, hfl5, hrefs5, href5, hng5, hsz5, hperm5, hct5, fun _ hk => by simp at hk, hm5⟩
  · fvt_steps
    exact hQ 1#64 s1 m1 hsp1 hl0_1 (by rw [hfl1]; exact Nat.le_refl _) hal1 hrefs1
      (Or.inl rfl) (fun h => by cases h) hm1
  · (try fvt_unmdata); (repeat fvt_strip); c0_steps
    · exact hQ 20#64 s1 m1 hsp1 hl0_1 (by rw [hfl1]; exact Nat.le_refl _) hal1 hrefs1
        (Or.inr (Or.inr rfl)) (fun _ => h20 rfl) hm1
    · contradiction


end VivClauseCanonAssign

end FullVivTopSpecs

section VivTopBridge

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

private theorem vivTopOtfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullVivTopSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem vivTopSimplify_adapter {Γ : Env}
    (hSimplify : ∀ a m Q X, fullVivSimplifySpec a m Q X →
      Γ "full_viv_simplify" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullVivTopSpecs.fullVivSimplifySpec a m Q X →
      Γ "full_viv_simplify" [i64, i32] [i64] a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hl0, href, hng, hm, hQ⟩
  exact hSimplify _ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hl0, href, hng, hm,
    fun r s' m' hsp' hl0' _ hal' _ hfl' hrefs' hr h20 h0 hm' =>
      hQ r s' m' hsp' hl0' hfl' hal' hrefs' hr h20 h0 hm'⟩

private theorem vivTopBacktrack_adapter {Γ : Env}
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullVivTopSpecs.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, hQ⟩
  exact hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
      hlen' hte hprop hcl hps _ htrl' _ hw_w hw_o hm' =>
      hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' hlen' hte hprop hcl hps htrl' hw_w
        (fun F0 Fc ho => hw_o F0 Fc (vivTopOtfs_to_canon ho)) hm'⟩

private theorem vivTopPropIgnore_adapter {Γ : Env}
    (hPropIgn : ∀ a m Q X, fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullVivTopSpecs.fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X := by
  rintro ⟨h, ign, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hm, hQ⟩
  refine hPropIgn _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr hperm hfu hr hr0 hr1 hr2 hnp hm'
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
  have hnd' : FullVivTopSpecs.FullArenaVarsNodup s' := by
    intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hnd ref href0 (hgb.symm.trans hng))
  have hps' : FullVivTopSpecs.FullProbeScratchPres s s' :=
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' s'.scratch m'
    hlen' hw' hnd' hps' htr.1 hfu hperm.2.1 hperm.2.2 htr.2.1 hr
    (fun h0 => let ⟨hp, hct, hoo, hfl⟩ := hr0 h0; ⟨hp, hoo, hct, hfl⟩)
    (fun h1 => let ⟨hf, hoo, hc, _⟩ := hr1 h1; ⟨hf, hoo, hc⟩) hr2 hnp hm'

private theorem vivTopProp_adapter {Γ : Env}
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullVivTopSpecs.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hm, hQ⟩
  refine hProp _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr hperm hfu hr hr0 hr1 hr2 hnp hm'
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
  have hnd' : FullVivTopSpecs.FullArenaVarsNodup s' := by
    intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hnd ref href0 (hgb.symm.trans hng))
  have hps' : FullVivTopSpecs.FullProbeScratchPres s s' :=
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' s'.scratch m'
    hlen' hw' hnd' hps' htr.1 hfu
    (fun ref href => by change ref ∈ fullArenaClauseRefsCore _; rw [hperm.2.1]; exact href)
    htr.2.1 hr hr0 hr1 hr2 hnp hm'

private theorem vivTopCommit_adapter {Γ : Env}
    (hCommit : ∀ a m Q X, fullVivCommitSpec a m Q X →
      Γ "full_viv_commit" [i64, i32, i64, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, FullVivTopSpecs.fullVivCommitSpec a m Q X →
      Γ "full_viv_commit" [i64, i32, i64, i32, .bool] [i64] a m Q X := by
  rintro ⟨h, cref, out_ptr, olen, used_red, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, rfl, hsp, hl0, href, hng, hol, hout, hm, hQ⟩
  exact hCommit _ m Q X ⟨c, F0, F_cur, s, R, rfl, rfl, hsp, hl0, href, hng, hol, hout, hm,
    fun r s' m' hsp' hl0' _ hal' _ hfl' hrefs' hr h20 hm' =>
      hQ r s' m' hsp' hl0' hfl' hal' hrefs' hr h20 hm'⟩

theorem full_viv_clause_bridge_wp (Γ : Env)
    (hSimplify : ∀ a m Q X, fullVivSimplifySpec a m Q X →
      Γ "full_viv_simplify" [i64, i32] [i64] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortLitsSpec a m Q X →
      Γ "full_viv_sort_lits" [i64, i64, i32] [] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hPropIgn : ∀ a m Q X, fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hDeduce : ∀ a m Q X, fullVivDeduceSpec a m Q X →
      Γ "full_viv_deduce" [i64, i32, i32, i64] [i32] a m Q X)
    (hCommit : ∀ a m Q X, fullVivCommitSpec a m Q X →
      Γ "full_viv_commit" [i64, i32, i64, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullVivClauseSpec a m Q X → Func.wp Γ full_viv_clause_body a m Q X :=
  FullVivTopSpecs.full_viv_clause_canon_assign_wp Γ (vivTopSimplify_adapter hSimplify) hSort
    hAssign (vivTopPropIgnore_adapter hPropIgn) (vivTopBacktrack_adapter hBt) hDeduce
    (vivTopCommit_adapter hCommit)

theorem full_vivify_bridge_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hVivClause : ∀ a m Q X, fullVivClauseSpec a m Q X →
      Γ "full_viv_clause" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullVivifySpec a m Q X → Func.wp Γ full_vivify_body a m Q X :=
  full_vivify_wp Γ (vivTopBacktrack_adapter hBt) hNext hVivClause (vivTopProp_adapter hProp)

end VivTopBridge

end LeanQbe.T.Examples.Kissat.Full
