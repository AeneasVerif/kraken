module
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof0
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
import LeanQbe.T.Examples.Kissat.FullTransLemmas
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Wave-2 `PR-W2C` (`RC-21`) Transitive Reduction Proofs (`FullM6VivBackboneProof4b`)

Proves the 3 transitive reduction functions (`full_trans_lit_m6`, `full_trans_sort_m6`,
`full_transitive_m6`), certifying exact canonical `FullFastBveBudgets.fullTransitiveFastSpec`.
UNSAT soundness ONLY (no SAT/model proofs).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6VivBackbone

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.Full.FullTransHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets Kraken.Bedrock2.Test
open scoped FullArenaTactics

/-! ## 1. Cross-File Specifications -/

/-- Canonical spec for `full_trans_lit_m6(h, src, stop_early)`. -/
@[expose] def fullTransLitM6Spec : Spec [i64, i32, .bool] [.bool] :=
  fun (h, src, _stop_early, ()) m Q _X =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧
      src.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
        FullSparseInv c F0 s' → s'.core.cur_level = 0 →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.scratch.work_stk1 = s.scratch.work_stk1 →
        (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical spec for `full_trans_sort_m6(h, n)` (Shell sort of `work_stk1[0..<n)`). -/
@[expose] def fullTransSortM6Spec : Spec [i64, i64] [] :=
  fun (h, n, ()) m Q _X =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ n.toNat ≤ s.core.cur_vars ∧
      (∀ i < n.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ws1' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with work_stk1 := ws1' } }
        ws1'.length = 2 * c.max_vars → FullSparseInv c F0 s' →
        (∀ i < n.toNat, (ws1'[i]?.getD 0#32).toNat < s.core.cur_vars) →
        (FullMem c s' ⋆ R) m' → Q () m'

/-! ## 2. Private Helpers -/

section TransM6Helpers

private theorem t4b_fullMem_eq {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (heq : s1 = s2) (hm : (FullMem c s1 ⋆ R) m) : (FullMem c s2 ⋆ R) m := heq ▸ hm

private theorem t4b_bnds {c : FullCfg} {k : FullCoreState} (hl : k.LengthsOk c) :
    2 * k.cur_vars + 1 < 2 ^ 30 ∧ k.wlen ≤ c.wcap ∧ k.wlen < 2 ^ 64 ∧ k.trail_end < 2 ^ 64 := by
  have := hl.cur_vars_le; have := hl.wlen_le; have := hl.trail_end_le
  have := c.hmaxv; have := c.hwcap; unfold dimacsBound at *; omega

private theorem t4b_wstk_lt {c : FullCfg} {k : FullCoreState} {p end_v : Nat}
    (hl : FullCoreState.LengthsOk c k) (hp : p < end_v) (he : end_v ≤ k.wlen) :
    p < k.wstk.length := by rw [hl.wstk_len_arr]; have := hl.wlen_le; omega

private theorem t4b_vals_lt {c : FullCfg} {k : FullCoreState} {l : Nat}
    (hl : FullCoreState.LengthsOk c k) (h : l < 2 * k.cur_vars) :
    l < k.vals.length := by rw [hl.vals_len]; have := hl.cur_vars_le; omega

private theorem t4b_getElem_toNat {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) :
    (xs[i]'hi).toNat = (xs[i]?.getD 0#32).toNat := by simp [List.getElem?_eq_getElem hi]

private theorem t4b_bv32_ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

private theorem t4b_bv64_sub_sz (a b r : BitVec 64) {bn rn : Nat}
    (hb : b.toNat = bn) (hr : r.toNat = rn) (h : rn ≤ bn) (hbn : bn < 2 ^ 32) :
    BitVec.setWidth 32 (a + b - a - r) = BitVec.ofNat 32 (bn - rn) := by
  apply BitVec.eq_of_toNat_eq; have : (a + b - a - r).toNat = bn - rn := by bv_omega
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, this, Nat.mod_eq_of_lt (by omega)]

private theorem t4b_bv64_sub1 {n : Nat} (hn1 : 0 < n) (hn2 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - 1).toNat = n - 1 := by bv_omega

private theorem t4b_vals_ff_of_domain {v : BitVec 8} {z : BitVec 32}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hz : z = 0#32)
    (hslt : (v.signExtend 32).slt z = true) : v = 0xFF#8 := by
  subst hz; rcases hdom with rfl | rfl | rfl <;> first | rfl | exact absurd hslt (by decide)

private theorem t4b_vals_zero_of_domain {v : BitVec 8} {z : BitVec 32}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hz : z = 0#32) (heq : v.signExtend 32 = z) :
    v = 0#8 := by
  subst hz; rcases hdom with rfl | rfl | rfl <;> first | rfl | exact absurd heq (by decide)

private theorem t4b_step_non_large {F_cur : List (List Nat)} {k : FullCoreState}
    {nl q lend nt : Nat} {qw : BitVec 32} (hq : q < lend) (hg : k.wstk[q]? = some qw)
    (hfl : (qw &&& 0x80000000#32) ≠ 0#32) (ht : TombWatchSliceOk F_cur k nl q (lend - q) nt) :
    ∃ nt2, TombWatchSliceOk F_cur k nl (q + 1) (lend - (q + 1)) nt2 := by
  have hs := ht.inv_step (by omega) hg; simp only [hfl, ↓reduceIte] at hs
  by_cases hq_t : qw = 0xFFFFFFFF#32 <;> simp only [hq_t, ↓reduceIte] at hs
  · exact ⟨nt - 1, by have hs2 := hs.2; rwa [show lend - q - 1 = lend - (q + 1) by omega] at hs2⟩
  · exact ⟨nt, by have hs3 := hs.2.2; rwa [show lend - q - 1 = lend - (q + 1) by omega] at hs3⟩

private theorem t4b_of_reduced0_full {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 : FullState} {src off p end_v : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (h : TransOuterInv c F0 F_cur s0 src off p end_v 0 st) :
    FullSparseInv c F0 st ∧ FullWitnessInv c F0 F_cur st.core :=
  have hcl : WatchSliceOk F_cur st.core src
      (fullWatchOffCore st.core src) (fullWatchSizeCore st.core src) := by
    rw [h.base.src_off, h.base.src_sz]; exact h.src_full_tomb.to_watchSlice
  ⟨h.base.toSparse hsp0 hw0 hcl, h.base.toWitness_of_src_clean hw0 hcl⟩

private theorem t4b_del_side_and_tomb {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 : FullState} {src off p end_v reduced dst : Nat}
    {st_r st' : FullState} {w0 : BitVec 32} {wvec' wstk' : List (BitVec 32)} {wu' tc' : BitVec 64}
    (hto : TransOuterInv c F0 F_cur s0 src off p end_v reduced st_r) (hp_lt : p < end_v)
    (hp_wc : p < c.wcap) (hs_lt : src < 2 * st_r.core.cur_vars)
    (hd_lt : dst < 2 * st_r.core.cur_vars) (hd_ne : dst ≠ src) (hget : st_r.core.wstk[p]? = some w0)
    (hfl : (w0 &&& 0x80000000#32) ≠ 0#32) (hst' : st' = { st_r with
      core := { st_r.core with wvec := wvec', wstk := wstk', wusable := wu' } })
    (hl' : st'.LengthsOk c) (hws : fullWatchOff st' dst = fullWatchOff st_r dst ∧
      fullWatchSize st' dst ≤ fullWatchSize st_r dst)
    (hows : ∀ l < 2 * st_r.core.cur_vars, l ≠ dst →
      fullWatchOff st' l = fullWatchOff st_r l ∧ fullWatchSize st' l = fullWatchSize st_r l)
    (hout : ∀ i < c.wcap, (i < fullWatchOff st_r dst ∨
      fullWatchOff st_r dst + fullWatchSize st_r dst ≤ i) → wstk'[i]? = st_r.core.wstk[i]?)
    (hsl : WatchSliceOk F_cur st_r.core dst (fullWatchOff st_r dst) (fullWatchSize st_r dst) →
      WatchSliceOk F_cur st'.core dst (fullWatchOff st' dst) (fullWatchSize st' dst)) :
    TransOuterInv c F0 F_cur s0 src off (p + 1) end_v (reduced + 1) { st' with
      core := { st'.core with wstk := wstk'.set p 0xFFFFFFFF#32 },
      scratch := { st_r.scratch with trans_cnt := tc' } } := by
  subst hst'
  have hp_out : p < fullWatchOff st_r dst ∨ fullWatchOff st_r dst + fullWatchSize st_r dst ≤ p := by
    by_cases hdz : fullWatchSize st_r dst = 0; · dsimp only [fullWatchSize] at hdz ⊢; omega
    rcases hto.base.disjoint_all src dst hs_lt hd_lt hd_ne.symm
        (by rw [hto.base.src_sz]; have := hto.off_le_p; omega) (Nat.pos_of_ne_zero hdz) with
      h1 | h2
    · left; have := hto.base.src_off; have := hto.base.src_sz; dsimp only [fullWatchOff]; omega
    · right; have := hto.off_le_p; have := hto.base.src_off
      dsimp only [fullWatchOff, fullWatchSize]; omega
  exact (hto.of_delete_bin_side hs_lt hd_lt hd_ne rfl hl' hws hows hout hsl).mark_tomb
    hp_lt hs_lt ((hout p hp_wc hp_out).trans hget) hfl

private theorem t4b_compact_done_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off end_v reduced : Nat} {wu' nb_bv : BitVec 64} {idx : Nat}
    {new_sz : BitVec 32} {st : FullState} (hsp0 : FullSparseInv c F0 s0)
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hb : TransOuterBase c F0 F_cur s0 src off end_v st)
    (hsrc_lt : src < 2 * st.core.cur_vars) (hred : reduced ≤ end_v - off)
    (hsl : WatchSliceOk F_cur st.core src off (end_v - off - reduced)) (hidx : idx = 2 * src + 1)
    (hsz : new_sz = BitVec.ofNat 32 (end_v - off - reduced)) :
    let st' := { st with core :=
      { st.core with wvec := st.core.wvec.set idx new_sz, wusable := wu', num_binary := nb_bv } }
    FullSparseInv c F0 st' ∧ FullWitnessInv c F0 F_cur st'.core := by
  subst hidx; subst hsz; have hnb : ((nb_bv.toNat : Nat) : BitVec 64) = nb_bv := by simp
  simpa only [hnb] using
    hb.of_compact_done_full hsp0 hw0 hsrc_lt hred hsl (wu' := wu') (nb' := nb_bv.toNat)

private theorem t4b_outer_with_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {src off p end_v reduced : Nat} (tk : BitVec 64)
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st) :
    TransOuterInv c F0 F_cur s0 src off p end_v reduced
      { st with scratch := { st.scratch with ant_sz := tk } } :=
  h.with_scratch { h.base.len_ok.scratch_ok with
    walk_vals_len := h.base.len_ok.scratch_ok.walk_vals_len } rfl rfl

private theorem t4b_unroll_with_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src saved : Nat} (tk : BitVec 64)
    (h : TransUnrollInv c F0 F_cur s0 st_pre src saved st) :
    TransUnrollInv c F0 F_cur s0
      { st_pre with scratch := { st_pre.scratch with ant_sz := tk } } src saved
      { st with scratch := { st.scratch with ant_sz := tk } } :=
  { len_ok := ⟨h.len_ok.core_ok,
      { h.len_ok.scratch_ok with walk_vals_len := h.len_ok.scratch_ok.walk_vals_len }⟩
    same_core := h.same_core
    same_scratch := by dsimp only; rw [h.same_scratch]
    saved_eq := h.saved_eq, saved_le_te := h.saved_le_te
    trl_pres := h.trl_pres, vals_pres := h.vals_pres, vals_hi_pres := h.vals_hi_pres
    bfs_trl_inv := h.bfs_trl_inv, bfs_vars_nodup := h.bfs_vars_nodup
    vals_only_trl := h.vals_only_trl }

private theorem t4b_unroll_c0_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st_r : FullState} {src saved : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (hlen_pre : st_pre.LengthsOk c) (hu_r : TransUnrollInv c F0 F_cur s0 st_pre src saved st_r)
    (hte_gt : saved < st_r.core.trail_end) (hte_r_lt : st_r.core.trail_end < 2 ^ 64) :
    let idx := (BitVec.ofNat 64 (BitVec.ofNat 64 st_r.core.trail_end - 1).toNat).toNat
    ∃ hidx : idx < st_r.core.trl.length, let ul := st_r.core.trl[idx]'hidx
      (BitVec.setWidth 64 ul).toNat < st_r.core.vals.length ∧
      (BitVec.setWidth 64 (ul ^^^ 1)).toNat < st_r.core.vals.length ∧
      (BitVec.ofNat 64 st_r.core.trail_end - 1).toNat = st_r.core.trail_end - 1 ∧
      TransUnrollInv c F0 F_cur s0 st_pre src saved { st_r with core := { st_r.core with
        vals := (st_r.core.vals.set (BitVec.setWidth 64 ul).toNat 0#8).set
          (BitVec.setWidth 64 (ul ^^^ 1)).toNat 0#8,
        trail_end := (BitVec.ofNat 64 st_r.core.trail_end - 1).toNat } } := by
  have hlen_r := hu_r.len_ok
  obtain ⟨ul, hul_get, hul_lt, hu_r'⟩ := hu_r.unroll_step hw0 hpre_vals hpre_cv hlen_pre hte_gt
  have hcv_r : st_pre.core.cur_vars ≤ c.max_vars := by
    have := hlen_r.core_ok.cur_vars_le; rw [hu_r.same_core] at this; exact this
  have hte1_bv := t4b_bv64_sub1 (n := st_r.core.trail_end) (by omega) hte_r_lt
  have hul_vlen := t4b_vals_lt (l := ul.toNat) hlen_r.core_ok (by rw [hu_r.same_core]; exact hul_lt)
  have huln_vlen := t4b_vals_lt (l := (ul ^^^ 1).toNat) hlen_r.core_ok
    (by rw [show (ul ^^^ 1).toNat = ul.toNat ^^^ 1 from ft_bv32_xor1 ul, hu_r.same_core]
        exact litNeg_lt_two_mul hul_lt)
  have hte1_len : (BitVec.ofNat 64 st_r.core.trail_end - 1).toNat < st_r.core.trl.length := by
    rw [hte1_bv, hlen_r.core_ok.trl_len]
    have := hlen_r.core_ok.trail_end_le; have := hlen_r.core_ok.cur_vars_le; omega
  have hte1_bv_len : (BitVec.ofNat 64 (BitVec.ofNat 64 st_r.core.trail_end - 1).toNat).toNat <
      st_r.core.trl.length := by simpa using hte1_len
  have hul_ge2 : st_r.core.trl[(BitVec.ofNat 64
      (BitVec.ofNat 64 st_r.core.trail_end - 1).toNat).toNat]'hte1_bv_len = ul := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)] using
      Option.some.inj ((List.getElem?_eq_getElem hte1_len).symm.trans (by rw [hte1_bv, hul_get]))
  exact ⟨hte1_bv_len, by rw [hul_ge2, ft_bv32_setWidth64]; exact hul_vlen,
    by rw [hul_ge2, ft_bv32_setWidth64]; exact huln_vlen, hte1_bv,
    by rw [hul_ge2, ft_bv32_setWidth64, ft_bv32_setWidth64, hte1_bv,
         show (ul ^^^ 1).toNat = ul.toNat ^^^ 1 from ft_bv32_xor1 ul]; exact hu_r'⟩

private theorem t4b_sparse_with_ws1 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {ws1' : List (BitVec 32)} (hsp : FullSparseInv c F0 s) (hlen : ws1'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with work_stk1 := ws1' } } := by
  refine ⟨⟨⟨hsp.1.lengths.core_ok, { hsp.1.lengths.scratch_ok with work_stk1_len := hlen }⟩,
    hsp.1.witness⟩, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩

private theorem t4b_ws1_set_lt {ws1 : List (BitVec 32)} {n k : Nat} {v : BitVec 32}
    (hkl : k < ws1.length) (hv : v.toNat < n)
    (hall : ∀ i < n, (ws1[i]?.getD 0#32).toNat < n) :
    ∀ i < n, ((ws1.set k v)[i]?.getD 0#32).toNat < n := by
  intro i hi
  by_cases hik : i = k
  · subst hik; rw [List.getElem?_set_self hkl, Option.getD_some]; exact hv
  · rw [List.getElem?_set_ne (Ne.symm hik)]; exact hall i hi

private theorem t4b_ws1_set_lt_bound {ws1 : List (BitVec 32)} {n cv k : Nat} {v : BitVec 32}
    (hkl : k < ws1.length) (hv : v.toNat < cv)
    (hall : ∀ i < n, (ws1[i]?.getD 0#32).toNat < cv) :
    ∀ i < n, ((ws1.set k v)[i]?.getD 0#32).toNat < cv := by
  intro i hi
  by_cases hik : i = k
  · subst hik; rw [List.getElem?_set_self hkl, Option.getD_some]; exact hv
  · rw [List.getElem?_set_ne (Ne.symm hik)]; exact hall i hi

end TransM6Helpers

/-! ## 3. `full_trans_lit_m6_wp` -/

section TransLitM6Proof

theorem full_trans_lit_m6_wp (Γ : Env)
    (h_del_bin : ∀ a m Q X, fullDeleteBinSideSpec a m Q X →
      Γ "full_delete_bin_side" [i64, i32, i32] [] a m Q X)
    (h_add_unit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullTransLitM6Spec a m Q X →
      Func.wp Γ full_trans_lit_m6_body a m Q X := by
  rintro ⟨h, src, stop_early, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hsrc_lt, hm, hQ⟩
  unfold Func.wp full_trans_lit_m6_body
  obtain ⟨F_cur, hw0⟩ := hsp.1.witness; have hlen0 := hsp.1.lengths
  have hsrc_vlen := t4b_vals_lt hlen0.core_ok hsrc_lt
  c0_hsplit
  · c0_hsteps; exact hQ true s m hsp hcl0 rfl rfl rfl (fun hf => absurd hf (by decide)) hm
  have hsrc0 : s.core.vals[src.toNat]?.getD 0#8 = 0#8 := t4b_vals_zero_of_domain (z := 0#32)
    (hw0.vals_domain src.toNat hsrc_lt) rfl
    (by rw [List.getElem?_eq_getElem hsrc_vlen]; exact hc)
  have hcv_lt : 2 * s.core.cur_vars < 2 ^ 32 := by have := (t4b_bnds hlen0.core_ok).1; omega
  have hsrc64 : (src.setWidth 64 <<< (1 : Nat)).toNat = 2 * src.toNat := by
    rw [ft_bv64_shl1 (by rw [ft_bv32_setWidth64]; omega), ft_bv32_setWidth64]
  have hsrc64_1 : ((src.setWidth 64 <<< (1 : Nat)) + 1).toNat = 2 * src.toNat + 1 := by
    rw [show (1 : BitVec 64) = 1#64 from rfl, ft_bv64_add1 (by rw [hsrc64]; omega), hsrc64]
  let off := fullWatchOff s src.toNat; let sz := fullWatchSize s src.toNat; let end_v := off + sz
  have hws_b : end_v ≤ s.core.wlen := by
    have hwm := hw0.watches; unfold ModeWatchesInv at hwm
    simp only [hsp.2.2.2.2, ↓reduceIte] at hwm; exact hwm.layout.bounds src.toNat hsrc_lt
  have hwv_b : 2 * src.toNat + 1 < s.core.wvec.length := by
    rw [hlen0.core_ok.wvec_len]; have := hlen0.core_ok.cur_vars_le; omega
  have hw0_b2 : 2 * src.toNat < s.core.wvec.length := by omega
  have hwc_lt : c.wcap < 2 ^ 64 := by have := c.hwcap; unfold dimacsBound at *; omega
  have hoff_lt : off < 2 ^ 32 := BitVec.isLt _; have hsz_lt : sz < 2 ^ 32 := BitVec.isLt _
  have hw0_b : (BitVec.setWidth 64 src <<< (1 : Nat)).toNat < s.core.wvec.length := by
    rw [hsrc64]; exact hw0_b2
  have hw1_b : (BitVec.setWidth 64 src <<< (1 : Nat) + 1).toNat < s.core.wvec.length := by
    rw [hsrc64_1]; exact hwv_b
  c0_hsplit
  · c0_hsteps; exact hQ true s m hsp hcl0 rfl rfl rfl (fun hf => absurd hf (by decide)) hm
  have hsz_pos : 0 < sz := by
    have hmod1 : (2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * src.toNat + 1 := by
      rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega)
    have hsz_eq : (s.core.wvec[(2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
        rw [hmod1]; exact hwv_b)).toNat = sz := by
      simp only [hmod1]; exact t4b_getElem_toNat hwv_b
    exact Nat.pos_of_ne_zero fun hz =>
      hc (BitVec.eq_of_toNat_eq (by rw [ft_bv32_setWidth64, hsz_eq, hz]; rfl))
  have hend_lt : end_v < 2 ^ 64 := by have := (t4b_bnds hlen0.core_ok).2.1; omega
  have hof64 : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h_off_arg : BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'
      hw0_b) = BitVec.ofNat 64 off := BitVec.eq_of_toNat_eq (by
    rw [ft_bv32_setWidth64, hof64]; simp only [hsrc64]; exact t4b_getElem_toNat hw0_b2)
  have h_sz_arg : BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat) + 1).toNat]'
      hw1_b) = BitVec.ofNat 64 sz := BitVec.eq_of_toNat_eq (by
    rw [ft_bv32_setWidth64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [hsrc64_1]; exact t4b_getElem_toNat hwv_b)
  have h_end_arg :
      (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'hw0_b) +
       BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat) + 1).toNat]'
         hw1_b)).toNat = end_v := by
    rw [h_off_arg, h_sz_arg, BitVec.toNat_add, hof64, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : sz < 2 ^ 64), Nat.mod_eq_of_lt hend_lt]
  c0_hsteps_nogrp
  -- Outer `while (p < end && !failed && h->ant_sz > 0)` with break join `(failed, reduced, p)`
  refine wp_loop_break_group (brkTs := [Ty.bool, i64, i64]) (lpTs := [Ty.bool, i64, i64])
    (BrkPost := fun xs m2 => let failed := xs.1; let reduced := xs.2.1; let p := xs.2.2.1
      ∃ st2 : FullState, off ≤ p.toNat ∧ p.toNat ≤ end_v ∧ reduced.toNat ≤ p.toNat - off ∧
        TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v reduced.toNat st2 ∧
        (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        st2.core.cur_vars = s.core.cur_vars ∧ st2.core.fuel = s.core.fuel ∧
        st2.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c st2 ⋆ R) m2)
    (Inv := fun n xs m1 => let failed := xs.1; let reduced := xs.2.1; let p := xs.2.2.1
      ∃ st : FullState, off ≤ p.toNat ∧ p.toNat ≤ end_v ∧ n = end_v - p.toNat ∧
        reduced.toNat ≤ p.toNat - off ∧
        TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v reduced.toNat st ∧
        (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        st.core.cur_vars = s.core.cur_vars ∧ st.core.fuel = s.core.fuel ∧
        st.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c st ⋆ R) m1) ?_ ?_ ?_
  · -- After outer loop breaks/exits: optional compaction + `if (failed) add_unit`
    rintro B ⟨failed, reduced, p, ⟨⟩⟩ m2
      ⟨st2, hp_lo2, hp_hi2, hred_le2, hto2, hfail2, hcv2, hfuel2, hws1_2, hm2⟩
    dsimp only at hp_lo2 hp_hi2 hred_le2 hto2 hfail2
    have hlen2 := hto2.base.len_ok
    refine wp_join_group (ts := [i64])
      (P := fun _ m3 => ∃ stf : FullState, FullSparseInv c F0 stf ∧
        FullWitnessInv c F0 F_cur stf.core ∧ stf.core.cur_level = 0 ∧
        stf.core.cur_vars = s.core.cur_vars ∧ stf.core.fuel = s.core.fuel ∧
        stf.scratch.work_stk1 = s.scratch.work_stk1 ∧
        (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        (FullMem c stf ⋆ R) m3) ?_ ?_
    · rintro J6 ⟨_, ⟨⟩⟩ m3 ⟨stf, hspf, hwf, hclf, hcvf, hfuelf, hws1f, hfailf, hm3⟩
      c0_hsplit
      · c0_hsteps_nogrp; c0_call h_add_unit
        obtain ⟨hsp_tc, hw_tc⟩ := fullSparseInv_with_trans_cnt hspf hwf
          (stf.scratch.trans_cnt + 1)
        refine ⟨c, F0, F_cur, _, R, rfl, hsp_tc.1.lengths, hw_tc, fun _ => hfailf hc,
          (by assumption),
          fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
            phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m4 hlen4 hw4 hcl4 huns4 _ hm4 => ?_⟩
        c0_hsteps
        let st_au : FullState := { stf with
          core := { stf.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop', cur_level := cl',
            unassigned := unass', unflushed := unfl', inconsistent := inc' },
          scratch := { stf.scratch with
            trans_cnt := stf.scratch.trans_cnt + 1, phases := phases', target_assigned := ta',
            best_assigned := ba', phases_target := pt', phases_best := pb', heap := hp', pos := ps',
            heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } }
        exact hQ ok st_au m4 (fullAddUnit_sparse hsp_tc rfl hlen4 hw4) hcl4 hcvf hfuelf hws1f
          (fun hok => (huns4 (by dsimp only [Arg.val_var] at *; omega) hok).1) hm4
      · c0_hsteps
        exact hQ true stf m3 hspf hclf hcvf hfuelf hws1f
          (fun h => absurd h (by decide)) hm3
    · intro J6 hJ6; c0_hsplit
      · have hred_pos : 0 < reduced.toNat := by c0_bound
        c0_hsteps_nogrp
        refine wp_loop_group (ts := [i64, i64])
          (Inv := fun nc xs m3 => let pc := xs.1; let qc := xs.2.1
            ∃ stc : FullState, off ≤ qc.toNat ∧ qc.toNat ≤ pc.toNat ∧ pc.toNat ≤ end_v ∧
              nc = end_v - pc.toNat ∧
              TransCompactInv c F0 F_cur s src.toNat off qc.toNat pc.toNat end_v reduced.toNat stc ∧
              stc.core.cur_vars = s.core.cur_vars ∧ stc.core.fuel = s.core.fuel ∧
              stc.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c stc ⋆ R) m3) ?_ ?_
        · rintro L8 nc ⟨pc, qc, ⟨⟩⟩ m3 hL8
            ⟨stc, hql, hqp, hpe, hcneq, hci, hcvc, hfuelc, hws1c, hm3⟩
          dsimp only at hql hqp hpe hcneq hci; have hlenc := hci.base.len_ok
          c0_hsplit
          · have hpc_lt : pc.toNat < end_v := by
              have h1 : pc.toNat < (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<<
                (1 : Nat)).toNat]'hw0_b) + BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src
                <<< (1 : Nat) + 1).toNat]'hw1_b)).toNat := by c0_bound
              rwa [h_end_arg] at h1
            have hpc_len := t4b_wstk_lt hlenc.core_ok hpc_lt hci.base.end_le_wlen
            have hpc1 : (pc + 1#64).toNat = pc.toNat + 1 := ft_bv64_add1 (by omega)
            c0_hsteps_nogrp; refine wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · have ht_pc : stc.core.wstk[pc.toNat]? = some 0xFFFFFFFF#32 := by
                rw [List.getElem?_eq_getElem hpc_len]; exact congrArg some hc
              c0_hsteps
              exact hL8 (end_v - (pc.toNat + 1)) (pc + 1#64, qc, ()) m3 (by omega)
                ⟨stc, hql, by dsimp only; rw [hpc1]; omega, by dsimp only; rw [hpc1]; omega,
                 by dsimp only; rw [hpc1],
                 by dsimp only; rw [hpc1]; exact hci.step_tomb hpc_lt ht_pc rfl,
                 hcvc, hfuelc, hws1c, hm3⟩
            · have hne_c : stc.core.wstk[pc.toNat] ≠ 0xFFFFFFFF#32 := hc
              have hsrc_c : src.toNat < 2 * stc.core.cur_vars := by rw [hcvc]; exact hsrc_lt
              c0_hsteps_nogrp; refine wp_unroll_group fun _ _ => ?_
              c0_hsplit
              · have hfl_c : (stc.core.wstk[pc.toNat] &&& 0x80000000#32) ≠ 0#32 := hc
                have hqc1 : (qc + 1#64).toNat = qc.toNat + 1 := ft_bv64_add1 (by omega)
                have hci_b := hci.step_bin hpc_lt hsrc_c (List.getElem?_eq_getElem hpc_len)
                  hne_c hfl_c
                rw [← hpc1, ← hqc1] at hci_b; c0_hsteps
                exact hL8 (end_v - (pc.toNat + 1)) (pc + 1#64, qc + 1#64, ()) _ (by omega)
                  ⟨_, by dsimp only; rw [hqc1]; omega, by dsimp only; rw [hpc1, hqc1]; omega,
                   by dsimp only; rw [hpc1]; omega, by dsimp only; rw [hpc1],
                   hci_b, hcvc, hfuelc, hws1c, (by assumption)⟩
              · have hfl0 : (stc.core.wstk[pc.toNat] &&& 0x80000000#32) = 0#32 := hc
                obtain ⟨hp1_lt, w1, hw1_get, hci_l⟩ :=
                  hci.step_large hpc_lt hsrc_c (List.getElem?_eq_getElem hpc_len) hfl0
                c0_hsteps_nogrp; refine wp_unroll_group fun _ _ => ?_
                c0_hsplit
                · have hpc2 := ft_bv64_add2 (by omega : pc.toNat + 2 < 2 ^ 64)
                  have hqc2 := ft_bv64_add2 (by omega : qc.toNat + 2 < 2 ^ 64)
                  have hqc1 := ft_bv64_add1 (by omega : qc.toNat + 1 < 2 ^ 64)
                  have hpc1_len := t4b_wstk_lt (p := (pc + 1#64).toNat) hlenc.core_ok
                    (by rw [hpc1]; exact hp1_lt) hci.base.end_le_wlen
                  have hqc1_len := t4b_wstk_lt (p := (qc + 1#64).toNat) hlenc.core_ok
                    (by rw [hqc1]; exact Nat.lt_of_lt_of_le (by omega) hp1_lt) hci.base.end_le_wlen
                  c0_hsteps
                  have hw1_hm : (stc.core.wstk.set qc.toNat stc.core.wstk[pc.toNat])[(pc +
                      1#64).toNat]'(by rw [List.length_set]; exact hpc1_len) = w1 := by
                    rw [List.getElem_set_ne (by omega : qc.toNat ≠ (pc + 1#64).toNat)]
                    exact Option.some.inj
                      ((List.getElem?_eq_getElem hpc1_len).symm.trans (by rw [hpc1, hw1_get]))
                  rw [← hpc2, ← hqc2, ← hqc1, ← hw1_hm] at hci_l
                  exact hL8 (end_v - (pc.toNat + 2)) (pc + 2#64, qc + 2#64, ()) _ (by omega)
                    ⟨_, by dsimp only; rw [hqc2]; omega, by dsimp only; rw [hpc2, hqc2]; omega,
                     by dsimp only; rw [hpc2]; omega, by dsimp only; rw [hpc2], hci_l, hcvc,
                     hfuelc, hws1c, (by assumption)⟩
                · exfalso
                  have h1 : ¬((pc + 1#64).toNat < (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth
                    64 src <<< (1 : Nat)).toNat]'hw0_b) + BitVec.setWidth 64 (s.core.wvec[
                    (BitVec.setWidth 64 src <<< (1 : Nat) + 1).toNat]'hw1_b)).toNat) := by c0_bound
                  rw [h_end_arg, hpc1] at h1; exact h1 hp1_lt
          · have hpc_end : pc.toNat = end_v := by
              have h1 : ¬(pc.toNat < (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<<
                (1 : Nat)).toNat]'hw0_b) + BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src
                <<< (1 : Nat) + 1).toNat]'hw1_b)).toNat) := by c0_bound
              rw [h_end_arg] at h1; omega
            rw [hpc_end] at hci; obtain ⟨hq_eq, hq_lo, hq_hi, hsl⟩ := hci.at_end
            c0_hsteps_nogrp
            refine wp_loop_group (ts := [i64])
              (Inv := fun nq xs m4 => let qf := xs.1
                ∃ stq : FullState, off ≤ end_v - reduced.toNat ∧ end_v - reduced.toNat ≤ qf.toNat ∧
                  qf.toNat ≤ end_v ∧ nq = end_v - qf.toNat ∧
                  TransOuterBase c F0 F_cur s src.toNat off end_v stq ∧
                  WatchSliceOk F_cur stq.core src.toNat off (end_v - off - reduced.toNat) ∧
                  stq.core.cur_vars = s.core.cur_vars ∧ stq.core.fuel = s.core.fuel ∧
                  stq.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c stq ⋆ R) m4) ?_ ?_
            · rintro L11 nq ⟨qf, ⟨⟩⟩ m4 hL11
                ⟨stq, hqo, hql2, hqh, hqneq, hbq, hslq, hcvq, hfuelq, hws1q, hm4⟩
              dsimp only at hqo hql2 hqh hqneq hbq hslq; have hlenq := hbq.len_ok
              have hsrc_q : src.toNat < 2 * stq.core.cur_vars := by rw [hcvq]; exact hsrc_lt
              c0_hsplit
              · have hq_lt : qf.toNat < end_v := by
                  have h1 : qf.toNat < (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<<
                    (1 : Nat)).toNat]'hw0_b) + BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
                    src <<< (1 : Nat) + 1).toNat]'hw1_b)).toNat := by c0_bound
                  rwa [h_end_arg] at h1
                have hqf_len := t4b_wstk_lt hlenq.core_ok hq_lt hbq.end_le_wlen
                c0_hsteps
                have hq1 : (qf + 1#64).toNat = qf.toNat + 1 := ft_bv64_add1 (by omega)
                obtain ⟨hbq', hslq'⟩ := hbq.sentinel_fill_step hsrc_q ⟨hqo, hql2, hq_lt⟩
                  (by rwa [show (end_v - reduced.toNat) - off = end_v - off - reduced.toNat by
                    omega])
                exact hL11 (end_v - (qf.toNat + 1)) (qf + 1#64, ()) _ (by omega) ⟨_, hqo,
                  by dsimp only; rw [hq1]; omega, by dsimp only; rw [hq1]; omega,
                  by dsimp only; rw [hq1], hbq', by simpa only [(show end_v - reduced.toNat - off =
                    end_v - off - reduced.toNat by omega)] using hslq',
                  hcvq, hfuelq, hws1q, (by assumption)⟩
              · have hred_off : reduced.toNat ≤ end_v - off := by omega
                have hq_wv1 : (BitVec.setWidth 64 src <<< (1 : Nat) + 1).toNat <
                    stq.core.wvec.length := by
                  rw [hsrc64_1, hlenq.core_ok.wvec_len, ← hlen0.core_ok.wvec_len]; exact hwv_b
                have hclq : stq.core.cur_level = 0 := hbq.core_pres.2.1
                have h_wsz_bv : BitVec.setWidth 32
                    (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<<
                      (1 : Nat)).toNat]'hw0_b) +
                     BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<<
                      (1 : Nat) + 1).toNat]'hw1_b) -
                     BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<<
                      (1 : Nat)).toNat]'hw0_b) - reduced) =
                    BitVec.ofNat 32 (end_v - off - reduced.toNat) := by
                  have hb : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<<
                      (1 : Nat) + 1).toNat]'hw1_b)).toNat = sz := by
                    rw [ft_bv32_setWidth64]; simp only [hsrc64_1]; exact t4b_getElem_toNat hwv_b
                  rw [show end_v - off = sz from Nat.add_sub_cancel_left off sz]
                  exact t4b_bv64_sub_sz _ _ reduced hb rfl (by omega) (by omega)
                c0_hsteps_nogrp; refine wp_unroll_group fun _ _ => ?_
                c0_hsplit
                · c0_hsteps
                  obtain ⟨hsp_d, hw_d⟩ := t4b_compact_done_eq hsp hw0 hbq hsrc_q hred_off hslq
                    (wu' := stq.core.wusable + reduced) (nb_bv := stq.core.num_binary - reduced)
                    hsrc64_1 h_wsz_bv
                  exact hJ6 (pc, ()) _ ⟨_, hsp_d, hw_d, hclq, hcvq, hfuelq, hws1q, hfail2,
                    (by assumption)⟩
                · c0_hsteps
                  obtain ⟨hsp_d, hw_d⟩ := t4b_compact_done_eq hsp hw0 hbq hsrc_q hred_off hslq
                    (wu' := stq.core.wusable + reduced) (nb_bv := stq.core.num_binary)
                    hsrc64_1 h_wsz_bv
                  exact hJ6 (pc, ()) _ ⟨_, hsp_d, hw_d, hclq, hcvq, hfuelq, hws1q, hfail2,
                    (by assumption)⟩
            · intro L11 hL11; c0_hsteps
              exact hL11 (end_v - qc.toNat) (qc, ()) m3 ⟨stc, hq_lo,
                by dsimp only; rw [hq_eq]; exact Nat.le_refl _,
                by dsimp only; rw [hq_eq]; exact hq_hi, rfl, hci.base, hsl, hcvc, hfuelc, hws1c,
                hm3⟩
        · intro L8 hL8; c0_hsteps; rw [h_off_arg]
          exact hL8 (end_v - off) (BitVec.ofNat 64 off, BitVec.ofNat 64 off, ()) m2 ⟨st2,
            (by dsimp only; rw [hof64]; exact Nat.le_refl _),
            (by dsimp only; rw [hof64]; exact Nat.le_refl _),
            by dsimp only; rw [hof64]; exact hto2.base.off_le_end, by dsimp only; rw [hof64],
            by dsimp only; rw [hof64]; exact TransCompactInv.init hto2, hcv2, hfuel2, hws1_2, hm2⟩
      · have hred0 : reduced.toNat = 0 := by c0_bound
        c0_hsteps; rw [hred0] at hto2
        obtain ⟨hsp2, hw2⟩ := t4b_of_reduced0_full hsp hw0 hto2
        exact hJ6 (p, ()) m2 ⟨st2, hsp2, hw2, hto2.base.core_pres.2.1, hcv2, hfuel2, hws1_2,
          hfail2, hm2⟩
  · -- Outer loop body
    rintro B L n ⟨failed, reduced, p, ⟨⟩⟩ m1 hB hL
      ⟨st, hp_lo, hp_hi, hneq, hred_le, hto, hfail_ent, hcv_st, hfuel_st, hws1_st, hm1⟩
    dsimp only at hp_lo hp_hi hneq hred_le hto hfail_ent
    have hlen_st := hto.base.len_ok
    have hst_cv_lt : st.core.cur_vars < 2 ^ 32 := by rw [hcv_st]; omega
    have hB_now : B (failed, reduced, p, ()) m1 :=
      hB (failed, reduced, p, ()) m1 ⟨st, hp_lo, hp_hi, hred_le, hto, hfail_ent, hcv_st, hfuel_st,
        hws1_st, hm1⟩
    c0_hsplit
    · have hp_lt : p.toNat < end_v := by
        have h1 : p.toNat < (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<<
          (1 : Nat)).toNat]'hw0_b) + BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<<
          (1 : Nat) + 1).toNat]'hw1_b)).toNat := by c0_bound
        rwa [h_end_arg] at h1
      c0_hsplit
      · c0_hsteps; exact hB_now
      · have hfail_f : failed = false := by revert hc; cases failed <;> decide
        c0_hsplit
        · have hp_len := t4b_wstk_lt hlen_st.core_ok hp_lt hto.base.end_le_wlen
          c0_hsplit
          · -- Large watch `(w0 & PW_BIN_FLAG) == 0`
            have hfl0 : (st.core.wstk[p.toNat] &&& 0x80000000#32) = 0#32 := hc
            obtain ⟨hp2, hto2⟩ := hto.skip_large hp_lt (List.getElem?_eq_getElem hp_len) hfl0
            c0_hsplit
            · c0_hsteps; exact hB_now
            · c0_hsteps
              have hp2_bv : (p + 2#64).toNat = p.toNat + 2 := ft_bv64_add2 (by omega)
              exact hL (end_v - (p.toNat + 2)) (failed, reduced, p + 2#64, ()) m1 (by omega) ⟨st,
                by dsimp only; rw [hp2_bv]; omega, by dsimp only; rw [hp2_bv]; omega,
                by dsimp only; rw [hp2_bv], by dsimp only; rw [hp2_bv]; omega,
                by dsimp only; rw [hp2_bv]; exact hto2, hfail_ent, hcv_st, hfuel_st, hws1_st, hm1⟩
          · -- Binary watch `(w0 & PW_BIN_FLAG) ≠ 0`
            have hfl_nz : (st.core.wstk[p.toNat] &&& 0x80000000#32) ≠ 0#32 := hc
            obtain ⟨hw0_ne, hdst_lt_st, hdst_ent, hto_skip⟩ :=
              hto.skip_bin hp_lt (List.getElem?_eq_getElem hp_len) hfl_nz
            let w0 := st.core.wstk[p.toNat]'hp_len; let dst := w0 &&& 0x7FFFFFFF#32
            have hdst_lt0 : dst.toNat < 2 * s.core.cur_vars := by rw [← hcv_st]; exact hdst_lt_st
            c0_hsteps_nogrp
            refine wp_join_group (ts := [])
              (P := fun _ m2 => ∃ st_s : FullState,
                TransOuterInv c F0 F_cur s src.toNat off (p.toNat + 1) end_v reduced.toNat st_s ∧
                (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
                st_s.core.cur_vars = s.core.cur_vars ∧ st_s.core.fuel = s.core.fuel ∧
                st_s.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c st_s ⋆ R) m2) ?_ ?_
            · rintro J9 ⟨⟩ m2 ⟨st_s, hto_s, hfail_s, hcv_s, hfuel_s, hws1_s, hm2⟩; c0_hsteps
              have hp1_bv : (p + 1#64).toNat = p.toNat + 1 := ft_bv64_add1 (by omega)
              exact hL (end_v - (p.toNat + 1)) (failed, reduced, p + 1#64, ()) m2 (by omega) ⟨st_s,
                by dsimp only; rw [hp1_bv]; omega, by dsimp only; rw [hp1_bv]; omega,
                by dsimp only; rw [hp1_bv], by dsimp only; rw [hp1_bv]; omega,
                by dsimp only; rw [hp1_bv]; exact hto_s, hfail_s, hcv_s, hfuel_s, hws1_s, hm2⟩
            · intro J9 hJ9
              c0_hsplit
              · c0_hsteps
                exact hJ9 () m1 ⟨st, hto_skip, hfail_ent, hcv_st, hfuel_st, hws1_st, hm1⟩
              c0_hsplit
              · c0_hsteps
                exact hJ9 () m1 ⟨st, hto_skip, hfail_ent, hcv_st, hfuel_st, hws1_st, hm1⟩
              have hdst_ne : dst.toNat ≠ src.toNat := by
                dsimp only [dst, w0]
                have hgt : ¬((st.core.wstk[p.toNat]'hp_len &&& 0x7FFFFFFF#32).toNat ≤
                    src.toNat) := by c0_bound
                omega
              have hdst_vlen := t4b_vals_lt hlen_st.core_ok hdst_lt_st
              c0_hsplit
              · c0_hsteps
                exact hJ9 () m1 ⟨st, hto_skip, hfail_ent, hcv_st, hfuel_st, hws1_st, hm1⟩
              let not_src := src ^^^ 1#32
              have hnot_eq : not_src.toNat = src.toNat ^^^ 1 := ft_bv32_xor1 src
              have hnot_lt : not_src.toNat < 2 * st.core.cur_vars := by
                rw [hnot_eq, hcv_st]; exact litNeg_lt_two_mul hsrc_lt
              have hnot_vlen := t4b_vals_lt hlen_st.core_ok hnot_lt
              have hpre_vals := hto.base.core_pres.2.2.2.2.2.2.2.2.2.2.1
              have hpre_te := hto.base.core_pres.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              have hpre_trl := hto.base.core_pres.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              let saved := st.core.trail_end
              obtain ⟨hsaved_lt, hu1, hte1⟩ := TransUnrollInv.init (st_pre := st) hw0 hlen_st
                hpre_vals hpre_te hcv_st (by rw [hcv_st]; exact hsrc_lt)
                (by rw [hpre_vals]; exact hsrc0)
              have hte_len : saved < st.core.trl.length := by
                rw [hlen_st.core_ok.trl_len]
                exact Nat.lt_of_lt_of_le hsaved_lt hlen_st.core_ok.cur_vars_le
              have hbv_not : BitVec.ofNat 32 (src.toNat ^^^ 1) = not_src := BitVec.eq_of_toNat_eq
                (by rw [hnot_eq, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
              have hsrc64_vlen : (BitVec.setWidth 64 src).toNat < st.core.vals.length := by
                rw [ft_bv32_setWidth64, hlen_st.core_ok.vals_len, ← hlen0.core_ok.vals_len]
                exact hsrc_vlen
              have hsav_lt := (t4b_bnds hlen_st.core_ok).2.2.2
              have hs_eq : (BitVec.ofNat 64 saved).toNat = saved := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsav_lt]
              have hte64_len : (BitVec.ofNat 64 st.core.trail_end).toNat < st.core.trl.length := by
                rw [show st.core.trail_end = saved from rfl, hs_eq]; exact hte_len
              have hnot64_vlen : (BitVec.setWidth 64 not_src).toNat < st.core.vals.length := by
                rw [ft_bv32_setWidth64]; exact hnot_vlen
              have hte_p1 : (BitVec.ofNat 64 st.core.trail_end + 1).toNat = saved + 1 := by
                rw [show (1 : BitVec 64) = 1#64 from rfl, ft_bv64_add1 (by rw [hs_eq]; omega),
                  hs_eq]
              c0_hsteps_nogrp
              -- BFS loop `[Ty.bool, i64, i64, Ty.bool]` = `(fb, ticks, prop, tb)`
              refine wp_loop_group (ts := [Ty.bool, i64, i64, Ty.bool])
                (Inv := fun nb xs m2 =>
                  let fb := xs.1; let _tk := xs.2.1; let prop := xs.2.2.1; let tb := xs.2.2.2.1
                  ∃ st_b : FullState, saved ≤ prop.toNat ∧ prop.toNat ≤ st_b.core.trail_end ∧
                    nb = st.core.cur_vars - prop.toNat ∧
                    TransUnrollInv c F0 F_cur s st src.toNat saved st_b ∧ ¬(fb = true ∧ tb = true) ∧
                    (fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
                    (tb = true → (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [src.toNat, dst.toNat])) ∧
                    (FullMem c st_b ⋆ R) m2) ?_ ?_
              · rintro L13 nb ⟨fb, tk, prop, tb, ⟨⟩⟩ m2 hL13
                  ⟨st_b, hsp_le, hpt_le, hbneq, hu_b, hntf, hfb, htb, hm2⟩
                dsimp only at hsp_le hpt_le hbneq hntf hfb htb; have hlen_b := hu_b.len_ok
                -- Exit BFS join `J15` (`[]`): store `h->ant_sz = tk`, unroll, optional delete
                refine wp_join_group (ts := [])
                  (P := fun _ m3 => ∃ st_u : FullState,
                    TransUnrollInv c F0 F_cur s st src.toNat saved st_u ∧
                    ¬(fb = true ∧ tb = true) ∧
                    (fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
                    (tb = true → (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [src.toNat, dst.toNat])) ∧
                    (FullMem c st_u ⋆ R) m3) ?_ ?_
                · rintro J15 ⟨⟩ m3 ⟨st_u, hu_u, hntf_u, hfb_u, htb_u, hm3⟩
                  c0_hsteps_nogrp
                  let st_pre2 : FullState := { st with scratch := { st.scratch with ant_sz := tk } }
                  let st_u2 : FullState :=
                    { st_u with scratch := { st_u.scratch with ant_sz := tk } }
                  have hto_pre2 := t4b_outer_with_ant_sz tk hto
                  have hu_u2 : TransUnrollInv c F0 F_cur s st_pre2 src.toNat saved st_u2 :=
                    t4b_unroll_with_ant_sz tk hu_u
                  refine wp_loop_group (ts := []) (Inv := fun nu _ m4 => ∃ st_r : FullState,
                      nu = st_r.core.trail_end - saved ∧
                      TransUnrollInv c F0 F_cur s st_pre2 src.toNat saved st_r ∧
                      (FullMem c st_r ⋆ R) m4) ?_ ?_
                  · rintro L17 nu ⟨⟩ m4 hL17 ⟨st_r, huneq, hu_r, hm4⟩
                    have hlen_r := hu_r.len_ok
                    have hte_r_lt : st_r.core.trail_end < 2 ^ 64 := (t4b_bnds hlen_r.core_ok).2.2.2
                    c0_hsplit
                    · have hte_gt : saved < st_r.core.trail_end := by
                        have h1 : saved % 2 ^ 64 < st_r.core.trail_end % 2 ^ 64 := by c0_bound
                        rwa [Nat.mod_eq_of_lt hsav_lt, Nat.mod_eq_of_lt hte_r_lt] at h1
                      obtain ⟨hte1_bv_len, hul_sw_bv, huln_sw_bv, hte1_bv, hu_r''⟩ :=
                        t4b_unroll_c0_aux (st_pre := st_pre2) hw0 hpre_vals hcv_st
                          hto_pre2.base.len_ok hu_r hte_gt hte_r_lt
                      have huln_sw_set : (BitVec.setWidth 64 (st_r.core.trl[(BitVec.ofNat 64
                          (BitVec.ofNat 64 st_r.core.trail_end - 1).toNat).toNat]'hte1_bv_len ^^^
                          1)).toNat < (st_r.core.vals.set (BitVec.setWidth 64 (st_r.core.trl[
                          (BitVec.ofNat 64 (BitVec.ofNat 64 st_r.core.trail_end - 1).toNat).toNat]'
                          hte1_bv_len)).toNat 0#8).length := by
                        rw [List.length_set]; exact huln_sw_bv
                      c0_hsteps
                      exact hL17 (st_r.core.trail_end - 1 - saved) () _ (by omega)
                        ⟨_, by dsimp only; rw [hte1_bv], hu_r'', (by assumption)⟩
                    · have hte_eq : st_r.core.trail_end = saved := by
                        have h1 : ¬(saved % 2 ^ 64 < st_r.core.trail_end % 2 ^ 64) := by c0_bound
                        rw [Nat.mod_eq_of_lt hsav_lt, Nat.mod_eq_of_lt hte_r_lt] at h1
                        have := hu_r.saved_le_te; omega
                      have hto_done := hu_r.done hto_pre2 hte_eq
                      have hp1_bv : (p + 1#64).toNat = p.toNat + 1 := ft_bv64_add1 (by omega)
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [i64]) (P := fun xs m5 => let red' := xs.1
                          ∃ st_d : FullState, red'.toNat ≤ p.toNat + 1 - off ∧
                            TransOuterInv c F0 F_cur s src.toNat off (p.toNat + 1) end_v
                              red'.toNat st_d ∧
                            st_d.core.cur_vars = s.core.cur_vars ∧ st_d.core.fuel = s.core.fuel ∧
                            st_d.scratch.work_stk1 = s.scratch.work_stk1 ∧
                            (FullMem c st_d ⋆ R) m5) ?_ ?_
                      · rintro J20 ⟨red', ⟨⟩⟩ m5 ⟨st_d, hrl_d, hto_d, hcv_d, hfuel_d, hws1_d, hm5⟩
                        c0_hsteps
                        exact hL (end_v - (p.toNat + 1)) (fb, red', p + 1#64, ()) m5 (by omega)
                          ⟨st_d, (by dsimp only; rw [hp1_bv]; omega),
                           (by dsimp only; rw [hp1_bv]; omega), (by dsimp only; rw [hp1_bv]),
                           (by dsimp only; rw [hp1_bv]; exact hrl_d),
                           (by dsimp only; rw [hp1_bv]; exact hto_d),
                           fun hf => hfb_u hf, hcv_d, hfuel_d, hws1_d, hm5⟩
                      · intro J20 hJ20
                        have hget_r : st_r.core.wstk[p.toNat]? = some w0 := by
                          rw [hu_r.same_core, List.getElem?_eq_getElem hp_len]
                        c0_hsplit
                        · c0_hsteps_nogrp; c0_call h_del_bin
                          have hdst_lt_d : dst.toNat < 2 * st_r.core.cur_vars := by
                            rw [hu_r.same_core, hcv_st]; exact hdst_lt0
                          have hsrc_lt_d : src.toNat < 2 * st_r.core.cur_vars := by
                            rw [hu_r.same_core, hcv_st]; exact hsrc_lt
                          refine ⟨c, st_r, R, rfl, hlen_r,
                            fun _ => hto_done.base.other_bounds dst.toNat hdst_lt_d hdst_ne, hm4,
                            fun wvec' wstk' wu' m5 hlen5 hdst_ws hother_ws hwstk_out hdst_sl
                              _ _ _ hm5 => ?_⟩
                          have hp_wc : p.toNat < c.wcap := by
                            have := hto_done.base.end_le_wlen
                            have := hlen_r.core_ok.wlen_le; omega
                          have hred1 : (reduced + 1#64).toNat = reduced.toNat + 1 :=
                            ft_bv64_add1 (by have := hto_done.base.end_le_wlen
                                             have := hlen_r.core_ok.wlen_le; omega)
                          have hto_mk := t4b_del_side_and_tomb hto_done hp_lt hp_wc hsrc_lt_d
                            hdst_lt_d hdst_ne hget_r hfl_nz rfl hlen5
                            (by dsimp only [dst, w0, Arg.val_var] at *; exact hdst_ws hdst_lt_d)
                            hother_ws
                            (fun idx hidx ho => hwstk_out idx hidx
                              (fun _ => by dsimp only [dst, w0, Arg.val_var] at *; exact ho))
                            (by dsimp only [dst, w0, Arg.val_var] at *; exact hdst_sl F_cur)
                            (tc' := st_r.scratch.trans_cnt + 1)
                          have hp_l5 : p.toNat < wstk'.length := by
                            rw [hlen5.core_ok.wstk_len_arr]; omega
                          c0_hsteps
                          exact hJ20 (reduced + 1#64, ()) _ ⟨_, by rw [hred1]; omega,
                            by rw [hred1]; exact hto_mk, by dsimp only; rw [hu_r.same_core, hcv_st],
                            by dsimp only; rw [hu_r.same_core, hfuel_st],
                            by dsimp only; rw [hu_r.same_scratch]; exact hws1_st, (by assumption)⟩
                        · obtain ⟨_, _, _, hto_nxt⟩ := hto_done.skip_bin hp_lt hget_r hfl_nz
                          c0_hsteps
                          exact hJ20 (reduced, ()) m4 ⟨st_r, by dsimp only; omega, hto_nxt,
                            by rw [hu_r.same_core, hcv_st], by rw [hu_r.same_core, hfuel_st],
                            by rw [hu_r.same_scratch]; exact hws1_st, hm4⟩
                  · intro L17 hL17; c0_hsteps
                    exact hL17 (st_u2.core.trail_end - saved) () _
                      ⟨st_u2, rfl, hu_u2, (by assumption)⟩
                · -- BFS loop body
                  intro J15 hJ15
                  have hJ15_now : J15 () m2 := hJ15 () m2 ⟨st_b, hu_b, hntf, hfb, htb, hm2⟩
                  c0_hsplit
                  · c0_hsteps; exact hJ15_now
                  have htb_f : tb = false := by revert hc; cases tb <;> decide
                  c0_hsplit
                  · c0_hsteps; exact hJ15_now
                  have hfb_f : fb = false := by revert hc; cases fb <;> decide
                  c0_hsplit
                  · have hte_b_lt := (t4b_bnds hlen_b.core_ok).2.2.2
                    have hcv_b_le := hlen_b.core_ok.cur_vars_le
                    have hpt_lt : prop.toNat < st_b.core.trail_end := by
                      have h1 : prop.toNat < st_b.core.trail_end % 2 ^ 64 := by c0_bound
                      rwa [Nat.mod_eq_of_lt hte_b_lt] at h1
                    c0_hsplit
                    · have hprop_tlen : prop.toNat < st_b.core.trl.length := by
                        rw [hlen_b.core_ok.trl_len]; have := hlen_b.core_ok.trail_end_le; omega
                      have hprop1 := ft_bv64_add1 (by omega : prop.toNat + 1 < 2 ^ 64)
                      obtain ⟨lit, hlit_get, hlit_lt, _, _, _, hent_lit⟩ :=
                        hu_b.bfs_trl_inv prop.toNat hsp_le hpt_lt
                      let nl := lit ^^^ 1#32; have hnl_eq := ft_bv32_xor1 lit
                      have hnl_lt : nl.toNat < 2 * st_b.core.cur_vars := by
                        rw [hnl_eq, hu_b.same_core]; exact litNeg_lt_two_mul hlit_lt
                      have hlit_ge : st_b.core.trl[prop.toNat]'hprop_tlen = lit :=
                        Option.some.inj ((List.getElem?_eq_getElem hprop_tlen).symm.trans hlit_get)
                      have hnl_shl : (BitVec.setWidth 64 (lit ^^^ 1) <<< (1 : Nat)).toNat =
                          2 * nl.toNat := by
                        rw [ft_bv64_shl1 (by rw [ft_bv32_setWidth64]; omega), ft_bv32_setWidth64]
                        rfl
                      have hnl_wv0 : (BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^
                          1) <<< (1 : Nat)).toNat < st_b.core.wvec.length := by
                        rw [hlit_ge, hnl_shl, hlen_b.core_ok.wvec_len]; omega
                      have hnl_wv1 : ((BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^
                          1) <<< (1 : Nat)) + 1).toNat < st_b.core.wvec.length := by
                        rw [hlit_ge, show (1 : BitVec 64) = 1#64 from rfl,
                          ft_bv64_add1 (by rw [hnl_shl]; omega), hnl_shl, hlen_b.core_ok.wvec_len]
                        omega
                      obtain ⟨hnl_bnd, nt0, htomb0⟩ := hu_b.watch_slice hto hnl_lt
                      let loff := fullWatchOffCore st_b.core nl.toNat
                      let lsz := fullWatchSizeCore st_b.core nl.toNat; let lend := loff + lsz
                      have hloff_lt : loff < 2 ^ 64 := by
                        have := (t4b_bnds hlen_b.core_ok).2.2.1; omega
                      have hlo_eq : (BitVec.ofNat 64 loff).toNat = loff := by
                        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hloff_lt]
                      have hlo_arg : BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth 64
                          (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1) <<< (1 : Nat)).toNat]'
                          hnl_wv0) = BitVec.ofNat 64 loff := by
                        apply BitVec.eq_of_toNat_eq; rw [ft_bv32_setWidth64, hlo_eq]
                        have hidx2 : (BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^
                            1) <<< (1 : Nat)).toNat = 2 * nl.toNat := by
                          simpa [hlit_ge] using hnl_shl
                        have hnl0 : 2 * nl.toNat < st_b.core.wvec.length := by
                          rw [← hidx2]; exact hnl_wv0
                        simp only [hidx2]; exact t4b_getElem_toNat hnl0
                      have hls_arg : BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth 64
                          (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1) <<< (1 : Nat) + 1).toNat]'
                          hnl_wv1) = BitVec.ofNat 64 lsz := by
                        apply BitVec.eq_of_toNat_eq
                        rw [ft_bv32_setWidth64, BitVec.toNat_ofNat,
                          Nat.mod_eq_of_lt (by have := (t4b_bnds hlen_b.core_ok).2.2.1; omega)]
                        have hidx3 : (BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^
                            1) <<< (1 : Nat) + 1).toNat = 2 * nl.toNat + 1 := by
                          rw [hlit_ge, show (1 : BitVec 64) = 1#64 from rfl,
                            ft_bv64_add1 (by rw [hnl_shl]; omega), hnl_shl]
                        have hnl1 : 2 * nl.toNat + 1 < st_b.core.wvec.length := by
                          rw [← hidx3]; exact hnl_wv1
                        simp only [hidx3]; exact t4b_getElem_toNat hnl1
                      have hlend_arg : (BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth 64
                          (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1) <<< (1 : Nat)).toNat]'
                          hnl_wv0) + BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth 64
                          (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1) <<< (1 : Nat) + 1).toNat]'
                          hnl_wv1)).toNat = lend := by
                        have := (t4b_bnds hlen_b.core_ok).2.2.1
                        rw [hlo_arg, hls_arg, BitVec.toNat_add, hlo_eq, BitVec.toNat_ofNat,
                          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                      c0_hsteps_nogrp
                      -- Inner watch loop: `brkTs = [bool, i64, bool, i64]`, `lpTs = [i64, i64]`
                      refine wp_loop_break_group
                        (brkTs := [Ty.bool, i64, Ty.bool, i64]) (lpTs := [i64, i64])
                        (BrkPost := fun xs m3 =>
                          let f2 := xs.1; let _tk2 := xs.2.1; let t2 := xs.2.2.1
                          ∃ st_w : FullState, TransUnrollInv c F0 F_cur s st src.toNat saved st_w ∧
                            st_b.core.trail_end ≤ st_w.core.trail_end ∧ ¬(f2 = true ∧ t2 = true) ∧
                            (f2 = true → (cnfOfClauses F_cur).EntailsClause
                              (cnfClause [src.toNat])) ∧
                            (t2 = true → (cnfOfClauses F_cur).EntailsClause
                              (cnfClause [src.toNat, dst.toNat])) ∧
                            (FullMem c st_w ⋆ R) m3)
                        (Inv := fun nq xs m3 => let _tkq := xs.1; let q := xs.2.1
                          ∃ st_q : FullState, ∃ nt : Nat, loff ≤ q.toNat ∧ q.toNat ≤ lend ∧
                            nq = lend - q.toNat ∧ st_b.core.trail_end ≤ st_q.core.trail_end ∧
                            TombWatchSliceOk F_cur st_q.core nl.toNat q.toNat (lend - q.toNat) nt ∧
                            TransUnrollInv c F0 F_cur s st src.toNat saved st_q ∧
                            (FullMem c st_q ⋆ R) m3) ?_ ?_ ?_
                      · rintro J19 ⟨f2, tk2, t2, _q, ⟨⟩⟩ m3
                          ⟨st_w, hu_w, hte_w, hntf2, hf2, ht2, hm3⟩
                        have hpt_pre : prop.toNat < st.core.cur_vars := by
                          have := hlen_b.core_ok.trail_end_le; rw [hu_b.same_core] at this
                          exact Nat.lt_of_lt_of_le hpt_lt this
                        c0_hsteps
                        exact hL13 (st.core.cur_vars - (prop.toNat + 1))
                          (f2, tk2, prop + 1#64, t2, ()) m3 (by rw [hbneq]; omega)
                          ⟨st_w, by rw [hprop1]; omega, by rw [hprop1]; omega,
                           by rw [hprop1], hu_w, hntf2, hf2, ht2, hm3⟩
                      · rintro J19 L20 nq ⟨tkq, q, ⟨⟩⟩ m3 hJ19 hL20
                          ⟨st_q, nt, hql, hqh, hqneq, hte_q, htm_q, hu_q, hm3⟩
                        dsimp only at hql hqh hqneq htm_q; have hlen_q := hu_q.len_ok
                        c0_hsplit
                        · have hq_lt : q.toNat < lend := by
                            have h1 : q.toNat < (BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth
                              64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1) <<< (1 : Nat)).toNat]'
                              hnl_wv0) + BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth 64
                              (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1) <<< (1 : Nat) +
                              1).toNat]'hnl_wv1)).toNat := by c0_bound
                            rwa [hlend_arg] at h1
                          have hq_len : q.toNat < st_q.core.wstk.length := by
                            rw [hlen_q.core_ok.wstk_len_arr]
                            have := hlen_b.core_ok.wlen_le; omega
                          have hstep := htm_q.inv_step (by omega) (List.getElem?_eq_getElem hq_len)
                          have hq1 : (q + 1#64).toNat = q.toNat + 1 :=
                            ft_bv64_add1 (by have := (t4b_bnds hlen_b.core_ok).2.2.1; omega)
                          c0_hsplit
                          · -- Explicit tombstone `qw == 0xFFFFFFFF`
                            have htomb : st_q.core.wstk[q.toNat] = 0xFFFFFFFF#32 := hc
                            simp only [htomb, ↓reduceIte] at hstep
                            have hstep2 := hstep.2
                            c0_hsteps
                            exact hL20 (lend - (q.toNat + 1)) (tkq, q + 1#64, ()) m3 (by omega)
                              ⟨st_q, nt - 1, by rw [hq1]; omega, by rw [hq1]; omega, by rw [hq1],
                               hte_q, by rw [hq1]; rwa [show lend - q.toNat - 1 =
                                 lend - (q.toNat + 1) by omega] at hstep2, hu_q, hm3⟩
                          · have hne_tomb : st_q.core.wstk[q.toNat] ≠ 0xFFFFFFFF#32 := hc
                            c0_hsplit
                            · -- Large watch `(qw & BIN) == 0`
                              have hfl0 : (st_q.core.wstk[q.toNat] &&& 0x80000000#32) = 0#32 := hc
                              simp only [hfl0, ↓reduceIte] at hstep
                              obtain ⟨hle2, _, _, _, _, htm'⟩ := hstep
                              c0_hsplit
                              · c0_hsteps
                                exact hJ19 (fb, tkq, tb, q, ()) m3
                                  ⟨st_q, hu_q, hte_q, hntf, hfb, htb, hm3⟩
                              · have hq2 : (q + 2#64).toNat = q.toNat + 2 :=
                                  ft_bv64_add2 (by have := (t4b_bnds hlen_b.core_ok).2.2.1; omega)
                                c0_hsteps_nogrp
                                refine wp_join_group (ts := [i64]) (fun _ m' => m' = m3)
                                  (fun _ ⟨tk_n, ⟨⟩⟩ m' heq => by
                                    subst heq; c0_hsteps
                                    exact hL20 (lend - (q.toNat + 2)) (tk_n, q + 2#64, ()) m'
                                      (by omega) ⟨st_q, nt, by rw [hq2]; omega, by rw [hq2]; omega,
                                      by rw [hq2], hte_q, by rw [hq2]; rwa [show lend - q.toNat - 2
                                        = lend - (q.toNat + 2) by omega] at htm', hu_q, hm3⟩)
                                  (fun Jtk hJtk => by
                                    c0_hsplit
                                    · c0_hsplit
                                      · c0_hsteps; exact hJtk _ m3 rfl
                                      · c0_hsteps; exact hJtk _ m3 rfl
                                    · c0_hsteps; exact hJtk _ m3 rfl)
                            · -- Non-tombstone binary watch
                              have hfl_nz : (st_q.core.wstk[q.toNat] &&& 0x80000000#32) ≠ 0#32 := hc
                              simp only [hfl_nz, hne_tomb, ↓reduceIte] at hstep
                              obtain ⟨hot_lt, hent_nl, htail⟩ := hstep
                              have htail' : TombWatchSliceOk F_cur st_q.core nl.toNat (q.toNat + 1)
                                  (lend - (q.toNat + 1)) nt := by
                                rwa [show lend - q.toNat - 1 = lend - (q.toNat + 1) by omega] at
                                  htail
                              c0_hsteps_nogrp
                              -- Join after `if (nl == src && q == p) { q++; continue; }`
                              refine wp_join_group (ts := []) (fun _ m4 => m4 = m3) ?_ ?_
                              · rintro J24 ⟨⟩ m4 rfl
                                c0_hsteps_nogrp
                                -- Join for optional `ticks = ticks - 1`
                                refine wp_join_group (ts := [i64]) (fun _ m5 => m5 = m4) ?_
                                  (fun Jtk hJtk => by
                                    c0_hsplit
                                    · c0_hsplit
                                      · c0_hsteps; exact hJtk _ m4 rfl
                                      · c0_hsteps; exact hJtk _ m4 rfl
                                    · c0_hsteps; exact hJtk _ m4 rfl)
                                rintro _ ⟨tk_n, ⟨⟩⟩ m5 rfl
                                let ot := st_q.core.wstk[q.toNat]'hq_len &&& 0x7FFFFFFF#32
                                have hent_ot := entails_pair_trans hent_lit (by rwa [← hnl_eq])
                                c0_hsplit
                                · -- `ot == dst`: transitive!
                                  have hdst_eq : st_q.core.wstk[q.toNat] &&& 0x7FFFFFFF#32 = dst :=
                                    hc
                                  rw [congrArg BitVec.toNat hdst_eq] at hent_ot
                                  c0_hsteps
                                  exact hJ19 (fb, tk_n, true, q + 1#64, ()) m5
                                    ⟨st_q, hu_q, hte_q, by simp [hfb_f],
                                     fun hf => absurd hf (by simp [hfb_f]), fun _ => hent_ot, hm3⟩
                                · c0_hsteps_nogrp
                                  refine wp_join_group (ts := [Ty.bool]) (P := fun _ m6 =>
                                    ∃ st_q2 : FullState,
                                      st_b.core.trail_end ≤ st_q2.core.trail_end ∧
                                      TombWatchSliceOk F_cur st_q2.core nl.toNat (q.toNat + 1)
                                        (lend - (q.toNat + 1)) nt ∧
                                      TransUnrollInv c F0 F_cur s st src.toNat saved st_q2 ∧
                                      (FullMem c st_q2 ⋆ R) m6) ?_ ?_
                                  · rintro J27 ⟨_, ⟨⟩⟩ m6 ⟨st_q2, hte_q2, htm_q2, hu_q2, hm6⟩
                                    c0_hsteps
                                    exact hL20 (lend - (q.toNat + 1)) (tk_n, q + 1#64, ()) m6
                                      (by omega) ⟨st_q2, nt, by rw [hq1]; omega, by rw [hq1]; omega,
                                      by rw [hq1], hte_q2, by rw [hq1]; exact htm_q2, hu_q2, hm6⟩
                                  · intro J27 hJ27
                                    have hot_vlen := t4b_vals_lt hlen_q.core_ok hot_lt
                                    have hot_st : ot.toNat < 2 * st.core.cur_vars := by
                                      have hcv_q : st_q.core.cur_vars = st.core.cur_vars := by
                                        rw [hu_q.same_core]
                                      rw [← hcv_q]; exact hot_lt
                                    have hdom_ot := hu_q.vals_domain hw0 hpre_vals hcv_st hot_st
                                    c0_hsplit
                                    · c0_hsplit
                                      · -- `vals[ot] < 0`: failed literal `src`!
                                        have hval_ff := t4b_vals_ff_of_domain (z := 0#32) hdom_ot
                                          rfl (by rw [List.getElem?_eq_getElem hot_vlen]; exact hc)
                                        have hent_src := hu_q.entails_src_of_falsified hw0 hpre_vals
                                          hcv_st hcl0 hot_st hval_ff hent_ot
                                        c0_hsteps
                                        exact hJ19 (true, tk_n, tb, q + 1#64, ()) m5
                                          ⟨st_q, hu_q, hte_q, by simp [htb_f], fun _ => hent_src,
                                           fun ht => absurd ht (by simp [htb_f]), hm3⟩
                                      · c0_hsteps_nogrp
                                        refine wp_unroll_group fun _ _ => ?_
                                        c0_hsplit
                                        · have hot0 := t4b_vals_zero_of_domain (z := 0#32) hdom_ot
                                            rfl (by rw [List.getElem?_eq_getElem hot_vlen]
                                                    exact hc)
                                          c0_hsplit
                                          · obtain ⟨hte_q_lt, hu_q'⟩ := hu_q.push hw0 hpre_vals
                                              hpre_te hpre_trl hcv_st hot_st hot0 hent_ot
                                            have hbv_ot : BitVec.ofNat 32 ot.toNat = ot :=
                                              t4b_bv32_ofNat_toNat ot
                                            have hot64 : ((st_q.core.wstk[q.toNat]'hq_len &&&
                                                2147483647).setWidth 64).toNat = ot.toNat :=
                                              ft_bv32_setWidth64 ot
                                            have hotn64 : (((st_q.core.wstk[q.toNat]'hq_len &&&
                                                2147483647) ^^^ 1).setWidth 64).toNat =
                                                ot.toNat ^^^ 1 := by
                                              rw [ft_bv32_setWidth64]; exact ft_bv32_xor1 ot
                                            have hotn_vlen : (ot ^^^ 1).toNat <
                                                (st_q.core.vals.set ot.toNat 1#8).length := by
                                              rw [List.length_set, show (ot ^^^ 1).toNat =
                                                ot.toNat ^^^ 1 from ft_bv32_xor1 ot,
                                                hlen_q.core_ok.vals_len]
                                              have := litNeg_lt_two_mul hot_lt
                                              have := hlen_q.core_ok.cur_vars_le
                                              dsimp only [ot]; omega
                                            have hteq_lt : st_q.core.trail_end < 2 ^ 64 :=
                                              (t4b_bnds hlen_q.core_ok).2.2.2
                                            have hte_bv : (BitVec.ofNat 64
                                                st_q.core.trail_end).toNat =
                                                st_q.core.trail_end := by
                                              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hteq_lt]
                                            have hteq_tlen : (BitVec.ofNat 64
                                                st_q.core.trail_end).toNat <
                                                st_q.core.trl.length := by
                                              rw [hte_bv, hlen_q.core_ok.trl_len]
                                              have := hlen_q.core_ok.cur_vars_le; omega
                                            have hteq1 : (BitVec.ofNat 64 st_q.core.trail_end +
                                                1).toNat = st_q.core.trail_end + 1 := by
                                              rw [show (1 : BitVec 64) = 1#64 from rfl,
                                                ft_bv64_add1 (by omega), hte_bv]
                                            c0_hsteps
                                            let st_q2 : FullState := { st_q with core := {
                                              st_q.core with
                                              vals := (st_q.core.vals.set ot.toNat 1#8).set
                                                (ot.toNat ^^^ 1) 0xFF#8
                                              trl := st_q.core.trl.set st_q.core.trail_end ot
                                              trail_end := st_q.core.trail_end + 1 } }
                                            refine hJ27 (fb, ()) _ ⟨st_q2,
                                              Nat.le_trans hte_q (Nat.le_succ _),
                                              TombWatchSliceOk.mono (k := st_q.core)
                                                (k' := st_q2.core) (Nat.le_refl _) (fun _ hr => hr)
                                                (fun _ _ _ => rfl) htail',
                                              by simpa only [hbv_ot] using hu_q', ?_⟩
                                            refine t4b_fullMem_eq ?_ (by assumption)
                                            dsimp only [st_q2]
                                            rw [hot64, hotn64, hte_bv, hteq1]; rfl
                                          · c0_hsteps
                                            exact hJ27 (fb, ()) m5 ⟨st_q, hte_q, htail', hu_q, hm3⟩
                                        · c0_hsteps
                                          exact hJ27 (fb, ()) m5 ⟨st_q, hte_q, htail', hu_q, hm3⟩
                                    · c0_hsteps
                                      exact hJ27 (fb, ()) m5 ⟨st_q, hte_q, htail', hu_q, hm3⟩
                              · intro J24 hJ24
                                c0_hsplit
                                · c0_hsplit
                                  · c0_hsteps
                                    exact hL20 (lend - (q.toNat + 1)) (tkq, q + 1#64, ()) m3
                                      (by omega) ⟨st_q, nt, by rw [hq1]; omega, by rw [hq1]; omega,
                                      by rw [hq1], hte_q, by rw [hq1]; exact htail', hu_q, hm3⟩
                                  · c0_hsteps; exact hJ24 () m3 rfl
                                · c0_hsteps; exact hJ24 () m3 rfl
                        · c0_hsteps
                          exact hJ19 (fb, tkq, tb, q, ()) m3
                            ⟨st_q, hu_q, hte_q, hntf, hfb, htb, hm3⟩
                      · intro J19 L20 hJ19 hL20; c0_hsteps; rw [hlo_arg]
                        exact hL20 (lend - loff) (tk - 1#64, BitVec.ofNat 64 loff, ()) m2
                          ⟨st_b, nt0, by rw [hlo_eq]; exact Nat.le_refl _, by rw [hlo_eq]; omega,
                           by rw [hlo_eq], Nat.le_refl _,
                           by rw [hlo_eq]; simpa [lend, loff, lsz] using htomb0, hu_b, hm2⟩
                    · c0_hsteps; exact hJ15_now
                  · c0_hsteps; exact hJ15_now
              · -- BFS loop entry
                intro L13 hL13
                have hnot_sw : (BitVec.setWidth 64 (src ^^^ 1)).toNat = src.toNat ^^^ 1 := by
                  rw [ft_bv32_setWidth64]; exact ft_bv32_xor1 src
                have hsrc_sw : (BitVec.setWidth 64 src).toNat = src.toNat := ft_bv32_setWidth64 src
                c0_hsteps
                let st_i : FullState := { st with core := { st.core with
                  vals := (st.core.vals.set (src.toNat ^^^ 1) 1#8).set src.toNat 0xFF#8
                  trl := st.core.trl.set saved not_src
                  trail_end := saved + 1 } }
                refine hL13 (st.core.cur_vars - saved)
                  (failed, st.scratch.ant_sz - 1#64, BitVec.ofNat 64 saved, false, ()) _
                  ⟨st_i, by dsimp only; rw [hs_eq]; exact Nat.le_refl _,
                   by dsimp only [st_i]; rw [hs_eq]; omega,
                   by dsimp only; rw [hs_eq],
                   by dsimp only [st_i]; simpa only [hbv_not] using hu1,
                   by dsimp only; simp [hfail_f],
                   fun hf => by dsimp only at hf; simp [hfail_f] at hf,
                   fun ht => False.elim (Bool.noConfusion ht), ?_⟩
                refine t4b_fullMem_eq ?_ (by assumption)
                dsimp only [st_i, saved, not_src] at hs_eq hte_p1 ⊢
                rw [hnot_sw, hsrc_sw, hs_eq, hte_p1]; rfl
        · c0_hsteps; exact hB_now
    · c0_hsteps; exact hB_now
  · -- Outer loop entry
    intro B L hB hL; c0_hsteps; rw [h_off_arg]
    have hto0 := TransOuterInv.init hlen0 hw0 hsp.2.2.2.2 hcl0 hsrc_lt hsz_pos
    exact hL (end_v - off) (false, 0#64, BitVec.ofNat 64 off, ()) m ⟨s,
      (by dsimp only; rw [hof64]; exact Nat.le_refl _),
      (by dsimp only; rw [hof64]; exact Nat.le_add_right off sz), (by dsimp only; rw [hof64]),
      (by dsimp only; simp), (by dsimp only; rw [hof64]; exact hto0),
      (by dsimp only; intro h; cases h), rfl, rfl, rfl, hm⟩

end TransLitM6Proof

/-! ## 4. `full_trans_sort_m6_wp` and `full_transitive_m6_wp` -/

section TransTopM6Proofs

theorem full_trans_sort_m6_wp (Γ : Env) :
    ∀ a m Q X, fullTransSortM6Spec a m Q X →
      Func.wp Γ full_trans_sort_m6_body a m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp, hn_le, hok0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp.1.lengths.core_ok; have hscl0 := hsp.1.lengths.scratch_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hcl0.cur_vars_le
  have hsc_len : s.scratch.score.length = c.max_vars := hscl0.score_len
  have hqs_len : s.scratch.q_stamp.length = c.max_vars := hscl0.q_stamp_len
  unfold Func.wp full_trans_sort_m6_body
  c0_hsteps_nogrp
  -- Outer loop on `gap`: `while (gap > 0)`
  refine wp_loop_inv (ts := [i64])
    (fun (gap, ()) mg => ∃ ws1 : List (BitVec 32),
      gap.toNat ≤ n.toNat ∧ ws1.length = 2 * c.max_vars ∧
      (∀ i < n.toNat, (ws1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) mg)
    (fun (gap, ()) _ => gap.toNat)
    (fun Jg hJg => by
      c0_hsteps
      have hshr : (n >>> (1 : Nat)).toNat = n.toNat / 2 := by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact hJg (n >>> (1 : Nat), ()) m0
        ⟨s.scratch.work_stk1, by rw [hshr]; omega, hscl0.work_stk1_len, hok0, hm0⟩)
    (fun Jg ⟨gap, ⟨⟩⟩ mg ⟨wsg, hgap_le, hwsg_len, hokg, hmg⟩ ihg => ?_)
  c0_hsplit
  · have hgap_pos : 0 < gap.toNat := by c0_bound
    c0_hsteps_nogrp
    -- Middle loop on `si`: `while (si < n)`
    refine wp_loop_inv (ts := [i64])
      (fun (si, ()) msi => ∃ wss : List (BitVec 32),
        gap.toNat ≤ si.toNat ∧ si.toNat ≤ n.toNat ∧ wss.length = 2 * c.max_vars ∧
        (∀ i < n.toNat, (wss[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := wss } } ⋆ R) msi)
      (fun (si, ()) _ => n.toNat - si.toNat)
      (fun Ji hJi => by
        c0_hsteps
        exact hJi (gap, ()) mg ⟨wsg, Nat.le_refl _, hgap_le, hwsg_len, hokg, hmg⟩)
      (fun Ji ⟨si, ⟨⟩⟩ msi ⟨wss, hgsi, hsi_le, hwss_len, hoks, hmsi⟩ ihi => ?_)
    c0_hsplit
    · have hsi_lt : si.toNat < n.toNat := by c0_bound
      have hsi_len : si.toNat < wss.length := by omega
      let v := wss[si.toNat]'hsi_len
      have hv_lt : v.toNat < s.core.cur_vars := by
        have h := hoks si.toNat hsi_lt
        rwa [List.getElem?_eq_getElem hsi_len, Option.getD_some] at h
      have hv64 : (v.setWidth 64).toNat = v.toNat := ft_bv32_setWidth64 v
      have hv_sc : (v.setWidth 64).toNat <
          ({ s with scratch := { s.scratch with work_stk1 := wss } } :
            FullState).scratch.score.length := by
        dsimp only; rw [hv64, hsc_len]; omega
      have hv_qs : (v.setWidth 64).toNat <
          ({ s with scratch := { s.scratch with work_stk1 := wss } } :
            FullState).scratch.q_stamp.length := by
        dsimp only; rw [hv64, hqs_len]; omega
      c0_hsteps_nogrp
      -- Join for `kv = stab ? sc[v] : (u64)qs[v]`
      refine wp_join_group (ts := [i64]) (fun _ mk => mk = msi) ?_
        (fun Jk hJk => by
          c0_hsplit
          · c0_hsteps; exact hJk _ msi rfl
          · c0_hsteps; exact hJk _ msi rfl)
      rintro _ ⟨kv, ⟨⟩⟩ mk rfl
      c0_hsteps_nogrp
      -- Inner gap-shift loop with break: `while (sj >= gap)`
      refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
        (BrkPost := fun (sj_b, ()) mb => ∃ wsb : List (BitVec 32),
          sj_b.toNat < n.toNat ∧ wsb.length = 2 * c.max_vars ∧
          (∀ i < n.toNat, (wsb[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := wsb } } ⋆ R) mb)
        (Inv := fun rem (sj, ()) mj => ∃ wsj : List (BitVec 32),
          sj.toNat < n.toNat ∧ rem = sj.toNat ∧ wsj.length = 2 * c.max_vars ∧
          (∀ i < n.toNat, (wsj[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := wsj } } ⋆ R) mj)
        ?_ ?_ ?_
      · -- After inner loop: `probes[sj_b] = v; si = si + 1;`
        rintro _ ⟨sj_b, ⟨⟩⟩ mb ⟨wsb, hsjb_lt, hwsb_len, hokb, hmb⟩
        have hsjb_len : sj_b.toNat < wsb.length := by omega
        have hsi1 : (si + 1#64).toNat = si.toNat + 1 := ft_bv64_add1 (by omega)
        c0_hsteps
        exact ihi (si + 1#64, ()) _ (by dsimp only; omega)
          ⟨wsb.set sj_b.toNat v, by rw [hsi1]; omega, by rw [hsi1]; omega,
           by simp [hwsb_len], t4b_ws1_set_lt_bound hsjb_len hv_lt hokb, (by assumption)⟩
      · -- Inner loop body
        rintro B L rem ⟨sj, ⟨⟩⟩ mj hB hL ⟨wsj, hsj_lt, hrem, hwsj_len, hokj, hmj⟩
        c0_hsplit
        · have hsj_ge : gap.toNat ≤ sj.toNat := by c0_bound
          have hpj_eq : (sj - gap).toNat = sj.toNat - gap.toNat := by bv_omega
          have hpj_len : (sj - gap).toNat < wsj.length := by omega
          let pv := wsj[(sj - gap).toNat]'hpj_len
          have hpv_lt : pv.toNat < s.core.cur_vars := by
            have h := hokj (sj - gap).toNat (by omega)
            rwa [List.getElem?_eq_getElem hpj_len, Option.getD_some] at h
          have hpv64 : (pv.setWidth 64).toNat = pv.toNat := ft_bv32_setWidth64 pv
          have hpv_sc : (pv.setWidth 64).toNat <
              ({ s with scratch := { s.scratch with work_stk1 := wsj } } :
                FullState).scratch.score.length := by
            dsimp only; rw [hpv64, hsc_len]; omega
          have hpv_qs : (pv.setWidth 64).toNat <
              ({ s with scratch := { s.scratch with work_stk1 := wsj } } :
                FullState).scratch.q_stamp.length := by
            dsimp only; rw [hpv64, hqs_len]; omega
          c0_hsteps_nogrp
          -- Join for `kpv = stab ? sc[pv] : (u64)qs[pv]`
          refine wp_join_group (ts := [i64]) (fun _ mp => mp = mj) ?_
            (fun Jp hJp => by
              c0_hsplit
              · c0_hsteps; exact hJp _ mj rfl
              · c0_hsteps; exact hJp _ mj rfl)
          rintro _ ⟨kpv, ⟨⟩⟩ mp rfl
          -- Break check `if (kpv > kv || (kpv == kv && pv <= v)) break;`
          c0_hsplit
          · c0_hsteps; exact hB (sj, ()) mp ⟨wsj, hsj_lt, hwsj_len, hokj, hmj⟩
          · refine wp_join_group (ts := []) (fun _ m_c => m_c = mp)
              (fun _ _ m_c heq => by
                subst heq
                have hsj_len : sj.toNat < wsj.length := by omega
                c0_hsteps
                exact hL (sj.toNat - gap.toNat) (sj - gap, ()) _ (by omega)
                  ⟨wsj.set sj.toNat pv, by rw [hpj_eq]; omega, by rw [hpj_eq],
                   by simp [hwsj_len], t4b_ws1_set_lt_bound hsj_len hpv_lt hokj, (by assumption)⟩)
              (fun Jc hJc => by
                c0_hsplit
                · c0_hsplit
                  · c0_hsteps; exact hB (sj, ()) mp ⟨wsj, hsj_lt, hwsj_len, hokj, hmj⟩
                  · c0_hsteps; exact hJc () mp rfl
                · c0_hsteps; exact hJc () mp rfl)
        · c0_hsteps; exact hB (sj, ()) mj ⟨wsj, hsj_lt, hwsj_len, hokj, hmj⟩
      · intro B L hB hL; c0_hsteps
        exact hL si.toNat (si, ()) mk ⟨wss, hsi_lt, rfl, hwss_len, hoks, hmsi⟩
    · -- Exit middle loop: `gap = gap >> 1`
      c0_hsteps
      have hshr : (gap >>> (1 : Nat)).toNat = gap.toNat / 2 := by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact ihg (gap >>> (1 : Nat), ()) msi (by dsimp only; rw [hshr]; omega)
        ⟨wss, by rw [hshr]; omega, hwss_len, hoks, hmsi⟩
  · c0_hsteps
    exact hQ wsg mg hwsg_len (t4b_sparse_with_ws1 hsp hwsg_len) hokg hmg

/-- `full_transitive_m6` satisfies canonical **`FullFastBveBudgets.fullTransitiveFastSpec`**. -/
private theorem t4b_fullPropagate_del_sparse {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} {vals' : List (BitVec 8)}
    {flags' lvl' rsns' trl' tp' : List (BitVec 32)} {te' prop' : Nat} {unass' unfl' : BitVec 64}
    {wvec' arena' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)} {delayed' : List (BitVec 32)}
    (hsp : FullSparseInv c F0 s)
    (hs' : s' = { s with
      core := { s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', unassigned := unass', unflushed := unfl',
        wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
        fuel := fuel', confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
        confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with
        search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } })
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm' : FullArenaPermEq s.core s'.core) : FullSparseInv c F0 s' := by
  let s0' : FullState := { s' with scratch := { s'.scratch with delayed := s.scratch.delayed } }
  have hlen0' : s0'.LengthsOk c :=
    ⟨hlen'.core_ok,
      { hlen'.scratch_ok with delayed_len_arr := hsp.1.lengths.scratch_ok.delayed_len_arr }⟩
  have hw0' : FullWitnessInv c F0 F_cur s0'.core := hw'
  have hperm0' : FullArenaPermEq s.core s0'.core := hperm'
  have hs0' : s0' = { s with
      core := { s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', unassigned := unass', unflushed := unfl',
        wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
        fuel := fuel', confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
        confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with
        search_ticks := ticks', wsort := wsort', phases := phases' } } := by
    subst hs'; rfl
  have hsp0' := fullPropagate_sparse hsp hs0' hlen0' hw0' hperm0'
  exact ⟨⟨hlen', F_cur, hw'⟩, hsp0'.2⟩

theorem full_transitive_m6_del_wp (Γ : Env)
    (h_backtrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (h_prio : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Γ "full_prioritize_binaries_m6" [i64] [.bool] a m Q X)
    (h_sort : ∀ a m Q X, fullTransSortM6Spec a m Q X →
      Γ "full_trans_sort_m6" [i64, i64] [] a m Q X)
    (h_trans_lit : ∀ a m Q X, fullTransLitM6Spec a m Q X →
      Γ "full_trans_lit_m6" [i64, i32, .bool] [.bool] a m Q X)
    (h_propagate : ∀ a m Q X, fullPropagateDelSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (h_defrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Func.wp Γ full_transitive_m6_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_transitive_m6_body
  -- Initial `if (h->cur_level != 0) full_backtrack(h, 0)`
  refine wp_join_group (ts := [])
    (P := fun _ m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro J1 ⟨⟩ m1 ⟨s1, hsp1, hcl1, hfuel1, hm1⟩
    have hlen1 := hsp1.1.lengths
    have hcv_lt : s1.core.cur_vars < 2 ^ 64 := by have := (t4b_bnds hlen1.core_ok).1; omega
    have hcv_le1 : s1.core.cur_vars ≤ c.max_vars := hlen1.core_ok.cur_vars_le
    c0_hsteps_nogrp
    -- Shared early-return join `if (num_binary == 0 || tick_lim == 0 || cv == 0)`
    refine wp_join_group (ts := []) (P := fun _ m_e => m_e = m1)
      (fun _ _ m_e heq => by
        subst heq; c0_hsteps
        exact hQ 1#64 _ _ (fullSparseInv_with_probing hsp1 0#64)
          (fun _ => hcl1) (fun _ => rfl) (fun _ _ => ⟨hcl1, rfl⟩)
          hfuel1 (Or.inl rfl) (fun h => absurd h (by decide)) (by assumption))
      (fun Je hJe => ?_)
    c0_hsplit
    · c0_hsteps; exact hJe () m1 rfl
    c0_hsplit
    · c0_hsteps; exact hJe () m1 rfl
    c0_hsplit
    · c0_hsteps; exact hJe () m1 rfl
    -- `h->probing = 1; stop_early = full_prioritize_binaries_m6(h);`
    c0_hsteps_nogrp; c0_call h_prio
    have hsp_p := fullSparseInv_with_probing hsp1 1#64
    obtain ⟨F_cur1, hw1⟩ := hsp_p.1.witness
    have hsp_pW : FullSparseInvW c F0 F_cur1
        { s1 with core := { s1.core with probing := 1#64 } } :=
      ⟨hsp_p.1.lengths, hw1, hsp_p.2.1, hsp_p.2.2.1, hsp_p.2.2.2.1, hsp_p.2.2.2.2⟩
    refine ⟨c, F0, F_cur1, _, R, rfl, hsp_pW, (by assumption),
      fun stop_early wstk' scr' m2 hsp2W hm2 => ?_⟩
    let s2 : FullState :=
      { s1 with
        core := { s1.core with probing := 1#64, wstk := wstk' }
        scratch := { s1.scratch with scratch_buf := scr' } }
    have hsp2 : FullSparseInv c F0 s2 := ⟨⟨hsp2W.1, ⟨F_cur1, hsp2W.2.1⟩⟩, hsp2W.2.2⟩
    have hcl2 : s2.core.cur_level = 0 := hcl1
    have hlen2 := hsp2.1.lengths
    have hcv_s2 : s2.core.cur_vars = s1.core.cur_vars := rfl
    have hfu_s2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfuel1
    c0_hsteps_nogrp
    -- Collect active `FL_TRANS` unassigned vars into `work_stk1[0..<pn)`
    refine wp_loop_inv (ts := [i64, i64])
      (fun (pn, v, ()) mc => ∃ ws1 : List (BitVec 32),
        pn.toNat ≤ v.toNat ∧ v.toNat ≤ s1.core.cur_vars ∧ ws1.length = 2 * c.max_vars ∧
        (∀ i < pn.toNat, (ws1[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
        (FullMem c { s2 with scratch := { s2.scratch with work_stk1 := ws1 } } ⋆ R) mc)
      (fun (_, v, ()) _ => s1.core.cur_vars - v.toNat)
      (fun Jc hJc => by
        c0_hsteps
        exact hJc (0#64, 0#64, ()) m2 ⟨s2.scratch.work_stk1, Nat.le_refl _, Nat.zero_le _,
          hlen2.scratch_ok.work_stk1_len, (fun _ h => by cases h), hm2⟩)
      (fun Jc ⟨pn, v, ⟨⟩⟩ mc ⟨ws1, hpn_le, hv_le, hws1_len, hpn_lt, hmc⟩ ihc => ?_)
    c0_hsplit
    · have hv_lt : v.toNat < s1.core.cur_vars := by
        have h1 : v.toNat < s1.core.cur_vars % 2 ^ 64 := by c0_bound
        rwa [Nat.mod_eq_of_lt hcv_lt] at h1
      have hv_fl : v.toNat < s2.core.flags.length := by rw [hlen2.core_ok.flags_len]; omega
      have hv_shl : (v <<< (1 : Nat)).toNat = 2 * v.toNat := ft_bv64_shl1 (by omega)
      have hv_vl : (v <<< (1 : Nat)).toNat < s2.core.vals.length := by
        rw [hv_shl, hlen2.core_ok.vals_len]; omega
      have hv1 : (v + 1#64).toNat = v.toNat + 1 := ft_bv64_add1 (by omega)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (pn', ()) m' => ∃ ws1' : List (BitVec 32),
        pn'.toNat ≤ v.toNat + 1 ∧ ws1'.length = 2 * c.max_vars ∧
        (∀ i < pn'.toNat, (ws1'[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
        (FullMem c { s2 with scratch := { s2.scratch with work_stk1 := ws1' } } ⋆ R) m')
        (fun _ ⟨pn', ⟨⟩⟩ m' ⟨ws1', hpn', hws1', hlt', hm'⟩ => by
          c0_hsteps
          exact ihc (pn', v + 1#64, ()) m' (by dsimp only; omega)
            ⟨ws1', by rw [hv1]; exact hpn', by rw [hv1]; omega, hws1', hlt', hm'⟩)
        (fun Jw hJw => by
          c0_hsplit
          · c0_hsplit
            · have hpn1 : (pn + 1#64).toNat = pn.toNat + 1 := ft_bv64_add1 (by omega)
              have hpn_ws1 : pn.toNat < ws1.length := by omega
              have hv32 : (v.truncate 32).toNat = v.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              c0_hsteps
              exact hJw (pn + 1#64, ()) _ ⟨ws1.set pn.toNat (v.truncate 32), by rw [hpn1]; omega,
                by simp [hws1_len], fun i hi => by
                  rw [hpn1] at hi
                  by_cases hip : i = pn.toNat
                  · subst hip; rw [List.getElem?_set_self hpn_ws1, Option.getD_some, hv32]
                    exact hv_lt
                  · rw [List.getElem?_set_ne (Ne.symm hip)]; exact hpn_lt i (by omega),
                (by assumption)⟩
            · c0_hsteps; exact hJw (pn, ()) mc ⟨ws1, by omega, hws1_len, hpn_lt, hmc⟩
          · c0_hsteps; exact hJw (pn, ()) mc ⟨ws1, by omega, hws1_len, hpn_lt, hmc⟩)
    · -- Exit collect loop: optional `full_trans_sort_m6`, then main probe loop
      let s3 : FullState := { s2 with scratch := { s2.scratch with work_stk1 := ws1 } }
      have hsp3 : FullSparseInv c F0 s3 := t4b_sparse_with_ws1 hsp2 hws1_len
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (P := fun _ ms => ∃ ws1s : List (BitVec 32),
        ws1s.length = 2 * c.max_vars ∧
        (∀ i < pn.toNat, (ws1s[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
        FullSparseInv c F0 { s2 with scratch := { s2.scratch with work_stk1 := ws1s } } ∧
        (FullMem c { s2 with scratch := { s2.scratch with work_stk1 := ws1s } } ⋆ R) ms)
        ?_ ?_
      · rintro Js ⟨⟩ ms ⟨ws1s, hws1s_len, hpn_lts, hsp_s, hms⟩
        c0_hsteps_nogrp
        -- Main probe loop with break: `brkTs = [i64, i64]` `(res, pi)`, `lpTs = [i64]` `(pi)`
        refine wp_loop_break_group (brkTs := [i64, i64]) (lpTs := [i64])
          (BrkPost := fun xs mb => let res := xs.1
            ∃ sb : FullState, FullSparseInv c F0 sb ∧ sb.core.cur_level = 0 ∧
              sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (res = 1#64 ∨ res = 20#64) ∧
              (res = 20#64 → F0.Unsat) ∧ (FullMem c sb ⋆ R) mb)
          (Inv := fun rem (pi, ()) ml => ∃ sl : FullState,
            pi.toNat ≤ pn.toNat ∧ rem = pn.toNat - pi.toNat ∧
            FullSparseInv c F0 sl ∧ sl.core.cur_level = 0 ∧ sl.core.cur_vars = s1.core.cur_vars ∧
            sl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (∀ i < pn.toNat, (sl.scratch.work_stk1[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
            (FullMem c sl ⋆ R) ml) ?_ ?_ ?_
        · -- After main loop: optional `full_wstack_defrag`, `probing = 0`, `return res`
          rintro B ⟨res, _pi, ⟨⟩⟩ mb ⟨sb, hspb, hclb, hfuelb, hresb, hunsatb, hmb⟩
          refine wp_join_group (ts := []) (P := fun _ m3 => ∃ sd : FullState,
            FullSparseInv c F0 sd ∧ sd.core.cur_level = 0 ∧
            sd.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sd ⋆ R) m3) ?_ ?_
          · rintro Jd ⟨⟩ m3 ⟨sd, hspd, hcld, hfueld, hm3⟩; c0_hsteps
            exact hQ res _ _ (fullSparseInv_with_probing hspd 0#64)
              (fun _ => hcld) (fun _ => rfl) (fun _ _ => ⟨hcld, rfl⟩)
              hfueld hresb hunsatb (by assumption)
          · intro Jd hJd; have hlenb := hspb.1.lengths; c0_hsplit
            · c0_hsteps_nogrp; c0_call h_defrag
              obtain ⟨F_cb, hwb⟩ := hspb.1.witness
              have hwm := hwb.watches
              simp only [ModeWatchesInv, hspb.2.2.2.2, ↓reduceIte] at hwm
              refine ⟨c, sb, R, rfl, hlenb, hwm.layout, hmb,
                fun _ _ _ _ m3 hlen3 hlay3 _ hpres hm3 => by
                  c0_hsteps
                  exact hJd () m3 ⟨_, fullWstackDefrag_sparse hspb rfl hlen3 hlay3 hpres, hclb,
                    hfuelb, hm3⟩⟩
            · c0_hsteps; exact hJd () mb ⟨sb, hspb, hclb, hfuelb, hmb⟩
        · -- Main loop body
          rintro B L rem ⟨pi, ⟨⟩⟩ ml hB hL
            ⟨sl, hpi_le, hrem, hspl, hcll, hcvl, hfuell, hws1l, hml⟩
          have hlenl := hspl.1.lengths
          have hB1 : B (1#64, pi, ()) ml := hB (1#64, pi, ()) ml ⟨sl, hspl, hcll, hfuell,
            Or.inl rfl, fun h => by dsimp only at h; exact absurd h (by decide), hml⟩
          c0_hsplit
          · have hpi_lt : pi.toNat < pn.toNat := by c0_bound
            c0_hsplit
            · c0_hsplit
              · c0_hsplit
                · have hpi_ws1 : pi.toNat < sl.scratch.work_stk1.length := by
                    rw [hlenl.scratch_ok.work_stk1_len]; omega
                  let pv := sl.scratch.work_stk1[pi.toNat]'hpi_ws1
                  have hpv_lt : pv.toNat < s1.core.cur_vars := by
                    have h := hws1l pi.toNat hpi_lt
                    rwa [List.getElem?_eq_getElem hpi_ws1, Option.getD_some] at h
                  have hpv64 : (pv.setWidth 64).toNat = pv.toNat := ft_bv32_setWidth64 pv
                  have hpv_fl : pv.toNat < sl.core.flags.length := by
                    rw [hlenl.core_ok.flags_len]; omega
                  have hpv_shl : (pv.setWidth 64 <<< (1 : Nat)).toNat = 2 * pv.toNat := by
                    rw [ft_bv64_shl1 (by rw [hpv64]; omega), hpv64]
                  have hpv_vl : (pv.setWidth 64 <<< (1 : Nat)).toNat < sl.core.vals.length := by
                    rw [hpv_shl, hlenl.core_ok.vals_len]; omega
                  c0_hsteps_nogrp
                  -- Continue join `J_cont` (`[i64]` = `res`)
                  refine wp_join_group (ts := [i64]) (P := fun xs m_c => xs.1 = 1#64 ∧
                    ∃ sn : FullState, FullSparseInv c F0 sn ∧ sn.core.cur_level = 0 ∧
                      sn.core.cur_vars = s1.core.cur_vars ∧
                      sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (∀ i < pn.toNat,
                        (sn.scratch.work_stk1[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
                      (FullMem c sn ⋆ R) m_c) ?_ ?_
                  · rintro Jc ⟨_, ⟨⟩⟩ m_c ⟨rfl, sn, hspn, hcln, hcvn, hfueln, hws1n, hm_c⟩
                    have hpi1 : (pi + 1#64).toNat = pi.toNat + 1 := ft_bv64_add1 (by omega)
                    c0_hsteps
                    exact hL (pn.toNat - (pi.toNat + 1)) (pi + 1#64, ()) m_c (by omega)
                      ⟨sn, by rw [hpi1]; omega, by rw [hpi1], hspn, hcln, hcvn, hfueln, hws1n, hm_c⟩
                  · intro Jc hJc
                    -- Inner else join: `fl[pv] &= ~FL_TRANS; jump Jc 1`
                    refine wp_join_group (ts := []) (P := fun _ m_e => m_e = ml)
                      (fun _ _ m_e heq => by
                        subst heq; c0_hsteps
                        have hsp_cl : FullSparseInv c F0 { sl with core := { sl.core with
                            flags := sl.core.flags.set pv.toNat
                              (sl.core.flags[pv.toNat] &&& ~~~512#32) } } :=
                          fullSparseInv_clear_fl_trans hspl
                        exact hJc (1#64, ()) _ ⟨rfl, _, hsp_cl, hcll, hcvl, hfuell, hws1l,
                          by refine t4b_fullMem_eq ?_ (by assumption)
                             dsimp only [pv] at hpv64 ⊢; simp only [hpv64]; rfl⟩)
                      (fun Jelse hJelse => ?_)
                    c0_hsplit
                    · c0_hsplit
                      · -- Active & unassigned: probe `pv<<1` and `(pv<<1)|1`
                        have hpv32 : 2 * pv.toNat + 1 < 2 ^ 32 := by
                          have := (t4b_bnds hlenl.core_ok).1; omega
                        have hlit0 : (pv <<< (1 : Nat)).toNat < 2 * sl.core.cur_vars := by
                          rw [show (pv <<< (1 : Nat)).toNat = 2 * pv.toNat by
                            simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega]
                          omega
                        c0_hsteps_nogrp; c0_call h_trans_lit
                        refine ⟨c, F0, sl, R, rfl, hspl, hcll, hlit0, hml,
                          fun ok0 st0 m3 hspt0 hclt0 hcvt0 hfuelt0 hws1t0 huns0 hm3 => ?_⟩
                        have hcv_t0 : st0.core.cur_vars = s1.core.cur_vars := hcvt0.trans hcvl
                        have hfu_t0 : st0.core.fuel.toNat ≤ s.core.fuel.toNat := by
                          rw [hfuelt0]; exact hfuell
                        have hws1_t0 : ∀ i < pn.toNat,
                            (st0.scratch.work_stk1[i]?.getD 0#32).toNat < s1.core.cur_vars := by
                          rw [hws1t0]; exact hws1l
                        c0_hsplit
                        · obtain ⟨F_ct0, hwt0⟩ := hspt0.1.witness
                          c0_hsteps_nogrp; c0_call h_propagate
                          refine ⟨c, F0, F_ct0, st0, R, rfl, hspt0.1.lengths, hwt0, hspt0.2.2.2.2,
                            hm3, fun r_p0 vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl'
                              wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks'
                              wsort' phases' delayed' m4 hlen4 hw4 _ hperm4 hfu4 _ _ hr1 _ _ hm4 =>
                            ?_⟩
                          have hsp_p0 :=
                            t4b_fullPropagate_del_sparse hspt0 rfl hlen4 hw4 hperm4
                          have hfu_p0 : fuel'.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu4 hfu_t0
                          c0_hsplit
                          · c0_hsteps
                            exact hB (20#64, pi, ()) m4 ⟨_, hsp_p0, hclt0, hfu_p0, Or.inr rfl,
                              fun _ => level0_unsat_of_conflict_okW hw4 hclt0 (hr1 hc).2.2, hm4⟩
                          · c0_hsplit
                            · c0_hsteps
                              exact hB (1#64, pi, ()) m4 ⟨_, hsp_p0, hclt0, hfu_p0, Or.inl rfl,
                                fun h => by dsimp only at h; exact absurd h (by decide), hm4⟩
                            · c0_hsplit
                              · c0_hsteps
                                exact hB (1#64, pi, ()) m4 ⟨_, hsp_p0, hclt0, hfu_p0, Or.inl rfl,
                                  fun h => by dsimp only at h; exact absurd h (by decide), hm4⟩
                              · c0_hsplit
                                · c0_hsteps
                                  exact hB (1#64, pi, ()) m4 ⟨_, hsp_p0, hclt0, hfu_p0, Or.inl rfl,
                                    fun h => by dsimp only at h; exact absurd h (by decide), hm4⟩
                                · c0_hsplit
                                  · c0_hsteps
                                    exact hB (1#64, pi, ()) m4
                                      ⟨_, hsp_p0, hclt0, hfu_p0, Or.inl rfl,
                                      fun h => by dsimp only at h; exact absurd h (by decide), hm4⟩
                                  · let st_p0 : FullState := { st0 with
                                      scratch := { st0.scratch with
                                        search_ticks := ticks', wsort := wsort',
                                        phases := phases', delayed := delayed' }
                                      core := { st0.core with
                                        vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                        trl := trl', trail_pos := tp', trail_end := te',
                                        propagated := prop', unassigned := unass',
                                        unflushed := unfl', wvec := wvec', arena := arena',
                                        wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                                        confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                        confl_lit1 := c1', oom := oom' } }
                                    have hlit1 : ((pv <<< (1 : Nat)) ||| 1#32).toNat <
                                        2 * st_p0.core.cur_vars := by
                                      have hsh : (pv <<< (1 : Nat)).toNat = 2 * pv.toNat := by
                                        simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
                                      have hor : (2 * pv.toNat) ||| 1 = 2 * pv.toNat + 1 := by
                                        apply Nat.eq_of_testBit_eq; intro i
                                        rw [Nat.testBit_or]
                                        cases i with
                                        | zero => simp [Nat.testBit_zero]
                                        | succ n =>
                                          simp [Nat.testBit_succ,
                                            show (2 * pv.toNat + 1) / 2 = pv.toNat by omega]
                                      have h1 : ((pv <<< (1 : Nat)) ||| 1#32).toNat =
                                          2 * pv.toNat + 1 := by
                                        rw [BitVec.toNat_or, hsh,
                                          show (1#32 : BitVec 32).toNat = 1 from rfl, hor]
                                      rw [h1]; dsimp only [st_p0]; omega
                                    c0_hsteps_nogrp; c0_call h_trans_lit
                                    refine ⟨c, F0, st_p0, R, rfl, hsp_p0, hclt0, hlit1, hm4,
                                      fun ok1 st1 m5 hspt1 hclt1 hcvt1 hfuelt1 hws1t1 huns1 hm5 =>
                                        ?_⟩
                                    have hcv_t1 : st1.core.cur_vars = s1.core.cur_vars :=
                                      hcvt1.trans hcv_t0
                                    have hfu_t1 : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                      rw [hfuelt1]; exact hfu_p0
                                    have hws1_t1 : ∀ i < pn.toNat,
                                        (st1.scratch.work_stk1[i]?.getD 0#32).toNat <
                                          s1.core.cur_vars := by
                                      rw [hws1t1]; exact hws1_t0
                                    c0_hsplit
                                    · obtain ⟨F_ct1, hwt1⟩ := hspt1.1.witness
                                      c0_hsteps_nogrp; c0_call h_propagate
                                      refine ⟨c, F0, F_ct1, st1, R, rfl, hspt1.1.lengths, hwt1,
                                        hspt1.2.2.2.2, hm5,
                                        fun _ _ flags2 _ _ _ _ _ _ _ _ _ _ _ _ _ fuel2 _ _ _ _ _
                                          _ _ _ delayed2 m6 hlen6 hw6 _ hperm6 hfu6 _ _ hr1_2 _ _
                                          hm6 => ?_⟩
                                      have hsp_p1 :=
                                        t4b_fullPropagate_del_sparse hspt1 rfl hlen6 hw6 hperm6
                                      have hfu_p1 : fuel2.toNat ≤ s.core.fuel.toNat :=
                                        Nat.le_trans hfu6 hfu_t1
                                      c0_hsplit
                                      · c0_hsteps
                                        exact hB (20#64, pi, ()) m6 ⟨_, hsp_p1, hclt1, hfu_p1,
                                          Or.inr rfl, fun _ => level0_unsat_of_conflict_okW hw6
                                            hclt1 (hr1_2 hc).2.2, hm6⟩
                                      · c0_hsplit
                                        · c0_hsteps
                                          exact hB (1#64, pi, ()) m6 ⟨_, hsp_p1, hclt1, hfu_p1,
                                            Or.inl rfl,
                                            fun h => by dsimp only at h; exact absurd h (by decide),
                                            hm6⟩
                                        · c0_hsteps_nogrp
                                          refine wp_unroll_group fun _ _ => ?_
                                          c0_hsplit
                                          · c0_hsplit
                                            · c0_hsplit
                                              · have hpv_fl2 : pv.toNat < flags2.length := by
                                                  rw [hlen6.core_ok.flags_len]; omega
                                                c0_hsteps
                                                have hsp_cl2 : FullSparseInv c F0 {
                                                  st1 with
                                                  core := { st1.core with
                                                    vals := _, flags := flags2.set pv.toNat
                                                      (flags2[pv.toNat] &&& ~~~512#32),
                                                    lvl := _, rsns := _, trl := _, trail_pos := _,
                                                    trail_end := _, propagated := _,
                                                    unassigned := _, unflushed := _, wvec := _,
                                                    arena := _, wstk := _, wlen := _, wusable := _,
                                                    fuel := fuel2, confl_type := _, confl_ref := _,
                                                    confl_lit0 := _, confl_lit1 := _, oom := _ }
                                                  scratch := { st1.scratch with
                                                    search_ticks := _, wsort := _,
                                                    phases := _, delayed := delayed2 } } :=
                                                  fullSparseInv_clear_fl_trans hsp_p1
                                                exact hJc (1#64, ()) _ ⟨rfl, _, hsp_cl2, hclt1,
                                                  hcv_t1, hfu_p1, hws1_t1,
                                                  by refine t4b_fullMem_eq ?_ (by assumption)
                                                     dsimp only [pv] at hpv64 ⊢
                                                     simp only [hpv64]; rfl⟩
                                              · c0_hsteps
                                                exact hJc (1#64, ()) m6 ⟨rfl, _, hsp_p1, hclt1,
                                                  hcv_t1, hfu_p1, hws1_t1, hm6⟩
                                            · c0_hsteps
                                              exact hJc (1#64, ()) m6 ⟨rfl, _, hsp_p1, hclt1,
                                                hcv_t1, hfu_p1, hws1_t1, hm6⟩
                                          · c0_hsteps
                                            exact hJc (1#64, ()) m6 ⟨rfl, _, hsp_p1, hclt1,
                                              hcv_t1, hfu_p1, hws1_t1, hm6⟩
                                    · c0_hsteps
                                      exact hB (20#64, pi, ()) m5 ⟨st1, hspt1, hclt1, hfu_t1,
                                        Or.inr rfl,
                                        fun _ => huns1 (by revert hc; cases ok1 <;> decide), hm5⟩
                        · c0_hsteps
                          exact hB (20#64, pi, ()) m3 ⟨st0, hspt0, hclt0, hfu_t0, Or.inr rfl,
                            fun _ => huns0 (by revert hc; cases ok0 <;> decide), hm3⟩
                      · c0_hsteps; exact hJelse () ml rfl
                    · c0_hsteps; exact hJelse () ml rfl
                · c0_hsteps; exact hB1
              · c0_hsteps; exact hB1
            · c0_hsteps; exact hB1
          · c0_hsteps; exact hB1
        · intro B L hB hL; c0_hsteps
          exact hL pn.toNat (0#64, ()) _ ⟨_, Nat.zero_le _, by simp,
            fullSparseInv_with_ant_sz hsp_s tick_lim, hcl2, hcv_s2, hfu_s2, hpn_lts,
            (by assumption)⟩
      · intro Js hJs; c0_hsplit
        · c0_hsteps_nogrp; c0_call h_sort
          refine ⟨c, F0, s3, R, rfl, hsp3, by dsimp only [s3]; omega,
            by simpa [hcv_s2] using hpn_lt, hmc,
            fun ws1s ms hws1s hsp_s hpn_lts hms => by
              c0_hsteps
              exact hJs () ms ⟨ws1s, hws1s, by simpa [hcv_s2] using hpn_lts, hsp_s, hms⟩⟩
        · c0_hsteps; exact hJs () mc ⟨ws1, hws1_len, hpn_lt, hsp3, hmc⟩
  · -- Initial `if (h->cur_level != 0) full_backtrack(h, 0)`
    intro J1 hJ1; have hlen := hsp.1.lengths; obtain ⟨F_cur, hw⟩ := hsp.1.witness
    have hcl_lt : s.core.cur_level < 2 ^ 64 := by
      have := hw.cur_level_le; have := (t4b_bnds hlen.core_ok).2.2.2; omega
    c0_hsplit
    · c0_hsteps_nogrp; c0_call h_backtrack
      have htl0 : (0 : BitVec 64).toNat = 0 := rfl
      refine ⟨c, s, R, rfl, hlen, hcl_lt, (fun hpos => by
          have := hlen.core_ok.cur_vars_le; have := hw.cur_level_le
          have := hlen.core_ok.trail_end_le; rw [htl0] at hpos ⊢; omega), hw.trail_lits_lt, hm0,
        fun _ _ _ _ _ _ _ _ _ _ _ hlen1 _ _ hcl1 hpr1 _ _ _ hw1 _ hm1 => by
          c0_hsteps
          exact hJ1 () _ ⟨_, fullBacktrack_sparse hsp rfl hlen1 hpr1 hw1, by simp [hcl1],
            Nat.le_refl _, hm1⟩⟩
    · c0_hsteps
      have hcl0' : s.core.cur_level = 0 := by
        have h1 : s.core.cur_level % 2 ^ 64 = 0 := by c0_bound
        rwa [Nat.mod_eq_of_lt hcl_lt] at h1
      exact hJ1 () m0 ⟨s, hsp, hcl0', Nat.le_refl _, hm0⟩

theorem full_transitive_m6_wp (Γ : Env)
    (h_backtrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (h_prio : ∀ a m Q X, fullPrioritizeBinariesM6Spec a m Q X →
      Γ "full_prioritize_binaries_m6" [i64] [.bool] a m Q X)
    (h_sort : ∀ a m Q X, fullTransSortM6Spec a m Q X →
      Γ "full_trans_sort_m6" [i64, i64] [] a m Q X)
    (h_trans_lit : ∀ a m Q X, fullTransLitM6Spec a m Q X →
      Γ "full_trans_lit_m6" [i64, i32, .bool] [.bool] a m Q X)
    (h_propagate : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (h_defrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Func.wp Γ full_transitive_m6_body a m Q X :=
  full_transitive_m6_del_wp Γ h_backtrack h_prio h_sort h_trans_lit
    (fun a m Q X h => h_propagate a m Q X (fullPropagateSpec_of_del h)) h_defrag

end TransTopM6Proofs

end LeanQbe.T.Examples.Kissat.FullM6VivBackbone
