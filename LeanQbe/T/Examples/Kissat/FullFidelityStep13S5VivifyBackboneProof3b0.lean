/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof0a
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof4b
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Examples.Kissat.FullTransLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S5-B — Transitive Reduction Helpers (`Proof3b0`)

Exports shared pure/WP helper lemmas and factored sub-block WP theorems for
`FullFidelityStep13S5VivifyBackboneProof3b` (`full_trans_lit_m6_s5_wp`,
`full_transitive_m6_s5_wp`), keeping every file `< 1,400` LOC and every theorem `<= 420` lines.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.Full.FullTransHelpers
open LeanQbe.T.Examples.Kissat.FullM6Hdr LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets Kraken.Bedrock2.Test
open scoped FullArenaTactics

section TransLitS5Helpers

theorem s13_tl_fullMem_eq {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (heq : s1 = s2) (hm : (FullMem c s1 ⋆ R) m) : (FullMem c s2 ⋆ R) m := heq ▸ hm

theorem s13_tl_bnds {c : FullCfg} {k : FullCoreState} (hl : k.LengthsOk c) :
    2 * k.cur_vars + 1 < 2 ^ 30 ∧ k.wlen ≤ c.wcap ∧ k.wlen < 2 ^ 64 ∧ k.trail_end < 2 ^ 64 := by
  have := hl.cur_vars_le; have := hl.wlen_le; have := hl.trail_end_le
  have := c.hmaxv; have := c.hwcap; unfold dimacsBound at *; omega

theorem s13_tl_wstk_lt {c : FullCfg} {k : FullCoreState} {p end_v : Nat}
    (hl : FullCoreState.LengthsOk c k) (hp : p < end_v) (he : end_v ≤ k.wlen) :
    p < k.wstk.length := by rw [hl.wstk_len_arr]; have := hl.wlen_le; omega

theorem s13_tl_vals_lt {c : FullCfg} {k : FullCoreState} {l : Nat}
    (hl : FullCoreState.LengthsOk c k) (h : l < 2 * k.cur_vars) :
    l < k.vals.length := by rw [hl.vals_len]; have := hl.cur_vars_le; omega

theorem s13_tl_getElem_toNat {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) :
    (xs[i]'hi).toNat = (xs[i]?.getD 0#32).toNat := by simp [List.getElem?_eq_getElem hi]

theorem s13_tl_bv32_ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

theorem s13_tl_bv64_sub1 {n : Nat} (hn1 : 0 < n) (hn2 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - 1).toNat = n - 1 := by bv_omega

theorem s13_tl_vals_ff_of_domain {v : BitVec 8} {z : BitVec 32}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hz : z = 0#32)
    (hslt : (v.signExtend 32).slt z = true) : v = 0xFF#8 := by
  subst hz; rcases hdom with rfl | rfl | rfl <;> first | rfl | exact absurd hslt (by decide)

theorem s13_tl_vals_zero_of_domain {v : BitVec 8} {z : BitVec 32}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hz : z = 0#32) (heq : v.signExtend 32 = z) :
    v = 0#8 := by
  subst hz; rcases hdom with rfl | rfl | rfl <;> first | rfl | exact absurd heq (by decide)

theorem s13_tl_of_reduced0_full {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 : FullState} {src off p end_v : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (h : TransOuterInv c F0 F_cur s0 src off p end_v 0 st) :
    FullSparseInv c F0 st ∧ FullWitnessInv c F0 F_cur st.core :=
  have hcl : WatchSliceOk F_cur st.core src
      (fullWatchOffCore st.core src) (fullWatchSizeCore st.core src) := by
    rw [h.base.src_off, h.base.src_sz]; exact h.src_full_tomb.to_watchSlice
  ⟨h.base.toSparse hsp0 hw0 hcl, h.base.toWitness_of_src_clean hw0 hcl⟩

theorem s13_tl_del_side_and_tomb {c : FullCfg} {F0 : CNF Nat}
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

theorem s13_tl_compact_done_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

theorem s13_tl_outer_with_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {src off p end_v reduced : Nat} (tk : BitVec 64)
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st) :
    TransOuterInv c F0 F_cur s0 src off p end_v reduced
      { st with scratch := { st.scratch with ant_sz := tk } } :=
  h.with_scratch { h.base.len_ok.scratch_ok with
    walk_vals_len := h.base.len_ok.scratch_ok.walk_vals_len } rfl rfl

theorem s13_tl_unroll_with_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

theorem s13_tl_unroll_c0_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
  have hte1_bv := s13_tl_bv64_sub1 (n := st_r.core.trail_end) (by omega) hte_r_lt
  have hul_vlen := s13_tl_vals_lt (l := ul.toNat) hlen_r.core_ok
    (by rw [hu_r.same_core]; exact hul_lt)
  have huln_vlen := s13_tl_vals_lt (l := (ul ^^^ 1).toNat) hlen_r.core_ok
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

theorem s13_tl_sparse_with_ws1 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {ws1' : List (BitVec 32)} (hsp : FullSparseInv c F0 s) (hlen : ws1'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with work_stk1 := ws1' } } := by
  refine ⟨⟨⟨hsp.1.lengths.core_ok, { hsp.1.lengths.scratch_ok with work_stk1_len := hlen }⟩,
    hsp.1.witness⟩, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩

theorem s13_tl_sparse_of_bcp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64} {sc' : FullScratch}
    (s' : FullState) (hs' : s' = { s with
      core := { s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', unassigned := unass', unflushed := unfl',
        wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
        fuel := fuel', confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
        confl_lit1 := c1', oom := oom' }
      scratch := sc' })
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm' : FullArenaPermEq s.core s'.core)
    (hpr : Full.FullProbeScratchPres { s with scratch := { s.scratch with
      search_ticks := sc'.search_ticks, wsort := sc'.wsort,
      phases := sc'.phases, delayed := sc'.delayed } } s') :
    FullSparseInv c F0 s' := by
  have hspW : FullSparseInvW c F0 F_cur s := ⟨hsp.1.lengths, hw, hsp.2⟩
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    have hr0 : r ∈ fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs at hr ⊢; rwa [hperm'.2.1] at hr
    obtain ⟨_, hgb, hpm⟩ := hperm'.2.2 r hr0
    have hng0 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb at hng ⊢; exact hgb ▸ hng
    unfold fullArenaClauseLits; exact (hpm.map (· / 2)).nodup_iff.mpr (hspW.2.2.2.1 r hr0 hng0)
  have hrefs : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s' := fun r hr => by
    unfold fullArenaClauseRefs at hr ⊢; rwa [hperm'.2.1]
  subst hs'
  have hspW' := FullVivTop.fullSparseInvW_of_prop_state hspW hlen' hw' hnd' hpr hrefs
  exact ⟨⟨hspW'.1, ⟨F_cur, hspW'.2.1⟩⟩, hspW'.2.2⟩

theorem s13_ext_pres_trans_tr {ext0 ext1 ext2 : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (h2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2) :
    M6HdrExtInitOk ext0 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext0 ext2 := fun hi =>
  ⟨(h2 (h1 hi).1).1, (h1 hi).2.trans (h2 (h1 hi).1).2⟩

end TransLitS5Helpers

/-! ## 2. Factored `J6` Exit & Compaction (`s13_tl_compact_wp`) -/

section TransLitCompactS5

abbrev s13TlCompactExpr {V : Ty → Type} {L : List Ty → Type}
    (h : V i64) (src : V i32) (ld_2 ld_3 off_v end_v : V i64)
    (failed : V Ty.bool) (reduced p_cur : V i64) : Expr V L [Ty.bool] :=
  Expr.group (sig := [[i64]]) (fun _Js => Blocks.cons (fun _ => Expr.jnz (Arg.var failed) (
    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 1048, ())) fun p_32 =>
    Expr.load i64 (Arg.var p_32.fst) fun ld =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld, Arg.imm 1, ())) fun p_33 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 1048, ())) fun p_34 =>
    Expr.store (Arg.var p_33.fst) (Arg.var p_34.fst) (
    Expr.call (as := [i64, i32]) (bs := [.bool]) "full_add_unit" (Arg.var h, Arg.var src, ())
      fun p =>
    Expr.ret (Arg.var p.fst, ()))) (Expr.ret (Arg.imm true, ()))) Blocks.nil) fun Js =>
    Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var reduced, Arg.imm 0, ()))
    fun p_31 => Expr.jnz (Arg.var p_31.fst) (Expr.group (sig := [[i64, i64]])
    (fun Js_1 => Blocks.cons (fun p_32 =>
    Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_32.fst, Arg.var end_v, ()))
    fun p_33 => Expr.jnz (Arg.var p_33.fst) (
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_32.fst, Arg.imm 4, ())) fun p =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld_3, Arg.var p.fst, ())) fun p =>
    Expr.load i32 (Arg.var p.fst) fun ld => Expr.group (sig := [[i64, i64]])
    (fun _ => Blocks.cons (fun p =>
    Expr.jump Js_1.fst (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil) fun Js =>
    Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl) (Arg.var ld, Arg.imm 4294967295, ())) fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.let_ (Op.mk (.add i64) (Arg.var p_32.fst, Arg.imm 1, ()))
    fun p => Expr.jump Js.fst (Arg.var p.fst, Arg.var p_32.snd.fst, ())) (Expr.group
    (sig := [[i64, i64]]) (fun _ => Blocks.cons (fun p =>
    Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ()))
    Blocks.nil) fun Js => Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 2147483648, ()))
    fun p => Expr.let_ (Op.mk (.cmp .ne i32 Ty.bool rfl) (Arg.var p.fst, Arg.imm 0, ()))
    fun p => Expr.jnz (Arg.var p.fst) (
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_32.snd.fst, Arg.imm 4, ())) fun p =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld_3, Arg.var p.fst, ())) fun p =>
    Expr.store (Arg.var ld) (Arg.var p.fst) (
    Expr.let_ (Op.mk (.add i64) (Arg.var p_32.snd.fst, Arg.imm 1, ())) fun p =>
    Expr.let_ (Op.mk (.add i64) (Arg.var p_32.fst, Arg.imm 1, ())) fun p_34 =>
    Expr.jump Js.fst (Arg.var p_34.fst, Arg.var p.fst, ()))) (Expr.group
    (sig := [[i64, i64]]) (fun _ => Blocks.cons (fun p =>
    Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ()))
    Blocks.nil) fun Js => Expr.let_ (Op.mk (.add i64) (Arg.var p_32.fst, Arg.imm 1, ()))
    fun p =>
    Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p.fst, Arg.var end_v, ()))
    fun p => Expr.jnz (Arg.var p.fst) (
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_32.snd.fst, Arg.imm 4, ())) fun p =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld_3, Arg.var p.fst, ())) fun p =>
    Expr.store (Arg.var ld) (Arg.var p.fst) (
    Expr.let_ (Op.mk (.add i64) (Arg.var p_32.snd.fst, Arg.imm 1, ())) fun p =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld_3, Arg.var p.fst, ())) fun p =>
    Expr.let_ (Op.mk (.add i64) (Arg.var p_32.fst, Arg.imm 1, ())) fun p_34 =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_34.fst, Arg.imm 4, ())) fun p_35 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld_3, Arg.var p_35.fst, ())) fun p_36 =>
    Expr.load i32 (Arg.var p_36.fst) fun ld => Expr.store (Arg.var ld) (Arg.var p.fst) (
    Expr.let_ (Op.mk (.add i64) (Arg.var p_32.snd.fst, Arg.imm 2, ())) fun p =>
    Expr.let_ (Op.mk (.add i64) (Arg.var p_32.fst, Arg.imm 2, ())) fun p_37 =>
    Expr.jump Js.fst (Arg.var p_37.fst, Arg.var p.fst, ())))) (
    Expr.let_ (Op.mk (.add i64) (Arg.var p_32.fst, Arg.imm 1, ())) fun p =>
    Expr.jump Js.fst (Arg.var p.fst, Arg.var p_32.snd.fst, ()))))) (Expr.group
    (sig := [[i64]]) (fun Js_2 => Blocks.cons (fun p_34 =>
    Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_34.fst, Arg.var end_v, ()))
    fun p_35 => Expr.jnz (Arg.var p_35.fst) (
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_34.fst, Arg.imm 4, ())) fun p =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld_3, Arg.var p.fst, ())) fun p =>
    Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p.fst) (
    Expr.let_ (Op.mk (.add i64) (Arg.var p_34.fst, Arg.imm 1, ())) fun p =>
    Expr.jump Js_2.fst (Arg.var p.fst, ()))) (
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var src, ())) fun p_36 =>
    Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun p_37 =>
    Expr.let_ (Op.mk (.shl i64) (Arg.var p_36.fst, Arg.var p_37.fst, ())) fun p_38 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var p_38.fst, Arg.imm 1, ())) fun p_39 =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_39.fst, Arg.imm 4, ())) fun p_40 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld_2, Arg.var p_40.fst, ())) fun p_41 =>
    Expr.let_ (Op.mk (.sub i64) (Arg.var end_v, Arg.var off_v, ())) fun p_42 =>
    Expr.let_ (Op.mk (.sub i64) (Arg.var p_42.fst, Arg.var reduced, ())) fun p_43 =>
    Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p_43.fst, ())) fun p_44 =>
    Expr.store (Arg.var p_44.fst) (Arg.var p_41.fst) (
    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 464, ())) fun p_45 =>
    Expr.load i64 (Arg.var p_45.fst) fun ld =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld, Arg.var reduced, ())) fun p_46 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 464, ())) fun p_47 =>
    Expr.store (Arg.var p_46.fst) (Arg.var p_47.fst) (Expr.group (sig := [[]]) (fun _Js_3 =>
    Blocks.cons (fun _ => Expr.jump Js.fst (Arg.var p_32.fst, ())) Blocks.nil) fun Js =>
    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 504, ())) fun p_48 =>
    Expr.load i64 (Arg.var p_48.fst) fun ld =>
    Expr.let_ (Op.mk (.cmp .uge i64 Ty.bool rfl) (Arg.var ld, Arg.var reduced, ()))
    fun p_49 => Expr.jnz (Arg.var p_49.fst) (
    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 504, ())) fun p_50 =>
    Expr.load i64 (Arg.var p_50.fst) fun ld =>
    Expr.let_ (Op.mk (.sub i64) (Arg.var ld, Arg.var reduced, ())) fun p_51 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 504, ())) fun p =>
    Expr.store (Arg.var p_51.fst) (Arg.var p.fst) (Expr.jump Js.fst ())) (
    Expr.jump Js.fst ()))))) Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.var p_32.snd.fst, ()))) Blocks.nil) fun Js =>
    Expr.jump Js.fst (Arg.var off_v, Arg.var off_v, ())) (
    Expr.jump Js.fst (Arg.var p_cur, ()))

theorem s13_tl_compact_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    (h_add_unit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st2 : FullState} {R : Mem 64 → Prop}
    {src : BitVec 32} {failed : Bool} {reduced p_cur : BitVec 64} {off sz : Nat} {m2 : Mem 64}
    (hsp : FullSparseInv c F0 s) (hw0 : FullWitnessInv c F0 F_cur s.core)
    (hsrc_lt : src.toNat < 2 * s.core.cur_vars)
    (hoff_32 : off < 2 ^ 32) (hsz_32 : sz < 2 ^ 32) (hend_lt : off + sz < 2 ^ 64)
    (hp_lo2 : off ≤ p_cur.toNat) (hp_hi2 : p_cur.toNat ≤ off + sz)
    (hred_le2 : reduced.toNat ≤ p_cur.toNat - off)
    (hto2 : TransOuterInv c F0 F_cur s src.toNat off p_cur.toNat (off + sz) reduced.toNat st2)
    (hfail2 : failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat]))
    (hcv2 : st2.core.cur_vars = s.core.cur_vars) (hfuel2 : st2.core.fuel = s.core.fuel)
    (hws1_2 : st2.scratch.work_stk1 = s.scratch.work_stk1) (hm2 : (FullMem c st2 ⋆ R) m2)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (s13TlCompactExpr c.hdr src c.pWvec c.pWstk (BitVec.ofNat 64 off)
      (BitVec.ofNat 64 (off + sz)) failed reduced p_cur) m2 := by
  unfold s13TlCompactExpr
  have hlen0 := hsp.1.lengths; have hlen2 := hto2.base.len_ok
  have hof64 : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hen64 : (BitVec.ofNat 64 (off + sz)).toNat = off + sz := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hend_lt]
  have hsrc64 : (src.setWidth 64 <<< (1 : Nat)).toNat = 2 * src.toNat := by
    have := (s13_tl_bnds hlen0.core_ok).1
    rw [ft_bv64_shl1 (by rw [ft_bv32_setWidth64]; omega), ft_bv32_setWidth64]
  have hsrc64_1 : ((src.setWidth 64 <<< (1 : Nat)) + 1).toNat = 2 * src.toNat + 1 := by
    have := (s13_tl_bnds hlen0.core_ok).1
    rw [show (1 : BitVec 64) = 1#64 from rfl, ft_bv64_add1 (by rw [hsrc64]; omega), hsrc64]
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
      obtain ⟨hsp_tc, hw_tc⟩ := fullSparseInv_with_trans_cnt hspf hwf (stf.scratch.trans_cnt + 1)
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
      exact hQ true stf m3 hspf hclf hcvf hfuelf hws1f (fun h => absurd h (by decide)) hm3
  · intro J6 hJ6; c0_hsplit
    · have hred_pos : 0 < reduced.toNat := by c0_bound
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i64, i64])
        (Inv := fun nc xs m3 => let pc := xs.1; let qc := xs.2.1
          ∃ stc : FullState, off ≤ qc.toNat ∧ qc.toNat ≤ pc.toNat ∧ pc.toNat ≤ off + sz ∧
            nc = (off + sz) - pc.toNat ∧
            TransCompactInv c F0 F_cur s src.toNat off qc.toNat pc.toNat (off + sz)
              reduced.toNat stc ∧
            stc.core.cur_vars = s.core.cur_vars ∧ stc.core.fuel = s.core.fuel ∧
            stc.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c stc ⋆ R) m3) ?_ ?_
      · rintro L8 nc ⟨pc, qc, ⟨⟩⟩ m3 hL8
          ⟨stc, hql, hqp, hpe, hcneq, hci, hcvc, hfuelc, hws1c, hm3⟩
        dsimp only at hql hqp hpe hcneq hci; have hlenc := hci.base.len_ok
        c0_hsplit
        · have hpc_lt : pc.toNat < off + sz := by
            have h1 : pc.toNat < (BitVec.ofNat 64 (off + sz)).toNat := by c0_bound
            rwa [hen64] at h1
          have hpc_len := s13_tl_wstk_lt hlenc.core_ok hpc_lt hci.base.end_le_wlen
          have hpc1 : (pc + 1#64).toNat = pc.toNat + 1 := ft_bv64_add1 (by omega)
          c0_hsteps_nogrp; refine wp_unroll_group fun _ _ => ?_
          c0_hsplit
          · have ht_pc : stc.core.wstk[pc.toNat]? = some 0xFFFFFFFF#32 := by
              rw [List.getElem?_eq_getElem hpc_len]; exact congrArg some hc
            c0_hsteps
            exact hL8 ((off + sz) - (pc.toNat + 1)) (pc + 1#64, qc, ()) m3 (by omega)
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
              exact hL8 ((off + sz) - (pc.toNat + 1)) (pc + 1#64, qc + 1#64, ()) _ (by omega)
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
                have hpc1_len := s13_tl_wstk_lt (p := (pc + 1#64).toNat) hlenc.core_ok
                  (by rw [hpc1]; exact hp1_lt) hci.base.end_le_wlen
                have hqc1_len := s13_tl_wstk_lt (p := (qc + 1#64).toNat) hlenc.core_ok
                  (by rw [hqc1]; exact Nat.lt_of_lt_of_le (by omega) hp1_lt) hci.base.end_le_wlen
                c0_hsteps
                have hw1_hm : (stc.core.wstk.set qc.toNat stc.core.wstk[pc.toNat])[(pc +
                    1#64).toNat]'(by rw [List.length_set]; exact hpc1_len) = w1 := by
                  rw [List.getElem_set_ne (by omega : qc.toNat ≠ (pc + 1#64).toNat)]
                  exact Option.some.inj
                    ((List.getElem?_eq_getElem hpc1_len).symm.trans (by rw [hpc1, hw1_get]))
                rw [← hpc2, ← hqc2, ← hqc1, ← hw1_hm] at hci_l
                exact hL8 ((off + sz) - (pc.toNat + 2)) (pc + 2#64, qc + 2#64, ()) _ (by omega)
                  ⟨_, by dsimp only; rw [hqc2]; omega, by dsimp only; rw [hpc2, hqc2]; omega,
                   by dsimp only; rw [hpc2]; omega, by dsimp only; rw [hpc2], hci_l, hcvc,
                   hfuelc, hws1c, (by assumption)⟩
              · exfalso
                have h1 : ¬((pc + 1#64).toNat < (BitVec.ofNat 64 (off + sz)).toNat) := by c0_bound
                rw [hen64, hpc1] at h1; exact h1 hp1_lt
        · have hpc_end : pc.toNat = off + sz := by
            have h1 : ¬(pc.toNat < (BitVec.ofNat 64 (off + sz)).toNat) := by c0_bound
            rw [hen64] at h1; omega
          rw [hpc_end] at hci; obtain ⟨hq_eq, hq_lo, hq_hi, hsl⟩ := hci.at_end
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64])
            (Inv := fun nq xs m4 => let qf := xs.1
              ∃ stq : FullState, off ≤ (off + sz) - reduced.toNat ∧
                (off + sz) - reduced.toNat ≤ qf.toNat ∧
                qf.toNat ≤ off + sz ∧ nq = (off + sz) - qf.toNat ∧
                TransOuterBase c F0 F_cur s src.toNat off (off + sz) stq ∧
                WatchSliceOk F_cur stq.core src.toNat off ((off + sz) - off - reduced.toNat) ∧
                stq.core.cur_vars = s.core.cur_vars ∧ stq.core.fuel = s.core.fuel ∧
                stq.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c stq ⋆ R) m4) ?_ ?_
          · rintro L11 nq ⟨qf, ⟨⟩⟩ m4 hL11
              ⟨stq, hqo, hql2, hqh, hqneq, hbq, hslq, hcvq, hfuelq, hws1q, hm4⟩
            dsimp only at hqo hql2 hqh hqneq hbq hslq; have hlenq := hbq.len_ok
            have hsrc_q : src.toNat < 2 * stq.core.cur_vars := by rw [hcvq]; exact hsrc_lt
            c0_hsplit
            · have hq_lt : qf.toNat < off + sz := by
                have h1 : qf.toNat < (BitVec.ofNat 64 (off + sz)).toNat := by c0_bound
                rwa [hen64] at h1
              have hqf_len := s13_tl_wstk_lt hlenq.core_ok hq_lt hbq.end_le_wlen
              c0_hsteps
              have hq1 : (qf + 1#64).toNat = qf.toNat + 1 := ft_bv64_add1 (by omega)
              obtain ⟨hbq', hslq'⟩ := hbq.sentinel_fill_step hsrc_q ⟨hqo, hql2, hq_lt⟩
                (by rwa [show ((off + sz) - reduced.toNat) - off =
                  (off + sz) - off - reduced.toNat by omega])
              exact hL11 ((off + sz) - (qf.toNat + 1)) (qf + 1#64, ()) _ (by omega) ⟨_, hqo,
                by dsimp only; rw [hq1]; omega, by dsimp only; rw [hq1]; omega,
                by dsimp only; rw [hq1], hbq', by simpa only [(show (off + sz) - reduced.toNat - off
                  = (off + sz) - off - reduced.toNat by omega)] using hslq',
                hcvq, hfuelq, hws1q, (by assumption)⟩
            · have hred_off : reduced.toNat ≤ (off + sz) - off := by omega
              have hq_wv1 : (BitVec.setWidth 64 src <<< (1 : Nat) + 1).toNat <
                  stq.core.wvec.length := by
                rw [hsrc64_1, hlenq.core_ok.wvec_len]; have := hlenq.core_ok.cur_vars_le; omega
              have hclq : stq.core.cur_level = 0 := hbq.core_pres.2.1
              have h_wsz_bv : BitVec.setWidth 32
                  (BitVec.ofNat 64 (off + sz) - BitVec.ofNat 64 off - reduced) =
                  BitVec.ofNat 32 ((off + sz) - off - reduced.toNat) := by
                apply BitVec.eq_of_toNat_eq
                have hsub : (BitVec.ofNat 64 (off + sz) - BitVec.ofNat 64 off - reduced).toNat =
                    sz - reduced.toNat := by bv_omega
                rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hsub,
                  show off + sz - off - reduced.toNat = sz - reduced.toNat by omega,
                  Nat.mod_eq_of_lt (by omega)]
              c0_hsteps_nogrp; refine wp_unroll_group fun _ _ => ?_
              c0_hsplit
              · c0_hsteps
                obtain ⟨hsp_d, hw_d⟩ := s13_tl_compact_done_eq hsp hw0 hbq hsrc_q hred_off hslq
                  (wu' := stq.core.wusable + reduced) (nb_bv := stq.core.num_binary - reduced)
                  hsrc64_1 h_wsz_bv
                exact hJ6 (pc, ()) _ ⟨_, hsp_d, hw_d, hclq, hcvq, hfuelq, hws1q, hfail2,
                  (by assumption)⟩
              · c0_hsteps
                obtain ⟨hsp_d, hw_d⟩ := s13_tl_compact_done_eq hsp hw0 hbq hsrc_q hred_off hslq
                  (wu' := stq.core.wusable + reduced) (nb_bv := stq.core.num_binary)
                  hsrc64_1 h_wsz_bv
                exact hJ6 (pc, ()) _ ⟨_, hsp_d, hw_d, hclq, hcvq, hfuelq, hws1q, hfail2,
                  (by assumption)⟩
          · intro L11 hL11; c0_hsteps
            exact hL11 ((off + sz) - qc.toNat) (qc, ()) m3 ⟨stc, hq_lo,
              by dsimp only; rw [hq_eq]; exact Nat.le_refl _,
              by dsimp only; rw [hq_eq]; exact hq_hi, rfl, hci.base, hsl, hcvc, hfuelc, hws1c,
              hm3⟩
      · intro L8 hL8; c0_hsteps
        exact hL8 ((off + sz) - off) (BitVec.ofNat 64 off, BitVec.ofNat 64 off, ()) m2 ⟨st2,
          (by dsimp only; rw [hof64]; exact Nat.le_refl _),
          (by dsimp only; rw [hof64]; exact Nat.le_refl _),
          by dsimp only; rw [hof64]; exact hto2.base.off_le_end, by dsimp only; rw [hof64],
          by dsimp only; rw [hof64]; exact TransCompactInv.init hto2, hcv2, hfuel2, hws1_2, hm2⟩
    · have hred0 : reduced.toNat = 0 := by c0_bound
      c0_hsteps; rw [hred0] at hto2
      obtain ⟨hsp2, hw2⟩ := s13_tl_of_reduced0_full hsp hw0 hto2
      exact hJ6 (p_cur, ()) m2 ⟨st2, hsp2, hw2, hto2.base.core_pres.2.1, hcv2, hfuel2, hws1_2,
        hfail2, hm2⟩

end TransLitCompactS5

/-! ## 3. Factored `J15` Unroll + Delete (`s13_tl_unroll_wp`) -/

section TransLitUnrollS5

abbrev s13TlUnrollExpr {V : Ty → Type} {L : List Ty → Type}
    (h : V i64) (src : V i32) (ld ld_3 ld_4 ld_12 : V i64)
    (reduced p_cur : V i64) (dst : V i32) (fb : V Ty.bool) (tk : V i64) (tb : V Ty.bool)
    (Js_1 : L [Ty.bool, i64, i64]) : Expr V L [Ty.bool] :=
  Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 1136, ())) fun p_64 =>
  Expr.store (Arg.var tk) (Arg.var p_64.fst) (Expr.group (sig := [[]]) (fun Js => Blocks.cons (
  fun _ => Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 144, ())) fun p_66 =>
  Expr.load i64 (Arg.var p_66.fst) fun ld_13 =>
  Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld_13, Arg.var ld_12, ()))
  fun p_67 => Expr.jnz (Arg.var p_67.fst) (
  Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 144, ())) fun p_68 =>
  Expr.load i64 (Arg.var p_68.fst) fun ld_14 =>
  Expr.let_ (Op.mk (.sub i64) (Arg.var ld_14, Arg.imm 1, ())) fun p_69 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 144, ())) fun p_70 =>
  Expr.store (Arg.var p_69.fst) (Arg.var p_70.fst) (
  Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 144, ())) fun p =>
  Expr.load i64 (Arg.var p.fst) fun ld_15 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var ld_15, Arg.imm 4, ())) fun p =>
  Expr.let_ (Op.mk (.add i64) (Arg.var ld_4, Arg.var p.fst, ())) fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld_16 =>
  Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_16, ())) fun p =>
  Expr.let_ (Op.mk (.add i64) (Arg.var ld, Arg.var p.fst, ())) fun p =>
  Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p_71 =>
  Expr.store (Arg.var p_71.fst) (Arg.var p.fst) (
  Expr.let_ (Op.mk (.xor i32) (Arg.var ld_16, Arg.imm 1, ())) fun p =>
  Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.fst, ())) fun p =>
  Expr.let_ (Op.mk (.add i64) (Arg.var ld, Arg.var p.fst, ())) fun p =>
  Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p_72 =>
  Expr.store (Arg.var p_72.fst) (Arg.var p.fst) (Expr.jump Js.fst ())))) (Expr.group
  (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
  Expr.let_ (Op.mk (.add i64) (Arg.var p_cur, Arg.imm 1, ())) fun p_68 =>
  Expr.jump Js_1 (Arg.var fb, Arg.var p.fst, Arg.var p_68.fst, ())) Blocks.nil)
  fun Js => Expr.jnz (Arg.var tb) (
  Expr.call (as := [i64, i32, i32]) (bs := []) "full_delete_bin_side"
    (Arg.var h, Arg.var dst, Arg.var src, ())
  fun _ => Expr.let_ (Op.mk (.mul i64) (Arg.var p_cur, Arg.imm 4, ()))
  fun p_69 => Expr.let_ (Op.mk (.add i64) (Arg.var ld_3, Arg.var p_69.fst, ())) fun p_70 =>
  Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p_70.fst) (
  Expr.let_ (Op.mk (.add i64) (Arg.var reduced, Arg.imm 1, ())) fun p_71 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 1048, ())) fun p_72 =>
  Expr.load i64 (Arg.var p_72.fst) fun ld =>
  Expr.let_ (Op.mk (.add i64) (Arg.var ld, Arg.imm 1, ())) fun p_73 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 1048, ())) fun p =>
  Expr.store (Arg.var p_73.fst) (Arg.var p.fst) (Expr.jump Js.fst (Arg.var p_71.fst, ())))) (
  Expr.jump Js.fst (Arg.var reduced, ())))) Blocks.nil) fun Js => Expr.jump Js.fst ())

theorem s13_tl_unroll_wp {Γ : Env} {Js_1 : Cont [Ty.bool, i64, i64]}
    {Q_fn : Post [Ty.bool]} {X : XPost}
    (h_del_bin : ∀ a m Q X, fullDeleteBinSideSpec a m Q X →
      Γ "full_delete_bin_side" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st st_u : FullState}
    {R : Mem 64 → Prop} {src dst : BitVec 32} {fb tb : Bool}
    {reduced p_cur tk : BitVec 64} {off sz saved : Nat} {m3 : Mem 64}
    (hw0 : FullWitnessInv c F0 F_cur s.core)
    (hsrc_lt : src.toNat < 2 * s.core.cur_vars)
    (hdst_lt0 : dst.toNat < 2 * s.core.cur_vars) (hdst_ne : dst.toNat ≠ src.toNat)
    (hp_lo : off ≤ p_cur.toNat) (hp_lt : p_cur.toNat < off + sz)
    (hred_le : reduced.toNat ≤ p_cur.toNat - off)
    (hto : TransOuterInv c F0 F_cur s src.toNat off p_cur.toNat (off + sz) reduced.toNat st)
    (hcv_st : st.core.cur_vars = s.core.cur_vars) (hfuel_st : st.core.fuel = s.core.fuel)
    (hws1_st : st.scratch.work_stk1 = s.scratch.work_stk1)
    (hp_len : p_cur.toNat < st.core.wstk.length)
    (_hw0_eq : st.core.wstk[p_cur.toNat]'hp_len &&& 0x7FFFFFFF#32 = dst)
    (hfl_nz : (st.core.wstk[p_cur.toNat]'hp_len &&& 0x80000000#32) ≠ 0#32)
    (hpre_vals : st.core.vals = s.core.vals) (hsav_eq : st.core.trail_end = saved)
    (hsav_lt : saved < 2 ^ 64)
    (hu_u : TransUnrollInv c F0 F_cur s st src.toNat saved st_u)
    (hfb_u : fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat]))
    (hm3 : (FullMem c st_u ⋆ R) m3)
    (hL : ∀ (failed' : Bool) (red' p' : BitVec 64) (m' : Mem 64),
      (off + sz - p'.toNat < off + sz - p_cur.toNat) →
      (∃ st_d : FullState, off ≤ p'.toNat ∧ p'.toNat ≤ off + sz ∧
        red'.toNat ≤ p'.toNat - off ∧
        TransOuterInv c F0 F_cur s src.toNat off p'.toNat (off + sz) red'.toNat st_d ∧
        (failed' = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        st_d.core.cur_vars = s.core.cur_vars ∧ st_d.core.fuel = s.core.fuel ∧
        st_d.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c st_d ⋆ R) m') →
      Js_1 (failed', red', p', ()) m') :
    wp Γ Q_fn X (s13TlUnrollExpr c.hdr src c.pVals c.pWstk c.pTrail (BitVec.ofNat 64 saved)
      reduced p_cur dst fb tk tb Js_1) m3 := by
  unfold s13TlUnrollExpr
  c0_hsteps_nogrp
  let st_pre2 : FullState := { st with scratch := { st.scratch with ant_sz := tk } }
  let st_u2 : FullState := { st_u with scratch := { st_u.scratch with ant_sz := tk } }
  have hto_pre2 := s13_tl_outer_with_ant_sz tk hto
  have hu_u2 : TransUnrollInv c F0 F_cur s st_pre2 src.toNat saved st_u2 :=
    s13_tl_unroll_with_ant_sz tk hu_u
  refine wp_loop_group (ts := []) (Inv := fun nu _ m4 => ∃ st_r : FullState,
      nu = st_r.core.trail_end - saved ∧
      TransUnrollInv c F0 F_cur s st_pre2 src.toNat saved st_r ∧
      (FullMem c st_r ⋆ R) m4) ?_ ?_
  · rintro L17 nu ⟨⟩ m4 hL17 ⟨st_r, huneq, hu_r, hm4⟩
    have hlen_r := hu_r.len_ok
    have hte_r_lt : st_r.core.trail_end < 2 ^ 64 := (s13_tl_bnds hlen_r.core_ok).2.2.2
    c0_hsplit
    · have hte_gt : saved < st_r.core.trail_end := by
        have h1 : saved % 2 ^ 64 < st_r.core.trail_end % 2 ^ 64 := by c0_bound
        rwa [Nat.mod_eq_of_lt hsav_lt, Nat.mod_eq_of_lt hte_r_lt] at h1
      obtain ⟨hte1_bv_len, hul_sw_bv, huln_sw_bv, hte1_bv, hu_r''⟩ :=
        s13_tl_unroll_c0_aux (st_pre := st_pre2) hw0 hpre_vals hcv_st
          hto_pre2.base.len_ok hu_r hte_gt hte_r_lt
      have huln_sw_set : (BitVec.setWidth 64 (st_r.core.trl[(BitVec.ofNat 64
          (BitVec.ofNat 64 st_r.core.trail_end - 1).toNat).toNat]'hte1_bv_len ^^^ 1)).toNat <
          (st_r.core.vals.set (BitVec.setWidth 64 (st_r.core.trl[(BitVec.ofNat 64
          (BitVec.ofNat 64 st_r.core.trail_end - 1).toNat).toNat]'hte1_bv_len)).toNat
            0#8).length := by rw [List.length_set]; exact huln_sw_bv
      c0_hsteps
      exact hL17 (st_r.core.trail_end - 1 - saved) () _ (by omega)
        ⟨_, by dsimp only; rw [hte1_bv], hu_r'', (by assumption)⟩
    · have hte_eq : st_r.core.trail_end = saved := by
        have h1 : ¬(saved % 2 ^ 64 < st_r.core.trail_end % 2 ^ 64) := by c0_bound
        rw [Nat.mod_eq_of_lt hsav_lt, Nat.mod_eq_of_lt hte_r_lt] at h1
        have := hu_r.saved_le_te; omega
      have hto_done := hu_r.done hto_pre2 hte_eq
      have hp1_bv : (p_cur + 1#64).toNat = p_cur.toNat + 1 :=
        ft_bv64_add1
          (by have := hto_done.base.end_le_wlen; have := (s13_tl_bnds hlen_r.core_ok).2.2.1; omega)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (P := fun xs m5 => let red' := xs.1
          ∃ st_d : FullState, red'.toNat ≤ p_cur.toNat + 1 - off ∧
            TransOuterInv c F0 F_cur s src.toNat off (p_cur.toNat + 1) (off + sz) red'.toNat st_d ∧
            st_d.core.cur_vars = s.core.cur_vars ∧ st_d.core.fuel = s.core.fuel ∧
            st_d.scratch.work_stk1 = s.scratch.work_stk1 ∧ (FullMem c st_d ⋆ R) m5) ?_ ?_
      · rintro J20 ⟨red', ⟨⟩⟩ m5 ⟨st_d, hrl_d, hto_d, hcv_d, hfuel_d, hws1_d, hm5⟩
        c0_hsteps
        exact hL fb red' (p_cur + 1#64) m5 (by rw [hp1_bv]; omega)
          ⟨st_d, by rw [hp1_bv]; omega, by rw [hp1_bv]; omega,
           by rw [hp1_bv]; exact hrl_d, by rw [hp1_bv]; exact hto_d,
           fun hf => hfb_u hf, hcv_d, hfuel_d, hws1_d, hm5⟩
      · intro J20 hJ20
        have hget_r : st_r.core.wstk[p_cur.toNat]? = some (st.core.wstk[p_cur.toNat]'hp_len) := by
          rw [hu_r.same_core, List.getElem?_eq_getElem hp_len]
        have hfl_r : (st.core.wstk[p_cur.toNat]'hp_len &&& 0x80000000#32) ≠ 0#32 := hfl_nz
        c0_hsplit
        · c0_hsteps_nogrp; c0_call h_del_bin
          have hdst_lt_d : dst.toNat < 2 * st_r.core.cur_vars := by
            rw [hu_r.same_core, hcv_st]; exact hdst_lt0
          have hsrc_lt_d : src.toNat < 2 * st_r.core.cur_vars := by
            rw [hu_r.same_core, hcv_st]; exact hsrc_lt
          refine ⟨c, st_r, R, rfl, hlen_r,
            fun _ => hto_done.base.other_bounds dst.toNat hdst_lt_d hdst_ne, hm4,
            fun wvec' wstk' wu' m5 hlen5 hdst_ws hother_ws hwstk_out hdst_sl _ _ _ hm5 => ?_⟩
          have hp_wc : p_cur.toNat < c.wcap := by
            have := hto_done.base.end_le_wlen; have := hlen_r.core_ok.wlen_le; omega
          have hred1 : (reduced + 1#64).toNat = reduced.toNat + 1 :=
            ft_bv64_add1
              (by have := hto_done.base.end_le_wlen; have := hlen_r.core_ok.wlen_le; omega)
          have hto_mk := s13_tl_del_side_and_tomb hto_done hp_lt hp_wc hsrc_lt_d
            hdst_lt_d hdst_ne hget_r hfl_r rfl hlen5
            (by dsimp only [Arg.val_var] at *; exact hdst_ws hdst_lt_d) hother_ws
            (fun idx hidx ho => hwstk_out idx hidx
              (fun _ => by dsimp only [Arg.val_var] at *; exact ho))
            (by dsimp only [Arg.val_var] at *; exact hdst_sl F_cur)
            (tc' := st_r.scratch.trans_cnt + 1)
          have hp_l5 : p_cur.toNat < wstk'.length := by rw [hlen5.core_ok.wstk_len_arr]; omega
          c0_hsteps
          exact hJ20 (reduced + 1#64, ()) _ ⟨_, by rw [hred1]; omega,
            by rw [hred1]; exact hto_mk, by dsimp only; rw [hu_r.same_core, hcv_st],
            by dsimp only; rw [hu_r.same_core, hfuel_st],
            by dsimp only; rw [hu_r.same_scratch]; exact hws1_st, (by assumption)⟩
        · obtain ⟨_, _, _, hto_nxt⟩ := hto_done.skip_bin hp_lt hget_r hfl_r
          c0_hsteps
          exact hJ20 (reduced, ()) m4 ⟨st_r, by dsimp only; omega, hto_nxt,
            by rw [hu_r.same_core, hcv_st], by rw [hu_r.same_core, hfuel_st],
            by rw [hu_r.same_scratch]; exact hws1_st, hm4⟩
  · intro L17 hL17; c0_hsteps
    exact hL17 (st_u2.core.trail_end - saved) () _ ⟨st_u2, rfl, hu_u2, (by assumption)⟩

end TransLitUnrollS5

/-! ## 4. Factored `L20` Inner Watch Loop (`s13_tl_inner_watch_wp`) -/

section TransLitInnerWatchS5

abbrev s13TlInnerWatchExpr {V : Ty → Type} {L : List Ty → Type}
    (h : V i64) (src : V i32) (stop_early : V Ty.bool)
    (ld ld_3 ld_4 nlits loff_v lend_v tk_m1 p_cur : V i64)
    (dst nl : V i32) (fb : V Ty.bool) (tb : V Ty.bool)
    (Js_19 : L [Ty.bool, i64, Ty.bool, i64]) : Expr V L [Ty.bool] :=
  Expr.group (sig := [[i64, i64]]) (fun Js_3 => Blocks.cons (fun p_85 =>
    Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_85.snd.fst, Arg.var lend_v, ()))
    fun p_86 => Expr.jnz (Arg.var p_86.fst) (
    Expr.let_ (Op.mk (.mul i64) (Arg.var p_85.snd.fst, Arg.imm 4, ())) fun p_87 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld_3, Arg.var p_87.fst, ())) fun p_88 =>
    Expr.load i32 (Arg.var p_88.fst) fun ld_17 =>
    Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl) (Arg.var ld_17, Arg.imm 4294967295, ()))
    fun p_89 => Expr.jnz (Arg.var p_89.fst) (
    Expr.let_ (Op.mk (.add i64) (Arg.var p_85.snd.fst, Arg.imm 1, ())) fun p =>
    Expr.jump Js_3.fst (Arg.var p_85.fst, Arg.var p.fst, ())) (
    Expr.let_ (Op.mk (.and i32) (Arg.var ld_17, Arg.imm 2147483648, ())) fun p_90 =>
    Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl) (Arg.var p_90.fst, Arg.imm 0, ())) fun p_91 =>
    Expr.jnz (Arg.var p_91.fst) (Expr.jnz (Arg.var stop_early) (
    Expr.jump Js_19 (Arg.var fb, Arg.var p_85.fst, Arg.var tb, Arg.var p_85.snd.fst, ())) (
    Expr.let_ (Op.mk (.add i64) (Arg.var p_85.snd.fst, Arg.imm 2, ())) fun p => Expr.group
    (sig := [[i64]]) (fun _ => Blocks.cons (fun p_92 =>
    Expr.jump Js_3.fst (Arg.var p_92.fst, Arg.var p.fst, ())) Blocks.nil) fun Js =>
    Expr.let_ (Op.mk (.sub i64) (Arg.var p.fst, Arg.var loff_v, ())) fun p =>
    Expr.let_ (Op.mk (.and i64) (Arg.var p.fst, Arg.imm 31, ())) fun p =>
    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 0, ())) fun p =>
    Expr.jnz (Arg.var p.fst) (
    Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var p_85.fst, Arg.imm 0, ())) fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.let_ (Op.mk (.sub i64) (Arg.var p_85.fst, Arg.imm 1, ()))
    fun p => Expr.jump Js.fst (Arg.var p.fst, ())) (Expr.jump Js.fst (Arg.var p_85.fst, ()))) (
    Expr.jump Js.fst (Arg.var p_85.fst, ())))) (Expr.group (sig := [[]]) (fun _Js_4 => Blocks.cons
    (fun _ => Expr.let_ (Op.mk (.add i64) (Arg.var p_85.snd.fst, Arg.imm 1, ())) fun p_93 =>
    Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p_94 =>
    Expr.let_ (Op.mk (.and i32) (Arg.var ld_17, Arg.imm 2147483647, ())) fun p_95 =>
    Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl) (Arg.var p_95.fst, Arg.var dst, ()))
    fun p_96 => Expr.jnz (Arg.var p_96.fst) (
    Expr.jump Js_19 (Arg.var fb, Arg.var p_94.fst, Arg.imm true, Arg.var p_93.fst, ())) (
    Expr.group (sig := [[Ty.bool]]) (fun _ => Blocks.cons (fun _ =>
    Expr.jump Js_3.fst (Arg.var p_94.fst, Arg.var p_93.fst, ())) Blocks.nil) fun Js_6 =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_95.fst, ())) fun p_97 =>
    Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_97.fst, Arg.var nlits, ()))
    fun p_98 => Expr.jnz (Arg.var p_98.fst) (
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_95.fst, ())) fun p_99 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld, Arg.var p_99.fst, ())) fun p_100 =>
    Expr.load i8 (Arg.var p_100.fst) fun ld_18 =>
    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p_101 =>
    Expr.let_ (Op.mk (.sext 8 32) (Arg.var ld_18, ())) fun p_102 =>
    Expr.let_ (Op.mk (.sext 8 32) (Arg.var p_101.fst, ())) fun p_103 =>
    Expr.let_ (Op.mk (.cmp .slt i32 Ty.bool rfl) (Arg.var p_102.fst, Arg.var p_103.fst, ()))
    fun p_104 => Expr.jnz (Arg.var p_104.fst) (
    Expr.jump Js_19 (Arg.imm true, Arg.var p_94.fst, Arg.var tb, Arg.var p_93.fst, ())) (
    Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => Expr.jump Js_6.fst (Arg.var fb, ()))
    Blocks.nil) fun Js => Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_95.fst, ())) fun p_105 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld, Arg.var p_105.fst, ())) fun p_106 =>
    Expr.load i8 (Arg.var p_106.fst) fun ld_19 =>
    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p_107 =>
    Expr.let_ (Op.mk (.sext 8 32) (Arg.var ld_19, ())) fun p_108 =>
    Expr.let_ (Op.mk (.sext 8 32) (Arg.var p_107.fst, ())) fun p_109 =>
    Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl) (Arg.var p_108.fst, Arg.var p_109.fst, ()))
    fun p_110 => Expr.jnz (Arg.var p_110.fst) (
    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 144, ())) fun p_111 =>
    Expr.load i64 (Arg.var p_111.fst) fun ld_20 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 768, ())) fun p_112 =>
    Expr.load i64 (Arg.var p_112.fst) fun ld_21 =>
    Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var ld_20, Arg.var ld_21, ()))
    fun p_113 => Expr.jnz (Arg.var p_113.fst) (
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_95.fst, ())) fun p_114 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld, Arg.var p_114.fst, ())) fun p_115 =>
    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 1, ())) fun p_116 =>
    Expr.store (Arg.var p_116.fst) (Arg.var p_115.fst) (
    Expr.let_ (Op.mk (.xor i32) (Arg.var p_95.fst, Arg.imm 1, ())) fun p_117 =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_117.fst, ())) fun p_118 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld, Arg.var p_118.fst, ())) fun p_119 =>
    Expr.let_ (Op.mk (.neg i32) (Arg.imm 1, ())) fun p_120 =>
    Expr.let_ (Op.mk (.trunc 32 8) (Arg.var p_120.fst, ())) fun p_121 =>
    Expr.store (Arg.var p_121.fst) (Arg.var p_119.fst) (
    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 144, ())) fun p_122 =>
    Expr.load i64 (Arg.var p_122.fst) fun ld =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var ld, Arg.imm 4, ())) fun p_123 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld_4, Arg.var p_123.fst, ())) fun p_124 =>
    Expr.store (Arg.var p_95.fst) (Arg.var p_124.fst) (
    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 144, ())) fun p_125 =>
    Expr.load i64 (Arg.var p_125.fst) fun ld =>
    Expr.let_ (Op.mk (.add i64) (Arg.var ld, Arg.imm 1, ())) fun p_126 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var h, Arg.imm 144, ())) fun p =>
    Expr.store (Arg.var p_126.fst) (Arg.var p.fst) (Expr.jump Js.fst ()))))) (
    Expr.jump Js.fst ())) (Expr.jump Js.fst ()))) (Expr.jump Js_6.fst (Arg.var fb, ()))))
    Blocks.nil) fun Js => Expr.let_ (Op.mk (.sub i64) (Arg.var p_93.fst, Arg.var loff_v, ()))
    fun p => Expr.let_ (Op.mk (.and i64) (Arg.var p.fst, Arg.imm 31, ())) fun p =>
    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 0, ())) fun p =>
    Expr.jnz (Arg.var p.fst) (
    Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var p_85.fst, Arg.imm 0, ())) fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.let_ (Op.mk (.sub i64) (Arg.var p_85.fst, Arg.imm 1, ()))
    fun p => Expr.jump Js.fst (Arg.var p.fst, ())) (Expr.jump Js.fst (Arg.var p_85.fst, ()))) (
    Expr.jump Js.fst (Arg.var p_85.fst, ()))) Blocks.nil) fun Js =>
    Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl) (Arg.var nl, Arg.var src, ()))
    fun p => Expr.jnz (Arg.var p.fst) (
    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_85.snd.fst, Arg.var p_cur, ()))
    fun p => Expr.jnz (Arg.var p.fst) (
    Expr.let_ (Op.mk (.add i64) (Arg.var p_85.snd.fst, Arg.imm 1, ())) fun p =>
    Expr.jump Js_3.fst (Arg.var p_85.fst, Arg.var p.fst, ())) (Expr.jump Js.fst ())) (
    Expr.jump Js.fst ())))) (
    Expr.jump Js_19 (Arg.var fb, Arg.var p_85.fst, Arg.var tb, Arg.var p_85.snd.fst, ())))
    Blocks.nil) fun Js => Expr.jump Js.fst (Arg.var tk_m1, Arg.var loff_v, ())

theorem s13_tl_inner_watch_wp {Γ : Env} {Js_19 : Cont [Ty.bool, i64, Ty.bool, i64]}
    {Q_fn : Post [Ty.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s st st_b : FullState}
    {R : Mem 64 → Prop} {src dst nl : BitVec 32} {stop_early fb tb : Bool}
    {p_cur tk_m1 : BitVec 64} {saved loff lsz nt0 : Nat} {m2 : Mem 64}
    (hw0 : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (_hsrc_lt : src.toNat < 2 * s.core.cur_vars) (hcv_st : st.core.cur_vars = s.core.cur_vars)
    (hpre_vals : st.core.vals = s.core.vals) (hpre_te : st.core.trail_end = s.core.trail_end)
    (hpre_trl : ∀ i < s.core.trail_end, st.core.trl[i]? = s.core.trl[i]?)
    (hu_b : TransUnrollInv c F0 F_cur s st src.toNat saved st_b)
    (hntf : ¬(fb = true ∧ tb = true)) (hfb_f : fb = false) (htb_f : tb = false)
    (hfb : fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat]))
    (htb : tb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat, dst.toNat]))
    (hent_lit : (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat, nl.toNat ^^^ 1]))
    (hnl_bnd : loff + lsz ≤ st_b.core.wlen)
    (htomb0 : TombWatchSliceOk F_cur st_b.core nl.toNat loff lsz nt0)
    (hm2 : (FullMem c st_b ⋆ R) m2)
    (hJ19 : ∀ (f2 : Bool) (tk2 : BitVec 64) (t2 : Bool) (q : BitVec 64) (m3 : Mem 64),
      (∃ st_w : FullState, TransUnrollInv c F0 F_cur s st src.toNat saved st_w ∧
        st_b.core.trail_end ≤ st_w.core.trail_end ∧ ¬(f2 = true ∧ t2 = true) ∧
        (f2 = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        (t2 = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat, dst.toNat])) ∧
        (FullMem c st_w ⋆ R) m3) →
      Js_19 (f2, tk2, t2, q, ()) m3) :
    wp Γ Q_fn X (s13TlInnerWatchExpr c.hdr src stop_early c.pVals c.pWstk c.pTrail
      (BitVec.ofNat 64 s.core.cur_vars <<< 1#64) (BitVec.ofNat 64 loff)
      (BitVec.ofNat 64 (loff + lsz)) tk_m1 p_cur dst nl fb tb Js_19) m2 := by
  unfold s13TlInnerWatchExpr
  have hlen_b := hu_b.len_ok
  have hloff_lt : loff < 2 ^ 64 := by have := (s13_tl_bnds hlen_b.core_ok).2.2.1; omega
  have hlo_eq : (BitVec.ofNat 64 loff).toNat = loff := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hloff_lt]
  have hlend_eq : (BitVec.ofNat 64 (loff + lsz)).toNat = loff + lsz := by
    have := (s13_tl_bnds hlen_b.core_ok).2.2.1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnlits_eq : (BitVec.ofNat 64 s.core.cur_vars <<< 1#64).toNat = 2 * st.core.cur_vars := by
    have hcv_b_eq : st_b.core.cur_vars = s.core.cur_vars := by rw [hu_b.same_core, hcv_st]
    have hcv_bnd : 2 * s.core.cur_vars + 1 < 2 ^ 30 := by
      have := (s13_tl_bnds hlen_b.core_ok).1; omega
    have hbv : (BitVec.ofNat 64 s.core.cur_vars <<< 1#64).toNat = 2 * s.core.cur_vars := by
      change (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars
      rw [ft_bv64_shl1 (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hcv_st, hbv]
  refine wp_loop_group (ts := [i64, i64])
    (Inv := fun nq xs m3 => let _tkq := xs.1; let q := xs.2.1
      ∃ st_q : FullState, ∃ nt : Nat, loff ≤ q.toNat ∧ q.toNat ≤ loff + lsz ∧
        nq = (loff + lsz) - q.toNat ∧ st_b.core.trail_end ≤ st_q.core.trail_end ∧
        TombWatchSliceOk F_cur st_q.core nl.toNat q.toNat ((loff + lsz) - q.toNat) nt ∧
        TransUnrollInv c F0 F_cur s st src.toNat saved st_q ∧
        (FullMem c st_q ⋆ R) m3) ?_ ?_
  · rintro L20 nq ⟨tkq, q, ⟨⟩⟩ m3 hL20
      ⟨st_q, nt, hql, hqh, hqneq, hte_q, htm_q, hu_q, hm3⟩
    dsimp only at hql hqh hqneq htm_q; have hlen_q := hu_q.len_ok
    c0_hsplit
    · have hq_lt : q.toNat < loff + lsz := by
        have h1 : q.toNat < (BitVec.ofNat 64 (loff + lsz)).toNat := by c0_bound
        rwa [hlend_eq] at h1
      have hq_len : q.toNat < st_q.core.wstk.length := by
        rw [hlen_q.core_ok.wstk_len_arr]; have := hlen_b.core_ok.wlen_le; omega
      have hstep := htm_q.inv_step (by omega) (List.getElem?_eq_getElem hq_len)
      have hq1 : (q + 1#64).toNat = q.toNat + 1 :=
        ft_bv64_add1 (by have := (s13_tl_bnds hlen_b.core_ok).2.2.1; omega)
      c0_hsplit
      · have htomb : st_q.core.wstk[q.toNat] = 0xFFFFFFFF#32 := hc
        simp only [htomb, ↓reduceIte] at hstep
        have hstep2 := hstep.2
        c0_hsteps
        exact hL20 ((loff + lsz) - (q.toNat + 1)) (tkq, q + 1#64, ()) m3 (by omega)
          ⟨st_q, nt - 1, by rw [hq1]; omega, by rw [hq1]; omega, by rw [hq1], hte_q,
           by rw [hq1]; rwa [show loff + lsz - q.toNat - 1 = loff + lsz - (q.toNat + 1) by omega]
             at hstep2,
           hu_q, hm3⟩
      · have hne_tomb : st_q.core.wstk[q.toNat] ≠ 0xFFFFFFFF#32 := hc
        c0_hsplit
        · have hfl0 : (st_q.core.wstk[q.toNat] &&& 0x80000000#32) = 0#32 := hc
          simp only [hfl0, ↓reduceIte] at hstep
          obtain ⟨_, _, _, _, _, htm'⟩ := hstep
          c0_hsplit
          · c0_hsteps
            exact hJ19 fb tkq tb q m3
              ⟨st_q, hu_q, hte_q, hntf, hfb, htb, hm3⟩
          · have hq2 : (q + 2#64).toNat = q.toNat + 2 :=
              ft_bv64_add2 (by have := (s13_tl_bnds hlen_b.core_ok).2.2.1; omega)
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ m' => m' = m3)
              (fun _ ⟨tk_n, ⟨⟩⟩ m' heq => by
                subst heq; c0_hsteps
                exact hL20 ((loff + lsz) - (q.toNat + 2)) (tk_n, q + 2#64, ()) m' (by omega)
                  ⟨st_q, nt, by rw [hq2]; omega, by rw [hq2]; omega, by rw [hq2], hte_q,
                   by rw [hq2]; rwa [show loff + lsz - q.toNat - 2 = loff + lsz - (q.toNat + 2)
                     by omega] at htm', hu_q, hm3⟩)
              (fun Jtk hJtk => by
                c0_hsplit
                · c0_hsplit
                  · c0_hsteps; exact hJtk _ m3 rfl
                  · c0_hsteps; exact hJtk _ m3 rfl
                · c0_hsteps; exact hJtk _ m3 rfl)
        · have hfl_nz : (st_q.core.wstk[q.toNat] &&& 0x80000000#32) ≠ 0#32 := hc
          simp only [hfl_nz, hne_tomb, ↓reduceIte] at hstep
          obtain ⟨hot_lt, h_bin, htail⟩ := hstep
          have htail' : TombWatchSliceOk F_cur st_q.core nl.toNat (q.toNat + 1)
              ((loff + lsz) - (q.toNat + 1)) nt := by
            rwa [show loff + lsz - q.toNat - 1 = loff + lsz - (q.toNat + 1) by omega] at htail
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun _ m4 => m4 = m3) ?_ ?_
          · rintro J24 ⟨⟩ m4 rfl
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ m5 => m5 = m4) ?_
              (fun Jtk hJtk => by
                c0_hsplit
                · c0_hsplit
                  · c0_hsteps; exact hJtk _ m4 rfl
                  · c0_hsteps; exact hJtk _ m4 rfl
                · c0_hsteps; exact hJtk _ m4 rfl)
            rintro _ ⟨tk_n, ⟨⟩⟩ m5 rfl
            let ot := st_q.core.wstk[q.toNat]'hq_len &&& 0x7FFFFFFF#32
            have hent_ot := entails_pair_trans hent_lit (by
              rw [show nl.toNat ^^^ 1 ^^^ 1 = litNeg (litNeg nl.toNat) from rfl,
                litNeg_litNeg]; exact h_bin)
            c0_hsplit
            · have hdst_eq : st_q.core.wstk[q.toNat] &&& 0x7FFFFFFF#32 = dst := hc
              rw [congrArg BitVec.toNat hdst_eq] at hent_ot
              c0_hsteps
              exact hJ19 fb tk_n true (q + 1#64) m5
                ⟨st_q, hu_q, hte_q, by simp [hfb_f],
                 fun hf => absurd hf (by simp [hfb_f]), fun _ => hent_ot, hm3⟩
            · c0_hsteps_nogrp
              refine wp_join_group (ts := [Ty.bool]) (P := fun _ m6 =>
                ∃ st_q2 : FullState, st_b.core.trail_end ≤ st_q2.core.trail_end ∧
                  TombWatchSliceOk F_cur st_q2.core nl.toNat (q.toNat + 1)
                    ((loff + lsz) - (q.toNat + 1)) nt ∧
                  TransUnrollInv c F0 F_cur s st src.toNat saved st_q2 ∧
                  (FullMem c st_q2 ⋆ R) m6) ?_ ?_
              · rintro J27 ⟨_, ⟨⟩⟩ m6 ⟨st_q2, hte_q2, htm_q2, hu_q2, hm6⟩
                c0_hsteps
                exact hL20 ((loff + lsz) - (q.toNat + 1)) (tk_n, q + 1#64, ()) m6 (by omega)
                  ⟨st_q2, nt, by rw [hq1]; omega, by rw [hq1]; omega, by rw [hq1], hte_q2,
                   by rw [hq1]; exact htm_q2, hu_q2, hm6⟩
              · intro J27 hJ27
                have hot_vlen := s13_tl_vals_lt hlen_q.core_ok hot_lt
                have hot_st : ot.toNat < 2 * st.core.cur_vars := by
                  have hcv_q : st_q.core.cur_vars = st.core.cur_vars := by rw [hu_q.same_core]
                  rw [← hcv_q]; exact hot_lt
                have hdom_ot := hu_q.vals_domain hw0 hpre_vals hcv_st hot_st
                c0_hsplit
                · c0_hsplit
                  · have hval_ff := s13_tl_vals_ff_of_domain (z := 0#32) hdom_ot rfl
                      (by rw [List.getElem?_eq_getElem hot_vlen]; exact hc)
                    have hent_src := hu_q.entails_src_of_falsified hw0 hpre_vals
                      hcv_st hcl0 hot_st hval_ff hent_ot
                    c0_hsteps
                    exact hJ19 true tk_n tb (q + 1#64) m5
                      ⟨st_q, hu_q, hte_q, by simp [htb_f], fun _ => hent_src,
                       fun ht => absurd ht (by simp [htb_f]), hm3⟩
                  · c0_hsteps_nogrp
                    refine wp_unroll_group fun _ _ => ?_
                    c0_hsplit
                    · have hot0 := s13_tl_vals_zero_of_domain (z := 0#32) hdom_ot
                        rfl (by rw [List.getElem?_eq_getElem hot_vlen]; exact hc)
                      c0_hsplit
                      · obtain ⟨hte_q_lt, hu_q'⟩ := hu_q.push hw0 hpre_vals
                          hpre_te hpre_trl hcv_st hot_st hot0 hent_ot
                        have hbv_ot : BitVec.ofNat 32 ot.toNat = ot :=
                          s13_tl_bv32_ofNat_toNat ot
                        have hot64 : ((st_q.core.wstk[q.toNat]'hq_len &&&
                            2147483647).setWidth 64).toNat = ot.toNat :=
                          ft_bv32_setWidth64 ot
                        have hotn64 : (((st_q.core.wstk[q.toNat]'hq_len &&&
                            2147483647) ^^^ 1).setWidth 64).toNat = ot.toNat ^^^ 1 := by
                          rw [ft_bv32_setWidth64]; exact ft_bv32_xor1 ot
                        have hotn_vlen : (ot ^^^ 1).toNat <
                            (st_q.core.vals.set ot.toNat 1#8).length := by
                          rw [List.length_set, show (ot ^^^ 1).toNat =
                            ot.toNat ^^^ 1 from ft_bv32_xor1 ot, hlen_q.core_ok.vals_len]
                          have := litNeg_lt_two_mul hot_lt
                          have := hlen_q.core_ok.cur_vars_le
                          dsimp only [ot]; omega
                        have hteq_lt : st_q.core.trail_end < 2 ^ 64 :=
                          (s13_tl_bnds hlen_q.core_ok).2.2.2
                        have hte_bv : (BitVec.ofNat 64 st_q.core.trail_end).toNat =
                            st_q.core.trail_end := by
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hteq_lt]
                        have hteq_tlen : (BitVec.ofNat 64 st_q.core.trail_end).toNat <
                            st_q.core.trl.length := by
                          rw [hte_bv, hlen_q.core_ok.trl_len]
                          have := hlen_q.core_ok.cur_vars_le; omega
                        have hteq1 : (BitVec.ofNat 64 st_q.core.trail_end + 1).toNat =
                            st_q.core.trail_end + 1 := by
                          rw [show (1 : BitVec 64) = 1#64 from rfl,
                            ft_bv64_add1 (by omega), hte_bv]
                        c0_hsteps
                        let st_q2 : FullState := { st_q with core := {
                          st_q.core with
                          vals := (st_q.core.vals.set ot.toNat 1#8).set (ot.toNat ^^^ 1) 0xFF#8
                          trl := st_q.core.trl.set st_q.core.trail_end ot
                          trail_end := st_q.core.trail_end + 1 } }
                        refine hJ27 (fb, ()) _ ⟨st_q2,
                          Nat.le_trans hte_q (Nat.le_succ _),
                          TombWatchSliceOk.mono (k := st_q.core)
                            (k' := st_q2.core) (Nat.le_refl _) (fun _ hr => hr)
                            (fun _ _ _ => rfl) htail',
                          by simpa only [hbv_ot] using hu_q', ?_⟩
                        refine s13_tl_fullMem_eq ?_ (by assumption)
                        dsimp only [st_q2]; rw [hot64, hotn64, hte_bv, hteq1]; rfl
                      · c0_hsteps; exact hJ27 (fb, ()) m5 ⟨st_q, hte_q, htail', hu_q, hm3⟩
                    · c0_hsteps; exact hJ27 (fb, ()) m5 ⟨st_q, hte_q, htail', hu_q, hm3⟩
                · c0_hsteps; exact hJ27 (fb, ()) m5 ⟨st_q, hte_q, htail', hu_q, hm3⟩
          · intro J24 hJ24
            c0_hsplit
            · c0_hsplit
              · c0_hsteps
                exact hL20 ((loff + lsz) - (q.toNat + 1)) (tkq, q + 1#64, ()) m3 (by omega)
                  ⟨st_q, nt, by rw [hq1]; omega, by rw [hq1]; omega, by rw [hq1], hte_q,
                   by rw [hq1]; exact htail', hu_q, hm3⟩
              · c0_hsteps; exact hJ24 () m3 rfl
            · c0_hsteps; exact hJ24 () m3 rfl
    · c0_hsteps; exact hJ19 fb tkq tb q m3 ⟨st_q, hu_q, hte_q, hntf, hfb, htb, hm3⟩
  · intro L20 hL20; c0_hsteps
    exact hL20 ((loff + lsz) - loff) (tk_m1, BitVec.ofNat 64 loff, ()) m2
      ⟨st_b, nt0, by rw [hlo_eq]; exact Nat.le_refl _, by rw [hlo_eq]; omega,
       by rw [hlo_eq], Nat.le_refl _,
       by rw [hlo_eq]; simpa using htomb0, hu_b, hm2⟩

end TransLitInnerWatchS5

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

end
