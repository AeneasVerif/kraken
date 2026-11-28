/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Helpers

/-!
# Pure Helpers & Loop Invariants for `full_subst_rewrite_bins`

Extracts pure `FullState` invariants and transition lemmas from `WpRewriteBins`
so every declaration stays compact (`<= 450` LOC) and free of `@[expose]`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Substitute

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped Proof.Spec.FullArenaTactics SubstArenaTactics

private theorem rb_bv64_one : (1#64 : BitVec 64).toNat = 1 := rfl
private theorem rb_bv64_two : (2#64 : BitVec 64).toNat = 2 := rfl

private theorem getElem_eq_getElem?_getD {α : Type} (d : α)
    {xs ys : List α} {i j : Nat} (hi : i < xs.length) (hxs : xs = ys) (hij : i = j) :
    xs[i]'hi = ys[j]?.getD d := by
  subst hxs; subst hij; rw [List.getElem?_eq_getElem hi, Option.getD_some]

public section

def withWstk (k : FullCoreState) (ws : List (BitVec 32)) : FullCoreState :=
  { k with wstk := ws }

structure RbAgrees (s t : FullState) : Prop where
  core_eq : { t.core with lit_mark := [], wstk := [], num_binary := 0#64 } =
    { s.core with lit_mark := [], wstk := [], num_binary := 0#64 }
  scratch_eq : { t.scratch with work_stk1 := [], work_stk2 := [] } =
    { s.scratch with work_stk1 := [], work_stk2 := [] }

theorem rbAgrees_refl (s : FullState) : RbAgrees s s := ⟨rfl, rfl⟩

theorem rbAgrees_trans {a b c : FullState} (h1 : RbAgrees a b) (h2 : RbAgrees b c) :
    RbAgrees a c :=
  ⟨h2.core_eq.trans h1.core_eq, h2.scratch_eq.trans h1.scratch_eq⟩

theorem rbAgrees_cur_vars {s t : FullState} (h : RbAgrees s t) :
    t.core.cur_vars = s.core.cur_vars := by
  have hc := h.core_eq; cases t with | mk ct _ => cases s with | mk cs _ =>
  cases ct; cases cs; cases hc; rfl

theorem rbAgrees_repr {s t : FullState} (h : RbAgrees s t) :
    t.core.repr = s.core.repr := by
  have hc := h.core_eq; cases t with | mk ct _ => cases s with | mk cs _ =>
  cases ct; cases cs; cases hc; rfl

theorem rbAgrees_wvec {s t : FullState} (h : RbAgrees s t) :
    t.core.wvec = s.core.wvec := by
  have hc := h.core_eq; cases t with | mk ct _ => cases s with | mk cs _ =>
  cases ct; cases cs; cases hc; rfl

theorem rb_st4_eq {st st3 : FullState} (hag : RbAgrees st st3)
    (wv' : List (BitVec 32)) (wu' : BitVec 64) :
    ({ st3 with core := { st3.core with wvec := wv', wusable := wu' } } : FullState) =
      { st with
        core := { st.core with
          lit_mark := st3.core.lit_mark, wvec := wv', wstk := st3.core.wstk,
          wusable := wu', num_binary := st3.core.num_binary }
        scratch := { st.scratch with
          work_stk1 := st3.scratch.work_stk1, work_stk2 := st3.scratch.work_stk2 } } := by
  have hc := hag.core_eq; have hs := hag.scratch_eq
  cases st3 with | mk c3 sc3 => cases st with | mk cs scs =>
  cases c3; cases cs; cases hc
  cases sc3; cases scs; cases hs; rfl

structure RbOuterCore (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (l : BitVec 64) (st : FullState) : Prop where
  sp : FullSparseInvW c F0 F_cur st
  cv_eq : st.core.cur_vars = s0.core.cur_vars
  hl0 : st.core.cur_level = 0
  fuel_eq : st.core.fuel = s0.core.fuel
  repr : FullReprEquiv F_cur st
  l_le : l.toNat ≤ 2 * s0.core.cur_vars

def RbLmCov (c : FullCfg) (st1 : FullState) (off q_n pn_n : Nat) : Prop :=
  ∀ x < 2 * c.max_vars, st1.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
    (∃ idx, off ≤ idx ∧ idx < q_n ∧
      (st1.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
      (st1.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∨
    (∃ k, k < pn_n ∧ (st1.scratch.work_stk2[k]?.getD 0#32).toNat = x)

def RbPaOk (F_cur : List (List Nat)) (st st1 : FullState) (pn_n : Nat) : Prop :=
  ∀ k < pn_n,
    (st1.scratch.work_stk1[k]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧
    (st1.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(st1.scratch.work_stk1[k]?.getD 0#32).toNat,
                  (st1.scratch.work_stk2[k]?.getD 0#32).toNat])

structure RbInner1Core (c : FullCfg) (F_cur : List (List Nat)) (st : FullState)
    (l off sz : Nat) (pn p q : BitVec 64) (st1 : FullState) : Prop where
  ag : RbAgrees st st1
  len : st1.LengthsOk c
  q_lo : off ≤ q.toNat
  qp : q.toNat ≤ p.toNat
  p_hi : p.toNat ≤ off + sz
  pn_le : pn.toNat ≤ 2 * st.core.cur_vars
  tail_eq : ∀ idx, p.toNat ≤ idx → st1.core.wstk[idx]? = st.core.wstk[idx]?
  out_eq : ∀ idx, (idx < off ∨ off + sz ≤ idx) → st1.core.wstk[idx]? = st.core.wstk[idx]?
  rem : WatchSliceOk F_cur st.core l p.toNat (off + sz - p.toNat)
  kept : WatchSliceOk F_cur (withWstk st.core st1.core.wstk) l off (q.toNat - off)
  lm : RbLmCov c st1 off q.toNat pn.toNat
  pa : RbPaOk F_cur st st1 pn.toNat

structure RbClear1Core (c : FullCfg) (st st1 : FullState) (off q_n pn_n : Nat)
    (ci : BitVec 64) (st2 : FullState) : Prop where
  ag : RbAgrees st st2
  len : st2.LengthsOk c
  wstk_eq : st2.core.wstk = st1.core.wstk
  nb_eq : st2.core.num_binary = st1.core.num_binary
  ws1_eq : st2.scratch.work_stk1 = st1.scratch.work_stk1
  ws2_eq : st2.scratch.work_stk2 = st1.scratch.work_stk2
  ci_lo : off ≤ ci.toNat
  ci_hi : ci.toNat ≤ q_n
  lm : ∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
    (∃ idx, ci.toNat ≤ idx ∧ idx < q_n ∧
      (st2.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
      (st2.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∨
    (∃ k, k < pn_n ∧ (st2.scratch.work_stk2[k]?.getD 0#32).toNat = x)

structure RbClear2Core (c : FullCfg) (st st1 : FullState) (pn_n : Nat)
    (ci2 : BitVec 64) (st2b : FullState) : Prop where
  ag : RbAgrees st st2b
  len : st2b.LengthsOk c
  wstk_eq : st2b.core.wstk = st1.core.wstk
  nb_eq : st2b.core.num_binary = st1.core.num_binary
  ws1_eq : st2b.scratch.work_stk1 = st1.scratch.work_stk1
  ws2_eq : st2b.scratch.work_stk2 = st1.scratch.work_stk2
  ci2_le : ci2.toNat ≤ pn_n
  lm : ∀ x < 2 * c.max_vars, st2b.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
    ∃ k, ci2.toNat ≤ k ∧ k < pn_n ∧ (st2b.scratch.work_stk2[k]?.getD 0#32).toNat = x

structure RbTrimCore (c : FullCfg) (st st1 st2b : FullState) (q_n off sz : Nat)
    (ci3 : BitVec 64) (st3 : FullState) : Prop where
  ag : RbAgrees st st3
  len : st3.LengthsOk c
  lm_eq : st3.core.lit_mark = st2b.core.lit_mark
  nb_eq : st3.core.num_binary = st1.core.num_binary
  ws1_eq : st3.scratch.work_stk1 = st1.scratch.work_stk1
  ws2_eq : st3.scratch.work_stk2 = st1.scratch.work_stk2
  ci3_lo : q_n ≤ ci3.toNat
  ci3_hi : ci3.toNat ≤ off + sz
  out_eq : ∀ idx, (idx < q_n ∨ off + sz ≤ idx) → st3.core.wstk[idx]? = st1.core.wstk[idx]?

structure RbEmitCore (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st4 : FullState) (pn_n : Nat) (ci4 : BitVec 64) (st5 : FullState) : Prop where
  sp : FullSparseInvW c F0 F_cur st5
  cv_eq : st5.core.cur_vars = s0.core.cur_vars
  hl0 : st5.core.cur_level = 0
  fuel_eq : st5.core.fuel = s0.core.fuel
  repr : FullReprEquiv F_cur st5
  ws1_eq : st5.scratch.work_stk1 = st4.scratch.work_stk1
  ws2_eq : st5.scratch.work_stk2 = st4.scratch.work_stk2
  ci4_le : ci4.toNat ≤ pn_n

theorem rb_outer_watches {F_cur : List (List Nat)} {c : FullCfg} {F0 : CNF Nat}
    {st : FullState} (hsp : FullSparseInvW c F0 F_cur st) :
    WatchesInv F_cur st.core := by
  have hm_w := hsp.2.1.watches; unfold ModeWatchesInv at hm_w
  simp only [hsp.2.2.2.2.2, ↓reduceIte] at hm_w; exact hm_w

theorem rb_wvec_shl_lt {c : FullCfg} {st : FullState} (hcl : st.LengthsOk c)
    (hl : st.core.cur_vars ≤ c.max_vars) {l : BitVec 64} (hl_lt : l.toNat < 2 * st.core.cur_vars) :
    (l <<< 1#64).toNat = 2 * l.toNat ∧ ((l <<< 1#64) + 1#64).toNat = 2 * l.toNat + 1 ∧
    (l <<< 1#64).toNat < st.core.wvec.length ∧
    ((l <<< 1#64) + 1#64).toNat < st.core.wvec.length := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hwvl := hcl.core_ok.wvec_len
  have h2l : (l <<< 1#64).toNat = 2 * l.toNat := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have h2l1 : ((l <<< 1#64) + 1#64).toNat = 2 * l.toNat + 1 := by
    rw [BitVec.toNat_add, h2l, rb_bv64_one, Nat.mod_eq_of_lt (by omega)]
  exact ⟨h2l, h2l1, by rw [h2l, hwvl]; omega, by rw [h2l1, hwvl]; omega⟩

theorem rb_wvec_off_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {l : BitVec 64}
    (ho : RbOuterCore c F0 F_cur s0 l st) (hl_lt : l.toNat < 2 * s0.core.cur_vars)
    (hwat : WatchesInv F_cur st.core) :
    let hcv := ho.cv_eq
    let hwv := rb_wvec_shl_lt ho.sp.1 ho.sp.1.core_ok.cur_vars_le (hcv ▸ hl_lt)
    let off := fullWatchOff st l.toNat
    let sz := fullWatchSize st l.toNat
    (st.core.wvec[(l <<< 1#64).toNat]'hwv.2.2.1).toNat = off ∧
    (st.core.wvec[((l <<< 1#64) + 1#64).toNat]'hwv.2.2.2).toNat = sz ∧
    off + sz ≤ st.core.wlen ∧ off + sz ≤ c.wcap ∧
    WatchSliceOk F_cur st.core l.toNat off sz := by
  have hcv := ho.cv_eq; have hwle := ho.sp.1.core_ok.wlen_le
  have hwv := rb_wvec_shl_lt ho.sp.1 ho.sp.1.core_ok.cur_vars_le (hcv ▸ hl_lt)
  have hoff : (st.core.wvec[(l <<< 1#64).toNat]'hwv.2.2.1).toNat = fullWatchOff st l.toNat :=
    congrArg BitVec.toNat (getElem_eq_getElem?_getD 0#32 hwv.2.2.1 rfl hwv.1)
  have hsz : (st.core.wvec[((l <<< 1#64) + 1#64).toNat]'hwv.2.2.2).toNat =
      fullWatchSize st l.toNat :=
    congrArg BitVec.toNat (getElem_eq_getElem?_getD 0#32 hwv.2.2.2 rfl hwv.2.1)
  have hbd := hwat.layout.bounds l.toNat (hcv ▸ hl_lt)
  have hsl := hwat.slices l.toNat (hcv ▸ hl_lt)
  exact ⟨hoff, hsz, hbd, Nat.le_trans hbd hwle, hsl⟩

theorem rb_inner1_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {l : BitVec 64}
    (ho : RbOuterCore c F0 F_cur s0 l st) (hl_lt : l.toNat < 2 * s0.core.cur_vars)
    (hoff_eq : (st.core.wvec[(l <<< 1#64).toNat]'(rb_wvec_shl_lt ho.sp.1
      ho.sp.1.core_ok.cur_vars_le (ho.cv_eq ▸ hl_lt)).2.2.1).toNat = fullWatchOff st l.toNat)
    (_hbound : fullWatchOff st l.toNat + fullWatchSize st l.toNat ≤ st.core.wlen)
    (hslice : WatchSliceOk F_cur st.core l.toNat (fullWatchOff st l.toNat)
      (fullWatchSize st l.toNat)) :
    let hwv := rb_wvec_shl_lt ho.sp.1 ho.sp.1.core_ok.cur_vars_le (ho.cv_eq ▸ hl_lt)
    let offBV := (st.core.wvec[(l <<< 1#64).toNat]'hwv.2.2.1).setWidth 64
    RbInner1Core c F_cur st l.toNat (fullWatchOff st l.toNat) (fullWatchSize st l.toNat)
      0#64 offBV offBV st := by
  have hcl := ho.sp.1.core_ok; have hwle := hcl.wlen_le
  have h0_eq : ((st.core.wvec[(l <<< 1#64).toNat]'(rb_wvec_shl_lt ho.sp.1
      hcl.cur_vars_le (ho.cv_eq ▸ hl_lt)).2.2.1).setWidth 64).toNat = fullWatchOff st l.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hoff_eq]
  refine ⟨rbAgrees_refl st, ho.sp.1, Nat.le_of_eq h0_eq.symm, Nat.le_refl _,
    Nat.le_trans (Nat.le_of_eq h0_eq) (Nat.le_add_right _ _), Nat.zero_le _,
    fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, fun _ h => by simp at h⟩
  · refine Eq.subst (motive := fun x => WatchSliceOk F_cur st.core l.toNat x
      (fullWatchOff st l.toNat + fullWatchSize st l.toNat - x)) h0_eq.symm ?_
    rw [Nat.add_sub_cancel_left]; exact hslice
  · refine Eq.subst (motive := fun x => WatchSliceOk F_cur (withWstk st.core st.core.wstk)
      l.toNat (fullWatchOff st l.toNat) (x - fullWatchOff st l.toNat)) h0_eq.symm ?_
    rw [Nat.sub_self]; exact .empty
  · intro x hx hnz; exact absurd (ho.sp.2.2.1.2 x hx) hnz

theorem rb_nonbin_step {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz : Nat} {pn p q : BitVec 64} {w0 : BitVec 32}
    (hin : RbInner1Core c F_cur st l off sz pn p q st1)
    (hp_lt : p.toNat < off + sz) (hend_lt : off + sz ≤ c.wcap)
    (hp1 : (p + 1#64).toNat = p.toNat + 1) (hq1 : (q + 1#64).toNat = q.toNat + 1)
    (hq2 : (q + 2#64).toNat = q.toNat + 2) (hp11 : (p + 1#64 + 1#64).toNat = p.toNat + 2)
    (hw0_eq : st.core.wstk[p.toNat]? = some w0)
    (hfl0 : (w0 &&& 0x80000000#32) = 0#32) :
    ∃ (_hcr_lt : p.toNat + 1 < off + sz)
      (hcr_len1 : (p + 1#64).toNat < (st1.core.wstk.set q.toNat w0).length),
    p.toNat < (p + 1#64 + 1#64).toNat ∧
    ∀ wstk2, wstk2 = (st1.core.wstk.set q.toNat w0).set (q + 1#64).toNat
        ((st1.core.wstk.set q.toNat w0)[(p + 1#64).toNat]'hcr_len1) →
      RbInner1Core c F_cur st l off sz pn (p + 1#64 + 1#64) (q + 2#64)
        { st1 with core := { st1.core with wstk := wstk2 } } := by
  have hcl1 := hin.len.core_ok; have hwsl1 := hcl1.wstk_len_arr
  have hq_lo := hin.q_lo; have hqp := hin.qp
  obtain ⟨w0', cref, _, hw0_s, hcr_s, _, hcr_lt, hcr_ref, hrem_next⟩ :=
    wsStepNonbin hin.rem (by omega) (by rw [hw0_eq, Option.getD_some]; exact hfl0)
  have hw0_id : w0' = w0 := Option.some.inj (hw0_s.symm.trans hw0_eq)
  have hcr_eq1 : st1.core.wstk[(p + 1#64).toNat]'(by rw [hp1]; omega) = cref := by
    have hs : st1.core.wstk[p.toNat + 1]? = some cref :=
      (hin.tail_eq (p.toNat + 1) (by omega)).trans hcr_s
    rw [← hp1, List.getElem?_eq_getElem (by rw [hp1]; omega)] at hs
    exact Option.some.inj hs
  have hcr_len1 : (p + 1#64).toNat < (st1.core.wstk.set q.toNat w0).length := by
    rw [List.length_set, hp1, hwsl1]; omega
  refine ⟨by omega, hcr_len1, by rw [hp11]; omega, fun wstk2 hws2 => ?_⟩
  have hval : (st1.core.wstk.set q.toNat w0)[(p + 1#64).toNat]'hcr_len1 = cref := by
    rw [List.getElem_set_ne (by rw [hp1]; omega)]; exact hcr_eq1
  have hwstk2_def : wstk2 = (st1.core.wstk.set q.toNat w0).set (q.toNat + 1) cref := by
    rw [hws2, hq1, hval]
  let st2 : FullState := { st1 with core := { st1.core with wstk := wstk2 } }
  have hlen2 : st2.LengthsOk c :=
    ⟨{ hcl1 with wstk_len_arr := by simp [st2, hwstk2_def, hwsl1] }, hin.len.scratch_ok⟩
  have hkept2 : WatchSliceOk F_cur (withWstk st.core st2.core.wstk) l off
      ((q + 2#64).toNat - off) := by
    rw [hq2, show q.toNat + 2 - off = (q.toNat - off) + 2 by omega]
    refine wsAppendLarge (k := withWstk st.core st1.core.wstk)
      (Nat.le_refl _) (fun _ r => r) (fun idx hidx => by
        dsimp only [st2]; rw [hwstk2_def]; dsimp only [withWstk]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
      hin.kept
      (by dsimp only [st2]; rw [hwstk2_def]; dsimp only [withWstk]
          rw [show off + (q.toNat - off) = q.toNat by omega]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)])
      (by dsimp only [st2]; rw [hwstk2_def]; dsimp only [withWstk]
          rw [show off + (q.toNat - off) + 1 = q.toNat + 1 by omega]
          exact List.getElem?_set_self (by rw [List.length_set, hwsl1]; omega))
      hfl0 hcr_lt hcr_ref
  have hlm2 : RbLmCov c st2 off (q + 2#64).toNat pn.toNat := by
    intro x hx hnz
    rcases hin.lm x hx hnz with ⟨idx, hi1, hi2, hf, hv⟩ | hpb
    · left; refine ⟨idx, hi1, by omega, ?_, ?_⟩
      · dsimp only [st2]; rw [hwstk2_def]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hf
      · dsimp only [st2]; rw [hwstk2_def]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hv
    · exact Or.inr hpb
  exact ⟨rbAgrees_trans hin.ag ⟨rfl, rfl⟩, hlen2, by rw [hq2]; omega,
    by rw [hp11, hq2]; omega, by rw [hp11]; omega, hin.pn_le,
    fun idx hidx => by
      dsimp only [st2]; rw [hwstk2_def]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hin.tail_eq idx (by rw [hp11] at hidx; omega),
    fun idx hidx => by
      dsimp only [st2]; rw [hwstk2_def]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hin.out_eq idx hidx,
    by rw [hp11, show off + sz - (p.toNat + 2) = off + sz - p.toNat - 2 by omega]; exact hrem_next,
    hkept2, hlm2, hin.pa⟩

theorem rb_bin_prep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st1 : FullState} {lbv : BitVec 64} {l off sz : Nat}
    {pn p q : BitVec 64} {w0 : BitVec 32}
    (ho : RbOuterCore c F0 F_cur s0 lbv st)
    (hin : RbInner1Core c F_cur st l off sz pn p q st1)
    (hl_lt : l < 2 * s0.core.cur_vars) (hl_rp : l < st.core.repr.length)
    (hp_lt : p.toNat < off + sz) (hp1 : (p + 1#64).toNat = p.toNat + 1)
    (hw0_eq : st.core.wstk[p.toNat]? = some w0)
    (hfl_ne : (w0 &&& 0x80000000#32) ≠ 0#32) :
    let ot := w0 &&& 0x7FFFFFFF#32
    (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
    ot.toNat < 2 * st.core.cur_vars ∧ ot.toNat < st1.core.repr.length ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l, ot.toNat]) ∧
    WatchSliceOk F_cur st.core l (p + 1#64).toNat (off + sz - (p + 1#64).toNat) ∧
    ∀ (hot_lt : ot.toNat < st1.core.repr.length),
      let rot := st1.core.repr[ot.toNat]'hot_lt
      rot.toNat < 2 * st.core.cur_vars ∧
      rot.toNat < st1.core.lit_mark.length ∧
      ot.toNat < st1.core.lit_mark.length ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [(st.core.repr[l]'hl_rp).toNat, rot.toNat]) := by
  have hcl := ho.sp.1.core_ok; have hcl1 := hin.len.core_ok
  have hcv_le := hcl.cur_vars_le; have hcv := ho.cv_eq
  have hrp1 := rbAgrees_repr hin.ag
  obtain ⟨w0', hw0_s, hfl_bin, hne_ff, hot_lt, hent_bin, hrem_next⟩ :=
    wsStepBin hin.rem (by omega) (by rw [hw0_eq, Option.getD_some]; exact hfl_ne)
  have hw0_id : w0' = w0 := Option.some.inj (hw0_s.symm.trans hw0_eq)
  rw [hw0_id] at hfl_bin hne_ff hot_lt hent_bin
  have hot_rp : (w0 &&& 0x7FFFFFFF#32).toNat < st1.core.repr.length := by
    rw [hcl1.repr_len]; omega
  have hrem_p1 : WatchSliceOk F_cur st.core l (p + 1#64).toNat
      (off + sz - (p + 1#64).toNat) := by
    rw [hp1, show off + sz - (p.toNat + 1) = off + sz - p.toNat - 1 by omega]; exact hrem_next
  refine ⟨hfl_bin, hne_ff, hot_lt, hot_rp, hent_bin, hrem_p1, fun hot_lt_rp => ?_⟩
  let ot := w0 &&& 0x7FFFFFFF#32
  let rot := st1.core.repr[ot.toNat]'hot_lt_rp
  have hrot_eq : st.core.repr[ot.toNat]?.getD 0#32 = rot := by
    have h1 : st1.core.repr[ot.toNat]?.getD 0#32 = rot := by
      rw [List.getElem?_eq_getElem hot_lt_rp, Option.getD_some]
    rwa [hrp1] at h1
  have hrot_lt : rot.toNat < 2 * st.core.cur_vars := by
    rw [← hrot_eq]; exact FullReprEquiv.lt ho.repr hot_lt
  have hrot_eqv : LitEquiv (cnfOfClauses F_cur) ot.toNat rot.toNat := by
    rw [← hrot_eq]; exact FullReprEquiv.litEquiv ho.repr hot_lt
  have hrl_eqv : LitEquiv (cnfOfClauses F_cur) l (st.core.repr[l]'hl_rp).toNat := by
    have := FullReprEquiv.litEquiv ho.repr (hcv ▸ hl_lt)
    rwa [List.getElem?_eq_getElem hl_rp, Option.getD_some] at this
  have hrot_u : (st1.core.repr[(w0 &&& 0x7FFFFFFF#32).toNat]'hot_lt_rp).toNat <
      2 * st.core.cur_vars := hrot_lt
  exact ⟨hrot_u, by rw [hcl1.lit_mark_len]; omega,
    by rw [hcl1.lit_mark_len]; omega, entails_bin_subst hrl_eqv hrot_eqv hent_bin⟩

theorem rb_bin_keep_step {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz : Nat} {pn p q : BitVec 64} {w0 ot : BitVec 32}
    (hin : RbInner1Core c F_cur st l off sz pn p q st1)
    (hot_def : ot = w0 &&& 0x7FFFFFFF#32)
    (hp1 : (p + 1#64).toNat = p.toNat + 1) (hq1 : (q + 1#64).toNat = q.toNat + 1)
    (hp_lt : p.toNat < off + sz) (hend_lt : off + sz ≤ c.wcap)
    (hfl_bin : (w0 &&& 0x80000000#32) ≠ 0#32) (hne_ff : w0 ≠ 0xFFFFFFFF#32)
    (hot_lt : ot.toNat < 2 * st.core.cur_vars)
    (hent_bin : (cnfOfClauses F_cur).EntailsClause (cnfClause [l, ot.toNat]))
    (hrem_p1 : WatchSliceOk F_cur st.core l (p + 1#64).toNat (off + sz - (p + 1#64).toNat))
    (hot_lm : (BitVec.setWidth 64 ot).toNat < st1.core.lit_mark.length) :
    let lm2 := st1.core.lit_mark.set (BitVec.setWidth 64 ot).toNat
      (BitVec.setWidth 8 (BitVec.setWidth 32
        (st1.core.lit_mark[(BitVec.setWidth 64 ot).toNat]'hot_lm) ||| 1#32))
    RbInner1Core c F_cur st l off sz pn (p + 1#64) (q + 1#64)
      { st1 with core :=
        { st1.core with lit_mark := lm2, wstk := st1.core.wstk.set q.toNat w0 } } := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl1 := hin.len.core_ok; have hlml1 := hcl1.lit_mark_len; have hwsl1 := hcl1.wstk_len_arr
  have hcv_le1 : st1.core.cur_vars ≤ c.max_vars := hcl1.cur_vars_le
  have hcv1 : st1.core.cur_vars = st.core.cur_vars := rbAgrees_cur_vars hin.ag
  have hq_lo := hin.q_lo; have hqp := hin.qp
  have hot64 : (BitVec.setWidth 64 ot).toNat = ot.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  let lm2_raw := st1.core.lit_mark.set ot.toNat (st1.core.lit_mark[ot.toNat]'(by omega) ||| 1#8)
  have hlm2_eq : st1.core.lit_mark.set (BitVec.setWidth 64 ot).toNat
      (BitVec.setWidth 8 (BitVec.setWidth 32
        (st1.core.lit_mark[(BitVec.setWidth 64 ot).toNat]'hot_lm) ||| 1#32)) = lm2_raw := by
    have hget : st1.core.lit_mark[(BitVec.setWidth 64 ot).toNat]'hot_lm =
        st1.core.lit_mark[ot.toNat]'(by omega) :=
      Option.some.inj (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hot64])
    rw [bv8_trunc_or1, hget]; exact congrArg (st1.core.lit_mark.set · _) hot64
  let st2 : FullState :=
    { st1 with core := { st1.core with lit_mark := lm2_raw, wstk := st1.core.wstk.set q.toNat w0 } }
  have hlen2 : st2.LengthsOk c :=
    ⟨{ hcl1 with
        lit_mark_len := by simp [st2, lm2_raw, hlml1],
        wstk_len_arr := by simp [st2, hwsl1] }, hin.len.scratch_ok⟩
  have hkept2 : WatchSliceOk F_cur (withWstk st.core st2.core.wstk) l off
      ((q + 1#64).toNat - off) := by
    rw [hq1, show q.toNat + 1 - off = (q.toNat - off) + 1 by omega]
    exact wsAppendBin (k := withWstk st.core st1.core.wstk)
      (Nat.le_refl _) (fun _ r => r)
      (fun idx hidx => by dsimp only [st2, withWstk]; rw [List.getElem?_set_ne (by omega)])
      hin.kept
      (by dsimp only [st2, withWstk]; rw [show off + (q.toNat - off) = q.toNat by omega]
          exact List.getElem?_set_self (by omega))
      hfl_bin hne_ff (by rwa [← hot_def]) (by rwa [← hot_def])
  have hlm2 : RbLmCov c st2 off (q + 1#64).toNat pn.toNat := by
    intro x hx hnz; dsimp only [st2, lm2_raw] at hnz ⊢
    by_cases hxot : x = ot.toNat
    · subst hxot; left; refine ⟨q.toNat, hq_lo, by omega, ?_, ?_⟩
      · rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hfl_bin
      · rw [List.getElem?_set_self (by omega), Option.getD_some, hot_def]
    · rw [List.getElem?_set_ne (Ne.symm hxot)] at hnz
      rcases hin.lm x hx hnz with ⟨idx, hi1, hi2, hf, hv⟩ | hpb
      · left; refine ⟨idx, hi1, by omega, ?_, ?_⟩ <;> rw [List.getElem?_set_ne (by omega)]
        · exact hf
        · exact hv
      · exact Or.inr hpb
  rw [hlm2_eq]
  exact ⟨rbAgrees_trans hin.ag ⟨rfl, rfl⟩, hlen2, by omega, by rw [hp1, hq1]; omega,
    by rw [hp1]; omega, hin.pn_le,
    fun idx hidx => by
      dsimp only [st2]; rw [List.getElem?_set_ne (by omega)]; exact hin.tail_eq idx (by omega),
    fun idx hidx => by
      dsimp only [st2]; rw [List.getElem?_set_ne (by omega)]; exact hin.out_eq idx hidx,
    hrem_p1, hkept2, hlm2, hin.pa⟩

theorem rb_bin_push_step {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz : Nat} {pn p q : BitVec 64} {rot : BitVec 32} {nb' : BitVec 64}
    (hin : RbInner1Core c F_cur st l off sz pn p q st1)
    (hp1 : (p + 1#64).toNat = p.toNat + 1) (hpn1 : (pn + 1#64).toNat = pn.toNat + 1)
    (hp_lt : p.toNat < off + sz) (hpn_lt : pn.toNat < 2 * st.core.cur_vars)
    (_hl_lt : l < 2 * st.core.cur_vars) (hl_rp : l < st.core.repr.length)
    (hrot_lt : rot.toNat < 2 * st.core.cur_vars)
    (hent_sub : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(st.core.repr[l]'hl_rp).toNat, rot.toNat]))
    (hrem_p1 : WatchSliceOk F_cur st.core l (p + 1#64).toNat (off + sz - (p + 1#64).toNat))
    (hrot_lm : (BitVec.setWidth 64 rot).toNat < st1.core.lit_mark.length)
    (hrl_lt : (st.core.repr[l]'hl_rp).toNat < 2 * st.core.cur_vars) :
    let lm3 := st1.core.lit_mark.set (BitVec.setWidth 64 rot).toNat
      (BitVec.setWidth 8 (BitVec.setWidth 32
        (st1.core.lit_mark[(BitVec.setWidth 64 rot).toNat]'hrot_lm) ||| 2#32))
    let ws1' := st1.scratch.work_stk1.set pn.toNat (st.core.repr[l]'hl_rp)
    let ws2' := st1.scratch.work_stk2.set pn.toNat rot
    RbInner1Core c F_cur st l off sz (pn + 1#64) (p + 1#64) q
      { core := { st1.core with lit_mark := lm3, num_binary := nb' }
        scratch := { st1.scratch with work_stk1 := ws1', work_stk2 := ws2' } } := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl1 := hin.len.core_ok; have hsl1 := hin.len.scratch_ok
  have hlml1 := hcl1.lit_mark_len; have hws1l1 := hsl1.work_stk1_len
  have hws2l1 := hsl1.work_stk2_len; have hcv_le1 := hcl1.cur_vars_le
  have hcv1 := rbAgrees_cur_vars hin.ag
  have hq_lo := hin.q_lo; have hqp := hin.qp
  have hrot64 : (BitVec.setWidth 64 rot).toNat = rot.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  let lm3_raw := st1.core.lit_mark.set rot.toNat (st1.core.lit_mark[rot.toNat]'(by omega) ||| 2#8)
  have hlm3_eq : st1.core.lit_mark.set (BitVec.setWidth 64 rot).toNat
      (BitVec.setWidth 8 (BitVec.setWidth 32
        (st1.core.lit_mark[(BitVec.setWidth 64 rot).toNat]'hrot_lm) ||| 2#32)) = lm3_raw := by
    have hget : st1.core.lit_mark[(BitVec.setWidth 64 rot).toNat]'hrot_lm =
        st1.core.lit_mark[rot.toNat]'(by omega) :=
      Option.some.inj (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hrot64])
    rw [bv8_trunc_or2, hget]; exact congrArg (st1.core.lit_mark.set · _) hrot64
  let ws1' := st1.scratch.work_stk1.set pn.toNat (st.core.repr[l]'hl_rp)
  let ws2' := st1.scratch.work_stk2.set pn.toNat rot
  let st3 : FullState :=
    { core := { st1.core with lit_mark := lm3_raw, num_binary := nb' }
      scratch := { st1.scratch with work_stk1 := ws1', work_stk2 := ws2' } }
  have hlen3 : st3.LengthsOk c :=
    ⟨{ hcl1 with lit_mark_len := by simp [st3, lm3_raw, hlml1] },
     { hsl1 with work_stk1_len := by simp [st3, ws1', hws1l1],
                 work_stk2_len := by simp [st3, ws2', hws2l1] }⟩
  have hlm3 : RbLmCov c st3 off q.toNat (pn + 1#64).toNat := by
    intro x hx hnz; dsimp only [st3, lm3_raw, ws2'] at hnz ⊢
    by_cases hxr : x = rot.toNat
    · subst hxr; right; refine ⟨pn.toNat, by omega, ?_⟩
      rw [List.getElem?_set_self (by omega), Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hxr)] at hnz
      rcases hin.lm x hx hnz with h1 | ⟨k, hk, hkeq⟩
      · exact Or.inl h1
      · right; refine ⟨k, by omega, ?_⟩; rw [List.getElem?_set_ne (by omega)]; exact hkeq
  have hpa3 : RbPaOk F_cur st st3 (pn + 1#64).toNat := by
    intro k hk; dsimp only [st3, ws1', ws2']
    by_cases hkp : k = pn.toNat
    · subst hkp
      rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
        Option.getD_some, Option.getD_some]
      exact ⟨hrl_lt, hrot_lt, hent_sub⟩
    · rw [List.getElem?_set_ne (Ne.symm hkp), List.getElem?_set_ne (Ne.symm hkp)]
      exact hin.pa k (by omega)
  rw [hlm3_eq]
  exact ⟨rbAgrees_trans hin.ag ⟨rfl, rfl⟩, hlen3, hq_lo, by rw [hp1]; omega,
    by rw [hp1]; omega, by rw [hpn1]; omega,
    fun idx hidx => hin.tail_eq idx (by omega), hin.out_eq, hrem_p1, hin.kept, hlm3, hpa3⟩

theorem rb_bin_nb_step {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz : Nat} {pn p q : BitVec 64} {nb' : BitVec 64}
    (hin : RbInner1Core c F_cur st l off sz pn p q st1)
    (hp1 : (p + 1#64).toNat = p.toNat + 1) (hp_lt : p.toNat < off + sz)
    (hrem_p1 : WatchSliceOk F_cur st.core l (p + 1#64).toNat (off + sz - (p + 1#64).toNat)) :
    RbInner1Core c F_cur st l off sz pn (p + 1#64) q
      { st1 with core := { st1.core with num_binary := nb' } } := by
  have := hin.qp
  exact ⟨rbAgrees_trans hin.ag ⟨rfl, rfl⟩,
    ⟨{ hin.len.core_ok with wstk_len_arr := hin.len.core_ok.wstk_len_arr }, hin.len.scratch_ok⟩,
    hin.q_lo, by rw [hp1]; omega, by rw [hp1]; omega, hin.pn_le,
    fun idx hidx => hin.tail_eq idx (by omega), hin.out_eq, hrem_p1, hin.kept, hin.lm, hin.pa⟩

theorem rb_inner1_to_clear1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st1 : FullState} {l pn p q : BitVec 64} {off sz : Nat}
    (ho : RbOuterCore c F0 F_cur s0 l st)
    (hin : RbInner1Core c F_cur st l.toNat off sz pn p q st1)
    (hl_lt : l.toNat < 2 * s0.core.cur_vars)
    (hoff_def : off = fullWatchOff st l.toNat) (hsz_def : sz = fullWatchSize st l.toNat)
    (hoff_eq : (st.core.wvec[(l <<< 1#64).toNat]'(rb_wvec_shl_lt ho.sp.1
      ho.sp.1.core_ok.cur_vars_le (ho.cv_eq ▸ hl_lt)).2.2.1).toNat = off) :
    let hwv := rb_wvec_shl_lt ho.sp.1 ho.sp.1.core_ok.cur_vars_le (ho.cv_eq ▸ hl_lt)
    let offBV := (st.core.wvec[(l <<< 1#64).toNat]'hwv.2.2.1).setWidth 64
    RbClear1Core c st st1 off q.toNat pn.toNat offBV st1 := by
  subst hoff_def; subst hsz_def
  have hcl := ho.sp.1.core_ok; have hwle := hcl.wlen_le
  have hbd : fullWatchOff st l.toNat ≤ c.wcap := by
    have := hin.q_lo; have := hin.qp; have := hin.p_hi
    have hsb := (rb_outer_watches ho.sp).layout.bounds l.toNat (ho.cv_eq ▸ hl_lt)
    exact Nat.le_trans (Nat.le_trans hin.q_lo (Nat.le_trans hin.qp hin.p_hi))
      (Nat.le_trans hsb hwle)
  have h0_eq : ((st.core.wvec[(l <<< 1#64).toNat]'(rb_wvec_shl_lt ho.sp.1
      hcl.cur_vars_le (ho.cv_eq ▸ hl_lt)).2.2.1).setWidth 64).toNat =
      fullWatchOff st l.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hoff_eq]
  refine ⟨hin.ag, hin.len, rfl, rfl, rfl, rfl, Nat.le_of_eq h0_eq.symm,
    Nat.le_trans (Nat.le_of_eq h0_eq) hin.q_lo, fun x hx hnz => ?_⟩
  rcases hin.lm x hx hnz with ⟨idx, hi1, hi2, hf, hv⟩ | hpb
  · exact Or.inl ⟨idx, Nat.le_trans (Nat.le_of_eq h0_eq) hi1, hi2, hf, hv⟩
  · exact Or.inr hpb

theorem rb_clear1_bin_step {c : FullCfg} {F_cur : List (List Nat)} {st st1 st2 : FullState}
    {l off q_n pn_n : Nat} {ci q : BitVec 64}
    (hkept : WatchSliceOk F_cur (withWstk st.core st1.core.wstk) l off (q.toNat - off))
    (hc2 : RbClear1Core c st st1 off q_n pn_n ci st2)
    (hq_eq : q_n = q.toNat) (hci_lt : ci.toNat < q_n) (hci1 : (ci + 1#64).toNat = ci.toNat + 1)
    (hqs : q.toNat ≤ st1.core.wstk.length)
    (hf_ne : (st2.core.wstk[ci.toNat]'(by rw [hc2.wstk_eq]; omega) &&& 0x80000000#32) ≠ 0#32) :
    let w_ci := st2.core.wstk[ci.toNat]'(by rw [hc2.wstk_eq]; omega)
    let lit_ci := w_ci &&& 0x7FFFFFFF#32
    (BitVec.setWidth 64 lit_ci).toNat < st2.core.lit_mark.length ∧
    RbClear1Core c st st1 off q_n pn_n (ci + 1#64)
      { st2 with core := { st2.core with
        lit_mark := st2.core.lit_mark.set (BitVec.setWidth 64 lit_ci).toNat
          (BitVec.setWidth 8 (0 : BitVec 32)) } } := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl2 := hc2.len.core_ok; have hlml2 := hcl2.lit_mark_len
  have hcv2 := rbAgrees_cur_vars hc2.ag
  have hcv_le2 : st2.core.cur_vars ≤ c.max_vars := hcl2.cur_vars_le
  have hbin_lt : (st2.core.wstk[ci.toNat]'(by rw [hc2.wstk_eq]; omega) &&& 0x7FFFFFFF#32).toNat <
      2 * st.core.cur_vars := by
    have hb := wsBinLtOfFlag hkept ci.toNat hc2.ci_lo (by omega) (by
      dsimp only [withWstk]; rw [← hc2.wstk_eq, List.getElem?_eq_getElem (by
        rw [hc2.wstk_eq]; omega), Option.getD_some]; exact hf_ne)
    dsimp only [withWstk] at hb
    rwa [← hc2.wstk_eq, List.getElem?_eq_getElem (by rw [hc2.wstk_eq]; omega),
      Option.getD_some] at hb
  have hbin_lt_b : (BitVec.setWidth 64
      (st2.core.wstk[ci.toNat]'(by rw [hc2.wstk_eq]; omega) &&& 0x7FFFFFFF#32)).toNat <
      st2.core.lit_mark.length := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlml2]; omega
  refine ⟨hbin_lt_b, ?_⟩
  let clit := (st2.core.wstk[ci.toNat]'(by rw [hc2.wstk_eq]; omega) &&& 0x7FFFFFFF#32).toNat
  have hclit64 : (BitVec.setWidth 64
      (st2.core.wstk[ci.toNat]'(by rw [hc2.wstk_eq]; omega) &&& 0x7FFFFFFF#32)).toNat = clit := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hzero8 : BitVec.setWidth 8 (0 : BitVec 32) = 0#8 := rfl
  let st2' : FullState :=
    { st2 with core := { st2.core with lit_mark := st2.core.lit_mark.set clit 0#8 } }
  have hlm2' : ∀ x < 2 * c.max_vars, st2'.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
      (∃ idx, (ci + 1#64).toNat ≤ idx ∧ idx < q_n ∧
        (st2'.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
        (st2'.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∨
      (∃ k, k < pn_n ∧ (st2'.scratch.work_stk2[k]?.getD 0#32).toNat = x) := by
    intro x hx hnz; dsimp only [st2'] at hnz ⊢
    by_cases hxc : x = clit
    · subst hxc; rw [List.getElem?_set_self (by omega), Option.getD_some] at hnz
      exact absurd rfl hnz
    · rw [List.getElem?_set_ne (Ne.symm hxc)] at hnz
      rcases hc2.lm x hx hnz with ⟨idx, hi1, hi2, hf, hv⟩ | hpb
      · left; have hne_ci : idx ≠ ci.toNat := by
          rintro rfl
          rw [List.getElem?_eq_getElem (by rw [hc2.wstk_eq]; omega), Option.getD_some] at hv
          exact hxc hv.symm
        exact ⟨idx, by rw [hci1]; omega, hi2, hf, hv⟩
      · exact Or.inr hpb
  rw [hclit64, hzero8]
  exact ⟨rbAgrees_trans hc2.ag ⟨rfl, rfl⟩,
    ⟨{ hcl2 with lit_mark_len := by simp [hlml2] }, hc2.len.scratch_ok⟩,
    hc2.wstk_eq, hc2.nb_eq, hc2.ws1_eq, hc2.ws2_eq, by rw [hci1]; have := hc2.ci_lo; omega,
    by rw [hci1]; omega, hlm2'⟩

theorem rb_clear1_nonbin_step {c : FullCfg} {st st1 st2 : FullState} {off q_n pn_n : Nat}
    {ci : BitVec 64} (hc2 : RbClear1Core c st st1 off q_n pn_n ci st2)
    (hci_lt : ci.toNat < q_n) (hci1 : (ci + 1#64).toNat = ci.toNat + 1)
    (hci_w : ci.toNat < st2.core.wstk.length)
    (hf_eq : (st2.core.wstk[ci.toNat]'hci_w &&& 0x80000000#32) = 0#32) :
    RbClear1Core c st st1 off q_n pn_n (ci + 1#64) st2 := by
  refine ⟨hc2.ag, hc2.len, hc2.wstk_eq, hc2.nb_eq, hc2.ws1_eq, hc2.ws2_eq,
    by rw [hci1]; have := hc2.ci_lo; omega, by rw [hci1]; omega, fun x hx hnz => ?_⟩
  rcases hc2.lm x hx hnz with ⟨idx, hi1, hi2, hf, hv⟩ | hpb
  · left; have hne_ci : idx ≠ ci.toNat := by
      rintro rfl; rw [List.getElem?_eq_getElem hci_w, Option.getD_some] at hf; exact hf hf_eq
    exact ⟨idx, by rw [hci1]; omega, hi2, hf, hv⟩
  · exact Or.inr hpb

theorem rb_clear1_to_clear2 {c : FullCfg} {st st1 st2 : FullState} {off q_n pn_n : Nat}
    {ci : BitVec 64} (hc2 : RbClear1Core c st st1 off q_n pn_n ci st2)
    (hnl : ¬ ci.toNat < q_n) : RbClear2Core c st st1 pn_n 0#64 st2 :=
  ⟨hc2.ag, hc2.len, hc2.wstk_eq, hc2.nb_eq, hc2.ws1_eq, hc2.ws2_eq, Nat.zero_le _,
   fun x hx hnz => by
     rcases hc2.lm x hx hnz with ⟨idx, hi1, hi2, _⟩ | ⟨k, hk, heq⟩
     · omega
     · exact ⟨k, Nat.zero_le _, hk, heq⟩⟩

theorem rb_clear2_step {c : FullCfg} {F_cur : List (List Nat)} {st st1 st2b : FullState}
    {pn_n : Nat} {ci2 : BitVec 64}
    (hpa : RbPaOk F_cur st st1 pn_n) (hc2b : RbClear2Core c st st1 pn_n ci2 st2b)
    (hci2_lt : ci2.toNat < pn_n) (hci2_1 : (ci2 + 1#64).toNat = ci2.toNat + 1)
    (hpn_bd : pn_n ≤ st1.scratch.work_stk2.length) :
    ∃ (hci2_ws2 : ci2.toNat < st2b.scratch.work_stk2.length),
    let pblit := st2b.scratch.work_stk2[ci2.toNat]'hci2_ws2
    (BitVec.setWidth 64 pblit).toNat < st2b.core.lit_mark.length ∧
    RbClear2Core c st st1 pn_n (ci2 + 1#64)
      { st2b with core := { st2b.core with
        lit_mark := st2b.core.lit_mark.set (BitVec.setWidth 64 pblit).toNat
          (BitVec.setWidth 8 (0 : BitVec 32)) } } := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl2b := hc2b.len.core_ok; have hsl2b := hc2b.len.scratch_ok
  have hlml2b := hcl2b.lit_mark_len; have hws2l2b := hsl2b.work_stk2_len
  have hcv2b := rbAgrees_cur_vars hc2b.ag; have hcv_le2b := hcl2b.cur_vars_le
  have hci2_ws2 : ci2.toNat < st2b.scratch.work_stk2.length := by rw [hc2b.ws2_eq]; omega
  have hpb_lt_v : (st2b.scratch.work_stk2[ci2.toNat]'hci2_ws2).toNat < 2 * st.core.cur_vars := by
    have h0 := (hpa ci2.toNat hci2_lt).2.1
    rwa [← hc2b.ws2_eq, List.getElem?_eq_getElem hci2_ws2, Option.getD_some] at h0
  have hpb_lm : (BitVec.setWidth 64 (st2b.scratch.work_stk2[ci2.toNat]'hci2_ws2)).toNat <
      st2b.core.lit_mark.length := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlml2b]; omega
  refine ⟨hci2_ws2, hpb_lm, ?_⟩
  let pblit := (st2b.scratch.work_stk2[ci2.toNat]'hci2_ws2).toNat
  have hpblit64 : (BitVec.setWidth 64
      (st2b.scratch.work_stk2[ci2.toNat]'hci2_ws2)).toNat = pblit := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hzero8 : BitVec.setWidth 8 (0 : BitVec 32) = 0#8 := rfl
  let st2b' : FullState :=
    { st2b with core := { st2b.core with lit_mark := st2b.core.lit_mark.set pblit 0#8 } }
  have hlm2b' : ∀ x < 2 * c.max_vars, st2b'.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
      ∃ k, (ci2 + 1#64).toNat ≤ k ∧ k < pn_n ∧
        (st2b'.scratch.work_stk2[k]?.getD 0#32).toNat = x := by
    intro x hx hnz; dsimp only [st2b'] at hnz ⊢
    by_cases hxp : x = pblit
    · subst hxp; rw [List.getElem?_set_self (by omega), Option.getD_some] at hnz
      exact absurd rfl hnz
    · rw [List.getElem?_set_ne (Ne.symm hxp)] at hnz
      obtain ⟨k, hk1, hk2, hkeq⟩ := hc2b.lm x hx hnz
      have hne_k : k ≠ ci2.toNat := by
        rintro rfl
        rw [List.getElem?_eq_getElem hci2_ws2, Option.getD_some] at hkeq
        exact hxp hkeq.symm
      exact ⟨k, by rw [hci2_1]; omega, hk2, hkeq⟩
  rw [hpblit64, hzero8]
  exact ⟨rbAgrees_trans hc2b.ag ⟨rfl, rfl⟩,
    ⟨{ hcl2b with lit_mark_len := by simp [hlml2b] }, hsl2b⟩,
    hc2b.wstk_eq, hc2b.nb_eq, hc2b.ws1_eq, hc2b.ws2_eq, by rw [hci2_1]; omega, hlm2b'⟩

theorem rb_clear2_to_trim {c : FullCfg} {st st1 st2b : FullState} {q_n off sz pn_n : Nat}
    {ci2 q : BitVec 64} (hc2b : RbClear2Core c st st1 pn_n ci2 st2b)
    (hq_eq : q_n = q.toNat) (hq_hi : q_n ≤ off + sz) (hnl : ¬ ci2.toNat < pn_n) :
    (∀ x < 2 * c.max_vars, st2b.core.lit_mark[x]?.getD 0#8 = 0#8) ∧
    RbTrimCore c st st1 st2b q_n off sz q st2b :=
  ⟨fun x hx => Classical.byContradiction fun hnz => by
     obtain ⟨k, hk1, hk2, _⟩ := hc2b.lm x hx hnz; omega,
   ⟨hc2b.ag, hc2b.len, rfl, hc2b.nb_eq, hc2b.ws1_eq, hc2b.ws2_eq,
    hq_eq ▸ Nat.le_refl _, hq_eq ▸ hq_hi, fun _ _ => by rw [hc2b.wstk_eq]⟩⟩

theorem rb_trim_step {c : FullCfg} {st st1 st2b st3 : FullState} {q_n off sz : Nat}
    {ci3 : BitVec 64} (ht : RbTrimCore c st st1 st2b q_n off sz ci3 st3)
    (hci3_lt : ci3.toNat < off + sz) (hci3_1 : (ci3 + 1#64).toNat = ci3.toNat + 1)
    (_hend_bd : off + sz ≤ st3.core.wstk.length) :
    RbTrimCore c st st1 st2b q_n off sz (ci3 + 1#64)
      { st3 with core := { st3.core with
        wstk := st3.core.wstk.set ci3.toNat 0xFFFFFFFF#32 } } :=
  ⟨rbAgrees_trans ht.ag ⟨rfl, rfl⟩,
   ⟨{ ht.len.core_ok with wstk_len_arr := by simp [ht.len.core_ok.wstk_len_arr] },
     ht.len.scratch_ok⟩,
   ht.lm_eq, ht.nb_eq, ht.ws1_eq, ht.ws2_eq,
   by rw [hci3_1]; have := ht.ci3_lo; omega, by rw [hci3_1]; omega,
   fun idx hidx => by
     have hne : ci3.toNat ≠ idx := by have := ht.ci3_lo; omega
     dsimp only; rw [List.getElem?_set_ne hne]; exact ht.out_eq idx hidx⟩

theorem rb_finish_slice {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st1 st2b st3 : FullState} {l pn p q ci3 : BitVec 64} {off sz : Nat}
    (ho : RbOuterCore c F0 F_cur s0 l st)
    (hin : RbInner1Core c F_cur st l.toNat off sz pn p q st1)
    (ht : RbTrimCore c st st1 st2b q.toNat off sz ci3 st3)
    (hlm_zero : ∀ x < 2 * c.max_vars, st2b.core.lit_mark[x]?.getD 0#8 = 0#8)
    (hl_lt : l.toNat < 2 * s0.core.cur_vars)
    (hoff_def : off = fullWatchOff st l.toNat) (hsz_def : sz = fullWatchSize st l.toNat)
    (hoff_eq : (st.core.wvec[(l <<< 1#64).toNat]'(rb_wvec_shl_lt ho.sp.1
      ho.sp.1.core_ok.cur_vars_le (ho.cv_eq ▸ hl_lt)).2.2.1).toNat = off)
    (hsz_eq : (st.core.wvec[((l <<< 1#64) + 1#64).toNat]'(rb_wvec_shl_lt ho.sp.1
      ho.sp.1.core_ok.cur_vars_le (ho.cv_eq ▸ hl_lt)).2.2.2).toNat = sz)
    (hbound : off + sz ≤ st.core.wlen) (hq_hi : q.toNat ≤ off + sz)
    (hci3_eq : ci3.toNat = off + sz) :
    let hwv := rb_wvec_shl_lt ho.sp.1 ho.sp.1.core_ok.cur_vars_le (ho.cv_eq ▸ hl_lt)
    let wv_off := st.core.wvec[(l <<< 1#64).toNat]'hwv.2.2.1
    let wv_sz := st.core.wvec[((l <<< 1#64) + 1#64).toNat]'hwv.2.2.2
    let wu4 := st3.core.wusable + (wv_off.setWidth 64 + wv_sz.setWidth 64 - q)
    let wv4 := st3.core.wvec.set ((l <<< 1#64) + 1#64).toNat
      (BitVec.setWidth 32 (q - wv_off.setWidth 64))
    let st4 : FullState := { st3 with core := { st3.core with wvec := wv4, wusable := wu4 } }
    ((l <<< 1#64) + 1#64).toNat < st3.core.wvec.length ∧
    FullSparseInvW c F0 F_cur st4 ∧
    FullSparseInvW c F0 F_cur { st4 with core := { st4.core with oom := 1#64 } } ∧
    st4.core.cur_vars = s0.core.cur_vars ∧ st4.core.cur_level = 0 ∧
    st4.core.fuel = s0.core.fuel ∧ FullReprEquiv F_cur st4 ∧
    RbPaOk F_cur st st4 pn.toNat ∧
    RbEmitCore c F0 F_cur s0 st4 pn.toNat 0#64 st4 := by
  subst hoff_def; subst hsz_def
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := ho.sp.1.core_ok; have hwle := hcl.wlen_le; have hcv := ho.cv_eq
  have hcl3 := ht.len.core_ok; have hsl3 := ht.len.scratch_ok
  have hwv := rb_wvec_shl_lt ho.sp.1 hcl.cur_vars_le (hcv ▸ hl_lt)
  have hwu_idx : ((l <<< 1#64) + 1#64).toNat < st3.core.wvec.length := by
    rw [rbAgrees_wvec ht.ag, hwv.2.1, hcl.wvec_len]; have := hcl.cur_vars_le; omega
  let wv_off := st.core.wvec[(l <<< 1#64).toNat]'hwv.2.2.1
  let wv_sz := st.core.wvec[((l <<< 1#64) + 1#64).toNat]'hwv.2.2.2
  let wu4 := st3.core.wusable + (wv_off.setWidth 64 + wv_sz.setWidth 64 - q)
  let wv4 := st3.core.wvec.set ((l <<< 1#64) + 1#64).toNat
    (BitVec.setWidth 32 (q - wv_off.setWidth 64))
  let st4_raw : FullState :=
    { st with
      core := { st.core with
        lit_mark := st3.core.lit_mark
        wvec := st.core.wvec.set (2 * l.toNat + 1)
          (BitVec.ofNat 32 (q.toNat - fullWatchOff st l.toNat))
        wstk := st3.core.wstk, wusable := wu4, num_binary := st3.core.num_binary }
      scratch := { st.scratch with
        work_stk1 := st3.scratch.work_stk1, work_stk2 := st3.scratch.work_stk2 } }
  have hsp4 : FullSparseInvW c F0 F_cur st4_raw :=
    rewriteBins_slice_preserves_fullSparse ho.sp (hcv ▸ hl_lt) hin.q_lo hq_hi
      hcl3.wstk_len_arr hcl3.lit_mark_len hsl3.work_stk1_len hsl3.work_stk2_len
      (fun x hx => by rw [ht.lm_eq]; exact hlm_zero x hx)
      (fun idx hidx => by
        have hidx' : idx < q.toNat ∨ fullWatchOff st l.toNat + fullWatchSize st l.toNat ≤ idx :=
          hidx.elim (fun h1 => Or.inl (by have := hin.q_lo; omega)) (fun h2 => Or.inr h2)
        rw [ht.out_eq idx hidx']; exact hin.out_eq idx hidx)
      (wsRelocate (k := withWstk st.core st1.core.wstk)
        (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ r => r)
        (fun idx hidx => by
          dsimp only [withWstk]; exact ht.out_eq (fullWatchOff st l.toNat + idx)
            (Or.inl (by have := hin.q_lo; omega)))
        hin.kept)
  have hwvec_eq4 : wv4 = st.core.wvec.set (2 * l.toNat + 1)
      (BitVec.ofNat 32 (q.toNat - fullWatchOff st l.toNat)) := by
    have hw3 : st3.core.wvec = st.core.wvec := rbAgrees_wvec ht.ag
    have hoff_s : (BitVec.setWidth 64 wv_off).toNat = fullWatchOff st l.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hoff_eq]
    have hbv_eq : BitVec.setWidth 32 (q - wv_off.setWidth 64) =
        BitVec.ofNat 32 (q.toNat - fullWatchOff st l.toNat) := by
      apply BitVec.eq_of_toNat_eq
      have hsub : (q - wv_off.setWidth 64).toNat = q.toNat - fullWatchOff st l.toNat := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hoff_s]; exact hin.q_lo)), hoff_s]
      rw [BitVec.toNat_setWidth, hsub, BitVec.toNat_ofNat]
    dsimp only [wv4]; rw [hw3, hwv.2.1, hbv_eq]
  have heq_s : ({ st3 with core := { st3.core with wvec := wv4, wusable := wu4 } } : FullState) =
      st4_raw := by
    rw [hwvec_eq4]; exact rb_st4_eq ht.ag _ _
  have hpa4 : RbPaOk F_cur st st4_raw pn.toNat := by
    intro k hk; dsimp only [st4_raw]; rw [ht.ws1_eq, ht.ws2_eq]; exact hin.pa k hk
  refine ⟨hwu_idx, heq_s ▸ hsp4, ?_,
    (congrArg (fun x => x.core.cur_vars) heq_s).trans ho.cv_eq,
    (congrArg (fun x => x.core.cur_level) heq_s).trans ho.hl0,
    (congrArg (fun x => x.core.fuel) heq_s).trans ho.fuel_eq,
    heq_s ▸ ho.repr, heq_s ▸ hpa4,
    ⟨heq_s ▸ hsp4, (congrArg (fun x => x.core.cur_vars) heq_s).trans ho.cv_eq,
      (congrArg (fun x => x.core.cur_level) heq_s).trans ho.hl0,
      (congrArg (fun x => x.core.fuel) heq_s).trans ho.fuel_eq,
      heq_s ▸ ho.repr, rfl, rfl, Nat.zero_le _⟩⟩
  refine Eq.mpr (congrArg (FullSparseInvW c F0 F_cur) ?_) (fullSparseInvW_with_oom hsp4 1#64)
  dsimp only [wu4, wv4]
  have h1 := congrArg (fun x : FullState => { x with core := { x.core with oom := 1#64 } }) heq_s
  dsimp only [wu4, wv4] at h1
  exact h1

theorem rb_emit_unit_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st4 st5 : FullState} {pn ci4 : BitVec 64}
    (he : RbEmitCore c F0 F_cur s0 st4 pn.toNat ci4 st5)
    (hpa : RbPaOk F_cur st st4 pn.toNat) (hcv : st.core.cur_vars = s0.core.cur_vars)
    (hci4_lt : ci4.toNat < pn.toNat)
    (hci1 : ci4.toNat < st5.scratch.work_stk1.length)
    (hci2 : ci4.toNat < st5.scratch.work_stk2.length)
    (heq_ab : st5.scratch.work_stk1[ci4.toNat]'hci1 = st5.scratch.work_stk2[ci4.toNat]'hci2) :
    (st5.scratch.work_stk1[ci4.toNat]'hci1).toNat < 2 * st5.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(st5.scratch.work_stk1[ci4.toNat]'hci1).toNat]) := by
  obtain ⟨ha_lt, _, hab_ent⟩ := hpa ci4.toNat hci4_lt
  have h1_get := getElem_eq_getElem?_getD 0#32 hci1 he.ws1_eq rfl
  have h2_get := getElem_eq_getElem?_getD 0#32 hci2 he.ws2_eq rfl
  rw [h1_get, h2_get] at heq_ab
  rw [← heq_ab, ← h1_get] at hab_ent
  exact ⟨by rw [h1_get, he.cv_eq, ← hcv]; exact ha_lt, entails_unit_of_dup hab_ent⟩

theorem rb_emit_bin_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st4 st5 : FullState} {pn ci4 : BitVec 64}
    (he : RbEmitCore c F0 F_cur s0 st4 pn.toNat ci4 st5)
    (hpa : RbPaOk F_cur st st4 pn.toNat) (hci4_lt : ci4.toNat < pn.toNat)
    (hci1 : ci4.toNat < st5.scratch.work_stk1.length)
    (hci2 : ci4.toNat < st5.scratch.work_stk2.length) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(st5.scratch.work_stk1[ci4.toNat]'hci1).toNat,
                  (st5.scratch.work_stk2[ci4.toNat]'hci2).toNat]) := by
  obtain ⟨_, _, hab_ent⟩ := hpa ci4.toNat hci4_lt
  rw [getElem_eq_getElem?_getD 0#32 hci1 he.ws1_eq rfl,
    getElem_eq_getElem?_getD 0#32 hci2 he.ws2_eq rfl]
  exact hab_ent

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute
