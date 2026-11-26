/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep11
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearchProof0
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 11 PR 1: `full_switch_mode_m7` Proof (`FullFidelityStep11ProofMode`)

UNSAT-only `Func.wp` proof (`public section`, `0` `@[expose]` on theorems/lemmas, `0` `import all`,
`std3`, `XPost`-polymorphic) for Step-11 `fidStep11SwitchModeM7Fn` (`full_switch_mode_m7`,
implementing `S11-4` faithful `randec` mode-switch burst in `glue_used[56..63]`) against
`FullM7Search.m7SwitchModeSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep11

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
open LeanQbe.T.Examples.Kissat.FullM7Search
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

section SwitchModeStep11Helpers

local macro "fs_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

local macro "fs_jnz" h:ident : tactic =>
  `(tactic| (rw [wp_jnz]; dsimp only [Arg.val]; refine ⟨fun $h => ?_, fun $h => ?_⟩))

local elab "fs_nojnz" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

private theorem s11_bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem s11_bv64_sub1 {x : BitVec 64} (hx : x ≠ 0#64) : (x - 1#64).toNat = x.toNat - 1 := by
  have hpos : 0 < x.toNat := Nat.pos_of_ne_zero fun h0 =>
    hx (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

private theorem s11_bv64_lshr1_le (x : BitVec 64) : (x >>> 1#64).toNat ≤ x.toNat := by
  change (x >>> (1 : Nat)).toNat ≤ _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]; omega

private theorem s11_len_scalars {c : FullCfg} {s s' : FullState} (h : s.LengthsOk c)
    (hc : s'.core = s.core := by rfl)
    (h1 : s'.scratch.walk_vals = s.scratch.walk_vals := by rfl)
    (h2 : s'.scratch.phases = s.scratch.phases := by rfl)
    (h3 : s'.scratch.phases_target = s.scratch.phases_target := by rfl)
    (h4 : s'.scratch.phases_best = s.scratch.phases_best := by rfl)
    (h5 : s'.scratch.walk_best = s.scratch.walk_best := by rfl)
    (h6 : s'.scratch.heap = s.scratch.heap := by rfl)
    (h7 : s'.scratch.pos = s.scratch.pos := by rfl)
    (h8 : s'.scratch.shrink_stk = s.scratch.shrink_stk := by rfl)
    (h9 : s'.scratch.q_prev = s.scratch.q_prev := by rfl)
    (h10 : s'.scratch.q_next = s.scratch.q_next := by rfl)
    (h11 : s'.scratch.q_stamp = s.scratch.q_stamp := by rfl)
    (h12 : s'.scratch.wsort = s.scratch.wsort := by rfl)
    (h13 : s'.scratch.work_stk1 = s.scratch.work_stk1 := by rfl)
    (h14 : s'.scratch.work_stk2 = s.scratch.work_stk2 := by rfl)
    (h15 : s'.scratch.tarjan_mark = s.scratch.tarjan_mark := by rfl)
    (h16 : s'.scratch.tarjan_reach = s.scratch.tarjan_reach := by rfl)
    (h17 : s'.scratch.score = s.scratch.score := by rfl)
    (h18 : s'.scratch.sim_sig = s.scratch.sim_sig := by rfl)
    (h19 : s'.scratch.glue_used = s.scratch.glue_used := by rfl)
    (h20 : s'.scratch.last_learned = s.scratch.last_learned := by rfl)
    (h21 : s'.scratch.delayed = s.scratch.delayed := by rfl)
    (h22 : s'.scratch.red_refs = s.scratch.red_refs := by rfl)
    (h23 : s'.scratch.extend_stk = s.scratch.extend_stk := by rfl)
    (h24 : s'.scratch.scratch_buf = s.scratch.scratch_buf := by rfl) : s'.LengthsOk c :=
  ⟨hc ▸ h.core_ok, ⟨h1 ▸ h.scratch_ok.walk_vals_len, h2 ▸ h.scratch_ok.phases_len,
    h3 ▸ h.scratch_ok.phases_target_len, h4 ▸ h.scratch_ok.phases_best_len,
    h5 ▸ h.scratch_ok.walk_best_len, h6 ▸ h.scratch_ok.heap_len_arr, h7 ▸ h.scratch_ok.pos_len,
    h8 ▸ h.scratch_ok.shrink_stk_len, h9 ▸ h.scratch_ok.q_prev_len, h10 ▸ h.scratch_ok.q_next_len,
    h11 ▸ h.scratch_ok.q_stamp_len, h12 ▸ h.scratch_ok.wsort_len, h13 ▸ h.scratch_ok.work_stk1_len,
    h14 ▸ h.scratch_ok.work_stk2_len, h15 ▸ h.scratch_ok.tarjan_mark_len,
    h16 ▸ h.scratch_ok.tarjan_reach_len, h17 ▸ h.scratch_ok.score_len,
    h18 ▸ h.scratch_ok.sim_sig_len, h19 ▸ h.scratch_ok.glue_used_len,
    h20 ▸ h.scratch_ok.last_learned_len, h21 ▸ h.scratch_ok.delayed_len_arr,
    h22 ▸ h.scratch_ok.red_refs_len, h23 ▸ h.scratch_ok.extend_stk_len,
    h24 ▸ h.scratch_ok.scratch_buf_len⟩⟩

private theorem s11_apply_ite {α β : Type} (f : α → β) (P : Prop) [Decidable P] (a b : α) :
    f (if P then a else b) = if P then f a else f b := by
  by_cases h : P <;> simp [h]

private theorem s11_ite_eq {α : Type} (P : Prop) [Decidable P] {a b c : α}
    (ha : a = c) (hb : b = c) : (if P then a else b) = c := by
  by_cases h : P <;> simp [h, ha, hb]

private theorem s11_emaSwapSc_proj {α : Type} (f : FullScratch → α)
    (hf : ∀ (sc : FullScratch) st fb fe sb se gu,
      f { sc with
        stable := st, ema_fast_biased := fb, ema_fast_exp := fe,
        ema_slow_biased := sb, ema_slow_exp := se, glue_used := gu } = f sc)
    (sc : FullScratch) (om nm : BitVec 64) :
    f (m7EmaSwapSc sc om nm) = f sc := by
  rw [m7EmaSwapSc_eq]; dsimp only
  rw [s11_apply_ite f]
  exact s11_ite_eq _ (hf _ _ _ _ _ _ _) (hf _ _ _ _ _ _ _)

private theorem s11_probePres_emaSwap (sc : FullScratch) (om nm : BitVec 64)
    {s0 s1 : FullState} (hp : FullProbeScratchPres s0 s1)
    (hsc : s1.scratch = sc) :
    FullProbeScratchPres s0 { s1 with scratch := m7EmaSwapSc sc om nm } := by
  subst hsc
  have h : ∀ {α} (f : FullScratch → α)
      (hf : ∀ (sc : FullScratch) st fb fe sb se gu,
        f { sc with
          stable := st, ema_fast_biased := fb, ema_fast_exp := fe,
          ema_slow_biased := sb, ema_slow_exp := se, glue_used := gu } = f sc),
      f (m7EmaSwapSc s1.scratch om nm) = f s1.scratch :=
    fun f hf => s11_emaSwapSc_proj f hf s1.scratch om nm
  exact ⟨⟨(h _ fun _ _ _ _ _ _ _ => rfl).trans hp.1.1,
      (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.1.2⟩,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.2.2.1,
    (h _ fun _ _ _ _ _ _ _ => rfl).trans hp.2.2.2.2.2.2.2⟩

private theorem s11_probePres_refl (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem s11_probePres_trans {s0 s1 s2 : FullState}
    (h1 : FullProbeScratchPres s0 s1) (h2 : FullProbeScratchPres s1 s2) :
    FullProbeScratchPres s0 s2 :=
  ⟨⟨h2.1.1.trans h1.1.1, h2.1.2.trans h1.1.2⟩,
    h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
    h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2⟩

private theorem s11_ema_swap_f2s_stable (sc : FullScratch) :
    (m7EmaSwapSc sc 0#64 1#64).stable = 1#64 := by
  rw [m7EmaSwapSc_eq]; dsimp only
  rw [s11_apply_ite FullScratch.stable]
  exact s11_ite_eq _ rfl rfl

private theorem s11_get64_emaSet_mask (gu : List (BitVec 32)) (mode : Nat)
    (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :
    m7Get64Val (m7ModeEmaSet gu mode v) m7GuEmaMaskIdx = m7Get64Val gu m7GuEmaMaskIdx := by
  have hltG : ∀ (g : List (BitVec 32)) idx val, 40 ≤ idx →
      m7Get64Val (m7Set64List g idx val) m7GuEmaMaskIdx = m7Get64Val g m7GuEmaMaskIdx :=
    fun g idx val hidx => m7Get64Val_set64_ne val (Or.inl (by rw [m7GuEmaMaskIdx_eq]; omega))
  rw [m7ModeEmaSet_eq, m7GuEma0FbIdx_eq, m7GuEma1FbIdx_eq]; dsimp only
  by_cases hm : mode = 0 <;> simp only [hm, ↓reduceIte]
  · rw [hltG _ 46 _ (by omega), hltG _ 44 _ (by omega),
      hltG _ 42 _ (by omega), hltG _ 40 _ (by omega)]
  · rw [hltG _ 54 _ (by omega), hltG _ 52 _ (by omega),
      hltG _ 50 _ (by omega), hltG _ 48 _ (by omega)]

private theorem s11_modeEmaGet_set_mask (gu : List (BitVec 32)) (mode : Nat)
    (idx : BitVec 64) :
    m7ModeEmaGet (m7Set64List gu m7GuEmaMaskIdx idx) mode = m7ModeEmaGet gu mode := by
  have hge : ∀ j, 40 ≤ j → m7Get64Val (m7Set64List gu m7GuEmaMaskIdx idx) j = m7Get64Val gu j :=
    fun j hj => m7Get64Val_set64_ne idx (Or.inr (by rw [m7GuEmaMaskIdx_eq]; omega))
  rw [m7ModeEmaGet_eq, m7ModeEmaGet_eq, m7GuEma0FbIdx_eq, m7GuEma1FbIdx_eq]; dsimp only
  by_cases hm : mode = 0 <;> simp only [hm, ↓reduceIte]
  · rw [hge 40 (by omega), hge 42 (by omega), hge 44 (by omega), hge 46 (by omega)]
  · rw [hge 48 (by omega), hge 50 (by omega), hge 52 (by omega), hge 54 (by omega)]

private theorem s11_bit0_or_left {a b : BitVec 64} (h : (a &&& 1#64) ≠ 0#64) :
    ((a ||| b) &&& 1#64) ≠ 0#64 := by
  intro hc
  have h1 := congrArg (fun x : BitVec 64 => x[0]) hc
  simp only [BitVec.getElem_and, BitVec.getElem_or,
    show (1#64 : BitVec 64)[0] = true by decide, Bool.and_true,
    show (0#64 : BitVec 64)[0] = false by decide, Bool.or_eq_false_iff] at h1
  apply h
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rcases k with rfl | k
  · simp [h1.1]
  · have hb : (1#64 : BitVec 64)[k + 1] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, show (1#64 : BitVec 64).toNat = 1 by decide,
        Nat.testBit_succ]
      simp
    simp only [BitVec.getElem_and, BitVec.getElem_zero, hb, Bool.and_false]

private theorem s11_ema_swap_s2f_facts (sc : FullScratch) (hgu : sc.glue_used.length = 64) :
    let sc' := m7EmaSwapSc sc 1#64 0#64
    sc'.stable = 0#64 ∧
      m7ModeEmaGet sc'.glue_used 1 =
        (sc.ema_fast_biased, sc.ema_fast_exp, sc.ema_slow_biased, sc.ema_slow_exp) ∧
      ((m7Get64Val sc.glue_used m7GuMagicIdx = m7SearchMagic ∧
        (m7Get64Val sc.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
       let saved := m7ModeEmaGet sc.glue_used 0
       sc'.ema_fast_biased = saved.1 ∧ sc'.ema_fast_exp = saved.2.1 ∧
       sc'.ema_slow_biased = saved.2.2.1 ∧ sc'.ema_slow_exp = saved.2.2.2) := by
  rw [m7EmaSwapSc_eq]; dsimp only
  simp only [show ((1#64 : BitVec 64) ≠ 0#64) = True by decide,
    show ((0#64 : BitVec 64) ≠ 0#64) = False by decide, ↓reduceIte]
  let gu0 := m7StateInitGu { sc with stable := BitVec.ofNat 64 1 }
  have hgu0 : gu0.length = 64 := (m7StateInitGu_length _).trans hgu
  let curV := (sc.ema_fast_biased, sc.ema_fast_exp, sc.ema_slow_biased, sc.ema_slow_exp)
  let gu1 := m7ModeEmaSet gu0 1 curV
  let mask := m7Get64Val gu1 m7GuEmaMaskIdx ||| 1#64 <<< 1
  refine ⟨?_, ?_, ?_⟩
  · rw [s11_apply_ite FullScratch.stable]; exact s11_ite_eq _ rfl rfl
  · by_cases hcond : mask &&& 1#64 <<< 0 ≠ 0#64
    · have hc' := hcond; dsimp only [mask, gu1, curV, gu0] at hc'
      simp only [eq_true hc', ↓reduceIte, s11_modeEmaGet_set_mask]
      exact m7ModeEmaGet_set_self curV hgu0
    · have hc' := hcond; dsimp only [mask, gu1, curV, gu0] at hc'
      simp only [eq_false hc', ↓reduceIte, s11_modeEmaGet_set_mask]
      rw [m7ModeEmaGet_set_other _ (by decide : (0 = 0) ≠ (1 = 0))]
      exact m7ModeEmaGet_set_self curV hgu0
  · rintro ⟨hmag, hmask⟩
    have hgu0_eq : gu0 = sc.glue_used := m7StateInitGu_of_magic hmag
    have hmask1 : m7Get64Val gu1 m7GuEmaMaskIdx = m7Get64Val sc.glue_used m7GuEmaMaskIdx := by
      dsimp only [gu1]; rw [s11_get64_emaSet_mask, hgu0_eq]
    have hcond : mask &&& 1#64 <<< 0 ≠ 0#64 := by
      rw [show (1#64 <<< 0 : BitVec 64) = 1#64 by decide]
      dsimp only [mask]; rw [hmask1]
      exact s11_bit0_or_left hmask
    have hc' := hcond; dsimp only [mask, gu1, curV, gu0] at hc'
    simp only [eq_true hc', ↓reduceIte]
    have hnw : m7ModeEmaGet gu1 0 = m7ModeEmaGet sc.glue_used 0 := by
      dsimp only [gu1]; rw [m7ModeEmaGet_set_other _ (by decide : (1 = 0) ≠ (0 = 0)), hgu0_eq]
    rw [hnw]
    exact ⟨rfl, rfl, rfl, rfl⟩

private theorem s11_modeEmaGet1_set64_ge56 (gu : List (BitVec 32)) {idx : Nat} (val : BitVec 64)
    (hidx : 56 ≤ idx) :
    m7ModeEmaGet (m7Set64List gu idx val) 1 = m7ModeEmaGet gu 1 := by
  rw [m7ModeEmaGet_eq, m7ModeEmaGet_eq, m7GuEma1FbIdx_eq]; dsimp only
  simp only [show (1 = 0) = False by decide, ↓reduceIte]
  rw [m7Get64Val_set64_ne val (Or.inl (by omega)),
    m7Get64Val_set64_ne val (Or.inl (by omega)),
    m7Get64Val_set64_ne val (Or.inl (by omega)),
    m7Get64Val_set64_ne val (Or.inl (by omega))]

private def S11ModeFocusInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (sRet : FullState) (mRet : Mem 64) : Prop :=
  sRet.core = s.core ∧ sRet.LengthsOk c ∧ FullProbeScratchPres s sRet ∧
  M7GuPrefixPres s sRet ∧ M7StateInitOk sRet.scratch.glue_used ∧
  m7ModeEmaGet sRet.scratch.glue_used 1 =
    (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
     s.scratch.ema_slow_biased, s.scratch.ema_slow_exp) ∧
  sRet.scratch.stable = 0#64 ∧
  ((m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic ∧
    (m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
   let saved := m7ModeEmaGet s.scratch.glue_used 0
   sRet.scratch.ema_fast_biased = saved.1 ∧ sRet.scratch.ema_fast_exp = saved.2.1 ∧
   sRet.scratch.ema_slow_biased = saved.2.2.1 ∧
   sRet.scratch.ema_slow_exp = saved.2.2.2) ∧
  (FullMem c sRet ⋆ R) mRet

private theorem s11_call_set64_randec {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64, i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {s sCur : FullState} {idx val : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, idx, val, ()))
    (hSet : EnvSpec Γ "full_m7_set64" m7Set64Spec)
    (hidx_lo : 56 ≤ idx.toNat) (hidx_hi : idx.toNat < 63)
    (hinv : S11ModeFocusInv c s R sCur m)
    (hk : ∀ (s' : FullState) (m' : Mem 64), S11ModeFocusInv c s R s' m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_m7_set64" args k) m := by
  obtain ⟨hcore, hlen, hps, hpre, hinit, hema1, hst0, hsaved, hm⟩ := hinv
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hSet _ _ _ _ (m7Set64Spec_of hlen hm fun hlen' m' hm' => ?_)
  dsimp only at hlen' hm'
  simp only [hidx_hi, ↓reduceIte] at hlen' hm'
  let sc' : FullScratch :=
    { sCur.scratch with glue_used := m7Set64List sCur.scratch.glue_used idx.toNat val }
  let s' : FullState := { sCur with scratch := sc' }
  refine hk s' m' ⟨hcore, hlen', hps,
    M7GuPrefixPres.trans hpre (M7GuPrefixPres.of_set64 val (by omega)),
    M7StateInitOk.of_set64 hinit (by omega) val,
    (s11_modeEmaGet1_set64_ge56 sCur.scratch.glue_used val hidx_lo).trans hema1,
    hst0, hsaved, hm'⟩

private theorem s11_call_get64_randec {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {s sCur : FullState} {idx : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, idx, ()))
    (hGet : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hinv : S11ModeFocusInv c s R sCur m)
    (hk : ∀ (v : BitVec 64), wp Γ Q X (k (v, ())) m) :
    wp Γ Q X (.call "full_m7_get64" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hGet _ _ _ _ (m7Get64Spec_of hinv.2.1 hinv.2.2.2.2.2.2.2.2 (hk _))

/-- Parametric `Func.wp` proof for `fidStep11SwitchModeM7Fn` (`full_switch_mode_m7` with `S11-4`
faithful `randec` burst on focused re-entry) against `FullM7Search.m7SwitchModeSpec`. -/
theorem full_switch_mode_m7_step11_wp (Γ : Env)
    (hIlog : EnvSpec Γ "full_ilog10" fullIlog10Spec)
    (hHeapDown : EnvSpec Γ "full_heap_down" fullHeapDownSpec)
    (hEmaSwap : EnvSpec Γ "full_ema_swap_m7" m7EmaSwapSpec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hGet64 : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet64 : EnvSpec Γ "full_m7_set64" m7Set64Spec) :
    ∀ a m Q X, m7SwitchModeSpec a m Q X → Func.wp Γ fidStep11SwitchModeM7Fn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, s, R, hc_eq, hlen, hm, hQ⟩ := m7SwitchModeSpec_elim hspec
  dsimp only at hc_eq; subst hc_eq
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  have hok := hlen.core_ok
  have hsok := hlen.scratch_ok
  have hcv_le := hok.cur_vars_le
  unfold Func.wp fidStep11SwitchModeM7Fn full_switch_mode_m7_body; dsimp only
  let P : Tup Val [i64, i64] → Mem 64 → Prop := fun (om, nm, _) mJ =>
    ∃ sJ : FullState,
      sJ.core = s.core ∧ sJ.LengthsOk c ∧ FullProbeScratchPres s sJ ∧
      om = (if s.scratch.stable = 0#64 then 0#64 else 1#64) ∧
      nm = (if s.scratch.stable = 0#64 then 1#64 else 0#64) ∧
      (s.scratch.stable = 0#64 → s.scratch.mode_confl_lim ≤ s.scratch.conflicts) ∧
      (s.scratch.stable ≠ 0#64 →
        s.scratch.mode_tick_lim ≤ s.scratch.search_ticks ∧ M7GuPrefixPres s sJ ∧
        sJ.scratch.glue_used = s.scratch.glue_used ∧
        sJ.scratch.ema_fast_biased = s.scratch.ema_fast_biased ∧
        sJ.scratch.ema_fast_exp = s.scratch.ema_fast_exp ∧
        sJ.scratch.ema_slow_biased = s.scratch.ema_slow_biased ∧
        sJ.scratch.ema_slow_exp = s.scratch.ema_slow_exp) ∧
      (FullMem c sJ ⋆ R) mJ
  refine wp_join_group P ?_ ?_
  · rintro Js ⟨om, nm, ⟨⟩⟩ mJ ⟨sJ, hcJ, hlenJ, hpsJ, hom, hnm, hf2s, hs2f, hmJ⟩
    rw [Blocks.get_here]
    c0_hsteps_nogrp
    let sJ1 : FullState := { sJ with scratch := { sJ.scratch with
      switched := sJ.scratch.switched + 1#64
      mode_count := sJ.scratch.mode_count + 1#64 } }
    have hlenJ1 : sJ1.LengthsOk c := s11_len_scalars hlenJ
    fs_call hEmaSwap
    refine m7EmaSwapSpec_of hlenJ1 (by assumption) fun hlenSw hpreSw hinitSw mSw hmSw => ?_
    let sSw : FullState := { sJ1 with scratch := m7EmaSwapSc sJ1.scratch om nm }
    let Pret : Tup Val [] → Mem 64 → Prop := fun _ mRet =>
      ∃ sRet : FullState,
        sRet.core = s.core ∧ sRet.LengthsOk c ∧ FullProbeScratchPres s sRet ∧
        (s.scratch.stable = 0#64 →
          M7StateInitOk sRet.scratch.glue_used ∧ sRet.scratch.stable = 1#64) ∧
        (s.scratch.stable ≠ 0#64 →
          M7GuPrefixPres s sRet ∧ M7StateInitOk sRet.scratch.glue_used ∧
          m7ModeEmaGet sRet.scratch.glue_used 1 =
            (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
             s.scratch.ema_slow_biased, s.scratch.ema_slow_exp) ∧
          sRet.scratch.stable = 0#64 ∧
          ((m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic ∧
            (m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
           let saved := m7ModeEmaGet s.scratch.glue_used 0
           sRet.scratch.ema_fast_biased = saved.1 ∧ sRet.scratch.ema_fast_exp = saved.2.1 ∧
           sRet.scratch.ema_slow_biased = saved.2.2.1 ∧
           sRet.scratch.ema_slow_exp = saved.2.2.2)) ∧
        (FullMem c sRet ⋆ R) mRet
    refine wp_join_group Pret ?_ ?_
    · rintro Js_r ⟨⟩ mRet ⟨sRet, hcRet, hlenRet, hpsRet, hrf2s, hrs2f, hmRet⟩
      rw [Blocks.get_here]
      c0_hsteps_nogrp
      refine hQ sRet mRet hcRet hlenRet hpsRet ?_ ?_ ?_ hmRet
      · intro hEarly
        exfalso
        rcases hEarly with ⟨hst0, hlt⟩ | ⟨hstne, hlt⟩
        · have hle := hf2s hst0
          exact Nat.not_lt_of_ge (BitVec.le_def.mp hle) (BitVec.lt_def.mp hlt)
        · have hle := (hs2f hstne).1
          exact Nat.not_lt_of_ge (BitVec.le_def.mp hle) (BitVec.lt_def.mp hlt)
      · rintro ⟨hst0, _⟩; exact hrf2s hst0
      · rintro ⟨hstne, _⟩; exact hrs2f hstne
    · intro Js_r hJs_r
      have hpsSw : FullProbeScratchPres s sSw :=
        s11_probePres_emaSwap sJ1.scratch om nm hpsJ rfl
      fs_nojnz
      fs_jnz hstab0
      · simp only [beq_iff_eq] at hstab0
        have hstne : s.scratch.stable ≠ 0#64 := by
          intro hst0
          have hom0 : om = 0#64 := by simp [hom, hst0]
          have hnm1 : nm = 1#64 := by simp [hnm, hst0]
          have h1 : sSw.scratch.stable = 1#64 := by
            dsimp only [sSw]; rw [hom0, hnm1]; exact s11_ema_swap_f2s_stable _
          rw [h1] at hstab0
          exact absurd hstab0 (by decide)
        obtain ⟨_, hpreJ, hguJ, hfbJ, hfeJ, hsbJ, hseJ⟩ := hs2f hstne
        have hom1 : om = 1#64 := by simp [hom, hstne]
        have hnm0 : nm = 0#64 := by simp [hnm, hstne]
        have hguSw : sJ1.scratch.glue_used.length = 64 := hlenJ1.scratch_ok.glue_used_len
        have hfacts := s11_ema_swap_s2f_facts sJ1.scratch hguSw
        have heq_f : sSw.scratch = m7EmaSwapSc sJ1.scratch 1#64 0#64 := by
          dsimp only [sSw]; rw [hom1, hnm0]
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun _ mRl => mRl = mSw) ?_ ?_
        · rintro J_rl ⟨rs, ⟨⟩⟩ mRl rfl
          rw [Blocks.get_here]
          c0_hsteps_nogrp
          let sRet0 : FullState := { sSw with scratch := { sSw.scratch with
            restart_limit := sSw.scratch.conflicts + rs } }
          have hlenRet0 : sRet0.LengthsOk c := s11_len_scalars hlenSw
          have hpre0 : M7GuPrefixPres s sRet0 :=
            M7GuPrefixPres.trans hpreJ (@M7GuPrefixPres.congr_glue sJ1 sSw sJ sRet0 rfl rfl hpreSw)
          have hema1_0 : m7ModeEmaGet sRet0.scratch.glue_used 1 =
              (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
               s.scratch.ema_slow_biased, s.scratch.ema_slow_exp) := by
            change m7ModeEmaGet sSw.scratch.glue_used 1 = _
            rw [heq_f, hfacts.2.1]
            change (sJ.scratch.ema_fast_biased, sJ.scratch.ema_fast_exp,
              sJ.scratch.ema_slow_biased, sJ.scratch.ema_slow_exp) = _
            rw [hfbJ, hfeJ, hsbJ, hseJ]
          have hst0_0 : sRet0.scratch.stable = 0#64 := by
            change sSw.scratch.stable = 0#64; rw [heq_f]; exact hfacts.1
          have hmag_eq : m7Get64Val sJ1.scratch.glue_used m7GuMagicIdx =
              m7Get64Val s.scratch.glue_used m7GuMagicIdx := by
            change m7Get64Val sJ.scratch.glue_used _ = _; rw [hguJ]
          have hmsk_eq : m7Get64Val sJ1.scratch.glue_used m7GuEmaMaskIdx =
              m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx := by
            change m7Get64Val sJ.scratch.glue_used _ = _; rw [hguJ]
          have hget0_eq : m7ModeEmaGet sJ1.scratch.glue_used 0 =
              m7ModeEmaGet s.scratch.glue_used 0 := by
            change m7ModeEmaGet sJ.scratch.glue_used 0 = _; rw [hguJ]
          have hsaved0 :
              ((m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic ∧
                (m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
               let saved := m7ModeEmaGet s.scratch.glue_used 0
               sRet0.scratch.ema_fast_biased = saved.1 ∧ sRet0.scratch.ema_fast_exp = saved.2.1 ∧
               sRet0.scratch.ema_slow_biased = saved.2.2.1 ∧
               sRet0.scratch.ema_slow_exp = saved.2.2.2) := by
            intro ⟨hm1, hm2⟩
            have hsav := hfacts.2.2 ⟨by rw [hmag_eq]; exact hm1, by rw [hmsk_eq]; exact hm2⟩
            rw [← hget0_eq]
            change sSw.scratch.ema_fast_biased = _ ∧ sSw.scratch.ema_fast_exp = _ ∧
              sSw.scratch.ema_slow_biased = _ ∧ sSw.scratch.ema_slow_exp = _
            rw [heq_f]; exact hsav
          have hinv0 : S11ModeFocusInv c s R sRet0 _ :=
            ⟨hcJ, hlenRet0, hpsSw, hpre0, hinitSw, hema1_0, hst0_0, hsaved0, by assumption⟩
          refine s11_call_get64_randec rfl hGet64 hinv0 fun rem0 => ?_
          c0_hsteps_nogrp
          refine s11_call_get64_randec rfl hGet64 hinv0 fun lc0 => ?_
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ m1 => ∃ s1, S11ModeFocusInv c s R s1 m1) ?_ ?_
          · rintro _ ⟨rem1, ⟨⟩⟩ m1 ⟨s1, hinv1⟩
            rw [Blocks.get_here]
            have hm1 := hinv1.2.2.2.2.2.2.2.2
            c0_hsteps_nogrp
            refine s11_call_set64_randec rfl hSet64 (by decide) (by decide) hinv1
              fun s2 m2 hinv2 => ?_
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ m3 => ∃ s3, S11ModeFocusInv c s R s3 m3) ?_ ?_
            · rintro _ ⟨⟩ m3 ⟨s3, hc3, hlen3, hps3, hpre3, hinit3, hema3, hst3, hsav3, hm3⟩
              rw [Blocks.get_here]
              exact hJs_r () m3 ⟨s3, hc3, hlen3, hps3, fun h0 => absurd h0 hstne,
                fun _ => ⟨hpre3, hinit3, hema3, hst3, hsav3⟩, hm3⟩
            · intro Jb hJb
              fs_nojnz
              fs_jnz hrem0
              · c0_hsteps_nogrp
                refine s11_call_get64_randec rfl hGet64 hinv2 fun seq0 => ?_
                c0_hsteps_nogrp
                refine s11_call_set64_randec rfl hSet64 (by decide) (by decide) hinv2
                  fun s3 m3 hinv3 => ?_
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64])
                  (fun _ m4 => m4 = m3) ?_ ?_
                · rintro _ ⟨qarg, ⟨⟩⟩ m4 rfl
                  rw [Blocks.get_here]; c0_hsteps_nogrp
                  fs_call hLog10
                  refine m7Log10Q16Spec_of fun lg _ _ => ?_
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64]) (fun _ m5 => m5 = m4) ?_ ?_
                  · rintro _ ⟨rlen, ⟨⟩⟩ m5 rfl
                    rw [Blocks.get_here]; c0_hsteps_nogrp
                    refine s11_call_set64_randec rfl hSet64 (by decide) (by decide) hinv3
                      fun s4 m4 hinv4 => ?_
                    have hm4 := hinv4.2.2.2.2.2.2.2.2
                    c0_hsteps_nogrp
                    refine s11_call_set64_randec rfl hSet64 (by decide) (by decide) hinv4
                      fun s5 m5 hinv5 => ?_
                    c0_hsteps_nogrp
                    exact hJb () m5 ⟨s5, hinv5⟩
                  · intro Jrlen hJrlen; fs_nojnz
                    fs_jnz hrl <;> c0_hsteps_nogrp <;> exact hJrlen _ m4 rfl
                · intro Jq hJq; fs_nojnz
                  fs_jnz hq <;> c0_hsteps_nogrp <;> exact hJq _ m3 rfl
              · c0_hsteps_nogrp
                exact hJb () m2 ⟨s2, hinv2⟩
          · intro Jd hJd
            have hm0 := hinv0.2.2.2.2.2.2.2.2
            fs_nojnz
            fs_jnz hgt
            · c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun _ m1 => S11ModeFocusInv c s R sRet0 m1) ?_ ?_
              · rintro _ ⟨rem', ⟨⟩⟩ m1 hinv1'
                rw [Blocks.get_here]; c0_hsteps_nogrp
                refine s11_call_set64_randec rfl hSet64 (by decide) (by decide) hinv1'
                  fun s1 m1 hinv1 => ?_
                c0_hsteps_nogrp
                exact hJd (rem', ()) m1 ⟨s1, hinv1⟩
              · intro Jsub hJsub; fs_nojnz
                fs_jnz hrg <;> c0_hsteps_nogrp <;> exact hJsub _ _ hinv0
            · c0_hsteps_nogrp
              exact hJd (rem0, ()) _ ⟨sRet0, hinv0⟩
        · intro J_rl hJ_rl
          fs_nojnz
          fs_jnz hrg0
          · c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = mSw) ?_ ?_
            · rintro J_r2 ⟨rc, ⟨⟩⟩ m2 hm2
              subst m2; rw [Blocks.get_here]; c0_hsteps_nogrp
              fs_call hIlog; intro r _ _
              refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = mSw) ?_ ?_
              · rintro J_r3 ⟨d, ⟨⟩⟩ m3 hm3
                subst m3; rw [Blocks.get_here]; c0_hsteps_nogrp
                exact hJ_rl (d, ()) mSw rfl
              · intro J_r3 hJ_r3; fs_nojnz
                fs_jnz hdg1 <;> c0_hsteps_nogrp <;> exact hJ_r3 _ mSw rfl
            · intro J_r2 hJ_r2; fs_nojnz
              fs_jnz hrlim <;> c0_hsteps_nogrp <;> exact hJ_r2 _ mSw rfl
          · c0_hsteps_nogrp; exact hJ_rl (1#64, ()) mSw rfl
      · simp only [beq_eq_false_iff_ne] at hstab0
        have hst0 : s.scratch.stable = 0#64 := by
          by_cases hst : s.scratch.stable = 0#64
          · exact hst
          · exfalso
            have hom1 : om = 1#64 := by simp [hom, hst]
            have hnm0 : nm = 0#64 := by simp [hnm, hst]
            have h0 : sSw.scratch.stable = 0#64 := by
              dsimp only [sSw]; rw [hom1, hnm0]
              exact (s11_ema_swap_s2f_facts sJ1.scratch hlenJ1.scratch_ok.glue_used_len).1
            exact hstab0 h0
        have hom0 : om = 0#64 := by simp [hom, hst0]
        have hnm1 : nm = 1#64 := by simp [hnm, hst0]
        have h1 : sSw.scratch.stable = 1#64 := by
          dsimp only [sSw]; rw [hom0, hnm1]; exact s11_ema_swap_f2s_stable _
        c0_hsteps_nogrp
        exact hJs_r () mSw ⟨sSw, hcJ, hlenSw, hpsSw,
          fun _ => ⟨hinitSw, h1⟩, fun hne => absurd hst0 hne, hmSw⟩
  · intro Js hJs
    fs_nojnz
    fs_jnz hst0
    · simp only [beq_iff_eq] at hst0
      fs_nojnz
      fs_jnz hconfl
      · simp only [BitVec.ult, decide_eq_true_eq] at hconfl
        c0_hsteps_nogrp
        exact hQ s m rfl hlen (s11_probePres_refl s) (fun _ => rfl)
          (fun ⟨_, hle⟩ => absurd (BitVec.le_def.mp hle) (Nat.not_le_of_gt hconfl))
          (fun ⟨hne, _⟩ => absurd hst0 hne) hm
      · simp only [BitVec.ult, decide_eq_false_iff_not] at hconfl
        have hle_confl : s.scratch.mode_confl_lim ≤ s.scratch.conflicts :=
          BitVec.le_def.mpr (Nat.le_of_not_lt hconfl)
        c0_hsteps_nogrp
        let s1 : FullState := { s with scratch := { s.scratch with stable := 1#64 } }
        refine wp_join_group (ts := [i64])
          (fun _ m1 => (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro J_d ⟨delta, ⟨⟩⟩ m1 hm1
          rw [Blocks.get_here]; c0_hsteps_nogrp
          let s2 : FullState := { s1 with scratch := { s1.scratch with
            mode_tick_lim := s1.scratch.search_ticks + delta
            mode_saved_ticks := s1.scratch.search_ticks } }
          refine wp_join_group (ts := [i64])
            (fun _ m2 => (FullMem c s2 ⋆ R) m2) ?_ ?_
          · rintro J_l ⟨lim, ⟨⟩⟩ m2 hm2
            rw [Blocks.get_here]; c0_hsteps_nogrp
            let s3 : FullState := { s2 with scratch := { s2.scratch with
              rel_wait := lim, rel_u := 1#64, rel_v := 1#64, rel_trigger := 0#64 } }
            have hlen3 : s3.LengthsOk c := s11_len_scalars hlen
            have hps3 : FullProbeScratchPres s s3 := s11_probePres_refl s
            refine wp_loop_inv (ts := [i64, i64])
              (fun (hl, i, ()) mL => ∃ hp ps : List (BitVec 32),
                hp.length = c.max_vars ∧ ps.length = c.max_vars ∧
                hl.toNat ≤ i.toNat ∧ i.toNat ≤ s.core.cur_vars ∧
                (FullMem c { s3 with scratch :=
                  { s3.scratch with heap := hp, pos := ps } } ⋆ R) mL)
              (fun (_, i, ()) _ => s.core.cur_vars - i.toNat) ?_ ?_
            · intro J3 hJ3; c0_hsteps_nogrp
              exact hJ3 (0#64, 0#64, ()) _ ⟨s3.scratch.heap, s3.scratch.pos,
                hsok.heap_len_arr, hsok.pos_len, by simp, Nat.zero_le _, by assumption⟩
            · rintro J3 ⟨hl, i, ⟨⟩⟩ mL ⟨hp, ps, hhp, hps_len, hle_hi, hi_le, hmL⟩ hJ3
              rw [Blocks.get_here]; fs_nojnz
              fs_jnz hilt
              · simp only [BitVec.ult, decide_eq_true_eq] at hilt
                have hi_lt : i.toNat < s.core.cur_vars := by
                  change _ < s.core.cur_vars % 2 ^ 64 at hilt
                  rw [Nat.mod_eq_of_lt (by omega)] at hilt; exact hilt
                have hi_mx : i.toNat < c.max_vars := by omega
                refine wp_join_group (ts := [i64])
                  (fun (hl', ()) mN => ∃ hp' ps' : List (BitVec 32),
                    hp'.length = c.max_vars ∧ ps'.length = c.max_vars ∧
                    hl'.toNat ≤ i.toNat + 1 ∧
                    (FullMem c { s3 with scratch :=
                      { s3.scratch with heap := hp', pos := ps' } } ⋆ R) mN)
                  ?_ ?_
                · rintro J_nx ⟨hl', ⟨⟩⟩ mN ⟨hp', ps', hhp', hps', hle', hmN⟩
                  rw [Blocks.get_here]; c0_hsteps_nogrp
                  have hi1 : (i + 1#64).toNat = i.toNat + 1 := s11_bv64_add1 (by omega)
                  exact hJ3 (hl', i + 1#64, ()) mN (by dsimp only; rw [hi1]; omega)
                    ⟨hp', ps', hhp', hps', by rw [hi1]; exact hle', by omega, hmN⟩
                · intro J_nx hJ_nx
                  have hfl_lt : i.toNat < s3.core.flags.length := by rw [hok.flags_len]; omega
                  fs_nojnz
                  fs_jnz hact
                  · have hhp_lt : hl.toNat < hp.length := by omega
                    have hps_lt : i.toNat < ps.length := by omega
                    rw [wp_let_mul_eq]
                    simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val]
                    rw [wp_let_add_eq]
                    simp only [Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val]
                    c0_hsteps_nogrp
                    have hhl1 : (hl + 1#64).toNat = hl.toNat + 1 := s11_bv64_add1 (by omega)
                    exact hJ_nx (hl + 1#64, ()) _ ⟨hp.set hl.toNat (i.setWidth 32),
                      ps.set i.toNat (hl.setWidth 32), by simpa using hhp,
                      by simpa using hps_len, by omega, by assumption⟩
                  · have hps_lt : i.toNat < ps.length := by omega
                    c0_hsteps_nogrp
                    exact hJ_nx (hl, ()) _ ⟨hp, ps.set i.toNat 0xFFFFFFFF#32, hhp,
                      by simpa using hps_len, by omega, by assumption⟩
              · c0_hsteps_nogrp
                have hhl_le : hl.toNat ≤ c.max_vars := by omega
                let s4 : FullState := { s3 with scratch :=
                  { s3.scratch with heap := hp, pos := ps, heap_len := hl.toNat } }
                have hlen4 : s4.LengthsOk c :=
                  ⟨hlen3.core_ok, { hlen3.scratch_ok with heap_len_arr := hhp, pos_len := hps_len }⟩
                refine wp_loop_inv (ts := [i64])
                  (fun (k, ()) mD => ∃ sD : FullState,
                    sD.core = s.core ∧ sD.LengthsOk c ∧ FullProbeScratchPres s sD ∧
                    k.toNat ≤ c.max_vars ∧ (FullMem c sD ⋆ R) mD)
                  (fun (k, ()) _ => k.toNat) ?_ ?_
                · intro J4 hJ4; c0_hsteps_nogrp
                  exact hJ4 (hl >>> 1#64, ()) _ ⟨s4, rfl, hlen4, hps3,
                    le_trans (s11_bv64_lshr1_le hl) hhl_le, by assumption⟩
                · rintro J4 ⟨k, ⟨⟩⟩ mD ⟨sD, hcD, hlenD, hpsD, hk_le, hmD⟩ hJ4
                  rw [Blocks.get_here]; fs_nojnz
                  fs_jnz hkpos
                  · simp only [BitVec.ult, decide_eq_true_eq] at hkpos
                    have hk_gt : 0 < k.toNat := by simpa using hkpos
                    have hk1 : (k - 1#64).toNat = k.toNat - 1 :=
                      s11_bv64_sub1 (fun h => by simp [h] at hk_gt)
                    have hk1_hp : (k - 1#64).toNat < sD.scratch.heap.length := by
                      rw [hlenD.scratch_ok.heap_len_arr]; omega
                    c0_hsteps_nogrp
                    fs_call hHeapDown
                    refine ⟨c, sD, R, rfl, hlenD, hmD, fun () sD' mD' hcD' hlenD' hpost hmD' => ?_⟩
                    rcases hpost with ⟨_, hpsD'⟩
                    have hcD'_eq : sD'.core = sD.core := hcD'
                    exact hJ4 (k - 1#64, ()) mD' (by dsimp only; rw [hk1]; omega)
                      ⟨sD', hcD'_eq.trans hcD, hlenD', s11_probePres_trans hpsD hpsD',
                        by rw [hk1]; omega, hmD'⟩
                  · c0_hsteps_nogrp
                    exact hJs (0#64, 1#64, ()) mD ⟨sD, hcD, hlenD, hpsD,
                      by simp [hst0], by simp [hst0], fun _ => hle_confl,
                      fun hne => absurd hst0 hne, hmD⟩
          · intro J_l hJ_l; fs_nojnz
            fs_jnz hlim1
            · fs_nojnz
              fs_jnz hlim2 <;> c0_hsteps_nogrp <;> exact hJ_l _ _ (by assumption)
            · c0_hsteps_nogrp; exact hJ_l _ _ (by assumption)
        · intro J_d hJ_d; fs_nojnz
          fs_jnz hdiff <;> c0_hsteps_nogrp <;> exact hJ_d _ _ (by assumption)
    · simp only [beq_eq_false_iff_ne] at hst0
      fs_nojnz
      fs_jnz hticks
      · simp only [BitVec.ult, decide_eq_true_eq] at hticks
        c0_hsteps_nogrp
        exact hQ s m rfl hlen (s11_probePres_refl s) (fun _ => rfl)
          (fun ⟨h0, _⟩ => absurd h0 hst0)
          (fun ⟨_, hle⟩ => absurd (BitVec.le_def.mp hle) (Nat.not_le_of_gt hticks)) hm
      · simp only [BitVec.ult, decide_eq_false_iff_not] at hticks
        have hle_ticks : s.scratch.mode_tick_lim ≤ s.scratch.search_ticks :=
          BitVec.le_def.mpr (Nat.le_of_not_lt hticks)
        c0_hsteps_nogrp
        let s1 : FullState := { s with scratch := { s.scratch with stable := 0#64 } }
        refine wp_join_group (ts := [i64]) (fun _ m1 => (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro J_c ⟨cc, ⟨⟩⟩ m1 hm1
          rw [Blocks.get_here]; c0_hsteps_nogrp
          fs_call hLog10
          refine m7Log10Q16Spec_of fun r _ _ => ?_
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ m2 => (FullMem c s1 ⋆ R) m2) ?_ ?_
          · rintro J_d ⟨delta, ⟨⟩⟩ m2 hm2
            rw [Blocks.get_here]; c0_hsteps_nogrp
            let s4 : FullState := { s1 with scratch := { s1.scratch with
              mode_confl_lim := s1.scratch.conflicts + delta
              mode_saved_ticks := s1.scratch.search_ticks
              q_search_idx := s1.scratch.q_last } }
            refine wp_join_group (ts := [])
              (fun _ m5 => ∃ qss : BitVec 64,
                (FullMem c { s4 with scratch :=
                  { s4.scratch with q_search_stamp := qss } } ⋆ R) m5) ?_ ?_
            · rintro J_q ⟨⟩ m5 ⟨qss, hm5⟩
              rw [Blocks.get_here]; c0_hsteps_nogrp
              let sJ : FullState := { s4 with scratch :=
                { s4.scratch with q_search_stamp := qss } }
              have hlenJ : sJ.LengthsOk c := s11_len_scalars hlen
              exact hJs (1#64, 0#64, ()) m5 ⟨sJ, rfl, hlenJ, s11_probePres_refl s,
                by rw [ite_eq_right_iff.mpr fun h => absurd h (by simpa using hst0)],
                by rw [ite_eq_right_iff.mpr fun h => absurd h (by simpa using hst0)],
                fun h0 => absurd h0 hst0,
                fun _ => ⟨hle_ticks,
                  @M7GuPrefixPres.congr_glue s s s sJ rfl rfl (M7GuPrefixPres.refl s),
                  rfl, rfl, rfl, rfl, rfl⟩, hm5⟩
            · intro J_q hJ_q; fs_nojnz
              fs_jnz hqlt
              · simp only [BitVec.ult, decide_eq_true_eq] at hqlt
                have hq_nat : s.scratch.q_last.toNat < s.core.cur_vars := by
                  change _ < s.core.cur_vars % 2 ^ 64 at hqlt
                  rw [Nat.mod_eq_of_lt (by omega)] at hqlt; exact hqlt
                have hq_len : s.scratch.q_last.toNat < s.scratch.q_stamp.length := by
                  rw [hsok.q_stamp_len]; omega
                c0_hsteps_nogrp; exact hJ_q () _ ⟨_, by assumption⟩
              · c0_hsteps_nogrp; exact hJ_q () _ ⟨s4.scratch.q_search_stamp, by assumption⟩
          · intro J_d hJ_d; fs_nojnz
            fs_jnz hcle
            · c0_hsteps_nogrp; exact hJ_d _ _ (by assumption)
            · c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun _ mx => (FullMem c s1 ⋆ R) mx) ?_ ?_
              · rintro J_x ⟨cv, ⟨⟩⟩ mx hmx2
                rw [Blocks.get_here]; c0_hsteps_nogrp; exact hJ_d _ _ hmx2
              · intro J_x hJ_x; fs_nojnz
                fs_jnz hcgt <;> c0_hsteps_nogrp <;> exact hJ_x _ _ (by assumption)
        · intro J_c hJ_c; fs_nojnz
          fs_jnz hcc <;> c0_hsteps_nogrp <;> exact hJ_c _ _ (by assumption)

end SwitchModeStep11Helpers

end LeanQbe.T.Examples.Kissat.FullFidelityStep11

end
