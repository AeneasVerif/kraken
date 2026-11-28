/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Top-Level Driver WP Proof for `Src.Factor` (`full_factor`)

Proves `full_factor_wp` (`fullFactorHeapSpec`) parametrically in `Γ` (`0` legacy imports,
`0` placeholders, `XPost`-polymorphic) using explicit `Γ.Has` callee hypotheses for
`full_bva_steps_cap_fid`, `full_bva_connect_clauses_fid`, `full_fheap_up_fid`,
`full_fheap_down_fid`, `full_bva_try_lit`, and `full_bva_upd_lit_fid`.
-/

set_option autoImplicit false

local elab "c0_hstraight" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps
    { splitJnz := false, unrollGroup := false, pruneJnz := false } 10000

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

namespace LeanQbe.T.Examples.Kissat.Proof.Factor

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Factor
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics

/-! ## 1. Fheap & Core State Framing Helpers -/

private def S13FheapRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreByteArrs c s.core ⋆
  FullCoreU32A c s.core ⋆ array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
  array (t := i32) c.pFrameDec s.core.frame_dec ⋆ array (t := i32) c.pMinStk s.core.min_stk ⋆
  array (t := i32) c.pWvec s.core.wvec ⋆ FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
  array (t := i32) c.pWsort s.scratch.wsort ⋆ array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
  array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
  FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad

private theorem s13_focus_fheap {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
      array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
      array (t := i32) c.pRepr s.core.repr ⋆ (S13FheapRest c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrWksArrs at hm
  unfold S13FheapRest; exact sep_ac hm

private theorem s13_unfocus_fheap {c : FullCfg} {s : FullState} {hp' ps' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pTarjanMark hp' ⋆ array (t := i32) c.pTarjanReach ps' ⋆
      array (t := i32) c.pRepr s.core.repr ⋆ (S13FheapRest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } ⋆
      R) m := by
  unfold S13FheapRest at hm
  unfold FullMem FullCoreArrays FullCoreU32B FullScratchArrays FullScrWksArrs; exact sep_ac hm

private theorem s13_dense_set_fheap {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {hp' ps' : List (BitVec 32)}
    (hhp : hp'.length = 2 * c.max_vars) (hps : ps'.length = 2 * c.max_vars) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with tarjan_mark := hp', tarjan_reach := ps' } } :=
  hinv.of_safetySlice
    ⟨hinv.1.lengths.core_ok,
      { hinv.1.lengths.scratch_ok with tarjan_mark_len := hhp, tarjan_reach_len := hps }⟩
    rfl ⟨rfl, rfl⟩

private theorem s13_dense_set_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨F_cur, hw⟩ := hinv.1.witness
  have hw' : FullWitnessInv c F0 F_cur { s.core with flags := fl' } :=
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨⟨⟨{ hinv.1.lengths.core_ok with flags_len := hfl }, hinv.1.lengths.scratch_ok⟩,
    F_cur, hw'⟩, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩

private def s13SetLmWs2 (s : FullState) (tmk : List (BitVec 8))
    (tlits : List (BitVec 32)) : FullState :=
  { s with core := { s.core with lit_mark := tmk }
           scratch := { s.scratch with work_stk2 := tlits } }

private theorem s13_dense_set_lm_ws2 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullDenseInv c F0 s) {tmk : List (BitVec 8)} {tlits : List (BitVec 32)}
    (hlm : tmk.length = 2 * c.max_vars) (hws2 : tlits.length = 2 * c.max_vars)
    (hzero : ∀ l < 2 * c.max_vars, tmk[l]?.getD 0#8 = 0#8) :
    FullDenseInv c F0 (s13SetLmWs2 s tmk tlits) := by
  obtain ⟨F_cur, hw⟩ := hinv.1.witness
  have hw' : FullWitnessInv c F0 F_cur (s13SetLmWs2 s tmk tlits).core :=
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨⟨⟨{ hinv.1.lengths.core_ok with lit_mark_len := hlm },
      { hinv.1.lengths.scratch_ok with work_stk2_len := hws2 }⟩, F_cur, hw'⟩,
    ⟨hinv.2.1.1, hzero⟩, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩

private def S13HeapFr (s st : FullState) : Prop :=
  ∃ rp hp ps, st = { s with core := { s.core with repr := rp }
                            scratch := { s.scratch with tarjan_mark := hp, tarjan_reach := ps } }

private theorem s13HeapFr_refl (s : FullState) : S13HeapFr s s := ⟨_, _, _, rfl⟩
private theorem s13HeapFr_cur_vars {s st : FullState} (h : S13HeapFr s st) :
    st.core.cur_vars = s.core.cur_vars := by obtain ⟨_, _, _, rfl⟩ := h; rfl
private theorem s13HeapFr_fuel {s st : FullState} (h : S13HeapFr s st) :
    st.core.fuel = s.core.fuel := by obtain ⟨_, _, _, rfl⟩ := h; rfl
private theorem s13HeapFr_work_stk2 {s st : FullState} (h : S13HeapFr s st) :
    st.scratch.work_stk2 = s.scratch.work_stk2 := by obtain ⟨_, _, _, rfl⟩ := h; rfl

private def S13UpdInv (c : FullCfg) (F0 : CNF Nat) (s0 : FullState) (R : Mem 64 → Prop)
    (hsz : BitVec 32) (m : Mem 64) : Prop :=
  ∃ st, FullDenseInv c F0 st ∧ S13HeapFr s0 st ∧ hsz.toNat ≤ 2 * s0.core.cur_vars ∧
    (∀ i < hsz.toNat, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
    (FullMem c st ⋆ R) m

private def S13TouchInv (c : FullCfg) (st3 : FullState) (R : Mem 64 → Prop)
    (nt : BitVec 64) (tmk : List (BitVec 8)) (tlits : List (BitVec 32)) (m : Mem 64) : Prop :=
  tmk.length = 2 * c.max_vars ∧ tlits.length = 2 * c.max_vars ∧
  nt.toNat ≤ 2 * st3.core.cur_vars ∧
  (∀ i < nt.toNat, (tlits[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars) ∧
  (∀ l < 2 * c.max_vars, tmk[l]?.getD 0#8 ≠ 0#8 →
    ∃ k < nt.toNat, (tlits[k]?.getD 0#32).toNat = l) ∧
  (FullMem c (s13SetLmWs2 st3 tmk tlits) ⋆ R) m

private abbrev facZeroSt (s : FullState) (ws hp ps : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with wsort := ws, tarjan_mark := hp, tarjan_reach := ps } }

/-! ## 2. Arithmetic, Callee & Touched-Literal Deduplication Helpers -/

private theorem fac13_lex_dec_cv {maxv cv1 cv2 h1 h2 : Nat}
    (hcv_lt : cv1 < cv2) (hcv2_le : cv2 ≤ maxv) (hh2 : h2 ≤ 2 * maxv) :
    (maxv - cv2) * (2 * maxv + 1) + h2 < (maxv - cv1) * (2 * maxv + 1) + h1 := by
  have hmul : (maxv - cv2 + 1) * (2 * maxv + 1) ≤ (maxv - cv1) * (2 * maxv + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_one_mul] at hmul; omega

private theorem fac13_push_pre_lt {hp : List (BitVec 32)} {hlen : Nat} {lit : BitVec 32}
    {lim : Nat} (hlt : lit.toNat < lim) (hhl_lt : hlen < hp.length)
    (hprev : ∀ k < hlen, (hp[k]?.getD 0#32).toNat < lim) :
    ∀ i ≤ hlen, ((hp.set hlen lit)[i]?.getD 0#32).toNat < lim := by
  intro i hi
  by_cases heq : i = hlen
  · subst heq; rw [List.getElem?_set_self hhl_lt, Option.getD_some]; exact hlt
  · rw [List.getElem?_set_ne (Ne.symm heq)]; exact hprev i (Nat.lt_of_le_of_ne hi heq)

private theorem s13_lengths_set_ant_sz {c : FullCfg} {sc : FullScratch}
    (h : sc.LengthsOk c) (b : BitVec 64) : ({ sc with ant_sz := b } : FullScratch).LengthsOk c :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15, h.16, h.17,
   h.18, h.19, h.20, h.21, h.22, h.23, h.24⟩

private theorem fac13_bv32_shl1_or1 (x : BitVec 64) (hx : x.toNat < 2 ^ 30) :
    (BitVec.setWidth 32 (x <<< (1 : Nat)) ||| 1#32).toNat = 2 * x.toNat + 1 := by
  have h1 : (BitVec.setWidth 32 (x <<< (1 : Nat))).toNat = 2 * x.toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 1 < 2 ^ 32)]; omega
  rw [BitVec.toNat_or, h1, show (1#32 : BitVec 32).toNat = 1 from rfl]
  apply Nat.eq_of_testBit_eq; intro k; cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
      show 1 / 2 = 0 from rfl, show (2 * x.toNat) / 2 = x.toNat from by omega,
      show (2 * x.toNat + 1) / 2 = x.toNat from by omega, Nat.zero_testBit, Bool.or_false]

private theorem fac13_bv32_xor1_lt {fv : BitVec 32} {lim : Nat} (h : fv.toNat < lim)
    (heven : lim % 2 = 0) : (fv ^^^ 1#32).toNat < lim := by
  rw [FidK6Tactics.fid_bv32_xor1_lit]; omega

private theorem s13_call_steps_cap {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSteps : Γ.Has "full_bva_steps_cap_fid" fidBvaStepsCapSpec)
    {c : FullCfg} {m : Mem 64} {k : Tup Val [i32] → Expr Val Cont rs}
    (hk : ∀ scb : BitVec 32, scb.toNat = fidStepsCap c.scratch_cap →
      wp Γ Q X (k (scb, ())) m) :
    wp Γ Q X (Expr.call (as := [i64]) "full_bva_steps_cap_fid"
      (Arg.var (BitVec.ofNat 64 c.scratch_cap), ()) k) m := by
  refine wp_call_of_spec _ _ (hSteps _ _ _ _ (hk _ ?_))
  have h1 := c.hscr; unfold dimacsBound at h1; have h2 := fidStepsCap_le_256 c.scratch_cap
  change (BitVec.ofNat 32 (fidStepsCap (BitVec.ofNat 64 c.scratch_cap).toNat)).toNat = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := c.scratch_cap) (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem s13_call_fheap_up {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hUp : Γ.Has "full_fheap_up_fid" fidFheapUpSpec)
    {c : FullCfg} {F0 : CNF Nat} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {idx : BitVec 32} {k : Tup Val [] → Expr Val Cont rs} {hlen_chk : Nat}
    (hinv : FullDenseInv c F0 st) (hidx_lt : idx.toNat < hlen_chk)
    (hhlen_le : hlen_chk ≤ 2 * st.core.cur_vars)
    (hhpp : ∀ i < hlen_chk, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ st' m', FullDenseInv c F0 st' → st'.core = st.core →
      (∀ i < hlen_chk, (st'.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i32]) "full_fheap_up_fid"
      (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr, Arg.var idx, ()) k) m := by
  have hcv_le := hinv.1.lengths.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx; have hlen := hinv.1.lengths
  refine wp_call_of_spec _ _ (hUp _ _ _ _ ?_)
  refine ⟨2 * st.core.cur_vars, st.scratch.tarjan_mark, st.scratch.tarjan_reach, st.core.repr,
    S13FheapRest c st ⋆ R, by rw [hlen.scratch_ok.tarjan_mark_len]; omega,
    by rw [hlen.scratch_ok.tarjan_reach_len]; omega, by rw [hlen.core_ok.repr_len]; omega,
    by omega, Nat.lt_of_lt_of_le hidx_lt hhlen_le,
    (fun i hi => hhpp i (Nat.lt_of_le_of_lt (by simpa using hi) hidx_lt)),
    s13_focus_fheap hm, fun hp' ps' m' hhp' hps' hsub hrest hm' => ?_⟩
  refine hk _ m' (s13_dense_set_fheap hinv (hhp'.trans hlen.scratch_ok.tarjan_mark_len)
    (hps'.trans hlen.scratch_ok.tarjan_reach_len)) rfl (fun i hi => ?_) (s13_unfocus_fheap hm')
  by_cases hle : i ≤ idx.toNat
  · obtain ⟨j, hj, hget⟩ := hsub i (by simpa using hle)
    rw [hget]; exact hhpp j (Nat.lt_of_le_of_lt (by simpa using hj) hidx_lt)
  · rw [hrest i (by simpa using Nat.lt_of_not_ge hle)]; exact hhpp i hi

private theorem s13_call_fheap_down {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hDown : Γ.Has "full_fheap_down_fid" fidFheapDownSpec)
    {c : FullCfg} {F0 : CNF Nat} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {idx n : BitVec 32} {k : Tup Val [] → Expr Val Cont rs}
    (hinv : FullDenseInv c F0 st) (hidx_lt : idx.toNat < n.toNat)
    (hn_le : n.toNat ≤ 2 * st.core.cur_vars)
    (hhpp : ∀ i < n.toNat, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ st' m', FullDenseInv c F0 st' → st'.core = st.core →
      (∀ i < n.toNat, (st'.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i32, i32]) "full_fheap_down_fid"
      (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr,
       Arg.var idx, Arg.var n, ()) k) m := by
  have hcv_le := hinv.1.lengths.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx; have hlen := hinv.1.lengths
  refine wp_call_of_spec _ _ (hDown _ _ _ _ ?_)
  refine ⟨2 * st.core.cur_vars, st.scratch.tarjan_mark, st.scratch.tarjan_reach, st.core.repr,
    S13FheapRest c st ⋆ R, by rw [hlen.scratch_ok.tarjan_mark_len]; omega,
    by rw [hlen.scratch_ok.tarjan_reach_len]; omega, by rw [hlen.core_ok.repr_len]; omega,
    by omega, hidx_lt, hn_le, (fun i hi => hhpp i (by simpa using hi)),
    s13_focus_fheap hm, fun hp' ps' m' hhp' hps' hsub _ hm' => ?_⟩
  refine hk _ m' (s13_dense_set_fheap hinv (hhp'.trans hlen.scratch_ok.tarjan_mark_len)
    (hps'.trans hlen.scratch_ok.tarjan_reach_len)) rfl (fun i hi => ?_) (s13_unfocus_fheap hm')
  obtain ⟨j, hj, hget⟩ := hsub i (by simpa using hi); rw [hget]; exact hhpp j (by simpa using hj)

private theorem s13_call_upd_lit {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hUpd : Γ.Has "full_bva_upd_lit_fid" step9BvaUpdLitSpec)
    {c : FullCfg} {F0 : CNF Nat} {s0 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {hsz : BitVec 32} {cur_nl : BitVec 64} {tl : BitVec 32}
    {k : Tup Val [i32] → Expr Val Cont rs}
    (hnl : cur_nl.toNat = 2 * s0.core.cur_vars) (htl : tl.toNat < 2 * s0.core.cur_vars)
    (hI : S13UpdInv c F0 s0 R hsz m)
    (hk : ∀ hsz' m', S13UpdInv c F0 s0 R hsz' m' → wp Γ Q X (k (hsz', ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i64, i64, i64, i64]) (bs := [i32])
      "full_bva_upd_lit_fid"
      (Arg.var c.hdr, Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr,
       Arg.var cur_nl,
       Arg.var ((BitVec.setWidth 64 hsz <<< (32 : Nat)) ||| BitVec.setWidth 64 tl), ()) k) m := by
  obtain ⟨st, hinv, hfr, hle, hhp, hm⟩ := hI
  have hcv := s13HeapFr_cur_vars hfr
  refine wp_call_of_spec _ _ (hUpd _ _ _ _ ?_)
  refine ⟨c, F0, st, R, hsz, tl, rfl, rfl, rfl, rfl, rfl, hinv, by rw [hcv]; exact hnl,
    by rw [hcv]; exact htl, by rw [hcv]; exact hle, fun i hi => by rw [hcv]; exact hhp i hi,
    hm, fun hsz' rp hp ps m' hinv' hle' hhp' hm' => ?_⟩
  obtain ⟨_, _, _, rfl⟩ := hfr
  exact hk hsz' m' ⟨_, hinv', ⟨rp, hp, ps, rfl⟩, by rw [← hcv]; exact hle',
    fun i hi => by rw [← hcv]; exact hhp' i hi, hm'⟩

private theorem s13_push_touched_step {c : FullCfg} {st3 : FullState}
    (hcv_le : st3.core.cur_vars ≤ c.max_vars)
    {nt : BitVec 64} {tmk : List (BitVec 8)} {tlits : List (BitVec 32)} {x : BitVec 32}
    (htmk_len : tmk.length = 2 * c.max_vars) (htlits_len : tlits.length = 2 * c.max_vars)
    (hx_lt : x.toNat < 2 * st3.core.cur_vars) (hnt_lt : nt.toNat < 2 * st3.core.cur_vars)
    (hnt1 : (nt + 1#64).toNat = nt.toNat + 1)
    (htlits_b : ∀ i < nt.toNat, (tlits[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars)
    (hcov : ∀ l < 2 * c.max_vars, tmk[l]?.getD 0#8 ≠ 0#8 →
      ∃ k < nt.toNat, (tlits[k]?.getD 0#32).toNat = l) :
    let tmk' := tmk.set (BitVec.setWidth 64 x).toNat 1#8
    let tlits' := tlits.set nt.toNat x
    tmk'.length = 2 * c.max_vars ∧ tlits'.length = 2 * c.max_vars ∧
    (nt + 1#64).toNat ≤ 2 * st3.core.cur_vars ∧
    (∀ i < (nt + 1#64).toNat, (tlits'[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars) ∧
    (∀ l < 2 * c.max_vars, tmk'[l]?.getD 0#8 ≠ 0#8 →
      ∃ k < (nt + 1#64).toNat, (tlits'[k]?.getD 0#32).toNat = l) := by
  intro tmk' tlits'
  have hx64 : (BitVec.setWidth 64 x).toNat = x.toNat := fid_bv64_32 x
  have htlits_nt : nt.toNat < tlits.length := by rw [htlits_len]; omega
  refine ⟨by simp [tmk', htmk_len], by simp [tlits', htlits_len], by rw [hnt1]; omega,
    fun i hi => ?_, fun l hl hnz => ?_⟩
  · rw [hnt1] at hi
    by_cases heq : i = nt.toNat
    · subst heq; simp only [tlits', List.getElem?_set_self htlits_nt, Option.getD_some]; exact hx_lt
    · simp only [tlits', List.getElem?_set_ne (Ne.symm heq)]; exact htlits_b i (by omega)
  · by_cases hlx : l = x.toNat
    · refine ⟨nt.toNat, by rw [hnt1]; omega, ?_⟩
      simp only [tlits', List.getElem?_set_self htlits_nt, Option.getD_some, hlx]
    · have hne : (BitVec.setWidth 64 x).toNat ≠ l := by rw [hx64]; exact Ne.symm hlx
      have hpre : tmk[l]?.getD 0#8 ≠ 0#8 := by
        dsimp only [tmk'] at hnz; rwa [List.getElem?_set_ne hne] at hnz
      obtain ⟨k, hk, hkl⟩ := hcov l hl hpre
      refine ⟨k, by rw [hnt1]; omega, ?_⟩
      simp only [tlits', List.getElem?_set_ne (by omega : nt.toNat ≠ k), hkl]

private theorem s13_clear_step {c : FullCfg} {st3 : FullState}
    (hcv_le : st3.core.cur_vars ≤ c.max_vars)
    {ui nt : BitVec 64} {tmk : List (BitVec 8)} {tlits : List (BitVec 32)}
    (htmk_len : tmk.length = 2 * c.max_vars)
    (htlits_b : ∀ i < nt.toNat, (tlits[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars)
    (hui_lt : ui.toNat < nt.toNat) (hui1 : (ui + 1#64).toNat = ui.toNat + 1)
    (hcov : ∀ l < 2 * c.max_vars, tmk[l]?.getD 0#8 ≠ 0#8 →
      ∃ k, ui.toNat ≤ k ∧ k < nt.toNat ∧ (tlits[k]?.getD 0#32).toNat = l) :
    ∀ l < 2 * c.max_vars,
      (tmk.set (BitVec.setWidth 64 (tlits[ui.toNat]?.getD 0#32)).toNat 0#8)[l]?.getD 0#8 ≠ 0#8 →
      ∃ k, (ui + 1#64).toNat ≤ k ∧ k < nt.toNat ∧ (tlits[k]?.getD 0#32).toNat = l := by
  intro l hl hnz
  have hx64 : (BitVec.setWidth 64 (tlits[ui.toNat]?.getD 0#32)).toNat =
      (tlits[ui.toNat]?.getD 0#32).toNat := fid_bv64_32 _
  have hlen : (BitVec.setWidth 64 (tlits[ui.toNat]?.getD 0#32)).toNat < tmk.length := by
    have := htlits_b ui.toNat hui_lt; rw [hx64, htmk_len]; omega
  by_cases hlx : l = (tlits[ui.toNat]?.getD 0#32).toNat
  · exfalso
    have heq : (tmk.set (BitVec.setWidth 64 (tlits[ui.toNat]?.getD 0#32)).toNat 0#8)[l]?.getD
        0#8 = 0#8 := by
      have hidx : (BitVec.setWidth 64 (tlits[ui.toNat]?.getD 0#32)).toNat = l := by rw [hx64, hlx]
      rw [hidx] at hlen ⊢; rw [List.getElem?_set_self hlen, Option.getD_some]
    exact hnz heq
  · have hne : (BitVec.setWidth 64 (tlits[ui.toNat]?.getD 0#32)).toNat ≠ l := by
      rw [hx64]; exact Ne.symm hlx
    obtain ⟨k, hk1, hk2, hkl⟩ := hcov l hl (by rwa [List.getElem?_set_ne hne] at hnz)
    refine ⟨k, ?_, hk2, hkl⟩; rw [hui1]
    by_cases hku : k = ui.toNat
    · subst hku; exact absurd hkl.symm hlx
    · omega

/-! ## 3. Subtree AST Extractors & Helper WP Proofs -/

private abbrev cIdx4 (ptr idx : Val i64) (k : Val i64 → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (.mul i64) (Arg.var idx, Arg.imm 4, ())) fun p1 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var ptr, Arg.var p1.fst, ())) fun p2 => k p2.fst

private abbrev cZextIdx4 (ptr : Val i64) (idx : Val i32) (k : Val i64 → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (.zext 32 64) (Arg.var idx, ())) fun p0 => cIdx4 ptr p0.fst k

private abbrev cCmpUlt32 (a b : Val i32) (k : Val .bool → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var a, Arg.var b, ())) fun p => k p.fst

private def s13FacZeroExpr (c : FullCfg) (max_nlits64 : Val i64)
    (afterZero : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64]])
    (fun Js => Blocks.cons (fun p =>
      Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p.fst, Arg.var max_nlits64, ())) fun p1 =>
      Expr.jnz (Arg.var p1.fst)
        (cIdx4 c.pWsort p.fst fun p3 =>
        Expr.store (t := i32) (Arg.imm 0) (Arg.var p3)
          (cIdx4 c.pTarjanMark p.fst fun p5 =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p5)
            (cIdx4 c.pTarjanReach p.fst fun p7 =>
            Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p7)
              (Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
              Expr.jump Js.fst (Arg.var p.fst, ())))))
        afterZero) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private def facBuildPushExpr (c : FullCfg) (v64 : Val i64) (hsz lit : Val i32)
    (mask : Int) (J : Cont [i32]) : Expr Val Cont [i64] :=
  cIdx4 c.pFlags v64 fun p2 =>
  Expr.load i32 (Arg.var p2) fun ld =>
  Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm mask, ())) fun p3 =>
  Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var p3.fst, Arg.imm 0, ())) fun p4 =>
  Expr.jnz (Arg.var p4.fst)
    (cZextIdx4 c.pRepr lit fun p7 =>
    Expr.load i32 (Arg.var p7) fun ld =>
    Expr.let_ (Op.mk (.cmp .ugt i32 .bool rfl) (Arg.var ld, Arg.imm 1, ())) fun p8 =>
    Expr.jnz (Arg.var p8.fst)
      (cZextIdx4 c.pTarjanMark hsz fun p11 =>
      Expr.store (Arg.var lit) (Arg.var p11)
        (cZextIdx4 c.pTarjanReach lit fun p14 =>
        Expr.store (Arg.var hsz) (Arg.var p14)
          (Expr.call (as := [i64, i64, i64, i32]) (bs := []) "full_fheap_up_fid"
            (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr, Arg.var hsz, ())
            fun _ =>
            Expr.let_ (Op.mk (.add i32) (Arg.var hsz, Arg.imm 1, ())) fun p =>
            Expr.jump J (Arg.var p.fst, ()))))
      (Expr.jump J (Arg.var hsz, ())))
    (Expr.jump J (Arg.var hsz, ()))

private def s13FacBuildExpr (c : FullCfg) (cv1 : Nat)
    (K : Tup Val [i32, i64] → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i32, i64]]) (fun Js => Blocks.cons (fun p =>
    Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
        (Arg.var p.snd.fst, Arg.var (BitVec.ofNat 64 cv1), ())) fun p2 =>
    Expr.jnz (Arg.var p2.fst)
      (Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p3 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p =>
          Expr.jump Js.fst (Arg.var p3.fst, Arg.var p.fst, ())) Blocks.nil)
        fun Js =>
        cIdx4 c.pFlags p.snd.fst fun p4 => Expr.load i32 (Arg.var p4) fun ld =>
        Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 1, ())) fun p5 =>
        Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var p5.fst, Arg.imm 0, ())) fun p6 =>
        Expr.jnz (Arg.var p6.fst)
          (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun p7 =>
          Expr.let_ (Op.mk (.shl i64) (Arg.var p.snd.fst, Arg.var p7.fst, ())) fun p8 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.pVals, Arg.var p8.fst, ())) fun p9 =>
          Expr.load i8 (Arg.var p9.fst) fun ld =>
          Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p10 =>
          Expr.let_ (Op.mk (.sext 8 32) (Arg.var ld, ())) fun p11 =>
          Expr.let_ (Op.mk (.sext 8 32) (Arg.var p10.fst, ())) fun p12 =>
          Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var p11.fst, Arg.var p12.fst, ()))
            fun p13 =>
          Expr.jnz (Arg.var p13.fst)
            (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun p14 =>
            Expr.let_ (Op.mk (.shl i64) (Arg.var p.snd.fst, Arg.var p14.fst, ())) fun p15 =>
            Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p15.fst, ())) fun p16 =>
            Expr.let_ (Op.mk (.or i32) (Arg.var p16.fst, Arg.imm 1, ())) fun p17 =>
            Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p18 =>
                Expr.group (sig := [[i32]])
                  (fun _ => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ()))
                    Blocks.nil)
                  fun Js => facBuildPushExpr c p.snd.fst p18.fst p17.fst 64 Js.fst) Blocks.nil)
              fun Js => facBuildPushExpr c p.snd.fst p.fst p16.fst 32 Js.fst)
            (Expr.jump Js.fst (Arg.var p.fst, ())))
          (Expr.jump Js.fst (Arg.var p.fst, ())))
      (K p)) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ())

private def s13FacFheapPopExpr (c : FullCfg) (hsz : BitVec 32) (J : Cont []) :
    Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (.cmp .ugt i32 .bool rfl) (Arg.var (hsz - 1#32), Arg.imm 0, ())) fun p =>
  Expr.jnz (Arg.var p.fst)
    (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 0, ())) fun p =>
    cIdx4 c.pTarjanMark p.fst fun p =>
    cZextIdx4 c.pTarjanMark (hsz - 1#32) fun p3 =>
    Expr.load i32 (Arg.var p3) fun ld =>
    Expr.store (Arg.var ld) (Arg.var p)
      (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 0, ())) fun p =>
      cIdx4 c.pTarjanMark p.fst fun p =>
      Expr.load i32 (Arg.var p) fun ld =>
      cZextIdx4 c.pTarjanReach ld fun p =>
      Expr.store (t := i32) (Arg.imm 0) (Arg.var p)
        (Expr.call (as := [i64, i64, i64, i32, i32]) (bs := []) "full_fheap_down_fid"
          (Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr,
           Arg.imm 0, Arg.var (hsz - 1#32), ())
          fun _ => Expr.jump J ())))
    (Expr.jump J ())

private def facPushTouchedExpr (c : FullCfg) (nl64 : Val i64) (lit : Val i32)
    (nt : Val i64) (J : Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (.zext 32 64) (Arg.var lit, ())) fun p1 =>
  Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p1.fst, Arg.var nl64, ())) fun p2 =>
  Expr.jnz (Arg.var p2.fst)
    (Expr.let_ (Op.mk (.zext 32 64) (Arg.var lit, ())) fun p3 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var c.pLitMark, Arg.var p3.fst, ())) fun p4 =>
    Expr.load i8 (Arg.var p4.fst) fun ld =>
    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p5 =>
    Expr.let_ (Op.mk (.zext 8 32) (Arg.var ld, ())) fun p6 =>
    Expr.let_ (Op.mk (.zext 8 32) (Arg.var p5.fst, ())) fun p7 =>
    Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var p6.fst, Arg.var p7.fst, ())) fun p8 =>
    Expr.jnz (Arg.var p8.fst)
      (Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var nt, Arg.var nl64, ())) fun p9 =>
      Expr.jnz (Arg.var p9.fst)
        (Expr.let_ (Op.mk (.zext 32 64) (Arg.var lit, ())) fun p10 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var c.pLitMark, Arg.var p10.fst, ())) fun p11 =>
        Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 1, ())) fun p12 =>
        Expr.store (Arg.var p12.fst) (Arg.var p11.fst)
          (cIdx4 c.pWorkStk2 nt fun p14 => Expr.store (Arg.var lit) (Arg.var p14)
            (Expr.let_ (Op.mk (.add i64) (Arg.var nt, Arg.imm 1, ())) fun p =>
            Expr.jump J (Arg.var p.fst, ()))))
        (Expr.jump J (Arg.var nt, ())))
      (Expr.jump J (Arg.var nt, ())))
    (Expr.jump J (Arg.var nt, ()))

private def s13FacQiScanExpr (c : FullCfg) (qn_bv ro_bv : BitVec 32) (nl64 : BitVec 64)
    (fac_lit qs_dec : BitVec 32) (nt2 : BitVec 64) (Ja : Cont [i64, i32]) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i32]]) (fun Js => Blocks.cons (fun p =>
    cCmpUlt32 p.snd.fst qn_bv fun p1 =>
    Expr.jnz (Arg.var p1)
      (Expr.let_ (Op.mk (.add i32) (Arg.var ro_bv, Arg.var p.snd.fst, ())) fun p2 =>
      cZextIdx4 c.pScratchBuf p2.fst fun p5 => Expr.load i32 (Arg.var p5) fun ld =>
      Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p6 =>
          Expr.let_ (Op.mk (.add i32) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p =>
          Expr.jump Js.fst (Arg.var p6.fst, Arg.var p.fst, ())) Blocks.nil)
        fun Js =>
        Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 2147483648, ())) fun p6 =>
        Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var p6.fst, Arg.imm 0, ())) fun p7 =>
        Expr.jnz (Arg.var p7.fst)
          (Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 2147483647, ())) fun p8 =>
          Expr.group (sig := [[i64]])
            (fun _ => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil)
            fun Js => facPushTouchedExpr c nl64 p8.fst p.fst Js.fst)
          (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p8 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p8.fst, Arg.imm 2, ())) fun p9 =>
          cIdx4 c.pArena p9.fst fun p11 => Expr.load i32 (Arg.var p11) fun ld1 =>
          Expr.group (sig := [[i64, i32]]) (fun Js1 => Blocks.cons (fun p =>
              cCmpUlt32 p.snd.fst ld1 fun p12 =>
              Expr.jnz (Arg.var p12)
                (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p13 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var p13.fst, Arg.imm 3, ())) fun p14 =>
                Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.snd.fst, ())) fun p15 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var p14.fst, Arg.var p15.fst, ())) fun p16 =>
                cIdx4 c.pArena p16.fst fun p18 => Expr.load i32 (Arg.var p18) fun ld =>
                Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p19 =>
                    Expr.let_ (Op.mk (.add i32) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p =>
                    Expr.jump Js1.fst (Arg.var p19.fst, Arg.var p.fst, ())) Blocks.nil)
                  fun Js =>
                  Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var ld, Arg.var fac_lit, ()))
                    fun p19 =>
                  Expr.jnz (Arg.var p19.fst)
                    (facPushTouchedExpr c nl64 ld p.fst Js.fst)
                    (Expr.jump Js.fst (Arg.var p.fst, ())))
                (Expr.jump Js.fst (Arg.var p.fst, ()))) Blocks.nil)
            fun Js => Expr.jump Js.fst (Arg.var p.fst, Arg.imm 0, ())))
      (Expr.jump Ja (Arg.var p.fst, Arg.var qs_dec, ()))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.var nt2, Arg.imm 0, ())

private def s13FacClearUpdExpr (c : FullCfg) (st3 : FullState) (nt : BitVec 64)
    (hsz' : BitVec 32) (Js : Cont [i32]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64]]) (fun Jsc => Blocks.cons (fun p =>
    Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p.fst, Arg.var nt, ())) fun p1 =>
    Expr.jnz (Arg.var p1.fst)
      (cIdx4 c.pWorkStk2 p.fst fun p3 => Expr.load i32 (Arg.var p3) fun ld =>
      Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p4 =>
      Expr.let_ (Op.mk (.add i64) (Arg.var c.pLitMark, Arg.var p4.fst, ())) fun p5 =>
      Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun p6 =>
      Expr.store (Arg.var p6.fst) (Arg.var p5.fst)
        (Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
        Expr.jump Jsc.fst (Arg.var p.fst, ())))
      (Expr.group (sig := [[i32, i64]]) (fun Jsu => Blocks.cons (fun p =>
          Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p.snd.fst, Arg.var nt, ())) fun p2 =>
          Expr.jnz (Arg.var p2.fst)
            (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.fst, ())) fun p3 =>
            Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 32, ())) fun p4 =>
            Expr.let_ (Op.mk (.shl i64) (Arg.var p3.fst, Arg.var p4.fst, ())) fun p5 =>
            cIdx4 c.pWorkStk2 p.snd.fst fun p7 => Expr.load i32 (Arg.var p7) fun ld =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p8 =>
            Expr.let_ (Op.mk (.or i64) (Arg.var p5.fst, Arg.var p8.fst, ())) fun p9 =>
            Expr.call (as := [i64, i64, i64, i64, i64, i64]) (bs := [i32]) "full_bva_upd_lit_fid"
              (Arg.var c.hdr, Arg.var c.pTarjanMark, Arg.var c.pTarjanReach, Arg.var c.pRepr,
               Arg.var (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)), Arg.var p9.fst, ())
              fun p10 => Expr.let_ (Op.mk (.add i64) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p =>
              Expr.jump Jsu.fst (Arg.var p10.fst, Arg.var p.fst, ()))
            (Expr.jump Js (Arg.var p.fst, ()))) Blocks.nil)
        fun Jsu => Expr.jump Jsu.fst (Arg.var hsz', Arg.imm 0, ()))) Blocks.nil)
    fun Jsc => Expr.jump Jsc.fst (Arg.imm 0, ())

private def s13FacExitExpr (c : FullCfg) (st : FullState) (init_cv : Nat) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun (p : Tup Val [i64]) =>
    Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
        (Arg.var p.fst, Arg.var (BitVec.ofNat 64 st.core.cur_vars <<< (1 : Nat)), ())) fun p1 =>
    Expr.jnz (Arg.var p1.fst)
      (cIdx4 c.pTarjanMark p.fst fun p3 => Expr.store (t := i32) (Arg.imm 0) (Arg.var p3)
        (cIdx4 c.pTarjanReach p.fst fun p5 => Expr.store (t := i32) (Arg.imm 0) (Arg.var p5)
          (Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p6 =>
          Expr.jump Js.fst (Arg.var p6.fst, ()))))
      (Expr.group (sig := [[]])
        (fun _ => Blocks.cons (fun (_ : Tup Val []) => Expr.ret (Arg.imm (t := i64) 1, ()))
          Blocks.nil)
        fun Js_ret =>
        Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p2 =>
        Expr.load i64 (Arg.var p2.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl)
            (Arg.var ld, Arg.var (BitVec.ofNat 64 init_cv), ())) fun p3 =>
        Expr.jnz (Arg.var p3.fst)
          (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p4 =>
          Expr.load i64 (Arg.var p4.fst) fun ld =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 376, ())) fun p5 =>
          Expr.load i64 (Arg.var p5.fst) fun ld1 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 384, ())) fun p6 =>
          Expr.load i64 (Arg.var p6.fst) fun ld2 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 608, ())) fun p7 =>
          Expr.load i64 (Arg.var p7.fst) fun ld3 =>
          Expr.group (sig := [[i64, i64]]) (fun Js1 => Blocks.cons (fun (p : Tup Val [i64, i64]) =>
            Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 640, ())) fun p10 =>
              Expr.store (t := i64) (Arg.var p.snd.fst) (Arg.var p10.fst)
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 616, ())) fun p11 =>
                Expr.load i64 (Arg.var p11.fst) fun ld4 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 624, ())) fun p12 =>
                Expr.store (t := i64) (Arg.var ld4) (Arg.var p12.fst)
                  (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 632, ())) fun p13 =>
                  Expr.store (t := i64) (Arg.var p.snd.fst) (Arg.var p13.fst)
                    (Expr.jump Js_ret.fst ())))) Blocks.nil)
              fun Jbr =>
              Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p.fst, Arg.var ld, ())) fun p8 =>
              Expr.jnz (Arg.var p8.fst)
                (Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                    (Arg.var p.snd.fst, Arg.var ld, ())) fun p9 =>
                Expr.jnz (Arg.var p9.fst)
                  (Expr.let_ (Op.mk (.add i64) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p10 =>
                  cIdx4 ld2 p.fst fun p12 =>
                  Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p10.fst, ())) fun p13 =>
                  Expr.store (t := i32) (Arg.var p13.fst) (Arg.var p12)
                    (cIdx4 ld1 p.fst fun p15 => Expr.load i32 (Arg.var p15) fun ld_n =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_n, ())) fun p16 =>
                    Expr.jump Js1.fst (Arg.var p16.fst, Arg.var p10.fst, ())))
                  (Expr.jump Jbr.fst ()))
                (Expr.jump Jbr.fst ())) Blocks.nil)
            fun Js1 => Expr.jump Js1.fst (Arg.var ld3, Arg.imm 0, ()))
          (Expr.jump Js_ret.fst ()))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private theorem fac13_build_branch_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hUp : Γ.Has "full_fheap_up_fid" fidFheapUpSpec)
    {c : FullCfg} {F0 : CNF Nat} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {v64 : Val i64} {hsz lit : Val i32} {mask : Int} {J : Cont [i32]} {cv1 : Nat}
    (hinv : FullDenseInv c F0 st) (hv_lt : v64.toNat < cv1) (hcv_eq : st.core.cur_vars = cv1)
    (hlit_lt : lit.toNat < 2 * cv1) (hhsz_lt : hsz.toNat < 2 * cv1)
    (hhp : ∀ i < hsz.toNat, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * cv1)
    (hm : (FullMem c st ⋆ R) m)
    (hJ : ∀ hsz' : Val i32, ∀ m',
      (∃ st' : FullState, (hsz' = hsz ∨ hsz' = hsz + 1#32) ∧ hsz'.toNat ≤ 2 * cv1 ∧
        FullDenseInv c F0 st' ∧ st'.core.cur_vars = cv1 ∧ st'.core.fuel = st.core.fuel ∧
        (∀ i < hsz'.toNat, (st'.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * cv1) ∧
        (FullMem c st' ⋆ R) m') →
      J (hsz', ()) m') :
    wp Γ Q X (facBuildPushExpr c v64 hsz lit mask J) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hl := hinv.1.lengths; have hcv_le := hl.core_ok.cur_vars_le
  have hfl_lt : v64.toNat < st.core.flags.length := by rw [hl.core_ok.flags_len]; omega
  have hlit_rp : (BitVec.setWidth 64 lit).toNat < st.core.repr.length := by
    rw [fid_bv64_32, hl.core_ok.repr_len]; omega
  have hhl1 : (hsz + 1#32).toNat = hsz.toNat + 1 := fid_bv32_add1 (by omega)
  have hhp_lt : hsz.toNat < st.scratch.tarjan_mark.length := by
    rw [hl.scratch_ok.tarjan_mark_len]; omega
  have hps_lt : (BitVec.setWidth 64 lit).toNat < st.scratch.tarjan_reach.length := by
    rw [fid_bv64_32, hl.scratch_ok.tarjan_reach_len]; omega
  unfold facBuildPushExpr; dsimp only [cIdx4, cZextIdx4]; c0_hfast_nogrp
  · let st0 : FullState := { st with scratch := { st.scratch with
      tarjan_mark := st.scratch.tarjan_mark.set (BitVec.setWidth 64 hsz).toNat lit
      tarjan_reach := st.scratch.tarjan_reach.set (BitVec.setWidth 64 lit).toNat hsz } }
    have hinv0 : FullDenseInv c F0 st0 := s13_dense_set_fheap hinv
      (by simp [hl.scratch_ok.tarjan_mark_len]) (by simp [hl.scratch_ok.tarjan_reach_len])
    refine s13_call_fheap_up hUp hinv0 (hlen_chk := hsz.toNat + 1)
      (Nat.lt_succ_self _) (by dsimp [st0]; omega) ?_ (by assumption)
      fun st' m' hinv' hcore' hhp' hm' => ?_
    · intro k hk; dsimp only [st0]; rw [fid_bv64_32, hcv_eq]
      exact fac13_push_pre_lt hlit_lt hhp_lt hhp k (Nat.lt_succ_iff.mp hk)
    · c0_hfast
      refine hJ (hsz + 1#32) m' ⟨st', Or.inr rfl, by rw [hhl1]; omega, hinv',
        (congrArg (·.cur_vars) hcore').trans hcv_eq, congrArg (·.fuel) hcore',
        fun i hi => by
          rw [hhl1] at hi; have h := hhp' i hi; dsimp [st0] at h; rwa [hcv_eq] at h,
        hm'⟩
  all_goals exact hJ hsz m ⟨st, Or.inl rfl, by omega, hinv, hcv_eq, rfl, hhp, hm⟩

private theorem fac13_push_touched_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {st3 : FullState} {R : Mem 64 → Prop}
    {nl64 nt : Val i64} {lit : Val i32} {tmk : List (BitVec 8)} {tlits : List (BitVec 32)}
    {m : Mem 64} {J : Cont [i64]}
    (hmx : c.max_vars < 2 * dimacsBound) (hnl64 : nl64.toNat = 2 * st3.core.cur_vars)
    (hcv_le : st3.core.cur_vars ≤ c.max_vars) (hlit_lt : lit.toNat < 2 * st3.core.cur_vars)
    (hT : S13TouchInv c st3 R nt tmk tlits m)
    (hJ : ∀ nt' m', (∃ tmk' tlits', S13TouchInv c st3 R nt' tmk' tlits' m') → J (nt', ()) m') :
    wp Γ Q X (facPushTouchedExpr c nl64 lit nt J) m := by
  unfold dimacsBound at hmx; obtain ⟨htmk_l, htlits_l, hnt_le, htlits_b, hcov, hm⟩ := hT
  have hlm_x : (BitVec.setWidth 64 lit).toNat < tmk.length := by
    rw [fid_bv64_32, htmk_l]; exact Nat.lt_of_lt_of_le hlit_lt (Nat.mul_le_mul_left 2 hcv_le)
  unfold facPushTouchedExpr; dsimp only [cIdx4]; c0_hfast_nogrp
  · have hnt_lt : nt.toNat < 2 * st3.core.cur_vars := by
      rw [← hnl64]; exact BitVec.lt_def.mp (by assumption)
    have hnt1 : (nt + 1#64).toNat = nt.toNat + 1 := fid_bv64_add1 (by omega)
    have hws_nt : nt.toNat < tlits.length := by
      rw [htlits_l]; exact Nat.lt_of_lt_of_le hnt_lt (Nat.mul_le_mul_left 2 hcv_le)
    c0_hfast_nogrp
    have hps := s13_push_touched_step hcv_le htmk_l htlits_l hlit_lt hnt_lt hnt1 htlits_b hcov
    exact hJ (nt + 1#64) _
      ⟨_, _, hps.1, hps.2.1, hps.2.2.1, hps.2.2.2.1, hps.2.2.2.2, by assumption⟩
  all_goals exact hJ nt m ⟨tmk, tlits, htmk_l, htlits_l, hnt_le, htlits_b, hcov, hm⟩

private theorem fac13_zero_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {s1 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {max_nlits64 : Val i64} {afterZero : Expr Val Cont [i64]}
    (_hmx : c.max_vars < 2 * dimacsBound) (hinv1 : FullDenseInv c F0 s1)
    (hmnl_64 : max_nlits64.toNat = 2 * c.max_vars) (hm : (FullMem c s1 ⋆ R) m)
    (hAfter : ∀ wsZ hpZ psZ mz, let sZ := facZeroSt s1 wsZ hpZ psZ
      wsZ.length = 2 * c.max_vars → hpZ.length = 2 * c.max_vars → psZ.length = 2 * c.max_vars →
      FullDenseInv c F0 sZ → (FullMem c sZ ⋆ R) mz → wp Γ Q X afterZero mz) :
    wp Γ Q X (s13FacZeroExpr c max_nlits64 afterZero) m := by
  have h1l := hinv1.1.lengths; have h1sc := h1l.scratch_ok
  unfold s13FacZeroExpr; dsimp only [cIdx4]
  refine wp_loop_inv (ts := [i64])
    (fun (zi, ()) mz => zi.toNat ≤ 2 * c.max_vars ∧ ∃ wsZ hpZ psZ : List (BitVec 32),
      wsZ.length = 2 * c.max_vars ∧ hpZ.length = 2 * c.max_vars ∧ psZ.length = 2 * c.max_vars ∧
      (FullMem c (facZeroSt s1 wsZ hpZ psZ) ⋆ R) mz)
    (fun (zi, ()) _ => 2 * c.max_vars - zi.toNat)
    (fun Jz hJz => by
      c0_hfast_nogrp
      exact hJz (0#64, ()) _ ⟨Nat.zero_le _, s1.scratch.wsort, s1.scratch.tarjan_mark,
        s1.scratch.tarjan_reach, h1sc.wsort_len, h1sc.tarjan_mark_len, h1sc.tarjan_reach_len, hm⟩)
    (fun Jz (zi, ()) mz ⟨hzi_le, wsZ, hpZ, psZ, hwsZ, hhpZ, hpsZ, hmz⟩ ihz => ?_)
  · c0_hfast_nogrp
    · have hzi_lt : zi.toNat < 2 * c.max_vars := by
        rw [← hmnl_64]; exact BitVec.lt_def.mp (by assumption : zi < max_nlits64)
      have hzi1 : (zi + 1#64).toNat = zi.toNat + 1 := fid_bv64_add1 (by omega)
      c0_hfast_nogrp
      exact ihz (zi + 1#64, ()) _ (by dsimp only; rw [hzi1]; omega)
        ⟨by rw [hzi1]; omega, wsZ.set zi.toNat 0#32, hpZ.set zi.toNat 0#32,
         psZ.set zi.toNat 0xFFFFFFFF#32, by simp [hwsZ], by simp [hhpZ], by simp [hpsZ],
         by assumption⟩
    · clear ihz
      exact hAfter wsZ hpZ psZ mz hwsZ hhpZ hpsZ
        (hinv1.of_safetySlice ⟨h1l.core_ok,
          { h1sc with wsort_len := hwsZ, tarjan_mark_len := hhpZ, tarjan_reach_len := hpsZ }⟩
          rfl ⟨rfl, rfl⟩) hmz

private theorem fac13_build_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hUp : Γ.Has "full_fheap_up_fid" fidFheapUpSpec)
    {c : FullCfg} {F0 : CNF Nat} {s1 sZ : FullState} {R : Mem 64 → Prop} {mz : Mem 64}
    {K : Tup Val [i32, i64] → Expr Val Cont [i64]}
    (hmx : c.max_vars < 2 * dimacsBound) (hinvZ : FullDenseInv c F0 sZ)
    (hcvZ : sZ.core.cur_vars = s1.core.cur_vars) (hfuZ : sZ.core.fuel = s1.core.fuel)
    (hmz : (FullMem c sZ ⋆ R) mz)
    (hK : ∀ (hsz : Val i32) (_vi : Val i64) (mh : Mem 64),
      (∃ st1 : FullState, hsz.toNat ≤ 2 * s1.core.cur_vars ∧ FullDenseInv c F0 st1 ∧
        st1.core.cur_vars = s1.core.cur_vars ∧ st1.core.fuel = s1.core.fuel ∧
        (∀ i < hsz.toNat,
          (st1.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * s1.core.cur_vars) ∧
        (FullMem c st1 ⋆ R) mh) →
      wp Γ Q X (K (hsz, _vi, ())) mh) :
    wp Γ Q X (s13FacBuildExpr c s1.core.cur_vars K) mz := by
  unfold dimacsBound at hmx
  have h1_cv_le : s1.core.cur_vars ≤ c.max_vars := by
    rw [← hcvZ]; exact hinvZ.1.lengths.core_ok.cur_vars_le
  unfold s13FacBuildExpr; dsimp only [cIdx4, cZextIdx4]; c0_hfast_nogrp
  refine wp_loop_inv (ts := [i32, i64])
    (fun (hsz, vi, ()) mh => ∃ st1 : FullState,
      vi.toNat ≤ s1.core.cur_vars ∧ hsz.toNat ≤ 2 * vi.toNat ∧ FullDenseInv c F0 st1 ∧
      st1.core.cur_vars = s1.core.cur_vars ∧ st1.core.fuel = s1.core.fuel ∧
      (∀ i < hsz.toNat, (st1.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * s1.core.cur_vars) ∧
      (FullMem c st1 ⋆ R) mh)
    (fun (_, vi, ()) _ => s1.core.cur_vars - vi.toNat)
    (fun Jh hJh => by
      c0_hfast_nogrp
      exact hJh (0#32, 0#64, ()) mz ⟨sZ, Nat.zero_le _, Nat.zero_le _, hinvZ, hcvZ, hfuZ,
        fun _ hi => absurd hi (Nat.not_lt_zero _), hmz⟩)
    (fun Jh (hsz, vi, ()) mh ⟨st1, hvi_le, hhsz_le, hinv_1, hcv_1, hfu_1, hhp1, hmh⟩ ih1 => ?_)
  · c0_hfast_nogrp
    · have hvi_lt : vi.toNat < s1.core.cur_vars := by
        have h1 : vi.toNat < s1.core.cur_vars % 2 ^ 64 := by assumption
        rwa [Nat.mod_eq_of_lt (by omega)] at h1
      have hcv1_lt32 : 2 * st1.core.cur_vars < 2 ^ 32 := by
        have := hinv_1.1.lengths.core_ok.cur_vars_le; omega
      have hvi1 : (vi + 1#64).toNat = vi.toNat + 1 := fid_bv64_add1 (by omega)
      have hhl1 : (hsz + 1#32).toNat = hsz.toNat + 1 := fid_bv32_add1 (by omega)
      have h1l := hinv_1.1.lengths
      have hfl_lt : vi.toNat < st1.core.flags.length := by rw [h1l.core_ok.flags_len]; omega
      have hvl_lt : (vi.toNat * 2 ^ 1) % 2 ^ 64 < st1.core.vals.length := by
        rw [h1l.core_ok.vals_len, Nat.mod_eq_of_lt (by omega)]; omega
      have hpl32_toNat : (BitVec.setWidth 32 (vi <<< (1 : Nat))).toNat = 2 * vi.toNat := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
          Nat.mod_eq_of_lt (by omega : vi.toNat * 2 ^ 1 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : vi.toNat * 2 ^ 1 < 2 ^ 32)]; omega
      have hnl32_toNat : (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32).toNat =
          2 * vi.toNat + 1 := fac13_bv32_shl1_or1 vi (by omega)
      refine wp_join_group (ts := [i32])
        (fun (hsz_f, ()) mf => ∃ stf : FullState,
          hsz_f.toNat ≤ 2 * (vi.toNat + 1) ∧ FullDenseInv c F0 stf ∧
          stf.core.cur_vars = s1.core.cur_vars ∧ stf.core.fuel = st1.core.fuel ∧
          (∀ i < hsz_f.toNat,
            (stf.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * s1.core.cur_vars) ∧
          (FullMem c stf ⋆ R) mf) ?_ ?_
      · rintro _ ⟨hsz_f, ⟨⟩⟩ mf ⟨stf, hf_le, hinv_f, hcv_f, hfu_f, hhpf, hmf⟩
        c0_hfast_nogrp
        exact ih1 (hsz_f, vi + 1#64, ()) mf (by dsimp only; rw [hvi1]; omega)
          ⟨stf, by rw [hvi1]; omega, by rw [hvi1]; omega,
           hinv_f, hcv_f, hfu_f.trans hfu_1, hhpf, hmf⟩
      · intro _ hJf
        c0_hfast_nogrp
        · refine wp_join_group (ts := [i32])
            (fun (hsz_p, ()) m_p => ∃ stp : FullState,
              (hsz_p = hsz ∨ hsz_p = hsz + 1#32) ∧ hsz_p.toNat ≤ 2 * vi.toNat + 1 ∧
              FullDenseInv c F0 stp ∧ stp.core.cur_vars = s1.core.cur_vars ∧
              stp.core.fuel = st1.core.fuel ∧
              (∀ i < hsz_p.toNat,
                (stp.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * s1.core.cur_vars) ∧
              (FullMem c stp ⋆ R) m_p) ?_ ?_
          · rintro _ ⟨hsz_p, ⟨⟩⟩ m_p ⟨stp, _, hp_le, hinv_p, hcv_p, hfu_p, hhpp, hm_p⟩
            refine wp_join_group (ts := [i32])
              (fun (hsz_pn, ()) m_pn => ∃ stpn : FullState,
                hsz_pn.toNat ≤ 2 * (vi.toNat + 1) ∧ FullDenseInv c F0 stpn ∧
                stpn.core.cur_vars = s1.core.cur_vars ∧ stpn.core.fuel = st1.core.fuel ∧
                (∀ i < hsz_pn.toNat,
                  (stpn.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * s1.core.cur_vars) ∧
                (FullMem c stpn ⋆ R) m_pn) ?_ ?_
            · rintro _ ⟨hsz_pn, ⟨⟩⟩ m_pn ⟨stpn, hpn_le, hinv_pn, hcv_pn, hfu_pn, hhppn, hm_pn⟩
              c0_hfast_nogrp
              exact hJf (hsz_pn, ()) m_pn ⟨stpn, hpn_le, hinv_pn, hcv_pn, hfu_pn, hhppn, hm_pn⟩
            · intro _ hJn
              refine fac13_build_branch_wp hUp hinv_p hvi_lt hcv_p
                (by change (BitVec.setWidth 32 (vi <<< (1 : Nat)) ||| 1#32).toNat < _
                    rw [hnl32_toNat]; omega) (by dsimp only; omega) hhpp hm_p
                fun hsz_pn m_pn ⟨stpn, hor_pn, _, hinv_pn, hcv_pn, hfu_pn, hhppn, hm_pn⟩ =>
                  hJn (hsz_pn, ()) m_pn ⟨stpn, ?_, hinv_pn, hcv_pn,
                    hfu_pn.trans hfu_p, hhppn, hm_pn⟩
              rcases hor_pn with rfl | rfl; · omega
              dsimp only; rw [fid_bv32_add1 (by omega)]; omega
          · intro _ hJp
            refine fac13_build_branch_wp hUp hinv_1 hvi_lt hcv_1
              (by dsimp only; rw [hpl32_toNat]; omega) (by dsimp only; omega) hhp1 (by assumption)
              fun hsz_p m_p ⟨stp, hor_p, _, hinv_p, hcv_p, hfu_p, hhpp, hm_p⟩ =>
                hJp (hsz_p, ()) m_p ⟨stp, hor_p, ?_, hinv_p, hcv_p, hfu_p, hhpp, hm_p⟩
            rcases hor_p with rfl | rfl; · omega
            rw [hhl1]; omega
        all_goals
          c0_hfast_nogrp
          exact hJf (hsz, ()) _ ⟨st1, by omega, hinv_1, hcv_1, rfl, hhp1, by assumption⟩
    · clear ih1; exact hK hsz vi mh ⟨st1, by omega, hinv_1, hcv_1, hfu_1, hhp1, hmh⟩

private theorem fac13_fheap_pop_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hDown : Γ.Has "full_fheap_down_fid" fidFheapDownSpec)
    {c : FullCfg} {F0 : CNF Nat} {st st1a : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {init_cv : Nat} {init_fuel : BitVec 64} {hsz : BitVec 32} {J : Cont []}
    (hhsz_pos : 0 < hsz.toNat) (hhsz1 : (hsz - 1#32).toNat = hsz.toNat - 1)
    (hhsz_le : hsz.toNat ≤ 2 * st.core.cur_vars)
    (hcv_st : init_cv ≤ st.core.cur_vars) (hfu_st : st.core.fuel = init_fuel)
    (hinv1a : FullDenseInv c F0 st1a) (hc_eq : st1a.core = st.core)
    (htm_eq : st1a.scratch.tarjan_mark = st.scratch.tarjan_mark)
    (hhp_st : ∀ i < hsz.toNat, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (hm : (FullMem c st1a ⋆ R) m)
    (hJ : ∀ xs m2, (∃ st2 : FullState, init_cv ≤ st2.core.cur_vars ∧
        st2.core.fuel = init_fuel ∧ st2.core.cur_vars = st.core.cur_vars ∧
        FullDenseInv c F0 st2 ∧
        (∀ i < (hsz - 1#32).toNat,
          (st2.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st2.core.cur_vars) ∧
        (FullMem c st2 ⋆ R) m2) → J xs m2) :
    wp Γ Q X (s13FacFheapPopExpr c hsz J) m := by
  have h1al := hinv1a.1.lengths; have h1a_cv_le := h1al.core_ok.cur_vars_le
  have hcv1a : st1a.core.cur_vars = st.core.cur_vars := congrArg (·.cur_vars) hc_eq
  unfold s13FacFheapPopExpr; dsimp only [cIdx4, cZextIdx4]; c0_hfast_nogrp
  · have hhsz1_pos : 0 < (hsz - 1#32).toNat :=
      by simpa using (by assumption : BitVec.toNat 0 < (hsz - 1#32).toNat)
    have hhsz1_lt : (hsz - 1#32).toNat < 2 * st.core.cur_vars := by rw [hhsz1]; omega
    have hlast_lt : (BitVec.setWidth 64 (hsz - 1#32)).toNat < st1a.scratch.tarjan_mark.length := by
      rw [fid_bv64_32, h1al.scratch_ok.tarjan_mark_len]; omega
    let last := st1a.scratch.tarjan_mark[(BitVec.setWidth 64 (hsz - 1#32)).toNat]'hlast_lt
    have hlast_lt2 : last.toNat < 2 * st.core.cur_vars := by
      have h1 := hhp_st (hsz - 1#32).toNat (by rw [hhsz1]; omega)
      have hmlt : (hsz - 1#32).toNat < st1a.scratch.tarjan_mark.length := by
        rw [h1al.scratch_ok.tarjan_mark_len]; omega
      rw [← htm_eq, List.getElem?_eq_getElem hmlt, Option.getD_some] at h1
      simpa only [last, fid_bv64_32] using h1
    have h0_lt : 0 < st1a.scratch.tarjan_mark.length := by
      rw [h1al.scratch_ok.tarjan_mark_len]; omega
    c0_hfast_nogrp
    let st1m : FullState := { st1a with scratch := { st1a.scratch with
      tarjan_mark := st1a.scratch.tarjan_mark.set (BitVec.ofNat 64 0).toNat last } }
    have hval_last_lt : (BitVec.setWidth 64 last).toNat < st1m.scratch.tarjan_reach.length := by
      dsimp only [st1m]; rw [fid_bv64_32, h1al.scratch_ok.tarjan_reach_len]; omega
    replace hm : (FullMem c st1m ⋆ R) m := hm
    rw [List.getElem_set_self (by rw [List.length_set]; simpa using h0_lt)]
    c0_hfast_nogrp
    let st1b : FullState := { st1m with scratch := { st1m.scratch with
      tarjan_reach := st1m.scratch.tarjan_reach.set last.toNat 0#32 } }
    have hm_b : (FullMem c st1b ⋆ R) m := by
      dsimp only [st1b, st1m]; rw [← fid_bv64_32 (x := last)]; exact hm
    have hinv1b : FullDenseInv c F0 st1b := s13_dense_set_fheap hinv1a
      (by dsimp [st1b, st1m]; rw [List.length_set, h1al.scratch_ok.tarjan_mark_len])
      (by dsimp [st1b, st1m]; rw [List.length_set, h1al.scratch_ok.tarjan_reach_len])
    have hhp1b : ∀ i < (hsz - 1#32).toNat,
        (st1b.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st1b.core.cur_vars := by
      intro i hi; dsimp only [st1b, st1m]; rw [hcv1a, show (BitVec.ofNat 64 0).toNat = 0 from rfl]
      by_cases hi0 : i = 0
      · subst hi0; rw [List.getElem?_set_self h0_lt, Option.getD_some]; exact hlast_lt2
      · rw [List.getElem?_set_ne (Ne.symm hi0), htm_eq]; exact hhp_st i (by omega)
    refine s13_call_fheap_down (idx := 0#32) (n := hsz - 1#32) hDown hinv1b
      hhsz1_pos (by dsimp only [st1b, st1m]; rw [hcv1a]; omega) hhp1b hm_b
      fun st2 m2 hinv2 hcore2 hhp2 hm2 =>
      hJ () m2 ⟨st2, by rw [congrArg (·.cur_vars) hcore2, hcv1a]; exact hcv_st,
        (congrArg (·.fuel) hcore2).trans ((congrArg (·.fuel) hc_eq).trans hfu_st),
        (congrArg (·.cur_vars) hcore2).trans hcv1a,
        hinv2, by rw [congrArg (·.cur_vars) hcore2]; exact hhp2, hm2⟩
  · have hc0 : ¬ (0#32).toNat < (2 ^ 32 - 1 % 2 ^ 32 + hsz.toNat) % 2 ^ 32 := by assumption
    change ¬ 0 < (hsz - 1#32).toNat at hc0; rw [hhsz1] at hc0
    exact hJ () m ⟨st1a, hcv1a ▸ hcv_st, (congrArg (·.fuel) hc_eq).trans hfu_st, hcv1a, hinv1a,
      fun i hi => by rw [hhsz1] at hi; omega, hm⟩

private theorem fac13_clear_upd_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hUpd : Γ.Has "full_bva_upd_lit_fid" step9BvaUpdLitSpec)
    {c : FullCfg} {F0 : CNF Nat} {st3 : FullState} {R : Mem 64 → Prop} {mA : Mem 64}
    {nt : BitVec 64} {tmk : List (BitVec 8)} {tlits : List (BitVec 32)} {hsz' : BitVec 32}
    {Js : Cont [i32]} (hinv3 : FullDenseInv c F0 st3)
    (htmk_l : tmk.length = 2 * c.max_vars) (htlits_l : tlits.length = 2 * c.max_vars)
    (hnt_le : nt.toNat ≤ 2 * st3.core.cur_vars)
    (htlits_b : ∀ i < nt.toNat, (tlits[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars)
    (hcov : ∀ l < 2 * c.max_vars, tmk[l]?.getD 0#8 ≠ 0#8 →
      ∃ k < nt.toNat, (tlits[k]?.getD 0#32).toNat = l)
    (hhsz'_le : hsz'.toNat ≤ 2 * st3.core.cur_vars)
    (hhp3 : ∀ i < hsz'.toNat, (st3.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars)
    (hmA : (FullMem c (s13SetLmWs2 st3 tmk tlits) ⋆ R) mA)
    (hOut : ∀ hsz_u mU,
      (∃ st_end : FullState, FullDenseInv c F0 st_end ∧
        st_end.core.cur_vars = st3.core.cur_vars ∧ st_end.core.fuel = st3.core.fuel ∧
        hsz_u.toNat ≤ 2 * st_end.core.cur_vars ∧
        (∀ i < hsz_u.toNat,
          (st_end.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st_end.core.cur_vars) ∧
        (FullMem c st_end ⋆ R) mU) →
      Js (hsz_u, ()) mU) :
    wp Γ Q X (s13FacClearUpdExpr c st3 nt hsz' Js) mA := by
  have h3_cv_le := hinv3.1.lengths.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hnt_30 : nt.toNat < 2 ^ 30 := Nat.lt_of_le_of_lt hnt_le (by omega)
  have hcnl_eq : (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)).toNat =
      2 * st3.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  unfold s13FacClearUpdExpr; dsimp only [cIdx4]
  refine wp_loop_inv
    (fun (ui, ()) mC => ui.toNat ≤ nt.toNat ∧ ∃ tmkC : List (BitVec 8),
      tmkC.length = 2 * c.max_vars ∧
      (∀ l < 2 * c.max_vars, tmkC[l]?.getD 0#8 ≠ 0#8 →
        ∃ k, ui.toNat ≤ k ∧ k < nt.toNat ∧ (tlits[k]?.getD 0#32).toNat = l) ∧
      (FullMem c (s13SetLmWs2 st3 tmkC tlits) ⋆ R) mC)
    (fun (ui, ()) _ => nt.toNat - ui.toNat)
    (fun Jc hJc => by c0_hfast_nogrp; exact hJc (0#64, ()) mA ⟨Nat.zero_le _, tmk, htmk_l,
      fun l hl hnz => let ⟨k, hk, hkl⟩ := hcov l hl hnz; ⟨k, Nat.zero_le _, hk, hkl⟩, hmA⟩)
    (fun Jc (ui, ()) mC ⟨hui_le, tmkC, htmkC_l, hcovC, hmC⟩ ihc => ?_)
  c0_hfast_nogrp
  · have hui_lt : ui.toNat < nt.toNat := BitVec.lt_def.mp (by assumption)
    have hui1 : (ui + 1#64).toNat = ui.toNat + 1 := fid_bv64_add1 (by omega)
    have htl_i : ui.toNat < tlits.length := by rw [htlits_l]; omega
    have hlm_x : (BitVec.setWidth 64 (tlits[ui.toNat]'htl_i)).toNat < tmkC.length := by
      have h := htlits_b ui.toNat hui_lt
      rw [List.getElem?_eq_getElem htl_i, Option.getD_some] at h
      rw [fid_bv64_32, htmkC_l]; omega
    c0_hfast_nogrp
    have hcovC' := s13_clear_step h3_cv_le htmkC_l htlits_b hui_lt hui1 hcovC
    rw [List.getElem?_eq_getElem htl_i, Option.getD_some] at hcovC'
    exact ihc (ui + 1#64, ()) _ (by dsimp only; rw [hui1]; omega)
      ⟨by rw [hui1]; omega, _, by simp [htmkC_l], hcovC', by assumption⟩
  · clear ihc
    have hui_ge : nt.toNat ≤ ui.toNat :=
      Nat.le_of_not_lt fun h => (by assumption : ¬ ui < nt) (BitVec.lt_def.mpr h)
    have hzero : ∀ l < 2 * c.max_vars, tmkC[l]?.getD 0#8 = 0#8 := by
      intro l hl; cases hget : (tmkC[l]?.getD 0#8 == 0#8)
      · exfalso; obtain ⟨k, _⟩ := hcovC l hl (by simp_all); omega
      · exact beq_iff_eq.mp hget
    let st_clr := s13SetLmWs2 st3 tmkC tlits
    have hinv_clr : FullDenseInv c F0 st_clr := s13_dense_set_lm_ws2 hinv3 htmkC_l htlits_l hzero
    c0_hfast_nogrp
    refine wp_loop_inv (ts := [i32, i64])
      (fun (hsz_u, ui, ()) mU => ui.toNat ≤ nt.toNat ∧ S13UpdInv c F0 st_clr R hsz_u mU)
      (fun (_, ui, ()) _ => nt.toNat - ui.toNat) ?_ ?_
    · intro Ju hJu; c0_hfast_nogrp; exact hJu (hsz', 0#64, ()) mC
        ⟨Nat.zero_le _, st_clr, hinv_clr, s13HeapFr_refl st_clr, hhsz'_le, hhp3, hmC⟩
    · intro Ju (hsz_u, ui, ()) mU ⟨hui_leU, hU⟩ ihu
      c0_hfast_nogrp
      · have hui_ltU : ui.toNat < nt.toNat := BitVec.lt_def.mp (by assumption)
        have hui1U : (ui + 1#64).toNat = ui.toNat + 1 := fid_bv64_add1 (by omega)
        have ⟨stU, _, hfrU, _, _, _⟩ := hU
        have hws_u_eq : stU.scratch.work_stk2 = tlits := s13HeapFr_work_stk2 hfrU
        have htl_u_lt : ui.toNat < stU.scratch.work_stk2.length := by rw [hws_u_eq, htlits_l]; omega
        have htl_val_lt : (stU.scratch.work_stk2[ui.toNat]'htl_u_lt).toNat <
            2 * st_clr.core.cur_vars := by
          have h := htlits_b ui.toNat hui_ltU
          rw [List.getElem?_eq_getElem (by rw [← hws_u_eq]; exact htl_u_lt), Option.getD_some] at h
          dsimp only [st_clr, s13SetLmWs2]; simp only [hws_u_eq]; exact h
        c0_hfast_nogrp
        refine s13_call_upd_lit (s0 := st_clr) hUpd
          (by dsimp only [st_clr, s13SetLmWs2]; exact hcnl_eq) htl_val_lt hU
          fun hsz_u' mU' hU' => ihu (hsz_u', ui + 1#64, ()) mU'
            (by dsimp only; rw [hui1U]; omega) ⟨by rw [hui1U]; omega, hU'⟩
      · clear ihu
        obtain ⟨st_end, hinv_end, hfr_end, hhsz_end, hhp_end, hm_end⟩ := hU
        have hcv_end := s13HeapFr_cur_vars hfr_end; have hfu_end := s13HeapFr_fuel hfr_end
        exact hOut hsz_u mU ⟨st_end, hinv_end, hcv_end, hfu_end,
          by rw [hcv_end]; exact hhsz_end, by rw [hcv_end]; exact hhp_end, hm_end⟩

private theorem fac13_qi_scan_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {st3 : FullState} {R : Mem 64 → Prop}
    {qn_bv ro_bv : BitVec 32} {nl64 : BitVec 64} {fac_lit qs_dec : BitVec 32}
    {nt2 : BitVec 64} {tmk2 : List (BitVec 8)} {tlits2 : List (BitVec 32)} {mP2 : Mem 64}
    {Ja : Cont [i64, i32]}
    (hmx : c.max_vars < 2 * dimacsBound) (hscr_b : c.scratch_cap < 2 ^ 28)
    (hinv3 : FullDenseInv c F0 st3) (hnl64 : nl64.toNat = 2 * st3.core.cur_vars)
    (hroqn_bnd : ro_bv.toNat + qn_bv.toNat ≤ c.scratch_cap)
    (hrow_ok : ∀ qi_n < qn_bv.toNat,
      Step7RowRefOk st3 (st3.scratch.scratch_buf[ro_bv.toNat + qi_n]?.getD 0#32))
    (hT2 : S13TouchInv c st3 R nt2 tmk2 tlits2 mP2)
    (hJa_next : ∀ ntQ mQ, (∃ tmkQ tlitsQ, S13TouchInv c st3 R ntQ tmkQ tlitsQ mQ) →
      Ja (ntQ, qs_dec, ()) mQ) :
    wp Γ Q X (s13FacQiScanExpr c qn_bv ro_bv nl64 fac_lit qs_dec nt2 Ja) mP2 := by
  unfold dimacsBound at hmx; have h3l := hinv3.1.lengths; have h3_cv_le := h3l.core_ok.cur_vars_le
  have h3_cv32 : 2 * c.max_vars < 2 ^ 30 := by omega
  obtain ⟨htmk2_l, htlits2_l, hnt2_le, htlits2_b, hcov2, hmP2⟩ := hT2
  unfold s13FacQiScanExpr; dsimp only [cIdx4, cZextIdx4, cCmpUlt32]
  refine wp_loop_inv (ts := [i64, i32])
    (fun (ntQ, qi, ()) mQ => qi.toNat ≤ qn_bv.toNat ∧ ∃ tmkQ tlitsQ,
      S13TouchInv c st3 R ntQ tmkQ tlitsQ mQ)
    (fun (_, qi, ()) _ => qn_bv.toNat - qi.toNat)
    (fun Jq hJq => by c0_hfast_nogrp; exact hJq (nt2, 0#32, ()) mP2 ⟨Nat.zero_le _, tmk2, tlits2,
      htmk2_l, htlits2_l, hnt2_le, htlits2_b, hcov2, hmP2⟩)
    (fun Jq (ntQ, qi, ()) mQ
        ⟨hqi_le, tmkQ, tlitsQ, htmkQ_l, htlitsQ_l, hntQ_le, htlitsQ_b, hcovQ, hmQ⟩ ihq => ?_)
  c0_hfast_nogrp
  · have hqi_lt : qi.toNat < qn_bv.toNat := BitVec.lt_def.mp (by assumption)
    have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 :=
      fid_bv32_add1 (Nat.lt_of_le_of_lt hqi_lt qn_bv.isLt)
    have hro_add_qi : ro_bv.toNat + qi.toNat < c.scratch_cap :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hqi_lt _) hroqn_bnd
    have hcw_idx : (ro_bv + qi).toNat = ro_bv.toNat + qi.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt
        (Nat.lt_trans hro_add_qi (Nat.lt_trans hscr_b (by decide)))]
    have hcw_sc : (BitVec.setWidth 64 (ro_bv + qi)).toNat < st3.scratch.scratch_buf.length := by
      rw [fid_bv64_32, hcw_idx, h3l.scratch_ok.scratch_buf_len]; exact hro_add_qi
    let cw := st3.scratch.scratch_buf[(BitVec.setWidth 64 (ro_bv + qi)).toNat]'hcw_sc
    have hcw_ok : Step7RowRefOk st3 cw := by
      have h := hrow_ok qi.toNat hqi_lt
      rw [List.getElem?_eq_getElem (by rw [h3l.scratch_ok.scratch_buf_len]; exact hro_add_qi),
        Option.getD_some] at h
      simpa only [cw, fid_bv64_32, hcw_idx] using h
    have hcw_sc_Q : (BitVec.setWidth 64 (ro_bv + qi)).toNat <
        (s13SetLmWs2 st3 tmkQ tlitsQ).scratch.scratch_buf.length := hcw_sc
    c0_hfast_nogrp
    refine wp_join_group (ts := [i64]) (fun (nt', ()) mQ' =>
        ∃ tmk' tlits', S13TouchInv c st3 R nt' tmk' tlits' mQ') ?_ ?_
    · rintro _ ⟨nt', ⟨⟩⟩ mQ' ⟨tmk', tlits', hT'⟩; c0_hstraight
      exact ihq (nt', qi + 1#32, ()) mQ' (by dsimp only; rw [hqi1]; omega)
        ⟨by rw [hqi1]; exact hqi_lt, tmk', tlits', hT'⟩
    · intro _ hJs
      c0_hstraight; refine LeanQbe.T.C0HeadStep.head_wp_jnz rfl ?_ ?_
      · intro hcBin
        have hbin : (cw &&& 0x80000000#32) ≠ 0#32 := bne_iff_ne.mp hcBin
        have hol_lt : (cw &&& 0x7FFFFFFF#32).toNat < 2 * st3.core.cur_vars := by
          unfold Step7RowRefOk at hcw_ok; rwa [ite_eq_left hbin] at hcw_ok
        c0_hstraight
        refine wp_join_group (ts := [i64]) (fun (nt', ()) mQ' =>
            ∃ tmk' tlits', S13TouchInv c st3 R nt' tmk' tlits' mQ') ?_ ?_
        · rintro _ ⟨nt', ⟨⟩⟩ mQ' ⟨tmk', tlits', hT'⟩; c0_hstraight
          exact hJs (nt', ()) mQ' ⟨tmk', tlits', hT'⟩
        · intro _ hJo
          exact fac13_push_touched_wp hmx hnl64 h3_cv_le hol_lt
            ⟨htmkQ_l, htlitsQ_l, hntQ_le, htlitsQ_b, hcovQ, hmQ⟩
            fun nt' m' hT' => hJo (nt', ()) m' hT'
      · intro hcCls
        have hnbin : (cw &&& 0x80000000#32) = 0#32 :=
          if h : (cw &&& 0x80000000#32) = 0#32 then h else False.elim <| by
            have hb := bne_iff_ne.mpr h
            have hfl : ((cw &&& 0x80000000#32) != 0#32) = false := hcCls
            rw [hfl] at hb; cases hb
        have hcw_lg : cw.toNat ∈ fullArenaClauseRefs st3 ∧
            cw.toNat + 3 + fullArenaClauseSize st3 cw.toNat ≤ st3.core.arena_len ∧
            ∀ l ∈ fullArenaClauseLits st3 cw.toNat, l < 2 * st3.core.cur_vars := by
          unfold Step7RowRefOk at hcw_ok; rwa [ite_eq_right (fun h => h hnbin)] at hcw_ok
        have har_lt32 : st3.core.arena_len < 2 ^ 32 := by
          have := h3l.core_ok.arena_len_le; have := c.harena; unfold dimacsBound at *; omega
        have har2_lt : (BitVec.setWidth 64 cw + 2#64).toNat < st3.core.arena.length := by
          rw [BitVec.toNat_add, fid_bv64_32, show (2#64 : BitVec 64).toNat = 2 from rfl,
            Nat.mod_eq_of_lt (by omega), h3l.core_ok.arena_len_arr]
          have := h3l.core_ok.arena_len_le; omega
        c0_hstraight
        let csz_bv := st3.core.arena[(BitVec.setWidth 64 cw + 2#64).toNat]'har2_lt
        have hcsz_eq : csz_bv.toNat = fullArenaClauseSizeCore st3.core cw.toNat := by
          dsimp only [csz_bv]; unfold fullArenaClauseSizeCore
          have hidx : (BitVec.setWidth 64 cw + 2#64).toNat = cw.toNat + 2 := by
            rw [BitVec.toNat_add, fid_bv64_32, show (2#64 : BitVec 64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          simp only [hidx]
          rw [List.getElem?_eq_getElem (by
            rw [h3l.core_ok.arena_len_arr]; have := h3l.core_ok.arena_len_le; omega),
            Option.getD_some]
        refine wp_loop_inv (ts := [i64, i32])
          (fun (ntL, lj, ()) mL => lj.toNat ≤ csz_bv.toNat ∧
            ∃ tmkL tlitsL, S13TouchInv c st3 R ntL tmkL tlitsL mL)
          (fun (_, lj, ()) _ => csz_bv.toNat - lj.toNat)
          (fun Jl hJl => by c0_hstraight; exact hJl (ntQ, 0#32, ()) mQ ⟨Nat.zero_le _, tmkQ, tlitsQ,
            htmkQ_l, htlitsQ_l, hntQ_le, htlitsQ_b, hcovQ, hmQ⟩)
          (fun Jl (ntL, lj, ()) mL
              ⟨hlj_le, tmkL, tlitsL, htmkL_l, htlitsL_l, hntL_le, htlitsL_b, hcovL, hmL⟩ ihl => ?_)
        c0_hfast_nogrp
        · have hlj_lt : lj.toNat < csz_bv.toNat := BitVec.lt_def.mp (by assumption)
          have hcsz_le_ar : csz_bv.toNat ≤ st3.core.arena_len := by
            rw [hcsz_eq]; exact Nat.le_trans (Nat.le_add_left _ _) hcw_lg.2.1
          have hlj1 : (lj + 1#32).toNat = lj.toNat + 1 := fid_bv32_add1 (by omega)
          have hcsz_cl : csz_bv.toNat = fullArenaClauseSize st3 cw.toNat := hcsz_eq
          have harl_idx : (BitVec.setWidth 64 cw + 3#64 + BitVec.setWidth 64 lj).toNat =
              cw.toNat + 3 + lj.toNat := by
            have := cw.isLt; have := lj.isLt
            exact fid_bv64_add3_u32 (by simp only [fid_bv64_32]; omega)
          have harl_lt : (BitVec.setWidth 64 cw + 3#64 + BitVec.setWidth 64 lj).toNat <
              st3.core.arena.length := by
            rw [harl_idx, h3l.core_ok.arena_len_arr]; have := h3l.core_ok.arena_len_le; omega
          have hl_lt : (st3.core.arena[(BitVec.setWidth 64 cw + 3#64 +
              BitVec.setWidth 64 lj).toNat]'harl_lt).toNat < 2 * st3.core.cur_vars := by
            have hg := fullArenaClauseLitsCore_getElem (k := st3.core) (r := cw.toNat)
              (j := lj.toNat) (by rw [← hcsz_eq]; exact hlj_lt)
              (by rw [← harl_idx]; exact harl_lt)
            exact hcw_lg.2.2 _ (List.mem_iff_getElem?.mpr
              ⟨lj.toNat, by simpa only [harl_idx] using hg⟩)
          c0_hfast_nogrp
          refine wp_join_group (ts := [i64]) (fun (ntL', ()) mL' =>
              ∃ tmkL' tlitsL', S13TouchInv c st3 R ntL' tmkL' tlitsL' mL') ?_ ?_
          · rintro _ ⟨ntL', ⟨⟩⟩ mL' ⟨tmkL', tlitsL', hTL'⟩; c0_hfast_nogrp
            exact ihl (ntL', lj + 1#32, ()) mL' (by dsimp only; rw [hlj1]; omega)
              ⟨by rw [hlj1]; exact hlj_lt, tmkL', tlitsL', hTL'⟩
          · intro _ hJl'; c0_hstraight
            refine LeanQbe.T.C0HeadStep.head_wp_jnz rfl ?_ ?_
            · intro _; exact fac13_push_touched_wp hmx hnl64 h3_cv_le hl_lt
                ⟨htmkL_l, htlitsL_l, hntL_le, htlitsL_b, hcovL, hmL⟩
                fun nt' m' hT' => hJl' (nt', ()) m' hT'
            · intro _; c0_hstraight; exact hJl' (ntL, ()) mL
                ⟨tmkL, tlitsL, htmkL_l, htlitsL_l, hntL_le, htlitsL_b, hcovL, hmL⟩
        · exact hJs (ntL, ()) mL ⟨tmkL, tlitsL, htmkL_l, htlitsL_l, hntL_le, htlitsL_b, hcovL, hmL⟩
  · exact hJa_next ntQ mQ ⟨tmkQ, tlitsQ, htmkQ_l, htlitsQ_l, hntQ_le, htlitsQ_b, hcovQ, hmQ⟩

private theorem fac13_exit_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {st : FullState} {R : Mem 64 → Prop} {mw : Mem 64}
    {init_cv : Nat} {init_fuel : BitVec 64}
    (hcv_st : init_cv ≤ st.core.cur_vars) (hfu_st : st.core.fuel = init_fuel)
    (hinv_st : FullDenseInv c F0 st) (hmw : (FullMem c st ⋆ R) mw)
    (hQ : ∀ (res : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → init_cv ≤ s'.core.cur_vars → s'.core.fuel = init_fuel →
      res = 1#64 → (FullMem c s' ⋆ R) m' → Q (res, ()) m') :
    wp Γ Q X (s13FacExitExpr c st init_cv) mw := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx; have hstl := hinv_st.1.lengths
  have hst_cv_le := hstl.core_ok.cur_vars_le
  have henl_eq : (BitVec.ofNat 64 st.core.cur_vars <<< (1 : Nat)).toNat = 2 * st.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  unfold s13FacExitExpr; dsimp only [cIdx4]
  refine wp_loop_inv (ts := [i64])
    (fun (ci, ()) mf => ci.toNat ≤ 2 * st.core.cur_vars ∧ ∃ hpf psf,
      hpf.length = 2 * c.max_vars ∧ psf.length = 2 * c.max_vars ∧
      (FullMem c { st with scratch := { st.scratch with tarjan_mark := hpf, tarjan_reach := psf } }
        ⋆ R) mf)
    (fun (ci, ()) _ => 2 * st.core.cur_vars - ci.toNat)
    (fun J4 hJ4 => by
      c0_hfast_nogrp; exact hJ4 (0#64, ()) mw ⟨Nat.zero_le _, st.scratch.tarjan_mark,
        st.scratch.tarjan_reach, hstl.scratch_ok.tarjan_mark_len,
        hstl.scratch_ok.tarjan_reach_len, hmw⟩)
    (fun J4 (ci, ()) mf ⟨hci_le, hpf, psf, hhpf, hpsf, hmf⟩ ih4 => ?_)
  c0_hfast_nogrp
  · have hci_lt : ci.toNat < 2 * st.core.cur_vars := by
      rw [← henl_eq]; exact BitVec.lt_def.mp (by assumption)
    have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := fid_bv64_add1 (by omega)
    c0_hfast_nogrp
    refine ih4 (ci + 1#64, ()) _ (by dsimp only; rw [hci1]; omega)
      ⟨by rw [hci1]; omega, _, _, ?_, ?_, by assumption⟩ <;> simp [hhpf, hpsf]
  · clear ih4
    let stf : FullState := { st with scratch := { st.scratch with
      tarjan_mark := hpf, tarjan_reach := psf } }
    have hinvf := s13_dense_set_fheap hinv_st hhpf hpsf
    have hfl := hinvf.1.lengths
    have hstf_cv_le : stf.core.cur_vars ≤ c.max_vars := hfl.core_ok.cur_vars_le
    refine wp_join_group (ts := []) (fun _ mEx => ∃ s' : FullState,
        FullDenseInv c F0 s' ∧ init_cv ≤ s'.core.cur_vars ∧ s'.core.fuel = init_fuel ∧
        (FullMem c s' ⋆ R) mEx)
      (fun _ _ mEx ⟨s', hinv', hcv', hfu', hmEx⟩ => by
        c0_hfast_nogrp; exact hQ 1#64 s' mEx hinv' hcv' hfu' rfl hmEx)
      (fun Js_ret hJs_ret => ?_)
    c0_hfast_nogrp
    · refine wp_loop_inv (ts := [i64, i64])
        (fun (qidx, qst, ()) mq => qst.toNat ≤ stf.core.cur_vars ∧
          ∃ qs' : List (BitVec 32), qs'.length = c.max_vars ∧
          (FullMem c { stf with scratch := { stf.scratch with q_stamp := qs' } } ⋆ R) mq)
        (fun (_, qst, ()) _ => stf.core.cur_vars - qst.toNat) ?_ ?_
      · intro J9 hJ9; c0_hfast_nogrp; exact hJ9 (_, 0#64, ()) mf
          ⟨Nat.zero_le _, stf.scratch.q_stamp, hfl.scratch_ok.q_stamp_len, hmf⟩
      · intro J9 (qidx, qst, ()) mq ⟨hqst_le, qs', hqs', hmq⟩ ih9
        refine wp_join_group (ts := []) (fun _ mq' => mq' = mq) ?_ ?_
        · rintro _ ⟨⟩ mq' rfl; c0_hfast_nogrp
          let stq : FullState := { stf with scratch := { stf.scratch with
            q_stamp := qs', q_cur_stamp := qst,
            q_search_idx := stf.scratch.q_last, q_search_stamp := qst } }
          exact hJs_ret () _ ⟨stq, hinvf.of_safetySlice
            ⟨hfl.core_ok, { hfl.scratch_ok with q_stamp_len := hqs' }⟩ rfl ⟨rfl, rfl⟩,
            hcv_st, hfu_st, by assumption⟩
        · intro _ hJbr; c0_hfast_nogrp
          · have hqi_lt : qidx.toNat < stf.core.cur_vars := by
              have h1 := BitVec.lt_def.mp
                (by assumption : qidx < BitVec.ofNat 64 st.core.cur_vars)
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
            have hqs_lt : qst.toNat < stf.core.cur_vars := by
              have h1 := BitVec.lt_def.mp (by assumption : qst < BitVec.ofNat 64 st.core.cur_vars)
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
            have hqs_idx : qidx.toNat < qs'.length := by rw [hqs']; omega
            have hqn_idx : qidx.toNat < stf.scratch.q_next.length := by
              rw [hfl.scratch_ok.q_next_len]; omega
            have hqst1 : (qst + 1#64).toNat = qst.toNat + 1 := fid_bv64_add1 (by omega)
            c0_hfast_nogrp
            refine ih9 (BitVec.setWidth 64 (stf.scratch.q_next[qidx.toNat]'hqn_idx),
                qst + 1#64, ()) _ (by dsimp only; rw [hqst1]; omega)
              ⟨by rw [hqst1]; omega, qs'.set qidx.toNat (BitVec.setWidth 32 (qst + 1#64)),
               by rw [List.length_set, hqs'], by assumption⟩
          all_goals exact hJbr () mq rfl
    · exact hJs_ret () mf ⟨stf, hinvf, hcv_st, hfu_st, hmf⟩

/-! ## 4. Top-Level Driver Proof (`full_factor_wp`) -/

public section

/-- Parametric `Func.wp` proof for `Src.Factor.full_factor_body` against canonical
`fullFactorHeapSpec`. -/
theorem full_factor_wp (Γ : Env)
    (hSteps : Γ.Has "full_bva_steps_cap_fid" fidBvaStepsCapSpec)
    (hConnect : Γ.Has "full_bva_connect_clauses_fid" fidBvaConnectClausesSpec)
    (hUp : Γ.Has "full_fheap_up_fid" fidFheapUpSpec)
    (hDown : Γ.Has "full_fheap_down_fid" fidFheapDownSpec)
    (hTryLit : Γ.Has "full_bva_try_lit" step7BvaTryLitSpec)
    (hUpd : Γ.Has "full_bva_upd_lit_fid" step9BvaUpdLitSpec) :
    ∀ args m Q X, Factor.Spec.fullFactorHeapSpec args m Q X →
      Func.wp Γ full_factor_body args m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_factor_body
  have hmx := c.hmaxv; have hmx_n : c.max_vars < 2 * 2 ^ 28 := by simpa [dimacsBound] using hmx
  have hscr_b := c.hscr; unfold dimacsBound at hscr_b
  have hlen := hinv.1.lengths; have hcv_le := hlen.core_ok.cur_vars_le
  c0_hfast_nogrp
  refine s13_call_steps_cap hSteps fun scb _hscb => ?_
  iterate 3 (c0_hsplit; · c0_hfast; exact hQ 1#64 s m hinv (Nat.le_refl _) rfl rfl hm)
  obtain ⟨F_cur0, hw0⟩ := hinv.1.witness
  have hdw0 : FullDenseInvW c F0 F_cur0 s :=
    ⟨hlen, hw0, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩
  refine wp_call_of_spec _ _ (hConnect (c.hdr, ()) m (fun r m' => wp Γ Q X _ m') X
    ⟨c, F0, F_cur0, s, R, rfl, hdw0, hm, fun s0 m0 hdw1 hcv0 hfu0 _ _ _ hm0 => ?_⟩)
  have hinv0 : FullDenseInv c F0 s0 :=
    ⟨⟨hdw1.1, F_cur0, hdw1.2.1⟩, hdw1.2.2.1, hdw1.2.2.2.1, hdw1.2.2.2.2.1,
     hdw1.2.2.2.2.2.1, hdw1.2.2.2.2.2.2⟩
  c0_hfast_nogrp
  · exact hQ 1#64 s0 m0 hinv0 (Nat.le_of_eq hcv0.symm) hfu0 rfl hm0
  let s1 : FullState := { s0 with scratch := { s0.scratch with ant_sz := budget } }
  have hinv1 : FullDenseInv c F0 s1 :=
    hinv0.of_safetySlice ⟨hdw1.1.core_ok, s13_lengths_set_ant_sz hdw1.1.scratch_ok budget⟩
      rfl ⟨rfl, rfl⟩
  let init_cv := s1.core.cur_vars; let init_fuel := s1.core.fuel
  have hmnl_64 : (BitVec.ofNat 64 c.max_vars <<< (1 : Nat)).toNat = 2 * c.max_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  refine fac13_zero_wp (R := R) hmx hinv1 hmnl_64 (by assumption)
    fun _wsZ _hpZ _psZ mz _hwsZ _hhpZ _hpsZ hinvZ hmz => ?_
  refine fac13_build_wp hUp hmx hinvZ rfl rfl hmz
    fun hsz _vi mh ⟨st1, hhsz_1, hinv_1, hcv_1, hfu_1, hhp1, hmh⟩ => ?_
  c0_hfast_nogrp
  refine wp_while_state (ts := [i32]) (α := FullState × BitVec 32) (fun p => (p.2, ()))
    (fun p => (c.max_vars - p.1.core.cur_vars) * (2 * c.max_vars + 1) + p.2.toNat)
    (fun (st, hsz) mw => init_cv ≤ st.core.cur_vars ∧ st.core.fuel = init_fuel ∧
      hsz.toNat ≤ 2 * st.core.cur_vars ∧ FullDenseInv c F0 st ∧
      (∀ i < hsz.toNat, (st.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st.core.cur_vars) ∧
      (FullMem c st ⋆ R) mw)
    (fun Jm hJm => by
      c0_hfast_nogrp
      exact hJm (st1, hsz) mh ⟨Nat.le_of_eq hcv_1.symm, hfu_1,
        by rw [hcv_1]; exact hhsz_1, hinv_1, fun i hi => by rw [hcv_1]; exact hhp1 i hi, hmh⟩)
    (fun Jm (st, hsz) mw ⟨hcv_st, hfu_st, hhsz_st, hinv_st, hhp_st, hmw⟩ ihm => ?_)
  c0_hfast_nogrp
  refine wp_join_group (ts := []) (fun _ mEx => mEx = mw) ?_ ?_
  · rintro _ ⟨⟩ mEx rfl; clear ihm; c0_hfast_nogrp
    exact fac13_exit_wp hcv_st hfu_st hinv_st hmw fun res s' m' hinv' hcv' hfu' hr' hm' =>
      hQ res s' m' hinv' (by rw [← hcv0]; exact hcv') (hfu'.trans hfu0) hr' hm'
  · intro Jex hJex; c0_hfast_nogrp; rotate_left 1; iterate 4 exact hJex () mw rfl
    have hhsz_pos : 0 < hsz.toNat := by simpa using (by assumption : BitVec.toNat 0 < hsz.toNat)
    have hhsz1 : (hsz - 1#32).toNat = hsz.toNat - 1 := s9_bv32_sub1 hhsz_pos
    have hstl := hinv_st.1.lengths; have hst_cv_le := hstl.core_ok.cur_vars_le
    have hf0_lt : (st.scratch.tarjan_mark[0]'(by
        rw [hstl.scratch_ok.tarjan_mark_len]; omega)).toNat < 2 * st.core.cur_vars := by
      have h := hhp_st 0 hhsz_pos
      rwa [List.getElem?_eq_getElem (by rw [hstl.scratch_ok.tarjan_mark_len]; omega),
        Option.getD_some] at h
    let f0 := st.scratch.tarjan_mark[0]'(by rw [hstl.scratch_ok.tarjan_mark_len]; omega)
    have hf0_lt' : f0.toNat < 2 * st.core.cur_vars := hf0_lt
    have hf0_ps_lt : (BitVec.setWidth 64 f0).toNat < st.scratch.tarjan_reach.length := by
      rw [fid_bv64_32, hstl.scratch_ok.tarjan_reach_len]; omega
    have htm0 : 0 < st.scratch.tarjan_mark.length := by rw [hstl.scratch_ok.tarjan_mark_len]; omega
    c0_hfast_nogrp
    let st1a : FullState := { st with scratch := { st.scratch with
      tarjan_reach := st.scratch.tarjan_reach.set (BitVec.setWidth 64 f0).toNat 0xFFFFFFFF#32 } }
    have hinv1a : FullDenseInv c F0 st1a := s13_dense_set_fheap hinv_st
      hstl.scratch_ok.tarjan_mark_len (by simp [hstl.scratch_ok.tarjan_reach_len])
    refine wp_join_group (ts := []) (fun _ mf => ∃ st2 : FullState,
        init_cv ≤ st2.core.cur_vars ∧ st2.core.fuel = init_fuel ∧
        st2.core.cur_vars = st.core.cur_vars ∧ FullDenseInv c F0 st2 ∧
        (∀ i < (hsz - 1#32).toNat,
          (st2.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st2.core.cur_vars) ∧
        (FullMem c st2 ⋆ R) mf) ?_ ?_
    · rintro _ ⟨⟩ mf ⟨st2, hcv2, hfu2, hcv2_eq, hinv2, hhp2, hmf⟩
      have h2l := hinv2.1.lengths; have h2_cv_le := h2l.core_ok.cur_vars_le
      have hf0_lt2 : f0.toNat < 2 * st2.core.cur_vars := hcv2_eq ▸ hf0_lt
      have hfv_lt : (BitVec.setWidth 64 (f0 >>> (1 : Nat))).toNat < st2.core.flags.length := by
        rw [fid_bv64_32, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one,
          h2l.core_ok.flags_len]; omega
      have hval_lt : (BitVec.setWidth 64 f0).toNat < st2.core.vals.length := by
        rw [fid_bv64_32, h2l.core_ok.vals_len]; omega
      have hdeg_lt : (BitVec.setWidth 64 f0).toNat < st2.core.repr.length := by
        rw [fid_bv64_32, h2l.core_ok.repr_len]; omega
      have hhsz1_lt : (hsz - 1#32).toNat < hsz.toNat := by omega
      c0_hfast_nogrp
      refine wp_join_group (ts := [i32])
        (fun (fbit, ()) mf0 => (fbit = 32#32 ∨ fbit = 64#32) ∧ (FullMem c st2 ⋆ R) mf0)
        ?_ (fun _ hJfb => by
          c0_hfast_nogrp; · exact hJfb (64#32, ()) mf ⟨Or.inr rfl, hmf⟩
          exact hJfb (32#32, ()) mf ⟨Or.inl rfl, hmf⟩)
      rintro _ ⟨fbit, ⟨⟩⟩ mf ⟨_, hmf⟩
      have hdec_hsz : ∀ st' : FullState, st'.core.cur_vars = st.core.cur_vars →
          (c.max_vars - st'.core.cur_vars) * (2 * c.max_vars + 1) + (hsz - 1#32).toNat <
            (c.max_vars - st.core.cur_vars) * (2 * c.max_vars + 1) + hsz.toNat :=
        fun st' h => by rw [h, hhsz1]; omega
      have hhsz1_le : (hsz - 1#32).toNat ≤ 2 * st2.core.cur_vars := by rw [hcv2_eq, hhsz1]; omega
      have h_jm_st2a : ∀ {fl' : List (BitVec 32)} {m' : Mem 64},
          (FullMem c { st2 with core := { st2.core with flags := fl' } } ⋆ R) m' →
          fl'.length = c.max_vars → Jm (hsz - 1#32, ()) m' := fun {fl' m'} hm' hlen =>
        ihm ({ st2 with core := { st2.core with flags := fl' } }, hsz - 1#32) m'
          (hdec_hsz _ hcv2_eq) ⟨hcv2, hfu2, hhsz1_le, s13_dense_set_flags hinv2 hlen, hhp2, hm'⟩
      c0_hfast_nogrp
      all_goals try
        (c0_hfast_nogrp; exact ihm (st2, hsz - 1#32) mf (hdec_hsz st2 hcv2_eq) ⟨hcv2, hfu2,
          hhsz1_le, hinv2, hhp2, hmf⟩)
      all_goals try
        (c0_hfast_nogrp; refine h_jm_st2a hm ?_; simp [h2l.core_ok.flags_len])
      · obtain ⟨fl', hfl'_len, hm2a⟩ : ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
            (FullMem c { st2 with core := { st2.core with flags := fl' } } ⋆ R) m :=
          ⟨_, by simp [h2l.core_ok.flags_len], hm⟩
        let st2a : FullState := { st2 with core := { st2.core with flags := fl' } }
        refine wp_join_group (ts := [i32]) Jm
          (fun _ _ _ h_j => by c0_hfast_nogrp; exact h_j) (fun _ hJs => ?_)
        refine wp_call_of_spec _ _ (hTryLit _ _ _ _ ?_)
        refine ⟨c, F0, st2a, R, rfl, s13_dense_set_flags hinv2 hfl'_len, hf0_lt2, hm2a, ?_⟩
        intro ok3 st3 m3 hinv3 hcv3_le hcv3_lt hcom3 hfu3 htm3 _ hm3
        c0_hsplit
        · have hok_t : ok3 = true := by assumption
          have hcv3_gt : st2.core.cur_vars < st3.core.cur_vars := hcv3_lt hok_t
          obtain ⟨bkNat, hbk⟩ := hcom3 hok_t
          have h3l := hinv3.1.lengths; have h3_cv_le := h3l.core_ok.cur_vars_le
          have hbk_sc := hbk.1; have hcap_le := fidStepsCap_le_256 c.scratch_cap
          have hmul4_le := fidStepsCap_mul4_le c.scratch_cap
          c0_hfast_nogrp
          refine s13_call_steps_cap hSteps fun sc_b hsc_b => ?_
          c0_hfast_nogrp
          have hbk_eq : (BitVec.setWidth 32 st3.scratch.res_sz).toNat = bkNat := by
            rw [hbk.2.1, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have hcnl_eq : (BitVec.ofNat 64 st3.core.cur_vars <<< (1 : Nat)).toNat =
              2 * st3.core.cur_vars := by
            rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
          refine wp_loop_inv (ts := [i64, i32])
            (fun (nt, qs_idx, ()) mA => qs_idx.toNat ≤ bkNat + 1 ∧ ∃ tmk tlits,
              S13TouchInv c st3 R nt tmk tlits mA)
            (fun (_, qs_idx, ()) _ => qs_idx.toNat)
            (fun Ja hJa => by
              c0_hfast_nogrp
              exact hJa (0#64, BitVec.setWidth 32 st3.scratch.res_sz + 1#32, ()) m3
                ⟨by rw [fid_bv32_add1 (by rw [hbk_eq]; omega), hbk_eq]; omega,
                 st3.core.lit_mark, st3.scratch.work_stk2, h3l.core_ok.lit_mark_len,
                 h3l.scratch_ok.work_stk2_len, Nat.zero_le _,
                 fun _ hi => absurd hi (Nat.not_lt_zero _),
                 fun l hl hnz => absurd (hinv3.2.1.2 l hl) hnz, hm3⟩)
            (fun Ja (nt, qs_idx, ()) mA
                ⟨hqs_le, tmk, tlits, htmk_l, htlits_l, hnt_le, htlits_b, hcov, hmA⟩ iha => ?_)
          · c0_hfast_nogrp
            · have hqs_pos : 0 < qs_idx.toNat := by
                first
                | exact Nat.pos_of_ne_zero
                    (fun h => (by assumption : qs_idx ≠ 0#32) (BitVec.eq_of_toNat_eq h))
                | simpa using BitVec.lt_def.mp (by assumption : 0#32 < qs_idx)
              have hqs1 : (qs_idx - 1#32).toNat = qs_idx.toNat - 1 := s9_bv32_sub1 hqs_pos
              have hrow := hbk.2.2 (qs_idx - 1#32).toNat (by omega)
              have hsc_lt : (qs_idx - 1#32).toNat < st3.scratch.scratch_buf.length := by
                rw [h3l.scratch_ok.scratch_buf_len]; omega
              have hsc_lt64 : (BitVec.setWidth 64 (qs_idx - 1#32)).toNat <
                  st3.scratch.scratch_buf.length := by rw [fid_bv64_32]; exact hsc_lt
              have heq_sb : st3.scratch.scratch_buf[
                  (BitVec.setWidth 64 (qs_idx - 1#32)).toNat]'hsc_lt64 =
                  st3.scratch.scratch_buf[(qs_idx - 1#32).toNat]'hsc_lt := by
                simp only [fid_bv64_32]
              have hfac_lt : (st3.scratch.scratch_buf[(qs_idx - 1#32).toNat]'hsc_lt).toNat <
                  2 * st3.core.cur_vars := by
                have h := hrow.1; rwa [List.getElem?_eq_getElem hsc_lt, Option.getD_some] at h
              have hfneg_lt : ((st3.scratch.scratch_buf[(qs_idx - 1#32).toNat]'hsc_lt) ^^^
                  1#32).toNat < 2 * st3.core.cur_vars := fac13_bv32_xor1_lt hfac_lt (by omega)
              c0_hfast_nogrp
              refine wp_join_group (ts := [i64]) (fun (nt1, ()) mP1 => ∃ tmk1 tlits1,
                  S13TouchInv c st3 R nt1 tmk1 tlits1 mP1) ?_ ?_
              · rintro _ ⟨nt1, ⟨⟩⟩ mP1
                  ⟨tmk1, tlits1, htmk1_l, htlits1_l, hnt1_le, htlits1_b, hcov1, hmP1⟩
                c0_hfast_nogrp
                refine wp_join_group (ts := [i64]) (fun (nt2, ()) mP2 => ∃ tmk2 tlits2,
                    S13TouchInv c st3 R nt2 tmk2 tlits2 mP2) ?_ ?_
                · rintro _ ⟨nt2, ⟨⟩⟩ mP2
                    ⟨tmk2, tlits2, htmk2_l, htlits2_l, hnt2_le, htlits2_b, hcov2, hmP2⟩
                  have hro_idx : (sc_b + (qs_idx - 1#32)).toNat =
                      sc_b.toNat + (qs_idx - 1#32).toNat := by
                    rw [BitVec.toNat_add, hsc_b, Nat.mod_eq_of_lt (by omega)]
                  have hro_sc : (BitVec.setWidth 64 (sc_b + (qs_idx - 1#32))).toNat <
                      st3.scratch.scratch_buf.length := by
                    rw [fid_bv64_32, hro_idx, h3l.scratch_ok.scratch_buf_len]; omega
                  have hqn_idx : (2#32 * sc_b + (qs_idx - 1#32)).toNat =
                      2 * sc_b.toNat + (qs_idx - 1#32).toNat := by
                    rw [BitVec.toNat_add, BitVec.toNat_mul, hsc_b,
                      show (2#32 : BitVec 32).toNat = 2 from rfl,
                      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                  have hqn_sc : (BitVec.setWidth 64 (2#32 * sc_b + (qs_idx - 1#32))).toNat <
                      st3.scratch.scratch_buf.length := by
                    rw [fid_bv64_32, hqn_idx, h3l.scratch_ok.scratch_buf_len]; omega
                  have hro_sc' : fidStepsCap c.scratch_cap + (qs_idx - 1#32).toNat <
                      st3.scratch.scratch_buf.length := by
                    rw [← hsc_b, ← hro_idx, ← fid_bv64_32]; exact hro_sc
                  have hqn_sc' : 2 * fidStepsCap c.scratch_cap + (qs_idx - 1#32).toNat <
                      st3.scratch.scratch_buf.length := by
                    rw [← hsc_b, ← hqn_idx, ← fid_bv64_32]; exact hqn_sc
                  let ro_bv := st3.scratch.scratch_buf[
                    (BitVec.setWidth 64 (sc_b + (qs_idx - 1#32))).toNat]'hro_sc
                  let qn_bv := st3.scratch.scratch_buf[
                    (BitVec.setWidth 64 (2#32 * sc_b + (qs_idx - 1#32))).toNat]'hqn_sc
                  have hroqn_bnd : ro_bv.toNat + qn_bv.toNat ≤ c.scratch_cap := by
                    have h := hrow.2.1; dsimp only [ro_bv, qn_bv]
                    simp only [fid_bv64_32, hro_idx, hqn_idx, hsc_b,
                      List.getElem?_eq_getElem hro_sc', List.getElem?_eq_getElem hqn_sc',
                      Option.getD_some] at h ⊢; exact h
                  c0_hfast_nogrp
                  refine fac13_qi_scan_wp hmx hscr_b hinv3 hcnl_eq hroqn_bnd ?_
                    ⟨htmk2_l, htlits2_l, hnt2_le, htlits2_b, hcov2, hmP2⟩
                    (fun ntQ mQ ⟨tmkQ, tlitsQ, hT⟩ =>
                      iha (ntQ, qs_idx - 1#32, ()) mQ (by dsimp only; rw [hqs1]; omega)
                        ⟨by rw [hqs1]; omega, tmkQ, tlitsQ, hT⟩)
                  · intro qi_n hqi_n
                    change qi_n < st3.scratch.scratch_buf[
                      (2#32 * sc_b + (qs_idx - 1#32)).toNat].toNat at hqi_n
                    have hqi_row : qi_n < (st3.scratch.scratch_buf[
                        2 * fidStepsCap c.scratch_cap + (qs_idx - 1#32).toNat]?.getD
                        0#32).toNat := by
                      rw [List.getElem?_eq_getElem hqn_sc', Option.getD_some]
                      simpa only [hqn_idx, hsc_b] using hqi_n
                    have h := hrow.2.2 qi_n hqi_row
                    have heq_ro' : (st3.scratch.scratch_buf[(sc_b + (qs_idx - 1#32)).toNat]'(by
                          rw [hro_idx, hsc_b]; exact hro_sc')).toNat =
                        (st3.scratch.scratch_buf[fidStepsCap c.scratch_cap +
                          (qs_idx - 1#32).toNat]?.getD 0#32).toNat := by
                      simp only [List.getElem?_eq_getElem hro_sc', Option.getD_some,
                        hro_idx, hsc_b]
                    change Step7RowRefOk st3 (st3.scratch.scratch_buf[
                      (st3.scratch.scratch_buf[(sc_b + (qs_idx - 1#32)).toNat]'(by
                        rw [hro_idx, hsc_b]; exact hro_sc')).toNat + qi_n]?.getD 0#32)
                    rwa [← heq_ro'] at h
                · intro Jp2 hJp2
                  have hlt2 : (st3.scratch.scratch_buf[
                      (BitVec.setWidth 64 (qs_idx - 1#32)).toNat]'hsc_lt64 ^^^ 1#32).toNat <
                      2 * st3.core.cur_vars := by rw [heq_sb]; exact hfneg_lt
                  exact fac13_push_touched_wp hmx hcnl_eq h3_cv_le hlt2
                    ⟨htmk1_l, htlits1_l, hnt1_le, htlits1_b, hcov1, hmP1⟩
                    fun nt' m' hT' => hJp2 (nt', ()) m' hT'
              · intro Jp1 hJp1
                have hlt1 : (st3.scratch.scratch_buf[
                    (BitVec.setWidth 64 (qs_idx - 1#32)).toNat]'hsc_lt64).toNat <
                    2 * st3.core.cur_vars := by rw [heq_sb]; exact hfac_lt
                exact fac13_push_touched_wp hmx hcnl_eq h3_cv_le hlt1
                  ⟨htmk_l, htlits_l, hnt_le, htlits_b, hcov, hmA⟩
                  fun nt' m' hT' => hJp1 (nt', ()) m' hT'
            · clear iha; c0_hfast_nogrp
              have hhsz'_le : (hsz - 1#32).toNat ≤ 2 * st3.core.cur_vars := by omega
              have hhp3 : ∀ i < (hsz - 1#32).toNat,
                  (st3.scratch.tarjan_mark[i]?.getD 0#32).toNat < 2 * st3.core.cur_vars :=
                fun i hi => by rw [htm3]; dsimp only [st2a]; have := hhp2 i hi; omega
              refine fac13_clear_upd_wp hUpd hinv3 htmk_l htlits_l hnt_le htlits_b hcov
                hhsz'_le hhp3 hmA fun hsz_u mU ⟨st_end, hinv_end, hcv_end, hfu_end,
                  hhsz_end, hhp_end, hm_end⟩ =>
                hJs (hsz_u, ()) mU (ihm (st_end, hsz_u) mU
                  (fac13_lex_dec_cv (by dsimp only; rw [hcv_end, ← hcv2_eq]; exact hcv3_gt)
                    hinv_end.1.lengths.core_ok.cur_vars_le (by dsimp only; omega))
                  ⟨by omega, hfu_end.trans (hfu3.trans hfu2), hhsz_end, hinv_end, hhp_end, hm_end⟩)
        · c0_hfast_nogrp
          refine hJs (hsz - 1#32, ()) m3 (ihm (st3, hsz - 1#32) m3 ?_ ?_)
          · rcases Nat.lt_or_eq_of_le (hcv3_le : st2.core.cur_vars ≤ st3.core.cur_vars) with h | h
            · exact fac13_lex_dec_cv (by dsimp only; rw [← hcv2_eq]; exact h)
                hinv3.1.lengths.core_ok.cur_vars_le (by dsimp only; omega)
            · exact hdec_hsz st3 (by rw [← h, hcv2_eq])
          · have hcv3_le' : st2.core.cur_vars ≤ st3.core.cur_vars := hcv3_le
            refine ⟨Nat.le_trans hcv2 hcv3_le', hfu3.trans hfu2, by omega, hinv3, fun i hi => by
              rw [htm3]; dsimp only [st2a]; have := hhp2 i hi; omega, hm3⟩
    · intro Jf hJf
      exact fac13_fheap_pop_wp hDown hhsz_pos hhsz1 hhsz_st hcv_st hfu_st hinv1a
        rfl rfl hhp_st (by assumption) hJf

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
