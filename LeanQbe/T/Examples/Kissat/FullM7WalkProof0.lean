module

public import LeanQbe.T.Examples.Kissat.FullM7Walk
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.C0Agrees
import LeanQbe.T.Examples.Kissat.FullArena

/-!
# Kissat M7 Walk & Warmup Proofs — Part 0 (`FullM7WalkProof0`)

Proves UNSAT-only memory-safety and invariant `Func.wp` contracts (`XPost := False`, `0` SAT
model proofs) for the `10` core-preserving ProbSAT local-search helpers in `FullM7Walk`.
-/

set_option autoImplicit false

local elab "m7_hsteps" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "m7_hsteps_nj" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Walk

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

/-! ## 1. `FullState.LengthsOk` & `FullExtScratchPres` Scratch Helpers -/

section Helpers

private theorem m7_ext_refl (s : FullState) : FullExtScratchPres s s := ⟨rfl, rfl⟩

private theorem m7_ext_trans {s1 s2 s3 : FullState}
    (h12 : FullExtScratchPres s1 s2) (h23 : FullExtScratchPres s2 s3) :
    FullExtScratchPres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.trans h12.2⟩

private theorem m7_len_scrBuf {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {i : Nat} {v : BitVec 32} :
    ({ s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set i v } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with scratch_buf_len := by simp [h.scratch_ok.scratch_buf_len] }⟩

private theorem m7_len_wvals {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {i : Nat} {v : BitVec 8} :
    ({ s with scratch := { s.scratch with walk_vals := s.scratch.walk_vals.set i v } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with walk_vals_len := by simp [h.scratch_ok.walk_vals_len] }⟩

private theorem m7_len_wbest {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {i : Nat} {v : BitVec 8} :
    ({ s with scratch := { s.scratch with walk_best := s.scratch.walk_best.set i v } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with walk_best_len := by simp [h.scratch_ok.walk_best_len] }⟩

private theorem m7_len_phases {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {i : Nat} {v : BitVec 8} :
    ({ s with scratch := { s.scratch with phases := s.scratch.phases.set i v } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with phases_len := by simp [h.scratch_ok.phases_len] }⟩

private theorem m7_len_trc {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {i : Nat} {v : BitVec 32} :
    ({ s with scratch := { s.scratch with tarjan_reach := s.scratch.tarjan_reach.set i v } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with tarjan_reach_len := by simp [h.scratch_ok.tarjan_reach_len] }⟩

private theorem m7_len_tmk {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {i : Nat} {v : BitVec 32} :
    ({ s with scratch := { s.scratch with tarjan_mark := s.scratch.tarjan_mark.set i v } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with tarjan_mark_len := by simp [h.scratch_ok.tarjan_mark_len] }⟩

private theorem m7_len_wsort {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {i : Nat} {v : BitVec 32} :
    ({ s with scratch := { s.scratch with wsort := s.scratch.wsort.set i v } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with wsort_len := by simp [h.scratch_ok.wsort_len] }⟩

private theorem m7_len_wk1 {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {i : Nat} {v : BitVec 32} :
    ({ s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set i v } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with work_stk1_len := by simp [h.scratch_ok.work_stk1_len] }⟩

private theorem m7_len_wk2 {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {i : Nat} {v : BitVec 32} :
    ({ s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set i v } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with work_stk2_len := by simp [h.scratch_ok.work_stk2_len] }⟩

private theorem m7_bv64_shl1_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 63) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega

private theorem m7_bv64_shl1_or1_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 63) :
    ((x <<< (1 : Nat)) ||| 1#64).toNat = 2 * x.toNat + 1 := by
  have hs := m7_bv64_shl1_toNat hx
  rw [BitVec.toNat_or, hs, show (1#64 : BitVec 64).toNat = 1 from rfl]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    simp [Nat.testBit_succ, show (2 * x.toNat + 1) / 2 = x.toNat by omega,
      show (2 * x.toNat) / 2 = x.toNat by omega]

private theorem m7_bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem m7_bv32_xor1_lt {x : BitVec 32} {n : Nat} (hx : x.toNat < 2 * n) :
    (x ^^^ 1#32).toNat < 2 * n := by
  have h1 : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := rfl
  rw [h1]
  exact litNeg_lt_two_mul hx

private theorem m7_bv64_zext32_lt {x : BitVec 32} {ub : Nat} (hx : x.toNat < ub) :
    (x.setWidth 64).toNat < ub := by
  rwa [zext_toNat x (by decide)]

private theorem m7_sext16_mod : ((16 : BitVec 32).signExtend 64).toNat % 64 = 16 := by decide
private theorem m7_sext1_mod : ((1 : BitVec 32).signExtend 64).toNat % 64 = 1 := by decide
private theorem m7_sext2_mod : ((2 : BitVec 32).signExtend 64).toNat % 64 = 2 := by decide
private theorem m7_sext32_mod : ((32 : BitVec 32).signExtend 64).toNat % 64 = 32 := by decide

private theorem m7_pos_of_bv64_ofNat_ne0 {n : Nat} (hb : n < 2 ^ 64)
    (hne : BitVec.ofNat 64 n ≠ 0#64) : 0 < n := by
  have h0 : (BitVec.ofNat 64 n).toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
  rw [bv64_ofNat_toNat hb] at h0; omega

private theorem m7_lt_of_bv64_ofNat_lt {x : BitVec 64} {n : Nat} (hb : n < 2 ^ 64)
    (hlt : x < BitVec.ofNat 64 n) : x.toNat < n := by
  have h : x.toNat < (BitVec.ofNat 64 n).toNat := hlt
  rwa [bv64_ofNat_toNat hb] at h

private theorem m7_le_of_not_bv64_ofNat_lt {n : Nat} {x : BitVec 64} (hb : n < 2 ^ 64)
    (h : ¬ BitVec.ofNat 64 n < x) : x.toNat ≤ n := by
  have h1 : ¬ n < x.toNat := by
    intro hlt; apply h
    change (BitVec.ofNat 64 n).toNat < x.toNat
    rwa [bv64_ofNat_toNat hb]
  exact Nat.le_of_not_lt h1

private theorem m7_bv64_pack32_lo_and (hi cur : BitVec 64) :
    (((hi <<< (32 : Nat)) ||| (cur &&& 0xFFFFFFFF#64)) &&& 0xFFFFFFFF#64).toNat ≤
      cur.toNat := by
  have hzero : (hi <<< (32 : Nat)) &&& 0xFFFFFFFF#64 = 0#64 := by
    ext i hi_lt
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_zero]
    by_cases h32 : i < 32
    · simp [h32]
    · have hf : (0xFFFFFFFF#64 : BitVec 64)[i] = false := by
        rw [BitVec.getElem_eq_testBit_toNat, show (0xFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 32 - 1
          from rfl, Nat.testBit_two_pow_sub_one]; simp [h32]
      simp [hf]
  rw [BitVec.and_comm _ 0xFFFFFFFF#64, BitVec.and_or_distrib_left,
    BitVec.and_comm 0xFFFFFFFF#64 _, hzero, BitVec.zero_or,
    BitVec.and_comm 0xFFFFFFFF#64 _, BitVec.and_assoc,
    show (0xFFFFFFFF#64 &&& 0xFFFFFFFF#64 : BitVec 64) = 0xFFFFFFFF#64 by decide,
    BitVec.toNat_and]
  exact Nat.and_le_left

private theorem m7_bv64_and_lo32_le (x : BitVec 64) : (x &&& 0xFFFFFFFF#64).toNat ≤ x.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_left

private theorem m7_state_abs (s : FullState) {c : FullCfg} {s_new : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s_new ⋆ R) m) (hc : PreservesCoreSlice FullState.core s s_new)
    (hl : s_new.LengthsOk c) (he : FullExtScratchPres s s_new) :
    ∃ st : FullState, PreservesCoreSlice FullState.core s st ∧
      st.LengthsOk c ∧ FullExtScratchPres s st ∧ (FullMem c st ⋆ R) m :=
  ⟨s_new, hc, hl, he, hm⟩

private theorem m7_rem1_mod {ncl cap mk : Nat} (h5 : 32 + 5 * ncl ≤ cap) (hc : cap < 2 ^ 28)
    (hle : mk ≤ (2 ^ 64 - (32 + 2 * ncl + ncl + ncl + ncl) % 2 ^ 64 + cap) % 2 ^ 64) :
    mk ≤ cap - (32 + 5 * ncl) := by
  have hb : (32 + 2 * ncl + ncl + ncl + ncl) % 2 ^ 64 = 32 + 5 * ncl := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [hb, show 2 ^ 64 - (32 + 5 * ncl) + cap = (cap - (32 + 5 * ncl)) + 1 * 2 ^ 64 by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)] at hle
  exact hle

private theorem m7_rem2_mod {ncl cap mk r : Nat} (h5 : 32 + 5 * ncl ≤ cap) (hc : cap < 2 ^ 28)
    (hmk : mk ≤ cap - (32 + 5 * ncl))
    (hle : ¬ (2 ^ 64 - mk + (2 ^ 64 - (32 + 2 * ncl + ncl + ncl + ncl) % 2 ^ 64 + cap)) %
      2 ^ 64 < r) :
    r ≤ cap - (32 + 5 * ncl) - mk := by
  have hb : (32 + 2 * ncl + ncl + ncl + ncl) % 2 ^ 64 = 32 + 5 * ncl := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [hb, show 2 ^ 64 - mk + (2 ^ 64 - (32 + 5 * ncl) + cap) =
      (cap - (32 + 5 * ncl) - mk) + 2 * 2 ^ 64 by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)] at hle
  omega

private theorem m7_ext_scrBuf (s : FullState) (b : List (BitVec 32)) :
    FullExtScratchPres s { s with scratch := { s.scratch with scratch_buf := b } } :=
  m7_ext_refl s

private theorem m7_bv64_sub1_toNat {x : BitVec 64} (hx : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#64 : BitVec 64).toNat = 1 from rfl,
    show 2 ^ 64 - 1 + x.toNat = (x.toNat - 1) + 1 * 2 ^ 64 by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

private theorem m7_sub1_le {cu ncl : BitVec 64} (hpos : 0 < cu.toNat) (hle : cu.toNat ≤ ncl.toNat) :
    (cu - 1#64).toNat ≤ ncl.toNat := by
  rw [m7_bv64_sub1_toNat hpos]; omega

private theorem m7_zext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)

private theorem m7_rem_sub_le {ncl cap : Nat} {bv_ncl mk : BitVec 64}
    (hn : bv_ncl.toNat = ncl) (h5 : 32 + 5 * ncl ≤ cap) (hc : cap < 2 ^ 28)
    (hmk : mk.toNat ≤ cap - (32 + 5 * ncl)) :
    (BitVec.ofNat 64 cap - (32#64 + (bv_ncl <<< (1 : Nat)) + bv_ncl + bv_ncl + bv_ncl) -
      mk).toNat ≤ cap - (32 + 5 * ncl) - mk.toNat := by
  subst hn
  have hsh : (bv_ncl <<< (1 : Nat)).toNat = 2 * bv_ncl.toNat := m7_bv64_shl1_toNat (by omega)
  have hbase : (32#64 + (bv_ncl <<< (1 : Nat)) + bv_ncl + bv_ncl + bv_ncl).toNat =
      32 + 5 * bv_ncl.toNat := by
    simp only [BitVec.toNat_add, show (32#64 : BitVec 64).toNat = 32 from rfl, hsh,
      Nat.mod_add_mod]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hcap : (BitVec.ofNat 64 cap).toNat = cap := bv64_ofNat_toNat (by omega)
  have h1 : (BitVec.ofNat 64 cap -
      (32#64 + (bv_ncl <<< (1 : Nat)) + bv_ncl + bv_ncl + bv_ncl)).toNat =
      cap - (32 + 5 * bv_ncl.toNat) := by
    rw [BitVec.toNat_sub, hcap, hbase,
      show 2 ^ 64 - (32 + 5 * bv_ncl.toNat) + cap =
        (cap - (32 + 5 * bv_ncl.toNat)) + 1 * 2 ^ 64 by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub, h1,
    show 2 ^ 64 - mk.toNat + (cap - (32 + 5 * bv_ncl.toNat)) =
      (cap - (32 + 5 * bv_ncl.toNat) - mk.toNat) + 1 * 2 ^ 64 by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  exact Nat.le_refl _

private theorem m7_cb_piece_le {base coef lo hi avg : BitVec 64}
    (hb : base.toNat ≤ 4000) (hc : coef.toNat ≤ 2500)
    (h1 : lo.toNat ≤ avg.toNat) (h2 : avg.toNat < hi.toNat)
    (hd : hi.toNat - lo.toNat ≤ 65536) :
    (base + ((coef * (avg - lo)) >>> (16 : Nat))).toNat ≤ 600000 := by
  have hsub : (avg - lo).toNat < 65536 := by
    rw [BitVec.toNat_sub]; have := avg.isLt; have := lo.isLt; omega
  have hprod : (coef * (avg - lo)).toNat ≤ 2500 * 65536 := by
    have hm := Nat.mul_le_mul hc (Nat.le_of_lt hsub)
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]; exact hm
  have hsh : ((coef * (avg - lo)) >>> (16 : Nat)).toNat ≤ 2500 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  rw [BitVec.toNat_add]; omega

end Helpers

/-! ## 2. Specification Contracts & `*_call` Bridges (`10` Walk Helpers) -/

section Specs

def m7CbInvSpec : Spec [i64, i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _ncl, _tot, ()) _ => h = c.hdr)
    (fun _ (_, ncl, _tot, ()) (r, ()) s s' =>
      s' = s ∧ 1 ≤ r.toNat ∧ r.toNat ≤ 32768 ∧
      (((s.scratch.walk_cnt_stat &&& 1#64) = 0#64 ∨ ncl = 0#64) → r = 32768#64))

/-- Generalized callback-inversion specification without the parity/32768 clause. -/
def step7CbInvSpec : Spec [i64, i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _ncl, _tot, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' => s' = s ∧ 1 ≤ r.toNat ∧ r.toNat ≤ 32768)

theorem step7CbInvSpec_noExit : ∀ a m Q X,
    step7CbInvSpec a m Q X → step7CbInvSpec a m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ ⟨c, s, R, hp, hs, hm, hQ⟩ => ⟨c, s, R, hp, hs, hm, hQ⟩

theorem step7CbInvSpec_to_m7 {a m Q X} (h : step7CbInvSpec a m Q X) : m7CbInvSpec a m Q X := by
  rcases h with ⟨c, s, R, hpre, hsafe, hm, hQ⟩
  exact ⟨c, s, R, hpre, hsafe, hm, fun ret s' m' hcore hs' ⟨hs, h1, h2, _⟩ hm' =>
    hQ ret s' m' hcore hs' ⟨hs, h1, h2⟩ hm'⟩

def m7InitTableSpec : Spec [i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _iq, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

def m7InitTableMonoSpec : Spec [i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, iq, ()) _ => h = c.hdr ∧ 32 ≤ c.scratch_cap ∧
      1 ≤ iq.toNat ∧ iq.toNat ≤ 32768)
    (fun _ _ _ s s' => FullExtScratchPres s s' ∧
      (s'.scratch.scratch_buf[0]?.getD 0#32).toNat = 2 ^ 30 ∧
      (∀ i < 32, 1 ≤ (s'.scratch.scratch_buf[i]?.getD 0#32).toNat ∧
        (s'.scratch.scratch_buf[i]?.getD 0#32).toNat ≤ 2 ^ 30) ∧
      (∀ i < 31, (s'.scratch.scratch_buf[i + 1]?.getD 0#32).toNat ≤
        (s'.scratch.scratch_buf[i]?.getD 0#32).toNat))

def m7EffortSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _mf, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' => s' = s ∧ 500000 ≤ r.toNat ∧ r.toNat ≤ 40000000)

def m7InitValsSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

def m7CollectSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

def m7BuildOccSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _ncl, ()) _ => h = c.hdr)
    (fun _ (_, ncl, ()) (r, ()) s s' => FullExtScratchPres s s' ∧ r.toNat ≤ ncl.toNat)

def m7BreakSpec : Spec [i64, i32, i64] [i32] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _nl, _ncl, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s' = s)

def m7PickSpec : Spec [i64, i32, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _cl, _ncl, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

def m7FlipSpec : Spec [i64, i32, i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _fl, _ncl, _ul, ()) _ => h = c.hdr)
    (fun _ (_, _, ncl, _, ()) (r, ()) s s' =>
      FullExtScratchPres s s' ∧ (r &&& 0xFFFFFFFF#64).toNat ≤ ncl.toNat)

def m7SaveMinSpec : Spec [i64, i64, .bool] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _bp, _ok, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

theorem m7CbInv_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hFn : ∀ a m Q X, m7CbInvSpec a m Q X →
      Γ "full_walk_cb_inv_m7" [i64, i64, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r m', 1 ≤ r.toNat → r.toNat ≤ 32768 →
      (FullMem c s ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_cb_inv_m7" args k) m := by
  refine wp_call_of_spec args k (hFn _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ s' m' _ _ ⟨rfl, h1, h2, _⟩ hm'
  exact hk r m' h1 h2 hm'

theorem step7CbInv_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hFn : ∀ a m Q X, step7CbInvSpec a m Q X →
      Γ "full_walk_cb_inv_m7" [i64, i64, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r m', 1 ≤ r.toNat → r.toNat ≤ 32768 →
      (FullMem c s ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_cb_inv_m7" args k) m := by
  refine wp_call_of_spec args k (hFn _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ s' m' _ _ ⟨rfl, h1, h2⟩ hm'
  exact hk r m' h1 h2 hm'

theorem m7InitTable_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hFn : ∀ a m Q X, m7InitTableSpec a m Q X →
      Γ "full_walk_init_table_m7" [i64, i64] [] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_walk_init_table_m7" args k) m := by
  refine wp_call_of_spec args k (hFn _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro _ s' m' hcore hs' hext hm'
  exact hk s' m' hcore hs' hext hm'

theorem m7Effort_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hFn : ∀ a m Q X, m7EffortSpec a m Q X → Γ "full_walk_effort_m7" [i64, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r m', 500000 ≤ r.toNat → r.toNat ≤ 40000000 →
      (FullMem c s ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_effort_m7" args k) m := by
  refine wp_call_of_spec args k (hFn _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ _ m' _ _ ⟨rfl, h1, h2⟩ hm'
  exact hk r m' h1 h2 hm'

theorem m7InitVals_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hFn : ∀ a m Q X, m7InitValsSpec a m Q X → Γ "full_walk_init_vals_m7" [i64] [] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_walk_init_vals_m7" args k) m := by
  refine wp_call_of_spec args k (hFn _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro _ s' m' hcore hs' hext hm'
  exact hk s' m' hcore hs' hext hm'

theorem m7Collect_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hFn : ∀ a m Q X, m7CollectSpec a m Q X → Γ "full_walk_collect_m7" [i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_collect_m7" args k) m := by
  refine wp_call_of_spec args k (hFn _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ s' m' hcore hs' hext hm'
  exact hk r s' m' hcore hs' hext hm'

theorem m7BuildOcc_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hFn : ∀ a m Q X, m7BuildOccSpec a m Q X →
      Γ "full_walk_build_occ_m7" [i64, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      r.toNat ≤ args.2.1.val.toNat → (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_build_occ_m7" args k) m := by
  refine wp_call_of_spec args k (hFn _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ s' m' hcore hs' ⟨hext, hle⟩ hm'
  exact hk r s' m' hcore hs' hext hle hm'

theorem m7Break_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i32, i64]} {k : Tup Val [i32] → Expr Val Cont rs}
    (hFn : ∀ a m Q X, m7BreakSpec a m Q X → Γ "full_walk_break_m7" [i64, i32, i64] [i32] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r m', (FullMem c s ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_break_m7" args k) m := by
  refine wp_call_of_spec args k (hFn _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ _ m' _ _ rfl hm'
  exact hk r m' hm'

theorem m7Pick_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i32, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hFn : ∀ a m Q X, m7PickSpec a m Q X → Γ "full_walk_pick_m7" [i64, i32, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_pick_m7" args k) m := by
  refine wp_call_of_spec args k (hFn _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ s' m' hcore hs' hext hm'
  exact hk r s' m' hcore hs' hext hm'

theorem m7Flip_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i32, i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hFn : ∀ a m Q X, m7FlipSpec a m Q X →
      Γ "full_walk_flip_m7" [i64, i32, i64, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (r &&& 0xFFFFFFFF#64).toNat ≤ args.2.2.1.val.toNat →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_walk_flip_m7" args k) m := by
  refine wp_call_of_spec args k (hFn _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro ⟨r, ⟨⟩⟩ s' m' hcore hs' ⟨hext, hle⟩ hm'
  exact hk r s' m' hcore hs' hext hle hm'

theorem m7SaveMin_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64, .bool]} {k : Tup Val [] → Expr Val Cont rs}
    (hFn : ∀ a m Q X, m7SaveMinSpec a m Q X →
      Γ "full_walk_save_min_m7" [i64, i64, .bool] [] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.1.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_walk_save_min_m7" args k) m := by
  refine wp_call_of_spec args k (hFn _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  intro _ s' m' hcore hs' hext hm'
  exact hk s' m' hcore hs' hext hm'

end Specs

/-! ## 3. Helpers 1..4: `cb_inv`, `init_table`, `effort`, `init_vals` -/

section HelpersPart1

theorem full_walk_cb_inv_m7_wp (Γ : Env) :
    ∀ a m Q X, m7CbInvSpec a m Q X → Func.wp Γ full_walk_cb_inv_m7_body a m Q X := by
  rintro ⟨h, ncl, tot_lits, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hret_def : (s.scratch.walk_cnt_stat &&& 1#64) = 0#64 ∨ ncl = 0#64 →
      Q (32768#64, ()) m := fun hcond =>
    hQ (32768#64, ()) s m rfl hlen ⟨rfl, by decide, by decide, fun _ => rfl⟩ hm
  m7_hsteps_nj
  · exact hret_def (Or.inl ‹_›)
  · exact hret_def (Or.inr ‹_›)
  · have hodd : ¬ (s.scratch.walk_cnt_stat &&& 1#64) = 0#64 := ‹_›
    have hncl_ne : ncl ≠ 0#64 := ‹_›
    refine wp_join_group (ts := [i64]) (fun (occ, ()) m1 =>
        (FullMem c s ⋆ R) m1 ∧ occ.toNat ≤ 0x0000FFFFFFFFFFFF) ?_ ?_
    · rintro _ ⟨occ, ⟨⟩⟩ m1 ⟨hm1, hocc_le⟩
      m7_hsteps_nj
      refine wp_join_group (ts := [i64]) (fun (cb, ()) m2 =>
          (FullMem c s ⋆ R) m2 ∧ cb.toNat ≤ 600000) ?_ ?_
      · rintro _ ⟨cb, ⟨⟩⟩ m2 ⟨hm2, hcb_ub⟩
        m7_hsteps_nj
        refine wp_join_group (ts := [i64]) (fun (cb', ()) m3 =>
            (FullMem c s ⋆ R) m3 ∧ 2000 ≤ cb'.toNat ∧ cb'.toNat ≤ 600000) ?_ ?_
        · rintro _ ⟨cb', ⟨⟩⟩ m3 ⟨hm3, hcb1, hcb2⟩
          have hcb'_ne : cb' ≠ 0#64 := by
            intro hz; have := congrArg BitVec.toNat hz; simp at this; omega
          m7_hsteps_nj
          refine wp_join_group (ts := [i64]) (fun (inv, ()) m4 =>
              (FullMem c s ⋆ R) m4 ∧ 1 ≤ inv.toNat ∧ inv.toNat ≤ 65536) ?_ ?_
          · rintro _ ⟨inv, ⟨⟩⟩ m4 ⟨hm4, hinv1, hinv2⟩
            m7_hsteps_nj
            refine wp_join_group (ts := [i64]) (fun (inv', ()) m5 =>
                (FullMem c s ⋆ R) m5 ∧ 1 ≤ inv'.toNat ∧ inv'.toNat ≤ 32768) ?_ ?_
            · rintro _ ⟨inv', ⟨⟩⟩ m5 ⟨hm5, hi1, hi2⟩
              m7_hsteps_nj
              exact hQ (inv', ()) s m5 rfl hlen ⟨rfl, hi1, hi2,
                fun hc => by rcases hc with hc | hc <;> exact absurd hc ‹_›⟩ hm5
            · intro Jf hJf; m7_hsteps_nj
              · exact hJf (32768#64, ()) m4 ⟨hm4, by decide, by decide⟩
              · exact hJf (inv, ()) m4 ⟨hm4, hinv1, by c0_bound⟩
          · intro Ji hJi; m7_hsteps_nj
            · exact hJi (1#64, ()) m3 ⟨hm3, by decide, by decide⟩
            · have hnum_le : ((65536000 : BitVec 64) + cb' >>> (1 : Nat)).toNat ≤ 65836000 := by
                c0_bound
              have hdiv_le :
                  (((65536000 : BitVec 64) + cb' >>> (1 : Nat)) / cb').toNat ≤ 65536 := by
                rw [BitVec.toNat_udiv]
                have hmul : 65836000 ≤ cb'.toNat * 65536 :=
                  Nat.le_trans (show 65836000 ≤ 2000 * 65536 by decide)
                    (Nat.mul_le_mul_right 65536 hcb1)
                exact Nat.div_le_of_le_mul (Nat.le_trans hnum_le hmul)
              have hnz : (((65536000 : BitVec 64) + cb' >>> (1 : Nat)) / cb') ≠ 0#64 := ‹_›
              have hpos : 1 ≤ (((65536000 : BitVec 64) + cb' >>> (1 : Nat)) / cb').toNat :=
                Nat.pos_of_ne_zero fun h0 => hnz (BitVec.eq_of_toNat_eq h0)
              exact hJi (_, ()) m3 ⟨hm3, hpos, hdiv_le⟩
        · intro Jc hJc; m7_hsteps_nj
          · exact hJc (2000#64, ()) m2 ⟨hm2, by decide, by decide⟩
          · exact hJc (cb, ()) m2 ⟨hm2, by c0_bound, hcb_ub⟩
      · intro Jb hJb; m7_hsteps_nj
        · have havg_lt : (occ <<< (16 : Nat) / ncl).toNat < 196608 := by c0_bound
          have hm500 : (500#64 * (occ <<< (16 : Nat) / ncl)).toNat < 500 * 196608 := by
            rw [BitVec.toNat_mul, show (500#64 : BitVec 64).toNat = 500 from rfl,
              Nat.mod_eq_of_lt (by omega)]; omega
          have hd : (500#64 * (occ <<< (16 : Nat) / ncl) / 196608#64).toNat ≤ 500 := by
            rw [BitVec.toNat_udiv, show (196608#64 : BitVec 64).toNat = 196608 from rfl]
            omega
          have hcb_le :
              (2000#64 + 500#64 * (occ <<< (16 : Nat) / ncl) / 196608#64).toNat ≤ 600000 := by
            rw [BitVec.toNat_add, show (2000#64 : BitVec 64).toNat = 2000 from rfl]; omega
          exact hJb (_, ()) m1 ⟨hm1, hcb_le⟩
        · refine wp_join_group (ts := [i64]) (fun (cb1, ()) m2 =>
              (FullMem c s ⋆ R) m2 ∧ cb1.toNat ≤ 600000)
            (fun _ ⟨cb1, ⟨⟩⟩ m2 hm2 => hJb (cb1, ()) m2 hm2) ?_
          intro Jb1 hJb1; m7_hsteps_nj
          · exact hJb1 (_, ()) m1 ⟨hm1, m7_cb_piece_le (base := 2500#64) (coef := 350#64)
              (lo := 196608#64) (hi := 262144#64) (by decide) (by decide)
              (by c0_bound) (by c0_bound) (by decide)⟩
          · refine wp_join_group (ts := [i64]) (fun (cb2, ()) m2 =>
                (FullMem c s ⋆ R) m2 ∧ cb2.toNat ≤ 600000)
              (fun _ ⟨cb2, ⟨⟩⟩ m2 hm2 => hJb1 (cb2, ()) m2 hm2) ?_
            intro Jb2 hJb2; m7_hsteps_nj
            · exact hJb2 (_, ()) m1 ⟨hm1, m7_cb_piece_le (base := 2850#64) (coef := 850#64)
                (lo := 262144#64) (hi := 327680#64) (by decide) (by decide)
                (by c0_bound) (by c0_bound) (by decide)⟩
            · refine wp_join_group (ts := [i64]) (fun (cb3, ()) m2 =>
                  (FullMem c s ⋆ R) m2 ∧ cb3.toNat ≤ 600000)
                (fun _ ⟨cb3, ⟨⟩⟩ m2 hm2 => hJb2 (cb3, ()) m2 hm2) ?_
              intro Jb3 hJb3; m7_hsteps_nj
              · exact hJb3 (_, ()) m1 ⟨hm1, m7_cb_piece_le (base := 3700#64) (coef := 1400#64)
                  (lo := 327680#64) (hi := 393216#64) (by decide) (by decide)
                  (by c0_bound) (by c0_bound) (by decide)⟩
              · refine wp_join_group (ts := [i64]) (fun (ex, ()) m2 =>
                    (FullMem c s ⋆ R) m2 ∧ ex.toNat ≤ 2621440) ?_ ?_
                · rintro _ ⟨ex, ⟨⟩⟩ m2 ⟨hm2, hex⟩
                  m7_hsteps_nj
                  have hr_le : (((2300 : BitVec 64) * ex) >>> (16 : Nat)).toNat ≤ 92000 := by
                    rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul,
                      show (2300 : BitVec 64).toNat = 2300 from rfl,
                      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]; omega
                  have hcb5 :
                      (5100#64 + (((2300 : BitVec 64) * ex) >>> (16 : Nat))).toNat ≤ 600000 := by
                    rw [BitVec.toNat_add, show (5100#64 : BitVec 64).toNat = 5100 from rfl]; omega
                  exact hJb3 (_, ()) m2 ⟨hm2, hcb5⟩
                · intro Jex hJex; m7_hsteps_nj
                  · exact hJex (2621440#64, ()) m1 ⟨hm1, by decide⟩
                  · exact hJex (_, ()) m1 ⟨hm1, by c0_bound⟩
    · intro Jo hJo; m7_hsteps_nj
      · exact hJo (0x0000FFFFFFFFFFFF#64, ()) m ⟨hm, by decide⟩
      · exact hJo (tot_lits, ()) m ⟨hm, by c0_bound⟩

theorem full_walk_effort_m7_wp (Γ : Env) :
    ∀ a m Q X, m7EffortSpec a m Q X → Func.wp Γ full_walk_effort_m7_body a m Q X := by
  rintro ⟨h, max_flips, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  m7_hsteps_nj
  refine wp_join_group (ts := [i64]) (fun (dt, ()) m1 => (FullMem c s ⋆ R) m1) ?_ ?_
  · rintro _ ⟨dt, ⟨⟩⟩ m1 hm1
    m7_hsteps_nj
    refine wp_join_group (ts := [i64]) (fun (eff, ()) m2 =>
        (FullMem c s ⋆ R) m2 ∧ eff.toNat ≤ 40000000) ?_ ?_
    · rintro _ ⟨eff, ⟨⟩⟩ m2 ⟨hm2, heff⟩
      m7_hsteps_nj
      refine wp_join_group (ts := [i64]) (fun (mf, ()) m3 =>
          (FullMem c s ⋆ R) m3 ∧ mf.toNat ≤ 4096) ?_ ?_
      · rintro _ ⟨mf, ⟨⟩⟩ m3 ⟨hm3, hmf⟩
        m7_hsteps_nj
        refine wp_join_group (ts := [i64]) (fun (flr, ()) m4 =>
            (FullMem c s ⋆ R) m4 ∧ 500000 ≤ flr.toNat ∧ flr.toNat ≤ 8388608) ?_ ?_
        · rintro _ ⟨flr, ⟨⟩⟩ m4 ⟨hm4, hfl1, hfl2⟩
          m7_hsteps_nj
          refine wp_join_group (ts := [i64]) (fun (eff2, ()) m5 =>
              (FullMem c s ⋆ R) m5 ∧ 500000 ≤ eff2.toNat ∧ eff2.toNat ≤ 40000000) ?_ ?_
          · rintro _ ⟨eff2, ⟨⟩⟩ m5 ⟨hm5, he1, he2⟩
            m7_hsteps_nj
            refine wp_join_group (ts := [i64]) (fun (eff3, ()) m6 =>
                (FullMem c s ⋆ R) m6 ∧ 500000 ≤ eff3.toNat ∧ eff3.toNat ≤ 40000000) ?_ ?_
            · rintro _ ⟨eff3, ⟨⟩⟩ m6 ⟨hm6, hf1, hf2⟩
              m7_hsteps_nj
              exact hQ (eff3, ()) s m6 rfl hlen ⟨rfl, hf1, hf2⟩ hm6
            · intro J3 hJ3; m7_hsteps_nj
              · exact hJ3 (40000000#64, ()) m5 ⟨hm5, by decide, by decide⟩
              · exact hJ3 (eff2, ()) m5 ⟨hm5, he1, he2⟩
          · intro J2 hJ2; m7_hsteps_nj
            · exact hJ2 (flr, ()) m4 ⟨hm4, hfl1, by omega⟩
            · exact hJ2 (eff, ()) m4 ⟨hm4, by c0_bound, heff⟩
        · intro Jflr hJflr; m7_hsteps_nj
          · exact hJflr (500000#64, ()) m3 ⟨hm3, by decide, by decide⟩
          · exact hJflr (_, ()) m3 ⟨hm3, by c0_bound, by c0_bound⟩
      · intro Jmf hJmf; m7_hsteps_nj
        · exact hJmf (4096#64, ()) m2 ⟨hm2, by decide⟩
        · exact hJmf (max_flips, ()) m2 ⟨hm2, by c0_bound⟩
    · intro Je hJe; m7_hsteps_nj
      · have hdt : dt.toNat ≤ 800000000 := by c0_bound
        have hdiv : (dt / 20#64).toNat ≤ 40000000 := by
          rw [BitVec.toNat_udiv, show (20#64 : BitVec 64).toNat = 20 from rfl]; omega
        exact hJe (_, ()) m1 ⟨hm1, hdiv⟩
      · exact hJe (40000000#64, ()) m1 ⟨hm1, by decide⟩
  · intro Jdt hJdt; m7_hsteps_nj <;> exact hJdt (_, ()) m hm

private theorem full_walk_init_table_m7_core (Γ : Env)
    (c : FullCfg) (iq : BitVec 64) (s : FullState) (R : Mem 64 → Prop) (m : Mem 64)
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m) :
    Func.wp Γ full_walk_init_table_m7_body (c.hdr, iq, ()) m
      (fun () m' => ∃ s' : FullState, PreservesCoreSlice FullState.core s s' ∧
        s'.LengthsOk c ∧ FullExtScratchPres s s' ∧
        (32 ≤ c.scratch_cap → 1 ≤ iq.toNat → iq.toNat ≤ 32768 →
          (s'.scratch.scratch_buf[0]?.getD 0#32).toNat = 2 ^ 30 ∧
          (∀ i < 32, 1 ≤ (s'.scratch.scratch_buf[i]?.getD 0#32).toNat ∧
            (s'.scratch.scratch_buf[i]?.getD 0#32).toNat ≤ 2 ^ 30) ∧
          (∀ i < 31, (s'.scratch.scratch_buf[i + 1]?.getD 0#32).toNat ≤
            (s'.scratch.scratch_buf[i]?.getD 0#32).toNat)) ∧
        (FullMem c s' ⋆ R) m')
      (fun _ _ _ _ => False) := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  m7_hsteps_nj
  · exact ⟨s, rfl, hlen, m7_ext_refl s, fun h32 => by c0_bound, hm⟩
  · have h32 : 32 ≤ c.scratch_cap := by c0_bound
    refine wp_join_group (ts := [i64]) (fun (iqc, ()) m1 => (FullMem c s ⋆ R) m1 ∧
        iqc.toNat ≤ 32768 ∧ (iq.toNat ≤ 32768 → iqc = iq)) ?_ ?_
    · rintro _ ⟨iqc, ⟨⟩⟩ m1 ⟨hm1, hiq_le, hiq_eq⟩
      m7_hsteps_nj
      refine wp_loop_safety_slice_pure (ts := [i64, i64]) (fullSafetySlice c) s R
        (fun st (sc, i, ()) => i.toNat ≤ 32 ∧ FullExtScratchPres s st ∧
          1 ≤ sc.toNat ∧ sc.toNat ≤ 2 ^ 30 ∧
          (i.toNat = 0 → sc.toNat = 2 ^ 30) ∧
          (0 < i.toNat → sc.toNat ≤ (st.scratch.scratch_buf[i.toNat - 1]?.getD 0#32).toNat) ∧
          (∀ j < i.toNat, 1 ≤ (st.scratch.scratch_buf[j]?.getD 0#32).toNat ∧
            (st.scratch.scratch_buf[j]?.getD 0#32).toNat ≤ 2 ^ 30) ∧
          (∀ j, j + 1 < i.toNat → (st.scratch.scratch_buf[j + 1]?.getD 0#32).toNat ≤
            (st.scratch.scratch_buf[j]?.getD 0#32).toNat) ∧
          (∀ j < i.toNat, j = 0 → (st.scratch.scratch_buf[0]?.getD 0#32).toNat = 2 ^ 30))
        (fun (_sc, i, ()) => 32 - i.toNat) ?_ ?_
      · intro J hJ; m7_hsteps_nj
        exact hJ s (1#64 <<< (((30 : BitVec 32).signExtend 64).toNat % 64), 0#64, ()) m1 hm1 rfl
          hlen ⟨Nat.zero_le _, m7_ext_refl s, by decide, by decide, fun _ => by decide,
            fun h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h,
            fun _ h => by simp at h⟩
      · rintro J st ⟨sc, i, ⟨⟩⟩ ml hcore hlen'
          ⟨hi_le, hext, hsc1, hsc2, hsc_z, hsc_prev, hrng, hmono, h0eq⟩ hml ih
        dsimp only [fullSafetySlice] at hcore hlen' hml
        have hsbl := hlen'.scratch_ok.scratch_buf_len
        m7_hsteps_nj
        · have hi_lt : i.toNat < 32 := by c0_bound
          have hi_len : i.toNat < st.scratch.scratch_buf.length := by rw [hsbl]; omega
          let st' : FullState := { st with scratch := { st.scratch with
            scratch_buf := st.scratch.scratch_buf.set i.toNat (sc.setWidth 32) } }
          have hcore1 : PreservesCoreSlice (fullSafetySlice c).coreProj st st' := rfl
          have hlen1 : (fullSafetySlice c).safe st' := m7_len_scrBuf hlen'
          have hsc_t32 : (sc.setWidth 32).toNat = sc.toNat := by
            rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
          have hprod : sc.toNat * iqc.toNat ≤ 2 ^ 30 * 32768 := Nat.mul_le_mul hsc2 hiq_le
          have hprod_le : sc.toNat * iqc.toNat ≤ sc.toNat * 32768 :=
            Nat.mul_le_mul_left _ hiq_le
          have hmul_val : ((sc * iqc) >>> (16 : Nat)).toNat ≤ sc.toNat / 2 := by
            rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega),
              Nat.shiftRight_eq_div_pow]
            have hd : sc.toNat * iqc.toNat / 2 ^ 16 ≤ sc.toNat * 32768 / 2 ^ 16 :=
              Nat.div_le_div_right hprod_le
            omega
          m7_hsteps_nj
          refine wp_join_group (ts := [i64]) (fun (sc', ()) m' =>
              (FullMem c st' ⋆ R) m' ∧ 1 ≤ sc'.toNat ∧ sc'.toNat ≤ sc.toNat) ?_ ?_
          · rintro _ ⟨sc', ⟨⟩⟩ m' ⟨hm', hsc1', hsc2'⟩
            m7_hsteps_nj
            have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
            refine ih st' (sc', i + 1#64, ()) m' hm' (by dsimp only; omega) hcore1 hlen1 ?_
            refine ⟨by omega, hext, hsc1', Nat.le_trans hsc2' hsc2,
              fun h => by omega, fun _ => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj hz => ?_⟩
            · have hisub : (i + 1#64).toNat - 1 = i.toNat := by omega
              rw [hisub]
              change sc'.toNat ≤ (st'.scratch.scratch_buf[i.toNat]?.getD 0#32).toNat
              dsimp only [st']
              rw [List.getElem?_set_self (by rw [hsbl]; omega), Option.getD_some, hsc_t32]
              exact hsc2'
            · change 1 ≤ (st'.scratch.scratch_buf[j]?.getD 0#32).toNat ∧
                (st'.scratch.scratch_buf[j]?.getD 0#32).toNat ≤ 2 ^ 30
              dsimp only [st']; rw [List.getElem?_set]; split
              · rw [Option.getD_some, hsc_t32]; exact ⟨hsc1, hsc2⟩
              · exact hrng j (by omega)
            · rw [hi1] at hj
              change (st'.scratch.scratch_buf[j + 1]?.getD 0#32).toNat ≤
                (st'.scratch.scratch_buf[j]?.getD 0#32).toNat
              dsimp only [st']
              by_cases hj1 : j + 1 = i.toNat
              · have hm1 : 0 < i.toNat := by omega
                have hj_eq : j = i.toNat - 1 := by omega
                rw [hj1, hj_eq, List.getElem?_set_self (by rw [hsbl]; omega),
                  List.getElem?_set_ne (by omega), Option.getD_some, hsc_t32]
                exact hsc_prev hm1
              · rw [List.getElem?_set_ne (by omega),
                  List.getElem?_set_ne (show i.toNat ≠ j by omega)]
                exact hmono j (by omega)
            · subst hz
              change (st'.scratch.scratch_buf[0]?.getD 0#32).toNat = 2 ^ 30
              dsimp only [st']
              by_cases hi0 : 0 = i.toNat
              · rw [hi0, List.getElem?_set_self (by rw [hsbl]; omega),
                  Option.getD_some, hsc_t32]
                exact hsc_z hi0.symm
              · rw [List.getElem?_set_ne (Ne.symm hi0)]; exact h0eq 0 (by omega) rfl
          · intro Jsc hJsc; m7_hsteps_nj
            · exact hJsc (1#64, ()) _ ⟨‹_›, by decide, hsc1⟩
            · have hpos : 1 ≤ ((sc * iqc) >>> (16 : Nat)).toNat := by
                have h1 : (1 : BitVec 64).toNat = 1 := rfl
                have hnl : ¬ ((sc * iqc) >>> (16 : Nat)).toNat < (1 : BitVec 64).toNat := ‹_›
                omega
              exact hJsc (_, ()) _
                ⟨‹_›, hpos, Nat.le_trans hmul_val (Nat.div_le_self _ _)⟩
        · have hi32 : i.toNat = 32 := by c0_bound
          rw [hi32] at hrng hmono h0eq
          exact ⟨st, hcore, hlen', hext,
            fun _ _ _ => ⟨h0eq 0 (by decide) rfl, hrng, fun j hj => hmono j (by omega)⟩, hml⟩
    · intro Jiq hJiq; m7_hsteps_nj
      · exact hJiq (32768#64, ()) m ⟨hm, by decide, fun h => by c0_bound⟩
      · exact hJiq (iq, ()) m ⟨hm, by c0_bound, fun _ => rfl⟩

theorem full_walk_init_table_m7_wp (Γ : Env) :
    ∀ a m Q X, m7InitTableSpec a m Q X →
      Func.wp Γ full_walk_init_table_m7_body a m Q X := by
  rintro ⟨h, iq, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  refine wp_mono (fun () m' ⟨s', hcore, hlen', hext, _, hm'⟩ =>
      hQ () s' m' hcore hlen' hext hm')
    (fun _ _ _ _ hx => hx.elim) _ m
    (full_walk_init_table_m7_core Γ c iq s R m hlen hm)

theorem full_walk_init_table_m7_mono_wp (Γ : Env) :
    ∀ a m Q X, m7InitTableMonoSpec a m Q X →
      Func.wp Γ full_walk_init_table_m7_body a m Q X := by
  rintro ⟨h, iq, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, h32, h1, h2⟩, hlen, hm, hQ⟩
  refine wp_mono (fun () m' ⟨s', hcore, hlen', hext, hmono, hm'⟩ =>
      let ⟨h0, hbd, hm⟩ := hmono h32 h1 h2
      hQ () s' m' hcore hlen' ⟨hext, h0, hbd, hm⟩ hm')
    (fun _ _ _ _ hx => hx.elim) _ m
    (full_walk_init_table_m7_core Γ c iq s R m hlen hm)

end HelpersPart1

/-! ## 4. Helpers 4, 7, 10: `init_vals`, `break`, `save_min` -/

section HelpersPart2

theorem full_walk_init_vals_m7_wp (Γ : Env) :
    ∀ a m Q X, m7InitValsSpec a m Q X → Func.wp Γ full_walk_init_vals_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  m7_hsteps_nj
  refine wp_join_group (ts := [i64]) (fun (cv, ()) m1 =>
      (FullMem c s ⋆ R) m1 ∧ cv.toNat ≤ c.max_vars) ?_ ?_
  · rintro _ ⟨cv, ⟨⟩⟩ m1 ⟨hm1, hcv_le⟩
    m7_hsteps_nj
    refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) s R
      (fun st (v, ()) => v.toNat ≤ cv.toNat ∧ FullExtScratchPres s st)
      (fun (v, ()) => cv.toNat - v.toNat) ?_ ?_
    · intro Jv hJv; m7_hsteps_nj
      exact hJv s (0#64, ()) m1 hm1 rfl hlen ⟨Nat.zero_le _, m7_ext_refl s⟩
    · rintro Jv st ⟨v, ⟨⟩⟩ ml hcore hlen' ⟨hv_le, hext⟩ hml ihv
      dsimp only [fullSafetySlice] at hcore hlen' hml
      have hvl := hlen'.core_ok.vals_len
      have hfll := hlen'.core_ok.flags_len
      have hwvl := hlen'.scratch_ok.walk_vals_len
      have hwbl := hlen'.scratch_ok.walk_best_len
      have hphl := hlen'.scratch_ok.phases_len
      have hptl := hlen'.scratch_ok.phases_target_len
      m7_hsteps_nj
      · have hv_lt : v.toNat < cv.toNat := by c0_bound
        have hv_mx : v.toNat < c.max_vars := by omega
        have hv_shl1 : (v <<< (1 : Nat)).toNat = 2 * v.toNat :=
          m7_bv64_shl1_toNat (by omega)
        have hv_shl1_len : (v <<< (1 : Nat)).toNat < st.core.vals.length := by
          rw [hvl, hv_shl1]; omega
        have hv_fl_len : v.toNat < st.core.flags.length := by rw [hfll]; omega
        have hv_ph_len : v.toNat < st.scratch.phases.length := by rw [hphl]; omega
        have hv_pt_len : v.toNat < st.scratch.phases_target.length := by rw [hptl]; omega
        m7_hsteps_nj
        refine wp_join_group (ts := [i8]) (fun (_p, ()) mp => (FullMem c st ⋆ R) mp) ?_ ?_
        · rintro _ ⟨p, ⟨⟩⟩ mp hmp
          m7_hsteps_nj
          have hv2_wv : (v <<< (1 : Nat)).toNat < st.scratch.walk_vals.length := by
            rw [hwvl, hv_shl1]; omega
          have hvo_to : ((v <<< (1 : Nat)) ||| 1#64).toNat = 2 * v.toNat + 1 :=
            m7_bv64_shl1_or1_toNat (by omega)
          let st1 : FullState := { st with scratch := { st.scratch with
            walk_vals := st.scratch.walk_vals.set (v <<< (1 : Nat)).toNat p } }
          have hvo_wv : ((v <<< (1 : Nat)) ||| 1#64).toNat < st1.scratch.walk_vals.length := by
            dsimp only [st1]; rw [List.length_set, hwvl, hvo_to]; omega
          m7_hsteps_nj
          refine wp_join_group (ts := [i32]) (fun (s32, ()) ms => (FullMem c st1 ⋆ R) ms) ?_ ?_
          · rintro _ ⟨s32, ⟨⟩⟩ ms hms
            let st2 : FullState := { st1 with scratch := { st1.scratch with
              walk_vals := st1.scratch.walk_vals.set
                ((v <<< (1 : Nat)) ||| 1#64).toNat (s32.setWidth 8) } }
            have hv_wb : v.toNat < st2.scratch.walk_best.length := by
              dsimp only [st2, st1]; rw [hwbl]; omega
            let st3 : FullState := { st2 with scratch := { st2.scratch with
              walk_best := st2.scratch.walk_best.set v.toNat p } }
            m7_hsteps_nj
            have hv1 : (v + 1#64).toNat = v.toNat + 1 := m7_bv64_add1_toNat (by omega)
            exact ihv st3 (v + 1#64, ()) _ ‹_› (by dsimp only; omega) rfl
              (m7_len_wbest (m7_len_wvals (m7_len_wvals hlen'))) ⟨by omega, hext⟩
          · intro Js32 hJs32; m7_hsteps_nj <;> exact hJs32 (_, ()) _ ‹_›
        · intro Jp hJp; m7_hsteps <;> exact hJp (_, ()) _ hml
      · have hvv : v.toNat = cv.toNat := by c0_bound
        have htv : (cv <<< (1 : Nat)).toNat = 2 * cv.toNat := m7_bv64_shl1_toNat (by omega)
        m7_hsteps_nj
        refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) st R
          (fun st' (l, ()) => l.toNat ≤ (cv <<< (1 : Nat)).toNat ∧ FullExtScratchPres st st')
          (fun (l, ()) => (cv <<< (1 : Nat)).toNat - l.toNat) ?_ ?_
        · intro Jl hJl; m7_hsteps_nj
          exact hJl st (0#64, ()) _ hml rfl hlen' ⟨Nat.zero_le _, m7_ext_refl st⟩
        · rintro Jl st' ⟨l, ⟨⟩⟩ ml' hcore'' hlen'' ⟨hl_le, hext''⟩ hml' ihl
          dsimp only [fullSafetySlice] at hcore'' hlen'' hml'
          have htrcl := hlen''.scratch_ok.tarjan_reach_len
          m7_hsteps_nj
          · have hl_lt : l.toNat < (cv <<< (1 : Nat)).toNat := by c0_bound
            have hl_trc : l.toNat < st'.scratch.tarjan_reach.length := by rw [htrcl]; omega
            let st'' : FullState := { st' with scratch := { st'.scratch with
              tarjan_reach := st'.scratch.tarjan_reach.set l.toNat 0#32 } }
            m7_hsteps_nj
            have hl1 : (l + 1#64).toNat = l.toNat + 1 := m7_bv64_add1_toNat (by omega)
            exact ihl st'' (l + 1#64, ()) _ ‹_› (by dsimp only; omega) rfl (m7_len_trc hlen'')
              ⟨by omega, hext''⟩
          · exact hQ () st' ml' (hcore.trans hcore'') hlen'' (m7_ext_trans hext hext'') hml'
  · have hcv := hlen.core_ok.cur_vars_le
    intro Jcv hJcv; m7_hsteps_nj
    · exact hJcv (BitVec.ofNat 64 c.max_vars, ()) m ⟨hm, by c0_bound⟩
    · exact hJcv (BitVec.ofNat 64 s.core.cur_vars, ()) m
        ⟨hm, by rw [bv64_ofNat_toNat (by omega)]; exact hcv⟩

theorem full_walk_break_m7_wp (Γ : Env) :
    ∀ a m Q X, m7BreakSpec a m Q X → Func.wp Γ full_walk_break_m7_body a m Q X := by
  rintro ⟨h, not_lit, ncl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmax := c.hmaxv; have hscr := c.hscr; unfold dimacsBound at hmax hscr
  have hsbl := hlen.scratch_ok.scratch_buf_len
  have htmkl := hlen.scratch_ok.tarjan_mark_len
  have htrcl := hlen.scratch_ok.tarjan_reach_len
  have hret0 : Q (0#32, ()) m := hQ (0#32, ()) s m rfl hlen rfl hm
  m7_hsteps_nj
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · have hcv2 : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
    have hcv1 : 0 < s.core.cur_vars := m7_pos_of_bv64_ofNat_ne0 (by omega) ‹_›
    have hnl : not_lit.toNat < 2 * s.core.cur_vars := by
      have hnl0 : (not_lit.setWidth 64).toNat <
          ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
      rw [zext_toNat _ (by decide),
        m7_bv64_shl1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
        bv64_ofNat_toNat (by omega)] at hnl0
      exact hnl0
    have hncl_sc : ncl.toNat ≤ c.scratch_cap := m7_le_of_not_bv64_ofNat_lt (by omega) ‹_›
    have h5n : 32 + 5 * ncl.toNat ≤ c.scratch_cap := by
      have h5 : (32#64 + 5#64 * ncl).toNat ≤ c.scratch_cap := by c0_bound
      have hm5 : (5#64 * ncl).toNat = 5 * ncl.toNat := by
        rw [BitVec.toNat_mul, show (5#64 : BitVec 64).toNat = 5 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toNat_add, show (32#64 : BitVec 64).toNat = 32 from rfl, hm5,
        Nat.mod_eq_of_lt (by omega)] at h5
      exact h5
    have hnl_tmk : (not_lit.setWidth 64).toNat < s.scratch.tarjan_mark.length := by
      rw [htmkl]; exact m7_bv64_zext32_lt (by omega)
    have hnl_trc : (not_lit.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
      rw [htrcl]; exact m7_bv64_zext32_lt (by omega)
    have hoff_le :
        ((s.scratch.tarjan_mark[(not_lit.setWidth 64).toNat]'hnl_tmk).setWidth 64).toNat ≤
          c.scratch_cap - (32 + 5 * ncl.toNat) := by c0_bound
    refine wp_join_group (ts := [i64]) (fun (len', ()) m1 =>
        (FullMem c s ⋆ R) m1 ∧
        len'.toNat ≤ c.scratch_cap - (32 + 5 * ncl.toNat) -
          ((s.scratch.tarjan_mark[(not_lit.setWidth 64).toNat]'hnl_tmk).setWidth 64).toNat) ?_ ?_
    · rintro _ ⟨len', ⟨⟩⟩ m1 ⟨hm1, hlen_le⟩
      m7_hsteps_nj
      refine wp_loop_inv (ts := [i64, i32])
        (fun (k, _brk, ()) ml => (FullMem c s ⋆ R) ml ∧ k.toNat ≤ len'.toNat)
        (fun (k, _brk, ()) _ => len'.toNat - k.toNat) ?_ ?_
      · intro Jk hJk; m7_hsteps_nj
        exact hJk (0#64, 0#32, ()) m1 ⟨hm1, Nat.zero_le _⟩
      · rintro Jk ⟨k, brk, ⟨⟩⟩ ml ⟨hml, hk_le⟩ ihk
        m7_hsteps_nj
        · have hk_lt : k.toNat < len'.toNat := by c0_bound
          have hidx_occ : (32#64 + 5#64 * ncl +
              (s.scratch.tarjan_mark[(not_lit.setWidth 64).toNat]'hnl_tmk).setWidth 64 +
              k).toNat < s.scratch.scratch_buf.length := by
            rw [hsbl]; c0_bound
          m7_hsteps_nj
          refine wp_join_group (ts := [i32]) (fun (_brk', ()) mb => (FullMem c s ⋆ R) mb) ?_ ?_
          · rintro _ ⟨brk', ⟨⟩⟩ mb hmb
            m7_hsteps_nj
            have hk1 : (k + 1#64).toNat = k.toNat + 1 := m7_bv64_add1_toNat (by omega)
            exact ihk (k + 1#64, brk', ()) mb (by dsimp only; omega) ⟨hmb, by omega⟩
          · intro Jb hJb; m7_hsteps_nj
            · have hc_ncl :
                  ((s.scratch.scratch_buf[(32#64 + 5#64 * ncl +
                    (s.scratch.tarjan_mark[(not_lit.setWidth 64).toNat]'hnl_tmk).setWidth 64 +
                    k).toNat]'hidx_occ).setWidth 64).toNat < ncl.toNat := by c0_bound
              have hsh_ncl : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat :=
                m7_bv64_shl1_toNat (by omega)
              have hsat_lt :
                  (32#64 + (ncl <<< (1 : Nat)) +
                    (s.scratch.scratch_buf[(32#64 + 5#64 * ncl +
                      (s.scratch.tarjan_mark[(not_lit.setWidth 64).toNat]'hnl_tmk).setWidth 64 +
                      k).toNat]'hidx_occ).setWidth 64).toNat <
                  s.scratch.scratch_buf.length := by
                generalize hv32 : s.scratch.scratch_buf[(32#64 + 5#64 * ncl +
                  (s.scratch.tarjan_mark[(not_lit.setWidth 64).toNat]'hnl_tmk).setWidth 64 +
                  k).toNat]'hidx_occ = c32 at hc_ncl ⊢
                have hc_bnd : c32.toNat < ncl.toNat := by
                  simpa only [zext_toNat (n := 64) c32 (by decide)] using hc_ncl
                rw [hsbl, BitVec.toNat_add, BitVec.toNat_add, hsh_ncl,
                  show (32#64 : BitVec 64).toNat = 32 from rfl,
                  zext_toNat (n := 64) c32 (by decide),
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                omega
              m7_hsteps_nj <;> exact hJb (_, ()) _ ‹_›
            · exact hJb (brk, ()) _ ‹_›
        · exact hQ (brk, ()) s ml rfl hlen rfl hml
    · intro Jl hJl; m7_hsteps_nj
      · exact hJl (_, ()) _ ⟨‹_›, by c0_bound⟩
      · exact hJl (_, ()) _ ⟨‹_›, by c0_bound⟩

theorem full_walk_save_min_m7_wp (Γ : Env) :
    ∀ a m Q X, m7SaveMinSpec a m Q X → Func.wp Γ full_walk_save_min_m7_body a m Q X := by
  rintro ⟨h, best_pos, trail_ok, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  m7_hsteps_nj
  · exact hQ () s m rfl hlen (m7_ext_refl s) hm
  · exact hQ () s m rfl hlen (m7_ext_refl s) hm
  · have hcv2 : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
    have hcv1 : 0 < s.core.cur_vars := m7_pos_of_bv64_ofNat_ne0 (by omega) ‹_›
    have hlim_le : ((BitVec.ofNat 64 s.core.cur_vars >>> (2 : Nat)) + 1#64).toNat ≤
        s.core.cur_vars := by
      rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, bv64_ofNat_toNat (by omega),
        Nat.shiftRight_eq_div_pow, show (1#64 : BitVec 64).toNat = 1 from rfl]
      omega
    refine wp_join_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial
      (fun st _ => FullExtScratchPres s st)
      (fun Js st _ m1 hcore1 hlen1 _ hext1 hm1 => ?_) (fun Js hJs => ?_)
    · dsimp only [fullSafetySlice] at hcore1 hlen1 hm1
      have heq1 : st.core = s.core := hcore1
      m7_hsteps_nj
      refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) st R
        (fun st' (v, ()) => v.toNat ≤ st.core.cur_vars ∧ FullExtScratchPres st st')
        (fun (v, ()) => st.core.cur_vars - v.toNat) ?_ ?_
      · intro Jv hJv; m7_hsteps_nj
        exact hJv st (0#64, ()) m1 hm1 rfl hlen1 ⟨Nat.zero_le _, m7_ext_refl st⟩
      · rintro Jv st' ⟨v, ⟨⟩⟩ ml hcore2 hlen2 ⟨hv_le, hext2⟩ hml ihv
        dsimp only [fullSafetySlice] at hcore2 hlen2 hml
        have hvl := hlen2.core_ok.vals_len
        have hfll := hlen2.core_ok.flags_len
        have hwbl := hlen2.scratch_ok.walk_best_len
        have hphl := hlen2.scratch_ok.phases_len
        m7_hsteps_nj
        · have hv_lt : v.toNat < st.core.cur_vars := by
            have hlt : v.toNat < s.core.cur_vars % 2 ^ 64 := ‹_›
            rw [Nat.mod_eq_of_lt (by omega)] at hlt; rw [heq1]; exact hlt
          have hv_mx : v.toNat < c.max_vars := by rw [heq1] at hv_lt; omega
          have hv2_vl : (v <<< (1 : Nat)).toNat < st'.core.vals.length := by
            rw [hvl, m7_bv64_shl1_toNat (by omega)]; omega
          have hv_fl : v.toNat < st'.core.flags.length := by rw [hfll]; omega
          have hv_wb : v.toNat < st'.scratch.walk_best.length := by rw [hwbl]; omega
          have hv_ph : v.toNat < st'.scratch.phases.length := by rw [hphl]; omega
          have hv1 : (v + 1#64).toNat = v.toNat + 1 := m7_bv64_add1_toNat (by omega)
          m7_hsteps_nj
          refine wp_join_safety_slice (fullSafetySlice c) st' R (fun _ => True) trivial
            (fun st2 _ => FullExtScratchPres st' st2)
            (fun _ st2 _ m2 hcore3 hlen3 _ hext3 hm2 => ?_) (fun Jw hJw => ?_)
          · dsimp only [fullSafetySlice] at hcore3 hlen3 hm2
            m7_hsteps_nj
            exact ihv st2 (v + 1#64, ()) m2 hm2 (by dsimp only; omega) hcore3
              hlen3 ⟨by omega, m7_ext_trans hext2 hext3⟩
          · dsimp only [fullSafetySlice] at hJw
            m7_hsteps_nj
            · m7_hsteps
              · let st3 : FullState := { st' with scratch := { st'.scratch with
                  phases :=
                    st'.scratch.phases.set v.toNat (st'.scratch.walk_best[v.toNat]'hv_wb) } }
                exact hJw st3 () _ ‹_› rfl (m7_len_phases hlen2) (m7_ext_refl st')
              · exact hJw st' () _ ‹_› rfl hlen2 (m7_ext_refl st')
            · exact hJw st' () _ ‹_› rfl hlen2 (m7_ext_refl st')
            · exact hJw st' () _ ‹_› rfl hlen2 (m7_ext_refl st')
        · exact hQ () st' ml (hcore1.trans hcore2) hlen2 (m7_ext_trans hext1 hext2) hml
    · m7_hsteps_nj
      · refine wp_join_group (ts := [i64]) (fun (lim, ()) ml =>
            (FullMem c s ⋆ R) ml ∧ lim.toNat ≤ s.core.cur_vars) ?_ ?_
        · rintro _ ⟨lim, ⟨⟩⟩ ml ⟨hml, hlim_ok⟩
          m7_hsteps_nj
          refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) s R
            (fun st (k, ()) => k.toNat ≤ lim.toNat ∧ FullExtScratchPres s st)
            (fun (k, ()) => lim.toNat - k.toNat) ?_ ?_
          · intro Jk hJk; m7_hsteps_nj
            exact hJk s (0#64, ()) ml hml rfl hlen ⟨Nat.zero_le _, m7_ext_refl s⟩
          · rintro Jk st ⟨k, ⟨⟩⟩ mk hcorek hlenk ⟨hk_le, hextk⟩ hmk ihk
            dsimp only [fullSafetySlice] at hcorek hlenk hmk
            have hwsl := hlenk.scratch_ok.wsort_len
            have hwbl := hlenk.scratch_ok.walk_best_len
            m7_hsteps_nj
            · have hk_lt : k.toNat < lim.toNat := by c0_bound
              have hk_ws : k.toNat < st.scratch.wsort.length := by rw [hwsl]; omega
              have hk1 : (k + 1#64).toNat = k.toNat + 1 := m7_bv64_add1_toNat (by omega)
              m7_hsteps_nj
              refine wp_join_safety_slice (fullSafetySlice c) st R (fun _ => True) trivial
                (fun st1 _ => FullExtScratchPres st st1)
                (fun _ st1 _ m1 hcore1 hlen1 _ hext1 hm1 => ?_) (fun Jb hJb => ?_)
              · dsimp only [fullSafetySlice] at hcore1 hlen1 hm1
                m7_hsteps_nj
                exact ihk st1 (k + 1#64, ()) m1 hm1 (by dsimp only; omega) hcore1
                  hlen1 ⟨by omega, m7_ext_trans hextk hext1⟩
              · m7_hsteps_nj
                · have hbv_lt :
                      ((st.scratch.wsort[k.toNat]'hk_ws).setWidth 64).toNat <
                        st.scratch.walk_best.length := by rw [hwbl]; c0_bound
                  dsimp only [fullSafetySlice] at hJb
                  m7_hsteps_nj
                  refine wp_join_group (ts := [i32]) (fun _ mn => (FullMem c st ⋆ R) mn) ?_ ?_
                  · rintro _ ⟨nv, ⟨⟩⟩ mn hmn
                    let st_wb : FullState := { st with scratch := { st.scratch with
                      walk_best := st.scratch.walk_best.set
                        ((st.scratch.wsort[k.toNat]'hk_ws).setWidth 64).toNat (nv.setWidth 8) } }
                    m7_hsteps_nj
                    exact hJb st_wb () _ ‹_› rfl (m7_len_wbest hlenk) (m7_ext_refl st)
                  · intro Jnv hJnv; m7_hsteps_nj <;> exact hJnv (_, ()) _ ‹_›
                · dsimp only [fullSafetySlice] at hJb
                  exact hJb st () _ hmk rfl hlenk (m7_ext_refl st)
            · exact hJs st () mk hmk hcorek hlenk hextk
        · intro Jlim hJlim; m7_hsteps_nj
          · exact hJlim (_, ()) _ ⟨hm, hlim_le⟩
          · have hnb : ¬ ((BitVec.ofNat 64 s.core.cur_vars >>> (2 : Nat)).toNat + 1) % 2 ^ 64 <
                best_pos.toNat := ‹_›
            rw [BitVec.toNat_ushiftRight, bv64_ofNat_toNat (by omega),
              Nat.shiftRight_eq_div_pow] at hnb
            rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, bv64_ofNat_toNat (by omega),
              Nat.shiftRight_eq_div_pow, show (1#64 : BitVec 64).toNat = 1 from rfl] at hlim_le
            exact hJlim (best_pos, ()) _ ⟨hm, by omega⟩
      · exact hJs s () m hm rfl hlen (m7_ext_refl s)
      · exact hJs s () m hm rfl hlen (m7_ext_refl s)

end HelpersPart2

/-! ## 5. Helpers 5, 6, 8, 9: `collect`, `build_occ`, `pick`, `flip` -/

section HelpersPart3

theorem full_walk_flip_m7_wp (Γ : Env) :
    ∀ a m Q X, m7FlipSpec a m Q X → Func.wp Γ full_walk_flip_m7_body a m Q X := by
  rintro ⟨h, flip_lit, ncl, ulen, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmax := c.hmaxv; have hscr := c.hscr; unfold dimacsBound at hmax hscr
  have hsbl := hlen.scratch_ok.scratch_buf_len
  have hwvl := hlen.scratch_ok.walk_vals_len
  have htmkl := hlen.scratch_ok.tarjan_mark_len
  have htrcl := hlen.scratch_ok.tarjan_reach_len
  m7_hsteps_nj
  refine wp_join_group (ts := []) (fun () mu => (FullMem c s ⋆ R) mu) ?_ ?_
  · rintro _ ⟨⟩ m0 hm0
    refine wp_join_group (ts := [i64]) (fun (r0, ()) mr =>
        (FullMem c s ⋆ R) mr ∧ r0.toNat ≤ ncl.toNat)
      (fun _ ⟨r0, ⟨⟩⟩ mr ⟨hmr, hr0⟩ => by
        m7_hsteps_nj
        exact hQ (r0, ()) s mr rfl hlen
          ⟨m7_ext_refl s, Nat.le_trans (m7_bv64_and_lo32_le r0) hr0⟩ hmr)
      (fun Jr hJr => by
        m7_hsteps_nj
        · exact hJr (ncl, ()) _ ⟨hm0, Nat.le_refl _⟩
        · exact hJr (ulen, ()) _ ⟨hm0, by c0_bound⟩)
  · intro Jg hJg
    m7_hsteps_nj
    · exact hJg () m hm
    · exact hJg () m hm
    · exact hJg () m hm
    · exact hJg () m hm
    · exact hJg () m hm
    · exact hJg () m hm
    have hcv2 : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
    have hcv1 : 0 < s.core.cur_vars := m7_pos_of_bv64_ofNat_ne0 (by omega) ‹_›
    have hfl : flip_lit.toNat < 2 * s.core.cur_vars := by
      have h0 : (flip_lit.setWidth 64).toNat <
          ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
      rw [zext_toNat _ (by decide),
        m7_bv64_shl1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
        bv64_ofNat_toNat (by omega)] at h0
      exact h0
    have hnl : (flip_lit ^^^ 1#32).toNat < 2 * s.core.cur_vars := m7_bv32_xor1_lt hfl
    have hncl_pos : 0 < ncl.toNat := by
      have h0 : ncl.toNat ≠ 0 := fun hz => ‹ncl ≠ 0#64› (BitVec.eq_of_toNat_eq hz)
      omega
    have hncl_sc : ncl.toNat ≤ c.scratch_cap := m7_le_of_not_bv64_ofNat_lt (by omega) ‹_›
    have h5n : 32 + 5 * ncl.toNat ≤ c.scratch_cap := by
      have h5 : (32#64 + 5#64 * ncl).toNat ≤ c.scratch_cap := by c0_bound
      have hm5 : (5#64 * ncl).toNat = 5 * ncl.toNat := by
        rw [BitVec.toNat_mul, show (5#64 : BitVec 64).toNat = 5 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toNat_add, show (32#64 : BitVec 64).toNat = 32 from rfl, hm5,
        Nat.mod_eq_of_lt (by omega)] at h5
      exact h5
    have hnl_wv : ((flip_lit ^^^ 1#32).setWidth 64).toNat <
        (s.scratch.walk_vals.set (flip_lit.setWidth 64).toNat
          ((1 : BitVec 32).setWidth 8)).length := by
      rw [List.length_set, hwvl]; exact m7_bv64_zext32_lt (by omega)
    m7_hsteps_nj
    obtain ⟨st0, hcore0, hlen0, hext0, hm0⟩ :=
      m7_state_abs s hm rfl (m7_len_wvals (m7_len_wvals hlen)) (m7_ext_refl s)
    clear hm
    have hfl_tmk : (flip_lit.setWidth 64).toNat < st0.scratch.tarjan_mark.length := by
      rw [hlen0.scratch_ok.tarjan_mark_len]; exact m7_bv64_zext32_lt (by omega)
    have hfl_trc : (flip_lit.setWidth 64).toNat < st0.scratch.tarjan_reach.length := by
      rw [hlen0.scratch_ok.tarjan_reach_len]; exact m7_bv64_zext32_lt (by omega)
    refine wp_join_group (ts := [i64]) (fun (cu0, ()) m0 =>
        (FullMem c st0 ⋆ R) m0 ∧ cu0.toNat ≤ ncl.toNat) ?_ ?_
    · rintro _ ⟨cu0, ⟨⟩⟩ m0 ⟨hm0', hcu0⟩
      m7_hsteps_nj
      refine wp_join_safety_slice (fullSafetySlice c) st0 R (fun _ => True) trivial
        (fun st1 (cu1, _, ()) => cu1.toNat ≤ ncl.toNat ∧ FullExtScratchPres st0 st1)
        (fun _ st1 ⟨cu1, _, ⟨⟩⟩ m1 hcore1 hlen1 _ ⟨hcu1, hext1⟩ hm1 => ?_) (fun J1 hJ1 => ?_)
      · dsimp only [fullSafetySlice] at hcore1 hlen1 hm1
        have heq1 : PreservesCoreSlice FullState.core s st1 := hcore0.trans hcore1
        have hnl_tmk1 :
            ((flip_lit ^^^ 1#32).setWidth 64).toNat < st1.scratch.tarjan_mark.length := by
          rw [hlen1.scratch_ok.tarjan_mark_len]; exact m7_bv64_zext32_lt (by omega)
        have hnl_trc1 :
            ((flip_lit ^^^ 1#32).setWidth 64).toNat < st1.scratch.tarjan_reach.length := by
          rw [hlen1.scratch_ok.tarjan_reach_len]; exact m7_bv64_zext32_lt (by omega)
        m7_hsteps_nj
        refine wp_join_safety_slice (fullSafetySlice c) st1 R (fun _ => True) trivial
          (fun st2 (cu2, _, ()) => cu2.toNat ≤ ncl.toNat ∧ FullExtScratchPres st1 st2)
          (fun _ st2 ⟨cu2, _, ⟨⟩⟩ m2 hcore2 hlen2 _ ⟨hcu2, hext2⟩ hm2 => ?_) (fun J2 hJ2 => ?_)
        · dsimp only [fullSafetySlice] at hcore2 hlen2 hm2
          have hfl_trc2 : (flip_lit.setWidth 64).toNat < st2.scratch.tarjan_reach.length := by
            rw [hlen2.scratch_ok.tarjan_reach_len]; exact m7_bv64_zext32_lt (by omega)
          have hnl_trc2 : ((flip_lit ^^^ 1#32).setWidth 64).toNat <
              st2.scratch.tarjan_reach.length := by
            rw [hlen2.scratch_ok.tarjan_reach_len]; exact m7_bv64_zext32_lt (by omega)
          m7_hsteps_nj
          refine wp_join_group (ts := [i64]) (fun _ m3 => (FullMem c st2 ⋆ R) m3)
            (fun _ ⟨hi, ⟨⟩⟩ m3 hm3 => by
              m7_hsteps_nj
              exact hQ (_, ()) st2 m3 (hcore0.trans (hcore1.trans hcore2)) hlen2
                ⟨m7_ext_trans hext0 (m7_ext_trans hext1 hext2),
                  Nat.le_trans (m7_bv64_pack32_lo_and hi cu2) hcu2⟩ hm3)
            (fun Jh hJh => by
              m7_hsteps_nj
              · exact hJh (_, ()) _ hm2
              · exact hJh (_, ()) _ hm2)
        · dsimp only [fullSafetySlice] at hJ2
          m7_hsteps_nj
          · refine wp_join_group (ts := [i64]) (fun (lb', ()) ml =>
                (FullMem c st1 ⋆ R) ml ∧
                lb'.toNat ≤ c.scratch_cap - (32 + 5 * ncl.toNat) -
                  ((st1.scratch.tarjan_mark[
                    ((flip_lit ^^^ 1#32).setWidth 64).toNat]'hnl_tmk1).setWidth 64).toNat) ?_ ?_
            · rintro _ ⟨lb', ⟨⟩⟩ ml ⟨hml, hlb'⟩
              m7_hsteps_nj
              refine wp_loop_safety_slice_pure (ts := [i64, i64]) (fullSafetySlice c) st1 R
                (fun st (cu, k, ()) => k.toNat ≤ lb'.toNat ∧ cu.toNat ≤ ncl.toNat ∧
                  FullExtScratchPres st1 st)
                (fun (_cu, k, ()) => lb'.toNat - k.toNat) ?_ ?_
              · intro Jk hJk; m7_hsteps_nj
                exact hJk st1 (cu1, 0#64, ()) ml hml rfl hlen1
                  ⟨Nat.zero_le _, hcu1, m7_ext_refl st1⟩
              · rintro Jk st ⟨cu, k, ⟨⟩⟩ mk hcorek hlenk ⟨hk_le, hcu, hextk⟩ hmk ihk
                dsimp only [fullSafetySlice] at hcorek hlenk hmk
                have hsblk := hlenk.scratch_ok.scratch_buf_len
                m7_hsteps_nj
                · have hk_lt : k.toNat < lb'.toNat := by c0_bound
                  have hk1 : (k + 1#64).toNat = k.toNat + 1 := m7_bv64_add1_toNat (by omega)
                  have hidx_occ : (32#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl +
                      (st1.scratch.tarjan_mark[
                        ((flip_lit ^^^ 1#32).setWidth 64).toNat]'hnl_tmk1).setWidth 64 +
                      k).toNat < st.scratch.scratch_buf.length := by
                    have hsh : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat :=
                      m7_bv64_shl1_toNat (by omega)
                    simp only [m7_zext32] at hlb'
                    simp only [BitVec.toNat_add, show (32#64 : BitVec 64).toNat = 32 from rfl,
                      hsh, m7_zext32, Nat.mod_add_mod]
                    rw [Nat.mod_eq_of_lt (by omega), hsblk]
                    omega
                  m7_hsteps_nj
                  refine wp_join_safety_slice (fullSafetySlice c) st R (fun _ => True) trivial
                    (fun st' (cu', ()) => cu'.toNat ≤ ncl.toNat ∧ FullExtScratchPres st st')
                    (fun _ st' ⟨cu', ⟨⟩⟩ m' hcore' hlen' _ ⟨hcu', hext'⟩ hm' => ?_)
                    (fun Jc hJc => ?_)
                  · dsimp only [fullSafetySlice] at hcore' hlen' hm'
                    m7_hsteps_nj
                    exact ihk st' (cu', k + 1#64, ()) m' hm' (by dsimp only; omega) hcore'
                      hlen' ⟨by omega, hcu', m7_ext_trans hextk hext'⟩
                  · dsimp only [fullSafetySlice] at hJc
                    m7_hsteps_nj
                    · have hcb : (st.scratch.scratch_buf[(32#64 + (ncl <<< (1 : Nat)) + ncl +
                          ncl + ncl + (st1.scratch.tarjan_mark[((flip_lit ^^^ 1#32).setWidth
                            64).toNat]'hnl_tmk1).setWidth 64 + k).toNat]'hidx_occ).toNat <
                          ncl.toNat := by
                        have hlb_nat : lb'.toNat ≤ c.scratch_cap - (32 + 5 * ncl.toNat) -
                            st1.scratch.tarjan_mark[flip_lit.toNat ^^^ 1].toNat := by
                          simpa only [m7_zext32, BitVec.toNat_xor,
                            show (1#32 : BitVec 32).toNat = 1 from rfl] using hlb'
                        have hsh : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat :=
                          m7_bv64_shl1_toNat (by omega)
                        simp only [BitVec.toNat_add, show (32#64 : BitVec 64).toNat = 32 from rfl,
                          hsh, m7_zext32, Nat.mod_add_mod, BitVec.toNat_xor,
                          show (1#32 : BitVec 32).toNat = 1 from rfl]
                        have htmp :
                            st.scratch.scratch_buf[(32 + 2 * ncl.toNat + ncl.toNat + ncl.toNat +
                              ncl.toNat + st1.scratch.tarjan_mark[flip_lit.toNat ^^^ 1].toNat +
                              k.toNat) % 2 ^ 64].toNat < ncl.toNat := ‹_›
                        exact htmp
                      have hsh_ncl : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat :=
                        m7_bv64_shl1_toNat (by omega)
                      generalize hv32 : st.scratch.scratch_buf[(32#64 + (ncl <<< (1 : Nat)) +
                        ncl + ncl + ncl + (st1.scratch.tarjan_mark[
                          ((flip_lit ^^^ 1#32).setWidth 64).toNat]'hnl_tmk1).setWidth 64 +
                        k).toNat]'hidx_occ = c32 at hcb ⊢
                      have hsat_lt :
                          (32#64 + (ncl <<< (1 : Nat)) + c32.setWidth 64).toNat <
                            st.scratch.scratch_buf.length := by
                        rw [hsblk, BitVec.toNat_add, BitVec.toNat_add, hsh_ncl,
                          show (32#64 : BitVec 64).toNat = 32 from rfl, m7_zext32,
                          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                        omega
                      m7_hsteps_nj
                      refine wp_join_safety_slice (fullSafetySlice c) st R
                        (fun _ => True) trivial
                        (fun st' (cu', _s', ()) => cu'.toNat ≤ ncl.toNat ∧
                          FullExtScratchPres st st')
                        (fun _ st' ⟨cu', _s', ⟨⟩⟩ m' hcore' hlen' _ ⟨hcu', hext'⟩ hm' =>
                          hJc st' (cu', ()) m' hm' hcore' hlen' ⟨hcu', hext'⟩)
                        (fun Jsc hJsc => ?_)
                      dsimp only [fullSafetySlice] at hJsc
                      m7_hsteps_nj
                      · obtain ⟨st_s1, hcs1, hls1, hes1, hms1⟩ :=
                          m7_state_abs st hm rfl (m7_len_scrBuf hlenk) (m7_ext_scrBuf st _)
                        clear hm
                        refine wp_join_safety_slice (fullSafetySlice c) st_s1 R
                          (fun _ => True) trivial
                          (fun st' (cu', ()) => cu'.toNat ≤ ncl.toNat ∧
                            FullExtScratchPres st_s1 st')
                          (fun _ st' ⟨cu', ⟨⟩⟩ m' hcore' hlen' _ ⟨hcu', hext'⟩ hm' =>
                            hJsc st' (cu', _, ()) m' hm' (hcs1.trans hcore') hlen'
                              ⟨hcu', m7_ext_trans hes1 hext'⟩)
                          (fun Ju hJu => ?_)
                        dsimp only [fullSafetySlice] at hJu
                        m7_hsteps_nj
                        · have hcu_lt : cu.toNat < ncl.toNat := by c0_bound
                          have hupos_lt :
                              (32#64 + (ncl <<< (1 : Nat)) + ncl + c32.setWidth 64).toNat <
                                st_s1.scratch.scratch_buf.length := by
                            rw [hls1.scratch_ok.scratch_buf_len]
                            simp only [BitVec.toNat_add, hsh_ncl,
                              show (32#64 : BitVec 64).toNat = 32 from rfl, m7_zext32,
                              Nat.mod_add_mod]
                            rw [Nat.mod_eq_of_lt (by omega)]; omega
                          have hunsat_lt :
                              (32#64 + (ncl <<< (1 : Nat)) + ncl + ncl + cu).toNat <
                                (st_s1.scratch.scratch_buf.set
                                  (32#64 + (ncl <<< (1 : Nat)) + ncl +
                                    c32.setWidth 64).toNat
                                  (BitVec.setWidth 32 cu)).length := by
                            rw [List.length_set, hls1.scratch_ok.scratch_buf_len]
                            simp only [BitVec.toNat_add, hsh_ncl,
                              show (32#64 : BitVec 64).toNat = 32 from rfl,
                              Nat.mod_add_mod]
                            rw [Nat.mod_eq_of_lt (by omega)]; omega
                          m7_hsteps_nj
                          obtain ⟨st_s2, hcs2, hls2, hes2, hms2⟩ :=
                            m7_state_abs st_s1 hm rfl
                              (m7_len_scrBuf (m7_len_scrBuf hls1)) (m7_ext_scrBuf st_s1 _)
                          exact hJu st_s2 (cu + 1#64, ()) m hms2 hcs2 hls2
                            ⟨by rw [BitVec.toNat_add,
                              show (1#64 : BitVec 64).toNat = 1 from rfl,
                              Nat.mod_eq_of_lt (by omega)]; omega, hes2⟩
                        · exact hJu _ (cu, ()) _ hms1 rfl hls1 ⟨hcu, m7_ext_refl st_s1⟩
                        · exact hJu _ (cu, ()) _ hms1 rfl hls1 ⟨hcu, m7_ext_refl st_s1⟩
                      · exact hJsc st (cu, _, ()) mk hmk rfl hlenk ⟨hcu, m7_ext_refl st⟩
                    · exact hJc st (cu, ()) mk hmk rfl hlenk ⟨hcu, m7_ext_refl st⟩
                · exact hJ2 st (cu, _, ()) mk hmk hcorek hlenk ⟨hcu, hextk⟩
            · intro Jlb hJlb; m7_hsteps_nj
              · have hmk_le := m7_rem1_mod h5n hscr ‹_›
                have hmk_le' : ((st1.scratch.tarjan_mark[
                      ((flip_lit ^^^ 1#32).setWidth 64).toNat]'hnl_tmk1).setWidth 64).toNat ≤
                    c.scratch_cap - (32 + 5 * ncl.toNat) := by
                  simpa only [m7_zext32, BitVec.toNat_xor,
                    show (1#32 : BitVec 32).toNat = 1 from rfl] using hmk_le
                exact hJlb (_, ()) m1 ⟨hm1, m7_rem_sub_le rfl h5n hscr hmk_le'⟩
              · have hmk_le := m7_rem1_mod h5n hscr ‹_›
                have hreach_le := m7_rem2_mod h5n hscr hmk_le ‹_›
                have hrz : ((st1.scratch.tarjan_reach[
                      ((flip_lit ^^^ 1#32).setWidth 64).toNat]'hnl_trc1).setWidth 64).toNat ≤
                    c.scratch_cap - (32 + 5 * ncl.toNat) -
                      ((st1.scratch.tarjan_mark[
                        ((flip_lit ^^^ 1#32).setWidth 64).toNat]'hnl_tmk1).setWidth 64).toNat := by
                  simpa only [m7_zext32, BitVec.toNat_xor,
                    show (1#32 : BitVec 32).toNat = 1 from rfl] using hreach_le
                exact hJlb (_, ()) m1 ⟨hm1, hrz⟩
          · exact hJ2 st1 (cu1, _, ()) m1 hm1 rfl hlen1 ⟨hcu1, m7_ext_refl st1⟩
      · dsimp only [fullSafetySlice] at hJ1
        m7_hsteps_nj
        · refine wp_join_group (ts := [i64]) (fun (lm', ()) ml =>
              (FullMem c st0 ⋆ R) ml ∧
              lm'.toNat ≤ c.scratch_cap - (32 + 5 * ncl.toNat) -
                ((st0.scratch.tarjan_mark[
                  (flip_lit.setWidth 64).toNat]'hfl_tmk).setWidth 64).toNat) ?_ ?_
          · rintro _ ⟨lm', ⟨⟩⟩ ml ⟨hml, hlm'⟩
            m7_hsteps_nj
            refine wp_loop_safety_slice_pure (ts := [i64, i64]) (fullSafetySlice c) st0 R
              (fun st (cu, k, ()) => k.toNat ≤ lm'.toNat ∧ cu.toNat ≤ ncl.toNat ∧
                FullExtScratchPres st0 st)
              (fun (_cu, k, ()) => lm'.toNat - k.toNat) ?_ ?_
            · intro Jk hJk; m7_hsteps_nj
              exact hJk st0 (cu0, 0#64, ()) ml hml rfl hlen0
                ⟨Nat.zero_le _, hcu0, m7_ext_refl st0⟩
            · rintro Jk st ⟨cu, k, ⟨⟩⟩ mk hcorek hlenk ⟨hk_le, hcu, hextk⟩ hmk ihk
              dsimp only [fullSafetySlice] at hcorek hlenk hmk
              have hsblk := hlenk.scratch_ok.scratch_buf_len
              m7_hsteps_nj
              · have hk_lt : k.toNat < lm'.toNat := by c0_bound
                have hk1 : (k + 1#64).toNat = k.toNat + 1 := m7_bv64_add1_toNat (by omega)
                have hidx_occ : (32#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl +
                    (st0.scratch.tarjan_mark[
                      (flip_lit.setWidth 64).toNat]'hfl_tmk).setWidth 64 +
                    k).toNat < st.scratch.scratch_buf.length := by
                  have hsh : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat :=
                    m7_bv64_shl1_toNat (by omega)
                  simp only [m7_zext32] at hlm'
                  simp only [BitVec.toNat_add, show (32#64 : BitVec 64).toNat = 32 from rfl,
                    hsh, m7_zext32, Nat.mod_add_mod]
                  rw [Nat.mod_eq_of_lt (by omega), hsblk]
                  omega
                m7_hsteps_nj
                refine wp_join_safety_slice (fullSafetySlice c) st R (fun _ => True) trivial
                  (fun st' (cu', ()) => cu'.toNat ≤ ncl.toNat ∧ FullExtScratchPres st st')
                  (fun _ st' ⟨cu', ⟨⟩⟩ m' hcore' hlen' _ ⟨hcu', hext'⟩ hm' => ?_)
                  (fun Jc hJc => ?_)
                · dsimp only [fullSafetySlice] at hcore' hlen' hm'
                  m7_hsteps_nj
                  exact ihk st' (cu', k + 1#64, ()) m' hm' (by dsimp only; omega) hcore'
                    hlen' ⟨by omega, hcu', m7_ext_trans hextk hext'⟩
                · dsimp only [fullSafetySlice] at hJc
                  m7_hsteps_nj
                  · have hsh_ncl : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat :=
                      m7_bv64_shl1_toNat (by omega)
                    have hcb : (st.scratch.scratch_buf[(32#64 + (ncl <<< (1 : Nat)) + ncl +
                        ncl + ncl + (st0.scratch.tarjan_mark[
                          (flip_lit.setWidth 64).toNat]'hfl_tmk).setWidth 64 +
                        k).toNat]'hidx_occ).toNat < ncl.toNat := by c0_bound
                    generalize hv32 : st.scratch.scratch_buf[(32#64 + (ncl <<< (1 : Nat)) + ncl +
                      ncl + ncl + (st0.scratch.tarjan_mark[
                        (flip_lit.setWidth 64).toNat]'hfl_tmk).setWidth 64 +
                      k).toNat]'hidx_occ = c32 at hcb ⊢
                    have hc_lt : c32.toNat < ncl.toNat := hcb
                    have hsat_lt :
                        (32#64 + (ncl <<< (1 : Nat)) + c32.setWidth 64).toNat <
                          st.scratch.scratch_buf.length := by
                      rw [hsblk, BitVec.toNat_add, BitVec.toNat_add, hsh_ncl,
                        show (32#64 : BitVec 64).toNat = 32 from rfl,
                        zext_toNat (n := 64) c32 (by decide),
                        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                      omega
                    m7_hsteps_nj
                    obtain ⟨st_s1, hcs1, hls1, hes1, hms1⟩ :=
                      m7_state_abs st hm rfl (m7_len_scrBuf hlenk) (m7_ext_scrBuf st _)
                    clear hm
                    refine wp_join_safety_slice (fullSafetySlice c) st_s1 R
                      (fun _ => True) trivial
                      (fun st' (cu', ()) => cu'.toNat ≤ ncl.toNat ∧
                        FullExtScratchPres st_s1 st')
                      (fun _ st' ⟨cu', ⟨⟩⟩ m' hcore' hlen' _ ⟨hcu', hext'⟩ hm' =>
                        hJc st' (cu', ()) m' hm' (hcs1.trans hcore') hlen'
                          ⟨hcu', m7_ext_trans hes1 hext'⟩)
                      (fun Jz hJz => ?_)
                    dsimp only [fullSafetySlice] at hJz
                    m7_hsteps_nj
                    · have hupos_lt :
                          (32#64 + (ncl <<< (1 : Nat)) + ncl + c32.setWidth 64).toNat <
                            st_s1.scratch.scratch_buf.length := by
                        rw [hls1.scratch_ok.scratch_buf_len]
                        simp only [BitVec.toNat_add, hsh_ncl,
                          show (32#64 : BitVec 64).toNat = 32 from rfl, m7_zext32,
                          Nat.mod_add_mod]
                        rw [Nat.mod_eq_of_lt (by omega)]; omega
                      have hcu_pos : 0 < cu.toNat := by assumption
                      m7_hsteps_nj
                      refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) st_s1 R
                        (fun _ => True) trivial
                        (fun st' (cu', ()) => cu'.toNat ≤ ncl.toNat ∧
                          FullExtScratchPres st_s1 st')
                        (fun _ st' ⟨cu', ⟨⟩⟩ m' hcore' hlen' _ ⟨hcu', hext'⟩ hm' => by
                          dsimp only [fullSafetySlice] at hcore' hlen' hm'
                          m7_hsteps_nj
                          exact hJz st' (cu', ()) m' hm' hcore' hlen' ⟨hcu', hext'⟩)
                        (fun Jl hJl => ?_)
                      dsimp only [fullSafetySlice] at hJl
                      c0_let_simp
                      refine wp_jnz_of (fun hc => ?_) (fun hc => ?_)
                      all_goals
                        (try simp only [Arg.val_var] at hc)
                        c0_cond hc; try c0_let_simp
                      · have hupos_idx_eq :
                            (32 + 2 * ncl.toNat + ncl.toNat + c32.toNat) % 2 ^ 64 =
                            (32#64 + (ncl <<< (1 : Nat)) + ncl + c32.setWidth 64).toNat := by
                          simp only [BitVec.toNat_add, hsh_ncl,
                            show (32#64 : BitVec 64).toNat = 32 from rfl, m7_zext32,
                            Nat.mod_add_mod]
                        have hpos_cu : (st_s1.scratch.scratch_buf[(32#64 + (ncl <<< (1 : Nat)) +
                            ncl + c32.setWidth 64).toNat]'hupos_lt).toNat < cu.toNat := by
                          have hc' : st_s1.scratch.scratch_buf[(32 + 2 * ncl.toNat + ncl.toNat +
                              c32.toNat) % 2 ^ 64].toNat < cu.toNat := hc
                          simpa only [hupos_idx_eq] using hc'
                        have hsum_pos :
                            0 < (32#64 + (ncl <<< (1 : Nat)) + ncl + ncl + cu).toNat ∧
                            (32#64 + (ncl <<< (1 : Nat)) + ncl + ncl + cu).toNat =
                              32 + 4 * ncl.toNat + cu.toNat := by
                          simp only [BitVec.toNat_add, hsh_ncl,
                            show (32#64 : BitVec 64).toNat = 32 from rfl, Nat.mod_add_mod]
                          rw [Nat.mod_eq_of_lt (by omega)]; omega
                        have hlast_lt' :
                            (32#64 + (ncl <<< (1 : Nat)) + ncl + ncl + cu - 1#64).toNat <
                              st_s1.scratch.scratch_buf.length := by
                          rw [hls1.scratch_ok.scratch_buf_len, m7_bv64_sub1_toNat hsum_pos.1,
                            hsum_pos.2]
                          omega
                        have hpos_unsat_lt :
                            (32#64 + (ncl <<< (1 : Nat)) + ncl + ncl +
                              (st_s1.scratch.scratch_buf[(32#64 + (ncl <<< (1 : Nat)) +
                                ncl + c32.setWidth 64).toNat]'hupos_lt).setWidth 64).toNat <
                              st_s1.scratch.scratch_buf.length := by
                          have hp := hpos_cu
                          rw [hls1.scratch_ok.scratch_buf_len]
                          simp only [BitVec.toNat_add, hsh_ncl,
                            show (32#64 : BitVec 64).toNat = 32 from rfl, m7_zext32,
                            Nat.mod_add_mod] at hp ⊢
                          rw [Nat.mod_eq_of_lt (by omega)]; omega
                        m7_hsteps_nj
                        obtain ⟨st_s2, hcs2, hls2, hes2, hms2⟩ :=
                          m7_state_abs st_s1 hm rfl (m7_len_scrBuf hls1) (m7_ext_scrBuf st_s1 _)
                        clear hm
                        refine wp_join_safety_slice (ts := []) (fullSafetySlice c) st_s2 R
                          (fun _ => True) trivial (fun st' _ => FullExtScratchPres st_s2 st')
                          (fun _ st' ⟨⟩ m' hcore' hlen' _ hext' hm' => ?_)
                          (fun Js_1 hJs_1 => ?_)
                        · dsimp only [fullSafetySlice] at hcore' hlen' hm'
                          have hupos_c32_lt :
                              (32#64 + (ncl <<< (1 : Nat)) + ncl + c32.setWidth 64).toNat <
                                st'.scratch.scratch_buf.length := by
                            rw [hlen'.scratch_ok.scratch_buf_len]
                            simp only [BitVec.toNat_add, hsh_ncl,
                              show (32#64 : BitVec 64).toNat = 32 from rfl, m7_zext32,
                              Nat.mod_add_mod]
                            rw [Nat.mod_eq_of_lt (by omega)]; omega
                          m7_hsteps_nj
                          obtain ⟨st_s3, hcs3, hls3, hes3, hms3⟩ :=
                            m7_state_abs st' hm rfl (m7_len_scrBuf hlen') (m7_ext_scrBuf st' _)
                          exact hJl st_s3 (cu - 1#64, ()) _ hms3 (hcs2.trans (hcore'.trans hcs3))
                            hls3 ⟨m7_sub1_le hcu_pos hcu,
                              m7_ext_trans hes2 (m7_ext_trans hext' hes3)⟩
                        · dsimp only [fullSafetySlice] at hJs_1
                          have hupos_v_lt : ∀ v : BitVec 32, v.toNat < ncl.toNat →
                              (32#64 + (ncl <<< (1 : Nat)) + ncl + v.setWidth 64).toNat <
                                st_s2.scratch.scratch_buf.length := fun v hv => by
                            rw [hls2.scratch_ok.scratch_buf_len]
                            simp only [BitVec.toNat_add, hsh_ncl,
                              show (32#64 : BitVec 64).toNat = 32 from rfl, m7_zext32,
                              Nat.mod_add_mod]
                            rw [Nat.mod_eq_of_lt (by omega)]; omega
                          c0_let_simp
                          refine wp_jnz_of (fun hc2 => ?_) (fun hc2 => ?_)
                          all_goals
                            (try simp only [Arg.val_var] at hc2)
                            c0_cond hc2; try c0_let_simp
                          · have hupos_ld_lt := hupos_v_lt _ (by simpa only [m7_zext32] using hc2)
                            m7_hsteps_nj
                            obtain ⟨st_s3, hcs3, hls3, hes3, hms3⟩ :=
                              m7_state_abs st_s2 hm rfl (m7_len_scrBuf hls2)
                                (m7_ext_scrBuf st_s2 _)
                            exact hJs_1 st_s3 () _ hms3 hcs3 hls3 hes3
                          · exact hJs_1 st_s2 () _ hms2 rfl hls2 (m7_ext_refl st_s2)
                      · exact hJl st_s1 (cu, ()) m hms1 rfl hls1 ⟨hcu, m7_ext_refl st_s1⟩
                    · exact hJz _ (cu, ()) _ hms1 rfl hls1 ⟨hcu, m7_ext_refl st_s1⟩
                    · exact hJz _ (cu, ()) _ hms1 rfl hls1 ⟨hcu, m7_ext_refl st_s1⟩
                    · exact hJz _ (cu, ()) _ hms1 rfl hls1 ⟨hcu, m7_ext_refl st_s1⟩
                  · exact hJc st (cu, ()) mk hmk rfl hlenk ⟨hcu, m7_ext_refl st⟩
              · exact hJ1 st (cu, _, ()) mk hmk hcorek hlenk ⟨hcu, hextk⟩
          · intro Jlm hJlm; m7_hsteps_nj
            · have hmk_le := m7_rem1_mod h5n hscr ‹_›
              have hmk_le' : ((st0.scratch.tarjan_mark[
                    (flip_lit.setWidth 64).toNat]'hfl_tmk).setWidth 64).toNat ≤
                  c.scratch_cap - (32 + 5 * ncl.toNat) := by
                simpa only [m7_zext32] using hmk_le
              exact hJlm (_, ()) m0 ⟨hm0', m7_rem_sub_le rfl h5n hscr hmk_le'⟩
            · have hmk_le := m7_rem1_mod h5n hscr ‹_›
              have hreach_le := m7_rem2_mod h5n hscr hmk_le ‹_›
              have hrz : ((st0.scratch.tarjan_reach[
                    (flip_lit.setWidth 64).toNat]'hfl_trc).setWidth 64).toNat ≤
                  c.scratch_cap - (32 + 5 * ncl.toNat) -
                    ((st0.scratch.tarjan_mark[
                      (flip_lit.setWidth 64).toNat]'hfl_tmk).setWidth 64).toNat := by
                simpa only [m7_zext32] using hreach_le
              exact hJlm (_, ()) m0 ⟨hm0', hrz⟩
        · exact hJ1 st0 (cu0, _, ()) m0 hm0' rfl hlen0 ⟨hcu0, m7_ext_refl st0⟩
    · intro Jcu hJcu; m7_hsteps_nj
      · exact hJcu (ncl, ()) _ ⟨hm0, Nat.le_refl _⟩
      · exact hJcu (ulen, ()) _ ⟨hm0, by c0_bound⟩

end HelpersPart3

theorem m7CollectSpec_eq :
    m7CollectSpec = SafetySlice.spec (as := [i64]) (rs := [i64]) fullSafetySlice
      (fun c x _ => match x with | (h, ()) => h = c.hdr)
      (fun _ _ _ s s' => FullExtScratchPres s s') := by
  unfold m7CollectSpec; rfl

theorem m7BuildOccSpec_eq :
    m7BuildOccSpec = SafetySlice.spec (as := [i64, i64]) (rs := [i64]) fullSafetySlice
      (fun c x _ => match x with | (h, _ncl, ()) => h = c.hdr)
      (fun _ x r s s' => match x with
        | (_, ncl, ()) => match r with
          | (rv, ()) => FullExtScratchPres s s' ∧ rv.toNat ≤ ncl.toNat) := by
  unfold m7BuildOccSpec; rfl

theorem m7PickSpec_eq :
    m7PickSpec = SafetySlice.spec (as := [i64, i32, i64]) (rs := [i64]) fullSafetySlice
      (fun c x _ => match x with | (h, _cl, _ncl, ()) => h = c.hdr)
      (fun _ _ _ s s' => FullExtScratchPres s s') := by
  unfold m7PickSpec; rfl

theorem m7CbInvSpec_noExit {a m Q X X'} (h : m7CbInvSpec a m Q X) :
    m7CbInvSpec a m Q X' :=
  SafetySlice.spec_noExit h

theorem m7InitTableSpec_noExit {a m Q X X'} (h : m7InitTableSpec a m Q X) :
    m7InitTableSpec a m Q X' :=
  SafetySlice.spec_noExit h

theorem m7EffortSpec_noExit {a m Q X X'} (h : m7EffortSpec a m Q X) :
    m7EffortSpec a m Q X' :=
  SafetySlice.spec_noExit h

theorem m7InitValsSpec_noExit {a m Q X X'} (h : m7InitValsSpec a m Q X) :
    m7InitValsSpec a m Q X' :=
  SafetySlice.spec_noExit h

theorem m7CollectSpec_noExit {a m Q X X'} (h : m7CollectSpec a m Q X) :
    m7CollectSpec a m Q X' :=
  SafetySlice.spec_noExit h

theorem m7BuildOccSpec_noExit {a m Q X X'} (h : m7BuildOccSpec a m Q X) :
    m7BuildOccSpec a m Q X' :=
  SafetySlice.spec_noExit h

theorem m7BreakSpec_noExit {a m Q X X'} (h : m7BreakSpec a m Q X) :
    m7BreakSpec a m Q X' :=
  SafetySlice.spec_noExit h

theorem m7PickSpec_noExit {a m Q X X'} (h : m7PickSpec a m Q X) :
    m7PickSpec a m Q X' :=
  SafetySlice.spec_noExit h

theorem m7FlipSpec_noExit {a m Q X X'} (h : m7FlipSpec a m Q X) :
    m7FlipSpec a m Q X' :=
  SafetySlice.spec_noExit h

theorem m7SaveMinSpec_noExit {a m Q X X'} (h : m7SaveMinSpec a m Q X) :
    m7SaveMinSpec a m Q X' :=
  SafetySlice.spec_noExit h

end LeanQbe.T.Examples.Kissat.FullM7Walk
