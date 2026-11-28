/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2RSort
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA `ar_build_R` Pass 1 WP (`Arisca.Proof.Poly2R`)

`XPost`-polymorphic `Mem 64` WP proof for Pass 1 (`i < cnt` flip scan, fast path when
`!any && !fv_b`, and handoff into Pass 2..4 `buildR_pass2_wp` / `buildR_sort_wp`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Poly

public section

private theorem rule_range_bounds {nOut : Nat} {s : ArCtxState}
    {ruleOff ruleN rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool : List (BitVec 32)} {σ : Nat → Bool} {v : BitVec 32}
    (hv : v.toNat < s.n_nets.toNat) (hne : ruleN.getD v.toNat 0#32 ≠ cNone32)
    (hr : RulesRep nOut σ s ruleOff ruleN rsM rsL rsH rsPool) :
    (ruleOff.getD v.toNat 0#32).toNat + (ruleN.getD v.toNat 0#32).toNat ≤ s.rs_n.toNat ∧
      bv nOut (σ (2 * v.toNat)) = polyEvalRange nOut σ rsPool rsM rsL rsH
        (ruleOff.getD v.toNat 0#32).toNat (ruleN.getD v.toNat 0#32).toNat := by
  have h1 := hr.2.2.2.2.2.2.2.2.2 v.toNat hv hne
  exact ⟨h1.1, h1.2⟩

private theorem bv64_zext32_p1 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans x.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

private theorem pass1_any_eq (any : Bool) (flippedArr : List (BitVec 8))
    (rsPool rsM : List (BitVec 32)) (off i : Nat) (f : BitVec 32)
    (hany : any = decide (∃ t < i,
      flipCount flippedArr (symListAt rsPool (rsM.getD (off + t) 0#32).toNat) ≠ 0))
    (hf : f.toNat = flipCount flippedArr (symListAt rsPool (rsM.getD (off + i) 0#32).toNat)) :
    (any || (f != 0#32)) = decide (∃ t < i + 1,
      flipCount flippedArr (symListAt rsPool (rsM.getD (off + t) 0#32).toNat) ≠ 0) := by
  have hf_ne : (f != 0#32) = decide
      (flipCount flippedArr (symListAt rsPool (rsM.getD (off + i) 0#32).toNat) ≠ 0) := by
    rw [← hf]
    by_cases h0 : f = 0#32
    · subst h0; simp
    · have hnat : f.toNat ≠ 0 := fun hz => h0 (BitVec.eq_of_toNat_eq (by simpa using hz))
      simp [h0, hnat]
  rw [hany, hf_ne]
  by_cases h1 : ∃ t < i,
      flipCount flippedArr (symListAt rsPool (rsM.getD (off + t) 0#32).toNat) ≠ 0
  · have h1' : ∃ t < i + 1,
        flipCount flippedArr (symListAt rsPool (rsM.getD (off + t) 0#32).toNat) ≠ 0 :=
      ⟨h1.choose, Nat.lt_trans h1.choose_spec.1 (Nat.lt_succ_self i), h1.choose_spec.2⟩
    rw [decide_eq_true h1, decide_eq_true h1']; simp
  · rw [decide_eq_false h1, Bool.false_or]
    by_cases h2 : flipCount flippedArr (symListAt rsPool (rsM.getD (off + i) 0#32).toNat) ≠ 0
    · have h2' : ∃ t < i + 1,
          flipCount flippedArr (symListAt rsPool (rsM.getD (off + t) 0#32).toNat) ≠ 0 :=
        ⟨i, Nat.lt_succ_self i, h2⟩
      rw [decide_eq_true h2, decide_eq_true h2']
    · have hnone : ¬ ∃ t < i + 1,
          flipCount flippedArr (symListAt rsPool (rsM.getD (off + t) 0#32).toNat) ≠ 0 := by
        rintro ⟨t, ht, hne⟩
        by_cases hti : t = i
        · subst hti; exact h2 hne
        · exact h1 ⟨t, by omega, hne⟩
      rw [decide_eq_false h2, decide_eq_false hnone]

private theorem fast_pack_mem {cx : BitVec 64} {s0 s s' : ArCtxState}
    {ruleOff ruleN rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rm : List (BitVec 32)} {rl rh : List (BitVec 64)}
    {rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)}
    {rpool ix ix2 : List (BitVec 32)} {Rest R : Mem 64 → Prop} {m : Mem 64}
    (h1 : (arCtxMem cx s ⋆ Rest) m) (hs : s = s')
    (hrest : Rest = (array (t := i32) s0.rule_off ruleOff ⋆
      array (t := i32) s0.rule_n ruleN ⋆ array (t := i8) s0.flipped flippedArr ⋆
      rsMem s0 rsM rsL rsH rsPool ⋆ rMem s0 rm rl rh rm2 rl2 rh2 rpool ⋆
      array (t := i32) s0.ix ix ⋆ array (t := i32) s0.ix2 ix2 ⋆ R))
    (hro : s'.rule_off = s0.rule_off := by rfl) (hrn : s'.rule_n = s0.rule_n := by rfl)
    (hfl : s'.flipped = s0.flipped := by rfl)
    (hrm : s'.rs_m = s0.rs_m := by rfl) (hrl : s'.rs_l = s0.rs_l := by rfl)
    (hrh : s'.rs_h = s0.rs_h := by rfl) (hrp : s'.rs_pool = s0.rs_pool := by rfl)
    (hm1 : s'.rm = s0.rm := by rfl) (hl1 : s'.rl = s0.rl := by rfl)
    (hh1 : s'.rh = s0.rh := by rfl) (hm2 : s'.rm2 = s0.rm2 := by rfl)
    (hl2 : s'.rl2 = s0.rl2 := by rfl) (hh2 : s'.rh2 = s0.rh2 := by rfl)
    (hpo : s'.rpool = s0.rpool := by rfl)
    (hix : s'.ix = s0.ix := by rfl) (hix2 : s'.ix2 = s0.ix2 := by rfl) :
    (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆
      array (t := i32) s'.rule_n ruleN ⋆ array (t := i8) s'.flipped flippedArr ⋆
      rsMem s' rsM rsL rsH rsPool ⋆ rMem s' rm rl rh rm2 rl2 rh2 rpool ⋆
      array (t := i32) s'.ix ix ⋆ array (t := i32) s'.ix2 ix2 ⋆ R) m := by
  subst hs
  have hrs : rsMem s rsM rsL rsH rsPool = rsMem s0 rsM rsL rsH rsPool := by
    simp only [rsMem, hrm, hrl, hrh, hrp]
  have hrmem : rMem s rm rl rh rm2 rl2 rh2 rpool = rMem s0 rm rl rh rm2 rl2 rh2 rpool := by
    simp only [rMem, hm1, hl1, hh1, hm2, hl2, hh2, hpo]
  rw [hrest] at h1
  rw [hro, hrn, hfl, hrs, hrmem, hix, hix2]; exact sep_cast h1 (by ac_rfl)

private theorem buildR_pass1_bounds
    {fv_b : Bool} {off cnt i mlenBv fF : BitVec 32} {bt bw : BitVec 64}
    {s : ArCtxState} {flippedArr : List (BitVec 8)} {rsPool rsM : List (BitVec 32)}
    (hoff_cnt : off.toNat + cnt.toNat ≤ s.rs_n.toNat) (hi_lt : i.toNat < cnt.toNat)
    (hmOff_ptop : (rsM.getD (off.toNat + i.toNat) 0#32).toNat + 1 + mlenBv.toNat ≤ s.rs_ptop.toNat)
    (hwords_rs : monoTotalWords rsPool rsM s.rs_n.toNat ≤ s.rs_pcap.toNat)
    (hfF_le24 : fF.toNat ≤ arRMaxF)
    (hmax_lt : ∀ t < i.toNat,
      flipCount flippedArr (symListAt rsPool (rsM.getD (off.toNat + t) 0#32).toNat) ≤ arRMaxF)
    (hbt_eq : bt.toNat = (if fv_b then 1 else 0) + ruleBt8 flippedArr rsPool rsM off.toNat i.toNat)
    (hbw_eq : bw.toNat = (if fv_b then 1 else 0) + ruleBw8 flippedArr rsPool rsM off.toNat i.toNat)
    (hrs_ptop : s.rs_ptop.toNat ≤ s.rs_pcap.toNat) (hrsp_32 : s.rs_pcap.toNat < 2 ^ 32) :
    bt.toNat + 2 ^ fF.toNat < 2 ^ 64 ∧
    bw.toNat + 2 ^ fF.toNat * (mlenBv.toNat + 1) < 2 ^ 64 ∧
    (1#64 : BitVec 64) <<< ((BitVec.setWidth 64 fF).toNat % 64) =
      1#64 <<< BitVec.setWidth 64 fF := by
  have hif_le1 : (if fv_b then 1 else 0) ≤ 1 := by split <;> omega
  have hp24 : (2 ^ arRMaxF : Nat) = 16777216 := by decide
  have hp2 : 2 ^ fF.toNat ≤ 2 ^ arRMaxF := Nat.pow_le_pow_right (by decide) hfF_le24
  have hbt_lt64 : bt.toNat + 2 ^ fF.toNat < 2 ^ 64 := by
    have hbd := bt_pass1_bound hmax_lt
    have hi32 : i.toNat < 2 ^ 32 := i.isLt
    have hbd' : ruleBt8 flippedArr rsPool rsM off.toNat i.toNat ≤ 16777216 * i.toNat := by
      simpa [hp24, Nat.mul_comm] using hbd
    rw [hbt_eq]; omega
  have hbw_lt64 : bw.toNat + 2 ^ fF.toNat * (mlenBv.toNat + 1) < 2 ^ 64 := by
    have hbd := bw_pass1_bound (rpcap := s.rs_pcap.toNat) hoff_cnt hwords_rs
      hmax_lt (Nat.le_of_lt hi_lt)
    have hml_lt : mlenBv.toNat + 1 ≤ s.rs_pcap.toNat := by omega
    have hstep_bd : 2 ^ fF.toNat * (mlenBv.toNat + 1) ≤ 2 ^ arRMaxF * s.rs_pcap.toNat :=
      Nat.mul_le_mul hp2 hml_lt
    have hbd' : ruleBw8 flippedArr rsPool rsM off.toNat i.toNat ≤
        16777216 * monoTotalWords rsPool rsM s.rs_n.toNat := by
      simpa [hp24] using hbd
    have hw_mul : 16777216 * monoTotalWords rsPool rsM s.rs_n.toNat ≤ 16777216 * s.rs_pcap.toNat :=
      Nat.mul_le_mul_left 16777216 hwords_rs
    have hstep' : 2 ^ fF.toNat * (mlenBv.toNat + 1) ≤ 16777216 * s.rs_pcap.toNat := by
      simpa [hp24] using hstep_bd
    rw [hbw_eq]; omega
  have hshl_nat : (BitVec.setWidth 64 fF).toNat % 64 = fF.toNat := by
    have har : arRMaxF = 24 := rfl
    rw [bv64_zext32_p1, Nat.mod_eq_of_lt (by omega : fF.toNat < 64)]
  have hshl_eq : (1#64 : BitVec 64) <<< ((BitVec.setWidth 64 fF).toNat % 64) =
      1#64 <<< BitVec.setWidth 64 fF := by
    rw [hshl_nat]; apply BitVec.eq_of_toNat_eq
    change (1#64 <<< fF.toNat).toNat = (1#64 <<< (BitVec.setWidth 64 fF).toNat).toNat
    rw [bv64_zext32_p1]
  exact ⟨hbt_lt64, hbw_lt64, hshl_eq⟩

private theorem buildR_pass1_full_handoff (Γ : T.Env)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    (hCneg : ∀ xs m Q X, arCnegSpec xs m Q X → Γ "ar_cneg" [i64, i64, i64] [i64, i64] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    {cx : BitVec 64} {v off cnt : BitVec 32} {fv_b any : Bool} {bt bw : BitVec 64}
    {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rm : List (BitVec 32)} {rl rh : List (BitVec 64)}
    {rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)}
    {rpool ix ix2 : List (BitVec 32)} {Valid : (Nat → Bool) → Prop}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hoff_def : off = ruleOff.getD v.toNat 0#32) (hcnt_def : cnt = ruleN.getD v.toNat 0#32)
    (hfv_def : fv_b = (flippedArr.getD v.toNat 0#8 != 0#8))
    (hv_lt : v.toNat < s.n_nets.toNat) (hne : ruleN.getD v.toNat 0#32 ≠ cNone32)
    (hnn_bd : s.n_nets.toNat ≤ 0x3FFFFFFF) (hfl_len : s.n_nets.toNat ≤ flippedArr.length)
    (hqcap_lo : 16 ≤ s.qcap.toNat) (hqcap_hi : s.qcap.toNat + 16 < 2 ^ 32)
    (hrcap_le : s.rcap.toNat ≤ s.qcap.toNat) (hrpcap_32 : s.rpcap.toNat < 2 ^ 32)
    (hrsp_32 : s.rs_pcap.toNat < 2 ^ 32)
    (hrm_len : s.rcap.toNat ≤ rm.length) (hrl_len : s.rcap.toNat ≤ rl.length)
    (hrh_len : s.rcap.toNat ≤ rh.length) (hrm2_len : s.rcap.toNat ≤ rm2.length)
    (hrl2_len : s.rcap.toNat ≤ rl2.length) (hrh2_len : s.rcap.toNat ≤ rh2.length)
    (hrpool_len : s.rpcap.toNat ≤ rpool.length) (hix_eq : ix.length = ix2.length)
    (hix_len : s.qcap.toNat ≤ ix.length) (hMasks : MasksOk s.modW s.mlo s.mhi)
    (hoff_cnt : off.toNat + cnt.toNat ≤ s.rs_n.toNat)
    (hrs_n_le : s.rs_n.toNat ≤ s.rs_cap.toNat) (hrs_cap_le : s.rs_cap.toNat ≤ rsM.length)
    (hrsL_len : s.rs_cap.toNat ≤ rsL.length) (hrsH_len : s.rs_cap.toNat ≤ rsH.length)
    (hrsPool_len : s.rs_pcap.toNat ≤ rsPool.length) (hrs_ptop : s.rs_ptop.toNat ≤ s.rs_pcap.toNat)
    (hRsSl : ∀ i < s.rs_n.toNat, MonoSliceOk rsPool (rsM.getD i 0#32).toNat s.rs_ptop.toNat ∧
      (rsPool.getD (rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hRsSorted : RulesSorted rsPool rsM s.rs_n.toNat)
    (hRsSyms : SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat)
    (hmax_lt : ∀ t < cnt.toNat,
      flipCount flippedArr (symListAt rsPool (rsM.getD (off.toNat + t) 0#32).toNat) ≤ arRMaxF)
    (hbt_eq : bt.toNat =
      (if fv_b then 1 else 0) + ruleBt8 flippedArr rsPool rsM off.toNat cnt.toNat)
    (hbw_eq : bw.toNat =
      (if fv_b then 1 else 0) + ruleBw8 flippedArr rsPool rsM off.toNat cnt.toNat)
    (hRules : ∀ σ, Valid σ →
      (∀ w < s.n_nets.toNat, σ (2 * w + 1) = !(σ (2 * w))) ∧
      RulesRep s.modW σ s ruleOff ruleN rsM rsL rsH rsPool)
    (hm : (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i8) s.flipped flippedArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
      rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ array (t := i32) s.ix ix ⋆
      array (t := i32) s.ix2 ix2 ⋆ R) m)
    (hQ_false : Q (false, ⟨⟩) m)
    (hQ_full : ∀ (k2 : BitVec 32) (s' : ArCtxState)
        (rm' : List (BitVec 32)) (rl' rh' : List (BitVec 64))
        (rm2' : List (BitVec 32)) (rl2' rh2' : List (BitVec 64))
        (rpool' ix' ix2' : List (BitVec 32)) (m' : Mem 64),
      s' = { s with
        cur_rm := s.rm2, cur_rl := s.rl2, cur_rh := s.rh2,
        cur_rp := s.rpool, cur_nr := k2 } →
      k2.toNat ≤ s.rcap.toNat →
      rm'.length = rm.length → rl'.length = rl.length → rh'.length = rh.length →
      rm2'.length = rm2.length → rl2'.length = rl2.length → rh2'.length = rh2.length →
      rpool'.length = rpool.length → ix'.length = ix.length → ix2'.length = ix2.length →
      (∀ σ, Valid σ → CurRRep s.modW σ k2.toNat
        (if flippedArr.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat)
        rm2' rl2' rh2' rpool') →
      (∀ r < k2.toNat, MonoSliceOk rpool' (rm2'.getD r 0#32).toNat rpool'.length ∧
        (rpool'.getD (rm2'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ r < k2.toNat, MonoSorted rpool' (rm2'.getD r 0#32).toNat) →
      monoTotalWords rpool' rm2' k2.toNat ≤ s.rpcap.toNat →
      SymsBound rpool' rm2' k2.toNat s.n_nets.toNat →
      (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆ array (t := i32) s'.rule_n ruleN ⋆
        array (t := i8) s'.flipped flippedArr ⋆ rsMem s' rsM rsL rsH rsPool ⋆
        rMem s' rm' rl' rh' rm2' rl2' rh2' rpool' ⋆ array (t := i32) s'.ix ix' ⋆
        array (t := i32) s'.ix2 ix2' ⋆ R) m' →
      Q (true, ⟨⟩) m') :
    wp Γ Q X (buildRPass2EntryExpr cx v off cnt fv_b any bt bw) m := by
  have hEv_rules : ∀ σ, Valid σ →
      (if fv_b then 1#(s.modW) else 0#(s.modW)) +
        (if fv_b then
          -polyEvalRange s.modW σ rsPool rsM rsL rsH off.toNat cnt.toNat
         else polyEvalRange s.modW σ rsPool rsM rsL rsH off.toNat cnt.toNat) =
      bv s.modW
        (σ (if flippedArr.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat)) := by
    intro σ hσ
    have hR := hRules σ hσ
    have hrr := (rule_range_bounds hv_lt hne hR.2).2
    have hfb_eq : (flippedArr.getD v.toNat 0#8 ≠ 0#8) ↔ fv_b = true := by rw [hfv_def]; simp
    have hev := rules_flipped_eval s.modW v.toNat σ rsPool rsM rsL rsH off.toNat
      cnt.toNat fv_b (hR.1 v.toNat hv_lt) (by rw [← hoff_def, ← hcnt_def] at hrr; exact hrr)
    cases hfv : fv_b <;> simp [hfv] at hfb_eq <;> simp [hfb_eq] <;> simpa [hfv] using hev
  refine buildR_pass2_wp Γ hCneg (R := array (t := i32) s.ix ix ⋆ array (t := i32) s.ix2 ix2 ⋆ R)
    hv_lt hnn_bd hfl_len hqcap_lo hqcap_hi hrcap_le hrpcap_32 hrsp_32 hrm_len hrl_len hrh_len
    hrpool_len hMasks hoff_cnt hrs_n_le hrs_cap_le
    hrsL_len hrsH_len hrsPool_len hrs_ptop hRsSl hRsSorted hRsSyms
    hmax_lt hbt_eq hbw_eq
    (sep_cast hm (by ac_rfl)) hQ_false ?_
  intro nFinal rm' rl' rh' rpool' m' hn_eq hn_rcap hn_qcap hrm' hrl' hrh' hrpool'
    hSl' hSorted' hW' hSb' hEv' hm'
  refine buildR_sort_wp Γ hMcmp hCadd (Valid := Valid) (rl := rl') (rh := rh') (R := R)
    hn_rcap hn_qcap (Nat.le_trans (by decide) hqcap_lo) hqcap_hi hrpcap_32 (by omega) (by omega)
    (by omega) hrm2_len hrl2_len hrh2_len (by omega) hix_eq hix_len hMasks hSl' hSorted' hW' hSb' ?_
    (sep_cast hm' (by ac_rfl)) ?_
  · intro σ hσ
    rw [hEv' σ (hRules σ hσ).1]
    exact hEv_rules σ hσ
  · intro k2 s' rm2' rl2' rh2' ix' ix2' m'' hs' hk2 hrm2' hrl2' hrh2' hix' hix2'
      hCur hSl'' hSorted'' hW'' hSb'' hm''
    exact hQ_full k2 s' rm' rl' rh' rm2' rl2' rh2' rpool' ix' ix2' m'' hs' hk2
      hrm' hrl' hrh' hrm2' hrl2' hrh2' hrpool' hix' hix2' hCur hSl'' hSorted'' hW'' hSb'' hm''

/-- Complete `XPost`-polymorphic `Mem 64` WP theorem for `ar_build_R(cx, v)`. -/
theorem buildR_pass1_wp (Γ : T.Env)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    (hCneg : ∀ xs m Q X, arCnegSpec xs m Q X → Γ "ar_cneg" [i64, i64, i64] [i64, i64] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    {cx : BitVec 64} {v : BitVec 32}
    {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rm : List (BitVec 32)} {rl rh : List (BitVec 64)}
    {rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)}
    {rpool ix ix2 : List (BitVec 32)} {Valid : (Nat → Bool) → Prop}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hv_lt : v.toNat < s.n_nets.toNat) (hne : ruleN.getD v.toNat 0#32 ≠ cNone32)
    (hnn_bd : s.n_nets.toNat ≤ 0x3FFFFFFF)
    (hoff_len : s.n_nets.toNat ≤ ruleOff.length) (hn_len : s.n_nets.toNat ≤ ruleN.length)
    (hfl_len : s.n_nets.toNat ≤ flippedArr.length)
    (hqcap_lo : 16 ≤ s.qcap.toNat) (hqcap_hi : s.qcap.toNat + 16 < 2 ^ 32)
    (hrcap_le : s.rcap.toNat ≤ s.qcap.toNat) (hrpcap_32 : s.rpcap.toNat < 2 ^ 32)
    (hrsp_32 : s.rs_pcap.toNat < 2 ^ 32)
    (hrm_len : s.rcap.toNat ≤ rm.length) (hrl_len : s.rcap.toNat ≤ rl.length)
    (hrh_len : s.rcap.toNat ≤ rh.length) (hrm2_len : s.rcap.toNat ≤ rm2.length)
    (hrl2_len : s.rcap.toNat ≤ rl2.length) (hrh2_len : s.rcap.toNat ≤ rh2.length)
    (hrpool_len : s.rpcap.toNat ≤ rpool.length) (hix_eq : ix.length = ix2.length)
    (hix_len : s.qcap.toNat ≤ ix.length) (hMasks : MasksOk s.modW s.mlo s.mhi)
    (hrs_n_le : s.rs_n.toNat ≤ s.rs_cap.toNat) (hrs_cap_bd : s.rs_cap.toNat < 2 ^ 30)
    (hrs_cap_le : s.rs_cap.toNat ≤ rsM.length)
    (hrsL_len : s.rs_cap.toNat ≤ rsL.length) (hrsH_len : s.rs_cap.toNat ≤ rsH.length)
    (hrsPool_len : s.rs_pcap.toNat ≤ rsPool.length) (hrs_ptop : s.rs_ptop.toNat ≤ s.rs_pcap.toNat)
    (hRsSl : ∀ i < s.rs_n.toNat, MonoSliceOk rsPool (rsM.getD i 0#32).toNat s.rs_ptop.toNat ∧
      (rsPool.getD (rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hRsSorted : RulesSorted rsPool rsM s.rs_n.toNat)
    (hRsWords : monoTotalWords rsPool rsM s.rs_n.toNat ≤ s.rs_ptop.toNat)
    (hRsSyms : SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat)
    (hValid : ∃ σ₀, Valid σ₀)
    (hRules : ∀ σ, Valid σ →
      (∀ w < s.n_nets.toNat, σ (2 * w + 1) = !(σ (2 * w))) ∧
      RulesRep s.modW σ s ruleOff ruleN rsM rsL rsH rsPool)
    (hm : (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i8) s.flipped flippedArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
      rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ array (t := i32) s.ix ix ⋆
      array (t := i32) s.ix2 ix2 ⋆ R) m)
    (hQ_false : Q (false, ⟨⟩) m)
    (hQ_fast : ∀ s' m',
      let off := (ruleOff.getD v.toNat 0#32).toNat
      s' = { s with
        cur_rm := s.rs_m + BitVec.ofNat 64 (4 * off),
        cur_rl := s.rs_l + BitVec.ofNat 64 (8 * off),
        cur_rh := s.rs_h + BitVec.ofNat 64 (8 * off),
        cur_rp := s.rs_pool, cur_nr := ruleN.getD v.toNat 0#32 } →
      flippedArr.getD v.toNat 0#8 = 0#8 →
      (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆ array (t := i32) s'.rule_n ruleN ⋆
        array (t := i8) s'.flipped flippedArr ⋆ rsMem s' rsM rsL rsH rsPool ⋆
        rMem s' rm rl rh rm2 rl2 rh2 rpool ⋆ array (t := i32) s'.ix ix ⋆
        array (t := i32) s'.ix2 ix2 ⋆ R) m' →
      Q (true, ⟨⟩) m')
    (hQ_full : ∀ (k2 : BitVec 32) (s' : ArCtxState)
        (rm' : List (BitVec 32)) (rl' rh' : List (BitVec 64))
        (rm2' : List (BitVec 32)) (rl2' rh2' : List (BitVec 64))
        (rpool' ix' ix2' : List (BitVec 32)) (m' : Mem 64),
      s' = { s with
        cur_rm := s.rm2, cur_rl := s.rl2, cur_rh := s.rh2,
        cur_rp := s.rpool, cur_nr := k2 } →
      k2.toNat ≤ s.rcap.toNat →
      rm'.length = rm.length → rl'.length = rl.length → rh'.length = rh.length →
      rm2'.length = rm2.length → rl2'.length = rl2.length → rh2'.length = rh2.length →
      rpool'.length = rpool.length → ix'.length = ix.length → ix2'.length = ix2.length →
      (∀ σ, Valid σ → CurRRep s.modW σ k2.toNat
        (if flippedArr.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat)
        rm2' rl2' rh2' rpool') →
      (∀ r < k2.toNat, MonoSliceOk rpool' (rm2'.getD r 0#32).toNat rpool'.length ∧
        (rpool'.getD (rm2'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ r < k2.toNat, MonoSorted rpool' (rm2'.getD r 0#32).toNat) →
      monoTotalWords rpool' rm2' k2.toNat ≤ s.rpcap.toNat →
      SymsBound rpool' rm2' k2.toNat s.n_nets.toNat →
      (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆ array (t := i32) s'.rule_n ruleN ⋆
        array (t := i8) s'.flipped flippedArr ⋆ rsMem s' rsM rsL rsH rsPool ⋆
        rMem s' rm' rl' rh' rm2' rl2' rh2' rpool' ⋆ array (t := i32) s'.ix ix' ⋆
        array (t := i32) s'.ix2 ix2' ⋆ R) m' →
      Q (true, ⟨⟩) m') :
    Func.wp Γ ar_build_R_body (cx, v, ⟨⟩) m Q X := by
  obtain ⟨σ₀, hσ₀⟩ := hValid
  have hσ₀_rule := rule_range_bounds hv_lt hne (hRules σ₀ hσ₀).2
  let off := ruleOff.getD v.toNat 0#32
  let cnt := ruleN.getD v.toNat 0#32
  let fv := flippedArr.getD v.toNat 0#8
  let fv_b := fv != 0#8
  have hoff_cnt : off.toNat + cnt.toNat ≤ s.rs_n.toNat := hσ₀_rule.1
  have hv_off : v.toNat < ruleOff.length := by omega
  have hv_n : v.toNat < ruleN.length := by omega
  have hv_fl : v.toNat < flippedArr.length := by omega
  have hm_rs : (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆
      array (t := i32) s.rule_n ruleN ⋆ array (t := i8) s.flipped flippedArr ⋆
      array (t := i32) s.rs_m rsM ⋆
      array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆ array (t := i32) s.rs_pool rsPool ⋆
      u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆
      rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ array (t := i32) s.ix ix ⋆
      array (t := i32) s.ix2 ix2 ⋆ R) m := by
    have h' := hm; rw [rsMem_unfold] at h'; exact sep_cast h' (by ac_rfl)
  dsimp only [Func.wp, ar_build_R_body]
  c0_hsteps_nogrp
  have hfv_eq : (BitVec.setWidth 32 (flippedArr[v.toNat]'hv_fl) != BitVec.ofNat 32 0) = fv_b := by
    dsimp only [fv_b, fv]; rw [← getD_eq_getElem flippedArr 0#8 hv_fl]
    by_cases h0 : flippedArr.getD v.toNat 0#8 = 0#8
    · rw [h0]; decide
    · have h1 : (BitVec.setWidth 32 (flippedArr.getD v.toNat 0#8) != BitVec.ofNat 32 0) = true := by
        rw [bne_iff_ne]; intro heq; apply h0
        apply BitVec.eq_of_toNat_eq
        have hlt := (flippedArr.getD v.toNat 0#8).isLt
        have heqN := congrArg BitVec.toNat heq
        simpa [BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (lt_trans hlt (by decide : 2 ^ 8 < 2 ^ 32))] using heqN
      have h2 : (flippedArr.getD v.toNat 0#8 != 0#8) = true := bne_iff_ne.mpr h0
      rw [h1, h2]
  have hoff_eq : ruleOff[v.toNat]'hv_off = off := (getD_eq_getElem ruleOff 0#32 hv_off).symm
  have hcnt_eq : ruleN[v.toNat]'hv_n = cnt := (getD_eq_getElem ruleN 0#32 hv_n).symm
  simp only [bv64_zext32_p1]
  rw [hfv_eq, hoff_eq, hcnt_eq]
  refine wp_join_group (fun ⟨bt0, _⟩ m0 => m0 = m ∧ bt0.toNat = if fv_b then 1 else 0) ?_ ?_
  · rintro Jbt ⟨bt0, ⟨⟩⟩ m0 ⟨hm0, hbt0⟩; cases hm0
    refine wp_join_group (fun ⟨bw0, _⟩ m1 => m1 = m ∧ bw0.toNat = if fv_b then 1 else 0) ?_ ?_
    · rintro Jbw ⟨bw0, ⟨⟩⟩ m1 ⟨hm1, hbw0⟩; cases hm1
      refine wp_loop_group (fun rem ⟨any, bt, bw, i, ⟨⟩⟩ m1 =>
          m1 = m ∧ i.toNat ≤ cnt.toNat ∧ rem = cnt.toNat - i.toNat ∧
          any = decide (∃ t < i.toNat,
            flipCount flippedArr (symListAt rsPool (rsM.getD (off.toNat + t) 0#32).toNat) ≠ 0) ∧
          (∀ t < i.toNat,
            flipCount flippedArr
              (symListAt rsPool (rsM.getD (off.toNat + t) 0#32).toNat) ≤ arRMaxF) ∧
          bt.toNat = (if fv_b then 1 else 0) + ruleBt8 flippedArr rsPool rsM off.toNat i.toNat ∧
          bw.toNat = (if fv_b then 1 else 0) + ruleBw8 flippedArr rsPool rsM off.toNat i.toNat)
        ?_ ?_
      · intro Ji rem ⟨any, bt, bw, i, ⟨⟩⟩ m1 hrec
          ⟨hm1, hi_le, hrem, hany_eq, hmax_lt, hbt_eq, hbw_eq⟩
        cases hm1; c0_hsplit
        · have hi_lt : i.toNat < cnt.toNat := hc; clear hc
          have hidx_rsn : off.toNat + i.toNat < s.rs_n.toNat := by omega
          have hidx_rs : (off + i).toNat = off.toNat + i.toNat := by
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : off.toNat + i.toNat < 2 ^ 32)]
          have hidx_lt_rsM : (off + i).toNat < rsM.length := by omega
          let mOffBv := rsM.getD (off.toNat + i.toNat) 0#32
          have hmOff_sl := hRsSl (off.toNat + i.toNat) hidx_rsn
          dsimp only [MonoSliceOk] at hmOff_sl
          have hmOff_lt_pool : mOffBv.toNat < rsPool.length := by
            have h1 := hmOff_sl.1.1; dsimp only [mOffBv]; omega
          let mlenBv := rsPool.getD mOffBv.toNat 0#32
          have hmlen_eq : mlenBv = rsPool.getD mOffBv.toNat 0#32 := rfl
          have hmOff_32 : mlenBv.toNat + 1 < 2 ^ 32 := hmOff_sl.2
          have hmlen_end : mOffBv.toNat + mlenBv.toNat + 1 ≤ rsPool.length := by
            have h2 := hmOff_sl.1.2; dsimp only [mOffBv, mlenBv]; omega
          have hxs_bd : ∀ x ∈ symListAt rsPool mOffBv.toNat, x / 2 < s.n_nets.toNat :=
            hRsSyms (off.toNat + i.toNat) hidx_rsn
          have hmOff_elem' : rsM[off.toNat + i.toNat]'(by omega) = mOffBv := by
            rw [← getD_eq_getElem rsM 0#32 (by omega)]
          c0_hsteps_nogrp
          simp only [bv64_zext32_p1, hidx_rs]
          rw [hmOff_elem']
          let RrsP := arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆
            array (t := i32) s.rule_n ruleN ⋆ array (t := i8) s.flipped flippedArr ⋆
            array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
            u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆
            rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ array (t := i32) s.ix ix ⋆
            array (t := i32) s.ix2 ix2 ⋆ R
          refine wp_load_arr32_add (base := s.rs_pool) (off64 := BitVec.setWidth 64 mOffBv)
            (idx := 0#32) (xs := rsPool) (R := RrsP) (by simp)
            (by simp only [bv64_zext32_p1]; simpa using hmOff_lt_pool)
            (sep_cast hm_rs (by dsimp only [RrsP]; ac_rfl)) ?_
          have hmlen_at : rsPool[(BitVec.setWidth 64 mOffBv).toNat + (0#32).toNat]'(by
              rw [bv64_zext32_p1]; simpa using hmOff_lt_pool) = mlenBv := by
            rw [← getD_eq_getElem rsPool 0#32, bv64_zext32_p1,
              show (0#32).toNat = 0 from rfl, Nat.add_zero]
          rw [hmlen_at]
          c0_hsteps_nogrp
          refine wp_loop_group (fun remF ⟨fF, jF, ⟨⟩⟩ mF =>
              mF = m ∧ 1 ≤ jF.toNat ∧ jF.toNat ≤ mlenBv.toNat + 1 ∧
              remF = mlenBv.toNat + 1 - jF.toNat ∧
              fF.toNat = flipCount flippedArr ((symListAt rsPool mOffBv.toNat).take (jF.toNat - 1)))
            ?_ ?_
          · rintro Jf remF ⟨fF, jF, ⟨⟩⟩ mF hrecF ⟨hmF, hjF1, hjFle, hremF, hfF⟩
            subst mF
            have hfF_le : fF.toNat ≤ jF.toNat - 1 := by
              rw [hfF]; exact Nat.le_trans (flipCount_le_length _ _) (by simp [Nat.min_le_left])
            c0_hsplit
            · have hjF_le_m : jF.toNat ≤ mlenBv.toNat := hc
              have hmF_lt : mOffBv.toNat + jF.toNat < rsPool.length := by omega
              have hxj_eq : (rsPool[mOffBv.toNat + jF.toNat]'hmF_lt).toNat =
                  (rsPool.getD (mOffBv.toNat + jF.toNat) 0#32).toNat :=
                congrArg BitVec.toNat (getD_eq_getElem rsPool 0#32 hmF_lt).symm
              have htake_j : (symListAt rsPool mOffBv.toNat).take jF.toNat =
                  (symListAt rsPool mOffBv.toNat).take (jF.toNat - 1) ++
                    [(rsPool[mOffBv.toNat + jF.toNat]'hmF_lt).toNat] := by
                rw [hxj_eq]; exact symListAt_take_succ hjF1 (by rw [← hmlen_eq]; exact hjF_le_m)
              have hxj_mem : (rsPool[mOffBv.toNat + jF.toNat]'hmF_lt).toNat ∈
                  symListAt rsPool mOffBv.toNat := by
                simp only [symListAt, ← hmlen_eq, List.mem_map, List.mem_range]
                refine ⟨jF.toNat - 1, by omega, ?_⟩
                rw [show mOffBv.toNat + 1 + (jF.toNat - 1) = mOffBv.toNat + jF.toNat by omega,
                  ← hxj_eq]
              have hxj_half : (rsPool[mOffBv.toNat + jF.toNat]'hmF_lt).toNat / 2 <
                  flippedArr.length := Nat.lt_of_lt_of_le (hxs_bd _ hxj_mem) hfl_len
              c0_hsteps_nogrp
              let xF := rsPool[(BitVec.setWidth 64 mOffBv).toNat +
                (BitVec.setWidth 64 jF).toNat]'(by simp only [bv64_zext32_p1]; exact hmF_lt)
              have hxF_eq : xF = rsPool[mOffBv.toNat + jF.toNat]'hmF_lt := by
                dsimp only [xF]; simp only [bv64_zext32_p1]
              have hxF_half : (xF >>> 1#32).toNat < flippedArr.length := by
                rw [bv32_shr1_toNat, hxF_eq]; exact hxj_half
              have hjF1_nat : (jF + 1#32).toNat = jF.toNat + 1 :=
                bv32_succ_toNat (by omega)
              refine wp_join_group (fun ⟨fF', ⟨⟩⟩ mF' =>
                  mF' = m ∧ fF'.toNat = flipCount flippedArr
                    ((symListAt rsPool mOffBv.toNat).take jF.toNat)) ?_ ?_
              · rintro Jfc ⟨fF', ⟨⟩⟩ mF' ⟨hmF', hfF'⟩; subst mF'
                c0_hsteps_nogrp
                exact hrecF (mlenBv.toNat + 1 - (jF + 1#32).toNat) (fF', jF + 1#32, ⟨⟩) m
                  (by omega) ⟨rfl, by omega, by omega, rfl, by
                    rw [hjF1_nat, Nat.add_sub_cancel]; exact hfF'⟩
              · intro Jfc hJfc
                c0_hsplit
                · have hx1_0 : xF &&& 1#32 = 0#32 := by simpa [hxF_eq] using hc
                  c0_hsteps_nogrp
                  · have hfl_cond : flipCond flippedArr xF.toNat = true := by
                      simp only [flipCond, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
                      refine ⟨(bv32_and1_eq_zero_iff xF).mp hx1_0, ?_⟩
                      rw [getD_eq_getElem flippedArr 0#8
                        (by rw [← bv32_shr1_toNat xF]; exact hxF_half)]
                      have hne0 : ¬ BitVec.setWidth 32
                          (flippedArr[xF.toNat / 2 ^ (1 % 2 ^ 32)]'(by
                            simp; rw [← bv32_shr1_toNat xF]; exact hxF_half)) =
                          BitVec.ofNat 32 0 := by assumption
                      intro hz; apply hne0; simp [hz]
                    have hfF_add1 : (fF + 1).toNat = fF.toNat + 1 :=
                      bv32_succ_toNat (by omega)
                    c0_hsteps_nogrp
                    refine hJfc _ _ ⟨rfl, ?_⟩
                    rw [hfF_add1, htake_j, flipCount_append, flipCount_cons, flipCount_nil,
                      ← hxF_eq, hfl_cond, hfF]; rfl
                  · have hfl_cond : flipCond flippedArr xF.toNat = false := by
                      simp only [flipCond, Bool.and_eq_false_iff, bne_eq_false_iff_eq]
                      right
                      rw [getD_eq_getElem flippedArr 0#8
                        (by rw [← bv32_shr1_toNat xF]; exact hxF_half)]
                      have heq0 : BitVec.setWidth 32
                          (flippedArr[xF.toNat / 2 ^ (1 % 2 ^ 32)]'(by
                            simp; rw [← bv32_shr1_toNat xF]; exact hxF_half)) =
                          BitVec.ofNat 32 0 := by assumption
                      apply BitVec.eq_of_toNat_eq
                      have ht := congrArg BitVec.toNat heq0
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
                        (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at ht
                      simpa using ht
                    c0_hsteps_nogrp
                    refine hJfc _ _ ⟨rfl, ?_⟩
                    rw [htake_j, flipCount_append, flipCount_cons, flipCount_nil, ← hxF_eq,
                      hfl_cond, hfF]; simp
                · have hfl_cond : flipCond flippedArr xF.toNat = false := by
                    simp only [flipCond, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
                    left; intro hmod
                    exact absurd (by simpa [hxF_eq] using ((bv32_and1_eq_zero_iff xF).mpr hmod)) hc
                  c0_hsteps_nogrp
                  refine hJfc _ _ ⟨rfl, ?_⟩
                  rw [htake_j, flipCount_append, flipCount_cons, flipCount_nil, ← hxF_eq,
                    hfl_cond, hfF]; simp
            · have hjF_eq : jF.toNat = mlenBv.toNat + 1 := by
                have := BitVec.not_le.mp hc; omega
              have htake_all : (symListAt rsPool mOffBv.toNat).take (jF.toNat - 1) =
                  symListAt rsPool mOffBv.toNat := by
                rw [hjF_eq, Nat.add_sub_cancel]
                apply List.take_of_length_le
                simp only [symListAt, ← hmlen_eq, List.length_map, List.length_range, le_refl]
              have hfF_eq : fF.toNat = flipCount flippedArr (symListAt rsPool mOffBv.toNat) := by
                rw [hfF, htake_all]
              c0_hsplit
              · exact hQ_false
              · have hfF_le24 : fF.toNat ≤ arRMaxF := Nat.le_of_not_lt hc
                have hf_tgt : flipCount flippedArr (symListAt rsPool mOffBv.toNat) ≤ arRMaxF := by
                  rw [← hfF_eq]; exact hfF_le24
                have hmax' : ∀ t < i.toNat + 1,
                    flipCount flippedArr
                      (symListAt rsPool (rsM.getD (off.toNat + t) 0#32).toNat) ≤ arRMaxF := by
                  intro t ht
                  by_cases hti : t = i.toNat
                  · subst hti; exact hf_tgt
                  · exact hmax_lt t (by omega)
                have hip1 : (i + 1#32).toNat = i.toNat + 1 := bv32_succ_toNat (by omega)
                obtain ⟨hbt_lt64, hbw_lt64, hshl_eq⟩ := buildR_pass1_bounds hoff_cnt hi_lt
                  hmOff_sl.1.2 (Nat.le_trans hRsWords hrs_ptop) hfF_le24 hmax_lt
                  hbt_eq hbw_eq hrs_ptop hrsp_32
                refine wp_join_group (fun ⟨any1, _⟩ mA =>
                    mA = m ∧ any1 = (any || (fF != 0#32))) ?_ ?_
                · rintro Ja ⟨any1, ⟨⟩⟩ mA ⟨hmA, hany1⟩; subst mA
                  c0_hsteps_nogrp
                  change wp Γ Q X (Expr.jump (Ji, ()).fst
                    (Arg.var any1,
                     Arg.var (bt + (1#64 : BitVec 64) <<< ((BitVec.setWidth 64 fF).toNat % 64)),
                     Arg.var (bw + ((1#64 : BitVec 64) <<< ((BitVec.setWidth 64 fF).toNat % 64)) *
                       (BitVec.setWidth 64 mlenBv + 1#64)),
                     Arg.var (i + 1#32), ())) m
                  rw [hshl_eq]
                  refine hrec (cnt.toNat - (i + 1#32).toNat)
                    (any1,
                     bt + (1#64 <<< BitVec.setWidth 64 fF),
                     bw + (1#64 <<< BitVec.setWidth 64 fF) * (BitVec.setWidth 64 mlenBv + 1#64),
                     i + 1#32, ⟨⟩) m (by omega)
                    ⟨rfl, by omega, rfl, ?_, by rw [hip1]; exact hmax', ?_, ?_⟩
                  · rw [hany1, hip1]
                    exact pass1_any_eq any flippedArr rsPool rsM off.toNat i.toNat fF
                      hany_eq hfF_eq
                  · rw [pass1_bv64_bt_step hfF_le24 hbt_lt64, hip1, ruleBt8_succ, hbt_eq, hfF_eq]
                    dsimp only [mOffBv]; omega
                  · rw [pass1_bv64_bw_step hfF_le24 hbw_lt64, hip1, ruleBw8_succ, hbw_eq, hfF_eq]
                    dsimp only [mlenBv, mOffBv]; omega
                · intro Ja hJa
                  c0_hsplit
                  · c0_hsteps_nogrp; refine hJa (true, ⟨⟩) m ⟨rfl, ?_⟩
                    have hne : (fF != 0#32) = true := bne_iff_ne.mpr hc
                    simp [hne]
                  · c0_hsteps_nogrp; refine hJa (any, ⟨⟩) m ⟨rfl, ?_⟩
                    have h0 : fF = 0#32 := hc
                    simp [h0]
          · intro Jf hJf; c0_hsteps_nogrp
            exact hJf mlenBv.toNat (0#32, 1#32, ⟨⟩) m
              ⟨rfl, by decide, Nat.le_add_left 1 _, rfl, by simp [flipCount]⟩
        · have hi_eq : i.toNat = cnt.toNat := by
            have := BitVec.not_lt.mp hc; omega
          clear hc
          have hi_bv : i = cnt := BitVec.eq_of_toNat_eq hi_eq
          subst hi_bv
          refine wp_join_group (fun (_ : Tup Val []) mJ => mJ = m) ?_ ?_
          · rintro Jfull ⟨⟩ mJ hmJ; cases hmJ
            change wp Γ Q X (buildRPass2EntryExpr cx v off cnt fv_b any bt bw) m
            exact buildR_pass1_full_handoff Γ hMcmp hCneg hCadd rfl rfl rfl hv_lt hne hnn_bd
              hfl_len hqcap_lo hqcap_hi hrcap_le hrpcap_32 hrsp_32 hrm_len hrl_len hrh_len hrm2_len
              hrl2_len hrh2_len hrpool_len hix_eq hix_len hMasks hoff_cnt hrs_n_le hrs_cap_le
              hrsL_len hrsH_len hrsPool_len hrs_ptop hRsSl hRsSorted hRsSyms hmax_lt hbt_eq hbw_eq
              hRules hm hQ_false hQ_full
          · intro Jfull hJfull
            by_cases hany_b : any
            · subst hany_b; dsimp only; exact head_wp_jnz (vc := true) rfl
                (fun _ => hJfull ⟨⟩ m rfl) (fun h => by cases h)
            · have hany_f : any = false := Bool.eq_false_iff.mpr hany_b
              subst hany_f; dsimp only
              refine head_wp_jnz (vc := false) rfl (fun h => by cases h) (fun _ => ?_)
              by_cases hfv_c : fv_b
              · have hfv_t : fv_b = true := by simp [hfv_c]
                simp only [hfv_t]
                refine head_wp_jnz (vc := true) rfl (fun _ => ?_) (fun h => by cases h)
                have hfv_true : fv_b = true := hfv_t
                exact hJfull ⟨⟩ m rfl
              · have hfv_f : fv_b = false := Bool.eq_false_iff.mpr hfv_c
                have hfv_zero : flippedArr.getD v.toNat 0#8 = 0#8 := by
                  dsimp only [fv_b, fv] at hfv_f; simpa using hfv_f
                refine head_wp_jnz (vc := false) (by simp [hfv_c]) (fun h => by cases h)
                  (fun _ => ?_)
                c0_hsteps_nogrp
                have h4off : BitVec.setWidth 64 off * 4 = BitVec.ofNat 64 (4 * off.toNat) := by
                  apply BitVec.eq_of_toNat_eq; simp [Nat.mul_comm]
                have h8off : BitVec.setWidth 64 off * 8 = BitVec.ofNat 64 (8 * off.toNat) := by
                  apply BitVec.eq_of_toNat_eq; simp [Nat.mul_comm]
                refine hQ_fast { s with
                    cur_rm := s.rs_m + BitVec.ofNat 64 (4 * off.toNat),
                    cur_rl := s.rs_l + BitVec.ofNat 64 (8 * off.toNat),
                    cur_rh := s.rs_h + BitVec.ofNat 64 (8 * off.toNat),
                    cur_rp := s.rs_pool, cur_nr := cnt } _ rfl hfv_zero ?_
                refine fast_pack_mem (s0 := s) hm ?_ (by rw [rsMem_unfold]; ac_rfl)
                simp only [h4off, h8off]
      · intro Ji hJi; c0_hsteps_nogrp
        exact hJi cnt.toNat (false, bt0, bw0, 0#32, ⟨⟩) m
          ⟨rfl, Nat.zero_le _, rfl, by simp, fun _ ht => by simp at ht,
            by simp [hbt0, ruleBt8], by simp [hbw0, ruleBw8]⟩
    · intro Jbt hJbt
      by_cases hfv : fv_b
      · have hfv_t : fv_b = true := by simp [hfv]
        refine head_wp_jnz (vc := true) hfv_t (fun _ => ?_) (fun h => by cases h)
        c0_hsteps_nogrp; exact hJbt (1#64, ⟨⟩) m ⟨rfl, by simp [hfv_t]⟩
      · have hfv_f : fv_b = false := Bool.eq_false_iff.mpr hfv
        refine head_wp_jnz (vc := false) hfv_f (fun h => by cases h) (fun _ => ?_)
        c0_hsteps_nogrp; exact hJbt (0#64, ⟨⟩) m ⟨rfl, by simp [hfv_f]⟩
  · intro Jbw hJbw
    by_cases hfv : fv_b
    · have hfv_t : fv_b = true := by simp [hfv]
      refine head_wp_jnz (vc := true) hfv_t (fun _ => ?_) (fun h => by cases h)
      c0_hsteps_nogrp; exact hJbw (1#64, ⟨⟩) m ⟨rfl, by simp [hfv_t]⟩
    · have hfv_f : fv_b = false := Bool.eq_false_iff.mpr hfv
      refine head_wp_jnz (vc := false) hfv_f (fun h => by cases h) (fun _ => ?_)
      c0_hsteps_nogrp; exact hJbw (0#64, ⟨⟩) m ⟨rfl, by simp [hfv_f]⟩

/-- Public `arBuildRSpec` WP wrapper for `ar_build_R(cx, v)`. -/
public theorem ar_build_R_wp (Γ : T.Env)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    (hCneg : ∀ xs m Q X, arCnegSpec xs m Q X → Γ "ar_cneg" [i64, i64, i64] [i64, i64] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X) :
    ∀ xs m Q X, arBuildRSpec xs m Q X → Func.wp Γ ar_build_R_body xs m Q X := by
  rintro ⟨cx, v, ⟨⟩⟩ m Q X
    ⟨s, ruleOff, ruleN, rsM, rsL, rsH, rsPool, flippedArr, rm, rl, rh, rm2, rl2, rh2, rpool,
      ix, ix2, Valid, R, hv_lt, hne, hnn_bd, hfl_len, hqcap_lo, hqcap_hi, hrcap_le, hrpcap_32,
      hrscap_bd, hrsp_32, hrm_len, hrl_len, hrh_len, hrm2_len, hrl2_len, hrh2_len, hrpool_len,
      hix_len, hix2_len, hix_eq, hMasks, hValid, hRules, hRsSorted, hRsSl32, hRsWords,
      hRsSyms, hm, hQ⟩
  have ⟨σ₀, hσ₀⟩ := hValid
  have hr₀ := (hRules σ₀ hσ₀).2
  refine buildR_pass1_wp Γ hMcmp hCneg hCadd hv_lt hne hnn_bd hr₀.1 hr₀.2.1 hfl_len
    hqcap_lo hqcap_hi hrcap_le hrpcap_32 hrsp_32 hrm_len hrl_len hrh_len
    hrm2_len hrl2_len hrh2_len hrpool_len hix_eq hix_len hMasks
    hr₀.2.2.1 hrscap_bd hr₀.2.2.2.2.1 hr₀.2.2.2.2.2.1 hr₀.2.2.2.2.2.2.1
    hr₀.2.2.2.2.2.2.2.1 hr₀.2.2.2.1
    (fun i hi => ⟨hr₀.2.2.2.2.2.2.2.2.1 i hi, hRsSl32 i hi⟩)
    hRsSorted hRsWords hRsSyms hValid hRules hm
    (hQ false s rm rl rh rm2 rl2 rh2 rpool ix ix2 m
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun h => by cases h) hm)
    (fun s' m' hs' hfv0 hm' => hQ true s' rm rl rh rm2 rl2 rh2 rpool ix ix2 m'
      (by rw [hs']) rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun _ => Or.inl ⟨hfv0, by rw [hs'], by rw [hs'], by rw [hs'], by rw [hs'], by rw [hs']⟩)
      hm')
    (fun k2 s' rm' rl' rh' rm2' rl2' rh2' rpool' ix' ix2' m' hs' hk2
      hrm' hrl' hrh' hrm2' hrl2' hrh2' hrpool' hix' hix2' hCur hSl' hSorted' hW' _ hm' =>
      have hrmp : s'.cur_rp = s.rpool := by rw [hs']
      have hnr : s'.cur_nr = k2 := by rw [hs']
      hQ true s' rm' rl' rh' rm2' rl2' rh2' rpool' ix' ix2' m'
        (by rw [hs']) hrm' hrl' hrh' hrm2' hrl2' hrh2' hrpool' hix' hix2'
        (fun _ => Or.inr ⟨by rw [hs'], by rw [hs'], by rw [hs'], hrmp, by rw [hnr]; exact hk2,
          by rw [hnr]; exact hCur, by rw [hnr]; exact hSorted',
          (fun r hr => (hSl' r (by rw [← hnr]; exact hr)).2),
          by rw [hnr]; exact hW'⟩)
        hm')

end

end LeanQbe.T.Examples.Arisca.Proof
