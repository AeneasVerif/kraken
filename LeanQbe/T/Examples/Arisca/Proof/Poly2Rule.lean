/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2Base
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Rule Store WP (`Arisca.Proof.Poly2Rule`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP proof for `ar_store_rule_wp` of
`LeanQbe.T.Examples.Arisca.Src.Poly`.
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

private theorem storeRule_step_inv {srcPool srcTm rsPool0 rsPool rsM0 rsM : List (BitVec 32)}
    {srcTl srcTh rsL0 rsL rsH0 rsH : List (BitVec 64)}
    {rsN0 rsPt0 i rsN pt mOff mlen : Nat}
    (hrsN : rsN = rsN0 + i) (hpt_le0 : rsPt0 ≤ pt)
    (hPrefIdx : ∀ k < rsN0,
      rsM.getD k 0#32 = rsM0.getD k 0#32 ∧
      rsL.getD k 0#64 = rsL0.getD k 0#64 ∧
      rsH.getD k 0#64 = rsH0.getD k 0#64)
    (hPrefPool : ∀ idx < rsPt0, rsPool.getD idx 0#32 = rsPool0.getD idx 0#32)
    (hSlices : ∀ k < rsN, MonoSliceOk rsPool (rsM.getD k 0#32).toNat pt ∧
      (rsPool.getD (rsM.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hWords : monoTotalWords rsPool rsM rsN ≤ pt)
    (hCorr : ∀ t < i,
      symListAt rsPool (rsM.getD (rsN0 + t) 0#32).toNat =
        symListAt srcPool (srcTm.getD t 0#32).toNat ∧
      rsL.getD (rsN0 + t) 0#64 = srcTl.getD t 0#64 ∧
      rsH.getD (rsN0 + t) 0#64 = srcTh.getD t 0#64)
    (hrsN_len : rsN < rsM.length) (hrsL_len : rsN < rsL.length) (hrsH_len : rsN < rsH.length)
    (hm_eq : (srcTm.getD i 0#32).toNat = mOff)
    (hm_len : (srcPool.getD mOff 0#32).toNat = mlen)
    (hmlen32 : mlen + 1 < 2 ^ 32) (hpt32 : pt < 2 ^ 32)
    {rsPool' : List (BitVec 32)}
    (hOld : ∀ q < pt, rsPool'.getD q 0#32 = rsPool.getD q 0#32)
    (hCopied : ∀ r ≤ mlen, rsPool'.getD (pt + r) 0#32 = srcPool.getD (mOff + r) 0#32)
    {lNew hNew : BitVec 64}
    (hlNew : lNew = srcTl.getD i 0#64) (hhNew : hNew = srcTh.getD i 0#64) :
    let rsM' := rsM.set rsN (BitVec.ofNat 32 pt)
    let rsL' := rsL.set rsN lNew
    let rsH' := rsH.set rsN hNew
    let pt' := pt + mlen + 1
    (∀ k < rsN0,
      rsM'.getD k 0#32 = rsM0.getD k 0#32 ∧
      rsL'.getD k 0#64 = rsL0.getD k 0#64 ∧
      rsH'.getD k 0#64 = rsH0.getD k 0#64) ∧
    (∀ idx < rsPt0, rsPool'.getD idx 0#32 = rsPool0.getD idx 0#32) ∧
    (∀ k < rsN + 1, MonoSliceOk rsPool' (rsM'.getD k 0#32).toNat pt' ∧
      (rsPool'.getD (rsM'.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
    monoTotalWords rsPool' rsM' (rsN + 1) ≤ pt' ∧
    (∀ t < i + 1,
      symListAt rsPool' (rsM'.getD (rsN0 + t) 0#32).toNat =
        symListAt srcPool (srcTm.getD t 0#32).toNat ∧
      rsL'.getD (rsN0 + t) 0#64 = srcTl.getD t 0#64 ∧
      rsH'.getD (rsN0 + t) 0#64 = srcTh.getD t 0#64) := by
  intro rsM' rsL' rsH' pt'
  have hpt_toNat : (BitVec.ofNat 32 pt).toNat = pt := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpt32]
  have hpt0 : rsPool'.getD pt 0#32 = srcPool.getD mOff 0#32 := by
    have := hCopied 0 (Nat.zero_le mlen); simpa only [Nat.add_zero] using this
  have hpt0_nat : (rsPool'.getD pt 0#32).toNat = mlen := by rw [hpt0, hm_len]
  have hWords_eq : monoTotalWords rsPool' rsM rsN = monoTotalWords rsPool rsM rsN :=
    monoTotalWords_congr_prefix (fun k hk => (hSlices k hk).1) hOld (fun _ _ => rfl)
  refine ⟨fun k hk => ?_, fun idx hidx => ?_, fun k hk => ?_, ?_, fun t ht => ?_⟩
  · have hkn : k ≠ rsN := by omega
    obtain ⟨h1, h2, h3⟩ := hPrefIdx k hk
    exact ⟨by dsimp only [rsM']; rw [getD_set_eq rsM 0#32 _ hrsN_len, ite_eq_right hkn, h1],
      by dsimp only [rsL']; rw [getD_set_eq rsL 0#64 _ hrsL_len, ite_eq_right hkn, h2],
      by dsimp only [rsH']; rw [getD_set_eq rsH 0#64 _ hrsH_len, ite_eq_right hkn, h3]⟩
  · rw [hOld idx (by omega), hPrefPool idx hidx]
  · by_cases hkn : k = rsN
    · subst hkn
      have hrm_k : (rsM'.getD k 0#32).toNat = pt := by
        dsimp only [rsM']; rw [getD_set_eq rsM 0#32 _ hrsN_len, ite_eq_left rfl, hpt_toNat]
      rw [hrm_k]
      exact ⟨⟨by omega, by rw [hpt0_nat]; dsimp only [pt']; omega⟩, by rw [hpt0_nat]; exact hmlen32⟩
    · have hk_lt : k < rsN := by omega
      obtain ⟨hsl, h32⟩ := hSlices k hk_lt
      have hrm_k : rsM'.getD k 0#32 = rsM.getD k 0#32 := by
        dsimp only [rsM']; rw [getD_set_eq rsM 0#32 _ hrsN_len, ite_eq_right hkn]
      rw [hrm_k]
      have hlen_keep : rsPool'.getD (rsM.getD k 0#32).toNat 0#32 =
          rsPool.getD (rsM.getD k 0#32).toNat 0#32 := hOld _ hsl.1
      have hsl1 := hsl.1
      have hsl2 := hsl.2
      dsimp only [pt']
      exact ⟨⟨by omega, by rw [hlen_keep]; omega⟩, by rw [hlen_keep]; exact h32⟩
  · rw [monoTotalWords_succ]
    have hpref : monoTotalWords rsPool' rsM' rsN = monoTotalWords rsPool' rsM rsN :=
      monoTotalWords_congr_prefix (fun k hk => ⟨(hSlices k hk).1.1,
        by rw [hOld _ (hSlices k hk).1.1]; exact (hSlices k hk).1.2⟩) (fun _ _ => rfl)
        (fun k hk => by
          dsimp only [rsM']; rw [getD_set_eq rsM 0#32 _ hrsN_len, ite_eq_right (by omega)])
    rw [hpref, hWords_eq]
    dsimp only [rsM']
    rw [getD_set_eq rsM 0#32 _ hrsN_len, ite_eq_left rfl, hpt_toNat, hpt0_nat]
    dsimp only [pt']; omega
  · by_cases hti : t = i
    · subst hti
      have hidx_eq : rsN0 + t = rsN := hrsN.symm
      rw [hidx_eq]
      have hrm_eq : (rsM'.getD rsN 0#32).toNat = pt := by
        dsimp only [rsM']; rw [getD_set_eq rsM 0#32 _ hrsN_len, ite_eq_left rfl, hpt_toNat]
      refine ⟨?_, ?_, ?_⟩
      · rw [hrm_eq, hm_eq]
        exact symListAt_congr_slice (by rw [hpt0_nat, hm_len]) (fun r hr => by
          rw [hm_len] at hr; exact hCopied r hr)
      · dsimp only [rsL']; rw [getD_set_eq rsL 0#64 _ hrsL_len, ite_eq_left rfl, hlNew]
      · dsimp only [rsH']; rw [getD_set_eq rsH 0#64 _ hrsH_len, ite_eq_left rfl, hhNew]
    · have ht_lt : t < i := by omega
      have hne : rsN0 + t ≠ rsN := by omega
      obtain ⟨hsy, htl, hth⟩ := hCorr t ht_lt
      have hrm_eq : rsM'.getD (rsN0 + t) 0#32 = rsM.getD (rsN0 + t) 0#32 := by
        dsimp only [rsM']; rw [getD_set_eq rsM 0#32 _ hrsN_len, ite_eq_right hne]
      have hsl := (hSlices (rsN0 + t) (by omega)).1
      have hlen_keep : rsPool'.getD (rsM.getD (rsN0 + t) 0#32).toNat 0#32 =
          rsPool.getD (rsM.getD (rsN0 + t) 0#32).toNat 0#32 := hOld _ hsl.1
      refine ⟨?_, ?_, ?_⟩
      · rw [hrm_eq, ← hsy]
        exact symListAt_congr_slice (by rw [hlen_keep])
          (fun r hr => hOld _ (by have := hsl.2; omega))
      · dsimp only [rsL']; rw [getD_set_eq rsL 0#64 _ hrsL_len, ite_eq_right hne, htl]
      · dsimp only [rsH']; rw [getD_set_eq rsH 0#64 _ hrsH_len, ite_eq_right hne, hth]

private theorem storeRule_done_rulesRep {s : ArCtxState} {v : BitVec 32}
    {ruleOff ruleN rsM rsM' rsPool rsPool' srcPool srcTm : List (BitVec 32)}
    {rsL rsL' rsH rsH' srcTl srcTh : List (BitVec 64)}
    {pt : Nat} {Valid : (Nat → Bool) → Prop}
    (hv_lt : v.toNat < s.n_nets.toNat)
    (htcap30 : s.tcap.toNat < 2 ^ 30) (htn_le : s.tn.toNat ≤ s.tcap.toNat)
    (hrspcap32 : s.rs_pcap.toNat < 2 ^ 32)
    (hrsN_cap : s.rs_n.toNat + s.tn.toNat ≤ s.rs_cap.toNat) (hpt_cap : pt ≤ s.rs_pcap.toNat)
    (_hro_len : ruleOff.length = ruleOff.length) (_hrn_len : ruleN.length = ruleN.length)
    (hrsm_len : rsM'.length = rsM.length) (hrsl_len : rsL'.length = rsL.length)
    (hrsh_len : rsH'.length = rsH.length) (hrsp_len : rsPool'.length = rsPool.length)
    (hRules : ∀ σ, Valid σ → RulesRep s.modW σ s ruleOff ruleN rsM rsL rsH rsPool)
    (htEval : ∀ σ, Valid σ →
      polyEval s.modW σ srcPool srcTm srcTl srcTh s.tn.toNat =
        bv s.modW (σ (2 * v.toNat)))
    (hPrefIdx : ∀ k < s.rs_n.toNat,
      rsM'.getD k 0#32 = rsM.getD k 0#32 ∧ rsL'.getD k 0#64 = rsL.getD k 0#64 ∧
      rsH'.getD k 0#64 = rsH.getD k 0#64)
    (hPrefPool : ∀ idx < s.rs_ptop.toNat, rsPool'.getD idx 0#32 = rsPool.getD idx 0#32)
    (hSlices : ∀ k < s.rs_n.toNat + s.tn.toNat,
      MonoSliceOk rsPool' (rsM'.getD k 0#32).toNat pt)
    (hCorr : ∀ t < s.tn.toNat,
      symListAt rsPool' (rsM'.getD (s.rs_n.toNat + t) 0#32).toNat =
        symListAt srcPool (srcTm.getD t 0#32).toNat ∧
      rsL'.getD (s.rs_n.toNat + t) 0#64 = srcTl.getD t 0#64 ∧
      rsH'.getD (s.rs_n.toNat + t) 0#64 = srcTh.getD t 0#64) :
    let s' : ArCtxState :=
      { s with rs_n := BitVec.ofNat 32 (s.rs_n.toNat + s.tn.toNat), rs_ptop := BitVec.ofNat 64 pt }
    ∀ σ, Valid σ → RulesRep s'.modW σ s' (ruleOff.set v.toNat s.rs_n)
      (ruleN.set v.toNat s.tn) rsM' rsL' rsH' rsPool' := by
  intro s' σ hV
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hRules σ hV
  have hrs_pt32 : pt < 2 ^ 32 := Nat.lt_of_le_of_lt hpt_cap hrspcap32
  have hrsN_32 : s.rs_n.toNat + s.tn.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt hrsN_cap s.rs_cap.isLt
  have hs'n : s'.rs_n.toNat = s.rs_n.toNat + s.tn.toNat := by
    dsimp only [s']; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrsN_32]
  have hs'pt : s'.rs_ptop.toNat = pt := by
    dsimp only [s']; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs'mod : s'.modW = s.modW := by simp only [ArCtxState.modW, s']
  refine ⟨by dsimp only [s']; simp; omega, by dsimp only [s']; simp; omega,
    by rw [hs'n]; dsimp only [s']; exact hrsN_cap,
    by rw [hs'pt]; dsimp only [s']; exact hpt_cap,
    by dsimp only [s']; omega, by dsimp only [s']; omega,
    by dsimp only [s']; omega, by dsimp only [s']; omega,
    by rw [hs'n, hs'pt]; exact hSlices,
    fun w hw hwn => ?_⟩
  have hw0 : w < s.n_nets.toNat := by dsimp only [s'] at hw; exact hw
  rw [hs'n]; dsimp only [s']
  by_cases hwv : w = v.toNat
  · subst hwv
    rw [getD_set_eq ruleOff 0#32 s.rs_n (by omega), getD_set_eq ruleN 0#32 s.tn (by omega),
      ite_eq_left rfl, ite_eq_left rfl]
    refine ⟨le_refl _, ?_⟩
    rw [hs'mod, ← htEval σ hV]
    exact polyEval_eq_polyEvalRange_of_prefix s.modW σ
      (pool1 := srcPool) (tm1 := srcTm) (pool2 := rsPool') (mOff2 := rsM')
      (tl1 := srcTl) (th1 := srcTh) (cl2 := rsL') (ch2 := rsH')
      (off := s.rs_n.toNat) (n := s.tn.toNat)
      (fun t ht => ⟨(hCorr t ht).1.symm, (hCorr t ht).2.1.symm, (hCorr t ht).2.2.symm⟩)
  · rw [getD_set_eq ruleN 0#32 s.tn (by omega), ite_eq_right hwv] at hwn
    rw [getD_set_eq ruleOff 0#32 s.rs_n (by omega), getD_set_eq ruleN 0#32 s.tn (by omega),
      ite_eq_right hwv, ite_eq_right hwv]
    obtain ⟨hoff_old, hev_old⟩ := h10 w hw0 hwn
    refine ⟨by omega, ?_⟩
    rw [hs'mod, hev_old]
    have h10' : ∀ t < (ruleN.getD w 0#32).toNat,
        MonoSliceOk rsPool' (rsM'.getD ((ruleOff.getD w 0#32).toNat + t) 0#32).toNat
          s.rs_ptop.toNat := by
      intro t ht
      have hoff_old' : (ruleOff.getD w 0#32).toNat + (ruleN.getD w 0#32).toNat ≤ s.rs_n.toNat :=
        hoff_old
      have hlt : (ruleOff.getD w 0#32).toNat + t < s.rs_n.toNat := by omega
      have hms := h9 _ hlt
      rw [(hPrefIdx _ hlt).1]
      exact ⟨hms.1, by rw [hPrefPool _ hms.1]; exact hms.2⟩
    exact polyEvalRange_congr_prefix s.modW σ
      (pool1 := rsPool') (pool2 := rsPool) (mOff1 := rsM') (mOff2 := rsM)
      (cl1 := rsL') (ch1 := rsH') (cl2 := rsL) (ch2 := rsH)
      (bd := s.rs_ptop.toNat) (lo := (ruleOff.getD w 0#32).toNat)
      (len := (ruleN.getD w 0#32).toNat) h10' (fun idx hidx => (hPrefPool idx hidx).symm)
      (fun t ht =>
        have hoff_old' : (ruleOff.getD w 0#32).toNat + (ruleN.getD w 0#32).toNat ≤ s.rs_n.toNat :=
          hoff_old
        have hlt : (ruleOff.getD w 0#32).toNat + t < s.rs_n.toNat := by omega
        have hk := hPrefIdx _ hlt; ⟨hk.1.symm, hk.2.1.symm, hk.2.2.symm⟩)

private theorem storeRule_pack_mem {cx : BitVec 64} {s s' : ArCtxState}
    {tm0 tm1 pool0 pool1 srcTm srcPool ruleOff' ruleN'
      rsM rsPool rsMC rsPoolC : List (BitVec 32)}
    {ts0 tl0 th0 ts1 tl1 th1 srcTl srcTh rsLC rsHC : List (BitVec 64)}
    {restT R : Mem 64 → Prop} {m : Mem 64}
    (htms : s'.tm = s.tm) (htss : s'.ts = s.ts) (htls : s'.tl = s.tl)
    (hths : s'.th = s.th) (hpools : s'.pool = s.pool)
    (hro : s'.rule_off = s.rule_off) (hrn : s'.rule_n = s.rule_n)
    (hrsm_ptr : s'.rs_m = s.rs_m) (hrsl_ptr : s'.rs_l = s.rs_l)
    (hrsh_ptr : s'.rs_h = s.rs_h) (hrsp_ptr : s'.rs_pool = s.rs_pool)
    (hsrc_p : srcPool = if s.pc.toNat = 0 then pool0 else pool1)
    (hsrc_m : srcTm = if s.tc.toNat = 0 then tm0 else tm1)
    (hsrc_l : srcTl = if s.tc.toNat = 0 then tl0 else tl1)
    (hsrc_h : srcTh = if s.tc.toNat = 0 then th0 else th1)
    (hrsmC_len : rsMC.length = rsM.length) (hrspC_len : rsPoolC.length = rsPool.length)
    (htBack : ∀ (s1 : ArCtxState) (tm' : List (BitVec 32)) (ts' tl' th' : List (BitVec 64))
        (pool' : List (BitVec 32)),
      s1.tm = s.tm → s1.ts = s.ts → s1.tl = s.tl → s1.th = s.th → s1.pool = s.pool →
      tm'.length = srcTm.length → ts'.length = (if s.tc.toNat = 0 then ts0 else ts1).length →
      tl'.length = srcTl.length → th'.length = srcTh.length → pool'.length = srcPool.length →
      tMem s1 (if s.tc.toNat = 0 then tm' else tm0) (if s.tc.toNat = 0 then tm1 else tm')
          (if s.tc.toNat = 0 then ts' else ts0) (if s.tc.toNat = 0 then tl' else tl0)
          (if s.tc.toNat = 0 then th' else th0) (if s.tc.toNat = 0 then ts1 else ts')
          (if s.tc.toNat = 0 then tl1 else tl') (if s.tc.toNat = 0 then th1 else th')
          (if s.pc.toNat = 0 then pool' else pool0)
          (if s.pc.toNat = 0 then pool1 else pool') =
        (array (t := i32) (s.pool.getD s.pc.toNat 0#64) pool' ⋆
         array (t := i32) (s.tm.getD s.tc.toNat 0#64) tm' ⋆
         array64 (s.ts.getD s.tc.toNat 0#64) ts' ⋆
         array64 (s.tl.getD s.tc.toNat 0#64) tl' ⋆
         array64 (s.th.getD s.tc.toNat 0#64) th' ⋆ restT))
    (hmF : (arCtxMem cx s' ⋆ array (t := i32) s.rs_m rsMC ⋆ array64 s.rs_l rsLC ⋆
      array64 s.rs_h rsHC ⋆ array (t := i32) s.rs_pool rsPoolC ⋆
      (array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
        array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
        array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
        array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
        array (t := i32) s.rule_off ruleOff' ⋆ array (t := i32) s.rule_n ruleN' ⋆
        array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
        u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R)) m) :
    (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff' ⋆
      array (t := i32) s'.rule_n ruleN' ⋆ rsMem s' rsMC rsLC rsHC rsPoolC ⋆
      tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ R) m := by
  have htC := htBack s' srcTm (if s.tc.toNat = 0 then ts0 else ts1) srcTl srcTh srcPool
    htms htss htls hths hpools rfl rfl rfl rfl rfl
  have ht_eq : (if s.tc.toNat = 0 then srcTm else tm0) = tm0 ∧
      (if s.tc.toNat = 0 then tm1 else srcTm) = tm1 ∧
      (if s.tc.toNat = 0 then (if s.tc.toNat = 0 then ts0 else ts1) else ts0) = ts0 ∧
      (if s.tc.toNat = 0 then srcTl else tl0) = tl0 ∧
      (if s.tc.toNat = 0 then srcTh else th0) = th0 ∧
      (if s.tc.toNat = 0 then ts1 else (if s.tc.toNat = 0 then ts0 else ts1)) = ts1 ∧
      (if s.tc.toNat = 0 then tl1 else srcTl) = tl1 ∧
      (if s.tc.toNat = 0 then th1 else srcTh) = th1 ∧
      (if s.pc.toNat = 0 then srcPool else pool0) = pool0 ∧
      (if s.pc.toNat = 0 then pool1 else srcPool) = pool1 := by
    rw [hsrc_m, hsrc_l, hsrc_h, hsrc_p]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> split <;> rfl
  rw [ht_eq.1, ht_eq.2.1, ht_eq.2.2.1, ht_eq.2.2.2.1, ht_eq.2.2.2.2.1,
    ht_eq.2.2.2.2.2.1, ht_eq.2.2.2.2.2.2.1, ht_eq.2.2.2.2.2.2.2.1,
    ht_eq.2.2.2.2.2.2.2.2.1, ht_eq.2.2.2.2.2.2.2.2.2] at htC
  rw [htC, rsMem_unfold, hro, hrn, hrsm_ptr, hrsl_ptr, hrsh_ptr, hrsp_ptr, hrsmC_len, hrspC_len]
  exact sep_cast hmF (by ac_rfl)

theorem ar_store_rule_wp (Γ : T.Env) :
    ∀ xs m Q X, arStoreRuleSpec xs m Q X → Func.wp Γ ar_store_rule_body xs m Q X := by
  rintro ⟨cx, v, ⟨⟩⟩ m Q X
    ⟨s, ruleOff, ruleN, rsM, rsL, rsH, rsPool, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1,
      pool0, pool1, Valid, R, hpc, htc, hv_lt, htn_le, htcap30, hpcap32, hrscap30, hrspcap32,
      htm0_len, htm1_len, htl0_len, hth0_len, htl1_len, hth1_len, hp0_len, hp1_len,
      hNonEmpty, hRules, hrsSorted, hrsWords, hrsOk32, htSlices, htSorted, htWords, htEval, hm, hQ⟩
  obtain ⟨σ₀, hV₀⟩ := hNonEmpty
  obtain ⟨hroff_len, hrn_len, hrsn_le, hrspt_le, hrsm_len, hrsl_len, hrsh_len, hrsp_len,
    hrsSlices, _⟩ := hRules σ₀ hV₀
  let srcPool := if s.pc.toNat = 0 then pool0 else pool1
  let srcTm := if s.tc.toNat = 0 then tm0 else tm1
  let srcTl := if s.tc.toNat = 0 then tl0 else tl1
  let srcTh := if s.tc.toNat = 0 then th0 else th1
  have hpool_len : s.pcap.toNat ≤ srcPool.length := by dsimp only [srcPool]; split <;> assumption
  have htm_len : s.tcap.toNat ≤ srcTm.length := by dsimp only [srcTm]; split <;> assumption
  have htl_len : s.tcap.toNat ≤ srcTl.length := by dsimp only [srcTl]; split <;> assumption
  have hth_len : s.tcap.toNat ≤ srcTh.length := by dsimp only [srcTh]; split <;> assumption
  obtain ⟨restT, htEq, htBack⟩ :=
    tMem_focus_cur s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 hpc htc
  have hm_u : (arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
      array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
      array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
      array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
      array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
      array (t := i32) s.rs_pool rsPool ⋆
      (array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
        u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R)) m := by
    have hm0 := hm; rw [rsMem_unfold, htEq] at hm0; exact sep_cast hm0 (by ac_rfl)
  have hl_s : ArCtxLengthsOk s :=
    arCtx_lengths (R := array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      rsMem s rsM rsL rsH rsPool ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ R)
      (sep_cast hm (by ac_rfl))
  have hpool_pc : s.pool[s.pc.toNat]'(by rw [hl_s.pool]; exact hpc) =
      s.pool.getD s.pc.toNat 0#64 :=
    (getD_eq_getElem s.pool 0#64 (by rw [hl_s.pool]; exact hpc)).symm
  have htm_tc : s.tm[s.tc.toNat]'(by rw [hl_s.tm]; exact htc) =
      s.tm.getD s.tc.toNat 0#64 :=
    (getD_eq_getElem s.tm 0#64 (by rw [hl_s.tm]; exact htc)).symm
  have htl_tc : s.tl[s.tc.toNat]'(by rw [hl_s.tl]; exact htc) =
      s.tl.getD s.tc.toNat 0#64 :=
    (getD_eq_getElem s.tl 0#64 (by rw [hl_s.tl]; exact htc)).symm
  have hth_tc : s.th[s.tc.toNat]'(by rw [hl_s.th]; exact htc) =
      s.th.getD s.tc.toNat 0#64 :=
    (getD_eq_getElem s.th 0#64 (by rw [hl_s.th]; exact htc)).symm
  let Rloop := array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
    array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
    array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
    array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
    array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
    array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
    u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
  c0_hsteps_nogrp
  refine wp_loop_group (fun rem ⟨iV, ⟨⟩⟩ mL =>
      iV.toNat ≤ s.tn.toNat ∧ rem = s.tn.toNat - iV.toNat ∧
      ∃ (rsN pt : Nat) (rsMC rsPoolC : List (BitVec 32)) (rsLC rsHC : List (BitVec 64)),
        rsN = s.rs_n.toNat + iV.toNat ∧ rsN ≤ s.rs_cap.toNat ∧
        s.rs_ptop.toNat ≤ pt ∧ pt ≤ s.rs_pcap.toNat ∧
        rsMC.length = rsM.length ∧ rsLC.length = rsL.length ∧
        rsHC.length = rsH.length ∧ rsPoolC.length = rsPool.length ∧
        (∀ k < s.rs_n.toNat, rsMC.getD k 0#32 = rsM.getD k 0#32 ∧
          rsLC.getD k 0#64 = rsL.getD k 0#64 ∧ rsHC.getD k 0#64 = rsH.getD k 0#64) ∧
        (∀ idx < s.rs_ptop.toNat, rsPoolC.getD idx 0#32 = rsPool.getD idx 0#32) ∧
        (∀ k < rsN, MonoSliceOk rsPoolC (rsMC.getD k 0#32).toNat pt ∧
          (rsPoolC.getD (rsMC.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        monoTotalWords rsPoolC rsMC rsN ≤ pt ∧
        (∀ t < iV.toNat,
          symListAt rsPoolC (rsMC.getD (s.rs_n.toNat + t) 0#32).toNat =
            symListAt srcPool (srcTm.getD t 0#32).toNat ∧
          rsLC.getD (s.rs_n.toNat + t) 0#64 = srcTl.getD t 0#64 ∧
          rsHC.getD (s.rs_n.toNat + t) 0#64 = srcTh.getD t 0#64) ∧
        (arCtxMem cx { s with rs_n := BitVec.ofNat 32 rsN, rs_ptop := BitVec.ofNat 64 pt } ⋆
          array (t := i32) s.rs_m rsMC ⋆ array64 s.rs_l rsLC ⋆
          array64 s.rs_h rsHC ⋆ array (t := i32) s.rs_pool rsPoolC ⋆ Rloop) mL) ?_ ?_
  · intro J rem ⟨iV, ⟨⟩⟩ mL hrec
      ⟨hi_le, _, rsN, pt, rsMC, rsPoolC, rsLC, rsHC, hrsN_eq, hrsN_le, hpt_ge, hpt_le,
        hrsmC_len, hrslC_len, hrshC_len, hrspC_len, hPrefIdx, hPrefPool, hSlices,
        hWords, hCorr, hmL⟩
    let sC : ArCtxState := { s with rs_n := BitVec.ofNat 32 rsN, rs_ptop := BitVec.ofNat 64 pt }
    have hrsN_toNat : (BitVec.ofNat 32 rsN).toNat = rsN := by c0_bv_omega
    have hpt_toNat : (BitVec.ofNat 64 pt).toNat = pt := by c0_bv_omega
    have hfail_pack : ∀ {mF : Mem 64},
        (arCtxMem cx sC ⋆ array (t := i32) s.rs_m rsMC ⋆ array64 s.rs_l rsLC ⋆
          array64 s.rs_h rsHC ⋆ array (t := i32) s.rs_pool rsPoolC ⋆ Rloop) mF →
        Q (false, ⟨⟩) mF := fun {mF} hmF =>
      hQ false sC ruleOff ruleN rsMC rsLC rsHC rsPoolC mF
        (by simp [sC, hrsN_toNat, hrsN_le]) (by simp [sC, hpt_toNat, hpt_le]) rfl
        rfl rfl hrsmC_len hrslC_len hrshC_len hrspC_len (fun h => by cases h)
        (storeRule_pack_mem rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          hrsmC_len hrspC_len htBack (by dsimp only [Rloop] at hmF; exact hmF))
    c0_hsteps_nogrp
    · have hi_lt : iV.toNat < s.tn.toNat := hc
      have hi_tm : iV.toNat < srcTm.length := by omega
      let RtmS := arCtxMem cx sC ⋆ array (t := i32) s.rs_m rsMC ⋆ array64 s.rs_l rsLC ⋆
        array64 s.rs_h rsHC ⋆ array (t := i32) s.rs_pool rsPoolC ⋆
        array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
        array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆ array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
        array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
        array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
        u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
      refine wp_load_arr32_idx (base := s.tm.getD s.tc.toNat 0#64) (off := 0) (i := iV)
        (xs := srcTm) (R := RtmS) (by dsimp only [Arg.val]; rw [htm_tc]; simp) (by simp; omega)
        (sep_cast hmL (by dsimp only [sC, RtmS, Rloop]; ac_rfl)) ?_
      let mOff32 := srcTm[0 + iV.toNat]'(by simp; omega)
      let mOff := mOff32.toNat
      have hmOff_eq : mOff = (srcTm.getD iV.toNat 0#32).toNat := by
        dsimp only [mOff, mOff32]; rw [← getD_eq_getElem srcTm 0#32 (by simp; omega), Nat.zero_add]
      have htSl := (htSlices iV.toNat hi_lt).1
      have htOk32 := (htSlices iV.toNat hi_lt).2
      rw [← hmOff_eq] at htSl htOk32
      have hm_sw : (BitVec.setWidth 64 mOff32).toNat = mOff := by c0_bv_omega
      c0_hsteps_nogrp
      let RpS := arCtxMem cx sC ⋆ array (t := i32) s.rs_m rsMC ⋆ array64 s.rs_l rsLC ⋆
        array64 s.rs_h rsHC ⋆ array (t := i32) s.rs_pool rsPoolC ⋆
        array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
        array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆ array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
        array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
        array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
        u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
      refine wp_load_arr32_abs (base := s.pool.getD s.pc.toNat 0#64) (xs := srcPool) (R := RpS)
        (i := BitVec.setWidth 64 mOff32) (by dsimp only [Arg.val, mOff32]; rw [hpool_pc]; simp)
        (by rw [hm_sw]; exact htSl.1)
        (sep_cast hmL (by dsimp only [sC, RpS, Rloop]; ac_rfl)) ?_
      let mlen := srcPool[(BitVec.setWidth 64 mOff32).toNat]'(by rw [hm_sw]; exact htSl.1)
      have hmlen_eq : mlen.toNat = (srcPool.getD mOff 0#32).toNat := by
        dsimp only [mlen]; rw [← getD_eq_getElem srcPool 0#32 (by rw [hm_sw]; exact htSl.1), hm_sw]
      have hmlen32 : mlen.toNat + 1 < 2 ^ 32 := by rw [hmlen_eq]; exact htOk32
      c0_hsteps_nogrp
      · exact hfail_pack hmL
      · exact hfail_pack hmL
      · have hrsN_lt : rsN < s.rs_cap.toNat := by c0_bv_omega
        have hpt_add : pt + mlen.toNat + 1 ≤ s.rs_pcap.toNat := by
          have hi_eq : (BitVec.setWidth 64 mOff32).toNat = mOff32.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := mOff32.isLt; omega)]
          have hml_eq : (srcPool[mOff32.toNat]'(by dsimp only [mOff] at htSl; exact htSl.1)).toNat =
              mlen.toNat := by
            simp only [mlen, hi_eq]
          have hc' : ¬ (2 ^ 64 - pt % 2 ^ 64 + s.rs_pcap.toNat) % 2 ^ 64 <
              ((srcPool[mOff32.toNat]'(by dsimp only [mOff] at htSl; exact htSl.1)).toNat +
                BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := hc
          rw [hml_eq, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
            Nat.mod_eq_of_lt (by omega : pt < 2 ^ 64),
            show 2 ^ 64 - pt + s.rs_pcap.toNat = 2 ^ 64 + (s.rs_pcap.toNat - pt) by omega,
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : s.rs_pcap.toNat - pt < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : mlen.toNat + 1 < 2 ^ 64)] at hc'
          exact Nat.le_of_not_lt fun hlt => hc' (by omega)
        have hi_tl : iV.toNat < srcTl.length := by omega
        have hi_th : iV.toNat < srcTh.length := by omega
        let rsM' := rsMC.set rsN (BitVec.ofNat 32 pt)
        let rsL' := rsLC.set rsN (srcTl[iV.toNat]'hi_tl)
        let rsH' := rsHC.set rsN (srcTh[iV.toNat]'hi_th)
        have hrs_idx : (BitVec.setWidth 64 (BitVec.ofNat 32 rsN)).toNat = rsN := by
          rw [BitVec.toNat_setWidth, hrsN_toNat, Nat.mod_eq_of_lt (by omega)]
        have hrs_val : (BitVec.ofNat 64 pt).setWidth 32 = BitVec.ofNat 32 pt := by
          apply BitVec.eq_of_toNat_eq
          have hpt32 : pt < 2 ^ 32 := by omega
          have hpt64 : pt < 2 ^ 64 := by omega
          simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpt32,
            Nat.mod_eq_of_lt hpt64]
        rw [hrs_idx, hrs_val] at hm
        let RtlS := arCtxMem cx sC ⋆ array (t := i32) s.rs_m rsM' ⋆ array64 s.rs_l rsLC ⋆
          array64 s.rs_h rsHC ⋆ array (t := i32) s.rs_pool rsPoolC ⋆
          array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
          array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
          array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
          array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
          u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
        refine wp_load_arr64_idx (base := s.tl.getD s.tc.toNat 0#64) (i := iV) (xs := srcTl)
          (R := RtlS) (by dsimp only [Arg.val, sC]; rw [htl_tc]) hi_tl
          (sep_cast hm (by dsimp only [RtlS, Rloop]; ac_rfl)) ?_
        let RrslS := arCtxMem cx sC ⋆ array (t := i32) s.rs_m rsM' ⋆ array64 s.rs_h rsHC ⋆
          array (t := i32) s.rs_pool rsPoolC ⋆ Rloop
        refine wp_store_arr64_idx (base := s.rs_l) (idx := BitVec.ofNat 32 rsN) (xs := rsLC)
          (val := srcTl[iV.toNat]'hi_tl) (R := RrslS) rfl rfl (by rw [hrsN_toNat]; omega)
          (sep_cast hm (by dsimp only [RrslS]; ac_rfl)) ?_
        intro m1 hm1
        dsimp only [RrslS] at hm1
        rw [hrsN_toNat] at hm1
        c0_hsteps_nogrp
        let RthS := arCtxMem cx sC ⋆ array (t := i32) s.rs_m rsM' ⋆ array64 s.rs_l rsL' ⋆
          array64 s.rs_h rsHC ⋆ array (t := i32) s.rs_pool rsPoolC ⋆
          array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
          array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
          array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
          array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
          u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
        refine wp_load_arr64_idx (base := s.th.getD s.tc.toNat 0#64) (i := iV) (xs := srcTh)
          (R := RthS) (by dsimp only [Arg.val, sC]; rw [hth_tc]) hi_th
          (sep_cast hm1 (by dsimp only [RthS, Rloop]; ac_rfl)) ?_
        let RrshS := arCtxMem cx sC ⋆ array (t := i32) s.rs_m rsM' ⋆ array64 s.rs_l rsL' ⋆
          array (t := i32) s.rs_pool rsPoolC ⋆ Rloop
        refine wp_store_arr64_idx (base := s.rs_h) (idx := BitVec.ofNat 32 rsN) (xs := rsHC)
          (val := srcTh[iV.toNat]'hi_th) (R := RrshS) rfl rfl (by rw [hrsN_toNat]; omega)
          (sep_cast hm1 (by dsimp only [RrshS]; ac_rfl)) ?_
        intro m2 hm2
        dsimp only [RrshS] at hm2
        rw [hrsN_toNat] at hm2
        c0_hsteps_nogrp
        refine wp_loop_group (fun remj ⟨jV, ⟨⟩⟩ mJ =>
            jV.toNat ≤ mlen.toNat + 1 ∧ remj = mlen.toNat + 1 - jV.toNat ∧
            ∃ rsPJ : List (BitVec 32), rsPJ.length = rsPoolC.length ∧
              (∀ q < pt, rsPJ.getD q 0#32 = rsPoolC.getD q 0#32) ∧
              (∀ r < jV.toNat, rsPJ.getD (pt + r) 0#32 = srcPool.getD (mOff + r) 0#32) ∧
              (arCtxMem cx sC ⋆ array (t := i32) s.rs_m rsM' ⋆ array64 s.rs_l rsL' ⋆
                array64 s.rs_h rsH' ⋆ array (t := i32) s.rs_pool rsPJ ⋆ Rloop) mJ) ?_ ?_
        · intro Jj remj ⟨jV, ⟨⟩⟩ mJ hrecj ⟨hj_le, _, rsPJ, hrspJ_len, hOld, hCopied, hmJ⟩
          c0_hsteps_nogrp
          · have hj_ml : jV.toNat ≤ mlen.toNat := by
              have hc' : jV.toNat ≤
                  (srcPool[mOff32.toNat]'(by dsimp only [mOff] at htSl; exact htSl.1)).toNat := hc
              simpa only [mlen, hm_sw] using hc'
            have hj_src : mOff + jV.toNat < srcPool.length := by
              have h1 := htSl.2
              rw [← hmlen_eq] at h1
              exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_le hj_ml) mOff)
                (by dsimp only [srcPool]; exact Nat.le_trans (by omega) h1)
            have hj_dst : pt + jV.toNat < rsPJ.length := by omega
            have hm_ptr : s.pool[s.pc.toNat]'(by rw [hl_s.pool]; exact hpc) +
                BitVec.setWidth 64 (srcTm[0 + iV.toNat]'(by simp; exact hi_tm)) * 4 +
                BitVec.setWidth 64 jV * 4 =
                s.pool.getD s.pc.toNat 0#64 + BitVec.ofNat 64 (4 * mOff) +
                  BitVec.setWidth 64 jV * 4 := by
              rw [hpool_pc]
              apply congrArg (· + BitVec.setWidth 64 jV * 4)
              apply congrArg (s.pool.getD s.pc.toNat 0#64 + ·)
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_mul, BitVec.toNat_ofNat, hm_sw,
                show ((4 : BitVec 64)).toNat = 4 from rfl, Nat.mul_comm mOff 4]
            let RspJ := arCtxMem cx sC ⋆ array (t := i32) s.rs_m rsM' ⋆ array64 s.rs_l rsL' ⋆
              array64 s.rs_h rsH' ⋆ array (t := i32) s.rs_pool rsPJ ⋆
              array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
              array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
                array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
              array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
              array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
              u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
            refine wp_load_arr32_idx (base := s.pool.getD s.pc.toNat 0#64) (off := mOff)
              (i := jV) (xs := srcPool) (R := RspJ) hm_ptr hj_src
              (sep_cast hmJ (by dsimp only [RspJ, Rloop]; ac_rfl)) ?_
            have hptj_toNat : (BitVec.ofNat 64 pt + BitVec.setWidth 64 jV).toNat =
                pt + jV.toNat := by
              rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by have := jV.isLt; omega),
                Nat.mod_eq_of_lt (by omega)]
            let RrsPJ := arCtxMem cx sC ⋆ array (t := i32) s.rs_m rsM' ⋆ array64 s.rs_l rsL' ⋆
              array64 s.rs_h rsH' ⋆ Rloop
            refine wp_store_arr32_abs (base := s.rs_pool) (xs := rsPJ)
              (idx := BitVec.ofNat 64 pt + BitVec.setWidth 64 jV) (R := RrsPJ) rfl
              rfl (by rw [hptj_toNat]; exact hj_dst)
              (sep_cast hmJ (by dsimp only [RrsPJ]; ac_rfl)) ?_
            intro mJ' hmJ'
            dsimp only [RrsPJ] at hmJ'
            have hjp1 : (jV + 1#32).toNat = jV.toNat + 1 := by
              rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega)]
            c0_hsteps
            refine hrecj (mlen.toNat + 1 - (jV + 1#32).toNat) (jV + 1#32, ⟨⟩) mJ' (by omega)
              ⟨by rw [hjp1]; omega, rfl,
                rsPJ.set (pt + jV.toNat) (srcPool[mOff + jV.toNat]'hj_src),
                by simp [hrspJ_len], fun q hq => ?_, fun r hr => ?_, ?_⟩
            · rw [getD_set_eq rsPJ 0#32 _ hj_dst, ite_eq_right (by omega)]
              exact hOld q hq
            · rw [getD_set_eq rsPJ 0#32 _ hj_dst]
              by_cases hrj : r = jV.toNat
              · subst hrj; rw [ite_eq_left rfl, getD_eq_getElem srcPool 0#32 hj_src]
              · rw [ite_eq_right (by omega)]; exact hCopied r (by rw [hjp1] at hr; omega)
            · rw [hptj_toNat] at hmJ'; exact sep_cast hmJ' (by ac_rfl)
          · have hj_done : jV.toNat = mlen.toNat + 1 := by
              have hc' : ¬ jV.toNat ≤ mlen.toNat := hc
              omega
            have hCopied' : ∀ r ≤ mlen.toNat,
                rsPJ.getD (pt + r) 0#32 = srcPool.getD (mOff + r) 0#32 :=
              fun r hr => hCopied r (by omega)
            have hpt'_eq : BitVec.ofNat 64 pt + BitVec.setWidth 64 mlen + (1 : BitVec 64) =
                BitVec.ofNat 64 (pt + mlen.toNat + 1) := by
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                show ((1 : BitVec 64)).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : pt < 2 ^ 64),
                Nat.mod_eq_of_lt (by have := mlen.isLt; omega : mlen.toNat < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : pt + mlen.toNat < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : pt + mlen.toNat + 1 < 2 ^ 64)]
            have hrsn'_eq : BitVec.ofNat 32 rsN + (1 : BitVec 32) = BitVec.ofNat 32 (rsN + 1) := by
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
                show ((1 : BitVec 32)).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : rsN < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : rsN + 1 < 2 ^ 32)]
            have hip1 : (iV + 1#32).toNat = iV.toNat + 1 := by
              rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : iV.toNat + 1 < 2 ^ 32)]
            c0_hsteps
            have hstep := storeRule_step_inv hrsN_eq hpt_ge hPrefIdx hPrefPool hSlices hWords hCorr
              (by omega) (by omega) (by omega) hmOff_eq.symm hmlen_eq.symm hmlen32 (by omega)
              hOld hCopied'
              (show srcTl[iV.toNat]'hi_tl = srcTl.getD iV.toNat 0#64 by
                rw [← getD_eq_getElem srcTl 0#64 hi_tl])
              (show srcTh[iV.toNat]'hi_th = srcTh.getD iV.toNat 0#64 by
                rw [← getD_eq_getElem srcTh 0#64 hi_th])
            refine hrec (s.tn.toNat - (iV + 1#32).toNat) (iV + 1#32, ⟨⟩) _ (by omega)
              ⟨by omega, rfl, rsN + 1, pt + mlen.toNat + 1, rsM', rsPJ, rsL', rsH',
                by omega, by omega, by omega, hpt_add,
                by simp [rsM', hrsmC_len], by simp [rsL', hrslC_len],
                by simp [rsH', hrshC_len], hrspJ_len.trans hrspC_len,
                hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1,
                ?_, ?_⟩
            · rw [hip1]; exact hstep.2.2.2.2
            · dsimp only [sC] at hm; dsimp only [mlen] at hpt'_eq
              rw [hpt'_eq, hrsn'_eq] at hm; exact sep_cast hm (by ac_rfl)
        · intro Jj hJj
          c0_hsteps
          exact hJj (mlen.toNat + 1) (0#32, ⟨⟩) m2
            ⟨Nat.zero_le _, rfl, rsPoolC, rfl, fun _ _ => rfl,
              fun _ hr => absurd hr (Nat.not_lt_zero _),
              sep_cast hm2 (by dsimp only [Rloop]; ac_rfl)⟩
    · have hi_done : iV.toNat = s.tn.toNat := by c0_bv_omega
      have hrsN_done : rsN = s.rs_n.toNat + s.tn.toNat := by rw [hrsN_eq, hi_done]
      have hv_ro : v.toNat < ruleOff.length := by omega
      have hv_rn : v.toNat < ruleN.length := by omega
      let Rroff := arCtxMem cx sC ⋆ array (t := i32) s.rs_m rsMC ⋆ array64 s.rs_l rsLC ⋆
        array64 s.rs_h rsHC ⋆ array (t := i32) s.rs_pool rsPoolC ⋆
        array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
        array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
        array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
        array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
        array (t := i32) s.rule_n ruleN ⋆
        array64 (s.ts.getD s.tc.toNat 0#64) (if s.tc.toNat = 0 then ts0 else ts1) ⋆
        u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ restT ⋆ R
      refine wp_store_arr32_idx (base := s.rule_off) (idx := v) (xs := ruleOff)
        (val := s.rs_n) (R := Rroff) rfl rfl hv_ro
        (sep_cast hmL (by dsimp only [Rroff, Rloop]; ac_rfl)) ?_
      intro m3 hm3
      dsimp only [Rroff] at hm3
      c0_hsteps
      have hDone := storeRule_done_rulesRep hv_lt htcap30 htn_le hrspcap32 (by omega) hpt_le
        rfl rfl hrsmC_len hrslC_len hrshC_len hrspC_len hRules htEval hPrefIdx hPrefPool
        (fun k hk => (hSlices k (by rw [hrsN_done]; exact hk)).1)
        (fun t ht => hCorr t (by rw [hi_done]; exact ht))
      let s' : ArCtxState :=
        { s with
          rs_n := BitVec.ofNat 32 (s.rs_n.toNat + s.tn.toNat), rs_ptop := BitVec.ofNat 64 pt }
      have hsC_eq : sC = s' := by simp only [sC, s', hrsN_done]
      have hv_sw' : (BitVec.setWidth 64 v).toNat = v.toNat := by c0_bv_omega
      rw [hsC_eq, hv_sw'] at hm
      have hm2' := storeRule_pack_mem (s := s) (s' := s') (srcTm := srcTm) (srcTl := srcTl)
        (srcTh := srcTh) (srcPool := srcPool) (ruleOff' := ruleOff.set v.toNat s.rs_n)
        (ruleN' := ruleN.set v.toNat s.tn) (restT := restT) (R := R)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        hrsmC_len hrspC_len htBack (sep_cast hm (by ac_rfl))
      have hs'n_toNat : s'.rs_n.toNat = s.rs_n.toNat + s.tn.toNat := by
        dsimp only [s']; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := s.rs_cap.isLt; omega)]
      have hs'pt_toNat : s'.rs_ptop.toNat = pt := by
        dsimp only [s']
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := s.rs_pcap.isLt; omega)]
      refine hQ true s' (ruleOff.set v.toNat s.rs_n) (ruleN.set v.toNat s.tn)
        rsMC rsLC rsHC rsPoolC m (by rw [hs'n_toNat]; omega) (by rw [hs'pt_toNat]; omega)
        rfl (by simp) (by simp) hrsmC_len hrslC_len hrshC_len hrspC_len (fun _ => ?_) hm2'
      refine ⟨hDone, fun k hk => ?_, ?_, fun bd hSbRs hSbT k hk x hx => ?_, fun k hk => ?_⟩
      · rw [hs'n_toNat, ← hrsN_done] at hk
        by_cases hkn : k < s.rs_n.toNat
        · have hsm := hrsSlices k hkn
          have hsy : symListAt rsPool (rsM.getD k 0#32).toNat =
              symListAt rsPoolC (rsMC.getD k 0#32).toNat := by
            have hsm := hrsSlices k hkn
            rw [(hPrefIdx k hkn).1]
            simp only [symListAt, hPrefPool _ hsm.1]
            exact List.map_congr_left fun r hr => by
              have hr_lt := List.mem_range.mp hr
              have h2 := hsm.2
              rw [hPrefPool _ (by omega)]
          exact monoSorted_congr hsy (hrsSorted k hkn)
        · have hkt : k - s.rs_n.toNat < s.tn.toNat := by omega
          have hk_eq : s.rs_n.toNat + (k - s.rs_n.toNat) = k := by omega
          have hc := (hCorr (k - s.rs_n.toNat) (by rw [hi_done]; exact hkt)).1
          rw [hk_eq] at hc
          exact monoSorted_congr hc.symm (htSorted (k - s.rs_n.toNat) hkt)
      · rw [hs'n_toNat, hs'pt_toNat, ← hrsN_done]; exact hWords
      · rw [hs'n_toNat, ← hrsN_done] at hk
        by_cases hkn : k < s.rs_n.toNat
        · have hsm := hrsSlices k hkn
          have hsy : symListAt rsPool (rsM.getD k 0#32).toNat =
              symListAt rsPoolC (rsMC.getD k 0#32).toNat := by
            rw [(hPrefIdx k hkn).1]
            simp only [symListAt, hPrefPool _ hsm.1]
            exact List.map_congr_left fun r hr => by
              have hr_lt := List.mem_range.mp hr
              have h2 := hsm.2
              rw [hPrefPool _ (by omega)]
          rw [← hsy] at hx
          exact hSbRs k hkn x hx
        · have hkt : k - s.rs_n.toNat < s.tn.toNat := by omega
          have hk_eq : s.rs_n.toNat + (k - s.rs_n.toNat) = k := by omega
          have hc := (hCorr (k - s.rs_n.toNat) (by rw [hi_done]; exact hkt)).1
          rw [hk_eq] at hc
          rw [hc] at hx
          exact hSbT (k - s.rs_n.toNat) hkt x hx
      · rw [hs'n_toNat, ← hrsN_done] at hk; exact (hSlices k hk).2
  · intro J hJ
    c0_hsteps
    let Rinit := array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
      array (t := i32) s.rs_pool rsPool ⋆ Rloop
    let s0 : ArCtxState :=
      { s with rs_n := BitVec.ofNat 32 s.rs_n.toNat, rs_ptop := BitVec.ofNat 64 s.rs_ptop.toNat }
    have hm_init : (arCtxMem cx s0 ⋆ Rinit) m := by
      simp only [s0, BitVec.ofNat_toNat]
      exact sep_cast hm_u (by dsimp only [Rinit, Rloop]; ac_rfl)
    exact hJ s.tn.toNat (0#32, ⟨⟩) m
      ⟨Nat.zero_le _, rfl, s.rs_n.toNat, s.rs_ptop.toNat, rsM, rsPool, rsL, rsH,
        by simp, hrsn_le, le_refl _, hrspt_le, rfl, rfl, rfl, rfl,
        fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl,
        fun k hk => ⟨hrsSlices k hk, hrsOk32 k hk⟩,
        hrsWords, fun _ ht => absurd ht (Nat.not_lt_zero _),
        by dsimp only [s0, Rinit] at hm_init; exact sep_cast hm_init (by ac_rfl)⟩

end

end LeanQbe.T.Examples.Arisca.Proof
