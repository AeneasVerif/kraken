/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Driver0
public import LeanQbe.T.Examples.Arisca.Proof.Poly2Spec
public import LeanQbe.T.Examples.Arisca.Proof.Poly0
public import LeanQbe.T.Examples.Arisca.Proof.Sem
public import LeanQbe.T.Examples.Arisca.Proof.Arith
public import LeanQbe.T.Examples.Arisca.Proof.Arena
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import Kraken.Separation

/-!
# ARiSCA Rule Installer, Gate & Cone Specs (`Arisca.Proof.Driver1Base`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP contracts for `ar_install_rule`,
`ar_do_gate`, and `ar_do_cone`, pure `RulesRep` / `PartnerRep` / truth-table helpers, and
`ar_install_rule_wp`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca (Aig tOf tOf_bit tOf_lt xmask xmask_bit)
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Driver

/-! ## 1. WP Specifications (`arInstallRuleSpec`, `arDoGateSpec`, `arDoConeSpec`) -/

@[expose] public section

/-- WP specification for `ar_install_rule(cx, o, n)`. -/
def arInstallRuleSpec : Spec [i64, i32, i32] [.bool] :=
  fun ⟨cx, o, n, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (ruleOff ruleN partnerArr rsM : List (BitVec 32))
      (rsL rsH : List (BitVec 64)) (rsPool gsy : List (BitVec 32))
      (gcl gch : List (BitVec 64)) (R : Mem 64 → Prop),
      o.toNat < s.n_nets.toNat ∧ n.toNat ≤ 16 ∧
      s.n_nets.toNat ≤ 0x3FFFFFFF ∧
      s.rs_cap.toNat < 2 ^ 30 ∧ s.rs_pcap.toNat < 2 ^ 32 ∧
      s.n_nets.toNat ≤ ruleOff.length ∧ s.n_nets.toNat ≤ ruleN.length ∧
      s.n_nets.toNat ≤ partnerArr.length ∧
      s.rs_n.toNat ≤ s.rs_cap.toNat ∧ s.rs_ptop.toNat ≤ s.rs_pcap.toNat ∧
      s.rs_cap.toNat ≤ rsM.length ∧ s.rs_cap.toNat ≤ rsL.length ∧ s.rs_cap.toNat ≤ rsH.length ∧
      s.rs_pcap.toNat ≤ rsPool.length ∧
      80 ≤ gsy.length ∧ 16 ≤ gcl.length ∧ 16 ≤ gch.length ∧
      MasksOk s.modW s.mlo s.mhi ∧
      (∀ i < n.toNat,
        MonoSliceOk gsy (5 * i) 80 ∧ (gsy.getD (5 * i) 0#32).toNat + 1 < 2 ^ 32) ∧
      (∀ i < n.toNat, MonoSorted gsy (5 * i)) ∧
      (∀ i < s.rs_n.toNat,
        MonoSliceOk rsPool (rsM.getD i 0#32).toNat s.rs_ptop.toNat ∧
        (rsPool.getD (rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      RulesSorted rsPool rsM s.rs_n.toNat ∧
      monoTotalWords rsPool rsM s.rs_n.toNat ≤ s.rs_ptop.toNat ∧
      (∃ σ0 : Nat → Bool, PartnerRep σ0 s.n_nets.toNat partnerArr) ∧
      (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
        array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.gsy gsy ⋆
        array64 s.gcl gcl ⋆ array64 s.gch gch ⋆ rsMem s rsM rsL rsH rsPool ⋆ R) m ∧
      (∀ (ok : Bool) (s' : ArCtxState) (ruleOff' ruleN' rsM' : List (BitVec 32))
          (rsL' rsH' : List (BitVec 64)) (rsPool' : List (BitVec 32)) (m' : Mem 64),
        s'.rs_n.toNat ≤ s.rs_cap.toNat → s'.rs_ptop.toNat ≤ s.rs_pcap.toNat →
        s' = { s with rs_n := s'.rs_n, rs_ptop := s'.rs_ptop } →
        ruleOff'.length = ruleOff.length → ruleN'.length = ruleN.length →
        rsM'.length = rsM.length → rsL'.length = rsL.length →
        rsH'.length = rsH.length → rsPool'.length = rsPool.length →
        (ok = true →
          monoTotalWords rsPool' rsM' s'.rs_n.toNat ≤ s'.rs_ptop.toNat ∧
          (∀ bd : Nat, SymsBound rsPool rsM s.rs_n.toNat bd →
            (∀ i < n.toNat, ∀ x ∈ symListAt gsy (5 * i), x / 2 < bd) →
            SymsBound rsPool' rsM' s'.rs_n.toNat bd) ∧
          (∀ i < s'.rs_n.toNat,
            MonoSliceOk rsPool' (rsM'.getD i 0#32).toNat s'.rs_ptop.toNat ∧
            (rsPool'.getD (rsM'.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
          RulesSorted rsPool' rsM' s'.rs_n.toNat ∧
          (∀ σ : Nat → Bool,
            PartnerRep σ s.n_nets.toNat partnerArr →
            RulesRep s.modW σ s ruleOff ruleN rsM rsL rsH rsPool →
            polyEval s.modW σ gsy gsyMOff gcl gch n.toNat =
              bv s.modW (σ (2 * o.toNat)) →
            RulesRep s'.modW σ s' ruleOff' ruleN' rsM' rsL' rsH' rsPool')) →
        (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff' ⋆
          array (t := i32) s'.rule_n ruleN' ⋆ array (t := i32) s'.partner partnerArr ⋆
          array (t := i32) s'.gsy gsy ⋆ array64 s'.gcl gcl ⋆ array64 s'.gch gch ⋆
          rsMem s' rsM' rsL' rsH' rsPool' ⋆ R) m' →
        Q (ok, ⟨⟩) m')

/-- WP specification for `ar_do_gate(cx)` (universal over AIG assignments `ρ`). -/
def arDoGateSpec : Spec [i64] [.bool] :=
  fun ⟨cx, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (g : Aig) (artBytes : List UInt8)
      (rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32))
      (flippedArr : List (BitVec 8))
      (inNetArr outRefArr stkN stkP memoN : List (BitVec 32))
      (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32))
      (gcl gch : List (BitVec 64)) (rsM : List (BitVec 32))
      (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32))
      (R : Mem 64 → Prop),
      s.I.toNat = g.I ∧ s.M.toNat = g.M ∧ g.M ≤ 0x3FFFFFF0 ∧
      s.n_nets.toNat ≤ 0x3FFFFFFF ∧
      s.rs_cap.toNat < 2 ^ 30 ∧ s.rs_pcap.toNat < 2 ^ 32 ∧
      s.art.toNat + artBytes.length < 2 ^ 64 ∧ 4 * s.nw.toNat ≤ artBytes.length ∧
      160 ≤ stkN.length ∧ 160 ≤ stkP.length ∧ 64 ≤ memoN.length ∧ 64 ≤ memoV.length ∧
      128 ≤ dense.length ∧ 85 ≤ gsy.length ∧ 16 ≤ gcl.length ∧ 16 ≤ gch.length ∧
      MasksOk s.modW s.mlo s.mhi ∧
      AigRep g rhs0 rhs1 olit ∧
      BindRep s g bindArr inNetArr outRefArr ∧
      monoTotalWords rsPool rsM s.rs_n.toNat ≤ s.rs_ptop.toNat ∧
      (∀ i < s.rs_n.toNat, (rsPool.getD (rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      RulesSorted rsPool rsM s.rs_n.toNat ∧
      (∀ ρ : Nat → Bool,
        PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr ∧
        RulesRep s.modW (cSig g ρ bindArr) s ruleOff ruleN rsM rsL rsH rsPool) ∧
      (arCtxMem cx s ⋆ bytes s.art artBytes ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
        netTablesMem s bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
        gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆
        rsMem s rsM rsL rsH rsPool ⋆ R) m ∧
      (∀ (ok : Bool) (s' : ArCtxState)
          (ruleOff' ruleN' partnerArr' stkN' stkP' memoN' : List (BitVec 32))
          (memoV' dense' : List (BitVec 64)) (gsy' : List (BitVec 32))
          (gcl' gch' : List (BitVec 64)) (rsM' : List (BitVec 32))
          (rsL' rsH' : List (BitVec 64)) (rsPool' : List (BitVec 32))
          (m' : Mem 64),
        s'.rs_n.toNat ≤ s.rs_cap.toNat → s'.rs_ptop.toNat ≤ s.rs_pcap.toNat →
        (s.pos.toNat ≤ s.nw.toNat → s'.pos.toNat ≤ s.nw.toNat) →
        s' = { s with
          pos := s'.pos, rs_n := s'.rs_n, rs_ptop := s'.rs_ptop,
          g_lmask := s'.g_lmask, g_tin := s'.g_tin, g_tto := s'.g_tto,
          g_outs := s'.g_outs, g_innet := s'.g_innet, g_inneg := s'.g_inneg,
          g_lnode := s'.g_lnode, g_vs := s'.g_vs } →
        ruleOff'.length = ruleOff.length → ruleN'.length = ruleN.length →
        partnerArr'.length = partnerArr.length →
        stkN'.length = stkN.length → stkP'.length = stkP.length →
        memoN'.length = memoN.length → memoV'.length = memoV.length →
        dense'.length = dense.length → gsy'.length = gsy.length →
        gcl'.length = gcl.length → gch'.length = gch.length →
        rsM'.length = rsM.length → rsL'.length = rsL.length →
        rsH'.length = rsH.length → rsPool'.length = rsPool.length →
        (ok = true →
          monoTotalWords rsPool' rsM' s'.rs_n.toNat ≤ s'.rs_ptop.toNat ∧
          (SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
            SymsBound rsPool' rsM' s'.rs_n.toNat s.n_nets.toNat) ∧
          (∀ i < s'.rs_n.toNat,
            (rsPool'.getD (rsM'.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
          RulesSorted rsPool' rsM' s'.rs_n.toNat ∧
          (∀ ρ : Nat → Bool,
            PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr' ∧
            RulesRep s'.modW (cSig g ρ bindArr) s'
              ruleOff' ruleN' rsM' rsL' rsH' rsPool')) →
        (arCtxMem cx s' ⋆ bytes s'.art artBytes ⋆ aigArraysMem s' rhs0 rhs1 olit ⋆
          netTablesMem s' bindArr ruleOff' ruleN' partnerArr' flippedArr inNetArr outRefArr ⋆
          gateScratchMem s' stkN' stkP' memoN' memoV' dense' gsy' gcl' gch' ⋆
          rsMem s' rsM' rsL' rsH' rsPool' ⋆ R) m' →
        Q (ok, ⟨⟩) m')

/-- WP specification for `ar_do_cone(cx)` (universal over `Valid : (Nat → Bool) → Prop`). -/
def arDoConeSpec : Spec [i64] [.bool] :=
  fun ⟨cx, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (artBytes : List UInt8)
      (ruleOff ruleN partnerArr rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64))
      (rsPool tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
      (pool0 pool1 qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
      (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
      (Valid : (Nat → Bool) → Prop) (R : Mem 64 → Prop),
      s.pc.toNat < 2 ∧ s.tc.toNat < 2 ∧
      s.tcap.toNat < 2 ^ 30 ∧ 16 ≤ s.qcap.toNat ∧ s.qcap.toNat + 16 < 2 ^ 32 ∧
      s.pcap.toNat < 2 ^ 32 ∧ s.rs_cap.toNat < 2 ^ 30 ∧
      s.rs_pcap.toNat < 2 ^ 32 ∧ s.rs_pcap.toNat ≤ 4000000000 ∧
      s.n_nets.toNat ≤ 0x3FFFFFFF ∧ 2 * s.n_nets.toNat < 2 ^ 32 ∧
      s.art.toNat + artBytes.length < 2 ^ 64 ∧ 4 * s.nw.toNat ≤ artBytes.length ∧
      s.tcap.toNat ≤ tm0.length ∧ s.tcap.toNat ≤ tm1.length ∧
      s.tcap.toNat ≤ ts0.length ∧ s.tcap.toNat ≤ tl0.length ∧ s.tcap.toNat ≤ th0.length ∧
      s.tcap.toNat ≤ ts1.length ∧ s.tcap.toNat ≤ tl1.length ∧ s.tcap.toNat ≤ th1.length ∧
      s.pcap.toNat ≤ pool0.length ∧ s.pcap.toNat ≤ pool1.length ∧
      s.qcap.toNat ≤ qm.length ∧ s.qcap.toNat ≤ qs.length ∧
      s.qcap.toNat ≤ ql.length ∧ s.qcap.toNat ≤ qh.length ∧
      s.qcap.toNat ≤ ix.length ∧ s.qcap.toNat ≤ ix2.length ∧ ix.length = ix2.length ∧
      s.tcap.toNat ≤ bx.length ∧ s.qcap.toNat ≤ bx.length ∧ s.qcap.toNat + 1 ≤ vqOff.length ∧
      s.pcap.toNat ≤ vq.length ∧ s.qcap.toNat ≤ vqSkip.length ∧
      MasksOk s.modW s.mlo s.mhi ∧
      monoTotalWords rsPool rsM s.rs_n.toNat ≤ s.rs_ptop.toNat ∧
      (∀ i < s.rs_n.toNat, (rsPool.getD (rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      RulesSorted rsPool rsM s.rs_n.toNat ∧
      (∃ σ0 : Nat → Bool, Valid σ0) ∧
      (∀ σ : Nat → Bool, Valid σ →
        PartnerRep σ s.n_nets.toNat partnerArr ∧
        RulesRep s.modW σ s ruleOff ruleN rsM rsL rsH rsPool) ∧
      (arCtxMem cx s ⋆ bytes s.art artBytes ⋆ array (t := i32) s.rule_off ruleOff ⋆
        array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.partner partnerArr ⋆
        rsMem s rsM rsL rsH rsPool ⋆
        tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m ∧
      (∀ (ok : Bool) (s' : ArCtxState)
          (ruleOff' ruleN' rsM' : List (BitVec 32)) (rsL' rsH' : List (BitVec 64))
          (rsPool' tm0' tm1' : List (BitVec 32))
          (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64))
          (pool0' pool1' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64))
          (ix' ix2' bx' vqOff' vq' : List (BitVec 32)) (vqSkip' : List (BitVec 8))
          (m' : Mem 64),
        s'.pc.toNat < 2 → s'.tc.toNat < 2 →
        s'.rs_n.toNat ≤ s.rs_cap.toNat → s'.rs_ptop.toNat ≤ s.rs_pcap.toNat →
        (s.pos.toNat ≤ s.nw.toNat → s'.pos.toNat ≤ s.nw.toNat) →
        s' = { s with
          pos := s'.pos, rs_n := s'.rs_n, rs_ptop := s'.rs_ptop,
          tc := s'.tc, tn := s'.tn, pc := s'.pc, ptop := s'.ptop, qn := s'.qn,
          ix := s'.ix, ix2 := s'.ix2, cur_rm := s'.cur_rm, cur_rl := s'.cur_rl,
          cur_rh := s'.cur_rh, cur_rp := s'.cur_rp, cur_nr := s'.cur_nr } →
        ruleOff'.length = ruleOff.length → ruleN'.length = ruleN.length →
        rsM'.length = rsM.length → rsL'.length = rsL.length →
        rsH'.length = rsH.length → rsPool'.length = rsPool.length →
        tm0'.length = tm0.length → tm1'.length = tm1.length →
        ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
        ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
        pool0'.length = pool0.length → pool1'.length = pool1.length →
        qm'.length = qm.length → qs'.length = qs.length →
        ql'.length = ql.length → qh'.length = qh.length →
        ix'.length = ix.length → ix2'.length = ix2.length →
        ((s'.ix = s.ix ∧ s'.ix2 = s.ix2) ∨ (s'.ix = s.ix2 ∧ s'.ix2 = s.ix)) →
        bx'.length = bx.length → vqOff'.length = vqOff.length →
        vq'.length = vq.length → vqSkip'.length = vqSkip.length →
        (ok = true →
          monoTotalWords rsPool' rsM' s'.rs_n.toNat ≤ s'.rs_ptop.toNat ∧
          (SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
            SymsBound rsPool' rsM' s'.rs_n.toNat s.n_nets.toNat) ∧
          (∀ i < s'.rs_n.toNat,
            (rsPool'.getD (rsM'.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
          RulesSorted rsPool' rsM' s'.rs_n.toNat ∧
          (∀ σ : Nat → Bool, Valid σ →
            RulesRep s'.modW σ s' ruleOff' ruleN' rsM' rsL' rsH' rsPool')) →
        (arCtxMem cx s' ⋆ bytes s'.art artBytes ⋆ array (t := i32) s'.rule_off ruleOff' ⋆
          array (t := i32) s'.rule_n ruleN' ⋆ array (t := i32) s'.partner partnerArr ⋆
          rsMem s' rsM' rsL' rsH' rsPool' ⋆
          tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆
          qMem s' qm' qs' ql' qh' ix' ix2' bx' vqOff' vq' vqSkip' ⋆ R) m' →
        Q (ok, ⟨⟩) m')

end

/-! ## 2. Pure `RulesRep`, `PartnerRep`, Truth-Table, & Memory Helpers -/

public section

theorem ar_mvanish_univ {Γ : LeanQbe.T.Env}
    (hMvanish : ∀ xs m Q X, arMvanishSpec xs m Q X →
      Γ "ar_mvanish" [i64, i64] [.bool] xs m Q X)
    {cx mBase : BitVec 64} {s : ArCtxState} {partnerArr mArr : List (BitVec 32)} {mOff : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hM : MonoSliceOk mArr mOff mArr.length)
    (hlt32 : (mArr.getD mOff 0#32).toNat + 1 < 2 ^ 32)
    (hn32 : 2 * s.n_nets.toNat ≤ 2 ^ 32)
    (hPartEx : ∃ σ0 : Nat → Bool, PartnerRep σ0 s.n_nets.toNat partnerArr)
    (hm : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
      array (t := i32) mBase mArr ⋆ R) m)
    (hQ : ∀ ok : Bool,
      (ok = true → ∀ σ : Nat → Bool, PartnerRep σ s.n_nets.toNat partnerArr →
        monoValL σ (symListAt mArr mOff) = false) → Q (ok, ⟨⟩) m) :
    Γ "ar_mvanish" [i64, i64] [.bool] (cx, mBase + BitVec.ofNat 64 (4 * mOff), ⟨⟩) m Q X := by
  let ms := symListAt mArr mOff
  by_cases hpair : ∃ v < s.n_nets.toNat, partnerArr.getD v 0#32 ≠ cNone32 ∧
      (2 * v) ∈ ms ∧ (2 * (partnerArr.getD v 0#32).toNat) ∈ ms
  · obtain ⟨σ0, hPart0⟩ := hPartEx
    refine hMvanish _ m Q X
      ⟨s, partnerArr, mBase, mArr, mOff, σ0, R, rfl, hM, hlt32, hn32, hPart0, hm, fun ok _ => ?_⟩
    refine hQ ok (fun _ σ hPart => ?_)
    obtain ⟨v, hv, hne, hv_mem, hp_mem⟩ := hpair
    have hnot := (hPart.2 v hv hne).2
    by_cases hsv : σ (2 * v) = true
    · have hsp : σ (2 * (partnerArr.getD v 0#32).toNat) = false := by
        cases hb : σ (2 * (partnerArr.getD v 0#32).toNat)
        · rfl
        · exfalso; exact hnot ⟨hsv, hb⟩
      exact monoValL_false_of_mem hp_mem hsp
    · have hsf : σ (2 * v) = false := Bool.eq_false_iff.mpr hsv
      exact monoValL_false_of_mem hv_mem hsf
  · obtain ⟨σ0, hPart0⟩ := hPartEx
    let σms : Nat → Bool := fun x => decide (x ∈ ms)
    have hPartMs : PartnerRep σms s.n_nets.toNat partnerArr := by
      refine ⟨hPart0.1, fun v hv hne => ⟨(hPart0.2 v hv hne).1, fun ⟨h1, h2⟩ => ?_⟩⟩
      exact hpair ⟨v, hv, hne, of_decide_eq_true h1, of_decide_eq_true h2⟩
    refine hMvanish _ m Q X
      ⟨s, partnerArr, mBase, mArr, mOff, σms, R, rfl, hM, hlt32, hn32, hPartMs, hm,
        fun ok hok => ?_⟩
    refine hQ ok (fun htrue => ?_)
    have hfalse : monoValL σms ms = false := hok htrue
    have htrue_ms : monoValL σms ms = true := by
      rw [monoValL_eq_decide, decide_eq_true_eq]
      intro z hz; exact decide_eq_true hz
    rw [htrue_ms] at hfalse; cases hfalse

theorem gsyMOff_getD (i : Nat) (hi : i < 16) : (gsyMOff.getD i 0#32).toNat = 5 * i := by
  simp only [gsyMOff, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem symListAt_congr_lt {pool1 pool2 : List (BitVec 32)} {off bound : Nat}
    (hM : MonoSliceOk pool1 off bound)
    (heq : ∀ k < bound, pool1.getD k 0#32 = pool2.getD k 0#32) :
    symListAt pool2 off = symListAt pool1 off ∧ MonoSliceOk pool2 off bound := by
  have h0 : pool2.getD off 0#32 = pool1.getD off 0#32 := (heq off hM.1).symm
  have hM2 : MonoSliceOk pool2 off bound := ⟨hM.1, by rw [h0]; exact hM.2⟩
  refine ⟨?_, hM2⟩
  simp only [symListAt, h0]
  apply List.map_congr_left
  intro r hr; rw [List.mem_range] at hr
  rw [heq (off + 1 + r) (by have := hM.2; omega)]

theorem monoTotalWords_congr_lt {pool1 pool2 tm1 tm2 : List (BitVec 32)} {n bound : Nat}
    (hm : ∀ i < n, MonoSliceOk pool1 (tm1.getD i 0#32).toNat bound)
    (hp : ∀ k < bound, pool1.getD k 0#32 = pool2.getD k 0#32)
    (ht : ∀ i < n, tm1.getD i 0#32 = tm2.getD i 0#32) :
    monoTotalWords pool2 tm2 n = monoTotalWords pool1 tm1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [monoTotalWords_succ, monoTotalWords_succ,
      ih (fun i hi => hm i (Nat.lt_succ_of_lt hi)) (fun i hi => ht i (Nat.lt_succ_of_lt hi)),
      ← ht n (Nat.lt_succ_self n), ← hp (tm1.getD n 0#32).toNat (hm n (Nat.lt_succ_self n)).1]

theorem polyEvalRange_congr_lt {nOut : Nat} {σ : Nat → Bool}
    {pool1 pool2 mOff1 mOff2 : List (BitVec 32)} {cl1 cl2 ch1 ch2 : List (BitVec 64)}
    {lo n bound : Nat}
    (hm : ∀ k < n, MonoSliceOk pool1 (mOff1.getD (lo + k) 0#32).toNat bound)
    (hp : ∀ idx < bound, pool1.getD idx 0#32 = pool2.getD idx 0#32)
    (heq : ∀ k < n, mOff2.getD (lo + k) 0#32 = mOff1.getD (lo + k) 0#32 ∧
      cl2.getD (lo + k) 0#64 = cl1.getD (lo + k) 0#64 ∧
      ch2.getD (lo + k) 0#64 = ch1.getD (lo + k) 0#64) :
    polyEvalRange nOut σ pool2 mOff2 cl2 ch2 lo n =
      polyEvalRange nOut σ pool1 mOff1 cl1 ch1 lo n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [polyEvalRange_succ, polyEvalRange_succ,
      ih (fun k hk => hm k (Nat.lt_succ_of_lt hk)) (fun k hk => heq k (Nat.lt_succ_of_lt hk))]
    obtain ⟨hm', hl', hh'⟩ := heq n (Nat.lt_succ_self n)
    have hsym := (symListAt_congr_lt (hm n (Nat.lt_succ_self n)) hp).1
    simp only [termEval, hm', hl', hh', hsym]

theorem symListAt_copy_slice {gsy rsPool : List (BitVec 32)} {gOff pOff mlen : Nat}
    (hg : gsy.getD gOff 0#32 = BitVec.ofNat 32 mlen)
    (hmlen : mlen < 2 ^ 32)
    (hcopy : ∀ j ≤ mlen, rsPool.getD (pOff + j) 0#32 = gsy.getD (gOff + j) 0#32) :
    symListAt rsPool pOff = symListAt gsy gOff ∧
      MonoSliceOk rsPool pOff (pOff + mlen + 1) := by
  have h0 : (rsPool.getD pOff 0#32).toNat = mlen := by
    rw [show pOff = pOff + 0 by omega, hcopy 0 (Nat.zero_le _), Nat.add_zero, hg,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmlen]
  have hg0 : (gsy.getD gOff 0#32).toNat = mlen := by
    rw [hg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmlen]
  refine ⟨?_, ⟨by omega, by omega⟩⟩
  simp only [symListAt, h0, hg0]
  apply List.map_congr_left
  intro r hr; rw [List.mem_range] at hr
  rw [show pOff + 1 + r = pOff + (1 + r) by omega, hcopy (1 + r) (by omega),
    show gOff + (1 + r) = gOff + 1 + r by omega]

theorem rulesRep_install_done {nOut : Nat} {σ : Nat → Bool}
    {s s' : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)}
    {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)}
    {ruleOff' ruleN' rsM' : List (BitVec 32)}
    {rsL' rsH' : List (BitVec 64)} {rsPool' : List (BitVec 32)}
    {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)} {o n off cnt : Nat}
    (hs' : s' = { s with rs_n := s'.rs_n, rs_ptop := s'.rs_ptop })
    (ho : o < s.n_nets.toNat) (hn16 : n ≤ 16)
    (ho_len1 : ruleOff'.length = ruleOff.length) (ho_len2 : ruleN'.length = ruleN.length)
    (hm_len : rsM'.length = rsM.length) (hl_len : rsL'.length = rsL.length)
    (hh_len : rsH'.length = rsH.length) (hp_len : rsPool'.length = rsPool.length)
    (hsn_le : s'.rs_n.toNat ≤ s.rs_cap.toNat) (hspt_le : s'.rs_ptop.toNat ≤ s.rs_pcap.toNat)
    (hoff_eq : off = s.rs_n.toNat) (hcnt_eq : off + cnt = s'.rs_n.toNat) (hcnt_le : cnt ≤ n)
    (hSlices : ∀ i < s'.rs_n.toNat, MonoSliceOk rsPool' (rsM'.getD i 0#32).toNat s'.rs_ptop.toNat)
    (hrO : ∀ v < s.n_nets.toNat, v ≠ o →
      ruleOff'.getD v 0#32 = ruleOff.getD v 0#32 ∧ ruleN'.getD v 0#32 = ruleN.getD v 0#32)
    (hro_o : ruleOff'.getD o 0#32 = BitVec.ofNat 32 off)
    (hrn_o : ruleN'.getD o 0#32 = BitVec.ofNat 32 cnt)
    (hpreM : ∀ i < s.rs_n.toNat,
      rsM'.getD i 0#32 = rsM.getD i 0#32 ∧ rsL'.getD i 0#64 = rsL.getD i 0#64 ∧
      rsH'.getD i 0#64 = rsH.getD i 0#64)
    (hpreP : ∀ k < s.rs_ptop.toNat, rsPool'.getD k 0#32 = rsPool.getD k 0#32)
    (hRep : RulesRep nOut σ s ruleOff ruleN rsM rsL rsH rsPool)
    (hnew : polyEvalRange nOut σ rsPool' rsM' rsL' rsH' off cnt =
      polyEval nOut σ gsy gsyMOff gcl gch n)
    (heval : polyEval nOut σ gsy gsyMOff gcl gch n = bv nOut (σ (2 * o))) :
    RulesRep nOut σ s' ruleOff' ruleN' rsM' rsL' rsH' rsPool' := by
  have hsn : s'.n_nets.toNat = s.n_nets.toNat := by rw [hs']
  have hsc : s'.rs_cap.toNat = s.rs_cap.toNat := by rw [hs']
  have hspc : s'.rs_pcap.toNat = s.rs_pcap.toNat := by rw [hs']
  refine ⟨by rw [hsn, ho_len1]; exact hRep.1, by rw [hsn, ho_len2]; exact hRep.2.1,
    by rw [hsc]; exact hsn_le, by rw [hspc]; exact hspt_le,
    by rw [hsc, hm_len]; exact hRep.2.2.2.2.1, by rw [hsc, hl_len]; exact hRep.2.2.2.2.2.1,
    by rw [hsc, hh_len]; exact hRep.2.2.2.2.2.2.1, by rw [hspc, hp_len]; exact hRep.2.2.2.2.2.2.2.1,
    hSlices, fun v hv hne => ?_⟩
  rw [hsn] at hv
  by_cases hvo : v = o
  · subst hvo
    have hoff_lt : off < 2 ^ 32 := by rw [hoff_eq]; exact s.rs_n.isLt
    have hcnt_lt : cnt < 2 ^ 32 := by omega
    rw [hro_o, hrn_o, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hoff_lt, Nat.mod_eq_of_lt hcnt_lt]
    refine ⟨by omega, ?_⟩
    rw [hnew, heval]
  · obtain ⟨ho_eq, hn_eq⟩ := hrO v hv hvo
    rw [ho_eq, hn_eq]
    rw [hn_eq] at hne
    obtain ⟨hbd, hev⟩ := hRep.2.2.2.2.2.2.2.2.2 v hv hne
    refine ⟨by omega, ?_⟩
    rw [hev]
    refine (polyEvalRange_congr_lt
      (fun k hk => hRep.2.2.2.2.2.2.2.2.1 _ (by omega))
      (fun k hk => (hpreP k hk).symm)
      (fun k hk => hpreM _ (by omega))).symm

theorem all_mask_testBit {nl : BitVec 32} (hnl1 : 1 ≤ nl.toNat) (hnl6 : nl.toNat ≤ 6)
    {t : Nat} (ht : t < 2 ^ nl.toNat) :
    (if nl = 6#32 then ~~~0#64
      else (1#64 <<< BitVec.setWidth 64 (1#32 <<< nl)) - 1#64).toNat.testBit t = true := by
  by_cases h6 : nl = 6#32
  · rw [ite_eq_left h6]
    have ht64 : t < 64 := by
      have : nl.toNat = 6 := by rw [h6]; decide
      rw [this] at ht; omega
    have hval : (~~~0#64 : BitVec 64).toNat = 2 ^ 64 - 1 := by decide
    rw [hval, Nat.testBit_two_pow_sub_one]; exact decide_eq_true (by omega)
  · rw [ite_eq_right h6]
    have hlt6 : nl.toNat < 6 := by
      have hne : nl.toNat ≠ 6 := fun h => h6 (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    have hpow_le : 2 ^ nl.toNat ≤ 32 :=
      Nat.pow_le_pow_right (by decide) (by omega : nl.toNat ≤ 5)
    have h1sh : (1#32 <<< nl).toNat = 2 ^ nl.toNat := by
      rw [bv_c0_toNat_shiftLeft_bv, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.one_mul,
        Nat.mod_eq_of_lt (by omega)]
    have hsw : (BitVec.setWidth 64 (1#32 <<< nl)).toNat = 2 ^ nl.toNat := by
      rw [bv64_sw_toNat, h1sh]
    have h2sh : (1#64 <<< BitVec.setWidth 64 (1#32 <<< nl)).toNat = 2 ^ (2 ^ nl.toNat) := by
      rw [bv_c0_toNat_shiftLeft_bv, hsw, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.one_mul,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega : 2 ^ nl.toNat < 64))]
    have hpos : (1#64 : BitVec 64).toNat ≤ (1#64 <<< BitVec.setWidth 64 (1#32 <<< nl)).toNat := by
      rw [show (1#64 : BitVec 64).toNat = 1 from rfl, h2sh]; exact Nat.one_le_pow _ _ (by decide)
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hpos), h2sh,
      show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true ht

theorem gLmask_row_ok (g : Aig) (ρ : Nat → Bool) {nl : Nat} (hnl : nl ≤ 6)
    (all : BitVec 64) (bs : List (BitVec 32)) (lnode : List (BitVec 32)) (lmask : List (BitVec 64))
    (hall : ∀ t < 2 ^ nl, all.toNat.testBit t = true)
    (hnode : ∀ j < nl, lnode.getD j 0#32 = bs.getD j 0#32 >>> 1)
    (hmask : ∀ j < nl, lmask.getD j 0#64 =
      (BitVec.ofNat 64 (xmask j) &&& all) ^^^
        (if bs.getD j 0#32 &&& 1#32 ≠ 0#32 then all else 0#64)) :
    let t := tOf ((List.range nl).map (fun j => g.litVal ρ (bs.getD j 0#32).toNat))
    t < 2 ^ nl ∧ t < 64 ∧ all.toNat.testBit t = true ∧
      ∀ j < nl, (lmask.getD j 0#64).toNat.testBit t = g.nodeVal ρ (lnode.getD j 0#32).toNat := by
  dsimp only
  let lits := (List.range nl).map (fun j => g.litVal ρ (bs.getD j 0#32).toNat)
  let t := tOf lits
  have hlen : lits.length = nl := by simp [lits]
  have ht : t < 2 ^ nl := by simpa [hlen] using tOf_lt lits
  have ht64 : t < 64 := lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) hnl)
  have hallt : all.toNat.testBit t = true := hall t ht
  refine ⟨ht, ht64, hallt, fun j hj => ?_⟩
  rw [hmask j hj, hnode j hj, bv32_ushr1]
  have hxm : (BitVec.ofNat 64 (xmask j) &&& all).toNat.testBit t =
      g.litVal ρ (bs.getD j 0#32).toNat := by
    rw [bv64_and_testBit _ _ ht64, hallt, Bool.and_true]
    have hxlt : xmask j < 2 ^ 64 := by
      rcases show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxlt, xmask_bit j t (by omega) ht64]
    change (tOf lits).testBit j = _
    rw [tOf_bit, List.getD_eq_getElem?_getD]
    simp [lits, hj]
  rw [BitVec.toNat_xor, Nat.testBit_xor, hxm]
  by_cases hodd : bs.getD j 0#32 &&& 1#32 ≠ 0#32
  · rw [ite_eq_left hodd, hallt]
    have h1 : ((bs.getD j 0#32).toNat % 2 == 1) = true :=
      beq_iff_eq.mpr ((bv32_and1_ne _).mp hodd)
    dsimp only [Aig.litVal]; rw [h1]
    cases g.nodeVal ρ ((bs.getD j 0#32).toNat / 2) <;> rfl
  · have hev : ((bs.getD j 0#32).toNat % 2 == 1) = false :=
      beq_eq_false_iff_ne.mpr (fun h1 => hodd ((bv32_and1_ne _).mpr h1))
    rw [ite_eq_right hodd, show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.zero_testBit]
    dsimp only [Aig.litVal]; rw [hev]
    cases g.nodeVal ρ ((bs.getD j 0#32).toNat / 2) <;> rfl

theorem partnerRep_set_pair {σ : Nat → Bool} {nNets : Nat} {o0 o1 : BitVec 32}
    {partnerArr : List (BitVec 32)}
    (hPart : PartnerRep σ nNets partnerArr)
    (ho0 : o0.toNat < nNets) (ho1 : o1.toNat < nNets) (hne : o0 ≠ o1)
    (hno : ¬ (σ (2 * o0.toNat) = true ∧ σ (2 * o1.toNat) = true)) :
    PartnerRep σ nNets ((partnerArr.set o0.toNat o1).set o1.toNat o0) := by
  have hlen0 : o0.toNat < partnerArr.length := by have := hPart.1; omega
  have hlen1 : o1.toNat < (partnerArr.set o0.toNat o1).length := by
    rw [List.length_set]; have := hPart.1; omega
  have hneN : o0.toNat ≠ o1.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  refine ⟨by simp [hPart.1], fun v hv hne_c => ?_⟩
  by_cases hv1 : v = o1.toNat
  · subst hv1
    rw [d_getD_set_eq (partnerArr.set o0.toNat o1) 0#32 o0 hlen1]
    exact ⟨ho0, fun ⟨h1, h2⟩ => hno ⟨h2, h1⟩⟩
  · rw [getD_set_ne (partnerArr.set o0.toNat o1) 0#32 o0 hv1]
    by_cases hv0 : v = o0.toNat
    · subst hv0
      rw [d_getD_set_eq partnerArr 0#32 o1 hlen0]
      exact ⟨ho1, hno⟩
    · rw [getD_set_ne partnerArr 0#32 o1 hv0]
      rw [getD_set_ne (partnerArr.set o0.toNat o1) 0#32 o0 hv1,
        getD_set_ne partnerArr 0#32 o1 hv0] at hne_c
      exact hPart.2 v hv hne_c

theorem rsMem_unpack {s : ArCtxState} {rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool : List (BitVec 32)} :
    rsMem s rsM rsL rsH rsPool =
      (array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
       array (t := i32) s.rs_pool rsPool ⋆
       u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length) := by
  simp only [rsMem, arrayPad_u32_unfold]; ac_rfl

theorem rsMem_repack {s : ArCtxState} {rsM rsM' : List (BitVec 32)}
    {rsL' rsH' : List (BitVec 64)} {rsPool rsPool' : List (BitVec 32)}
    (hm : rsM'.length = rsM.length) (hp : rsPool'.length = rsPool.length) :
    (array (t := i32) s.rs_m rsM' ⋆ array64 s.rs_l rsL' ⋆ array64 s.rs_h rsH' ⋆
     array (t := i32) s.rs_pool rsPool' ⋆
     u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length) =
      rsMem s rsM' rsL' rsH' rsPool' := by
  rw [rsMem_unpack, hm, hp]

theorem netTablesMem_unpack {s : ArCtxState}
    {bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {inNetArr outRefArr : List (BitVec 32)} :
    netTablesMem s bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr =
      (array (t := i32) s.bind bindArr ⋆ array (t := i32) s.rule_off ruleOff ⋆
       array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.partner partnerArr ⋆
       u32PadTail s.bind bindArr.length ⋆ u32PadTail s.rule_off ruleOff.length ⋆
       u32PadTail s.rule_n ruleN.length ⋆ u32PadTail s.partner partnerArr.length ⋆
       arrayPad i8 s.flipped flippedArr ⋆ arrayPad i32 s.in_net inNetArr ⋆
       arrayPad i32 s.out_ref outRefArr) := by
  simp only [netTablesMem, arrayPad_u32_unfold]; ac_rfl

theorem netTablesMem_repack {s : ArCtxState}
    {bindArr ruleOff ruleOff' ruleN ruleN' partnerArr partnerArr' : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {inNetArr outRefArr : List (BitVec 32)}
    (h1 : ruleOff'.length = ruleOff.length) (h2 : ruleN'.length = ruleN.length)
    (h3 : partnerArr'.length = partnerArr.length) :
    (array (t := i32) s.bind bindArr ⋆ array (t := i32) s.rule_off ruleOff' ⋆
     array (t := i32) s.rule_n ruleN' ⋆ array (t := i32) s.partner partnerArr' ⋆
     u32PadTail s.bind bindArr.length ⋆ u32PadTail s.rule_off ruleOff.length ⋆
     u32PadTail s.rule_n ruleN.length ⋆ u32PadTail s.partner partnerArr.length ⋆
     arrayPad i8 s.flipped flippedArr ⋆ arrayPad i32 s.in_net inNetArr ⋆
     arrayPad i32 s.out_ref outRefArr) =
      netTablesMem s bindArr ruleOff' ruleN' partnerArr' flippedArr inNetArr outRefArr := by
  rw [netTablesMem_unpack, h1, h2, h3]

theorem gateScratchMem_unpack {s : ArCtxState} {stkN stkP memoN : List (BitVec 32)}
    {memoV dense : List (BitVec 64)} {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)} :
    gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch =
      (arrayPad i32 s.stk_n stkN ⋆ arrayPad i32 s.stk_p stkP ⋆ arrayPad i32 s.memo_n memoN ⋆
       array64 s.memo_v memoV ⋆ array64 s.dense dense ⋆ array (t := i32) s.gsy gsy ⋆
       array64 s.gcl gcl ⋆ array64 s.gch gch ⋆ u32PadTail s.gsy gsy.length) := by
  simp only [gateScratchMem, arrayPad_u32_unfold]; ac_rfl

theorem gateScratchMem_repack {s : ArCtxState} {stkN stkP memoN : List (BitVec 32)}
    {memoV dense : List (BitVec 64)} {gsy gsy' : List (BitVec 32)}
    {gcl gch : List (BitVec 64)} (hg : gsy'.length = gsy.length) :
    (arrayPad i32 s.stk_n stkN ⋆ arrayPad i32 s.stk_p stkP ⋆ arrayPad i32 s.memo_n memoN ⋆
     array64 s.memo_v memoV ⋆ array64 s.dense dense ⋆ array (t := i32) s.gsy gsy' ⋆
     array64 s.gcl gcl ⋆ array64 s.gch gch ⋆ u32PadTail s.gsy gsy.length) =
      gateScratchMem s stkN stkP memoN memoV dense gsy' gcl gch := by
  rw [gateScratchMem_unpack, hg]

theorem array64_split_16 {p : BitVec 64} {xs : List (BitVec 64)} (h : 16 ≤ xs.length) :
    array64 p xs = (array64 p (xs.take 16) ⋆ array64 (p + 128#64) (xs.drop 16)) := by
  conv => lhs; rw [← List.take_append_drop 16 xs]
  rw [array64_append, show (xs.take 16).length = 16 by simp [h]]

theorem dense_split8 (p : BitVec 64) (dense : List (BitVec 64)) (hd : 128 ≤ dense.length) :
    let d0 := dense.take 16
    let d1 := (dense.drop 16).take 16
    let d2 := (dense.drop 32).take 16
    let d3 := (dense.drop 48).take 16
    let d4 := (dense.drop 64).take 16
    let d5 := (dense.drop 80).take 16
    let d6 := (dense.drop 96).take 16
    let d7 := (dense.drop 112).take 16
    let dRest := dense.drop 128
    d0.length = 16 ∧ d1.length = 16 ∧ d2.length = 16 ∧ d3.length = 16 ∧
    d4.length = 16 ∧ d5.length = 16 ∧ d6.length = 16 ∧ d7.length = 16 ∧
    array64 p dense =
      (array64 p d0 ⋆ array64 (p + 128#64) d1 ⋆ array64 (p + 256#64) d2 ⋆
       array64 (p + 384#64) d3 ⋆ array64 (p + 512#64) d4 ⋆ array64 (p + 640#64) d5 ⋆
       array64 (p + 768#64) d6 ⋆ array64 (p + 896#64) d7 ⋆ array64 (p + 1024#64) dRest) := by
  refine ⟨by simp; omega, by simp; omega, by simp; omega, by simp; omega, by simp; omega,
    by simp; omega, by simp; omega, by simp; omega, ?_⟩
  rw [array64_split_16 (by omega)]
  rw [array64_split_16 (p := p + 128#64) (xs := dense.drop 16) (by simp; omega), List.drop_drop]
  rw [array64_split_16 (p := p + 128#64 + 128#64) (xs := dense.drop (16 + 16)) (by simp; omega),
    List.drop_drop]
  rw [array64_split_16 (p := p + 128#64 + 128#64 + 128#64) (xs := dense.drop (16 + 16 + 16))
    (by simp; omega), List.drop_drop]
  rw [array64_split_16 (p := p + 128#64 + 128#64 + 128#64 + 128#64)
    (xs := dense.drop (16 + 16 + 16 + 16)) (by simp; omega), List.drop_drop]
  rw [array64_split_16 (p := p + 128#64 + 128#64 + 128#64 + 128#64 + 128#64)
    (xs := dense.drop (16 + 16 + 16 + 16 + 16)) (by simp; omega), List.drop_drop]
  rw [array64_split_16 (p := p + 128#64 + 128#64 + 128#64 + 128#64 + 128#64 + 128#64)
    (xs := dense.drop (16 + 16 + 16 + 16 + 16 + 16)) (by simp; omega), List.drop_drop]
  rw [array64_split_16 (p := p + 128#64 + 128#64 + 128#64 + 128#64 + 128#64 + 128#64 + 128#64)
    (xs := dense.drop (16 + 16 + 16 + 16 + 16 + 16 + 16)) (by simp; omega), List.drop_drop]
  simp only [Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem dense_merge8 (p : BitVec 64) (d0 d1 d2 d3 d4 d5 d6 d7 dRest : List (BitVec 64))
    (h0 : d0.length = 16) (h1 : d1.length = 16) (h2 : d2.length = 16) (h3 : d3.length = 16)
    (h4 : d4.length = 16) (h5 : d5.length = 16) (h6 : d6.length = 16) (h7 : d7.length = 16) :
    let dense' := d0 ++ d1 ++ d2 ++ d3 ++ d4 ++ d5 ++ d6 ++ d7 ++ dRest
    dense'.length = 128 + dRest.length ∧
    (array64 p d0 ⋆ array64 (p + 128#64) d1 ⋆ array64 (p + 256#64) d2 ⋆
     array64 (p + 384#64) d3 ⋆ array64 (p + 512#64) d4 ⋆ array64 (p + 640#64) d5 ⋆
     array64 (p + 768#64) d6 ⋆ array64 (p + 896#64) d7 ⋆ array64 (p + 1024#64) dRest) =
      array64 p dense' := by
  refine ⟨by simp [h0, h1, h2, h3, h4, h5, h6, h7]; omega, ?_⟩
  simp only [List.append_assoc]
  rw [array64_append, h0, show p + BitVec.ofNat 64 (8 * 16) = p + 128#64 from rfl]
  rw [array64_append, h1, BitVec.add_assoc,
    show (128#64 : BitVec 64) + BitVec.ofNat 64 (8 * 16) = 256#64 from by decide]
  rw [array64_append, h2, BitVec.add_assoc,
    show (256#64 : BitVec 64) + BitVec.ofNat 64 (8 * 16) = 384#64 from by decide]
  rw [array64_append, h3, BitVec.add_assoc,
    show (384#64 : BitVec 64) + BitVec.ofNat 64 (8 * 16) = 512#64 from by decide]
  rw [array64_append, h4, BitVec.add_assoc,
    show (512#64 : BitVec 64) + BitVec.ofNat 64 (8 * 16) = 640#64 from by decide]
  rw [array64_append, h5, BitVec.add_assoc,
    show (640#64 : BitVec 64) + BitVec.ofNat 64 (8 * 16) = 768#64 from by decide]
  rw [array64_append, h6, BitVec.add_assoc,
    show (768#64 : BitVec 64) + BitVec.ofNat 64 (8 * 16) = 896#64 from by decide]
  rw [array64_append, h7, BitVec.add_assoc,
    show (896#64 : BitVec 64) + BitVec.ofNat 64 (8 * 16) = 1024#64 from by decide]
  ac_rfl

theorem monoTotalWords_drop_le {pool rsM : List (BitVec 32)} {off cnt n : Nat}
    (h : off + cnt ≤ n) :
    monoTotalWords pool (rsM.drop off) cnt ≤ monoTotalWords pool rsM n := by
  have h1 : monoTotalWords pool (rsM.drop off) cnt =
      (List.range cnt).foldl
        (fun acc r => acc + ((pool.getD (rsM.getD (off + r) 0#32).toNat 0#32).toNat + 1)) 0 := by
    induction cnt with
    | zero => rfl
    | succ c ih =>
      rw [monoTotalWords_succ, ih (by omega), List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hsplit : ∀ a b, monoTotalWords pool rsM (a + b) = monoTotalWords pool rsM a +
      (List.range b).foldl
        (fun acc r => acc + ((pool.getD (rsM.getD (a + r) 0#32).toNat 0#32).toNat + 1)) 0 := by
    intro a b
    induction b with
    | zero => simp [monoTotalWords]
    | succ b ih =>
      rw [← Nat.add_assoc, monoTotalWords_succ, ih, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      omega
  have hmono : ∀ a b, a ≤ b → monoTotalWords pool rsM a ≤ monoTotalWords pool rsM b := by
    intro a b hab
    rw [show b = a + (b - a) by omega, hsplit]
    omega
  calc
    monoTotalWords pool (rsM.drop off) cnt ≤ monoTotalWords pool rsM (off + cnt) := by
      rw [h1, hsplit off cnt]; omega
    _ ≤ monoTotalWords pool rsM n := hmono _ _ h

private theorem polyEvalRange_drop_eq (nOut : Nat) (σ : Nat → Bool)
    (rsPool rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (off cnt : Nat) :
    polyEvalRange nOut σ rsPool rsM rsL rsH off cnt =
      polyEval nOut σ rsPool (rsM.drop off) (rsL.drop off) (rsH.drop off) cnt := by
  induction cnt with
  | zero => rw [polyEvalRange_zero, polyEval_zero]
  | succ c ih =>
    rw [polyEval, polyEvalRange_succ, polyEvalRange_succ, Nat.zero_add, ← polyEval, ih]
    congr 1
    have hm_eq : (rsM.drop off).getD c 0#32 = rsM.getD (off + c) 0#32 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
    have hl_eq : (rsL.drop off).getD c 0#64 = rsL.getD (off + c) 0#64 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
    have hh_eq : (rsH.drop off).getD c 0#64 = rsH.getD (off + c) 0#64 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
    simp only [termEval, hm_eq, hl_eq, hh_eq]

theorem curRRep_of_rulesRep_drop {nOut : Nat} {σ : Nat → Bool} {s : ArCtxState}
    {ruleOff ruleN rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool : List (BitVec 32)} {v : BitVec 32}
    (hRep : RulesRep nOut σ s ruleOff ruleN rsM rsL rsH rsPool)
    (hv : v.toNat < s.n_nets.toNat) (hne : ruleN.getD v.toNat 0#32 ≠ cNone32) :
    let off := (ruleOff.getD v.toNat 0#32).toNat
    let cnt := (ruleN.getD v.toNat 0#32).toNat
    CurRRep nOut σ cnt (2 * v.toNat) (rsM.drop off) (rsL.drop off) (rsH.drop off) rsPool := by
  dsimp only
  obtain ⟨hbd, hev⟩ := hRep.2.2.2.2.2.2.2.2.2 v.toNat hv hne
  have hm_len : s.rs_n.toNat ≤ rsM.length := by have := hRep.2.2.1; have := hRep.2.2.2.2.1; omega
  have hl_len : s.rs_n.toNat ≤ rsL.length := by have := hRep.2.2.1; have := hRep.2.2.2.2.2.1; omega
  have hh_len : s.rs_n.toNat ≤ rsH.length := by
    have := hRep.2.2.1; have := hRep.2.2.2.2.2.2.1; omega
  have hp_len : s.rs_ptop.toNat ≤ rsPool.length := by
    have := hRep.2.2.2.1; have := hRep.2.2.2.2.2.2.2.1; omega
  let off := (ruleOff.getD v.toNat 0#32).toNat
  let cnt := (ruleN.getD v.toNat 0#32).toNat
  refine ⟨by rw [List.length_drop]; omega, by rw [List.length_drop]; omega,
    by rw [List.length_drop]; omega, fun i hi => ?_, ?_⟩
  · have hdrop : (rsM.drop off).getD i 0#32 = rsM.getD (off + i) 0#32 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [hdrop]
    have hsl := hRep.2.2.2.2.2.2.2.2.1 (off + i) (by omega)
    exact ⟨Nat.lt_of_lt_of_le hsl.1 hp_len, Nat.le_trans hsl.2 hp_len⟩
  · rw [hev, polyEvalRange_drop_eq]

theorem rs_split_at {s : ArCtxState} {rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {off : Nat} (hm : off ≤ rsM.length) (hl : off ≤ rsL.length) (hh : off ≤ rsH.length) :
    (array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH) =
      (array (t := i32) s.rs_m (rsM.take off) ⋆
       array (t := i32) (s.rs_m + BitVec.ofNat 64 (4 * off)) (rsM.drop off) ⋆
       array64 s.rs_l (rsL.take off) ⋆
       array64 (s.rs_l + BitVec.ofNat 64 (8 * off)) (rsL.drop off) ⋆
       array64 s.rs_h (rsH.take off) ⋆
       array64 (s.rs_h + BitVec.ofNat 64 (8 * off)) (rsH.drop off)) := by
  conv => lhs; rw [← List.take_append_drop off rsM, ← List.take_append_drop off rsL,
    ← List.take_append_drop off rsH]
  rw [array_append, array64_append, array64_append]
  simp only [List.length_take_of_le hm, List.length_take_of_le hl, List.length_take_of_le hh,
    Ty.bytes, Ty.size, Nat.reduceDiv, Nat.reduceAdd]
  ac_rfl

/-! ## 3. WP Proof: `ar_install_rule` -/

private theorem ar_install_rule_step_inv
    {s sCur : ArCtxState} {rsM rsMCur rsPool rsPoolCur rsPoolJ gsy : List (BitVec 32)}
    {rsL rsLCur rsH rsHCur gcl gch : List (BitVec 64)} {partnerArr : List (BitVec 32)}
    {i cnt mlen : BitVec 32} (hi_lt : i.toNat < 16)
    (hmlen_eq : mlen = gsy.getD (5 * i.toNat) 0#32)
    (hmlen32 : mlen.toNat + 1 < 2 ^ 32)
    (hrsn_eq : sCur.rs_n.toNat = s.rs_n.toNat + cnt.toNat)
    (hm_len : rsMCur.length = rsM.length) (hsn_lt : sCur.rs_n.toNat < rsM.length)
    (hl_len : rsLCur.length = rsL.length) (hsn_ltL : sCur.rs_n.toNat < rsL.length)
    (hh_len : rsHCur.length = rsH.length) (hsn_ltH : sCur.rs_n.toNat < rsH.length)
    (hspt_ge : s.rs_ptop.toNat ≤ sCur.rs_ptop.toNat)
    (hpt_lt32 : sCur.rs_ptop.toNat < 2 ^ 32)
    (hpreM : ∀ k < s.rs_n.toNat,
      rsMCur.getD k 0#32 = rsM.getD k 0#32 ∧
      rsLCur.getD k 0#64 = rsL.getD k 0#64 ∧ rsHCur.getD k 0#64 = rsH.getD k 0#64)
    (hpreP : ∀ k < s.rs_ptop.toNat, rsPoolCur.getD k 0#32 = rsPool.getD k 0#32)
    (hpj_pre : ∀ k < sCur.rs_ptop.toNat, rsPoolJ.getD k 0#32 = rsPoolCur.getD k 0#32)
    (hpj_cp : ∀ r < mlen.toNat + 1,
      rsPoolJ.getD (sCur.rs_ptop.toNat + r) 0#32 = gsy.getD (5 * i.toNat + r) 0#32)
    (hSl : ∀ k < sCur.rs_n.toNat,
      MonoSliceOk rsPoolCur (rsMCur.getD k 0#32).toNat sCur.rs_ptop.toNat ∧
      (rsPoolCur.getD (rsMCur.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted : RulesSorted rsPoolCur rsMCur sCur.rs_n.toNat)
    (hGsySorted : MonoSorted gsy (5 * i.toNat))
    (hTotCur : monoTotalWords rsPoolCur rsMCur sCur.rs_n.toNat ≤ sCur.rs_ptop.toNat)
    (hPoly : ∀ σ : Nat → Bool, PartnerRep σ s.n_nets.toNat partnerArr →
      polyEvalRange s.modW σ rsPoolCur rsMCur rsLCur rsHCur s.rs_n.toNat cnt.toNat =
        polyEval s.modW σ gsy gsyMOff gcl gch i.toNat) :
    let rsM1 := rsMCur.set sCur.rs_n.toNat (sCur.rs_ptop.setWidth 32)
    let rsL1 := rsLCur.set sCur.rs_n.toNat (gcl.getD i.toNat 0#64)
    let rsH1 := rsHCur.set sCur.rs_n.toNat (gch.getD i.toNat 0#64)
    let newPtop := sCur.rs_ptop.toNat + mlen.toNat + 1
    let newRsn := sCur.rs_n.toNat + 1
    (∀ k < s.rs_n.toNat,
      rsM1.getD k 0#32 = rsM.getD k 0#32 ∧
      rsL1.getD k 0#64 = rsL.getD k 0#64 ∧ rsH1.getD k 0#64 = rsH.getD k 0#64) ∧
    (∀ k < s.rs_ptop.toNat, rsPoolJ.getD k 0#32 = rsPool.getD k 0#32) ∧
    (∀ k < newRsn, MonoSliceOk rsPoolJ (rsM1.getD k 0#32).toNat newPtop ∧
      (rsPoolJ.getD (rsM1.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
    RulesSorted rsPoolJ rsM1 newRsn ∧
    monoTotalWords rsPoolJ rsM1 newRsn ≤ newPtop ∧
    (∀ σ : Nat → Bool, PartnerRep σ s.n_nets.toNat partnerArr →
      polyEvalRange s.modW σ rsPoolJ rsM1 rsL1 rsH1 s.rs_n.toNat (cnt.toNat + 1) =
        polyEval s.modW σ gsy gsyMOff gcl gch (i.toNat + 1)) := by
  intro rsM1 rsL1 rsH1 newPtop newRsn
  have hsym := symListAt_copy_slice (mlen := mlen.toNat)
    (by rw [← hmlen_eq]; simp) mlen.isLt (fun r hr => hpj_cp r (by omega))
  have h0_eq : rsPoolJ.getD sCur.rs_ptop.toNat 0#32 = mlen := by
    rw [show sCur.rs_ptop.toNat = sCur.rs_ptop.toNat + 0 by omega,
      hpj_cp 0 (by omega), Nat.add_zero, ← hmlen_eq]
  have hrs_ptop_sw : (sCur.rs_ptop.setWidth 32).toNat = sCur.rs_ptop.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hpt_lt32]
  have hm_last : (rsM1.getD sCur.rs_n.toNat 0#32).toNat = sCur.rs_ptop.toNat := by
    dsimp only [rsM1]; rw [d_getD_set_eq rsMCur 0#32 _ (by omega), hrs_ptop_sw]
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_, fun σ hPart => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hpreM k hk
    exact ⟨by dsimp only [rsM1]; rw [getD_set_ne rsMCur 0#32 _ (by omega), h1],
      by dsimp only [rsL1]; rw [getD_set_ne rsLCur 0#64 _ (by omega), h2],
      by dsimp only [rsH1]; rw [getD_set_ne rsHCur 0#64 _ (by omega), h3]⟩
  · rw [hpj_pre k (by omega), hpreP k hk]
  · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with rfl | hklt
    · rw [hm_last]
      exact ⟨hsym.2, by rw [h0_eq]; exact hmlen32⟩
    · have hm_old : rsM1.getD k 0#32 = rsMCur.getD k 0#32 := by
        dsimp only [rsM1]; exact getD_set_ne rsMCur 0#32 _ (by omega)
      obtain ⟨hm_sl, hm_lt⟩ := hSl k hklt
      have hc := symListAt_congr_lt hm_sl (fun idx hidx => (hpj_pre idx hidx).symm)
      rw [hm_old]
      exact ⟨⟨by have := hc.2.1; dsimp only [newPtop]; omega,
        by have := hc.2.2; dsimp only [newPtop]; omega⟩,
        by rw [hpj_pre _ hm_sl.1]; exact hm_lt⟩
  · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with rfl | hklt
    · rw [hm_last]; exact monoSorted_congr hsym.1.symm hGsySorted
    · have hm_old : rsM1.getD k 0#32 = rsMCur.getD k 0#32 := by
        dsimp only [rsM1]; exact getD_set_ne rsMCur 0#32 _ (by omega)
      have hc := symListAt_congr_lt (hSl k hklt).1 (fun idx hidx => (hpj_pre idx hidx).symm)
      rw [hm_old]; exact monoSorted_congr hc.1.symm (hSorted k hklt)
  · dsimp only [newRsn]
    rw [monoTotalWords_succ]
    have hprev : monoTotalWords rsPoolJ rsM1 sCur.rs_n.toNat =
        monoTotalWords rsPoolCur rsMCur sCur.rs_n.toNat :=
      monoTotalWords_congr_lt (fun k hk => (hSl k hk).1)
        (fun idx hidx => (hpj_pre idx hidx).symm)
        (fun k hk => (getD_set_ne rsMCur 0#32 _ (by omega)).symm)
    rw [hprev, hm_last, h0_eq]
    dsimp only [newPtop]; omega
  · rw [polyEvalRange_succ, polyEval, polyEvalRange_succ, Nat.zero_add]
    have hpe_pre : polyEvalRange s.modW σ rsPoolJ rsM1 rsL1 rsH1 s.rs_n.toNat cnt.toNat =
        polyEvalRange s.modW σ rsPoolCur rsMCur rsLCur rsHCur s.rs_n.toNat cnt.toNat := by
      refine polyEvalRange_congr_lt (fun k hk => (hSl (s.rs_n.toNat + k) (by omega)).1)
        (fun k hk => (hpj_pre k hk).symm) (fun k hk => ⟨?_, ?_, ?_⟩)
      · dsimp only [rsM1]; exact getD_set_ne rsMCur 0#32 _ (by omega)
      · dsimp only [rsL1]; exact getD_set_ne rsLCur 0#64 _ (by omega)
      · dsimp only [rsH1]; exact getD_set_ne rsHCur 0#64 _ (by omega)
    rw [hpe_pre, hPoly σ hPart]
    congr 1
    have hm_last' : (rsM1.getD (s.rs_n.toNat + cnt.toNat) 0#32).toNat = sCur.rs_ptop.toNat := by
      rw [← hrsn_eq, hm_last]
    have hl_last : rsL1.getD (s.rs_n.toNat + cnt.toNat) 0#64 = gcl.getD i.toNat 0#64 := by
      dsimp only [rsL1]; rw [← hrsn_eq, d_getD_set_eq rsLCur 0#64 _ (by omega)]
    have hh_last : rsH1.getD (s.rs_n.toNat + cnt.toNat) 0#64 = gch.getD i.toNat 0#64 := by
      dsimp only [rsH1]; rw [← hrsn_eq, d_getD_set_eq rsHCur 0#64 _ (by omega)]
    simp only [termEval, hm_last', hl_last, hh_last, hsym.1, gsyMOff_getD i.toNat hi_lt]

theorem ar_install_rule_wp (Γ : LeanQbe.T.Env)
    (hMvanish : ∀ xs m Q X, arMvanishSpec xs m Q X →
      Γ "ar_mvanish" [i64, i64] [.bool] xs m Q X) :
    ∀ xs m Q X, arInstallRuleSpec xs m Q X → Func.wp Γ ar_install_rule_body xs m Q X := by
  rintro ⟨cx, o, n, ⟨⟩⟩ m Q X
    ⟨s, ruleOff, ruleN, partnerArr, rsM, rsL, rsH, rsPool, gsy, gcl, gch, R,
     ho_lt, hn16, hnnets32, hrcap30, hrpcap32, hro_len, hrn_len, hpart_len,
     hrsn_le, hrspt_le, hrsm_len, hrsl_len, hrsh_len, hrsp_len,
     hgsy_len, hgcl_len, hgch_len, hmasks, hGsyOk, hGsySorted, hRsOk, hRsSorted, hTot,
     hPartEx, hm, hQ⟩
  rw [rsMem_unpack] at hm
  let Rpad : Mem 64 → Prop :=
    u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ R
  have hm0 : (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆
      array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.partner partnerArr ⋆
      array (t := i32) s.gsy gsy ⋆ array64 s.gcl gcl ⋆ array64 s.gch gch ⋆
      array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
      array (t := i32) s.rs_pool rsPool ⋆ Rpad) m := by
    dsimp only [Rpad]; exact sep_cast hm (by ac_rfl)
  c0_hsteps_nogrp
  refine wp_loop_group (fun rem ⟨cnt, i, ⟨⟩⟩ m' =>
      i.toNat ≤ n.toNat ∧ cnt.toNat ≤ i.toNat ∧ rem = n.toNat - i.toNat ∧
      ∃ (sCur : ArCtxState) (rsMCur rsPoolCur : List (BitVec 32))
        (rsLCur rsHCur : List (BitVec 64)),
        sCur = { s with rs_n := sCur.rs_n, rs_ptop := sCur.rs_ptop } ∧
        sCur.rs_n.toNat = s.rs_n.toNat + cnt.toNat ∧
        s.rs_ptop.toNat ≤ sCur.rs_ptop.toNat ∧
        sCur.rs_n.toNat ≤ s.rs_cap.toNat ∧ sCur.rs_ptop.toNat ≤ s.rs_pcap.toNat ∧
        rsMCur.length = rsM.length ∧ rsLCur.length = rsL.length ∧
        rsHCur.length = rsH.length ∧ rsPoolCur.length = rsPool.length ∧
        (∀ k < s.rs_n.toNat,
          rsMCur.getD k 0#32 = rsM.getD k 0#32 ∧
          rsLCur.getD k 0#64 = rsL.getD k 0#64 ∧ rsHCur.getD k 0#64 = rsH.getD k 0#64) ∧
        (∀ k < s.rs_ptop.toNat, rsPoolCur.getD k 0#32 = rsPool.getD k 0#32) ∧
        (∀ k < sCur.rs_n.toNat,
          MonoSliceOk rsPoolCur (rsMCur.getD k 0#32).toNat sCur.rs_ptop.toNat ∧
          (rsPoolCur.getD (rsMCur.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        RulesSorted rsPoolCur rsMCur sCur.rs_n.toNat ∧
        monoTotalWords rsPoolCur rsMCur sCur.rs_n.toNat ≤ sCur.rs_ptop.toNat ∧
        (∀ k < sCur.rs_n.toNat, s.rs_n.toNat ≤ k →
          ∃ idx < i.toNat, symListAt rsPoolCur (rsMCur.getD k 0#32).toNat =
            symListAt gsy (5 * idx)) ∧
        (∀ σ : Nat → Bool, PartnerRep σ s.n_nets.toNat partnerArr →
          polyEvalRange s.modW σ rsPoolCur rsMCur rsLCur rsHCur
              s.rs_n.toNat cnt.toNat =
            polyEval s.modW σ gsy gsyMOff gcl gch i.toNat) ∧
        (arCtxMem cx sCur ⋆ array (t := i32) s.rule_off ruleOff ⋆
          array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.partner partnerArr ⋆
          array (t := i32) s.gsy gsy ⋆ array64 s.gcl gcl ⋆ array64 s.gch gch ⋆
          array (t := i32) s.rs_m rsMCur ⋆ array64 s.rs_l rsLCur ⋆ array64 s.rs_h rsHCur ⋆
          array (t := i32) s.rs_pool rsPoolCur ⋆ Rpad) m') ?_ ?_
  · intro J rem ⟨cnt, i, ⟨⟩⟩ m' hrec
      ⟨hi_le, hcnt_le, _, sCur, rsMCur, rsPoolCur, rsLCur, rsHCur,
       hsCur, hrsn_eq, hspt_ge, hsn_cap, hspt_cap, hm_l, hl_l, hh_l, hp_l,
       hpreM, hpreP, hSl, hRsSortedCur, hTotCur, hGsyMapCur, hPoly, hmCur⟩
    have hrsn_c : sCur.n_nets = s.n_nets := by rw [hsCur]
    have hrs_cap_c : sCur.rs_cap = s.rs_cap := by rw [hsCur]
    have hrs_pcap_c : sCur.rs_pcap = s.rs_pcap := by rw [hsCur]
    have hrs_part_c : sCur.partner = s.partner := by rw [hsCur]
    have hrepack : ∀ {rsM' rsPool' : List (BitVec 32)} {rsL' rsH' : List (BitVec 64)}
        {s' : ArCtxState} {m'' : Mem 64},
        s' = { s with rs_n := s'.rs_n, rs_ptop := s'.rs_ptop } →
        rsM'.length = rsM.length → rsPool'.length = rsPool.length →
        (arCtxMem cx s' ⋆ array (t := i32) s.rule_off ruleOff ⋆
          array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.partner partnerArr ⋆
          array (t := i32) s.gsy gsy ⋆ array64 s.gcl gcl ⋆ array64 s.gch gch ⋆
          array (t := i32) s.rs_m rsM' ⋆ array64 s.rs_l rsL' ⋆ array64 s.rs_h rsH' ⋆
          array (t := i32) s.rs_pool rsPool' ⋆ Rpad) m'' →
        (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆
          array (t := i32) s'.rule_n ruleN ⋆ array (t := i32) s'.partner partnerArr ⋆
          array (t := i32) s'.gsy gsy ⋆ array64 s'.gcl gcl ⋆ array64 s'.gch gch ⋆
          rsMem s' rsM' rsL' rsH' rsPool' ⋆ R) m'' := by
      intro rsM' rsPool' rsL' rsH' s' m'' hs' hml hpl hm''
      have hro' : s'.rule_off = s.rule_off := by rw [hs']
      have hrn' : s'.rule_n = s.rule_n := by rw [hs']
      have hpa' : s'.partner = s.partner := by rw [hs']
      have hgy' : s'.gsy = s.gsy := by rw [hs']
      have hgl' : s'.gcl = s.gcl := by rw [hs']
      have hgh' : s'.gch = s.gch := by rw [hs']
      have hrm' : s'.rs_m = s.rs_m := by rw [hs']
      have hrl' : s'.rs_l = s.rs_l := by rw [hs']
      have hrh' : s'.rs_h = s.rs_h := by rw [hs']
      have hrp' : s'.rs_pool = s.rs_pool := by rw [hs']
      rw [hro', hrn', hpa', hgy', hgl', hgh', ← rsMem_repack hml hpl, hrm', hrl', hrh', hrp']
      dsimp only [Rpad] at hm''
      exact sep_cast hm'' (by ac_rfl)
    c0_hsteps_nogrp
    · have hi_lt : i.toNat < n.toNat := hc; clear hc
      have hip1 := bv32_add1_toNat (by omega : i.toNat + 1 < 2 ^ 32)
      have h5i_sw : (BitVec.setWidth 64 (5 * i) * 4) =
          BitVec.ofNat 64 (4 * (5 * i.toNat)) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_mul, Nat.mul_comm,
          Nat.mod_eq_of_lt (by omega : 4 * (5 * i.toNat) < 2 ^ 64)]
      have h5i_ok := hGsyOk i.toNat hi_lt
      have h5i_1 : 5 * i.toNat < 80 := h5i_ok.1.1
      have h5i_len : MonoSliceOk gsy (5 * i.toNat) gsy.length :=
        ⟨by omega, Nat.le_trans h5i_ok.1.2 hgsy_len⟩
      let Rm := arCtxMem cx sCur ⋆ array (t := i32) s.partner partnerArr ⋆
        array (t := i32) s.gsy gsy ⋆
        (array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
         array64 s.gcl gcl ⋆ array64 s.gch gch ⋆ array (t := i32) s.rs_m rsMCur ⋆
         array64 s.rs_l rsLCur ⋆ array64 s.rs_h rsHCur ⋆
         array (t := i32) s.rs_pool rsPoolCur ⋆ Rpad)
      have hmMv : (arCtxMem cx sCur ⋆ array (t := i32) sCur.partner partnerArr ⋆
          array (t := i32) s.gsy gsy ⋆
          (array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
           array64 s.gcl gcl ⋆ array64 s.gch gch ⋆ array (t := i32) s.rs_m rsMCur ⋆
           array64 s.rs_l rsLCur ⋆ array64 s.rs_h rsHCur ⋆
           array (t := i32) s.rs_pool rsPoolCur ⋆ Rpad)) m' := by
        rw [hrs_part_c]; exact sep_cast hmCur (by ac_rfl)
      have hgsy_c : sCur.gsy = s.gsy := by rw [hsCur]
      dsimp only [Arg.val]; rw [hgsy_c, h5i_sw]
      refine wp_join_group (fun ⟨cnt', _⟩ m'' =>
          cnt'.toNat ≤ i.toNat + 1 ∧
          ∃ (sNext : ArCtxState) (rsMNext rsPoolNext : List (BitVec 32))
            (rsLNext rsHNext : List (BitVec 64)),
            sNext = { s with rs_n := sNext.rs_n, rs_ptop := sNext.rs_ptop } ∧
            sNext.rs_n.toNat = s.rs_n.toNat + cnt'.toNat ∧
            s.rs_ptop.toNat ≤ sNext.rs_ptop.toNat ∧
            sNext.rs_n.toNat ≤ s.rs_cap.toNat ∧ sNext.rs_ptop.toNat ≤ s.rs_pcap.toNat ∧
            rsMNext.length = rsM.length ∧ rsLNext.length = rsL.length ∧
            rsHNext.length = rsH.length ∧ rsPoolNext.length = rsPool.length ∧
            (∀ k < s.rs_n.toNat,
              rsMNext.getD k 0#32 = rsM.getD k 0#32 ∧
              rsLNext.getD k 0#64 = rsL.getD k 0#64 ∧
              rsHNext.getD k 0#64 = rsH.getD k 0#64) ∧
            (∀ k < s.rs_ptop.toNat, rsPoolNext.getD k 0#32 = rsPool.getD k 0#32) ∧
            (∀ k < sNext.rs_n.toNat,
              MonoSliceOk rsPoolNext (rsMNext.getD k 0#32).toNat sNext.rs_ptop.toNat ∧
              (rsPoolNext.getD (rsMNext.getD k 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
            RulesSorted rsPoolNext rsMNext sNext.rs_n.toNat ∧
            monoTotalWords rsPoolNext rsMNext sNext.rs_n.toNat ≤ sNext.rs_ptop.toNat ∧
            (∀ k < sNext.rs_n.toNat, s.rs_n.toNat ≤ k →
              ∃ idx < i.toNat + 1, symListAt rsPoolNext (rsMNext.getD k 0#32).toNat =
                symListAt gsy (5 * idx)) ∧
            (∀ σ : Nat → Bool, PartnerRep σ s.n_nets.toNat partnerArr →
              polyEvalRange s.modW σ rsPoolNext rsMNext rsLNext rsHNext
                  s.rs_n.toNat cnt'.toNat =
                polyEval s.modW σ gsy gsyMOff gcl gch (i.toNat + 1)) ∧
            (arCtxMem cx sNext ⋆ array (t := i32) s.rule_off ruleOff ⋆
              array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.partner partnerArr ⋆
              array (t := i32) s.gsy gsy ⋆ array64 s.gcl gcl ⋆ array64 s.gch gch ⋆
              array (t := i32) s.rs_m rsMNext ⋆ array64 s.rs_l rsLNext ⋆
              array64 s.rs_h rsHNext ⋆ array (t := i32) s.rs_pool rsPoolNext ⋆ Rpad) m'')
        (fun _ ⟨cnt', _⟩ m'' hjoin => by
          c0_hsteps
          rw [← hip1] at hjoin
          exact hrec (n.toNat - (i + 1).toNat) (cnt', i + 1, ⟨⟩) m'' (by omega)
            ⟨by omega, hjoin.1, rfl, hjoin.2⟩)
        (fun J1 hJ1 => by
          apply wp_call_of_spec
          refine ar_mvanish_univ hMvanish h5i_len h5i_ok.2
            (by rw [hrsn_c]; omega) (by rw [hrsn_c]; exact hPartEx) hmMv fun okVan hokVan => ?_
          c0_hsteps_nogrp
          · have hvan : okVan = true := hc
            have hvan_all := hokVan hvan
            rw [hrsn_c] at hvan_all
            refine hJ1 (cnt, ⟨⟩) m' ⟨by omega, sCur, rsMCur, rsPoolCur, rsLCur, rsHCur,
              hsCur, hrsn_eq, hspt_ge, hsn_cap, hspt_cap, hm_l, hl_l, hh_l, hp_l,
              hpreM, hpreP, hSl, hRsSortedCur, hTotCur,
              fun k hk hge => by
                obtain ⟨idx, hidx, heq⟩ := hGsyMapCur k hk hge
                exact ⟨idx, Nat.lt_succ_of_lt hidx, heq⟩,
              fun σ hPart => ?_, hmCur⟩
            rw [polyEval, polyEvalRange_succ, Nat.zero_add, hPoly σ hPart,
              termEval, gsyMOff_getD i.toNat (by omega), hvan_all σ hPart]
            simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero]
            rfl
          · have hgsy_idx : 5 * i.toNat < gsy.length := by omega
            try c0_hsteps_nogrp
            refine wp_load_arr32 (base := s.gsy) (xs := gsy) (off := 5 * i.toNat) (i := 0)
              (R := arCtxMem cx sCur ⋆ array (t := i32) s.rule_off ruleOff ⋆
                array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.partner partnerArr ⋆
                array64 s.gcl gcl ⋆ array64 s.gch gch ⋆ array (t := i32) s.rs_m rsMCur ⋆
                array64 s.rs_l rsLCur ⋆ array64 s.rs_h rsHCur ⋆
                array (t := i32) s.rs_pool rsPoolCur ⋆ Rpad)
              (by simp) (by omega) (sep_cast hmCur (by ac_rfl)) (by
              let mlen := gsy[5 * i.toNat]'hgsy_idx
              have hmlen_eq : mlen = gsy.getD (5 * i.toNat) 0#32 :=
                getElem_eq_getD 0#32 hgsy_idx rfl
              have hmlen32 : mlen.toNat + 1 < 2 ^ 32 := by rw [hmlen_eq]; exact h5i_ok.2
              c0_hsteps_nogrp
              · exact hQ false sCur ruleOff ruleN rsMCur rsLCur rsHCur rsPoolCur m'
                  hsn_cap hspt_cap hsCur rfl rfl hm_l hl_l hh_l hp_l (fun h => by cases h)
                  (hrepack hsCur hm_l hp_l hmCur)
              · exact hQ false sCur ruleOff ruleN rsMCur rsLCur rsHCur rsPoolCur m'
                  hsn_cap hspt_cap hsCur rfl rfl hm_l hl_l hh_l hp_l (fun h => by cases h)
                  (hrepack hsCur hm_l hp_l hmCur)
              · have hrsn_lt : sCur.rs_n.toNat < s.rs_cap.toNat := by
                  have h' : ¬ s.rs_cap.toNat ≤ sCur.rs_n.toNat := by rw [← hrs_cap_c]; assumption
                  omega
                have hpt_le : sCur.rs_ptop.toNat ≤ s.rs_pcap.toNat := hspt_cap
                have hsub_eq : (s.rs_pcap - sCur.rs_ptop).toNat =
                    s.rs_pcap.toNat - sCur.rs_ptop.toNat :=
                  BitVec.toNat_sub_of_le (BitVec.le_def.mpr hpt_le)
                have hadd_lt64 : mlen.toNat + 1 < 2 ^ 64 := by omega
                have hadd_eq64 : (BitVec.setWidth 64 mlen + 1#64).toNat = mlen.toNat + 1 := by
                  rw [BitVec.toNat_add, bv64_sw_toNat, show (1#64 : BitVec 64).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt hadd_lt64]
                have hfit_p : mlen.toNat + 1 ≤ s.rs_pcap.toNat - sCur.rs_ptop.toNat := by
                  have h' : ¬ (s.rs_pcap - sCur.rs_ptop).toNat <
                      (BitVec.setWidth 64 mlen + 1#64).toNat := by
                    rw [← hrs_pcap_c]; assumption
                  omega
                have hpt_add_le : sCur.rs_ptop.toNat + mlen.toNat + 1 ≤ s.rs_pcap.toNat := by omega
                have hpt_lt32 : sCur.rs_ptop.toNat < 2 ^ 32 := by omega
                have hrm_lt : (BitVec.setWidth 64 sCur.rs_n).toNat < rsMCur.length := by
                  rw [bv64_sw_toNat]; omega
                have hrl_lt : (BitVec.setWidth 64 sCur.rs_n).toNat < rsLCur.length := by
                  rw [bv64_sw_toNat]; omega
                have hrh_lt : (BitVec.setWidth 64 sCur.rs_n).toNat < rsHCur.length := by
                  rw [bv64_sw_toNat]; omega
                have hi_gcl : (BitVec.setWidth 64 i).toNat < gcl.length := by
                  rw [bv64_sw_toNat]; omega
                have hi_gch : (BitVec.setWidth 64 i).toNat < gch.length := by
                  rw [bv64_sw_toNat]; omega
                have hrm_c : sCur.rs_m = s.rs_m := by rw [hsCur]
                have hrl_c : sCur.rs_l = s.rs_l := by rw [hsCur]
                have hrh_c : sCur.rs_h = s.rs_h := by rw [hsCur]
                have hrp_c : sCur.rs_pool = s.rs_pool := by rw [hsCur]
                have hgl_c : sCur.gcl = s.gcl := by rw [hsCur]
                have hgh_c : sCur.gch = s.gch := by rw [hsCur]
                rw [← hrm_c, ← hrl_c, ← hrh_c, ← hrp_c, ← hgl_c, ← hgh_c] at hmCur
                c0_hsteps_nogrp
                let rsM1 := rsMCur.set sCur.rs_n.toNat (sCur.rs_ptop.setWidth 32)
                let rsL1 := rsLCur.set sCur.rs_n.toNat (gcl.getD i.toNat 0#64)
                let rsH1 := rsHCur.set sCur.rs_n.toNat (gch.getD i.toNat 0#64)
                refine wp_loop_group (fun remj ⟨jV, _⟩ mj =>
                    jV.toNat ≤ mlen.toNat + 1 ∧ remj = mlen.toNat + 1 - jV.toNat ∧
                    ∃ rsPoolJ : List (BitVec 32),
                      rsPoolJ.length = rsPool.length ∧
                      (∀ k < sCur.rs_ptop.toNat, rsPoolJ.getD k 0#32 = rsPoolCur.getD k 0#32) ∧
                      (∀ r < jV.toNat,
                        rsPoolJ.getD (sCur.rs_ptop.toNat + r) 0#32 =
                          gsy.getD (5 * i.toNat + r) 0#32) ∧
                      (arCtxMem cx sCur ⋆ array (t := i32) s.rule_off ruleOff ⋆
                        array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.partner partnerArr ⋆
                        array (t := i32) s.gsy gsy ⋆ array64 s.gcl gcl ⋆ array64 s.gch gch ⋆
                        array (t := i32) s.rs_m rsM1 ⋆ array64 s.rs_l rsL1 ⋆
                        array64 s.rs_h rsH1 ⋆ array (t := i32) sCur.rs_pool rsPoolJ ⋆
                        Rpad) mj) ?_ ?_
                · intro Jj remj ⟨jV, _⟩ mj hrecj ⟨hj_le, _, rsPoolJ, hpj_l, hpj_pre, hpj_cp, hmj⟩
                  c0_hsteps_nogrp
                  · have hj_le_m : jV.toNat ≤ mlen.toNat := hc; clear hc
                    have hjp1 := bv32_add1_toNat (by omega : jV.toNat + 1 < 2 ^ 32)
                    have hsrc_lt : 5 * i.toNat + jV.toNat < gsy.length := by
                      have := h5i_ok.1.2; rw [← hmlen_eq] at this; omega
                    have hdst_lt : (sCur.rs_ptop + BitVec.setWidth 64 jV).toNat <
                        rsPoolJ.length := by
                      rw [BitVec.toNat_add, bv64_sw_toNat, Nat.mod_eq_of_lt (by omega)]; omega
                    have hdst_eq : (sCur.rs_ptop + BitVec.setWidth 64 jV).toNat =
                        sCur.rs_ptop.toNat + jV.toNat := by
                      rw [BitVec.toNat_add, bv64_sw_toNat, Nat.mod_eq_of_lt (by omega)]
                    have hsrc_adr : s.gsy + BitVec.ofNat 64 (4 * (5 * i.toNat)) +
                        BitVec.setWidth 64 jV * 4 =
                        s.gsy + BitVec.ofNat 64 (4 * (5 * i.toNat + jV.toNat)) := by
                      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
                      simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
                        Nat.mul_add, Nat.mul_comm jV.toNat 4]
                    refine wp_load_arr32_idx (base := s.gsy) (xs := gsy) (off := 5 * i.toNat)
                      (i := jV)
                      (R := arCtxMem cx sCur ⋆ array (t := i32) s.rule_off ruleOff ⋆
                        array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.partner partnerArr ⋆
                        array64 s.gcl gcl ⋆ array64 s.gch gch ⋆ array (t := i32) s.rs_m rsM1 ⋆
                        array64 s.rs_l rsL1 ⋆ array64 s.rs_h rsH1 ⋆
                        array (t := i32) sCur.rs_pool rsPoolJ ⋆ Rpad)
                      rfl hsrc_lt (sep_cast hmj (by ac_rfl)) ?_
                    c0_hsteps_nogrp
                    let rsPoolNext := rsPoolJ.set (sCur.rs_ptop.toNat + jV.toNat)
                      (gsy[5 * i.toNat + jV.toNat]'hsrc_lt)
                    refine hrecj (mlen.toNat + 1 - (jV + 1).toNat) (jV + 1, ⟨⟩) _ (by omega)
                      ⟨by omega, rfl, rsPoolNext, by simp [rsPoolNext, hpj_l], fun k hk => ?_,
                        fun r hr => ?_, ?_⟩
                    · dsimp only [rsPoolNext]
                      rw [getD_set_ne rsPoolJ 0#32 _ (by omega)]; exact hpj_pre k hk
                    · dsimp only [rsPoolNext]; rw [hjp1] at hr
                      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hr) with rfl | hrlt
                      · rw [d_getD_set_eq rsPoolJ 0#32 _ (by omega),
                          getElem_eq_getD 0#32 hsrc_lt rfl]
                      · rw [getD_set_ne rsPoolJ 0#32 _ (by omega)]; exact hpj_cp r hrlt
                    · dsimp only [rsPoolNext]
                      rw [← set_eq_of_eq (j := sCur.rs_ptop.toNat + jV.toNat)
                        (w := gsy[5 * i.toNat + jV.toNat]'hsrc_lt) hdst_eq rfl]
                      c0_frame
                  · have hj_eq : jV.toNat = mlen.toNat + 1 := by
                      simp only [Nat.add_zero] at hc
                      change ¬ jV.toNat ≤ mlen.toNat at hc
                      omega
                    have hrsn_p1 := bv32_add1_toNat (by omega : sCur.rs_n.toNat + 1 < 2 ^ 32)
                    have hcnt_p1 := bv32_add1_toNat (by omega : cnt.toNat + 1 < 2 ^ 32)
                    have hpt_new_eq : (sCur.rs_ptop + BitVec.setWidth 64 mlen + 1#64).toNat =
                        sCur.rs_ptop.toNat + mlen.toNat + 1 := by
                      rw [BitVec.toNat_add, BitVec.toNat_add, bv64_sw_toNat,
                        show (1#64 : BitVec 64).toNat = 1 from rfl,
                        Nat.mod_eq_of_lt (by omega : sCur.rs_ptop.toNat + mlen.toNat < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega)]
                    c0_hsteps
                    let sNext := { sCur with
                      rs_ptop := sCur.rs_ptop + BitVec.setWidth 64 mlen + 1#64,
                      rs_n := sCur.rs_n + 1 }
                    have hsNext_eq :
                        sNext = { s with rs_n := sNext.rs_n, rs_ptop := sNext.rs_ptop } := by
                      dsimp only [sNext]; rw [hsCur]
                    have hinv := ar_install_rule_step_inv (by omega)
                      hmlen_eq hmlen32 hrsn_eq hm_l (by omega) hl_l (by omega) hh_l (by omega)
                      hspt_ge hpt_lt32 hpreM hpreP hpj_pre (fun r hr => hpj_cp r (by omega))
                      hSl hRsSortedCur (hGsySorted i.toNat (by omega)) hTotCur hPoly
                    rcases hinv with
                      ⟨hpreM_next, hpreP_next, hSl_next, hRsSorted_next, hTot_next, hPoly_next⟩
                    refine hJ1 (cnt + 1, ⟨⟩) _ ⟨by rw [hcnt_p1]; omega, sNext, rsM1, rsPoolJ,
                      rsL1, rsH1, hsNext_eq,
                      by dsimp only [sNext]; rw [hrsn_p1, hcnt_p1, hrsn_eq]; omega,
                      by dsimp only [sNext]; rw [hpt_new_eq]; omega,
                      by dsimp only [sNext]; rw [hrsn_p1]; omega,
                      by dsimp only [sNext]; rw [hpt_new_eq]; exact hpt_add_le,
                      by simp [rsM1, hm_l], by simp [rsL1, hl_l], by simp [rsH1, hh_l], hpj_l,
                      hpreM_next, hpreP_next,
                      by simpa only [sNext, hrsn_p1, hpt_new_eq] using hSl_next,
                      by simpa only [sNext, hrsn_p1] using hRsSorted_next,
                      by simpa only [sNext, hrsn_p1, hpt_new_eq] using hTot_next,
                      fun k hk hge => by
                        have hk' : k < sCur.rs_n.toNat + 1 := by
                          dsimp only [sNext] at hk; rw [hrsn_p1] at hk; exact hk
                        rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk') with rfl | hklt
                        · have hsym_last := symListAt_copy_slice (mlen := mlen.toNat)
                            (by rw [← hmlen_eq]; simp) mlen.isLt (fun r hr => hpj_cp r (by omega))
                          have hrs_ptop_sw :
                              (sCur.rs_ptop.setWidth 32).toNat = sCur.rs_ptop.toNat := by
                            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hpt_lt32]
                          have hm_last :
                              (rsM1.getD sCur.rs_n.toNat 0#32).toNat = sCur.rs_ptop.toNat := by
                            dsimp only [rsM1]
                            rw [d_getD_set_eq rsMCur 0#32 _ (by omega), hrs_ptop_sw]
                          exact ⟨i.toNat, Nat.lt_succ_self _, by rw [hm_last, hsym_last.1]⟩
                        · have hm_old : rsM1.getD k 0#32 = rsMCur.getD k 0#32 := by
                            dsimp only [rsM1]; exact getD_set_ne rsMCur 0#32 _ (by omega)
                          have hc := symListAt_congr_lt (hSl k hklt).1
                            (fun idx hidx => (hpj_pre idx hidx).symm)
                          obtain ⟨idx, hidx, heq⟩ := hGsyMapCur k hklt hge
                          exact ⟨idx, Nat.lt_succ_of_lt hidx, by rw [hm_old, hc.1, heq]⟩,
                      by simpa only [hcnt_p1] using hPoly_next, ?_⟩
                    dsimp only [sNext]
                    rw [← hrp_c, show sCur.rs_ptop + BitVec.setWidth 64 mlen + 1#64 =
                      sCur.rs_ptop + BitVec.setWidth 64 (gsy[5 * i.toNat + 0]'hgsy_idx) + 1
                      from rfl]
                    c0_frame
                · intro Jj hJj; c0_hsteps
                  refine hJj (mlen.toNat + 1) (0#32, ⟨⟩) _
                    ⟨Nat.zero_le _, rfl, rsPoolCur, hp_l, fun _ _ => rfl,
                      fun _ hr => absurd hr (Nat.not_lt_zero _), ?_⟩
                  dsimp only [rsM1, rsL1, rsH1]
                  rw [← hrm_c, ← hrl_c, ← hrh_c, ← hgl_c, ← hgh_c,
                    ← set_eq_of_eq (j := sCur.rs_n.toNat) (w := sCur.rs_ptop.setWidth 32)
                      bv64_sw_toNat rfl,
                    ← set_eq_of_eq (j := sCur.rs_n.toNat) (w := gcl.getD i.toNat 0#64)
                      bv64_sw_toNat (getElem_eq_getD 0#64 hi_gcl bv64_sw_toNat),
                    ← set_eq_of_eq (j := sCur.rs_n.toNat) (w := gch.getD i.toNat 0#64)
                      bv64_sw_toNat (getElem_eq_getD 0#64 hi_gch bv64_sw_toNat)]
                  c0_frame))
    · have hi_eq : i.toNat = n.toNat := by omega
      have hro_lt : (BitVec.setWidth 64 o).toNat < ruleOff.length := by rw [bv64_sw_toNat]; omega
      have hrn_lt : (BitVec.setWidth 64 o).toNat < ruleN.length := by rw [bv64_sw_toNat]; omega
      have hro_c : sCur.rule_off = s.rule_off := by rw [hsCur]
      have hrn_c : sCur.rule_n = s.rule_n := by rw [hsCur]
      have hpa_c : sCur.partner = s.partner := by rw [hsCur]
      have hgy_c : sCur.gsy = s.gsy := by rw [hsCur]
      have hgl_c : sCur.gcl = s.gcl := by rw [hsCur]
      have hgh_c : sCur.gch = s.gch := by rw [hsCur]
      have hrm_c : sCur.rs_m = s.rs_m := by rw [hsCur]
      have hrl_c : sCur.rs_l = s.rs_l := by rw [hsCur]
      have hrh_c : sCur.rs_h = s.rs_h := by rw [hsCur]
      have hrp_c : sCur.rs_pool = s.rs_pool := by rw [hsCur]
      rw [← hro_c, ← hrn_c] at hmCur
      c0_hsteps
      let ruleOff' := ruleOff.set o.toNat s.rs_n
      let ruleN' := ruleN.set o.toNat cnt
      have hm_fin : (arCtxMem cx sCur ⋆ array (t := i32) sCur.rule_off ruleOff' ⋆
          array (t := i32) sCur.rule_n ruleN' ⋆ array (t := i32) s.partner partnerArr ⋆
          array (t := i32) s.gsy gsy ⋆ array64 s.gcl gcl ⋆ array64 s.gch gch ⋆
          array (t := i32) s.rs_m rsMCur ⋆ array64 s.rs_l rsLCur ⋆ array64 s.rs_h rsHCur ⋆
          array (t := i32) s.rs_pool rsPoolCur ⋆ Rpad) m := by
        dsimp only [ruleOff', ruleN']
        rw [set_eq_of_eq (j := o.toNat) (w := s.rs_n) bv64_sw_toNat rfl,
          set_eq_of_eq (j := o.toNat) (w := cnt) bv64_sw_toNat rfl] at hm
        exact sep_cast hm (by ac_rfl)
      have hm_final : (arCtxMem cx sCur ⋆ array (t := i32) sCur.rule_off ruleOff' ⋆
          array (t := i32) sCur.rule_n ruleN' ⋆ array (t := i32) sCur.partner partnerArr ⋆
          array (t := i32) sCur.gsy gsy ⋆ array64 sCur.gcl gcl ⋆ array64 sCur.gch gch ⋆
          rsMem sCur rsMCur rsLCur rsHCur rsPoolCur ⋆ R) m := by
        rw [hpa_c, hgy_c, hgl_c, hgh_c, ← rsMem_repack hm_l hp_l,
          hrm_c, hrl_c, hrh_c, hrp_c]
        dsimp only [Rpad] at hm_fin
        exact sep_cast hm_fin (by ac_rfl)
      refine hQ true sCur ruleOff' ruleN' rsMCur rsLCur rsHCur rsPoolCur m
        hsn_cap hspt_cap hsCur (by simp [ruleOff']) (by simp [ruleN'])
        hm_l hl_l hh_l hp_l (fun _ => ⟨hTotCur, ?_, hSl, hRsSortedCur, fun σ hPart hRep hev => ?_⟩)
        hm_final
      · intro bd hSbRs hSbGsy k hk x hx
        by_cases hk_lt : k < s.rs_n.toNat
        · have hm_eq := (hpreM k hk_lt).1
          have hpool_eq : symListAt rsPoolCur (rsMCur.getD k 0#32).toNat =
              symListAt rsPool (rsM.getD k 0#32).toNat := by
            have h0 : rsPoolCur.getD (rsMCur.getD k 0#32).toNat 0#32 =
                rsPool.getD (rsM.getD k 0#32).toNat 0#32 := by
              rw [hm_eq]; exact hpreP (rsM.getD k 0#32).toNat (hRsOk k hk_lt).1.1
            simp only [symListAt, h0]
            apply List.map_congr_left
            intro r hr; rw [List.mem_range] at hr
            rw [hm_eq]
            exact congrArg BitVec.toNat
              (hpreP ((rsM.getD k 0#32).toNat + 1 + r) (by have := (hRsOk k hk_lt).1.2; omega))
          rw [hpool_eq] at hx
          exact hSbRs k hk_lt x hx
        · obtain ⟨idx, hidx, heq⟩ := hGsyMapCur k hk (Nat.le_of_not_lt hk_lt)
          rw [heq] at hx
          exact hSbGsy idx (by omega) x hx
      have hnout_c : sCur.modW = s.modW := by rw [hsCur]; rfl
      rw [hnout_c]
      refine rulesRep_install_done hsCur ho_lt hn16 (by simp [ruleOff']) (by simp [ruleN'])
        hm_l hl_l hh_l hp_l hsn_cap hspt_cap rfl hrsn_eq.symm (by omega)
        (fun k hk => (hSl k hk).1) (fun v hv hvo => ⟨?_, ?_⟩) ?_ ?_ hpreM hpreP hRep ?_ hev
      · dsimp only [ruleOff']; exact getD_set_ne ruleOff 0#32 _ hvo
      · dsimp only [ruleN']; exact getD_set_ne ruleN 0#32 _ hvo
      · dsimp only [ruleOff']; rw [d_getD_set_eq ruleOff 0#32 _ (by omega)]; simp
      · dsimp only [ruleN']; rw [d_getD_set_eq ruleN 0#32 _ (by omega)]; simp
      · rw [← hi_eq]; exact hPoly σ hPart
  · intro J hJ; c0_hsteps
    refine hJ n.toNat (0#32, 0#32, ⟨⟩) m
      ⟨Nat.zero_le _, Nat.le_refl _, Nat.sub_zero _, s, rsM, rsPool, rsL, rsH,
       ?_, rfl, Nat.le_refl _, hrsn_le, hrspt_le, rfl, rfl, rfl, rfl,
       fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hRsOk, hRsSorted, hTot,
       fun _ hk hge => absurd hk (Nat.not_lt_of_le hge), fun σ _ => ?_, hm0⟩
    · cases s; rfl
    · simp [polyEvalRange_zero, polyEval_zero]

/-! ## 4. Pure `ar_do_gate` Truth-Table & Monomial Helpers -/

theorem gate_cSig_two_mul (g : Aig) (ρ : Nat → Bool) (bindArr : List (BitVec 32))
    (v : Nat) : cSig g ρ bindArr (2 * v) = g.litVal ρ (bindArr.getD v 0#32).toNat := by
  simp [cSig, Nat.mul_div_right _ (by decide : 0 < 2), Nat.mul_mod_right]

theorem gate_mask6_and_all_testBit {j t : Nat} {all : BitVec 64}
    (hj : j < 6) (ht : t < 64) (hall : all.toNat.testBit t = true) :
    ((BitVec.ofNat 64 (xmask j) &&& all).toNat.testBit t) = t.testBit j := by
  rw [bv64_and_testBit _ _ ht, hall, Bool.and_true]
  have hxlt : xmask j < 2 ^ 64 := by
    rcases show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega with
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxlt, xmask_bit j t hj ht]

theorem gate_bv64_shr_and1_eq (v : BitVec 64) {t : Nat} (ht : t < 64) :
    ((v >>> BitVec.ofNat 64 t) &&& 1#64) = if v.toNat.testBit t then 1#64 else 0#64 := by
  have ht' : (BitVec.ofNat 64 t).toNat = t := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hsh : (v >>> BitVec.ofNat 64 t).toNat = v.toNat / 2 ^ t := by
    have h1 : (v >>> BitVec.ofNat 64 t).toNat = v.toNat >>> t := by simp [ht']
    rw [h1, Nat.shiftRight_eq_div_pow]
  have hb : v.toNat.testBit t = (v.toNat / 2 ^ t % 2 == 1) := by
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm 1, Nat.and_one_is_mod]
    simp
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, hsh, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, hb]
  by_cases h : v.toNat / 2 ^ t % 2 = 1
  · simp [h]
  · have h0 : v.toNat / 2 ^ t % 2 = 0 := by omega
    simp [h0]

theorem gate_coeff128_bit {nOut : Nat} (_hn : 1 ≤ nOut) (b : Bool) :
    coeff128 nOut (if b then 1#64 else 0#64) 0#64 = bv nOut b := by
  cases b <;> simp [coeff128, bv, show (0#64 : BitVec 64).toNat = 0 from rfl,
    show (1#64 : BitVec 64).toNat = 1 from rfl]

theorem gate_partner_no_both {a b : BitVec 64} {t : Nat}
    (hand : a &&& b = 0#64) (ht : t < 64) :
    ¬ (a.toNat.testBit t = true ∧ b.toNat.testBit t = true) := by
  intro ⟨ha, hb⟩
  have h1 := bv64_and_testBit a b ht
  rw [hand, show (0#64 : BitVec 64).toNat = 0 from rfl, Nat.zero_testBit, ha, hb] at h1
  cases h1

theorem gate_polyEval_step {nOut : Nat} {σ : Nat → Bool} {gsy : List (BitVec 32)}
    {gcl gch : List (BitVec 64)} {i : Nat} {sl sh : BitVec 64} (hi : i < 16)
    (hcur : coeff128 nOut sl sh = polyEval nOut σ gsy gsyMOff gcl gch i) :
    (coeff128 nOut sl sh +
      if monoValL σ (symListAt gsy (5 * i)) then
        coeff128 nOut (gcl.getD i 0#64) (gch.getD i 0#64)
      else 0#nOut) = polyEval nOut σ gsy gsyMOff gcl gch (i + 1) := by
  rw [polyEval, polyEvalRange_succ, Nat.zero_add, ← polyEval, ← hcur]
  simp only [termEval, gsyMOff_getD i hi]

theorem gate_monoValL_iff_one {σ : Nat → Bool} {gsy : List (BitVec 32)}
    {i mlen k2 : Nat} {one : Bool} (hmlen : mlen = (gsy.getD (5 * i) 0#32).toNat)
    (hend : one = false ∨ mlen < k2)
    (htrue : one = true → ∀ r < k2 - 1, σ (gsy.getD (5 * i + 1 + r) 0#32).toNat = true)
    (hfalse : one = false → ∃ r < mlen, σ (gsy.getD (5 * i + 1 + r) 0#32).toNat = false) :
    monoValL σ (symListAt gsy (5 * i)) = one := by
  cases one
  · obtain ⟨r, hr, hrf⟩ := hfalse rfl
    apply monoValL_false_of_mem _ hrf
    simp only [symListAt, ← hmlen, List.mem_map, List.mem_range]
    exact ⟨r, hr, rfl⟩
  · have hlt : mlen < k2 := hend.resolve_left (by decide)
    rw [monoValL_eq_decide, decide_eq_true_eq]
    intro x hx
    simp only [symListAt, ← hmlen, List.mem_map, List.mem_range] at hx
    rcases hx with ⟨r, hr, rfl⟩
    exact htrue rfl r (by omega)

theorem gate_ntt_bounds {nl : BitVec 32} (_h1 : 1 ≤ nl.toNat) (h6 : nl.toNat ≤ 6) :
    (1#32 <<< nl).toNat = 2 ^ nl.toNat ∧ 1 ≤ 2 ^ nl.toNat ∧ 2 ^ nl.toNat ≤ 64 := by
  have hpow : 2 ^ nl.toNat ≤ 64 := Nat.pow_le_pow_right (by decide) h6
  have hsh : (1#32 <<< nl).toNat = 2 ^ nl.toNat := by
    rw [bv_c0_toNat_shiftLeft_bv, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.one_mul,
      Nat.mod_eq_of_lt (by omega)]
  exact ⟨hsh, Nat.one_le_pow _ _ (by decide), hpow⟩

theorem gate_row_of_tOf (g : Aig) (ρ : Nat → Bool) {nl nin nout : Nat}
    (hnl1 : 1 ≤ nl) (hnl6 : nl ≤ 6) (expl : BitVec 32) (hnin_nl : expl = 0#32 → nin ≤ nl)
    (all : BitVec 64)
    (bindArr gInnet gOuts gLnode bs : List (BitVec 32)) (gLmask gTin gTto : List (BitVec 64))
    (hall : ∀ t < 2 ^ nl, all.toNat.testBit t = true)
    (hnode : ∀ j < nl, gLnode.getD j 0#32 = bs.getD j 0#32 >>> 1)
    (hmask : ∀ j < nl, gLmask.getD j 0#64 =
      (BitVec.ofNat 64 (xmask j) &&& all) ^^^
        (if bs.getD j 0#32 &&& 1#32 ≠ 0#32 then all else 0#64))
    (hbs0 : expl = 0#32 → ∀ j < nin,
      bs.getD j 0#32 = bindArr.getD (gInnet.getD j 0#32).toNat 0#32)
    (htin0 : expl = 0#32 → ∀ j < nin, gTin.getD j 0#64 = BitVec.ofNat 64 (xmask j) &&& all)
    (htin1 : expl ≠ 0#32 → ∀ j < nin, ∀ t < 64, all.toNat.testBit t = true →
      (∀ q < nl, (gLmask.getD q 0#64).toNat.testBit t = g.nodeVal ρ (gLnode.getD q 0#32).toNat) →
      (gTin.getD j 0#64).toNat.testBit t =
        g.litVal ρ (bindArr.getD (gInnet.getD j 0#32).toNat 0#32).toNat)
    (htto : ∀ o < nout, ∀ t < 64, all.toNat.testBit t = true →
      (∀ q < nl, (gLmask.getD q 0#64).toNat.testBit t = g.nodeVal ρ (gLnode.getD q 0#32).toNat) →
      (gTto.getD o 0#64).toNat.testBit t =
        g.litVal ρ (bindArr.getD (gOuts.getD o 0#32).toNat 0#32).toNat) :
    ∃ t < 2 ^ nl, t < 64 ∧
      (∀ j < nin, (gTin.getD j 0#64).toNat.testBit t =
        cSig g ρ bindArr (2 * (gInnet.getD j 0#32).toNat)) ∧
      (∀ o < nout, (gTto.getD o 0#64).toNat.testBit t =
        cSig g ρ bindArr (2 * (gOuts.getD o 0#32).toNat)) := by
  obtain ⟨ht, ht64, hallt, hlmask⟩ := gLmask_row_ok g ρ hnl6 all bs gLnode gLmask hall hnode hmask
  refine ⟨_, ht, ht64, fun j hj => ?_, fun o ho => ?_⟩
  · by_cases he : expl = 0#32
    · have hnin := hnin_nl he
      rw [htin0 he j hj, gate_mask6_and_all_testBit (by omega) ht64 hallt, tOf_bit]
      rw [d_getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range, hbs0 he j hj, gate_cSig_two_mul]
    · rw [htin1 he j hj _ ht64 hallt hlmask, gate_cSig_two_mul]
  · rw [htto o ho _ ht64 hallt hlmask, gate_cSig_two_mul]

theorem gate_dlit_step {Γ : LeanQbe.T.Env}
    (hDlit : ∀ xs m Q X, arDlitSpec xs m Q X → Γ "ar_dlit" [i64, i32, i32] [] xs m Q X)
    {pa : Arg Val i64} {ja na : Arg Val i32} {p : BitVec 64} {j neg : BitVec 32}
    {d : List (BitVec 64)} {F : Mem 64 → Prop} {rs : List Ty} {Q : Post rs} {X : XPost}
    {k : Tup Val [] → Expr Val Cont rs} {m : Mem 64}
    (hpa : pa.val = p) (hja : ja.val = j) (hna : na.val = neg)
    (hj : j.toNat < 4) (hd : d.length = 16) (hm : (array64 p d ⋆ F) m)
    (hk : ∀ d' m', d'.length = 16 → (array64 p d' ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call (as := [i64, i32, i32]) (bs := []) "ar_dlit" (pa, ja, na, ()) k) m := by
  apply wp_call_of_spec; dsimp only [vals]; rw [hpa, hja, hna]
  exact hDlit _ _ _ _
    ⟨d, F, by omega, hj, hm, fun d' m' hlen _ _ hm' => hk d' m' (hlen.trans hd) hm'⟩

theorem gate_dzero_step {Γ : LeanQbe.T.Env}
    (hDzero : ∀ xs m Q X, arDzeroSpec xs m Q X → Γ "ar_dzero" [i64] [] xs m Q X)
    {pa : Arg Val i64} {p : BitVec 64} {d : List (BitVec 64)} {F : Mem 64 → Prop}
    {rs : List Ty} {Q : Post rs} {X : XPost} {k : Tup Val [] → Expr Val Cont rs} {m : Mem 64}
    (hpa : pa.val = p) (hd : d.length = 16) (hm : (array64 p d ⋆ F) m)
    (hk : ∀ d' m', d'.length = 16 → (array64 p d' ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call (as := [i64]) (bs := []) "ar_dzero" (pa, ()) k) m := by
  apply wp_call_of_spec; dsimp only [vals]; rw [hpa]
  exact hDzero _ _ _ _
    ⟨d, F, by omega, hm, fun d' m' hlen _ _ _ hm' => hk d' m' (hlen.trans hd) hm'⟩

theorem gate_dmul_step {Γ : LeanQbe.T.Env}
    (hDmul : ∀ xs m Q X, arDmulSpec xs m Q X → Γ "ar_dmul" [i64, i64, i64] [] xs m Q X)
    {aa ba ca : Arg Val i64} {pa pb pc : BitVec 64} {a b c : List (BitVec 64)}
    {F : Mem 64 → Prop} {rs : List Ty} {Q : Post rs} {X : XPost}
    {k : Tup Val [] → Expr Val Cont rs} {m : Mem 64}
    (haa : aa.val = pa) (hba : ba.val = pb) (hca : ca.val = pc)
    (ha : a.length = 16) (hb : b.length = 16) (hc : c.length = 16)
    (hm : (array64 pa a ⋆ array64 pb b ⋆ array64 pc c ⋆ F) m)
    (hk : ∀ c' m', c'.length = 16 →
      (array64 pa a ⋆ array64 pb b ⋆ array64 pc c' ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call (as := [i64, i64, i64]) (bs := []) "ar_dmul" (aa, ba, ca, ()) k) m := by
  apply wp_call_of_spec; dsimp only [vals]; rw [haa, hba, hca]
  exact hDmul _ _ _ _ ⟨a, b, c, F, by omega, by omega, by omega, hm,
    fun c' m' hlen _ _ hm' => hk c' m' (hlen.trans hc) hm'⟩

theorem gate_daxpy_step {Γ : LeanQbe.T.Env}
    (hDaxpy : ∀ xs m Q X, arDaxpySpec xs m Q X → Γ "ar_daxpy" [i64, i64, i64] [] xs m Q X)
    {ya ka xa : Arg Val i64} {py kv px : BitVec 64} {y x : List (BitVec 64)}
    {F : Mem 64 → Prop} {rs : List Ty} {Q : Post rs} {X : XPost}
    {k : Tup Val [] → Expr Val Cont rs} {m : Mem 64}
    (hya : ya.val = py) (hka : ka.val = kv) (hxa : xa.val = px)
    (hy : y.length = 16) (hx : x.length = 16)
    (hm : (array64 py y ⋆ array64 px x ⋆ F) m)
    (hk : ∀ y' m', y'.length = 16 →
      (array64 py y' ⋆ array64 px x ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call (as := [i64, i64, i64]) (bs := []) "ar_daxpy" (ya, ka, xa, ()) k) m := by
  apply wp_call_of_spec; dsimp only [vals]; rw [hya, hka, hxa]
  exact hDaxpy _ _ _ _ ⟨y, x, F, by omega, by omega, hm,
    fun y' m' hlen _ _ _ hm' => hk y' m' (hlen.trans hy) hm'⟩

theorem gate_ttsim_step {Γ : LeanQbe.T.Env}
    (hTtsim : ∀ xs m Q X, arTtsimSpec xs m Q X →
      Γ "ar_ttsim" [i64, i32, i32, i64] [.bool, i64] xs m Q X)
    {cxa : Arg Val i64} {lita nla : Arg Val i32} {alla : Arg Val i64}
    {cx : BitVec 64} {lit nl : BitVec 32} {all : BitVec 64}
    {s : ArCtxState} {g : Aig} {rhs0 rhs1 olit stkN stkP memoN gsy : List (BitVec 32)}
    {memoV dense gcl gch : List (BitVec 64)} {F : Mem 64 → Prop}
    {rs : List Ty} {Q : Post rs} {X : XPost}
    {k : Tup Val [.bool, i64] → Expr Val Cont rs} {m : Mem 64}
    (hcxa : cxa.val = cx) (hlita : lita.val = lit) (hnla : nla.val = nl) (halla : alla.val = all)
    (hsI : s.I.toNat = g.I) (hsM : s.M.toNat = g.M) (hAig : AigRep g rhs0 rhs1 olit)
    (hnl6 : nl.toNat ≤ 6) (hsn : 160 ≤ stkN.length) (hsp : 160 ≤ stkP.length)
    (hmn : 64 ≤ memoN.length) (hmv : 64 ≤ memoV.length)
    (hm : (arCtxMem cx s ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
      gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆ F) m)
    (hk : ∀ ok tv stkN' stkP' memoN' memoV' m',
      stkN'.length = stkN.length → stkP'.length = stkP.length →
      memoN'.length = memoN.length → memoV'.length = memoV.length →
      (ok = true → ∀ t ρ, t < 64 → all.toNat.testBit t = true →
        (∀ q < nl.toNat, (s.g_lmask.getD q 0#64).toNat.testBit t =
          g.nodeVal ρ (s.g_lnode.getD q 0#32).toNat) →
        tv.toNat.testBit t = g.litVal ρ lit.toNat) →
      (arCtxMem cx s ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
        gateScratchMem s stkN' stkP' memoN' memoV' dense gsy gcl gch ⋆ F) m' →
      wp Γ Q X (k (ok, tv, ())) m') :
    wp Γ Q X (.call (as := [i64, i32, i32, i64]) (bs := [.bool, i64])
      "ar_ttsim" (cxa, lita, nla, alla, ()) k) m := by
  apply wp_call_of_spec; dsimp only [vals]; rw [hcxa, hlita, hnla, halla]
  exact hTtsim _ _ _ _ ⟨s, g, rhs0, rhs1, olit, stkN, stkP, memoN, memoV, dense, gsy, gcl, gch, F,
    hsI, hsM, hAig, hnl6, hsn, hsp, hmn, hmv, hm, fun ok tv a b c d m' h1 h2 h3 h4 hok hm' =>
      hk ok tv a b c d m' h1 h2 h3 h4 hok hm'⟩

end

end LeanQbe.T.Examples.Arisca.Proof
