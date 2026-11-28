/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Src.Poly
public import LeanQbe.T.Examples.Arisca.Proof.Poly0
public import LeanQbe.T.Examples.Arisca.Proof.Poly1Base

/-!
# ARiSCA Poly2 WP Specifications (`Arisca.Proof.Poly2Spec`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP contracts for the remaining `6` functions of
`LeanQbe.T.Examples.Arisca.Src.Poly`:
- `ar_apply` (`arApplySpec`)
- `ar_add_q` (`arAddQSpec`)
- `ar_build_sp0` (`arBuildSp0Spec`)
- `ar_load_rule` (`arLoadRuleSpec`)
- `ar_store_rule` (`arStoreRuleSpec`)
- `ar_build_R` (`arBuildRSpec`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Poly

@[expose] public section

/-- Expected symbol list for `ar_add_q(cx, len, s0, s1, l, h)`. -/
def addQSyms (len s0 s1 : Nat) : List Nat :=
  if len = 0 then [] else if len = 1 then [s0] else [s0, s1]

/-- WP specification for `ar_add_q(cx, len, s0, s1, l, h)`. -/
def arAddQSpec : Spec [i64, i32, i32, i32, i64, i64] [.bool] :=
  fun ⟨cx, len, s0, s1, l, h, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (tm0 tm1 : List (BitVec 32))
      (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)) (pool0 pool1 : List (BitVec 32))
      (qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
      (partnerArr : List (BitVec 32)) (Valid : (Nat → Bool) → Prop) (R : Mem 64 → Prop),
      let srcPool := if s.pc.toNat = 0 then pool0 else pool1
      s.pc.toNat < 2 ∧ s.tc.toNat < 2 ∧
      s.qn.toNat ≤ s.qcap.toNat ∧ s.qcap.toNat + 16 < 2 ^ 32 ∧
      s.ptop.toNat ≤ s.pcap.toNat ∧ s.pcap.toNat < 2 ^ 32 ∧
      s.n_nets.toNat ≤ 0x3FFFFFFF ∧ 2 * s.n_nets.toNat < 2 ^ 32 ∧
      s.pcap.toNat ≤ pool0.length ∧ s.pcap.toNat ≤ pool1.length ∧
      s.qcap.toNat ≤ qm.length ∧ s.qcap.toNat ≤ qs.length ∧
      s.qcap.toNat ≤ ql.length ∧ s.qcap.toNat ≤ qh.length ∧
      MasksOk s.n_out.toNat s.mlo s.mhi ∧
      (∃ σ₀, Valid σ₀) ∧
      (∀ σ, Valid σ → PartnerRep σ s.n_nets.toNat partnerArr) ∧
      (∀ i < s.qn.toNat,
        MonoSliceOk srcPool (qm.getD i 0#32).toNat s.ptop.toNat ∧
        (srcPool.getD (qm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      (∀ i < s.qn.toNat, MonoSorted srcPool (qm.getD i 0#32).toNat) ∧
      SigOk srcPool qm qs s.qn.toNat ∧
      (len.toNat = 2 → s0.toNat < s1.toNat) ∧
      monoTotalWords srcPool qm s.qn.toNat ≤ s.ptop.toNat ∧
      (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
        tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆
        array64 s.qh qh ⋆ R) m ∧
      (∀ (ok : Bool) (s' : ArCtxState) (pool0' pool1' qm' : List (BitVec 32))
          (qs' ql' qh' : List (BitVec 64)) (m' : Mem 64),
        let dstPool := if s.pc.toNat = 0 then pool0' else pool1'
        s'.qn.toNat ≤ s.qcap.toNat → s'.ptop.toNat ≤ s.pcap.toNat →
        s' = { s with qn := s'.qn, ptop := s'.ptop } →
        pool0'.length = pool0.length → pool1'.length = pool1.length →
        qm'.length = qm.length → qs'.length = qs.length →
        ql'.length = ql.length → qh'.length = qh.length →
        (if s.pc.toNat = 0 then pool1' = pool1 else pool0' = pool0) →
        (∀ idx < s.ptop.toNat, dstPool.getD idx 0#32 = srcPool.getD idx 0#32) →
        (∀ i < s.qn.toNat, qm'.getD i 0#32 = qm.getD i 0#32 ∧
          ql'.getD i 0#64 = ql.getD i 0#64 ∧ qh'.getD i 0#64 = qh.getD i 0#64) →
        (ok = true →
          (∀ i < s'.qn.toNat,
            MonoSliceOk dstPool (qm'.getD i 0#32).toNat s'.ptop.toNat ∧
            (dstPool.getD (qm'.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
          (∀ i < s'.qn.toNat, MonoSorted dstPool (qm'.getD i 0#32).toNat) ∧
          SigOk dstPool qm' qs' s'.qn.toNat ∧
          monoTotalWords dstPool qm' s'.qn.toNat ≤ s'.ptop.toNat ∧
          (∀ σ, Valid σ →
            polyEval s.n_out.toNat σ dstPool qm' ql' qh' s'.qn.toNat =
              polyEval s.n_out.toNat σ srcPool qm ql qh s.qn.toNat +
                (if monoValL σ (addQSyms len.toNat s0.toNat s1.toNat)
                 then coeff128 s.n_out.toNat l h else 0#(s.n_out.toNat)))) →
        (arCtxMem cx s' ⋆ array (t := i32) s'.partner partnerArr ⋆
          tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0' pool1' ⋆
          array (t := i32) s'.qm qm' ⋆ array64 s'.qs qs' ⋆ array64 s'.ql ql' ⋆
          array64 s'.qh qh' ⋆ R) m' →
        Q (ok, ⟨⟩) m')

/-- WP specification for `ar_build_sp0(cx)` (universal over AIG assignments `ρ`). -/
def arBuildSp0Spec : Spec [i64] [.bool] :=
  fun ⟨cx, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (g : Aig) (bindArr inNetArr outRefArr partnerArr : List (BitVec 32))
      (tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
      (pool0 pool1 qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
      (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
      (R : Mem 64 → Prop),
      s.pc.toNat < 2 ∧ s.tc.toNat < 2 ∧
      s.tcap.toNat < 2 ^ 30 ∧ 16 ≤ s.qcap.toNat ∧ s.qcap.toNat + 16 < 2 ^ 32 ∧
      s.pcap.toNat < 2 ^ 32 ∧ s.n_nets.toNat ≤ 0x3FFFFFFF ∧ 2 * s.n_nets.toNat < 2 ^ 32 ∧
      (s.spec = 0#32 ∨ s.spec = 1#32) ∧
      s.tcap.toNat ≤ tm0.length ∧ s.tcap.toNat ≤ tm1.length ∧
      s.tcap.toNat ≤ ts0.length ∧ s.tcap.toNat ≤ tl0.length ∧ s.tcap.toNat ≤ th0.length ∧
      s.tcap.toNat ≤ ts1.length ∧ s.tcap.toNat ≤ tl1.length ∧ s.tcap.toNat ≤ th1.length ∧
      s.pcap.toNat ≤ pool0.length ∧ s.pcap.toNat ≤ pool1.length ∧
      s.qcap.toNat ≤ qm.length ∧ s.qcap.toNat ≤ qs.length ∧
      s.qcap.toNat ≤ ql.length ∧ s.qcap.toNat ≤ qh.length ∧
      s.qcap.toNat ≤ ix.length ∧ s.qcap.toNat ≤ ix2.length ∧ ix.length = ix2.length ∧
      MasksOk s.n_out.toNat s.mlo s.mhi ∧
      BindRep s g bindArr inNetArr outRefArr ∧
      (∀ ρ : Nat → Bool, PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr) ∧
      (arCtxMem cx s ⋆ array (t := i32) s.bind bindArr ⋆ array (t := i32) s.in_net inNetArr ⋆
        array (t := i32) s.out_ref outRefArr ⋆ array (t := i32) s.partner partnerArr ⋆
        tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m ∧
      (∀ (ok : Bool) (s' : ArCtxState) (tm0' tm1' : List (BitVec 32))
          (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64))
          (pool0' pool1' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64))
          (ix' ix2' : List (BitVec 32)) (m' : Mem 64),
        let dstPool := if s'.pc.toNat = 0 then pool0' else pool1'
        let dstTm := if s'.tc.toNat = 0 then tm0' else tm1'
        let dstTs := if s'.tc.toNat = 0 then ts0' else ts1'
        let dstTl := if s'.tc.toNat = 0 then tl0' else tl1'
        let dstTh := if s'.tc.toNat = 0 then th0' else th1'
        s'.pc.toNat < 2 → s'.tc.toNat < 2 →
        s'.tn.toNat ≤ s.tcap.toNat → s'.ptop.toNat ≤ s.pcap.toNat → s'.qn.toNat ≤ s.qcap.toNat →
        s' = { s with
          tc := s'.tc, tn := s'.tn, ptop := s'.ptop, qn := s'.qn, ix := s'.ix, ix2 := s'.ix2 } →
        tm0'.length = tm0.length → tm1'.length = tm1.length →
        ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
        ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
        pool0'.length = pool0.length → pool1'.length = pool1.length →
        qm'.length = qm.length → qs'.length = qs.length →
        ql'.length = ql.length → qh'.length = qh.length →
        ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧
          ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
         (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧
          ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
        (ok = true →
          (∀ i < s'.tn.toNat,
            MonoSliceOk dstPool (dstTm.getD i 0#32).toNat s'.ptop.toNat ∧
            (dstPool.getD (dstTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
          (∀ i < s'.tn.toNat, MonoSorted dstPool (dstTm.getD i 0#32).toNat) ∧
          SigOk dstPool dstTm dstTs s'.tn.toNat ∧
          monoTotalWords dstPool dstTm s'.tn.toNat ≤ s'.ptop.toNat ∧
          (∀ ρ : Nat → Bool,
            polyEval s.n_out.toNat (cSig g ρ bindArr) dstPool dstTm dstTl dstTh s'.tn.toNat =
              BitVec.ofNat s.n_out.toNat (outWord g ρ) -
                BitVec.ofInt s.n_out.toNat (inWord (decide (s.spec = 1#32)) (g.I / 2) ρ 0) *
                  BitVec.ofInt s.n_out.toNat
                    (inWord (decide (s.spec = 1#32)) (g.I / 2) ρ (g.I / 2)))) →
        (arCtxMem cx s' ⋆ array (t := i32) s'.bind bindArr ⋆ array (t := i32) s'.in_net inNetArr ⋆
          array (t := i32) s'.out_ref outRefArr ⋆ array (t := i32) s'.partner partnerArr ⋆
          tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆
          qMem s' qm' qs' ql' qh' ix' ix2' bx vqOff vq vqSkip ⋆ R) m' →
        Q (ok, ⟨⟩) m')

/-- WP specification for `ar_load_rule(cx, v)`. -/
def arLoadRuleSpec : Spec [i64, i32] [.bool] :=
  fun ⟨cx, v, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (ruleOff ruleN rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64))
      (rsPool tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
      (pool0 pool1 : List (BitVec 32)) (Valid : (Nat → Bool) → Prop) (R : Mem 64 → Prop),
      s.pc.toNat < 2 ∧ s.tc.toNat < 2 ∧
      v.toNat < s.n_nets.toNat ∧ ruleN.getD v.toNat 0#32 ≠ cNone32 ∧
      s.tcap.toNat < 2 ^ 30 ∧ s.pcap.toNat < 2 ^ 32 ∧ s.rs_pcap.toNat < 2 ^ 32 ∧
      s.tcap.toNat ≤ tm0.length ∧ s.tcap.toNat ≤ tm1.length ∧
      s.tcap.toNat ≤ ts0.length ∧ s.tcap.toNat ≤ tl0.length ∧ s.tcap.toNat ≤ th0.length ∧
      s.tcap.toNat ≤ ts1.length ∧ s.tcap.toNat ≤ tl1.length ∧ s.tcap.toNat ≤ th1.length ∧
      s.pcap.toNat ≤ pool0.length ∧ s.pcap.toNat ≤ pool1.length ∧
      (∃ σ₀, Valid σ₀) ∧
      (∀ σ, Valid σ → RulesRep s.n_out.toNat σ s ruleOff ruleN rsM rsL rsH rsPool) ∧
      RulesSorted rsPool rsM s.rs_n.toNat ∧
      (∀ i < s.rs_n.toNat, (rsPool.getD (rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
        rsMem s rsM rsL rsH rsPool ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ R) m ∧
      (∀ (ok : Bool) (s' : ArCtxState) (tm0' tm1' : List (BitVec 32))
          (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64)) (pool0' pool1' : List (BitVec 32))
          (m' : Mem 64),
        let dstPool := if s'.pc.toNat = 0 then pool0' else pool1'
        let dstTm := if s'.tc.toNat = 0 then tm0' else tm1'
        let dstTs := if s'.tc.toNat = 0 then ts0' else ts1'
        let dstTl := if s'.tc.toNat = 0 then tl0' else tl1'
        let dstTh := if s'.tc.toNat = 0 then th0' else th1'
        s'.tn.toNat ≤ s.tcap.toNat → s'.ptop.toNat ≤ s.pcap.toNat →
        s' = { s with tn := s'.tn, ptop := s'.ptop, qn := 0#32 } →
        tm0'.length = tm0.length → tm1'.length = tm1.length →
        ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
        ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
        pool0'.length = pool0.length → pool1'.length = pool1.length →
        (ok = true →
          (∀ i < s'.tn.toNat,
            MonoSliceOk dstPool (dstTm.getD i 0#32).toNat s'.ptop.toNat ∧
            (dstPool.getD (dstTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
          (∀ i < s'.tn.toNat, MonoSorted dstPool (dstTm.getD i 0#32).toNat) ∧
          SigOk dstPool dstTm dstTs s'.tn.toNat ∧
          monoTotalWords dstPool dstTm s'.tn.toNat ≤ s'.ptop.toNat ∧
          (∀ bd : Nat, SymsBound rsPool rsM s.rs_n.toNat bd →
            SymsBound dstPool dstTm s'.tn.toNat bd) ∧
          (∀ σ, Valid σ →
            polyEval s.n_out.toNat σ dstPool dstTm dstTl dstTh s'.tn.toNat =
              bv s.n_out.toNat (σ (2 * v.toNat)))) →
        (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆ array (t := i32) s'.rule_n ruleN ⋆
          rsMem s' rsM rsL rsH rsPool ⋆
          tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆ R) m' →
        Q (ok, ⟨⟩) m')

/-- WP specification for `ar_store_rule(cx, v)`. -/
def arStoreRuleSpec : Spec [i64, i32] [.bool] :=
  fun ⟨cx, v, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (ruleOff ruleN rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64))
      (rsPool tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
      (pool0 pool1 : List (BitVec 32)) (Valid : (Nat → Bool) → Prop) (R : Mem 64 → Prop),
      let srcPool := if s.pc.toNat = 0 then pool0 else pool1
      let srcTm := if s.tc.toNat = 0 then tm0 else tm1
      let srcTl := if s.tc.toNat = 0 then tl0 else tl1
      let srcTh := if s.tc.toNat = 0 then th0 else th1
      s.pc.toNat < 2 ∧ s.tc.toNat < 2 ∧
      v.toNat < s.n_nets.toNat ∧ s.tn.toNat ≤ s.tcap.toNat ∧ s.tcap.toNat < 2 ^ 30 ∧
      s.pcap.toNat < 2 ^ 32 ∧ s.rs_cap.toNat < 2 ^ 30 ∧ s.rs_pcap.toNat < 2 ^ 32 ∧
      s.tcap.toNat ≤ tm0.length ∧ s.tcap.toNat ≤ tm1.length ∧
      s.tcap.toNat ≤ tl0.length ∧ s.tcap.toNat ≤ th0.length ∧
      s.tcap.toNat ≤ tl1.length ∧ s.tcap.toNat ≤ th1.length ∧
      s.pcap.toNat ≤ pool0.length ∧ s.pcap.toNat ≤ pool1.length ∧
      (∃ σ₀, Valid σ₀) ∧
      (∀ σ, Valid σ → RulesRep s.n_out.toNat σ s ruleOff ruleN rsM rsL rsH rsPool) ∧
      RulesSorted rsPool rsM s.rs_n.toNat ∧
      monoTotalWords rsPool rsM s.rs_n.toNat ≤ s.rs_ptop.toNat ∧
      (∀ i < s.rs_n.toNat, (rsPool.getD (rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      (∀ i < s.tn.toNat,
        MonoSliceOk srcPool (srcTm.getD i 0#32).toNat srcPool.length ∧
        (srcPool.getD (srcTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      (∀ i < s.tn.toNat, MonoSorted srcPool (srcTm.getD i 0#32).toNat) ∧
      monoTotalWords srcPool srcTm s.tn.toNat ≤ s.pcap.toNat ∧
      (∀ σ, Valid σ →
        polyEval s.n_out.toNat σ srcPool srcTm srcTl srcTh s.tn.toNat =
          bv s.n_out.toNat (σ (2 * v.toNat))) ∧
      (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
        rsMem s rsM rsL rsH rsPool ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ R) m ∧
      (∀ (ok : Bool) (s' : ArCtxState) (ruleOff' ruleN' rsM' : List (BitVec 32))
          (rsL' rsH' : List (BitVec 64)) (rsPool' : List (BitVec 32)) (m' : Mem 64),
        s'.rs_n.toNat ≤ s.rs_cap.toNat → s'.rs_ptop.toNat ≤ s.rs_pcap.toNat →
        s' = { s with rs_n := s'.rs_n, rs_ptop := s'.rs_ptop } →
        ruleOff'.length = ruleOff.length → ruleN'.length = ruleN.length →
        rsM'.length = rsM.length → rsL'.length = rsL.length →
        rsH'.length = rsH.length → rsPool'.length = rsPool.length →
        (ok = true →
          (∀ σ, Valid σ → RulesRep s'.n_out.toNat σ s' ruleOff' ruleN' rsM' rsL' rsH' rsPool') ∧
          RulesSorted rsPool' rsM' s'.rs_n.toNat ∧
          monoTotalWords rsPool' rsM' s'.rs_n.toNat ≤ s'.rs_ptop.toNat ∧
          (∀ bd : Nat, SymsBound rsPool rsM s.rs_n.toNat bd →
            SymsBound srcPool srcTm s.tn.toNat bd →
            SymsBound rsPool' rsM' s'.rs_n.toNat bd) ∧
          (∀ i < s'.rs_n.toNat,
            (rsPool'.getD (rsM'.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)) →
        (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff' ⋆
          array (t := i32) s'.rule_n ruleN' ⋆ rsMem s' rsM' rsL' rsH' rsPool' ⋆
          tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ R) m' →
        Q (ok, ⟨⟩) m')

/-- WP specification for `ar_apply(cx, s)`. -/
def arApplySpec : Spec [i64, i32] [.bool] :=
  fun ⟨cx, sym, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (tm0 tm1 : List (BitVec 32))
      (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)) (pool0 pool1 : List (BitVec 32))
      (qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
      (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
      (partnerArr curRm : List (BitVec 32)) (curRl curRh : List (BitVec 64))
      (curRp : List (BitVec 32)) (Valid : (Nat → Bool) → Prop) (R : Mem 64 → Prop),
      let srcPool := if s.pc.toNat = 0 then pool0 else pool1
      let srcTm := if s.tc.toNat = 0 then tm0 else tm1
      let srcTs := if s.tc.toNat = 0 then ts0 else ts1
      let srcTl := if s.tc.toNat = 0 then tl0 else tl1
      let srcTh := if s.tc.toNat = 0 then th0 else th1
      s.pc.toNat < 2 ∧ s.tc.toNat < 2 ∧
      s.tn.toNat ≤ s.tcap.toNat ∧ s.tcap.toNat < 2 ^ 30 ∧
      16 ≤ s.qcap.toNat ∧ s.qcap.toNat + 16 < 2 ^ 32 ∧
      s.ptop.toNat ≤ s.pcap.toNat ∧ s.pcap.toNat < 2 ^ 32 ∧
      s.n_nets.toNat ≤ 0x3FFFFFFF ∧ 2 * s.n_nets.toNat < 2 ^ 32 ∧
      s.tcap.toNat ≤ tm0.length ∧ s.tcap.toNat ≤ tm1.length ∧
      s.tcap.toNat ≤ ts0.length ∧ s.tcap.toNat ≤ tl0.length ∧ s.tcap.toNat ≤ th0.length ∧
      s.tcap.toNat ≤ ts1.length ∧ s.tcap.toNat ≤ tl1.length ∧ s.tcap.toNat ≤ th1.length ∧
      s.pcap.toNat ≤ pool0.length ∧ s.pcap.toNat ≤ pool1.length ∧
      s.qcap.toNat ≤ qm.length ∧ s.qcap.toNat ≤ qs.length ∧
      s.qcap.toNat ≤ ql.length ∧ s.qcap.toNat ≤ qh.length ∧
      s.qcap.toNat ≤ ix.length ∧ s.qcap.toNat ≤ ix2.length ∧
      s.tcap.toNat ≤ bx.length ∧ s.qcap.toNat ≤ bx.length ∧ s.qcap.toNat + 1 ≤ vqOff.length ∧
      s.pcap.toNat ≤ vq.length ∧ s.qcap.toNat ≤ vqSkip.length ∧
      MasksOk s.n_out.toNat s.mlo s.mhi ∧
      (∃ σ₀, Valid σ₀) ∧
      (∀ σ, Valid σ → PartnerRep σ s.n_nets.toNat partnerArr) ∧
      (∀ σ, Valid σ → CurRRep s.n_out.toNat σ s.cur_nr.toNat sym.toNat curRm curRl curRh curRp) ∧
      (∀ r < s.cur_nr.toNat, MonoSorted curRp (curRm.getD r 0#32).toNat) ∧
      (∀ r < s.cur_nr.toNat, (curRp.getD (curRm.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      monoTotalWords curRp curRm s.cur_nr.toNat ≤ 4000000000 ∧
      (∀ i < s.tn.toNat,
        MonoSliceOk srcPool (srcTm.getD i 0#32).toNat s.ptop.toNat ∧
        (srcPool.getD (srcTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      (∀ i < s.tn.toNat, MonoSorted srcPool (srcTm.getD i 0#32).toNat) ∧
      SigOk srcPool srcTm srcTs s.tn.toNat ∧
      monoTotalWords srcPool srcTm s.tn.toNat ≤ s.ptop.toNat ∧
      (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
        array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
        array (t := i32) s.cur_rp curRp ⋆
        tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m ∧
      (∀ (ok : Bool) (s' : ArCtxState) (tm0' tm1' : List (BitVec 32))
          (ts0' tl0' th0' ts1' tl1' th1' : List (BitVec 64))
          (pool0' pool1' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64))
          (ix' ix2' bx' vqOff' vq' : List (BitVec 32)) (vqSkip' : List (BitVec 8))
          (m' : Mem 64),
        let dstPool := if s'.pc.toNat = 0 then pool0' else pool1'
        let dstTm := if s'.tc.toNat = 0 then tm0' else tm1'
        let dstTs := if s'.tc.toNat = 0 then ts0' else ts1'
        let dstTl := if s'.tc.toNat = 0 then tl0' else tl1'
        let dstTh := if s'.tc.toNat = 0 then th0' else th1'
        s'.pc.toNat < 2 → s'.tc.toNat < 2 →
        s'.ptop.toNat ≤ s.pcap.toNat → s'.tn.toNat ≤ s.tcap.toNat →
        s' = { s with
          tc := s'.tc, tn := s'.tn, pc := s'.pc, ptop := s'.ptop,
          qn := s'.qn, ix := s'.ix, ix2 := s'.ix2 } →
        tm0'.length = tm0.length → tm1'.length = tm1.length →
        ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
        ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
        pool0'.length = pool0.length → pool1'.length = pool1.length →
        qm'.length = qm.length → qs'.length = qs.length →
        ql'.length = ql.length → qh'.length = qh.length →
        ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧
          ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
         (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧
          ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
        bx'.length = bx.length → vqOff'.length = vqOff.length →
        vq'.length = vq.length → vqSkip'.length = vqSkip.length →
        (ok = true →
          (∀ i < s'.tn.toNat,
            MonoSliceOk dstPool (dstTm.getD i 0#32).toNat s'.ptop.toNat ∧
            (dstPool.getD (dstTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
          (∀ i < s'.tn.toNat, MonoSorted dstPool (dstTm.getD i 0#32).toNat) ∧
          SigOk dstPool dstTm dstTs s'.tn.toNat ∧
          monoTotalWords dstPool dstTm s'.tn.toNat ≤ s'.ptop.toNat ∧
          (∀ bd : Nat, SymsBound srcPool srcTm s.tn.toNat bd →
            SymsBound curRp curRm s.cur_nr.toNat bd →
            SymsBound dstPool dstTm s'.tn.toNat bd) ∧
          (∀ σ, Valid σ →
            polyEval s.n_out.toNat σ dstPool dstTm dstTl dstTh s'.tn.toNat =
              polyEval s.n_out.toNat σ srcPool srcTm srcTl srcTh s.tn.toNat)) →
        (arCtxMem cx s' ⋆ array (t := i32) s'.partner partnerArr ⋆
          array (t := i32) s'.cur_rm curRm ⋆ array64 s'.cur_rl curRl ⋆
          array64 s'.cur_rh curRh ⋆ array (t := i32) s'.cur_rp curRp ⋆
          tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0' pool1' ⋆
          qMem s' qm' qs' ql' qh' ix' ix2' bx' vqOff' vq' vqSkip' ⋆ R) m' →
        Q (ok, ⟨⟩) m')

/-- WP specification for `ar_build_R(cx, v)`. -/
def arBuildRSpec : Spec [i64, i32] [.bool] :=
  fun ⟨cx, v, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (ruleOff ruleN rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64))
      (rsPool : List (BitVec 32)) (flippedArr : List (BitVec 8))
      (rm : List (BitVec 32)) (rl rh : List (BitVec 64))
      (rm2 : List (BitVec 32)) (rl2 rh2 : List (BitVec 64))
      (rpool ix ix2 : List (BitVec 32)) (Valid : (Nat → Bool) → Prop) (R : Mem 64 → Prop),
      v.toNat < s.n_nets.toNat ∧ ruleN.getD v.toNat 0#32 ≠ cNone32 ∧
      s.n_nets.toNat ≤ 0x3FFFFFFF ∧ s.n_nets.toNat ≤ flippedArr.length ∧
      16 ≤ s.qcap.toNat ∧ s.qcap.toNat + 16 < 2 ^ 32 ∧
      s.rcap.toNat ≤ s.qcap.toNat ∧ s.rpcap.toNat < 2 ^ 32 ∧
      s.rs_cap.toNat < 2 ^ 30 ∧ s.rs_pcap.toNat < 2 ^ 32 ∧
      s.rcap.toNat ≤ rm.length ∧ s.rcap.toNat ≤ rl.length ∧ s.rcap.toNat ≤ rh.length ∧
      s.rcap.toNat ≤ rm2.length ∧ s.rcap.toNat ≤ rl2.length ∧ s.rcap.toNat ≤ rh2.length ∧
      s.rpcap.toNat ≤ rpool.length ∧ s.qcap.toNat ≤ ix.length ∧ s.qcap.toNat ≤ ix2.length ∧
      ix.length = ix2.length ∧
      MasksOk s.n_out.toNat s.mlo s.mhi ∧
      (∃ σ₀, Valid σ₀) ∧
      (∀ σ, Valid σ →
        (∀ w < s.n_nets.toNat, σ (2 * w + 1) = !(σ (2 * w))) ∧
        RulesRep s.n_out.toNat σ s ruleOff ruleN rsM rsL rsH rsPool) ∧
      RulesSorted rsPool rsM s.rs_n.toNat ∧
      (∀ i < s.rs_n.toNat, (rsPool.getD (rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      monoTotalWords rsPool rsM s.rs_n.toNat ≤ s.rs_ptop.toNat ∧
      SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat ∧
      (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
        array (t := i8) s.flipped flippedArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
        rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ array (t := i32) s.ix ix ⋆
        array (t := i32) s.ix2 ix2 ⋆ R) m ∧
      (∀ (ok : Bool) (s' : ArCtxState)
          (rm' : List (BitVec 32)) (rl' rh' : List (BitVec 64))
          (rm2' : List (BitVec 32)) (rl2' rh2' : List (BitVec 64))
          (rpool' ix' ix2' : List (BitVec 32)) (m' : Mem 64),
        s' = { s with
          cur_rm := s'.cur_rm, cur_rl := s'.cur_rl, cur_rh := s'.cur_rh,
          cur_rp := s'.cur_rp, cur_nr := s'.cur_nr } →
        rm'.length = rm.length → rl'.length = rl.length → rh'.length = rh.length →
        rm2'.length = rm2.length → rl2'.length = rl2.length → rh2'.length = rh2.length →
        rpool'.length = rpool.length → ix'.length = ix.length → ix2'.length = ix2.length →
        (ok = true →
          let sym := if flippedArr.getD v.toNat 0#8 ≠ 0#8 then 2 * v.toNat + 1 else 2 * v.toNat
          let off := (ruleOff.getD v.toNat 0#32).toNat
          (flippedArr.getD v.toNat 0#8 = 0#8 ∧
            s'.cur_rm = s.rs_m + BitVec.ofNat 64 (4 * off) ∧
            s'.cur_rl = s.rs_l + BitVec.ofNat 64 (8 * off) ∧
            s'.cur_rh = s.rs_h + BitVec.ofNat 64 (8 * off) ∧
            s'.cur_rp = s.rs_pool ∧ s'.cur_nr = ruleN.getD v.toNat 0#32) ∨
          (s'.cur_rm = s.rm2 ∧ s'.cur_rl = s.rl2 ∧ s'.cur_rh = s.rh2 ∧
            s'.cur_rp = s.rpool ∧ s'.cur_nr.toNat ≤ s.rcap.toNat ∧
            (∀ σ, Valid σ →
              CurRRep s.n_out.toNat σ s'.cur_nr.toNat sym rm2' rl2' rh2' rpool') ∧
            (∀ r < s'.cur_nr.toNat, MonoSorted rpool' (rm2'.getD r 0#32).toNat) ∧
            (∀ r < s'.cur_nr.toNat,
              (rpool'.getD (rm2'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
            monoTotalWords rpool' rm2' s'.cur_nr.toNat ≤ s.rpcap.toNat)) →
        (arCtxMem cx s' ⋆ array (t := i32) s'.rule_off ruleOff ⋆ array (t := i32) s'.rule_n ruleN ⋆
          array (t := i8) s'.flipped flippedArr ⋆ rsMem s' rsM rsL rsH rsPool ⋆
          rMem s' rm' rl' rh' rm2' rl2' rh2' rpool' ⋆ array (t := i32) s'.ix ix' ⋆
          array (t := i32) s'.ix2 ix2' ⋆ R) m' →
        Q (ok, ⟨⟩) m')

end

public section

/-- Universal wrapper lifting `arMvanishSpec` to any non-empty family
`Valid : (Nat → Bool) → Prop`. -/
theorem arMvanish_forall_of_spec (Γ : T.Env)
    (hMvan : ∀ xs m Q X, arMvanishSpec xs m Q X → Γ "ar_mvanish" [i64, i64] [.bool] xs m Q X)
    {cx mPtr mBase : BitVec 64} {s : ArCtxState} {partnerArr mArr : List (BitVec 32)}
    {mOff : Nat} {Valid : (Nat → Bool) → Prop} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hmPtr : mPtr = mBase + BitVec.ofNat 64 (4 * mOff))
    (hmo : MonoSliceOk mArr mOff mArr.length)
    (hm32 : (mArr.getD mOff 0#32).toNat + 1 < 2 ^ 32)
    (hnn32 : 2 * s.n_nets.toNat ≤ 2 ^ 32)
    (hNonEmpty : ∃ σ₀, Valid σ₀)
    (hPart : ∀ σ, Valid σ → PartnerRep σ s.n_nets.toNat partnerArr)
    (hm : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
      array (t := i32) mBase mArr ⋆ R) m)
    (hQ : ∀ ok : Bool,
      (ok = true → ∀ σ, Valid σ → monoValL σ (symListAt mArr mOff) = false) →
      Q (ok, ⟨⟩) m) :
    Γ "ar_mvanish" [i64, i64] [.bool] (cx, mPtr, ⟨⟩) m Q X := by
  classical
  by_cases hBad : ∃ σ₀, Valid σ₀ ∧ monoValL σ₀ (symListAt mArr mOff) = true
  · obtain ⟨σ₀, hV₀, hTrue⟩ := hBad
    refine hMvan (cx, mPtr, ⟨⟩) m Q X
      ⟨s, partnerArr, mBase, mArr, mOff, σ₀, R, hmPtr, hmo, hm32, hnn32, hPart σ₀ hV₀, hm,
        fun ok hvan => hQ ok fun hok σ _ => ?_⟩
    have hfalse := hvan hok
    rw [hfalse] at hTrue; cases hTrue
  · obtain ⟨σ₀, hV₀⟩ := hNonEmpty
    refine hMvan (cx, mPtr, ⟨⟩) m Q X
      ⟨s, partnerArr, mBase, mArr, mOff, σ₀, R, hmPtr, hmo, hm32, hnn32, hPart σ₀ hV₀, hm,
        fun ok _ => hQ ok fun _ σ hV => ?_⟩
    cases hmval : monoValL σ (symListAt mArr mOff)
    · rfl
    · exact absurd ⟨σ, hV, hmval⟩ hBad

end

end LeanQbe.T.Examples.Arisca.Proof
