/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Driver1Base
public import LeanQbe.T.Examples.Arisca.Proof.Driver1Gate
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import Kraken.Separation

/-!
# ARiSCA Gate Validator & Cone Reducer WPs (`Arisca.Proof.Driver1`)

Re-exports `arInstallRuleSpec`, `arDoGateSpec`, `arDoConeSpec`, and `ar_install_rule_wp` from
`Driver1Base`, and supplies `XPost`-polymorphic WP proofs for `ar_do_gate` (`ar_do_gate_wp`)
and `ar_do_cone` (`ar_do_cone_wp`).
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

public section

private structure ConeArrs where
  tm0 : List (BitVec 32)
  tm1 : List (BitVec 32)
  ts0 : List (BitVec 64)
  tl0 : List (BitVec 64)
  th0 : List (BitVec 64)
  ts1 : List (BitVec 64)
  tl1 : List (BitVec 64)
  th1 : List (BitVec 64)
  pool0 : List (BitVec 32)
  pool1 : List (BitVec 32)
  qm : List (BitVec 32)
  qs : List (BitVec 64)
  ql : List (BitVec 64)
  qh : List (BitVec 64)
  ix : List (BitVec 32)
  ix2 : List (BitVec 32)
  bx : List (BitVec 32)
  vqOff : List (BitVec 32)
  vq : List (BitVec 32)
  vqSkip : List (BitVec 8)

private abbrev ConeArrs.tMemOf (a : ConeArrs) (s : ArCtxState) : Mem 64 → Prop :=
  tMem s a.tm0 a.tm1 a.ts0 a.tl0 a.th0 a.ts1 a.tl1 a.th1 a.pool0 a.pool1

private abbrev ConeArrs.qMemOf (a : ConeArrs) (s : ArCtxState) : Mem 64 → Prop :=
  qMem s a.qm a.qs a.ql a.qh a.ix a.ix2 a.bx a.vqOff a.vq a.vqSkip

private abbrev ConeArrs.LenEq (a b : ConeArrs) : Prop :=
  a.tm0.length = b.tm0.length ∧ a.tm1.length = b.tm1.length ∧
  a.ts0.length = b.ts0.length ∧ a.tl0.length = b.tl0.length ∧ a.th0.length = b.th0.length ∧
  a.ts1.length = b.ts1.length ∧ a.tl1.length = b.tl1.length ∧ a.th1.length = b.th1.length ∧
  a.pool0.length = b.pool0.length ∧ a.pool1.length = b.pool1.length ∧
  a.qm.length = b.qm.length ∧ a.qs.length = b.qs.length ∧ a.ql.length = b.ql.length ∧
  a.qh.length = b.qh.length ∧ a.ix.length = b.ix.length ∧ a.ix2.length = b.ix2.length ∧
  a.bx.length = b.bx.length ∧ a.vqOff.length = b.vqOff.length ∧ a.vq.length = b.vq.length ∧
  a.vqSkip.length = b.vqSkip.length

private theorem coneArrs_lenEq_refl (a : ConeArrs) : ConeArrs.LenEq a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem coneArrs_lenEq_trans {a b c : ConeArrs}
    (h1 : ConeArrs.LenEq a b) (h2 : ConeArrs.LenEq b c) : ConeArrs.LenEq a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1,
   h1.2.2.2.1.trans h2.2.2.2.1, h1.2.2.2.2.1.trans h2.2.2.2.2.1,
   h1.2.2.2.2.2.1.trans h2.2.2.2.2.2.1, h1.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.trans h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

private abbrev ConeArrs.CapOk (s : ArCtxState) (a : ConeArrs) : Prop :=
  s.tcap.toNat ≤ a.tm0.length ∧ s.tcap.toNat ≤ a.tm1.length ∧
  s.tcap.toNat ≤ a.ts0.length ∧ s.tcap.toNat ≤ a.tl0.length ∧ s.tcap.toNat ≤ a.th0.length ∧
  s.tcap.toNat ≤ a.ts1.length ∧ s.tcap.toNat ≤ a.tl1.length ∧ s.tcap.toNat ≤ a.th1.length ∧
  s.pcap.toNat ≤ a.pool0.length ∧ s.pcap.toNat ≤ a.pool1.length ∧
  a.qs.length ≥ s.qcap.toNat ∧ a.ql.length ≥ s.qcap.toNat ∧
  a.qh.length ≥ s.qcap.toNat ∧ a.qm.length ≥ s.qcap.toNat ∧
  a.ix.length ≥ s.qcap.toNat ∧ a.ix2.length ≥ s.qcap.toNat ∧
  a.bx.length ≥ s.qcap.toNat ∧ a.vqOff.length ≥ s.qcap.toNat + 1 ∧
  s.pcap.toNat ≤ a.vq.length ∧ a.vqSkip.length ≥ s.qcap.toNat ∧
  s.tcap.toNat ≤ a.bx.length ∧ a.ix.length = a.ix2.length

private abbrev ConeSame (s s' : ArCtxState) : Prop :=
  s' = { s with
    pos := s'.pos, rs_n := s'.rs_n, rs_ptop := s'.rs_ptop,
    tc := s'.tc, tn := s'.tn, pc := s'.pc, ptop := s'.ptop, qn := s'.qn,
    ix := s'.ix, ix2 := s'.ix2, cur_rm := s'.cur_rm, cur_rl := s'.cur_rl,
    cur_rh := s'.cur_rh, cur_rp := s'.cur_rp, cur_nr := s'.cur_nr }

private abbrev ConeTQSame (s s' : ArCtxState) : Prop :=
  s' = { s with
    pos := s'.pos, tc := s'.tc, tn := s'.tn, pc := s'.pc, ptop := s'.ptop,
    qn := s'.qn, ix := s'.ix, ix2 := s'.ix2, cur_rm := s'.cur_rm,
    cur_rl := s'.cur_rl, cur_rh := s'.cur_rh, cur_rp := s'.cur_rp, cur_nr := s'.cur_nr }

private abbrev ConeQ (cx : Val i64) (s : ArCtxState) (artBytes : List UInt8)
    (ruleOff ruleN partnerArr rsM rsPool : List (BitVec 32)) (rsL rsH : List (BitVec 64))
    (a0 : ConeArrs) (Valid : (Nat → Bool) → Prop) (R : Mem 64 → Prop)
    (Q : Tup Val [.bool] → Mem 64 → Prop) : Prop :=
  ∀ ok s' ruleOff' ruleN' rsM' rsL' rsH' rsPool' (a' : ConeArrs) m',
    s'.pc.toNat < 2 → s'.tc.toNat < 2 →
    s'.rs_n.toNat ≤ s.rs_cap.toNat → s'.rs_ptop.toNat ≤ s.rs_pcap.toNat →
    (s.pos.toNat ≤ s.nw.toNat → s'.pos.toNat ≤ s.nw.toNat) → ConeSame s s' →
    ruleOff'.length = ruleOff.length → ruleN'.length = ruleN.length → rsM'.length = rsM.length →
    rsL'.length = rsL.length → rsH'.length = rsH.length → rsPool'.length = rsPool.length →
    ConeArrs.LenEq a' a0 →
    ((s'.ix = s.ix ∧ s'.ix2 = s.ix2) ∨ (s'.ix = s.ix2 ∧ s'.ix2 = s.ix)) →
    (ok = true →
      monoTotalWords rsPool' rsM' s'.rs_n.toNat ≤ s'.rs_ptop.toNat ∧
      (SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
        SymsBound rsPool' rsM' s'.rs_n.toNat s.n_nets.toNat) ∧
      (∀ r < s'.rs_n.toNat,
        (rsPool'.getD (rsM'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      RulesSorted rsPool' rsM' s'.rs_n.toNat ∧
      (∀ σ, Valid σ → RulesRep s'.n_out.toNat σ s' ruleOff' ruleN' rsM' rsL' rsH' rsPool')) →
    (arCtxMem cx s' ⋆ bytes s'.art artBytes ⋆
      array (t := i32) s'.rule_off ruleOff' ⋆ array (t := i32) s'.rule_n ruleN' ⋆
      array (t := i32) s'.partner partnerArr ⋆ rsMem s' rsM' rsL' rsH' rsPool' ⋆
      a'.tMemOf s' ⋆ a'.qMemOf s' ⋆ R) m' →
    Q (ok, ⟨⟩) m'

/-! ## 1. WP Proof: `ar_do_cone` -/

private theorem cone_rulesRep_eq {nOut : Nat} {σ : Nat → Bool} {s s' : ArCtxState}
    {ruleOff ruleN rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool : List (BitVec 32)}
    (h1 : s'.n_nets = s.n_nets)
    (h3 : s'.rs_n = s.rs_n) (h4 : s'.rs_cap = s.rs_cap)
    (h5 : s'.rs_ptop = s.rs_ptop) (h6 : s'.rs_pcap = s.rs_pcap)
    (hR : RulesRep nOut σ s ruleOff ruleN rsM rsL rsH rsPool) :
    RulesRep nOut σ s' ruleOff ruleN rsM rsL rsH rsPool := by
  refine ⟨by rw [h1]; exact hR.1, by rw [h1]; exact hR.2.1,
    by rw [h3, h4]; exact hR.2.2.1, by rw [h5, h6]; exact hR.2.2.2.1,
    by rw [h4]; exact hR.2.2.2.2.1, by rw [h4]; exact hR.2.2.2.2.2.1,
    by rw [h4]; exact hR.2.2.2.2.2.2.1, by rw [h6]; exact hR.2.2.2.2.2.2.2.1,
    by rw [h3, h5]; exact hR.2.2.2.2.2.2.2.2.1,
    fun v hv hne => by rw [h1] at hv; rw [h3]; exact hR.2.2.2.2.2.2.2.2.2 v hv hne⟩

private theorem cone_qMem_eq {s s' : ArCtxState}
    {qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff vq : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    (h1 : s'.qm = s.qm) (h2 : s'.qs = s.qs) (h3 : s'.ql = s.ql) (h4 : s'.qh = s.qh)
    (h5 : s'.ix = s.ix) (h6 : s'.ix2 = s.ix2) (h7 : s'.bx = s.bx)
    (h8 : s'.vq_off = s.vq_off) (h9 : s'.vq = s.vq) (h10 : s'.vq_skip = s.vq_skip) :
    qMem s' qm qs ql qh ix ix2 bx vqOff vq vqSkip =
      qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip := by
  simp only [qMem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

private theorem cone_rbase_eq {s s' : ArCtxState} {ruleOff ruleN partnerArr rsM : List (BitVec 32)}
    {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)} {a : ConeArrs} {R : Mem 64 → Prop}
    (h1 : s'.rule_off = s.rule_off) (h2 : s'.rule_n = s.rule_n) (h3 : s'.partner = s.partner)
    (h4 : s'.rs_m = s.rs_m) (h5 : s'.rs_l = s.rs_l) (h6 : s'.rs_h = s.rs_h)
    (h7 : s'.rs_pool = s.rs_pool) (h8 : s'.tm = s.tm) (h9 : s'.ts = s.ts)
    (h10 : s'.tl = s.tl) (h11 : s'.th = s.th) (h12 : s'.pool = s.pool)
    (h13 : s'.qm = s.qm) (h14 : s'.qs = s.qs) (h15 : s'.ql = s.ql) (h16 : s'.qh = s.qh)
    (h17 : s'.ix = s.ix) (h18 : s'.ix2 = s.ix2) (h19 : s'.bx = s.bx)
    (h20 : s'.vq_off = s.vq_off) (h21 : s'.vq = s.vq) (h22 : s'.vq_skip = s.vq_skip) :
    (array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i32) s.partner partnerArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
      a.tMemOf s ⋆ a.qMemOf s ⋆ R) =
    (array (t := i32) s'.rule_off ruleOff ⋆ array (t := i32) s'.rule_n ruleN ⋆
      array (t := i32) s'.partner partnerArr ⋆ rsMem s' rsM rsL rsH rsPool ⋆
      a.tMemOf s' ⋆ a.qMemOf s' ⋆ R) := by
  dsimp only [rsMem, ConeArrs.tMemOf, ConeArrs.qMemOf, tMem, qMem]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22]

private theorem cone_rbase_pos_eq {s s' : ArCtxState}
    {ruleOff ruleN partnerArr rsM : List (BitVec 32)}
    {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)} {a : ConeArrs} {R : Mem 64 → Prop}
    (hs' : s' = { s with pos := s'.pos }) :
    (array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i32) s.partner partnerArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
      a.tMemOf s ⋆ a.qMemOf s ⋆ R) =
    (array (t := i32) s'.rule_off ruleOff ⋆ array (t := i32) s'.rule_n ruleN ⋆
      array (t := i32) s'.partner partnerArr ⋆ rsMem s' rsM rsL rsH rsPool ⋆
      a.tMemOf s' ⋆ a.qMemOf s' ⋆ R) :=
  cone_rbase_eq (by rw [hs']) (by rw [hs']) (by rw [hs']) (by rw [hs']) (by rw [hs'])
    (by rw [hs']) (by rw [hs']) (by rw [hs']) (by rw [hs']) (by rw [hs']) (by rw [hs'])
    (by rw [hs']) (by rw [hs']) (by rw [hs']) (by rw [hs']) (by rw [hs']) (by rw [hs'])
    (by rw [hs']) (by rw [hs']) (by rw [hs']) (by rw [hs']) (by rw [hs'])

private theorem cone_rs_merge {s sA : ArCtxState} {cx : Val i64} {artBytes : List UInt8}
    {ruleOff ruleN partnerArr rsM rsPool : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {aA : ConeArrs} {off : Nat} {R : Mem 64 → Prop} {mA : Mem 64}
    (hoff_m : off ≤ rsM.length) (hoff_l : off ≤ rsL.length)
    (hoff_h : off ≤ rsH.length)
    (hcur1 : sA.cur_rm = s.rs_m + BitVec.ofNat 64 (4 * off))
    (hcur2 : sA.cur_rl = s.rs_l + BitVec.ofNat 64 (8 * off))
    (hcur3 : sA.cur_rh = s.rs_h + BitVec.ofNat 64 (8 * off))
    (hcur4 : sA.cur_rp = s.rs_pool)
    (hsA : sA.art = s.art ∧ sA.rule_off = s.rule_off ∧ sA.rule_n = s.rule_n ∧
      sA.rs_m = s.rs_m ∧ sA.rs_l = s.rs_l ∧ sA.rs_h = s.rs_h ∧ sA.rs_pool = s.rs_pool)
    (hmA : (arCtxMem cx sA ⋆ array (t := i32) sA.partner partnerArr ⋆
      array (t := i32) sA.cur_rm (rsM.drop off) ⋆ array64 sA.cur_rl (rsL.drop off) ⋆
      array64 sA.cur_rh (rsH.drop off) ⋆ array (t := i32) sA.cur_rp rsPool ⋆
      aA.tMemOf sA ⋆ aA.qMemOf sA ⋆
      (bytes s.art artBytes ⋆ array (t := i32) s.rule_off ruleOff ⋆
       array (t := i32) s.rule_n ruleN ⋆ array (t := i32) s.rs_m (rsM.take off) ⋆
       array64 s.rs_l (rsL.take off) ⋆ array64 s.rs_h (rsH.take off) ⋆
       u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ R)) mA) :
    (arCtxMem cx sA ⋆ bytes sA.art artBytes ⋆ array (t := i32) sA.rule_off ruleOff ⋆
      array (t := i32) sA.rule_n ruleN ⋆ array (t := i32) sA.partner partnerArr ⋆
      rsMem sA rsM rsL rsH rsPool ⋆ aA.tMemOf sA ⋆ aA.qMemOf sA ⋆ R) mA := by
  rcases hsA with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  rw [hcur1, hcur2, hcur3, hcur4] at hmA
  rw [h1, h2, h3, rsMem_unpack, h4, h5, h6, h7, rs_split_at hoff_m hoff_l hoff_h]
  exact sep_cast hmA (by ac_rfl)

private def coneStepIgnore : Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | @Expr.let_ _ _ _ [.bits 64] _ k => k (0#64, ())
  | @Expr.let_ _ _ _ [.bits 32] _ k => k (0#32, ())
  | @Expr.let_ _ _ _ [.bool] _ k => k (false, ())
  | @Expr.load _ _ _ (.bits 64) _ k => k 0#64
  | @Expr.load _ _ _ (.bits 32) _ k => k 0#32
  | .jnz _ _ f => f
  | e => e

private def coneFindLoop : Nat → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | 0, e => e
  | _ + 1, @Expr.call _ _ _ _ _ [.bool] _ k =>
    match k (true, ()) with
    | .jnz _ t _ => t
    | _ => .ret (Arg.imm false, ())
  | n + 1, e => coneFindLoop n (coneStepIgnore e)

private def coneLoopExpr (cx : Val i64) (root k : Val i32) : Expr Val Cont [.bool] :=
  match ar_do_cone_body Val Cont (cx, ()) with
  | @Expr.call _ _ _ _ _ [.bool, .bits 32] _ k1 =>
    match k1 (true, root, ()) with
    | .jnz _ (@Expr.call _ _ _ _ _ [.bool, .bits 32] _ k2) _ =>
      match k2 (true, k, ()) with
      | .jnz _ e _ => coneFindLoop 30 e
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

private theorem cone_store_step {Γ : LeanQbe.T.Env}
    (hStore : ∀ xs m Q X, arStoreRuleSpec xs m Q X →
      Γ "ar_store_rule" [i64, i32] [.bool] xs m Q X)
    {cx : Val i64} {root : BitVec 32} {s sL : ArCtxState} {artBytes : List UInt8}
    {ruleOff ruleN partnerArr rsM rsPool : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {a0 aL : ConeArrs} {Valid : (Nat → Bool) → Prop} {R : Mem 64 → Prop} {mL : Mem 64}
    {Q : Tup Val [.bool] → Mem 64 → Prop} {X : XPost}
    (hpcL : sL.pc.toNat < 2) (htcL : sL.tc.toNat < 2)
    (htnL : sL.tn.toNat ≤ s.tcap.toNat) (hposL : sL.pos.toNat ≤ s.nw.toNat)
    (hptL : sL.ptop.toNat ≤ s.pcap.toNat) (hsL : ConeTQSame s sL)
    (hixL : (sL.ix = s.ix ∧ sL.ix2 = s.ix2) ∨ (sL.ix = s.ix2 ∧ sL.ix2 = s.ix))
    (htcap30 : s.tcap.toNat < 2 ^ 30) (hpcap32 : s.pcap.toNat < 2 ^ 32)
    (hrcap30 : s.rs_cap.toNat < 2 ^ 30) (hrpcap32 : s.rs_pcap.toNat < 2 ^ 32)
    (hroot_lt : root.toNat < s.n_nets.toNat)
    (hcap0 : ConeArrs.CapOk s a0) (hlenL : ConeArrs.LenEq aL a0)
    (hTot : monoTotalWords rsPool rsM s.rs_n.toNat ≤ s.rs_ptop.toNat)
    (hRsOk : ∀ r < s.rs_n.toNat,
      (rsPool.getD (rsM.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hRsSorted : RulesSorted rsPool rsM s.rs_n.toNat)
    (hValEx : ∃ σ0, Valid σ0)
    (hValRep : ∀ σ, Valid σ →
      PartnerRep σ s.n_nets.toNat partnerArr ∧
      RulesRep s.n_out.toNat σ s ruleOff ruleN rsM rsL rsH rsPool)
    (hSlL : ∀ r < sL.tn.toNat,
      MonoSliceOk (if sL.pc.toNat = 0 then aL.pool0 else aL.pool1)
        ((if sL.tc.toNat = 0 then aL.tm0 else aL.tm1).getD r 0#32).toNat sL.ptop.toNat ∧
      ((if sL.pc.toNat = 0 then aL.pool0 else aL.pool1).getD
        ((if sL.tc.toNat = 0 then aL.tm0 else aL.tm1).getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSortedL : ∀ r < sL.tn.toNat,
      MonoSorted (if sL.pc.toNat = 0 then aL.pool0 else aL.pool1)
        ((if sL.tc.toNat = 0 then aL.tm0 else aL.tm1).getD r 0#32).toNat)
    (hTotL : monoTotalWords (if sL.pc.toNat = 0 then aL.pool0 else aL.pool1)
      (if sL.tc.toNat = 0 then aL.tm0 else aL.tm1) sL.tn.toNat ≤ sL.ptop.toNat)
    (hSyL : SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
      SymsBound (if sL.pc.toNat = 0 then aL.pool0 else aL.pool1)
        (if sL.tc.toNat = 0 then aL.tm0 else aL.tm1) sL.tn.toNat s.n_nets.toNat)
    (hPolyL : ∀ σ, Valid σ →
      polyEval s.n_out.toNat σ (if sL.pc.toNat = 0 then aL.pool0 else aL.pool1)
        (if sL.tc.toNat = 0 then aL.tm0 else aL.tm1)
        (if sL.tc.toNat = 0 then aL.tl0 else aL.tl1)
        (if sL.tc.toNat = 0 then aL.th0 else aL.th1) sL.tn.toNat =
          bv s.n_out.toNat (σ (2 * root.toNat)))
    (hmL : (arCtxMem cx sL ⋆ bytes sL.art artBytes ⋆
      array (t := i32) sL.rule_off ruleOff ⋆ array (t := i32) sL.rule_n ruleN ⋆
      array (t := i32) sL.partner partnerArr ⋆ rsMem sL rsM rsL rsH rsPool ⋆
      aL.tMemOf sL ⋆ aL.qMemOf sL ⋆ R) mL)
    (hQ : ConeQ cx s artBytes ruleOff ruleN partnerArr rsM rsPool rsL rsH a0 Valid R Q) :
    wp Γ Q X (@Expr.call Val Cont [.bool] "ar_store_rule" [i64, i32] [.bool]
      (Arg.var cx, Arg.var root, ()) fun p => Expr.ret (Arg.var p.fst, ())) mL := by
  have ⟨htm0_l, htm1_l, _, htl0_l, hth0_l, _, htl1_l, hth1_l, hp0_l, hp1_l, _⟩ := hcap0
  have ⟨htm0L, htm1L, _, htl0L, hth0L, _, htl1L, hth1L, hp0L, hp1L, _⟩ := hlenL
  let Rstore : Mem 64 → Prop :=
    bytes s.art artBytes ⋆ array (t := i32) s.partner partnerArr ⋆ aL.qMemOf sL ⋆ R
  have hsL_art : sL.art = s.art := by rw [hsL]
  have hsL_part : sL.partner = s.partner := by rw [hsL]
  have hm_store : (arCtxMem cx sL ⋆ array (t := i32) sL.rule_off ruleOff ⋆
      array (t := i32) sL.rule_n ruleN ⋆ rsMem sL rsM rsL rsH rsPool ⋆
      aL.tMemOf sL ⋆ Rstore) mL := by
    rw [hsL_art, hsL_part] at hmL
    dsimp only [Rstore]
    exact sep_cast hmL (by ac_rfl)
  have hpt_pool : sL.ptop.toNat ≤ (if sL.pc.toNat = 0 then aL.pool0 else aL.pool1).length := by
    split <;> omega
  apply wp_call_of_spec
  refine hStore _ _ _ _ ⟨sL, ruleOff, ruleN, rsM, rsL, rsH, rsPool,
    aL.tm0, aL.tm1, aL.ts0, aL.tl0, aL.th0, aL.ts1, aL.tl1, aL.th1, aL.pool0, aL.pool1,
    Valid, Rstore, hpcL, htcL, by rw [hsL]; dsimp only; exact hroot_lt,
    by rw [hsL]; dsimp only; exact htnL, by rw [hsL]; dsimp only; omega,
    by rw [hsL]; dsimp only; exact hpcap32, by rw [hsL]; dsimp only; omega,
    by rw [hsL]; dsimp only; exact hrpcap32, by rw [hsL]; dsimp only; omega,
    by rw [hsL]; dsimp only; omega, by rw [hsL]; dsimp only; omega,
    by rw [hsL]; dsimp only; omega, by rw [hsL]; dsimp only; omega,
    by rw [hsL]; dsimp only; omega, by rw [hsL]; dsimp only; omega,
    by rw [hsL]; dsimp only; omega, hValEx,
    fun σ hV => by
      rw [show sL.n_out = s.n_out by rw [hsL]]
      exact cone_rulesRep_eq (by rw [hsL]) (by rw [hsL]) (by rw [hsL])
        (by rw [hsL]) (by rw [hsL]) (hValRep σ hV).2,
    by rw [hsL]; dsimp only; exact hRsSorted,
    by rw [hsL]; dsimp only; exact hTot, by rw [hsL]; dsimp only; exact hRsOk,
    fun r hr => ⟨⟨Nat.lt_of_lt_of_le (hSlL r hr).1.1 hpt_pool,
      Nat.le_trans (hSlL r hr).1.2 hpt_pool⟩, (hSlL r hr).2⟩,
    by rw [hsL]; dsimp only; exact hSortedL,
    by rw [hsL]; dsimp only; omega, fun σ hV => by rw [hsL]; dsimp only; exact hPolyL σ hV,
    hm_store,
    fun okS s' ruleOff' ruleN' rsM' rsL' rsH' rsPool' m'
      hrsn' hrspt' hs'_eq hro' hrn' hrsm' hrsl' hrsh' hrsp' hokS hm' => ?_⟩
  c0_hsteps_nogrp
  have hs'_s : ConeSame s s' := by rw [hs'_eq, hsL]
  have hm'_fin : (arCtxMem cx s' ⋆ bytes s'.art artBytes ⋆
      array (t := i32) s'.rule_off ruleOff' ⋆ array (t := i32) s'.rule_n ruleN' ⋆
      array (t := i32) s'.partner partnerArr ⋆ rsMem s' rsM' rsL' rsH' rsPool' ⋆
      aL.tMemOf s' ⋆ aL.qMemOf s' ⋆ R) m' := by
    have h3 := cone_qMem_eq (s := sL) (s' := s') (qm := aL.qm) (qs := aL.qs) (ql := aL.ql)
      (qh := aL.qh) (ix := aL.ix) (ix2 := aL.ix2) (bx := aL.bx) (vqOff := aL.vqOff)
      (vq := aL.vq) (vqSkip := aL.vqSkip) (by rw [hs'_eq]) (by rw [hs'_eq]) (by rw [hs'_eq])
      (by rw [hs'_eq]) (by rw [hs'_eq]) (by rw [hs'_eq]) (by rw [hs'_eq])
      (by rw [hs'_eq]) (by rw [hs'_eq]) (by rw [hs'_eq])
    dsimp only [Rstore, ConeArrs.tMemOf, ConeArrs.qMemOf] at hm' ⊢
    rw [show s'.art = s.art by rw [hs'_s],
      show s'.partner = s.partner by rw [hs'_s], h3]
    exact sep_cast hm' (by ac_rfl)
  exact hQ okS s' ruleOff' ruleN' rsM' rsL' rsH' rsPool' aL m'
    (by rw [hs'_eq]; exact hpcL) (by rw [hs'_eq]; exact htcL)
    (by rw [hsL] at hrsn'; exact hrsn') (by rw [hsL] at hrspt'; exact hrspt')
    (fun _ => by rw [hs'_eq]; exact hposL)
    hs'_s hro' hrn' hrsm' hrsl' hrsh' hrsp' hlenL
    (by rw [show s'.ix = sL.ix by rw [hs'_eq], show s'.ix2 = sL.ix2 by rw [hs'_eq]]; exact hixL)
    (fun h => by
      obtain ⟨hR', hRsS', hT', hSy', hO'⟩ := hokS h
      rw [show sL.rs_n = s.rs_n by rw [hsL]] at hSy'
      exact ⟨hT', fun hSb => hSy' s.n_nets.toNat hSb (hSyL hSb), hO', hRsS', hR'⟩) hm'_fin

private theorem cone_apply_step {Γ : LeanQbe.T.Env}
    (hApply : ∀ xs m Q X, arApplySpec xs m Q X →
      Γ "ar_apply" [i64, i32] [.bool] xs m Q X)
    {cx : Val i64} {sym : BitVec 32} {s sAp : ArCtxState} {artBytes : List UInt8}
    {ruleOff ruleN partnerArr rsM rsPool : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {a0 aL : ConeArrs} {Valid : (Nat → Bool) → Prop} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Tup Val [.bool] → Mem 64 → Prop} {X : XPost} {kTrue : Expr Val Cont [.bool]}
    {off : Nat}
    (hpcL : sAp.pc.toNat < 2) (htcL : sAp.tc.toNat < 2)
    (htnL : sAp.tn.toNat ≤ s.tcap.toNat) (htcap30 : s.tcap.toNat < 2 ^ 30)
    (hqcap16 : 16 ≤ s.qcap.toNat) (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32)
    (hptL : sAp.ptop.toNat ≤ s.pcap.toNat) (hpcap32 : s.pcap.toNat < 2 ^ 32)
    (hnnets30 : s.n_nets.toNat ≤ 0x3FFFFFFF) (h2nnets32 : 2 * s.n_nets.toNat < 2 ^ 32)
    (hrsn_le : s.rs_n.toNat ≤ s.rs_cap.toNat) (hrspt_le : s.rs_ptop.toNat ≤ s.rs_pcap.toNat)
    (hpos : sAp.pos.toNat ≤ s.nw.toNat) (hsAp_s : ConeTQSame s sAp)
    (hoff_m : off ≤ rsM.length) (hoff_l : off ≤ rsL.length) (hoff_h : off ≤ rsH.length)
    (hcur1 : sAp.cur_rm = s.rs_m + BitVec.ofNat 64 (4 * off))
    (hcur2 : sAp.cur_rl = s.rs_l + BitVec.ofNat 64 (8 * off))
    (hcur3 : sAp.cur_rh = s.rs_h + BitVec.ofNat 64 (8 * off))
    (hcur4 : sAp.cur_rp = s.rs_pool)
    (hcap0 : ConeArrs.CapOk s a0) (hlenL : ConeArrs.LenEq aL a0)
    (hmasks : MasksOk s.n_out.toNat s.mlo s.mhi) (hValEx : ∃ σ0, Valid σ0)
    (hPartRep : ∀ σ, Valid σ → PartnerRep σ s.n_nets.toNat partnerArr)
    (hcurR : ∀ σ, Valid σ → CurRRep sAp.n_out.toNat σ sAp.cur_nr.toNat sym.toNat
      (rsM.drop off) (rsL.drop off) (rsH.drop off) rsPool)
    (hcurSorted : ∀ r < sAp.cur_nr.toNat,
      MonoSorted rsPool ((rsM.drop off).getD r 0#32).toNat)
    (hcurOk : ∀ r < sAp.cur_nr.toNat,
      (rsPool.getD ((rsM.drop off).getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hcurTot : monoTotalWords rsPool (rsM.drop off) sAp.cur_nr.toNat ≤ 4000000000)
    (hSlL : ∀ r < sAp.tn.toNat,
      MonoSliceOk (if sAp.pc.toNat = 0 then aL.pool0 else aL.pool1)
        ((if sAp.tc.toNat = 0 then aL.tm0 else aL.tm1).getD r 0#32).toNat sAp.ptop.toNat ∧
      ((if sAp.pc.toNat = 0 then aL.pool0 else aL.pool1).getD
        ((if sAp.tc.toNat = 0 then aL.tm0 else aL.tm1).getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSortedL : ∀ r < sAp.tn.toNat,
      MonoSorted (if sAp.pc.toNat = 0 then aL.pool0 else aL.pool1)
        ((if sAp.tc.toNat = 0 then aL.tm0 else aL.tm1).getD r 0#32).toNat)
    (hSigL : SigOk (if sAp.pc.toNat = 0 then aL.pool0 else aL.pool1)
      (if sAp.tc.toNat = 0 then aL.tm0 else aL.tm1)
      (if sAp.tc.toNat = 0 then aL.ts0 else aL.ts1) sAp.tn.toNat)
    (hTotL : monoTotalWords (if sAp.pc.toNat = 0 then aL.pool0 else aL.pool1)
      (if sAp.tc.toNat = 0 then aL.tm0 else aL.tm1) sAp.tn.toNat ≤ sAp.ptop.toNat)
    (hSyL : SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
      SymsBound (if sAp.pc.toNat = 0 then aL.pool0 else aL.pool1)
        (if sAp.tc.toNat = 0 then aL.tm0 else aL.tm1) sAp.tn.toNat s.n_nets.toNat)
    (hSyR : SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
      SymsBound rsPool (rsM.drop off) sAp.cur_nr.toNat s.n_nets.toNat)
    (hixSwL : (sAp.ix = s.ix ∧ sAp.ix2 = s.ix2) ∨ (sAp.ix = s.ix2 ∧ sAp.ix2 = s.ix))
    (hm : (arCtxMem cx sAp ⋆ bytes sAp.art artBytes ⋆ array (t := i32) sAp.rule_off ruleOff ⋆
      array (t := i32) sAp.rule_n ruleN ⋆ array (t := i32) sAp.partner partnerArr ⋆
      rsMem sAp rsM rsL rsH rsPool ⋆ aL.tMemOf sAp ⋆ aL.qMemOf sAp ⋆ R) m)
    (hkTrue : ∀ sA (aA : ConeArrs) mA,
      sA.pc.toNat < 2 → sA.tc.toNat < 2 →
      sA.tn.toNat ≤ s.tcap.toNat → sA.ptop.toNat ≤ s.pcap.toNat →
      sA.pos.toNat ≤ s.nw.toNat → ConeTQSame s sA → ConeArrs.LenEq aA a0 →
      ((sA.ix = s.ix ∧ sA.ix2 = s.ix2) ∨ (sA.ix = s.ix2 ∧ sA.ix2 = s.ix)) →
      (∀ r < sA.tn.toNat,
        MonoSliceOk (if sA.pc.toNat = 0 then aA.pool0 else aA.pool1)
          ((if sA.tc.toNat = 0 then aA.tm0 else aA.tm1).getD r 0#32).toNat sA.ptop.toNat ∧
        ((if sA.pc.toNat = 0 then aA.pool0 else aA.pool1).getD
          ((if sA.tc.toNat = 0 then aA.tm0 else aA.tm1).getD r 0#32).toNat 0#32).toNat + 1 <
          2 ^ 32) →
      (∀ r < sA.tn.toNat,
        MonoSorted (if sA.pc.toNat = 0 then aA.pool0 else aA.pool1)
          ((if sA.tc.toNat = 0 then aA.tm0 else aA.tm1).getD r 0#32).toNat) →
      SigOk (if sA.pc.toNat = 0 then aA.pool0 else aA.pool1)
        (if sA.tc.toNat = 0 then aA.tm0 else aA.tm1)
        (if sA.tc.toNat = 0 then aA.ts0 else aA.ts1) sA.tn.toNat →
      monoTotalWords (if sA.pc.toNat = 0 then aA.pool0 else aA.pool1)
        (if sA.tc.toNat = 0 then aA.tm0 else aA.tm1) sA.tn.toNat ≤ sA.ptop.toNat →
      (SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
        SymsBound (if sA.pc.toNat = 0 then aA.pool0 else aA.pool1)
          (if sA.tc.toNat = 0 then aA.tm0 else aA.tm1) sA.tn.toNat s.n_nets.toNat) →
      (∀ σ, Valid σ →
        polyEval sAp.n_out.toNat σ (if sA.pc.toNat = 0 then aA.pool0 else aA.pool1)
          (if sA.tc.toNat = 0 then aA.tm0 else aA.tm1)
          (if sA.tc.toNat = 0 then aA.tl0 else aA.tl1)
          (if sA.tc.toNat = 0 then aA.th0 else aA.th1) sA.tn.toNat =
        polyEval sAp.n_out.toNat σ (if sAp.pc.toNat = 0 then aL.pool0 else aL.pool1)
          (if sAp.tc.toNat = 0 then aL.tm0 else aL.tm1)
          (if sAp.tc.toNat = 0 then aL.tl0 else aL.tl1)
          (if sAp.tc.toNat = 0 then aL.th0 else aL.th1) sAp.tn.toNat) →
      (arCtxMem cx sA ⋆ bytes sA.art artBytes ⋆ array (t := i32) sA.rule_off ruleOff ⋆
        array (t := i32) sA.rule_n ruleN ⋆ array (t := i32) sA.partner partnerArr ⋆
        rsMem sA rsM rsL rsH rsPool ⋆ aA.tMemOf sA ⋆ aA.qMemOf sA ⋆ R) mA →
      wp Γ Q X kTrue mA)
    (hQ : ConeQ cx s artBytes ruleOff ruleN partnerArr rsM rsPool rsL rsH a0 Valid R Q) :
    wp Γ Q X (@Expr.call Val Cont [.bool] "ar_apply" [i64, i32] [.bool]
      (Arg.var cx, Arg.var sym, ()) fun p =>
      Expr.jnz (Arg.var p.fst) kTrue (Expr.ret (Arg.imm false, ())) ) m := by
  have ⟨htm0_l, htm1_l, hts0_l, htl0_l, hth0_l, hts1_l, htl1_l, hth1_l, hp0_l, hp1_l,
    hqs_l, hql_l, hqh_l, hqm_l, hix_l, hix2_l, hbx_l, hvqo_l, hvq_l, hvqs_l,
    htbx_l, hix_eq⟩ := hcap0
  have ⟨htm0L, htm1L, hts0L, htl0L, hth0L, hts1L, htl1L, hth1L, hp0L, hp1L,
    hqmL, hqsL, hqlL, hqhL, hixL, hix2L, hbxL, hvqoL, hvqL, hvqsL⟩ := hlenL
  have hs_art : sAp.art = s.art := by rw [hsAp_s]
  have hs_ro : sAp.rule_off = s.rule_off := by rw [hsAp_s]
  have hs_rn : sAp.rule_n = s.rule_n := by rw [hsAp_s]
  have hs_pa : sAp.partner = s.partner := by rw [hsAp_s]
  have hs_rm : sAp.rs_m = s.rs_m := by rw [hsAp_s]
  have hs_rl : sAp.rs_l = s.rs_l := by rw [hsAp_s]
  have hs_rh : sAp.rs_h = s.rs_h := by rw [hsAp_s]
  have hs_rp : sAp.rs_pool = s.rs_pool := by rw [hsAp_s]
  have hs_tcap : sAp.tcap = s.tcap := by rw [hsAp_s]
  have hs_qcap : sAp.qcap = s.qcap := by rw [hsAp_s]
  have hs_pcap : sAp.pcap = s.pcap := by rw [hsAp_s]
  have hs_nnets : sAp.n_nets = s.n_nets := by rw [hsAp_s]
  have hs_nout : sAp.n_out = s.n_out := by rw [hsAp_s]
  let Rapply : Mem 64 → Prop :=
    bytes s.art artBytes ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
    array (t := i32) s.rs_m (rsM.take off) ⋆ array64 s.rs_l (rsL.take off) ⋆
    array64 s.rs_h (rsH.take off) ⋆
    u32PadTail s.rs_m rsM.length ⋆ u32PadTail s.rs_pool rsPool.length ⋆ R
  have hm_sp : (arCtxMem cx sAp ⋆ array (t := i32) sAp.partner partnerArr ⋆
      array (t := i32) sAp.cur_rm (rsM.drop off) ⋆ array64 sAp.cur_rl (rsL.drop off) ⋆
      array64 sAp.cur_rh (rsH.drop off) ⋆ array (t := i32) sAp.cur_rp rsPool ⋆
      aL.tMemOf sAp ⋆ aL.qMemOf sAp ⋆ Rapply) m := by
    rw [hs_art, hs_ro, hs_rn, rsMem_unpack, hs_rm, hs_rl, hs_rh, hs_rp,
      rs_split_at hoff_m hoff_l hoff_h] at hm
    dsimp only [Rapply]
    rw [hcur1, hcur2, hcur3, hcur4]
    exact sep_cast hm (by ac_rfl)
  apply wp_call_of_spec
  refine hApply _ _ _ _ ⟨sAp, aL.tm0, aL.tm1, aL.ts0, aL.tl0, aL.th0, aL.ts1, aL.tl1, aL.th1,
    aL.pool0, aL.pool1, aL.qm, aL.qs, aL.ql, aL.qh, aL.ix, aL.ix2, aL.bx, aL.vqOff, aL.vq,
    aL.vqSkip, partnerArr, rsM.drop off, rsL.drop off, rsH.drop off, rsPool, Valid, Rapply,
    hpcL, htcL, by rw [hs_tcap]; exact htnL, by rw [hs_tcap]; exact htcap30,
    by rw [hs_qcap]; exact hqcap16, by rw [hs_qcap]; exact hqcap32,
    by rw [hs_pcap]; exact hptL, by rw [hs_pcap]; exact hpcap32,
    by rw [hs_nnets]; exact hnnets30, by rw [hs_nnets]; exact h2nnets32,
    by rw [hs_tcap, htm0L]; exact htm0_l, by rw [hs_tcap, htm1L]; exact htm1_l,
    by rw [hs_tcap, hts0L]; exact hts0_l, by rw [hs_tcap, htl0L]; exact htl0_l,
    by rw [hs_tcap, hth0L]; exact hth0_l, by rw [hs_tcap, hts1L]; exact hts1_l,
    by rw [hs_tcap, htl1L]; exact htl1_l, by rw [hs_tcap, hth1L]; exact hth1_l,
    by rw [hs_pcap, hp0L]; exact hp0_l, by rw [hs_pcap, hp1L]; exact hp1_l,
    by rw [hs_qcap, hqmL]; exact hqm_l, by rw [hs_qcap, hqsL]; exact hqs_l,
    by rw [hs_qcap, hqlL]; exact hql_l, by rw [hs_qcap, hqhL]; exact hqh_l,
    by rw [hs_qcap, hixL]; exact hix_l, by rw [hs_qcap, hix2L]; exact hix2_l,
    by rw [hs_tcap, hbxL]; exact htbx_l,
    by rw [hs_qcap, hbxL]; exact hbx_l, by rw [hs_qcap, hvqoL]; exact hvqo_l,
    by rw [hs_pcap, hvqL]; exact hvq_l, by rw [hs_qcap, hvqsL]; exact hvqs_l,
    by rw [hs_nout, hsAp_s]; exact hmasks, hValEx,
    fun σ hV => by rw [hs_nnets]; exact hPartRep σ hV,
    hcurR, hcurSorted, hcurOk, hcurTot, hSlL, hSortedL, hSigL, hTotL, hm_sp,
    fun okA sA tm0A tm1A ts0A tl0A th0A ts1A tl1A th1A pool0A pool1A
      qmA qsA qlA qhA ixA ix2A bxA vqOffA vqA vqSkipA mA
      hpcA htcA hptA htnA hsA_eq
      htm0A htm1A hts0A htl0A hth0A hts1A htl1A hth1A hp0A hp1A
      hqmA hqsA hqlA hqhA hix_sw hbxA hvqoA hvqA hvqsA hokA hmA => ?_⟩
  let aA : ConeArrs := ⟨tm0A, tm1A, ts0A, tl0A, th0A, ts1A, tl1A, th1A, pool0A, pool1A,
    qmA, qsA, qlA, qhA, ixA, ix2A, bxA, vqOffA, vqA, vqSkipA⟩
  have hsA_s : ConeTQSame s sA := by rw [hsA_eq, hsAp_s]
  have hmA_repack := cone_rs_merge (s := s) (sA := sA) (aA := aA) hoff_m hoff_l hoff_h
    (by rw [hsA_eq]; exact hcur1) (by rw [hsA_eq]; exact hcur2)
    (by rw [hsA_eq]; exact hcur3) (by rw [hsA_eq]; exact hcur4)
    ⟨by rw [hsA_s], by rw [hsA_s], by rw [hsA_s], by rw [hsA_s],
      by rw [hsA_s], by rw [hsA_s], by rw [hsA_s]⟩ hmA
  have htnA' : sA.tn.toNat ≤ s.tcap.toNat := by rw [← hs_tcap]; exact htnA
  have hptA' : sA.ptop.toNat ≤ s.pcap.toNat := by rw [← hs_pcap]; exact hptA
  have hposA' : sA.pos.toNat ≤ s.nw.toNat := by
    have : sA.pos = sAp.pos := by rw [hsA_eq]
    rw [this]; exact hpos
  have hixA : ixA.length = aL.ix.length := by
    rcases hix_sw with ⟨_, _, h1, _⟩ | ⟨_, _, h1, _⟩ <;> omega
  have hix2A : ix2A.length = aL.ix2.length := by
    rcases hix_sw with ⟨_, _, _, h2⟩ | ⟨_, _, _, h2⟩ <;> omega
  have hlenA : ConeArrs.LenEq aA a0 :=
    coneArrs_lenEq_trans ⟨htm0A, htm1A, hts0A, htl0A, hth0A, hts1A, htl1A, hth1A, hp0A, hp1A,
      hqmA, hqsA, hqlA, hqhA, hixA, hix2A, hbxA, hvqoA, hvqA, hvqsA⟩ hlenL
  have hixA_s : (sA.ix = s.ix ∧ sA.ix2 = s.ix2) ∨ (sA.ix = s.ix2 ∧ sA.ix2 = s.ix) := by
    rcases hixSwL with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hix_sw with ⟨h3, h4, _⟩ | ⟨h3, h4, _⟩
    · exact Or.inl ⟨h3.trans h1, h4.trans h2⟩
    · exact Or.inr ⟨h3.trans h2, h4.trans h1⟩
    · exact Or.inr ⟨h3.trans h1, h4.trans h2⟩
    · exact Or.inl ⟨h3.trans h2, h4.trans h1⟩
  cases hok_v : okA
  · dsimp only
    refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
    c0_hstraight
    have hrsA : sA.rs_n = s.rs_n ∧ sA.rs_ptop = s.rs_ptop := by rw [hsA_s]; exact ⟨rfl, rfl⟩
    exact hQ false sA ruleOff ruleN rsM rsL rsH rsPool aA mA
      hpcA htcA (by rw [hrsA.1]; exact hrsn_le) (by rw [hrsA.2]; exact hrspt_le)
      (fun _ => hposA') (by dsimp only [ConeSame]; rw [hrsA.1, hrsA.2]; exact hsA_s)
      rfl rfl rfl rfl rfl rfl hlenA hixA_s (fun h => by cases h) hmA_repack
  · dsimp only
    refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
    obtain ⟨hSlA, hSortedA, hSigA, hTotA, hSyA, hPolyA⟩ := hokA hok_v
    exact hkTrue sA aA mA hpcA htcA htnA' hptA' hposA' hsA_s hlenA hixA_s
      hSlA hSortedA hSigA hTotA (fun hSb => hSyA s.n_nets.toNat (hSyL hSb) (hSyR hSb))
      hPolyA hmA_repack

private theorem ar_do_cone_loop_wp {Γ : LeanQbe.T.Env}
    (hNW : ∀ xs m Q X, arNextWordSpec xs m Q X →
      Γ "ar_next_word" [i64] [.bool, i32] xs m Q X)
    (hApply : ∀ xs m Q X, arApplySpec xs m Q X →
      Γ "ar_apply" [i64, i32] [.bool] xs m Q X)
    (hStore : ∀ xs m Q X, arStoreRuleSpec xs m Q X →
      Γ "ar_store_rule" [i64, i32] [.bool] xs m Q X)
    {cx : Val i64} {root k : BitVec 32} {s s3 : ArCtxState} {artBytes : List UInt8}
    {ruleOff ruleN partnerArr rsM rsPool : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {a0 a3 : ConeArrs} {Valid : (Nat → Bool) → Prop} {R : Mem 64 → Prop} {m3 : Mem 64}
    {Q : Tup Val [.bool] → Mem 64 → Prop} {X : XPost}
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2) (htcap30 : s.tcap.toNat < 2 ^ 30)
    (hqcap16 : 16 ≤ s.qcap.toNat) (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32)
    (hpcap32 : s.pcap.toNat < 2 ^ 32) (hrcap30 : s.rs_cap.toNat < 2 ^ 30)
    (hrpcap32 : s.rs_pcap.toNat < 2 ^ 32) (hnnets30 : s.n_nets.toNat ≤ 0x3FFFFFFF)
    (h2nnets32 : 2 * s.n_nets.toNat < 2 ^ 32)
    (hart64 : s.art.toNat + artBytes.length < 2 ^ 64) (hnw4 : 4 * s.nw.toNat ≤ artBytes.length)
    (hroot_lt : root.toNat < s.n_nets.toNat)
    (hrsn_le : s.rs_n.toNat ≤ s.rs_cap.toNat) (hrspt_le : s.rs_ptop.toNat ≤ s.rs_pcap.toNat)
    (_hk_le_rem : k.toNat ≤ s.nw.toNat - s3.pos.toNat) (hpos3 : s3.pos.toNat ≤ s.nw.toNat)
    (hs3_s : s3 = { s with pos := s3.pos, tn := s3.tn, ptop := s3.ptop, qn := 0#32 })
    (htn3 : s3.tn.toNat ≤ s.tcap.toNat) (hpt3 : s3.ptop.toNat ≤ s.pcap.toNat)
    (hcap0 : ConeArrs.CapOk s a0) (hlen3 : ConeArrs.LenEq a3 a0)
    (hmasks : MasksOk s.n_out.toNat s.mlo s.mhi) (hrpcap4g : s.rs_pcap.toNat ≤ 4000000000)
    (hTotWords : monoTotalWords rsPool rsM s.rs_n.toNat ≤ s.rs_ptop.toNat)
    (hRsOk : ∀ r < s.rs_n.toNat,
      (rsPool.getD (rsM.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hRsSorted : RulesSorted rsPool rsM s.rs_n.toNat)
    (hValEx : ∃ σ0, Valid σ0)
    (hValRep : ∀ σ, Valid σ →
      PartnerRep σ s.n_nets.toNat partnerArr ∧
      RulesRep s.n_out.toNat σ s ruleOff ruleN rsM rsL rsH rsPool)
    (hSl3 : ∀ r < s3.tn.toNat,
      MonoSliceOk (if s3.pc.toNat = 0 then a3.pool0 else a3.pool1)
        ((if s3.tc.toNat = 0 then a3.tm0 else a3.tm1).getD r 0#32).toNat s3.ptop.toNat ∧
      ((if s3.pc.toNat = 0 then a3.pool0 else a3.pool1).getD
        ((if s3.tc.toNat = 0 then a3.tm0 else a3.tm1).getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted3 : ∀ r < s3.tn.toNat,
      MonoSorted (if s3.pc.toNat = 0 then a3.pool0 else a3.pool1)
        ((if s3.tc.toNat = 0 then a3.tm0 else a3.tm1).getD r 0#32).toNat)
    (hSig3 : SigOk (if s3.pc.toNat = 0 then a3.pool0 else a3.pool1)
      (if s3.tc.toNat = 0 then a3.tm0 else a3.tm1)
      (if s3.tc.toNat = 0 then a3.ts0 else a3.ts1) s3.tn.toNat)
    (hTot3 : monoTotalWords (if s3.pc.toNat = 0 then a3.pool0 else a3.pool1)
      (if s3.tc.toNat = 0 then a3.tm0 else a3.tm1) s3.tn.toNat ≤ s3.ptop.toNat)
    (hSy3 : SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
      SymsBound (if s3.pc.toNat = 0 then a3.pool0 else a3.pool1)
        (if s3.tc.toNat = 0 then a3.tm0 else a3.tm1) s3.tn.toNat s.n_nets.toNat)
    (hPoly3 : ∀ σ, Valid σ →
      polyEval s.n_out.toNat σ (if s3.pc.toNat = 0 then a3.pool0 else a3.pool1)
        (if s3.tc.toNat = 0 then a3.tm0 else a3.tm1)
        (if s3.tc.toNat = 0 then a3.tl0 else a3.tl1)
        (if s3.tc.toNat = 0 then a3.th0 else a3.th1) s3.tn.toNat =
          bv s.n_out.toNat (σ (2 * root.toNat)))
    (hm3 : (arCtxMem cx s3 ⋆ bytes s3.art artBytes ⋆
      array (t := i32) s3.rule_off ruleOff ⋆ array (t := i32) s3.rule_n ruleN ⋆
      array (t := i32) s3.partner partnerArr ⋆ rsMem s3 rsM rsL rsH rsPool ⋆
      a3.tMemOf s3 ⋆ a3.qMemOf s3 ⋆ R) m3)
    (hQ : ConeQ cx s artBytes ruleOff ruleN partnerArr rsM rsPool rsL rsH a0 Valid R Q) :
    wp Γ Q X (coneLoopExpr cx root k) m3 := by
  obtain ⟨σ0, hV0⟩ := hValEx
  have hRep0 := (hValRep σ0 hV0).2
  have hro_len : s.n_nets.toNat ≤ ruleOff.length := hRep0.1
  have hrn_len : s.n_nets.toNat ≤ ruleN.length := hRep0.2.1
  have hrsm_len : s.rs_cap.toNat ≤ rsM.length := hRep0.2.2.2.2.1
  have hrsl_len : s.rs_cap.toNat ≤ rsL.length := hRep0.2.2.2.2.2.1
  have hrsh_len : s.rs_cap.toNat ≤ rsH.length := hRep0.2.2.2.2.2.2.1
  dsimp only [coneLoopExpr, coneFindLoop, coneStepIgnore]
  refine wp_loop_group (fun rem ⟨_, i, ⟨⟩⟩ mL =>
      i.toNat ≤ k.toNat ∧ rem = k.toNat - i.toNat ∧
      ∃ (sL : ArCtxState) (aL : ConeArrs),
        let curPool := if sL.pc.toNat = 0 then aL.pool0 else aL.pool1
        let curTm := if sL.tc.toNat = 0 then aL.tm0 else aL.tm1
        let curTs := if sL.tc.toNat = 0 then aL.ts0 else aL.ts1
        let curTl := if sL.tc.toNat = 0 then aL.tl0 else aL.tl1
        let curTh := if sL.tc.toNat = 0 then aL.th0 else aL.th1
        sL.pc.toNat < 2 ∧ sL.tc.toNat < 2 ∧
        sL.tn.toNat ≤ s.tcap.toNat ∧ sL.ptop.toNat ≤ s.pcap.toNat ∧
        sL.pos.toNat ≤ s.nw.toNat ∧ ConeTQSame s sL ∧ ConeArrs.LenEq aL a0 ∧
        ((sL.ix = s.ix ∧ sL.ix2 = s.ix2) ∨ (sL.ix = s.ix2 ∧ sL.ix2 = s.ix)) ∧
        (∀ r < sL.tn.toNat,
          MonoSliceOk curPool (curTm.getD r 0#32).toNat sL.ptop.toNat ∧
          (curPool.getD (curTm.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        (∀ r < sL.tn.toNat, MonoSorted curPool (curTm.getD r 0#32).toNat) ∧
        SigOk curPool curTm curTs sL.tn.toNat ∧
        monoTotalWords curPool curTm sL.tn.toNat ≤ sL.ptop.toNat ∧
        (SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
          SymsBound curPool curTm sL.tn.toNat s.n_nets.toNat) ∧
        (∀ σ, Valid σ →
          polyEval s.n_out.toNat σ curPool curTm curTl curTh sL.tn.toNat =
            bv s.n_out.toNat (σ (2 * root.toNat))) ∧
        (arCtxMem cx sL ⋆ bytes sL.art artBytes ⋆
          array (t := i32) sL.rule_off ruleOff ⋆ array (t := i32) sL.rule_n ruleN ⋆
          array (t := i32) sL.partner partnerArr ⋆ rsMem sL rsM rsL rsH rsPool ⋆
          aL.tMemOf sL ⋆ aL.qMemOf sL ⋆ R) mL) ?_ ?_
  · intro J rem ⟨_okL, i, ⟨⟩⟩ mL hrec
      ⟨hi_le, _, sL, aL, hpcL, htcL, htnL, hptL, hposL, hsL, hlenL, hixL,
       hSlL, hSortedL, hSigL, hTotL, hSyL, hPolyL, hmL⟩
    have hsL_art : sL.art = s.art := by rw [hsL]
    have hsL_nw : sL.nw = s.nw := by rw [hsL]
    let RnwL : Mem 64 → Prop :=
      array (t := i32) sL.rule_off ruleOff ⋆ array (t := i32) sL.rule_n ruleN ⋆
      array (t := i32) sL.partner partnerArr ⋆ rsMem sL rsM rsL rsH rsPool ⋆
      aL.tMemOf sL ⋆ aL.qMemOf sL ⋆ R
    c0_hsteps_nogrp
    · have hi_lt : i.toNat < k.toNat := hc; clear hc
      have hip1 := bv32_add1_toNat (by omega : i.toNat + 1 < 2 ^ 32)
      dsimp only [Arg.val]; apply wp_call_of_spec
      refine hNW _ _ _ _ ⟨sL, artBytes, RnwL,
        by rw [hsL_art]; exact hart64, by rw [hsL_nw]; exact hnw4,
        sep_cast hmL (by dsimp only [RnwL]; ac_rfl),
        fun okV v sV mV hifV hmV => ?_⟩
      dsimp only [Arg.val] at hmV
      cases hokV : okV
      · rw [hokV] at hifV
        dsimp only
        refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
        c0_hstraight
        have hsV_eq : sV = sL := by
          by_cases hlt : sL.pos.toNat < sL.nw.toNat <;> simp only [hlt, ↓reduceIte] at hifV
          · cases hifV.1
          · exact hifV.2.2
        have hmV' : (arCtxMem cx sV ⋆ bytes sV.art artBytes ⋆ array (t := i32) sV.rule_off ruleOff ⋆
            array (t := i32) sV.rule_n ruleN ⋆ array (t := i32) sV.partner partnerArr ⋆
            rsMem sV rsM rsL rsH rsPool ⋆ aL.tMemOf sV ⋆ aL.qMemOf sV ⋆ R) mV := by
          rw [hsV_eq] at hmV ⊢; exact sep_cast hmV (by dsimp only [RnwL]; ac_rfl)
        exact hQ false sV ruleOff ruleN rsM rsL rsH rsPool aL mV
          (by rw [hsV_eq]; exact hpcL) (by rw [hsV_eq]; exact htcL)
          (by rw [hsV_eq, hsL]; exact hrsn_le) (by rw [hsV_eq, hsL]; exact hrspt_le)
          (fun _ => by rw [hsV_eq]; exact hposL) (by rw [hsV_eq, hsL])
          rfl rfl rfl rfl rfl rfl hlenL
          (by rw [show sV.ix = sL.ix by rw [hsV_eq], show sV.ix2 = sL.ix2 by rw [hsV_eq]]
              exact hixL)
          (fun h => by cases h) hmV'
      · rw [hokV] at hifV
        dsimp only
        refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
        have hpos_ltV : sL.pos.toNat < sL.nw.toNat := by
          by_cases hlt : sL.pos.toNat < sL.nw.toNat <;> simp only [hlt, ↓reduceIte] at hifV
          · exact hlt
          · cases hifV.1
        simp only [hpos_ltV, ↓reduceIte] at hifV
        rcases hifV with ⟨_, _, hsV_eq⟩
        have hsV_pos : sV.pos.toNat ≤ s.nw.toNat := by
          have := s.nw.isLt; rw [hsL_nw] at hpos_ltV
          rw [hsV_eq, hsL_nw, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]; omega
        have hsV_s : sV = { s with
            pos := sV.pos, tc := sL.tc, tn := sL.tn, pc := sL.pc,
            ptop := sL.ptop, qn := sL.qn, ix := sL.ix, ix2 := sL.ix2,
            cur_rm := sL.cur_rm, cur_rl := sL.cur_rl, cur_rh := sL.cur_rh,
            cur_rp := sL.cur_rp, cur_nr := sL.cur_nr } := by
          rw [hsV_eq, hsL]
        have hmV' : (arCtxMem cx sV ⋆ bytes sV.art artBytes ⋆ array (t := i32) sV.rule_off ruleOff ⋆
            array (t := i32) sV.rule_n ruleN ⋆ array (t := i32) sV.partner partnerArr ⋆
            rsMem sV rsM rsL rsH rsPool ⋆ aL.tMemOf sV ⋆ aL.qMemOf sV ⋆ R) mV := by
          dsimp only [RnwL] at hmV
          rw [cone_rbase_pos_eq (s := sL) (s' := sV) (by rw [hsV_eq])] at hmV
          rw [show sV.art = sL.art by rw [hsV_eq]]; exact sep_cast hmV (by ac_rfl)
        have hfailV : ∀ m' s', s' = { sV with
            cur_rm := s'.cur_rm, cur_rl := s'.cur_rl, cur_rh := s'.cur_rh,
            cur_rp := s'.cur_rp, cur_nr := s'.cur_nr } →
            (arCtxMem cx s' ⋆ bytes s'.art artBytes ⋆
              array (t := i32) s'.rule_off ruleOff ⋆ array (t := i32) s'.rule_n ruleN ⋆
              array (t := i32) s'.partner partnerArr ⋆ rsMem s' rsM rsL rsH rsPool ⋆
              aL.tMemOf s' ⋆ aL.qMemOf s' ⋆ R) m' →
            Q (false, ⟨⟩) m' := by
          intro m' s' hs' hm'
          exact hQ false s' ruleOff ruleN rsM rsL rsH rsPool aL m'
            (by rw [hs', hsV_s]; exact hpcL) (by rw [hs', hsV_s]; exact htcL)
            (by rw [hs', hsV_s]; exact hrsn_le) (by rw [hs', hsV_s]; exact hrspt_le)
            (fun _ => by rw [hs']; exact hsV_pos)
            (by rw [hs', hsV_s]) rfl rfl rfl rfl rfl rfl hlenL
            (by rw [show s'.ix = sL.ix by rw [hs', hsV_eq],
              show s'.ix2 = sL.ix2 by rw [hs', hsV_eq]]; exact hixL)
            (fun h => by cases h) hm'
        c0_hstraight
        c0_hstep
        · exact hfailV mV sV (by cases sV; rfl) hmV'
        · have hv_lt : v.toNat < s.n_nets.toNat := by
            have h1 : ¬ sV.n_nets.toNat ≤ v.toNat := hc
            have h2 : sV.n_nets.toNat = s.n_nets.toNat := by rw [hsV_s]
            omega
          have hv_rn : (BitVec.setWidth 64 v).toNat < ruleN.length := by
            rw [bv64_sw_toNat]; omega
          have hv_ro : (BitVec.setWidth 64 v).toNat < ruleOff.length := by
            rw [bv64_sw_toNat]; omega
          c0_hstraight
          c0_hstep
          · exact hfailV mV sV (by cases sV; rfl) hmV'
          · c0_hstraight
            c0_hstep
            · exact hfailV mV sV (by cases sV; rfl) hmV'
            c0_hstraight
            dsimp only
            c0_hstraight
            have hv_ne : ruleN.getD v.toNat 0#32 ≠ cNone32 := by
              rw [getD_eq_getElem ruleN 0#32 (by omega)]
              have h1 : ruleN[(BitVec.setWidth 64 v).toNat]'hv_rn ≠ 0xFFFFFFFF#32 := ‹_›
              simp only [bv64_sw_toNat] at h1; exact h1
            let off := ruleOff[(BitVec.setWidth 64 v).toNat]'hv_ro
            let cnt := ruleN[(BitVec.setWidth 64 v).toNat]'hv_rn
            have hoff_eq : off.toNat = (ruleOff.getD v.toNat 0#32).toNat := by
              dsimp only [off]
              rw [getD_eq_getElem ruleOff 0#32 (by omega)]; simp only [bv64_sw_toNat]
            have hcnt_eq : cnt.toNat = (ruleN.getD v.toNat 0#32).toNat := by
              dsimp only [cnt]
              rw [getD_eq_getElem ruleN 0#32 (by omega)]; simp only [bv64_sw_toNat]
            have hbd0 := (hRep0.2.2.2.2.2.2.2.2.2 v.toNat hv_lt hv_ne).1
            have hoff_lt_m : off.toNat ≤ rsM.length := by rw [hoff_eq]; omega
            have hoff_lt_l : off.toNat ≤ rsL.length := by rw [hoff_eq]; omega
            have hoff_lt_h : off.toNat ≤ rsH.length := by rw [hoff_eq]; omega
            have hoff_adr4 : BitVec.setWidth 64 off * 4#64 = BitVec.ofNat 64 (4 * off.toNat) := by
              apply BitVec.eq_of_toNat_eq
              simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_comm off.toNat 4]
            have hoff_adr8 : BitVec.setWidth 64 off * 8#64 = BitVec.ofNat 64 (8 * off.toNat) := by
              apply BitVec.eq_of_toNat_eq
              simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_comm off.toNat 8]
            have h2v_toNat : (2#32 * v).toNat = 2 * v.toNat := by
              rw [BitVec.toNat_mul, show (2#32 : BitVec 32).toNat = 2 from rfl,
                Nat.mod_eq_of_lt (by omega)]
            let sAp := { sV with
              cur_rm := sV.rs_m + BitVec.setWidth 64 off * 4#64,
              cur_rl := sV.rs_l + BitVec.setWidth 64 off * 8#64,
              cur_rh := sV.rs_h + BitVec.setWidth 64 off * 8#64,
              cur_rp := sV.rs_pool,
              cur_nr := cnt }
            have hsAp_s : sAp = { s with
                pos := sV.pos, tc := sL.tc, tn := sL.tn, pc := sL.pc,
                ptop := sL.ptop, qn := sL.qn, ix := sL.ix, ix2 := sL.ix2,
                cur_rm := sAp.cur_rm, cur_rl := sAp.cur_rl, cur_rh := sAp.cur_rh,
                cur_rp := sAp.cur_rp, cur_nr := sAp.cur_nr } := by
              dsimp only [sAp]; rw [hsV_s]
            have hValRepV : ∀ σ, Valid σ →
                RulesRep sV.n_out.toNat σ sV ruleOff ruleN rsM rsL rsH rsPool := fun σ hV => by
              rw [show sV.n_out = s.n_out by rw [hsV_s]]
              exact cone_rulesRep_eq (s := s) (s' := sV) (by rw [hsV_s]) (by rw [hsV_s])
                (by rw [hsV_s]) (by rw [hsV_s]) (by rw [hsV_s]) (hValRep σ hV).2
            have hcurR : ∀ σ, Valid σ → CurRRep sAp.n_out.toNat σ sAp.cur_nr.toNat
                (2#32 * v).toNat (rsM.drop off.toNat) (rsL.drop off.toNat)
                (rsH.drop off.toNat) rsPool := fun σ hV => by
              dsimp only [sAp]; rw [h2v_toNat, hcnt_eq, hoff_eq]
              exact curRRep_of_rulesRep_drop (hValRepV σ hV) (by rw [hsV_s]; exact hv_lt) hv_ne
            have hcurSorted : ∀ r < sAp.cur_nr.toNat,
                MonoSorted rsPool ((rsM.drop off.toNat).getD r 0#32).toNat := fun r hr => by
              dsimp only [sAp] at hr
              have hdrop : (rsM.drop off.toNat).getD r 0#32 = rsM.getD (off.toNat + r) 0#32 := by
                simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
              rw [hdrop]; exact hRsSorted _ (by omega)
            have hcurOk : ∀ r < sAp.cur_nr.toNat,
                (rsPool.getD ((rsM.drop off.toNat).getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 :=
              fun r hr => by
              dsimp only [sAp] at hr
              have hdrop : (rsM.drop off.toNat).getD r 0#32 = rsM.getD (off.toNat + r) 0#32 := by
                simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
              rw [hdrop]; exact hRsOk _ (by omega)
            have hcurTot : monoTotalWords rsPool (rsM.drop off.toNat) sAp.cur_nr.toNat ≤
                4000000000 := by
              dsimp only [sAp]
              have h1 := monoTotalWords_drop_le (pool := rsPool) (rsM := rsM)
                (off := off.toNat) (cnt := cnt.toNat) (n := s.rs_n.toNat) (by omega)
              omega
            dsimp only [Arg.val] at hm
            rw [show (4 : BitVec 64) = 4#64 from rfl, show (8 : BitVec 64) = 8#64 from rfl,
              show (ruleOff[(BitVec.setWidth 64 v).toNat]'hv_ro) = off from rfl,
              show (ruleN[(BitVec.setWidth 64 v).toNat]'hv_rn) = cnt from rfl,
              show ({ sV with
                cur_rm := sV.rs_m + BitVec.setWidth 64 off * 4#64,
                cur_rl := sV.rs_l + BitVec.setWidth 64 off * 8#64,
                cur_rh := sV.rs_h + BitVec.setWidth 64 off * 8#64,
                cur_rp := sV.rs_pool, cur_nr := cnt } : ArCtxState) = sAp from rfl] at hm
            have hqAp : aL.qMemOf sV = aL.qMemOf sAp :=
              cone_qMem_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            have htAp : aL.tMemOf sV = aL.tMemOf sAp := by simp only [tMem]; rfl
            have hrsAp : rsMem sV rsM rsL rsH rsPool = rsMem sAp rsM rsL rsH rsPool := by
              simp only [rsMem]; rfl
            rw [show sV.art = sAp.art from rfl, show sV.rule_off = sAp.rule_off from rfl,
              show sV.rule_n = sAp.rule_n from rfl, show sV.partner = sAp.partner from rfl,
              hrsAp, hqAp, htAp] at hm
            have hsAp_s' : ConeTQSame s sAp := by rw [hsAp_s]
            dsimp only [Arg.val]
            refine cone_apply_step hApply (by rw [hsAp_s]; exact hpcL) (by rw [hsAp_s]; exact htcL)
              (by rw [hsAp_s]; exact htnL) htcap30 hqcap16 hqcap32
              (by rw [hsAp_s]; exact hptL) hpcap32 hnnets30 h2nnets32 hrsn_le hrspt_le
              (by rw [hsAp_s]; exact hsV_pos) hsAp_s' hoff_lt_m hoff_lt_l hoff_lt_h
              (by dsimp only [sAp]; rw [show sV.rs_m = s.rs_m by rw [hsV_s], hoff_adr4])
              (by dsimp only [sAp]; rw [show sV.rs_l = s.rs_l by rw [hsV_s], hoff_adr8])
              (by dsimp only [sAp]; rw [show sV.rs_h = s.rs_h by rw [hsV_s], hoff_adr8])
              (by dsimp only [sAp]; rw [hsV_s])
              hcap0 hlenL
              hmasks ⟨σ0, hV0⟩ (fun σ hV => (hValRep σ hV).1) hcurR hcurSorted hcurOk hcurTot
              (fun r hr => by
                rw [show sAp.pc = sL.pc by rw [hsAp_s], show sAp.tc = sL.tc by rw [hsAp_s],
                  show sAp.ptop = sL.ptop by rw [hsAp_s]]
                exact hSlL r (by rw [show sL.tn = sAp.tn by rw [hsAp_s]]; exact hr))
              (fun r hr => by
                rw [show sAp.pc = sL.pc by rw [hsAp_s], show sAp.tc = sL.tc by rw [hsAp_s]]
                exact hSortedL r (by rw [show sL.tn = sAp.tn by rw [hsAp_s]]; exact hr))
              (by rw [show sAp.pc = sL.pc by rw [hsAp_s], show sAp.tc = sL.tc by rw [hsAp_s],
                    show sAp.tn = sL.tn by rw [hsAp_s]]; exact hSigL)
              (by rw [hsAp_s]; exact hTotL)
              (by rw [show sAp.pc = sL.pc by rw [hsAp_s], show sAp.tc = sL.tc by rw [hsAp_s],
                    show sAp.tn = sL.tn by rw [hsAp_s]]; exact hSyL)
              (fun hSb r hr x hx => by
                dsimp only [sAp] at hr
                rw [hcnt_eq] at hr
                have hdrop : (rsM.drop off.toNat).getD r 0#32 = rsM.getD (off.toNat + r) 0#32 := by
                  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
                rw [hdrop] at hx
                exact hSb (off.toNat + r) (by omega) x hx)
              (by rw [show sAp.ix = sL.ix by rw [hsAp_s, hsL],
                show sAp.ix2 = sL.ix2 by rw [hsAp_s, hsL]]; exact hixL)
              (sep_cast hm (by simp only [ExtHashMap.sep_emp]; ac_rfl))
              (fun sA aA mA hpcA htcA htnA hptA hposA hsA_s hlenA hixA_s
                hSlA hSortedA hSigA hTotA hSyA hPolyA hmA => by
                c0_hstraight
                refine hrec (k.toNat - (i + 1).toNat) (true, i + 1, ⟨⟩) mA (by omega)
                  ⟨by omega, rfl, sA, aA, hpcA, htcA, htnA, hptA, hposA, hsA_s, hlenA, hixA_s,
                   hSlA, hSortedA, hSigA, hTotA, hSyA, fun σ hV => ?_, hmA⟩
                have hP := hPolyA σ hV
                rw [show sAp.n_out = s.n_out by rw [hsAp_s],
                  show sAp.pc = sL.pc by rw [hsAp_s], show sAp.tc = sL.tc by rw [hsAp_s],
                  show sAp.tn = sL.tn by rw [hsAp_s]] at hP
                exact hP.trans (hPolyL σ hV)) hQ
    · exact cone_store_step hStore hpcL htcL htnL hposL hptL hsL hixL
        htcap30 hpcap32 hrcap30 hrpcap32 hroot_lt hcap0 hlenL
        hTotWords hRsOk hRsSorted ⟨σ0, hV0⟩ hValRep hSlL hSortedL hTotL hSyL hPolyL hmL hQ
  · intro J hJ; c0_hstraight
    refine hJ k.toNat (true, 0#32, ⟨⟩) m3 ⟨Nat.zero_le _, Nat.sub_zero _, s3, a3,
      by rw [hs3_s]; exact hpc, by rw [hs3_s]; exact htc,
      by rw [hs3_s]; exact htn3, by rw [hs3_s]; exact hpt3,
      by rw [hs3_s]; exact hpos3, by rw [hs3_s], hlen3,
      Or.inl ⟨by rw [hs3_s], by rw [hs3_s]⟩,
      hSl3, hSorted3, hSig3, hTot3, hSy3, hPoly3, hm3⟩

theorem ar_do_cone_wp (Γ : LeanQbe.T.Env)
    (hNW : ∀ xs m Q X, arNextWordSpec xs m Q X →
      Γ "ar_next_word" [i64] [.bool, i32] xs m Q X)
    (hLoad : ∀ xs m Q X, arLoadRuleSpec xs m Q X →
      Γ "ar_load_rule" [i64, i32] [.bool] xs m Q X)
    (hApply : ∀ xs m Q X, arApplySpec xs m Q X →
      Γ "ar_apply" [i64, i32] [.bool] xs m Q X)
    (hStore : ∀ xs m Q X, arStoreRuleSpec xs m Q X →
      Γ "ar_store_rule" [i64, i32] [.bool] xs m Q X) :
    ∀ xs m Q X, arDoConeSpec xs m Q X → Func.wp Γ ar_do_cone_body xs m Q X := by
  rintro ⟨cx, ⟨⟩⟩ m Q X
    ⟨s, artBytes, ruleOff, ruleN, partnerArr, rsM, rsL, rsH, rsPool,
     tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1,
     qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip, Valid, R,
     hpc, htc, htcap30, hqcap16, hqcap32, hpcap32, hrcap30, hrpcap32, hrpcap4g,
     hnnets30, h2nnets32, hart64, hnw4,
     htm0_l, htm1_l, hts0_l, htl0_l, hth0_l, hts1_l, htl1_l, hth1_l, hp0_l, hp1_l,
     hqm_l, hqs_l, hql_l, hqh_l, hix_l, hix2_l, hix_eq, htbx_l, hbx_l, hvqo_l, hvq_l, hvqs_l,
     hmasks, hTot, hRsOk, hRsSorted, hValEx, hValRep, hm, hQ⟩
  obtain ⟨σ0, hV0⟩ := hValEx
  have hRep0 := (hValRep σ0 hV0).2
  have hrsn_le : s.rs_n.toNat ≤ s.rs_cap.toNat := hRep0.2.2.1
  have hrspt_le : s.rs_ptop.toNat ≤ s.rs_pcap.toNat := hRep0.2.2.2.1
  have hrn_len : s.n_nets.toNat ≤ ruleN.length := hRep0.2.1
  let a0 : ConeArrs := ⟨tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1,
    qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip⟩
  have hcap0 : ConeArrs.CapOk s a0 :=
    ⟨htm0_l, htm1_l, hts0_l, htl0_l, hth0_l, hts1_l, htl1_l, hth1_l, hp0_l, hp1_l,
     hqs_l, hql_l, hqh_l, hqm_l, hix_l, hix2_l, hbx_l, hvqo_l, hvq_l, hvqs_l, htbx_l, hix_eq⟩
  let Rbase : Mem 64 → Prop :=
    array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
    array (t := i32) s.partner partnerArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
    a0.tMemOf s ⋆ a0.qMemOf s ⋆ R
  let hQ' : ConeQ cx s artBytes ruleOff ruleN partnerArr rsM rsPool rsL rsH a0 Valid R Q :=
    fun ok s' ro' rn' rm' rl' rh' rp' a' m' a b c d e f g h i j k l hl hix =>
    hQ ok s' ro' rn' rm' rl' rh' rp' a'.tm0 a'.tm1 a'.ts0 a'.tl0 a'.th0 a'.ts1 a'.tl1 a'.th1
      a'.pool0 a'.pool1 a'.qm a'.qs a'.ql a'.qh a'.ix a'.ix2 a'.bx a'.vqOff a'.vq a'.vqSkip m'
      a b c d e f g h i j k l
      hl.1 hl.2.1 hl.2.2.1 hl.2.2.2.1 hl.2.2.2.2.1 hl.2.2.2.2.2.1 hl.2.2.2.2.2.2.1
      hl.2.2.2.2.2.2.2.1 hl.2.2.2.2.2.2.2.2.1 hl.2.2.2.2.2.2.2.2.2.1
      hl.2.2.2.2.2.2.2.2.2.2.1 hl.2.2.2.2.2.2.2.2.2.2.2.1
      hl.2.2.2.2.2.2.2.2.2.2.2.2.1 hl.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hix
      hl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  c0_hsteps_nogrp
  dsimp only [Arg.val]; apply wp_call_of_spec
  refine hNW _ _ _ _ ⟨s, artBytes, Rbase, hart64, hnw4,
    sep_cast hm (by dsimp only [Rbase, ConeArrs.tMemOf, ConeArrs.qMemOf]; ac_rfl),
    fun ok1 root s1 m1 hif1 hm1 => ?_⟩
  cases hok1 : ok1
  · rw [hok1] at hif1
    dsimp only
    refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
    c0_hstraight
    have hs1_eq : s1 = s := by
      by_cases hlt : s.pos.toNat < s.nw.toNat <;> simp only [hlt, ↓reduceIte] at hif1
      · cases hif1.1
      · exact hif1.2.2
    have hm1' : (arCtxMem cx s1 ⋆ bytes s1.art artBytes ⋆ array (t := i32) s1.rule_off ruleOff ⋆
        array (t := i32) s1.rule_n ruleN ⋆ array (t := i32) s1.partner partnerArr ⋆
        rsMem s1 rsM rsL rsH rsPool ⋆ tMem s1 tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s1 qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m1 := by
      rw [hs1_eq] at hm1 ⊢
      exact sep_cast hm1 (by dsimp only [Rbase, ConeArrs.tMemOf, ConeArrs.qMemOf]; ac_rfl)
    refine hQ' false s1 ruleOff ruleN rsM rsL rsH rsPool a0 m1
      (by rw [hs1_eq]; exact hpc) (by rw [hs1_eq]; exact htc)
      (by rw [hs1_eq]; exact hrsn_le) (by rw [hs1_eq]; exact hrspt_le)
      (fun h => by rw [hs1_eq]; exact h) (by rw [hs1_eq]) rfl rfl rfl rfl rfl rfl
      (coneArrs_lenEq_refl a0) (Or.inl ⟨by rw [hs1_eq], by rw [hs1_eq]⟩)
      (fun h => by cases h) hm1'
  · rw [hok1] at hif1
    dsimp only
    refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
    have hpos_lt1 : s.pos.toNat < s.nw.toNat := by
      by_cases hlt : s.pos.toNat < s.nw.toNat <;> simp only [hlt, ↓reduceIte] at hif1
      · exact hlt
      · cases hif1.1
    simp only [hpos_lt1, ↓reduceIte] at hif1
    rcases hif1 with ⟨_, _, hs1_eq⟩
    have hs1_pos : s1.pos.toNat ≤ s.nw.toNat := by
      have := s.nw.isLt
      rw [hs1_eq, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]; omega
    have hs1_art : s1.art = s.art := by rw [hs1_eq]
    have hs1_nw : s1.nw = s.nw := by rw [hs1_eq]
    have hm1' : (arCtxMem cx s1 ⋆ bytes s1.art artBytes ⋆ Rbase) m1 := by
      rw [hs1_art]; exact hm1
    c0_hstraight
    apply wp_call_of_spec
    refine hNW _ _ _ _ ⟨s1, artBytes, Rbase,
      by rw [hs1_art]; exact hart64, by rw [hs1_nw]; exact hnw4, hm1',
      fun ok2 k s2 m2 hif2 hm2 => ?_⟩
    cases hok2 : ok2
    · rw [hok2] at hif2
      dsimp only
      refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
      c0_hstraight
      have hs2_eq : s2 = s1 := by
        by_cases hlt : s1.pos.toNat < s1.nw.toNat <;> simp only [hlt, ↓reduceIte] at hif2
        · cases hif2.1
        · exact hif2.2.2
      have hs2_s : s2 = { s with pos := s2.pos } := by rw [hs2_eq, hs1_eq]
      dsimp only [Rbase] at hm2
      rw [hs1_art, cone_rbase_pos_eq (s := s) (s' := s2) hs2_s] at hm2
      have hm2' : (arCtxMem cx s2 ⋆ bytes s2.art artBytes ⋆ array (t := i32) s2.rule_off ruleOff ⋆
          array (t := i32) s2.rule_n ruleN ⋆ array (t := i32) s2.partner partnerArr ⋆
          rsMem s2 rsM rsL rsH rsPool ⋆ tMem s2 tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
          qMem s2 qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m2 := by
        rw [show s2.art = s.art by rw [hs2_s]]
        exact sep_cast hm2 (by dsimp only [ConeArrs.tMemOf, ConeArrs.qMemOf]; ac_rfl)
      refine hQ' false s2 ruleOff ruleN rsM rsL rsH rsPool a0 m2
        (by rw [hs2_s]; exact hpc) (by rw [hs2_s]; exact htc)
        (by rw [hs2_s]; exact hrsn_le) (by rw [hs2_s]; exact hrspt_le)
        (fun _ => by rw [hs2_eq]; exact hs1_pos)
        (by rw [hs2_s]) rfl rfl rfl rfl rfl rfl (coneArrs_lenEq_refl a0)
        (Or.inl ⟨by rw [hs2_s], by rw [hs2_s]⟩) (fun h => by cases h) hm2'
    · rw [hok2] at hif2
      dsimp only
      refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
      have hpos_lt2 : s1.pos.toNat < s1.nw.toNat := by
        by_cases hlt : s1.pos.toNat < s1.nw.toNat <;> simp only [hlt, ↓reduceIte] at hif2
        · exact hlt
        · cases hif2.1
      simp only [hpos_lt2, ↓reduceIte] at hif2
      rcases hif2 with ⟨_, _, hs2_eq⟩
      have hs2_s : s2 = { s with pos := s2.pos } := by rw [hs2_eq, hs1_eq]
      have hs2_pos : s2.pos.toNat ≤ s.nw.toNat := by
        have := s.nw.isLt
        rw [hs1_nw] at hpos_lt2
        rw [hs2_eq, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]; omega
      rw [hs1_art] at hm2
      have hm2_s : (arCtxMem cx s2 ⋆ bytes s.art artBytes ⋆ Rbase) m2 := hm2
      have hfail2 : (arCtxMem cx s2 ⋆ bytes s2.art artBytes ⋆ array (t := i32) s2.rule_off ruleOff ⋆
          array (t := i32) s2.rule_n ruleN ⋆ array (t := i32) s2.partner partnerArr ⋆
          rsMem s2 rsM rsL rsH rsPool ⋆ tMem s2 tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
          qMem s2 qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m2 :=
        sep_cast hm2_s (by
          dsimp only [Rbase]
          rw [cone_rbase_pos_eq (s := s) (s' := s2) hs2_s, show s2.art = s.art by rw [hs2_s]]
          dsimp only [ConeArrs.tMemOf, ConeArrs.qMemOf]
          ac_rfl)
      have hs2_ret : ConeSame s s2 := by rw [hs2_s]
      have hq_fail2 : Q (false, ⟨⟩) m2 :=
        hQ' false s2 ruleOff ruleN rsM rsL rsH rsPool a0 m2
          (by rw [hs2_s]; exact hpc) (by rw [hs2_s]; exact htc)
          (by rw [hs2_s]; exact hrsn_le) (by rw [hs2_s]; exact hrspt_le) (fun _ => hs2_pos)
          hs2_ret rfl rfl rfl rfl rfl rfl (coneArrs_lenEq_refl a0)
          (Or.inl ⟨by rw [hs2_s], by rw [hs2_s]⟩) (fun h => by cases h) hfail2
      c0_hsteps_nogrp
      · exact hq_fail2
      · have hroot_lt : root.toNat < s.n_nets.toNat := by
          have h1 : ¬ s2.n_nets.toNat ≤ root.toNat := hc
          have h2 : s2.n_nets.toNat = s.n_nets.toNat := by rw [hs2_s]
          omega
        have hroot_rn : (BitVec.setWidth 64 root).toNat < ruleN.length := by
          rw [bv64_sw_toNat]; omega
        c0_hsteps_nogrp
        · exact hq_fail2
        · exact hq_fail2
        · refine hQ' true s2 ruleOff ruleN rsM rsL rsH rsPool a0 m2
            (by rw [hs2_s]; exact hpc) (by rw [hs2_s]; exact htc)
            (by rw [hs2_s]; exact hrsn_le) (by rw [hs2_s]; exact hrspt_le) (fun _ => hs2_pos)
            hs2_ret rfl rfl rfl rfl rfl rfl (coneArrs_lenEq_refl a0)
            (Or.inl ⟨by rw [hs2_s], by rw [hs2_s]⟩) (fun _ =>
              ⟨by rw [show s2.rs_n = s.rs_n by rw [hs2_s],
                 show s2.rs_ptop = s.rs_ptop by rw [hs2_s]]; exact hTot,
               (by rw [show s2.rs_n = s.rs_n by rw [hs2_s]]; exact id),
               fun i hi => by rw [show s2.rs_n = s.rs_n by rw [hs2_s]] at hi; exact hRsOk i hi,
               by rw [show s2.rs_n = s.rs_n by rw [hs2_s]]; exact hRsSorted,
               fun σ hV => by
                 rw [show s2.n_out = s.n_out by rw [hs2_s]]
                 exact cone_rulesRep_eq (s := s) (s' := s2) (by rw [hs2_s]) (by rw [hs2_s])
                   (by rw [hs2_s]) (by rw [hs2_s]) (by rw [hs2_s]) (hValRep σ hV).2⟩) hfail2
        · have hroot_ne : ruleN.getD root.toNat 0#32 ≠ cNone32 := by
            rw [getD_eq_getElem ruleN 0#32 (by omega)]
            have h1 : ruleN[(BitVec.setWidth 64 root).toNat]'hroot_rn ≠ 0xFFFFFFFF#32 := ‹_›
            simpa only [bv64_sw_toNat, cNone32] using h1
          have hk_le_rem : k.toNat ≤ s.nw.toNat - s2.pos.toNat := by
            have hsub : (s2.nw - s2.pos).toNat = s.nw.toNat - s2.pos.toNat := by
              rw [show s2.nw = s.nw by rw [hs2_s]]
              exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr hs2_pos)
            have h1 : ¬ (s2.nw - s2.pos).toNat < (BitVec.setWidth 64 k).toNat := ‹_›
            rw [bv64_sw_toNat, hsub] at h1; omega
          let Rload : Mem 64 → Prop := bytes s.art artBytes ⋆
            array (t := i32) s.partner partnerArr ⋆
            qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R
          have hm2_load : (arCtxMem cx s2 ⋆ array (t := i32) s2.rule_off ruleOff ⋆
              array (t := i32) s2.rule_n ruleN ⋆ rsMem s2 rsM rsL rsH rsPool ⋆
              tMem s2 tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ Rload) m2 := by
            dsimp only [Rbase] at hm2_s
            rw [cone_rbase_pos_eq (s := s) (s' := s2) hs2_s,
              show s.art = s2.art by rw [hs2_s]] at hm2_s
            dsimp only [Rload]
            rw [show s.art = s2.art by rw [hs2_s], show s.partner = s2.partner by rw [hs2_s],
              cone_qMem_eq (s := s2) (s' := s) (by rw [hs2_s]) (by rw [hs2_s]) (by rw [hs2_s])
                (by rw [hs2_s]) (by rw [hs2_s]) (by rw [hs2_s]) (by rw [hs2_s]) (by rw [hs2_s])
                (by rw [hs2_s]) (by rw [hs2_s])]
            exact sep_cast hm2_s (by dsimp only [ConeArrs.tMemOf, ConeArrs.qMemOf]; ac_rfl)
          have hValRep2 : ∀ σ, Valid σ →
              RulesRep s2.n_out.toNat σ s2 ruleOff ruleN rsM rsL rsH rsPool := fun σ hV => by
            rw [show s2.n_out = s.n_out by rw [hs2_s]]
            exact cone_rulesRep_eq (s := s) (s' := s2) (by rw [hs2_s]) (by rw [hs2_s])
              (by rw [hs2_s]) (by rw [hs2_s]) (by rw [hs2_s]) (hValRep σ hV).2
          apply wp_call_of_spec
          refine hLoad _ _ _ _ ⟨s2, ruleOff, ruleN, rsM, rsL, rsH, rsPool,
            tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1, Valid, Rload,
            by rw [hs2_s]; exact hpc, by rw [hs2_s]; exact htc,
            by rw [hs2_s]; exact hroot_lt, hroot_ne,
            by rw [hs2_s]; exact htcap30, by rw [hs2_s]; exact hpcap32,
            by rw [hs2_s]; exact hrpcap32,
            by rw [hs2_s]; exact htm0_l, by rw [hs2_s]; exact htm1_l,
            by rw [hs2_s]; exact hts0_l, by rw [hs2_s]; exact htl0_l, by rw [hs2_s]; exact hth0_l,
            by rw [hs2_s]; exact hts1_l, by rw [hs2_s]; exact htl1_l, by rw [hs2_s]; exact hth1_l,
            by rw [hs2_s]; exact hp0_l, by rw [hs2_s]; exact hp1_l,
            ⟨σ0, hV0⟩, hValRep2, by rw [hs2_s]; exact hRsSorted,
            by rw [hs2_s]; exact hRsOk, hm2_load,
            fun okL s3 tm0_3 tm1_3 ts0_3 tl0_3 th0_3 ts1_3 tl1_3 th1_3 pool0_3 pool1_3 m3
              htn3 hpt3 hs3_eq htm0_3 htm1_3 hts0_3 htl0_3 hth0_3 hts1_3 htl1_3 hth1_3
              hp0_3 hp1_3 hokL hm3 => ?_⟩
          have hs3_s : s3 = { s with pos := s2.pos, tn := s3.tn, ptop := s3.ptop, qn := 0#32 } :=
            by rw [hs3_eq, hs2_s]
          have hm3_norm : (arCtxMem cx s3 ⋆ bytes s3.art artBytes ⋆
              array (t := i32) s3.rule_off ruleOff ⋆ array (t := i32) s3.rule_n ruleN ⋆
              array (t := i32) s3.partner partnerArr ⋆ rsMem s3 rsM rsL rsH rsPool ⋆
              tMem s3 tm0_3 tm1_3 ts0_3 tl0_3 th0_3 ts1_3 tl1_3 th1_3 pool0_3 pool1_3 ⋆
              qMem s3 qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m3 := by
            have hq3 := cone_qMem_eq (s := s) (s' := s3) (qm := qm) (qs := qs) (ql := ql) (qh := qh)
              (ix := ix) (ix2 := ix2) (bx := bx) (vqOff := vqOff) (vq := vq) (vqSkip := vqSkip)
              (by rw [hs3_s]) (by rw [hs3_s]) (by rw [hs3_s]) (by rw [hs3_s]) (by rw [hs3_s])
              (by rw [hs3_s]) (by rw [hs3_s]) (by rw [hs3_s]) (by rw [hs3_s]) (by rw [hs3_s])
            dsimp only [Rload] at hm3
            rw [show s3.partner = s.partner by rw [hs3_s], hq3,
              show s3.art = s.art by rw [hs3_s]]
            exact sep_cast hm3 (by ac_rfl)
          cases hokL_b : okL
          · dsimp only
            refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
            c0_hstraight
            let a3 : ConeArrs := ⟨tm0_3, tm1_3, ts0_3, tl0_3, th0_3, ts1_3, tl1_3, th1_3,
              pool0_3, pool1_3, qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip⟩
            have hlen3 : ConeArrs.LenEq a3 a0 :=
              ⟨htm0_3, htm1_3, hts0_3, htl0_3, hth0_3, hts1_3, htl1_3, hth1_3, hp0_3, hp1_3,
               rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            exact hQ' false s3 ruleOff ruleN rsM rsL rsH rsPool a3 m3
              (by rw [hs3_s]; exact hpc) (by rw [hs3_s]; exact htc)
              (by rw [hs3_s]; exact hrsn_le) (by rw [hs3_s]; exact hrspt_le)
              (fun _ => by rw [hs3_s]; exact hs2_pos) (by rw [hs3_s]) rfl rfl rfl rfl rfl rfl
              hlen3 (Or.inl ⟨by rw [hs3_s], by rw [hs3_s]⟩) (fun h => by cases h) hm3_norm
          · dsimp only
            refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
            obtain ⟨hSl3, hSorted3, hSig3, hTot3, hSy3, hPoly3⟩ := hokL hokL_b
            c0_hstraight
            change wp Γ Q X (coneLoopExpr cx root k) m3
            have hs3_pos : s3.pos = s2.pos := by rw [hs3_s]
            have hs3_loop : s3 = { s with
                pos := s3.pos, tn := s3.tn, ptop := s3.ptop, qn := 0#32 } := by
              rw [hs3_pos]; exact hs3_s
            let a3 : ConeArrs := ⟨tm0_3, tm1_3, ts0_3, tl0_3, th0_3, ts1_3, tl1_3, th1_3,
              pool0_3, pool1_3, qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip⟩
            have hlen3 : ConeArrs.LenEq a3 a0 :=
              ⟨htm0_3, htm1_3, hts0_3, htl0_3, hth0_3, hts1_3, htl1_3, hth1_3, hp0_3, hp1_3,
               rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            exact ar_do_cone_loop_wp hNW hApply hStore hpc htc htcap30 hqcap16 hqcap32 hpcap32
              hrcap30 hrpcap32 hnnets30 h2nnets32 hart64 hnw4 hroot_lt hrsn_le hrspt_le
              (by rw [hs3_s]; exact hk_le_rem) (by rw [hs3_s]; exact hs2_pos) hs3_loop
              (by rw [show s2.tcap = s.tcap by rw [hs2_s]] at htn3; exact htn3)
              (by rw [show s2.pcap = s.pcap by rw [hs2_s]] at hpt3; exact hpt3)
              hcap0 hlen3 hmasks hrpcap4g hTot hRsOk hRsSorted ⟨σ0, hV0⟩ hValRep
              hSl3 hSorted3 hSig3 hTot3 (fun hSb => hSy3 s.n_nets.toNat (by
                rw [show s2.rs_n = s.rs_n by rw [hs2_s]]; exact hSb))
              (fun σ hV => by rw [show s.n_out = s2.n_out by rw [hs2_s]]; exact hPoly3 σ hV)
              hm3_norm hQ'

end

end LeanQbe.T.Examples.Arisca.Proof
