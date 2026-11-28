/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Driver1GateBase
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import Kraken.Separation

/-!
# ARiSCA Gate Validator WP Proof (`Arisca.Proof.Driver1Gate`)

Proves `ar_do_gate_wp` against `arDoGateSpec` using staged WP phase lemmas
(`ar_do_gate_vso_wp`, `ar_do_gate_tail_wp`, `ar_do_gate_nl_wp`, `ar_do_gate_wp`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca (Aig)
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Driver

@[expose] public section

@[reducible] def gateAfterKind (cx : Val i64) (kraw : Val i32) : Expr Val Cont [.bool] :=
  match ar_do_gate_body Val Cont (cx, ()) with
  | @Expr.call _ _ _ _ _ [.bool, .bits 32] _ k1 =>
    match k1 (true, kraw, ()) with
    | .jnz _ (@Expr.let_ _ _ _ [.bits 32] (.mk (.and (.bits 32)) (ka, kb, ())) kkind) _ =>
      match kkind (ka.val &&& kb.val, ()) with
      | @Expr.let_ _ _ _ [.bits 32] (.mk (.lshr (.bits 32)) (la, lb, ())) klshr =>
        match klshr (la.val >>> lb.val.toNat, ()) with
        | @Expr.let_ _ _ _ [.bits 32] (.mk (.and (.bits 32)) (ea, eb, ())) kexpl =>
          kexpl (ea.val &&& eb.val, ())
        | e => e
      | e => e
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

inductive GateStepT where
  | jnzT | jnzF | grp0
  | grp32 (v : Val i32)
  | grp64 (v : Val i64)
  | grpB32 (ok : Val .bool) (v : Val i32)

@[reducible] def runFastT : List GateStepT → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | [], e => e
  | .jnzT :: ss, e => match fastToJnz 12 e with | .jnz _ t _ => runFastT ss t | _ => e
  | .jnzF :: ss, e => match fastToJnz 12 e with | .jnz _ _ f => runFastT ss f | _ => e
  | .grp0 :: ss, e => match fastToGrp 12 e with
    | .group (sig := [[]]) b _ => runFastT ss (Blocks.get (b ((fun _ _ => False), ())) .here ())
    | _ => e
  | .grp32 v :: ss, e => match fastToGrp 12 e with
    | .group (sig := [[.bits 32]]) b _ =>
      runFastT ss (Blocks.get (b ((fun _ _ => False), ())) .here (v, ()))
    | _ => e
  | .grp64 v :: ss, e => match fastToGrp 12 e with
    | .group (sig := [[.bits 64]]) b _ =>
      runFastT ss (Blocks.get (b ((fun _ _ => False), ())) .here (v, ()))
    | _ => e
  | .grpB32 ok v :: ss, e => match fastToGrp 12 e with
    | .group (sig := [[.bool, .bits 32]]) b _ =>
      runFastT ss (Blocks.get (b ((fun _ _ => False), ())) .here (ok, v, ()))
    | _ => e

@[reducible] def gateInExpr (cx : Val i64) (kraw nout nin : Val i32) :
    Expr Val Cont [.bool] :=
  runFastT [.jnzF, .jnzF, .jnzF, .grp32 nout, .grp32 nin,
    .grpB32 true 0#32, .jnzF, .grp0] (gateAfterKind cx kraw)

@[reducible] def gateNlExpr (cx : Val i64) (kraw nout nin : Val i32) :
    Expr Val Cont [.bool] :=
  runFastT [.jnzF, .jnzF, .jnzF, .grp32 nout, .grp32 nin,
    .grpB32 true 0#32, .jnzF, .grp0, .grpB32 true 0#32, .jnzF] (gateAfterKind cx kraw)

@[reducible] def gateLmaskExpr (cx : Val i64) (ok : Val .bool)
    (kraw nout nin nl : Val i32) : Expr Val Cont [.bool] :=
  runFastT [.jnzF, .jnzF, .jnzF, .grp32 nout, .grp32 nin, .grpB32 true 0#32, .jnzF, .grp0,
    .grpB32 true 0#32, .jnzF, .grpB32 ok nl] (gateAfterKind cx kraw)

@[reducible] def gateTailExpr (cx : Val i64) (ok : Val .bool)
    (kraw nout nin nl : Val i32) (all : Val i64) : Expr Val Cont [.bool] :=
  runFastT [.jnzF, .jnzF, .jnzF, .grp32 nout, .grp32 nin, .grpB32 true 0#32, .jnzF, .grp0,
    .grpB32 true 0#32, .jnzF, .grpB32 false nl, .grp64 all, .grpB32 ok 0#32, .jnzF]
    (gateAfterKind cx kraw)

@[reducible] def gateTtoExpr (cx : Val i64) (ok : Val .bool)
    (kraw nout nin nl : Val i32) (all : Val i64) : Expr Val Cont [.bool] :=
  runFastT [.jnzF, .jnzF, .jnzF, .grp32 nout, .grp32 nin, .grpB32 true 0#32, .jnzF, .grp0,
    .grpB32 true 0#32, .jnzF, .grpB32 false nl, .grp64 all, .grpB32 false 0#32, .jnzF,
    .grpB32 ok 0#32, .jnzF] (gateAfterKind cx kraw)

end

public section

private theorem gate_ctx_ok {cx : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (arCtxMem cx s ⋆ R) m) : ArCtxLengthsOk s :=
  (sep_pure_l.mp h).1

private theorem gate_mem_same_rw {cx : BitVec 64} {s sC : ArCtxState} (hs : GateSame s sC)
    {artBytes : List UInt8} {rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {inNetArr outRefArr stkN stkP memoN : List (BitVec 32)}
    {memoV dense : List (BitVec 64)} {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)}
    {rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)}
    {R : Mem 64 → Prop} :
    (arCtxMem cx sC ⋆ bytes sC.art artBytes ⋆ aigArraysMem sC rhs0 rhs1 olit ⋆
      netTablesMem sC bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
      gateScratchMem sC stkN stkP memoN memoV dense gsy gcl gch ⋆
      rsMem sC rsM rsL rsH rsPool ⋆ R) =
    (arCtxMem cx sC ⋆ bytes s.art artBytes ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
      netTablesMem s bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
      gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆
      rsMem s rsM rsL rsH rsPool ⋆ R) := by
  have hsm := gate_same_mem_eq hs artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr
    flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool
  have h := congrArg (fun p => arCtxMem cx sC ⋆ p ⋆ R) hsm
  have hL : (arCtxMem cx sC ⋆ bytes sC.art artBytes ⋆ aigArraysMem sC rhs0 rhs1 olit ⋆
      netTablesMem sC bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
      gateScratchMem sC stkN stkP memoN memoV dense gsy gcl gch ⋆ rsMem sC rsM rsL rsH rsPool ⋆ R) =
      (arCtxMem cx sC ⋆ (bytes sC.art artBytes ⋆ aigArraysMem sC rhs0 rhs1 olit ⋆
        netTablesMem sC bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
        gateScratchMem sC stkN stkP memoN memoV dense gsy gcl gch ⋆
        rsMem sC rsM rsL rsH rsPool) ⋆ R) := by ac_rfl
  rw [hL, h]; ac_rfl

@[reducible] private def gateBodyMem (s : ArCtxState)
    (rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32))
    (flippedArr : List (BitVec 8)) (inNetArr outRefArr stkN stkP memoN : List (BitVec 32))
    (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64))
    (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32))
    (R : Mem 64 → Prop) : Mem 64 → Prop :=
  aigArraysMem s rhs0 rhs1 olit ⋆
  netTablesMem s bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
  gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆ rsMem s rsM rsL rsH rsPool ⋆ R

private def gateFnbMem (s : ArCtxState) (artBytes : List UInt8)
    (rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32))
    (flippedArr : List (BitVec 8)) (inNetArr outRefArr stkN stkP memoN : List (BitVec 32))
    (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64))
    (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32))
    (R : Mem 64 → Prop) : Mem 64 → Prop :=
  bytes s.art artBytes ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
  u32PadTail s.bind bindArr.length ⋆ array (t := i32) s.rule_off ruleOff ⋆
  u32PadTail s.rule_off ruleOff.length ⋆ u32PadTail s.rule_n ruleN.length ⋆
  array (t := i32) s.partner partnerArr ⋆ u32PadTail s.partner partnerArr.length ⋆
  arrayPad i8 s.flipped flippedArr ⋆ arrayPad i32 s.in_net inNetArr ⋆
  arrayPad i32 s.out_ref outRefArr ⋆
  gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆ rsMem s rsM rsL rsH rsPool ⋆ R

private theorem gate_fnb_pack {P : Mem 64 → Prop} {s : ArCtxState} {artBytes : List UInt8}
    {rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {inNetArr outRefArr stkN stkP memoN : List (BitVec 32)}
    {memoV dense : List (BitVec 64)} {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)}
    {rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)}
    {R : Mem 64 → Prop} :
    (P ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr
      flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH
      rsPool R) =
    (P ⋆ array (t := i32) s.bind bindArr ⋆ array (t := i32) s.rule_n ruleN ⋆
      gateFnbMem s artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
        inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R) := by
  dsimp only [gateBodyMem, gateFnbMem]; rw [netTablesMem_unpack]; ac_rfl

private theorem gate_aig_eq {s sC : ArCtxState} (h : GateSame s sC)
    (rhs0 rhs1 olit : List (BitVec 32)) :
    aigArraysMem sC rhs0 rhs1 olit = aigArraysMem s rhs0 rhs1 olit := by
  simp only [aigArraysMem, show sC.rhs0 = s.rhs0 by rw [h],
    show sC.rhs1 = s.rhs1 by rw [h], show sC.olit = s.olit by rw [h]]

private theorem gate_scratch_eq {s sC : ArCtxState} (h : GateSame s sC)
    (sN sP mN : List (BitVec 32)) (mV dense : List (BitVec 64)) (gsy : List (BitVec 32))
    (gcl gch : List (BitVec 64)) :
    gateScratchMem sC sN sP mN mV dense gsy gcl gch =
    gateScratchMem s sN sP mN mV dense gsy gcl gch := by
  simp only [gateScratchMem, show sC.stk_n = s.stk_n by rw [h], show sC.stk_p = s.stk_p by rw [h],
    show sC.memo_n = s.memo_n by rw [h], show sC.memo_v = s.memo_v by rw [h],
    show sC.dense = s.dense by rw [h], show sC.gsy = s.gsy by rw [h],
    show sC.gcl = s.gcl by rw [h], show sC.gch = s.gch by rw [h]]

@[reducible] private def GateFailPre (cx : BitVec 64) (s : ArCtxState) (artBytes : List UInt8)
    (rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32))
    (flippedArr : List (BitVec 8)) (inNetArr outRefArr stkN stkP memoN : List (BitVec 32))
    (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64))
    (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32))
    (R : Mem 64 → Prop) (Q : Post [.bool]) : Prop :=
  ∀ sC mC, sC.rs_n.toNat ≤ s.rs_cap.toNat → sC.rs_ptop.toNat ≤ s.rs_pcap.toNat →
    (s.pos.toNat ≤ s.nw.toNat → sC.pos.toNat ≤ s.nw.toNat) → GateSame s sC →
    (arCtxMem cx sC ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff ruleN
      partnerArr flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch
      rsM rsL rsH rsPool R) mC → Q (false, ⟨⟩) mC

@[reducible] private def GateFailScratch (cx : BitVec 64) (s : ArCtxState) (artBytes : List UInt8)
    (rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32))
    (flippedArr : List (BitVec 8)) (inNetArr outRefArr stkN stkP memoN : List (BitVec 32))
    (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64))
    (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32))
    (R : Mem 64 → Prop) (Q : Post [.bool]) : Prop :=
  ∀ sC sN sP mN mV mC, sC.rs_n.toNat ≤ s.rs_cap.toNat → sC.rs_ptop.toNat ≤ s.rs_pcap.toNat →
    (s.pos.toNat ≤ s.nw.toNat → sC.pos.toNat ≤ s.nw.toNat) → GateSame s sC →
    sN.length = stkN.length → sP.length = stkP.length →
    mN.length = memoN.length → mV.length = memoV.length →
    (arCtxMem cx sC ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff ruleN
      partnerArr flippedArr inNetArr outRefArr sN sP mN mV dense gsy gcl gch
      rsM rsL rsH rsPool R) mC → Q (false, ⟨⟩) mC

@[reducible] private def GatePostQ (cx : BitVec 64) (s : ArCtxState) (g : Aig)
    (artBytes : List UInt8) (rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32))
    (flippedArr : List (BitVec 8)) (inNetArr outRefArr stkN stkP memoN : List (BitVec 32))
    (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64))
    (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32))
    (R : Mem 64 → Prop) (Q : Post [.bool]) : Prop :=
  ∀ ok sC ruleOff' ruleN' partnerArr' sN sP mN mV dense' gsy' gcl' gch'
    rsM' rsL' rsH' rsPool' mC,
    sC.rs_n.toNat ≤ s.rs_cap.toNat → sC.rs_ptop.toNat ≤ s.rs_pcap.toNat →
    (s.pos.toNat ≤ s.nw.toNat → sC.pos.toNat ≤ s.nw.toNat) → GateSame s sC →
    ruleOff'.length = ruleOff.length → ruleN'.length = ruleN.length →
    partnerArr'.length = partnerArr.length → sN.length = stkN.length →
    sP.length = stkP.length → mN.length = memoN.length → mV.length = memoV.length →
    dense'.length = dense.length → gsy'.length = gsy.length → gcl'.length = gcl.length →
    gch'.length = gch.length → rsM'.length = rsM.length → rsL'.length = rsL.length →
    rsH'.length = rsH.length → rsPool'.length = rsPool.length →
    (ok = true → monoTotalWords rsPool' rsM' sC.rs_n.toNat ≤ sC.rs_ptop.toNat ∧
      (SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat →
        SymsBound rsPool' rsM' sC.rs_n.toNat s.n_nets.toNat) ∧
      (∀ r < sC.rs_n.toNat,
        (rsPool'.getD (rsM'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      RulesSorted rsPool' rsM' sC.rs_n.toNat ∧
      (∀ ρ, PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr' ∧
        RulesRep sC.n_out.toNat (cSig g ρ bindArr) sC ruleOff' ruleN' rsM' rsL' rsH' rsPool')) →
    (arCtxMem cx sC ⋆ bytes sC.art artBytes ⋆ gateBodyMem sC rhs0 rhs1 olit bindArr ruleOff' ruleN'
      partnerArr' flippedArr inNetArr outRefArr sN sP mN mV dense' gsy' gcl' gch'
      rsM' rsL' rsH' rsPool' R) mC → Q (ok, ⟨⟩) mC

private structure GateCommon (Γ : LeanQbe.T.Env) (s : ArCtxState) (g : Aig)
    (artBytes : List UInt8) (rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32))
    (flippedArr : List (BitVec 8)) (inNetArr outRefArr stkN stkP memoN : List (BitVec 32))
    (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64))
    (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32)) : Prop where
  nw : ∀ xs m Q X, arNextWordSpec xs m Q X → Γ "ar_next_word" [i64] [.bool, i32] xs m Q X
  mask6 : ∀ xs m Q X, arMask6Spec xs m Q X → Γ "ar_mask6" [i32] [i64] xs m Q X
  ttsim : ∀ xs m Q X, arTtsimSpec xs m Q X → Γ "ar_ttsim" [i64, i32, i32, i64] [.bool, i64] xs m Q X
  dzero : ∀ xs m Q X, arDzeroSpec xs m Q X → Γ "ar_dzero" [i64] [] xs m Q X
  dlit : ∀ xs m Q X, arDlitSpec xs m Q X → Γ "ar_dlit" [i64, i32, i32] [] xs m Q X
  dmul : ∀ xs m Q X, arDmulSpec xs m Q X → Γ "ar_dmul" [i64, i64, i64] [] xs m Q X
  daxpy : ∀ xs m Q X, arDaxpySpec xs m Q X → Γ "ar_daxpy" [i64, i64, i64] [] xs m Q X
  dcanon : ∀ xs m Q X, arDcanonSpec xs m Q X → Γ "ar_dcanon" [i64, i64] [i32] xs m Q X
  cadd : ∀ xs m Q X, arCaddSpec xs m Q X →
    Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X
  install : ∀ xs m Q X, arInstallRuleSpec xs m Q X →
    Γ "ar_install_rule" [i64, i32, i32] [.bool] xs m Q X
  sI : s.I.toNat = g.I
  sM : s.M.toNat = g.M
  nn30 : s.n_nets.toNat ≤ 0x3FFFFFFF
  rcap30 : s.rs_cap.toNat < 2 ^ 30
  rpcap32 : s.rs_pcap.toNat < 2 ^ 32
  art64 : s.art.toNat + artBytes.length < 2 ^ 64
  nw4 : 4 * s.nw.toNat ≤ artBytes.length
  sn : 160 ≤ stkN.length
  sp : 160 ≤ stkP.length
  mn : 64 ≤ memoN.length
  mv : 64 ≤ memoV.length
  dense_len : 128 ≤ dense.length
  gsy_len : 85 ≤ gsy.length
  gcl_len : 16 ≤ gcl.length
  gch_len : 16 ≤ gch.length
  masks : MasksOk s.n_out.toNat s.mlo s.mhi
  aig : AigRep g rhs0 rhs1 olit
  bind : BindRep s g bindArr inNetArr outRefArr
  nout1 : 1 ≤ s.n_out.toNat
  rsn : s.rs_n.toNat ≤ s.rs_cap.toNat
  rspt : s.rs_ptop.toNat ≤ s.rs_pcap.toNat
  tot : monoTotalWords rsPool rsM s.rs_n.toNat ≤ s.rs_ptop.toNat
  rsOk : ∀ r < s.rs_n.toNat, (rsPool.getD (rsM.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32
  rsSorted : RulesSorted rsPool rsM s.rs_n.toNat
  allRep : ∀ ρ : Nat → Bool, PartnerRep (cSig g ρ bindArr) s.n_nets.toNat partnerArr ∧
    RulesRep s.n_out.toNat (cSig g ρ bindArr) s ruleOff ruleN rsM rsL rsH rsPool

private theorem ar_do_gate_vso_wp {Γ : LeanQbe.T.Env}
    {cx : BitVec 64} {ok_ti : Bool} {kraw nout nin nl : BitVec 32} {all : BitVec 64}
    {s sO sI sL sTi : ArCtxState} {g : Aig} {artBytes : List UInt8}
    {rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {inNetArr outRefArr bs stkN stkP memoN sN' : List (BitVec 32)}
    {sP' mN' gsy rsM rsPool : List (BitVec 32)}
    {memoV mV' dense gcl gch rsL rsH : List (BitVec 64)} {R : Mem 64 → Prop} {mTi : Mem 64}
    (hc : GateCommon Γ s g artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
      inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool)
    {Q : Post [.bool]} {X : XPost} (hsn' : sN'.length = stkN.length)
    (hsp' : sP'.length = stkP.length) (hmn' : mN'.length = memoN.length)
    (hmv' : mV'.length = memoV.length) (hkraw : (kraw &&& 255#32) = 6#32 → nout = 2#32)
    (hnout : nout = 1#32 ∨ nout = 2#32) (hnin : nin = 2#32 ∨ nin = 3#32)
    (hnl1 : 1 ≤ nl.toNat) (hnl6 : nl.toNat ≤ 6)
    (hnl_e0 : ((kraw >>> 8#32) &&& 1#32) = 0#32 → nl = nin)
    (hall : ∀ t < 2 ^ nl.toNat, all.toNat.testBit t = true)
    (houts : ∀ q < nout.toNat, (sO.g_outs.getD q 0#32).toNat < s.n_nets.toNat)
    (hneU : nout.toNat = 2 → sO.g_outs.getD 0 0#32 ≠ sO.g_outs.getD 1 0#32)
    (hins : ∀ q < nin.toNat, (sI.g_innet.getD q 0#32).toNat < s.n_nets.toNat)
    (hVsIn : ∀ q < nin.toNat, (sI.g_vs.getD q 0#32).toNat / 2 < s.n_nets.toNat)
    (hposL : s.pos.toNat ≤ s.nw.toNat → sL.pos.toNat ≤ s.nw.toNat)
    (hsTi_eq : sTi = { s with
      pos := sL.pos, g_outs := sO.g_outs, g_innet := sI.g_innet,
      g_inneg := sI.g_inneg, g_vs := sI.g_vs, g_lnode := sL.g_lnode, g_lmask := sL.g_lmask,
      g_tin := sTi.g_tin })
    (hbs0 : ((kraw >>> 8#32) &&& 1#32) = 0#32 → ∀ q < nin.toNat,
      bs.getD q 0#32 = bindArr.getD (sI.g_innet.getD q 0#32).toNat 0#32)
    (hLnode : ∀ q < nl.toNat, sL.g_lnode.getD q 0#32 = bs.getD q 0#32 >>> 1#32 ∧
      sL.g_lmask.getD q 0#64 = (BitVec.ofNat 64 (xmask q) &&& all) ^^^
        (if bs.getD q 0#32 &&& 1#32 ≠ 0#32 then all else 0#64))
    (hTin0 : ((kraw >>> 8#32) &&& 1#32) = 0#32 → ∀ q < nin.toNat,
      sTi.g_tin.getD q 0#64 = BitVec.ofNat 64 (xmask q) &&& all)
    (hTin1 : ((kraw >>> 8#32) &&& 1#32) ≠ 0#32 → ∀ ρ : Nat → Bool, ∀ q < nin.toNat, ∀ t < 64,
      all.toNat.testBit t = true →
      (∀ r < nl.toNat, (sL.g_lmask.getD r 0#64).toNat.testBit t =
        g.nodeVal ρ (sL.g_lnode.getD r 0#32).toNat) →
      (sTi.g_tin.getD q 0#64).toNat.testBit t =
        g.litVal ρ (bindArr.getD (sI.g_innet.getD q 0#32).toNat 0#32).toNat)
    (hmTi : (arCtxMem cx sTi ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff
      ruleN partnerArr flippedArr inNetArr outRefArr sN' sP' mN' mV' dense gsy gcl gch
      rsM rsL rsH rsPool R) mTi)
    (hFail : GateFailScratch cx s artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr
      flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R Q)
    (hQ : GatePostQ cx s g artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
      inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R Q) :
    wp Γ Q X (gateTtoExpr cx ok_ti kraw nout nin nl all) mTi := by
  obtain ⟨_, _, hTtsim, hDzero, hDlit, hDmul, hDaxpy, hDcanon, hCadd, hInstall, hsI, hsM, hnn30,
    hrcap30, hrpcap32, _, _, hsn, hsp, hmn, hmv, hdense, hgsy, hgcl, hgch, hmasks, hAig, hBind,
    hnout1, hrsn, hrspt, hTot, hRsOk, hRsSorted, hAllRep⟩ := hc
  let expl := (kraw >>> 8#32) &&& 1#32
  have ho2 : nout.toNat ≤ 2 := by rcases hnout with rfl | rfl <;> decide
  have hn2 : nin.toNat ≤ 3 := by rcases hnin with rfl | rfl <;> decide
  have hbind_len : s.n_nets.toNat ≤ bindArr.length := hBind.bind_len
  have hsTi_ok := gate_ctx_ok (cx := cx) (R := bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit
    bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr sN' sP' mN' mV' dense gsy gcl
    gch rsM rsL rsH rsPool R) (sep_cast hmTi (by ac_rfl))
  have hgo0_lt : (BitVec.signExtend 64 0#32).toNat < sTi.g_outs.length := by
    have := hsTi_ok.g_outs; rw [show (BitVec.signExtend 64 0#32).toNat = 0 from by decide]; omega
  have hgvs3_lt : (BitVec.signExtend 64 3#32).toNat < sTi.g_vs.length := by
    have := hsTi_ok.g_vs; rw [show (BitVec.signExtend 64 3#32).toNat = 3 from by decide]; omega
  apply head_wp_add (va := cx) (vb := (756 : BitVec 64)) (by rfl) (by rfl)
  c0_hsteps_nogrp
  refine wp_join_group (fun _ mV =>
      ∃ sV, sV = { s with
        pos := sL.pos, g_outs := sO.g_outs, g_innet := sI.g_innet, g_inneg := sI.g_inneg,
        g_vs := sV.g_vs, g_lnode := sL.g_lnode, g_lmask := sL.g_lmask, g_tin := sTi.g_tin } ∧
      (∀ j < 4, (sV.g_vs.getD j 0#32).toNat / 2 < s.n_nets.toNat) ∧
      (arCtxMem cx sV ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit
        bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr sN' sP' mN' mV' dense gsy
        gcl gch rsM rsL rsH rsPool R) mV) ?_ ?_
  · rintro _ _ mV ⟨sV, hsV_eq, hVs, hmV⟩
    refine wp_loop_group (fun kto ⟨_, j, _⟩ mTo =>
      j.toNat ≤ nout.toNat ∧ kto = nout.toNat - j.toNat ∧ ∃ sTo sN'' sP'' mN'' mV'',
        sN''.length = stkN.length ∧ sP''.length = stkP.length ∧ mN''.length = memoN.length ∧
        mV''.length = memoV.length ∧ sTo = { s with
          pos := sL.pos, g_outs := sO.g_outs, g_innet := sI.g_innet, g_inneg := sI.g_inneg,
          g_vs := sV.g_vs, g_lnode := sL.g_lnode, g_lmask := sL.g_lmask,
          g_tin := sTi.g_tin, g_tto := sTo.g_tto } ∧
        (∀ ρ : Nat → Bool, ∀ q < j.toNat, ∀ t < 64, all.toNat.testBit t = true →
          (∀ r < nl.toNat, (sL.g_lmask.getD r 0#64).toNat.testBit t =
            g.nodeVal ρ (sL.g_lnode.getD r 0#32).toNat) →
          (sTo.g_tto.getD q 0#64).toNat.testBit t =
            g.litVal ρ (bindArr.getD (sO.g_outs.getD q 0#32).toNat 0#32).toNat) ∧
        (arCtxMem cx sTo ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff
          ruleN partnerArr flippedArr inNetArr outRefArr sN'' sP'' mN'' mV'' dense gsy gcl gch
          rsM rsL rsH rsPool R) mTo)
      (fun Jto kto ⟨_, j, _⟩ mTo hrecTo ⟨hj_le, hk_to, sTo, sN'', sP'',
        mN'', mV'', hsN'', hsP'', hmN'', hmV'', hsTo_eq, hTto, hmTo⟩ => by
        dsimp only at hrecTo hj_le hsN'' hsP'' hmN'' hmV'' hTto hmTo ⊢
        c0_hstep
        refine head_wp_jnz rfl (fun hc => by
          have hj_lt : j.toNat < nout.toNat := by simpa [BitVec.ult] using hc
          have hsTo_ok := gate_ctx_ok (cx := cx) (R := bytes s.art artBytes ⋆ gateBodyMem s rhs0
            rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr sN'' sP'' mN''
            mV'' dense gsy gcl gch rsM rsL rsH rsPool R) (sep_cast hmTo (by ac_rfl))
          have hgo_j : (BitVec.setWidth 64 j).toNat < sTo.g_outs.length := by
            have := hsTo_ok.g_outs; rw [bv64_sw_toNat]; omega
          have hto_g : GateSame s sTo := by rw [hsTo_eq]; rfl
          have hbo_j : (BitVec.setWidth 64 (sTo.g_outs[(BitVec.setWidth 64 j).toNat]'
              hgo_j)).toNat < bindArr.length := by
            rw [bv64_sw_toNat, ← d_getD_eq_getElem _ 0#32 hgo_j, bv64_sw_toNat,
              show sTo.g_outs = sO.g_outs by rw [hsTo_eq]]
            exact Nat.lt_of_lt_of_le (houts j.toNat hj_lt) hbind_len
          have hgo_j' : j.toNat < sTo.g_outs.length := bv64_sw_toNat ▸ hgo_j
          have hbo_j'' : (sTo.g_outs[j.toNat]'hgo_j').toNat < bindArr.length := by
            simpa [bv64_sw_toNat] using hbo_j
          let F_tt := array (t := i32) sTo.bind bindArr ⋆ (bytes s.art artBytes ⋆
            u32PadTail s.bind bindArr.length ⋆ array (t := i32) s.rule_off ruleOff ⋆
            u32PadTail s.rule_off ruleOff.length ⋆ array (t := i32) s.rule_n ruleN ⋆
            u32PadTail s.rule_n ruleN.length ⋆ array (t := i32) s.partner partnerArr ⋆
            u32PadTail s.partner partnerArr.length ⋆ arrayPad i8 s.flipped flippedArr ⋆
            arrayPad i32 s.in_net inNetArr ⋆ arrayPad i32 s.out_ref outRefArr ⋆
            rsMem s rsM rsL rsH rsPool ⋆ R)
          have hmTo_tt : (arCtxMem cx sTo ⋆ aigArraysMem sTo rhs0 rhs1 olit ⋆
              gateScratchMem sTo sN'' sP'' mN'' mV'' dense gsy gcl gch ⋆ F_tt) mTo := by
            dsimp only [F_tt]; dsimp only [gateBodyMem] at hmTo; rw [netTablesMem_unpack] at hmTo
            rw [gate_aig_eq hto_g, gate_scratch_eq hto_g, show sTo.bind = s.bind by rw [hto_g]]
            exact sep_cast hmTo (by ac_rfl)
          have hmTo_ld := hmTo_tt; dsimp only [F_tt] at hmTo_ld
          c0_hsteps_nogrp
          refine gate_ttsim_step hTtsim (cx := cx) (s := sTo)
            (lit := bindArr[(sTo.g_outs[j.toNat]'hgo_j').toNat]'hbo_j'') (all := all)
            (stkN := sN'') (stkP := sP'') (memoN := mN'') (memoV := mV'') (dense := dense)
            (gsy := gsy) (gcl := gcl) (gch := gch) (F := F_tt) rfl rfl rfl rfl
            (by rw [hsTo_eq]; exact hsI) (by rw [hsTo_eq]; exact hsM) hAig hnl6
            (by rw [hsN'']; exact hsn) (by rw [hsP'']; exact hsp)
            (by rw [hmN'']; exact hmn) (by rw [hmV'']; exact hmv) hmTo_tt
            (fun okT tv sN3 sP3 mN3 mV3 mT3 hsN3 hsP3 hmN3 hmV3 hokT hmT3 => by
              dsimp only [F_tt] at hmT3
              cases hokT_b : okT
              · refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
                c0_hstraight
                refine hFail sTo sN3 sP3 mN3 mV3 mT3
                  (by rw [hsTo_eq]; exact hrsn) (by rw [hsTo_eq]; exact hrspt)
                  (by rw [hsTo_eq]; exact hposL) hto_g
                  (hsN3.trans hsN'') (hsP3.trans hsP'') (hmN3.trans hmN'') (hmV3.trans hmV'') (by
                    rw [gate_aig_eq hto_g, gate_scratch_eq hto_g,
                      show sTo.bind = s.bind by rw [hto_g]] at hmT3
                    dsimp only [gateBodyMem]; rw [netTablesMem_unpack]
                    exact sep_cast hmT3 (by ac_rfl))
              · refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
                c0_hstraight
                let sTo' := { sTo with g_tto := sTo.g_tto.set (BitVec.toNat j) tv }
                have hsTo_b : array (t := i32) sTo.bind bindArr =
                    array (t := i32) s.bind bindArr := by rw [show sTo.bind = s.bind by rw [hto_g]]
                have hmemT :=
                  ‹(arCtxMem cx { sTo with g_tto := sTo.g_tto.set (BitVec.toNat j) tv } ⋆ _) _›
                rw [gate_aig_eq hto_g, gate_scratch_eq hto_g, hsTo_b] at hmemT
                refine hrecTo (nout.toNat - (j + 1).toNat) (true, j + 1, ()) _
                  (by rw [bv32_add1_toNat (by omega), hk_to]; omega)
                  ⟨by rw [bv32_add1_toNat (by omega)]; omega, rfl, sTo', sN3, sP3, mN3, mV3,
                   hsN3.trans hsN'', hsP3.trans hsP'', hmN3.trans hmN'', hmV3.trans hmV'',
                   by dsimp only [sTo']; rw [hsTo_eq], fun ρ q hq t ht64 hallt hlmask => ?_,
                   by dsimp only [gateBodyMem]; rw [netTablesMem_unpack]
                      exact sep_cast hmemT (by ac_rfl)⟩
                dsimp only at hq; rw [bv32_add1_toNat (by omega)] at hq
                rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hq) with rfl | hqlt
                · have := hsTo_ok.g_tto
                  rw [show sTo'.g_tto = sTo.g_tto.set (BitVec.toNat j) tv from rfl,
                    d_getD_set_eq _ 0#64 tv (by omega)]
                  rw [← d_getD_eq_getElem bindArr 0#32 hbo_j'',
                    ← d_getD_eq_getElem sTo.g_outs 0#32 hgo_j',
                    show sTo.g_outs = sO.g_outs by rw [hsTo_eq]] at hokT
                  exact hokT hokT_b t ρ ht64 hallt (fun r hr => by
                    rw [show sTo.g_lmask = sL.g_lmask by rw [hsTo_eq],
                      show sTo.g_lnode = sL.g_lnode by rw [hsTo_eq]]
                    exact hlmask r hr)
                · rw [show sTo'.g_tto = sTo.g_tto.set (BitVec.toNat j) tv from rfl,
                    getD_set_ne _ 0#64 tv (by omega)]
                  exact hTto ρ q hqlt t ht64 hallt hlmask)) (fun hc => by
          have hj_nlt : ¬ j.toNat < nout.toNat := by simpa [BitVec.ult] using hc
          have hsTo_g : GateSame s sTo := by rw [hsTo_eq]; rfl
          have hds := dense_split8 s.dense dense hdense
          let R_d := bytes s.art artBytes ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
            array (t := i32) s.bind bindArr ⋆ u32PadTail s.bind bindArr.length ⋆
            u32PadTail s.rule_off ruleOff.length ⋆ u32PadTail s.rule_n ruleN.length ⋆
            u32PadTail s.partner partnerArr.length ⋆ arrayPad i8 s.flipped flippedArr ⋆
            arrayPad i32 s.in_net inNetArr ⋆ arrayPad i32 s.out_ref outRefArr ⋆
            arrayPad i32 s.stk_n sN'' ⋆ arrayPad i32 s.stk_p sP'' ⋆
            arrayPad i32 s.memo_n mN'' ⋆ array64 s.memo_v mV'' ⋆ R
          have hmD_sp : (arCtxMem cx sTo ⋆ array64 sTo.dense (dense.take 16) ⋆
              array64 (sTo.dense + 128#64) ((dense.drop 16).take 16) ⋆
              array64 (sTo.dense + 256#64) ((dense.drop 32).take 16) ⋆
              array64 (sTo.dense + 384#64) ((dense.drop 48).take 16) ⋆
              array64 (sTo.dense + 512#64) ((dense.drop 64).take 16) ⋆
              array64 (sTo.dense + 640#64) ((dense.drop 80).take 16) ⋆
              array64 (sTo.dense + 768#64) ((dense.drop 96).take 16) ⋆
              array64 (sTo.dense + 896#64) ((dense.drop 112).take 16) ⋆
              array64 (sTo.dense + 1024#64) (dense.drop 128) ⋆ arrayPad i32 sTo.gsy gsy ⋆
              array64 sTo.gcl gcl ⋆ array64 sTo.gch gch ⋆ array (t := i32) sTo.rule_off ruleOff ⋆
              array (t := i32) sTo.rule_n ruleN ⋆ array (t := i32) sTo.partner partnerArr ⋆
              rsMem sTo rsM rsL rsH rsPool ⋆ R_d) mTo := by
            dsimp only [gateBodyMem] at hmTo
            rw [netTablesMem_unpack, gateScratchMem_unpack, hds.2.2.2.2.2.2.2.2] at hmTo
            rw [arrayPad_u32_unfold, show sTo.dense = s.dense by rw [hsTo_eq],
              show sTo.gsy = s.gsy by rw [hsTo_eq], show sTo.gcl = s.gcl by rw [hsTo_eq],
              show sTo.gch = s.gch by rw [hsTo_eq], show sTo.rule_off = s.rule_off by rw [hsTo_eq],
              show sTo.rule_n = s.rule_n by rw [hsTo_eq],
              show sTo.partner = s.partner by rw [hsTo_eq],
              show rsMem sTo rsM rsL rsH rsPool = rsMem s rsM rsL rsH rsPool by
                simp only [rsMem, show sTo.rs_m = s.rs_m by rw [hsTo_eq],
                  show sTo.rs_l = s.rs_l by rw [hsTo_eq], show sTo.rs_h = s.rs_h by rw [hsTo_eq],
                  show sTo.rs_pool = s.rs_pool by rw [hsTo_eq]]]
            exact sep_cast hmTo (by dsimp only [R_d]; ac_rfl)
          change wp Γ Q X (gateDenseExpr cx kraw nout nin nl j) mTo
          refine ar_do_gate_dense_wp hDzero hDlit hDmul hDaxpy hDcanon hCadd hInstall
            hkraw hnout hnin hnl1 hnl6 (by rw [hsTo_eq]; exact hnn30)
            (by rw [hsTo_eq]; exact hrcap30) (by rw [hsTo_eq]; exact hrpcap32)
            (by rw [hsTo_eq]; exact hmasks) (by rw [hsTo_eq]; exact hnout1)
            hds.1 hds.2.1 hds.2.2.1 hds.2.2.2.1 hds.2.2.2.2.1 hds.2.2.2.2.2.1
            hds.2.2.2.2.2.2.1 hds.2.2.2.2.2.2.2.1 hgsy hgcl hgch
            (fun q hq => by rw [hsTo_eq]; exact houts q hq) (by rw [hsTo_eq]; exact hneU)
            (fun q hq => by rw [hsTo_eq]; exact hins q hq) (fun ρ =>
              gate_row_of_tOf g ρ hnl1 hnl6 expl (nin := nin.toNat) (nout := nout.toNat)
                (fun he => by rw [hnl_e0 he]; exact Nat.le_refl _) all bindArr
                sTo.g_innet sTo.g_outs sTo.g_lnode bs sTo.g_lmask sTo.g_tin sTo.g_tto hall
                (fun q hq => by
                  rw [show sTo.g_lnode = sL.g_lnode by rw [hsTo_eq]]; exact (hLnode q hq).1)
                (fun q hq => by
                  rw [show sTo.g_lmask = sL.g_lmask by rw [hsTo_eq]]; exact (hLnode q hq).2)
                (by rw [show sTo.g_innet = sI.g_innet by rw [hsTo_eq]]; exact hbs0)
                (by rw [show sTo.g_tin = sTi.g_tin by rw [hsTo_eq]]; exact hTin0)
                (by rw [show sTo.g_tin = sTi.g_tin by rw [hsTo_eq],
                      show sTo.g_innet = sI.g_innet by rw [hsTo_eq], show sTo.g_lmask = sL.g_lmask
                      by rw [hsTo_eq], show sTo.g_lnode = sL.g_lnode by rw [hsTo_eq]]
                    exact fun he => hTin1 he ρ)
                (fun o ho t ht64 hallt hlmask => by
                  rw [show sTo.g_outs = sO.g_outs by rw [hsTo_eq],
                    show sTo.g_lmask = sL.g_lmask by rw [hsTo_eq],
                    show sTo.g_lnode = sL.g_lnode by rw [hsTo_eq]] at *
                  exact hTto ρ o (by omega) t ht64 hallt hlmask))
            (by rw [hsTo_eq]; exact hVs)
            (by rw [hsTo_eq]; exact hrsn) (by rw [hsTo_eq]; exact hrspt)
            (by rw [hsTo_eq]; exact hTot) (by rw [hsTo_eq]; exact hRsOk)
            (by rw [hsTo_eq]; exact hRsSorted)
            (fun ρ => ⟨by rw [hsTo_eq]; exact (hAllRep ρ).1, by
              have hR := (hAllRep ρ).2
              refine ⟨by rw [hsTo_eq]; exact hR.1, by rw [hsTo_eq]; exact hR.2.1,
                by rw [hsTo_eq]; exact hR.2.2.1, by rw [hsTo_eq]; exact hR.2.2.2.1,
                by rw [hsTo_eq]; exact hR.2.2.2.2.1, by rw [hsTo_eq]; exact hR.2.2.2.2.2.1,
                by rw [hsTo_eq]; exact hR.2.2.2.2.2.2.1, by rw [hsTo_eq]; exact hR.2.2.2.2.2.2.2.1,
                by rw [hsTo_eq]; exact hR.2.2.2.2.2.2.2.2.1,
                fun v hv hne => by rw [hsTo_eq] at hv ⊢; exact hR.2.2.2.2.2.2.2.2.2 v hv hne⟩⟩)
            hmD_sp ?_
          intro ok sF roF rnF paF denseF gsyF gclF gchF rmF rlF rhF rpF mF hsnF hsptF hsF_eq hrOF
            hrNF hpaF hdenseF hgsyF hgclF hgchF hrmF hrlF hrhF hrpF hokF hmF
          have hsF_base : GateSame s sF := by rw [hsF_eq, hsTo_eq]; rfl
          have hdense_len : denseF.length = dense.length := by
            rw [hdenseF, show (dense.drop 128).length = dense.length - 128 from by simp]; omega
          refine hQ ok sF roF rnF paF sN'' sP'' mN'' mV'' denseF gsyF gclF gchF
            rmF rlF rhF rpF mF (by rw [hsTo_eq] at hsnF; exact hsnF)
            (by rw [hsTo_eq] at hsptF; exact hsptF)
            (fun _ => by rw [hsF_eq, hsTo_eq]; exact hposL ‹_›) hsF_base hrOF hrNF hpaF
            hsN'' hsP'' hmN'' hmV'' hdense_len hgsyF hgclF hgchF hrmF hrlF hrhF hrpF
            (fun hokT => ⟨(hokF hokT).1,
              (by have h := (hokF hokT).2.1; rwa [hsTo_eq] at h),
              (hokF hokT).2.2.1, (hokF hokT).2.2.2.1, fun ρ =>
              ⟨by rw [hsTo_eq] at *; exact ((hokF hokT).2.2.2.2 ρ).1,
                ((hokF hokT).2.2.2.2 ρ).2⟩⟩)
            (by
              rw [show sTo.dense = s.dense by rw [hsTo_eq], show sTo.gsy = s.gsy by rw [hsTo_eq],
                show sTo.gcl = s.gcl by rw [hsTo_eq], show sTo.gch = s.gch by rw [hsTo_eq],
                show sTo.rule_off = s.rule_off by rw [hsTo_eq],
                show sTo.rule_n = s.rule_n by rw [hsTo_eq],
                show sTo.partner = s.partner by rw [hsTo_eq],
                show rsMem sF rmF rlF rhF rpF = rsMem s rmF rlF rhF rpF by simp only [rsMem,
                  show sF.rs_m = s.rs_m by rw [hsF_base], show sF.rs_l = s.rs_l by rw [hsF_base],
                  show sF.rs_h = s.rs_h by rw [hsF_base],
                  show sF.rs_pool = s.rs_pool by rw [hsF_base]]] at hmF
              have hmF' : (arCtxMem cx sF ⋆ bytes s.art artBytes ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
                  netTablesMem s bindArr roF rnF paF flippedArr inNetArr outRefArr ⋆
                  gateScratchMem s sN'' sP'' mN'' mV'' denseF gsyF gclF gchF ⋆
                  rsMem s rmF rlF rhF rpF ⋆ R) mF := by
                dsimp only [R_d] at hmF
                rw [netTablesMem_unpack, gateScratchMem_unpack, hrOF, hrNF, hpaF]
                simp only [arrayPad_u32_unfold] at hmF ⊢; exact sep_cast hmF (by ac_rfl)
              rw [← gate_mem_same_rw hsF_base] at hmF'
              dsimp only [gateBodyMem]; exact sep_cast hmF' (by ac_rfl))))
      (fun Jto hJto => by
        c0_hsteps; exact hJto nout.toNat (ok_ti, 0#32, ()) mV ⟨Nat.zero_le _, Nat.sub_zero _,
          sV, sN', sP', mN', mV', hsn', hsp', hmn', hmv', (by rw [hsV_eq]),
          fun _ _ hq => absurd hq (Nat.not_lt_zero _), hmV⟩)
  · intro Jv hJv
    have hgvs2_lt : (BitVec.signExtend 64 2#32).toNat <
        (sTi.g_vs.set ((BitVec.ofNat (OfNat.ofNat 64) 3 * 4).toNat / 4)
          (2 * sTi.g_outs[(BitVec.ofNat (OfNat.ofNat 64) 0 * 4).toNat / 4])).length := by
      rw [show (BitVec.signExtend 64 2#32).toNat = 2 from by decide, List.length_set]
      have := hsTi_ok.g_vs; omega
    have hsTi_mk : ∀ v : List (BitVec 32), { sTi with g_vs := v } =
        { s with
          pos := sL.pos, g_outs := sO.g_outs, g_innet := sI.g_innet,
          g_inneg := sI.g_inneg, g_vs := v, g_lnode := sL.g_lnode,
          g_lmask := sL.g_lmask, g_tin := sTi.g_tin } := fun v =>
      congrArg (fun x => { x with g_vs := v }) hsTi_eq
    have hVsOut : ((2#32 * sTi.g_outs[(BitVec.ofNat 64 0 * 4).toNat / 4]).toNat / 2) <
        s.n_nets.toNat := by
      have hk0 : (BitVec.ofNat 64 0 * 4).toNat / 4 = 0 := by decide
      have hnout_pos : 0 < nout.toNat := by rcases hnout with rfl | rfl <;> decide
      have hout0 : (sTi.g_outs.getD 0 0#32).toNat < s.n_nets.toNat := by
        rw [show sTi.g_outs = sO.g_outs by rw [hsTi_eq]]; exact houts 0 hnout_pos
      rw [d_getD_eq_getElem _ _ (by have h := hsTi_ok.g_outs; exact h ▸ by decide)] at hout0
      have hgel : sTi.g_outs[(BitVec.ofNat 64 0 * 4).toNat / 4] = sTi.g_outs[0] := by
        simp only [hk0]
      rw [hgel, BitVec.toNat_mul, show (2#32 : BitVec 32).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by omega)]
      omega
    have hVs01 : ∀ q < 2, (sTi.g_vs.getD q 0#32).toNat / 2 < s.n_nets.toNat := fun q hq => by
      rw [show sTi.g_vs = sI.g_vs by rw [hsTi_eq]]
      exact hVsIn q (by rcases hnin with rfl | rfl <;> exact lt_of_lt_of_le hq (by decide))
    have hsTi_len : sTi.g_vs.length = 4 := hsTi_ok.g_vs
    c0_hsteps_nogrp
    · refine hJv () _ ⟨_, hsTi_mk _, ?_, sep_cast ‹_› (by ac_rfl)⟩
      intro j hj
      have hk3 : (BitVec.ofNat 64 3 * 4).toNat / 4 = 3 := by decide
      have hk2 : (BitVec.ofNat 64 2 * 4).toNat / 4 = 2 := by decide
      rw [hk2, hk3]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
      · rw [getD_set_ne _ 0#32 _ (by decide), getD_set_ne _ 0#32 _ (by decide)]
        exact hVs01 0 (by decide)
      · rw [getD_set_ne _ 0#32 _ (by decide), getD_set_ne _ 0#32 _ (by decide)]
        exact hVs01 1 (by decide)
      · rw [d_getD_set_eq _ 0#32 _ (by rw [List.length_set, hsTi_len]; decide)]
        simpa using Nat.zero_lt_of_lt hVsOut
      · rw [getD_set_ne _ 0#32 _ (by decide), d_getD_set_eq _ 0#32 _ (by rw [hsTi_len]; decide)]
        exact hVsOut
    · refine hJv () _ ⟨_, hsTi_mk _, ?_, sep_cast ‹_› (by ac_rfl)⟩
      intro j hj
      have hk3 : (BitVec.ofNat 64 3 * 4).toNat / 4 = 3 := by decide
      have hnin3 : nin = 3#32 := hnin.resolve_left (fun h => by subst h; exact hc (by decide))
      rw [hk3]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
      · rw [getD_set_ne _ 0#32 _ (by decide)]; exact hVs01 0 (by decide)
      · rw [getD_set_ne _ 0#32 _ (by decide)]; exact hVs01 1 (by decide)
      · rw [getD_set_ne _ 0#32 _ (by decide), show sTi.g_vs = sI.g_vs by rw [hsTi_eq]]
        exact hVsIn 2 (by rw [hnin3]; decide)
      · rw [d_getD_set_eq _ 0#32 _ (by rw [hsTi_len]; decide)]; exact hVsOut

private theorem ar_do_gate_tail_wp {Γ : LeanQbe.T.Env}
    {cx : BitVec 64} {ok_l : Bool} {kraw nout nin nl : BitVec 32} {all : BitVec 64}
    {s sO sI sL : ArCtxState} {g : Aig} {artBytes : List UInt8}
    {rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {inNetArr outRefArr bs stkN stkP memoN : List (BitVec 32)}
    {memoV dense : List (BitVec 64)} {gsy rsM rsPool : List (BitVec 32)}
    {gcl gch rsL rsH : List (BitVec 64)} {R : Mem 64 → Prop} {mL : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hcm : GateCommon Γ s g artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
      inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool)
    (hkraw : (kraw &&& 255#32) = 6#32 → nout = 2#32)
    (hnout : nout = 1#32 ∨ nout = 2#32) (hnin : nin = 2#32 ∨ nin = 3#32)
    (hnl1 : 1 ≤ nl.toNat) (hnl6 : nl.toNat ≤ 6)
    (hnl_e0 : ((kraw >>> 8#32) &&& 1#32) = 0#32 → nl = nin)
    (hall : ∀ t < 2 ^ nl.toNat, all.toNat.testBit t = true)
    (houts : ∀ q < nout.toNat, (sO.g_outs.getD q 0#32).toNat < s.n_nets.toNat)
    (hneU : nout.toNat = 2 → sO.g_outs.getD 0 0#32 ≠ sO.g_outs.getD 1 0#32)
    (hins : ∀ q < nin.toNat, (sI.g_innet.getD q 0#32).toNat < s.n_nets.toNat)
    (hVsIn : ∀ q < nin.toNat, (sI.g_vs.getD q 0#32).toNat / 2 < s.n_nets.toNat)
    (hposL : s.pos.toNat ≤ s.nw.toNat → sL.pos.toNat ≤ s.nw.toNat)
    (hsL_eq : sL = { s with
      pos := sL.pos, g_outs := sO.g_outs, g_innet := sI.g_innet,
      g_inneg := sI.g_inneg, g_vs := sI.g_vs, g_lnode := sL.g_lnode, g_lmask := sL.g_lmask })
    (hbs0 : ((kraw >>> 8#32) &&& 1#32) = 0#32 → ∀ q < nin.toNat,
      bs.getD q 0#32 = bindArr.getD (sI.g_innet.getD q 0#32).toNat 0#32)
    (hLnode : ∀ q < nl.toNat, sL.g_lnode.getD q 0#32 = bs.getD q 0#32 >>> 1#32 ∧
      sL.g_lmask.getD q 0#64 = (BitVec.ofNat 64 (xmask q) &&& all) ^^^
        (if bs.getD q 0#32 &&& 1#32 ≠ 0#32 then all else 0#64))
    (hmL : (arCtxMem cx sL ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff
      ruleN partnerArr flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch
      rsM rsL rsH rsPool R) mL)
    (hFail : GateFailScratch cx s artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr
      flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R Q)
    (hQ : GatePostQ cx s g artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
      inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R Q) :
    wp Γ Q X (gateTailExpr cx ok_l kraw nout nin nl all) mL := by
  have hMask6 := hcm.mask6; have hTtsim := hcm.ttsim; have hsI := hcm.sI; have hsM := hcm.sM
  have hsn := hcm.sn; have hsp := hcm.sp; have hmn := hcm.mn; have hmv := hcm.mv
  have hAig := hcm.aig; have hBind := hcm.bind; have hrsn := hcm.rsn; have hrspt := hcm.rspt
  let expl := (kraw >>> 8#32) &&& 1#32
  have hn2 : nin.toNat ≤ 3 := by rcases hnin with rfl | rfl <;> decide
  have hbind_len : s.n_nets.toNat ≤ bindArr.length := hBind.bind_len
  refine wp_loop_group (ts := [.bool, i32]) (fun kti ⟨_, j, _⟩ mTi =>
    j.toNat ≤ nin.toNat ∧ kti = nin.toNat - j.toNat ∧ ∃ sTi sN' sP' mN' mV',
      sN'.length = stkN.length ∧ sP'.length = stkP.length ∧ mN'.length = memoN.length ∧
      mV'.length = memoV.length ∧ sTi = { s with
        pos := sL.pos, g_outs := sO.g_outs, g_innet := sI.g_innet, g_inneg := sI.g_inneg,
        g_vs := sI.g_vs, g_lnode := sL.g_lnode, g_lmask := sL.g_lmask, g_tin := sTi.g_tin } ∧
      (expl = 0#32 → ∀ q < j.toNat, sTi.g_tin.getD q 0#64 = BitVec.ofNat 64 (xmask q) &&& all) ∧
      (expl ≠ 0#32 → ∀ ρ : Nat → Bool, ∀ q < j.toNat, ∀ t < 64, all.toNat.testBit t = true →
        (∀ r < nl.toNat, (sL.g_lmask.getD r 0#64).toNat.testBit t =
          g.nodeVal ρ (sL.g_lnode.getD r 0#32).toNat) →
        (sTi.g_tin.getD q 0#64).toNat.testBit t =
          g.litVal ρ (bindArr.getD (sI.g_innet.getD q 0#32).toNat 0#32).toNat) ∧
      (arCtxMem cx sTi ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff
        ruleN partnerArr flippedArr inNetArr outRefArr sN' sP' mN' mV' dense gsy gcl gch
        rsM rsL rsH rsPool R) mTi)
    (fun Jti kti ⟨ok_ti, j, _⟩ mTi hrecTi ⟨hj_le, hk_ti, sTi, sN', sP', mN', mV',
      hsN', hsP', hmN', hmV', hsTi_eq, hTin0, hTin1, hmTi⟩ => by
      dsimp only at hrecTi hj_le hsN' hsP' hmN' hmV' hTin0 hTin1 hmTi ⊢
      have hsTi_len := gate_ctx_ok (cx := cx) (R := bytes s.art artBytes ⋆ gateBodyMem s rhs0
        rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr sN' sP' mN' mV'
        dense gsy gcl gch rsM rsL rsH rsPool R) (sep_cast hmTi (by ac_rfl))
      c0_hstep
      refine head_wp_jnz rfl (fun hc => by
        have hj_lt : j.toNat < nin.toNat := by simpa [BitVec.ult] using hc
        refine wp_join_group (fun _ mT2 => ∃ sT2 sN'' sP'' mN'' mV'',
            sN''.length = stkN.length ∧ sP''.length = stkP.length ∧ mN''.length = memoN.length ∧
            mV''.length = memoV.length ∧ sT2 = { s with
              pos := sL.pos, g_outs := sO.g_outs, g_innet := sI.g_innet, g_inneg := sI.g_inneg,
              g_vs := sI.g_vs, g_lnode := sL.g_lnode, g_lmask := sL.g_lmask,
              g_tin := sT2.g_tin } ∧
            (expl = 0#32 → ∀ q < j.toNat + 1,
              sT2.g_tin.getD q 0#64 = BitVec.ofNat 64 (xmask q) &&& all) ∧
            (expl ≠ 0#32 → ∀ ρ : Nat → Bool, ∀ q < j.toNat + 1, ∀ t < 64,
              all.toNat.testBit t = true →
              (∀ r < nl.toNat, (sL.g_lmask.getD r 0#64).toNat.testBit t =
                g.nodeVal ρ (sL.g_lnode.getD r 0#32).toNat) →
              (sT2.g_tin.getD q 0#64).toNat.testBit t =
                g.litVal ρ (bindArr.getD (sI.g_innet.getD q 0#32).toNat 0#32).toNat) ∧
            (arCtxMem cx sT2 ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff
              ruleN partnerArr flippedArr inNetArr outRefArr sN'' sP'' mN'' mV'' dense gsy gcl gch
              rsM rsL rsH rsPool R) mT2)
          (fun _ ⟨okT, _⟩ mT2 ⟨sT2, sN'', sP'', mN'', mV'', hsN'', hsP'', hmN'', hmV'',
            hsT2_eq, hTin0', hTin1', hmT2⟩ => by
            c0_hsteps_nogrp
            refine hrecTi (nin.toNat - (j + 1).toNat) (okT, j + 1, ()) mT2
              (by rw [bv32_add1_toNat (by omega), hk_ti]; omega)
              ⟨by rw [bv32_add1_toNat (by omega)]; omega, rfl,
               sT2, sN'', sP'', mN'', mV'', hsN'', hsP'', hmN'', hmV'', hsT2_eq,
               fun he q hq => hTin0' he q (by rw [bv32_add1_toNat (by omega)] at hq; exact hq),
               fun he ρ q hq => hTin1' he ρ q (by rw [bv32_add1_toNat (by omega)] at hq; exact hq),
               hmT2⟩)
          (fun Jm hJm => by
            c0_hsteps_nogrp
            · have hexp : expl ≠ 0#32 := by simpa [expl] using hc
              have hj_in : (BitVec.setWidth 64 j).toNat < sTi.g_innet.length := by
                rw [bv64_sw_toNat, hsTi_len.g_innet]; omega
              have hti_g : GateSame s sTi := by rw [hsTi_eq]; rfl
              have hbi_in : (BitVec.setWidth 64 (sTi.g_innet[(BitVec.setWidth 64 j).toNat]'
                  hj_in)).toNat < bindArr.length := by
                rw [bv64_sw_toNat, ← d_getD_eq_getElem _ 0#32 hj_in, bv64_sw_toNat,
                  show sTi.g_innet = sI.g_innet by rw [hsTi_eq]]
                exact Nat.lt_of_lt_of_le (hins j.toNat hj_lt) hbind_len
              have hj_in' : j.toNat < sTi.g_innet.length := bv64_sw_toNat ▸ hj_in
              have hbi_in'' : (sTi.g_innet[j.toNat]'hj_in').toNat < bindArr.length := by
                simpa [bv64_sw_toNat] using hbi_in
              let F_tt := array (t := i32) sTi.bind bindArr ⋆ (bytes s.art artBytes ⋆
                u32PadTail s.bind bindArr.length ⋆ array (t := i32) s.rule_off ruleOff ⋆
                u32PadTail s.rule_off ruleOff.length ⋆ array (t := i32) s.rule_n ruleN ⋆
                u32PadTail s.rule_n ruleN.length ⋆ array (t := i32) s.partner partnerArr ⋆
                u32PadTail s.partner partnerArr.length ⋆ arrayPad i8 s.flipped flippedArr ⋆
                arrayPad i32 s.in_net inNetArr ⋆ arrayPad i32 s.out_ref outRefArr ⋆
                rsMem s rsM rsL rsH rsPool ⋆ R)
              have hmTt : (arCtxMem cx sTi ⋆ aigArraysMem sTi rhs0 rhs1 olit ⋆
                  gateScratchMem sTi sN' sP' mN' mV' dense gsy gcl gch ⋆ F_tt) mTi := by
                dsimp only [F_tt]; dsimp only [gateBodyMem] at hmTi
                rw [netTablesMem_unpack] at hmTi
                rw [gate_aig_eq hti_g, gate_scratch_eq hti_g, show sTi.bind = s.bind by rw [hti_g]]
                exact sep_cast hmTi (by ac_rfl)
              have hmTt_ld := hmTt; dsimp only [F_tt] at hmTt_ld
              c0_hsteps_nogrp
              refine gate_ttsim_step hTtsim (cx := cx) (s := sTi)
                (lit := bindArr[(sTi.g_innet[j.toNat]'hj_in').toNat]'hbi_in'') (all := all)
                (stkN := sN') (stkP := sP') (memoN := mN') (memoV := mV') (dense := dense)
                (gsy := gsy) (gcl := gcl) (gch := gch) (F := F_tt) ?_ ?_ ?_ ?_ ?_ ?_ hAig hnl6
                ?_ ?_ ?_ ?_ hmTt (fun okT tv sN'' sP'' mN'' mV'' mT2 hsN'' hsP'' hmN'' hmV''
                  hokT hmT2 => by
                  dsimp only [F_tt] at hmT2; cases hokT_b : okT
                  · refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
                    c0_hstraight
                    refine hFail sTi sN'' sP'' mN'' mV'' mT2 (by rw [hsTi_eq]; exact hrsn)
                      (by rw [hsTi_eq]; exact hrspt) (by rw [hsTi_eq]; exact hposL) hti_g
                      (hsN''.trans hsN') (hsP''.trans hsP') (hmN''.trans hmN') (hmV''.trans hmV')
                      (by rw [gate_aig_eq hti_g, gate_scratch_eq hti_g,
                            show sTi.bind = s.bind by rw [hti_g]] at hmT2
                          dsimp only [gateBodyMem]; rw [netTablesMem_unpack]
                          exact sep_cast hmT2 (by ac_rfl))
                  · refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
                    c0_hstraight
                    have hsTi_b : array (t := i32) sTi.bind bindArr =
                        array (t := i32) s.bind bindArr := by
                      rw [show sTi.bind = s.bind by rw [hti_g]]
                    have hmemI :=
                      ‹(arCtxMem cx { sTi with g_tin := sTi.g_tin.set (BitVec.toNat j) tv } ⋆ _) _›
                    rw [gate_aig_eq hti_g, gate_scratch_eq hti_g, hsTi_b] at hmemI
                    refine hJm (true, ()) _
                      ⟨{ sTi with g_tin := sTi.g_tin.set (BitVec.toNat j) tv },
                       sN'', sP'', mN'', mV'', hsN''.trans hsN',
                       hsP''.trans hsP', hmN''.trans hmN', hmV''.trans hmV', by rw [hsTi_eq],
                       fun he => absurd he hexp, fun _ ρ q hq t ht64 hallt hlmask => ?_,
                       by dsimp only [gateBodyMem]; rw [netTablesMem_unpack]
                          exact sep_cast hmemI (by ac_rfl)⟩
                    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hq) with rfl | hqlt
                    · have := hsTi_len.g_tin; rw [d_getD_set_eq _ 0#64 tv (by omega)]
                      rw [← d_getD_eq_getElem bindArr 0#32 hbi_in'',
                        ← d_getD_eq_getElem sTi.g_innet 0#32 hj_in',
                        show sTi.g_innet = sI.g_innet by rw [hsTi_eq]] at hokT
                      exact hokT hokT_b t ρ ht64 hallt (fun r hr => by
                        rw [show sTi.g_lmask = sL.g_lmask by rw [hsTi_eq],
                          show sTi.g_lnode = sL.g_lnode by rw [hsTi_eq]]; exact hlmask r hr)
                    · rw [getD_set_ne _ 0#64 tv (by omega)]
                      exact hTin1 hexp ρ q hqlt t ht64 hallt hlmask) <;>
                (first | rfl | (rw [hsTi_eq]; first | exact hsI | exact hsM) | omega)
            · have he0 : expl = 0#32 := by simpa [expl] using hc
              apply wp_call_of_spec
              refine hMask6 (j, ()) _ _ _ ⟨by omega, ?_⟩
              c0_hsteps_nogrp
              have hg_len : j.toNat < sTi.g_tin.length := by have := hsTi_len.g_tin; omega
              refine hJm (ok_ti, ()) _ ⟨{ sTi with g_tin := sTi.g_tin.set (BitVec.toNat j) _ },
                sN', sP', mN', mV', hsN', hsP', hmN', hmV', by rw [hsTi_eq],
                fun _ q hq => ?_, fun hne => absurd he0 hne, sep_cast ‹_› (by ac_rfl)⟩
              rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hq) with rfl | hqlt
              · rw [d_getD_set_eq sTi.g_tin 0#64 _ hg_len, BitVec.and_comm]
              · rw [getD_set_ne sTi.g_tin 0#64 _ (by omega)]; exact hTin0 he0 q hqlt)) (fun hc => by
        have hj_nlt : ¬ j.toNat < nin.toNat := by simpa [BitVec.ult] using hc
        have hj_eq : j.toNat = nin.toNat := by omega
        rw [hj_eq] at hTin0 hTin1
        change wp Γ Q X (gateTtoExpr cx ok_ti kraw nout nin nl all) mTi
        exact ar_do_gate_vso_wp hcm hsN' hsP' hmN' hmV' hkraw hnout hnin hnl1 hnl6 hnl_e0 hall
          houts hneU hins hVsIn hposL hsTi_eq (fun he => hbs0 he) hLnode (fun he => hTin0 he)
          (fun he => hTin1 he) hmTi hFail hQ))
    (fun Jti hJti => by
      c0_hsteps
      exact hJti nin.toNat (ok_l, 0#32, ()) mL
        ⟨Nat.zero_le _, Nat.sub_zero _, sL, stkN, stkP, memoN, memoV,
         rfl, rfl, rfl, rfl, (by rw [hsL_eq]),
         fun _ _ hq => absurd hq (Nat.not_lt_zero _),
         fun _ _ _ hq => absurd hq (Nat.not_lt_zero _), hmL⟩)

private theorem ar_do_gate_lmask_wp {Γ : LeanQbe.T.Env}
    {cx : BitVec 64} {ok_nl : Bool} {kraw nout nin nl : BitVec 32} {s sO sI sN : ArCtxState}
    {g : Aig} {artBytes : List UInt8}
    {rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {inNetArr outRefArr stkN stkP memoN : List (BitVec 32)}
    {memoV dense : List (BitVec 64)} {gsy rsM rsPool : List (BitVec 32)}
    {gcl gch rsL rsH : List (BitVec 64)} {R : Mem 64 → Prop} {mNl : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hcm : GateCommon Γ s g artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
      inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool)
    (hnin : nin = 2#32 ∨ nin = 3#32)
    (hnl1 : 1 ≤ nl.toNat) (hnl6 : nl.toNat ≤ 6)
    (hnl_e0 : ((kraw >>> 8#32) &&& 1#32) = 0#32 → nl = nin)
    (hins : ∀ q < nin.toNat, (sI.g_innet.getD q 0#32).toNat < s.n_nets.toNat)
    (hposN : s.pos.toNat ≤ s.nw.toNat → sN.pos.toNat ≤ s.nw.toNat)
    (hsN_eq : sN = { s with
      pos := sN.pos, g_outs := sO.g_outs, g_innet := sI.g_innet,
      g_inneg := sI.g_inneg, g_vs := sI.g_vs })
    (hmN : (arCtxMem cx sN ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff
      ruleN partnerArr flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch
      rsM rsL rsH rsPool R) mNl)
    (hFailPre : GateFailPre cx s artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
      inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R Q)
    (hTail : ∀ sL (ok_l : Bool) (bs : List (BitVec 32)) (all : BitVec 64) mL,
      (∀ t < 2 ^ nl.toNat, all.toNat.testBit t = true) →
      (s.pos.toNat ≤ s.nw.toNat → sL.pos.toNat ≤ s.nw.toNat) →
      sL = { s with
        pos := sL.pos, g_outs := sO.g_outs, g_innet := sI.g_innet, g_inneg := sI.g_inneg,
        g_vs := sI.g_vs, g_lnode := sL.g_lnode, g_lmask := sL.g_lmask } →
      (((kraw >>> 8#32) &&& 1#32) = 0#32 → ∀ q < nin.toNat,
        bs.getD q 0#32 = bindArr.getD (sI.g_innet.getD q 0#32).toNat 0#32) →
      (∀ q < nl.toNat, sL.g_lnode.getD q 0#32 = bs.getD q 0#32 >>> 1#32 ∧
        sL.g_lmask.getD q 0#64 = (BitVec.ofNat 64 (xmask q) &&& all) ^^^
          (if bs.getD q 0#32 &&& 1#32 ≠ 0#32 then all else 0#64)) →
      (arCtxMem cx sL ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff ruleN
        partnerArr flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch
        rsM rsL rsH rsPool R) mL →
      wp Γ Q X (gateTailExpr cx ok_l kraw nout nin nl all) mL) :
    wp Γ Q X (gateLmaskExpr cx ok_nl kraw nout nin nl) mNl := by
  have hNW := hcm.nw; have hMask6 := hcm.mask6; have hart64 := hcm.art64; have hnw4 := hcm.nw4
  have hBind := hcm.bind; have hrsn := hcm.rsn; have hrspt := hcm.rspt
  let expl := (kraw >>> 8#32) &&& 1#32
  let Frest := gateBodyMem s rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
    inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R
  refine wp_join_group (ts := [i64]) (fun ⟨all, _⟩ mAll =>
    mAll = mNl ∧ ∀ t < 2 ^ nl.toNat, all.toNat.testBit t = true)
    (fun _ ⟨all, _⟩ mAll ⟨hm_all, hall⟩ => by
      rw [hm_all] at *
      refine wp_loop_group (ts := [.bool, i32]) (fun kl ⟨_, j, _⟩ mL =>
        j.toNat ≤ nl.toNat ∧ kl = nl.toNat - j.toNat ∧
        ∃ (sL : ArCtxState) (bs : List (BitVec 32)), bs.length = 6 ∧
          (s.pos.toNat ≤ s.nw.toNat → sL.pos.toNat ≤ s.nw.toNat) ∧
          sL = { s with
            pos := sL.pos, g_outs := sO.g_outs, g_innet := sI.g_innet,
            g_inneg := sI.g_inneg, g_vs := sI.g_vs, g_lnode := sL.g_lnode,
            g_lmask := sL.g_lmask } ∧
          (expl = 0#32 → ∀ q < j.toNat, bs.getD q 0#32 =
            bindArr.getD (sI.g_innet.getD q 0#32).toNat 0#32) ∧
          (∀ q < j.toNat,
            sL.g_lnode.getD q 0#32 = bs.getD q 0#32 >>> 1#32 ∧
            sL.g_lmask.getD q 0#64 = (BitVec.ofNat 64 (xmask q) &&& all) ^^^
              (if bs.getD q 0#32 &&& 1#32 ≠ 0#32 then all else 0#64)) ∧
          (arCtxMem cx sL ⋆ bytes s.art artBytes ⋆ Frest) mL)
        (fun Jl kl ⟨ok_l, j, _⟩ mL hrecL ⟨hj_le, hk_l, sL, bs, hbs_l, hposL,
          hsL_eq, hbs0, hLnode, hmL⟩ => by
          dsimp only at hrecL hj_le hbs_l hposL hbs0 hLnode hmL ⊢
          c0_hstep
          refine head_wp_jnz rfl (fun hc => by
            have hj_lt : j.toNat < nl.toNat := by simpa [BitVec.ult] using hc
            refine wp_join_group (ts := [.bool, i32]) (fun ⟨_, b, _⟩ mB => ∃ sB,
              (s.pos.toNat ≤ s.nw.toNat → sB.pos.toNat ≤ s.nw.toNat) ∧
              sB = { s with
                pos := sB.pos, g_outs := sO.g_outs, g_innet := sI.g_innet,
                g_inneg := sI.g_inneg, g_vs := sI.g_vs, g_lnode := sL.g_lnode,
                g_lmask := sL.g_lmask } ∧
              (expl = 0#32 → b =
                bindArr.getD (sI.g_innet.getD j.toNat 0#32).toNat 0#32) ∧
              (arCtxMem cx sB ⋆ bytes s.art artBytes ⋆ Frest) mB)
              (fun _ ⟨okB, b, _⟩ mB ⟨sB, hposB, hsB_eq, hb0, hmB⟩ => by
                have hsB_ok := gate_ctx_ok (cx := cx) (R := bytes s.art artBytes ⋆ Frest)
                  (sep_cast hmB (by ac_rfl))
                have hgl_j : (BitVec.setWidth 64 j).toNat < sB.g_lnode.length := by
                  have := hsB_ok.g_lnode; rw [bv64_sw_toNat]; omega
                have hgm_j : (BitVec.setWidth 64 j).toNat < sB.g_lmask.length := by
                  have := hsB_ok.g_lmask; rw [bv64_sw_toNat]; omega
                have hsB_mk : ∀ (v1 : List (BitVec 32)) (v2 : List (BitVec 64)),
                    { sB with g_lnode := v1, g_lmask := v2 } =
                    { s with
                      pos := sB.pos, g_outs := sO.g_outs, g_innet := sI.g_innet,
                      g_inneg := sI.g_inneg, g_vs := sI.g_vs,
                      g_lnode := v1, g_lmask := v2 } := fun v1 v2 =>
                  congrArg (fun x => { x with g_lnode := v1, g_lmask := v2 }) hsB_eq
                let sB1 := { sB with
                  g_lnode := sB.g_lnode.set (BitVec.setWidth 64 j).toNat (b >>> 1#32) }
                have hsB1_eq : sB1 = { s with
                    pos := sB.pos, g_outs := sO.g_outs, g_innet := sI.g_innet,
                    g_inneg := sI.g_inneg, g_vs := sI.g_vs,
                    g_lnode := sB1.g_lnode, g_lmask := sL.g_lmask } :=
                  congrArg (fun x => { x with g_lnode := sB1.g_lnode }) hsB_eq
                have hgl_j_set : (BitVec.setWidth 64 j).toNat < sB1.g_lnode.length := by
                  dsimp only [sB1]; rw [List.length_set]; exact hgl_j
                c0_hsteps_nogrp
                refine wp_loop_group (ts := [i32]) (fun kq ⟨q, _⟩ mQ =>
                  q.toNat ≤ j.toNat ∧ kq = j.toNat - q.toNat ∧
                  (arCtxMem cx sB1 ⋆ bytes s.art artBytes ⋆ Frest) mQ)
                  (fun Jq kq ⟨q, _⟩ mQ hrecQ ⟨hq_le, hk_q, hmQ⟩ => by
                    dsimp only at hrecQ hq_le hmQ ⊢
                    have hsB1_ok := gate_ctx_ok (cx := cx) (s := sB1)
                      (R := bytes s.art artBytes ⋆ Frest) (sep_cast hmQ (by ac_rfl))
                    have hgl_q_set : (BitVec.setWidth 64 q).toNat < sB1.g_lnode.length := by
                      have := hsB1_ok.g_lnode; rw [bv64_sw_toNat]; omega
                    have hgl_q_nat : q.toNat < sB1.g_lnode.length := by
                      simpa [bv64_sw_toNat] using hgl_q_set
                    c0_hsteps_nogrp
                    · exact hFailPre sB1 mQ (by rw [hsB1_eq]; exact hrsn)
                        (by rw [hsB1_eq]; exact hrspt) hposB (by rw [hsB1_eq]; rfl) hmQ
                    · have hq_lt : q.toNat < j.toNat := by
                        first | exact ‹q.toNat < j.toNat› | simpa [BitVec.ult] using ‹_›
                      refine hrecQ (j.toNat - (q + 1).toNat) (q + 1, ()) mQ
                        (by rw [bv32_add1_toNat (by omega), hk_q]; omega)
                        ⟨by rw [bv32_add1_toNat (by omega)]; omega, rfl, hmQ⟩
                    · apply wp_call_of_spec
                      refine hMask6 (j, ()) _ _ _ ⟨by omega, ?_⟩
                      refine wp_join_group (ts := [i64]) (fun ⟨msk, _⟩ mM =>
                        (arCtxMem cx sB1 ⋆ bytes s.art artBytes ⋆ Frest) mM ∧
                        msk = if b &&& 1#32 ≠ 0#32 then all else 0#64)
                        (fun _ ⟨msk, _⟩ mM ⟨hm_m, hmsk⟩ => by
                          have hgm_j1 : (BitVec.setWidth 64 j).toNat < sB1.g_lmask.length := hgm_j
                          c0_hsteps_nogrp
                          let sB2 := { sB1 with g_lmask := (sB1.g_lmask.set (BitVec.toNat j)
                            ((BitVec.ofNat 64 (xmask j.toNat) &&& all) ^^^ msk)) }
                          refine hrecL (nl.toNat - (j + 1).toNat) (okB, j + 1, ()) _
                            (by rw [bv32_add1_toNat (by omega), hk_l]; omega)
                            ⟨by rw [bv32_add1_toNat (by omega)]; omega, rfl, sB2,
                             bs.set j.toNat b, by simp [hbs_l],
                             hposB, hsB_mk _ _, fun he q hq => ?_, fun q hq => ?_,
                             by have hmM' := ‹(arCtxMem cx { sB1 with g_lmask := _ } ⋆ _) _›
                                dsimp only [Arg.val, lift2] at hmM'
                                rw [BitVec.xor_comm] at hmM'
                                exact sep_cast hmM' (by dsimp only [sB2]; ac_rfl)⟩
                          · rw [bv32_add1_toNat (by omega)] at hq
                            rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hq) with rfl | hqlt
                            · rw [d_getD_set_eq bs 0#32 b (by omega)]; exact hb0 he
                            · rw [getD_set_ne bs 0#32 b (by omega)]; exact hbs0 he q hqlt
                          · have hgl_j1 : j.toNat < sB.g_lnode.length := bv64_sw_toNat ▸ hgl_j
                            have hgm_j1' : j.toNat < sB1.g_lmask.length := bv64_sw_toNat ▸ hgm_j
                            dsimp only [sB2, sB1]
                            rw [bv32_add1_toNat (by omega)] at hq
                            rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hq) with rfl | hqlt
                            · rw [d_getD_set_eq bs 0#32 b (by omega), bv64_sw_toNat,
                                d_getD_set_eq _ 0#32 _ hgl_j1, d_getD_set_eq _ 0#64 _ hgm_j1', hmsk]
                              exact ⟨rfl, rfl⟩
                            · rw [getD_set_ne bs 0#32 b (by omega),
                                getD_set_ne _ 0#32 _ (by rw [bv64_sw_toNat]; omega),
                                getD_set_ne _ 0#64 _ (by omega),
                                show sB.g_lnode = sL.g_lnode by rw [hsB_eq],
                                show sB.g_lmask = sL.g_lmask by rw [hsB_eq]]
                              exact hLnode q hqlt)
                        (fun Jm hJm => by
                          c0_hsteps_nogrp
                          · exact hJm (all, ()) mQ ⟨hmQ, (ite_eq_left hc).symm⟩
                          · exact hJm (0#64, ()) mQ ⟨hmQ, (ite_eq_right (fun h => h hc)).symm⟩))
                  (fun Jq hJq => by
                    c0_hsteps
                    refine hJq j.toNat (0#32, ()) _ ⟨Nat.zero_le _, Nat.sub_zero _, ?_⟩
                    dsimp only [sB1]
                    exact sep_cast ‹(arCtxMem cx _ ⋆ _) _› (by ac_rfl)))
              (fun Jb hJb => by
                c0_hsteps_nogrp
                · have hexp : expl ≠ 0#32 := by simpa [expl] using hc
                  have hmL' : (arCtxMem cx sL ⋆ bytes sL.art artBytes ⋆ Frest) mL := by
                    rw [show sL.art = s.art by rw [hsL_eq]]
                    exact sep_cast hmL (by ac_rfl)
                  refine gate_nw_step (F := Frest) (cx := cx) hNW ?_
                    (by rw [show sL.art = s.art by rw [hsL_eq]]; exact hart64)
                    (by rw [show sL.nw = s.nw by rw [hsL_eq]]; exact hnw4) hmL' ?_ ?_
                  · rfl
                  · intro _ mB1 hmB1
                    c0_hstep <;> first
                      | contradiction
                      | (c0_hsteps_nogrp; rw [show sL.art = s.art by rw [hsL_eq]] at hmB1
                         exact hFailPre sL mB1 (by rw [hsL_eq]; exact hrsn)
                           (by rw [hsL_eq]; exact hrspt) hposL (by rw [hsL_eq]; rfl) hmB1)
                  · intro b sB1 mB1 _ hposB1 _ hsB1_eq hmB1
                    have hposB1' : s.pos.toNat ≤ s.nw.toNat → sB1.pos.toNat ≤ s.nw.toNat :=
                      fun _ => by rw [show sL.nw = s.nw by rw [hsL_eq]] at hposB1; exact hposB1
                    rw [show sL.art = s.art by rw [hsL_eq]] at hmB1
                    (c0_hstep <;> first | contradiction | c0_hsteps_nogrp)
                    · exact hFailPre sB1 mB1 (by rw [hsB1_eq, hsL_eq]; exact hrsn)
                        (by rw [hsB1_eq, hsL_eq]; exact hrspt) hposB1'
                        (by rw [hsB1_eq, hsL_eq]; rfl) hmB1
                    · exact hJb (true, b, ()) mB1 ⟨sB1, hposB1', by rw [hsB1_eq, hsL_eq],
                        fun he => absurd he hexp, hmB1⟩
                · have he0 : expl = 0#32 := by simpa [expl] using hc
                  have hj_nin : j.toNat < nin.toNat := by rw [← hnl_e0 he0]; exact hj_lt
                  have hnin3 : nin.toNat ≤ 3 := by rcases hnin with rfl | rfl <;> decide
                  have hnin_lt_in : j.toNat < sL.g_innet.length := by
                    have := (gate_ctx_ok (cx := cx) (s := sL) (R := bytes s.art artBytes ⋆ Frest)
                      (sep_cast hmL (by ac_rfl))).g_innet; omega
                  have hbind_len := hBind.bind_len
                  have hbi_nl : (BitVec.setWidth 64 (sL.g_innet[j.toNat]'hnin_lt_in)).toNat <
                      bindArr.length := by
                    rw [bv64_sw_toNat, ← d_getD_eq_getElem _ 0#32 hnin_lt_in,
                      show sL.g_innet = sI.g_innet by rw [hsL_eq]]
                    exact Nat.lt_of_lt_of_le (hins j.toNat hj_nin) hbind_len
                  have hbi_nl' : (sL.g_innet[j.toNat]'hnin_lt_in).toNat < bindArr.length := by
                    simpa [bv64_sw_toNat] using hbi_nl
                  have hmLu : (arCtxMem cx sL ⋆ array (t := i32) sL.bind bindArr ⋆
                      array (t := i32) sL.rule_n ruleN ⋆ gateFnbMem s artBytes rhs0 rhs1 olit
                        bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr stkN stkP
                        memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R) mL := by
                    have hmLp := hmL; dsimp only [Frest] at hmLp; rw [gate_fnb_pack] at hmLp
                    rw [show s.bind = sL.bind by rw [hsL_eq],
                      show s.rule_n = sL.rule_n by rw [hsL_eq]] at hmLp
                    exact hmLp
                  c0_hsteps_nogrp; refine hJb (ok_l, _, ()) mL ⟨sL, hposL, hsL_eq, ?_, hmL⟩
                  · intro _; simp only [bv64_sw_toNat]
                    rw [← d_getD_eq_getElem bindArr 0#32 hbi_nl', ← d_getD_eq_getElem sL.g_innet
                      0#32 hnin_lt_in, show sL.g_innet = sI.g_innet by rw [hsL_eq]])) (fun hc => by
            have hj_eq : j.toNat = nl.toNat := by
              have hnot : ¬ j.toNat < nl.toNat := by simpa [BitVec.ult] using hc
              omega
            rw [hj_eq] at hbs0 hLnode
            have hbs0' : expl = 0#32 → ∀ q < nin.toNat, bs.getD q 0#32 =
                bindArr.getD (sI.g_innet.getD q 0#32).toNat 0#32 := fun he q hq =>
              hbs0 he q (by rw [hnl_e0 he]; exact hq)
            change wp Γ Q X (gateTailExpr cx ok_l kraw nout nin nl all) mL
            exact hTail sL ok_l bs all mL hall hposL hsL_eq hbs0' hLnode hmL))
        (fun Jl hJl => by
          c0_hsteps; exact hJl nl.toNat (ok_nl, 0#32, ()) mNl
            ⟨Nat.zero_le _, Nat.sub_zero _, sN, List.replicate 6 0#32, by decide, hposN,
             by rw [hsN_eq], fun _ _ hq => absurd hq (Nat.not_lt_zero _),
             fun _ hq => absurd hq (Nat.not_lt_zero _), hmN⟩))
    (fun Ja hJa => by
      c0_hsteps_nogrp
      · exact hJa (~~~0#64, ()) mNl ⟨rfl, fun t ht => by
          have hnl6' : nl.toNat = 6 := by rw [‹nl = 6#32›]; decide
          have ht64 : t < 64 := by rw [hnl6'] at ht; omega
          have hval : (~~~0#64 : BitVec 64).toNat = 2 ^ 64 - 1 := by decide
          rw [hval, Nat.testBit_two_pow_sub_one]; exact decide_eq_true ht64⟩
      · have hne6 : nl ≠ 6#32 := ‹nl ≠ 6#32›
        refine hJa _ mNl ⟨rfl, fun t ht => ?_⟩
        have hlt6 : nl.toNat ≠ 6 := fun h => hne6 (BitVec.eq_of_toNat_eq h)
        have hnlc : nl.toNat = 1 ∨ nl.toNat = 2 ∨ nl.toNat = 3 ∨
          nl.toNat = 4 ∨ nl.toNat = 5 := by omega
        have hsz : ∀ (m : Nat) (x : BitVec 64),
            x.toNat = 2 ^ m - 1 → t < m → x.toNat.testBit t = true := fun m x hx htm => by
          rw [hx, Nat.testBit_two_pow_sub_one]; exact decide_eq_true htm
        rcases hnlc with h | h | h | h | h
        · rw [BitVec.eq_of_toNat_eq (y := 1#32) h] at ht ⊢; exact hsz 2 _ (by decide) ht
        · rw [BitVec.eq_of_toNat_eq (y := 2#32) h] at ht ⊢; exact hsz 4 _ (by decide) ht
        · rw [BitVec.eq_of_toNat_eq (y := 3#32) h] at ht ⊢; exact hsz 8 _ (by decide) ht
        · rw [BitVec.eq_of_toNat_eq (y := 4#32) h] at ht ⊢; exact hsz 16 _ (by decide) ht
        · rw [BitVec.eq_of_toNat_eq (y := 5#32) h] at ht ⊢; exact hsz 32 _ (by decide) ht)

private theorem ar_do_gate_nl_wp {Γ : LeanQbe.T.Env}
    {cx : BitVec 64} {kraw nout nin : BitVec 32} {s sO sI : ArCtxState} {g : Aig}
    {artBytes : List UInt8}
    {rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {inNetArr outRefArr stkN stkP memoN : List (BitVec 32)}
    {memoV dense : List (BitVec 64)} {gsy rsM rsPool : List (BitVec 32)}
    {gcl gch rsL rsH : List (BitVec 64)} {R : Mem 64 → Prop} {mI : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hcm : GateCommon Γ s g artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
      inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool)
    (hkraw : (kraw &&& 255#32) = 6#32 → nout = 2#32)
    (hnout : nout = 1#32 ∨ nout = 2#32) (hnin : nin = 2#32 ∨ nin = 3#32)
    (houts : ∀ q < nout.toNat, (sO.g_outs.getD q 0#32).toNat < s.n_nets.toNat)
    (hneU : nout.toNat = 2 → sO.g_outs.getD 0 0#32 ≠ sO.g_outs.getD 1 0#32)
    (hins : ∀ q < nin.toNat, (sI.g_innet.getD q 0#32).toNat < s.n_nets.toNat)
    (hVsIn : ∀ q < nin.toNat, (sI.g_vs.getD q 0#32).toNat / 2 < s.n_nets.toNat)
    (hposI : s.pos.toNat ≤ s.nw.toNat → sI.pos.toNat ≤ s.nw.toNat)
    (hsI_eq : sI = { s with
      pos := sI.pos, g_outs := sO.g_outs, g_innet := sI.g_innet,
      g_inneg := sI.g_inneg, g_vs := sI.g_vs })
    (hmI : (arCtxMem cx sI ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff
      ruleN partnerArr flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch
      rsM rsL rsH rsPool R) mI)
    (hFailPre : GateFailPre cx s artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr
      flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R Q)
    (hFail : GateFailScratch cx s artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr
      flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R Q)
    (hQ : GatePostQ cx s g artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
      inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R Q) :
    wp Γ Q X (gateNlExpr cx kraw nout nin) mI := by
  have hNW := hcm.nw; have hart64 := hcm.art64; have hnw4 := hcm.nw4
  have hrsn := hcm.rsn; have hrspt := hcm.rspt
  let expl := (kraw >>> 8#32) &&& 1#32
  let Frest := gateBodyMem s rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
    inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R
  refine wp_join_group (ts := [.bool, i32]) (fun ⟨_, nl, _⟩ mNl =>
    1 ≤ nl.toNat ∧ nl.toNat ≤ 6 ∧ (expl = 0#32 → nl = nin) ∧
    ∃ sN, (s.pos.toNat ≤ s.nw.toNat → sN.pos.toNat ≤ s.nw.toNat) ∧
      sN = { s with
        pos := sN.pos, g_outs := sO.g_outs, g_innet := sI.g_innet,
        g_inneg := sI.g_inneg, g_vs := sI.g_vs } ∧
      (arCtxMem cx sN ⋆ bytes s.art artBytes ⋆ Frest) mNl) ?_ ?_
  · rintro _ ⟨ok_nl, nl, _⟩ mNl ⟨hnl1, hnl6, hnl_e0, sN, hposN, hsN_eq, hmN⟩
    change wp Γ Q X (gateLmaskExpr cx ok_nl kraw nout nin nl) mNl
    exact ar_do_gate_lmask_wp hcm hnin hnl1 hnl6 hnl_e0 hins hposN hsN_eq hmN hFailPre
      (fun sL ok_l bs all mL hall hposL hsL_eq hbs0 hLnode hmL =>
        ar_do_gate_tail_wp hcm hkraw hnout hnin hnl1 hnl6 hnl_e0 hall houts hneU hins hVsIn
          hposL hsL_eq hbs0 hLnode hmL hFail hQ)
  · intro Jnl hJnl
    c0_hsteps_nogrp
    · have hmI' : (arCtxMem cx sI ⋆ bytes sI.art artBytes ⋆ Frest) mI := by
        rw [show sI.art = s.art by rw [hsI_eq]]; exact hmI
      refine gate_nw_step (F := Frest) (cx := cx) hNW ?_
        (by rw [show sI.art = s.art by rw [hsI_eq]]; exact hart64)
        (by rw [show sI.nw = s.nw by rw [hsI_eq]]; exact hnw4) hmI' ?_ ?_
      · rfl
      · intro _ mN1 hmN1
        c0_hstep <;> first
          | contradiction
          | (c0_hsteps_nogrp; rw [show sI.art = s.art by rw [hsI_eq]] at hmN1
             exact hFailPre sI mN1 (by rw [hsI_eq]; exact hrsn)
               (by rw [hsI_eq]; exact hrspt) hposI (by rw [hsI_eq]; rfl) hmN1)
      · intro nl sN1 mN1 _ hposN1 _ hsN1_eq hmN1
        have hposN1' : s.pos.toNat ≤ s.nw.toNat → sN1.pos.toNat ≤ s.nw.toNat := fun _ => by
          rw [show sI.nw = s.nw by rw [hsI_eq]] at hposN1; exact hposN1
        rw [show sI.art = s.art by rw [hsI_eq]] at hmN1
        (c0_hstep <;> first | contradiction | c0_hsteps_nogrp) <;>
          try {
            exact hFailPre sN1 mN1 (by rw [hsN1_eq, hsI_eq]; exact hrsn)
              (by rw [hsN1_eq, hsI_eq]; exact hrspt) hposN1' (by rw [hsN1_eq, hsI_eq]; rfl) hmN1
          }
        · have hnl1' : 1 ≤ nl.toNat := BitVec.le_def.mp (BitVec.not_lt.mp ‹¬ nl < 1#32›)
          have hnl6' : nl.toNat ≤ 6 := BitVec.le_def.mp (BitVec.not_lt.mp ‹¬ 6#32 < nl›)
          exact hJnl (true, nl, ()) mN1 ⟨hnl1', hnl6', fun he => absurd he ‹expl ≠ 0#32›,
            sN1, hposN1', by rw [hsN1_eq, hsI_eq], hmN1⟩
    · have hnin1 : 1 ≤ nin.toNat := by rcases hnin with rfl | rfl <;> decide
      have hnin6 : nin.toNat ≤ 6 := by rcases hnin with rfl | rfl <;> decide
      exact hJnl (true, nin, ()) mI ⟨hnin1, hnin6, fun _ => rfl, sI, hposI, hsI_eq, hmI⟩

private theorem ar_do_gate_in_wp {Γ : LeanQbe.T.Env}
    {cx : BitVec 64} {kraw nout nin : BitVec 32} {s sO : ArCtxState} {g : Aig}
    {artBytes : List UInt8}
    {rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {inNetArr outRefArr stkN stkP memoN : List (BitVec 32)}
    {memoV dense : List (BitVec 64)} {gsy rsM rsPool : List (BitVec 32)}
    {gcl gch rsL rsH : List (BitVec 64)} {R : Mem 64 → Prop} {mO : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hcm : GateCommon Γ s g artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
      inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool)
    (hnin : nin = 2#32 ∨ nin = 3#32)
    (hposO : s.pos.toNat ≤ s.nw.toNat → sO.pos.toNat ≤ s.nw.toNat)
    (hsO_eq : sO = { s with pos := sO.pos, g_outs := sO.g_outs })
    (hmO : (arCtxMem cx sO ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff
      ruleN partnerArr flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch
      rsM rsL rsH rsPool R) mO)
    (hFailPre : GateFailPre cx s artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr
      flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R Q)
    (hNl : ∀ sI mI,
      (∀ q < nin.toNat, (sI.g_innet.getD q 0#32).toNat < s.n_nets.toNat) →
      (∀ q < nin.toNat, (sI.g_vs.getD q 0#32).toNat / 2 < s.n_nets.toNat) →
      (s.pos.toNat ≤ s.nw.toNat → sI.pos.toNat ≤ s.nw.toNat) →
      sI = { s with
        pos := sI.pos, g_outs := sO.g_outs, g_innet := sI.g_innet,
        g_inneg := sI.g_inneg, g_vs := sI.g_vs } →
      (arCtxMem cx sI ⋆ bytes s.art artBytes ⋆ gateBodyMem s rhs0 rhs1 olit bindArr ruleOff
        ruleN partnerArr flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch
        rsM rsL rsH rsPool R) mI →
      wp Γ Q X (gateNlExpr cx kraw nout nin) mI) :
    wp Γ Q X (gateInExpr cx kraw nout nin) mO := by
  have hNW := hcm.nw; have hart64 := hcm.art64; have hnw4 := hcm.nw4
  have hbind_len : s.n_nets.toNat ≤ bindArr.length := hcm.bind.bind_len
  have hrsn := hcm.rsn; have hrspt := hcm.rspt
  have hn2 : nin.toNat ≤ 3 := by rcases hnin with rfl | rfl <;> decide
  let Frest := gateBodyMem s rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
    inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R
  let Fnb := gateFnbMem s artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
    inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R
  refine wp_loop_group (ts := [.bool, i32]) (fun kj ⟨okI, j, _⟩ mI =>
    okI = true ∧ j.toNat ≤ nin.toNat ∧ kj = nin.toNat - j.toNat ∧ ∃ sI,
      (s.pos.toNat ≤ s.nw.toNat → sI.pos.toNat ≤ s.nw.toNat) ∧
      sI = { s with
        pos := sI.pos, g_outs := sO.g_outs, g_innet := sI.g_innet,
        g_inneg := sI.g_inneg, g_vs := sI.g_vs } ∧
      (∀ q < j.toNat, (sI.g_innet.getD q 0#32).toNat < s.n_nets.toNat) ∧
      (∀ q < j.toNat, (sI.g_vs.getD q 0#32).toNat / 2 < s.n_nets.toNat) ∧
      (arCtxMem cx sI ⋆ bytes s.art artBytes ⋆ Frest) mI)
    (fun J2 kj ⟨okI, j, _⟩ mI hrec2 ⟨hokI, hj_le, hk_2, sI, hposI, hsI_eq, hInsI, hVsI, hmI⟩ => by
      dsimp only at hrec2 hj_le hposI hInsI hmI ⊢
      c0_hsteps_nogrp
      · have hj_lt : j.toNat < nin.toNat := by simpa [BitVec.ult] using hc
        have hmI' : (arCtxMem cx sI ⋆ bytes sI.art artBytes ⋆ Frest) mI := by
          rw [show sI.art = s.art by rw [hsI_eq]]; exact hmI
        refine gate_nw_step (F := Frest) (cx := cx) hNW rfl
          (by rw [show sI.art = s.art by rw [hsI_eq]]; exact hart64)
          (by rw [show sI.nw = s.nw by rw [hsI_eq]]; exact hnw4) hmI' ?_ ?_
        · intro _ mI1 hmI1
          c0_hstep <;> first
            | contradiction
            | (c0_hsteps_nogrp; rw [show sI.art = s.art by rw [hsI_eq]] at hmI1
               exact hFailPre sI mI1 (by rw [hsI_eq]; exact hrsn)
                 (by rw [hsI_eq]; exact hrspt) hposI (by rw [hsI_eq]; rfl) hmI1)
        · intro wd sI1 mI1 _ hposI1 _ hsI1_eq hmI1
          have hposI1' : s.pos.toNat ≤ s.nw.toNat → sI1.pos.toNat ≤ s.nw.toNat := fun _ => by
            rw [show sI.nw = s.nw by rw [hsI_eq]] at hposI1; exact hposI1
          have hsI1_ok := gate_ctx_ok (cx := cx) (s := sI1)
            (R := bytes sI.art artBytes ⋆ Frest) (sep_cast hmI1 (by ac_rfl))
          have hj_lt_in : j.toNat < sI1.g_innet.length := by have := hsI1_ok.g_innet; omega
          rw [show sI.art = s.art by rw [hsI_eq]] at hmI1
          have hmI1u : (arCtxMem cx sI1 ⋆ array (t := i32) sI1.bind bindArr ⋆
              array (t := i32) sI1.rule_n ruleN ⋆ Fnb) mI1 := by
            dsimp only [Frest, Fnb] at hmI1 ⊢; rw [gate_fnb_pack] at hmI1
            rw [show sI1.bind = s.bind by rw [hsI1_eq, hsI_eq],
              show sI1.rule_n = s.rule_n by rw [hsI1_eq, hsI_eq]]
            exact hmI1
          let sI2 := { sI1 with
            g_innet := sI1.g_innet.set (BitVec.toNat j) (wd >>> 1#32),
            g_inneg := sI1.g_inneg.set (BitVec.toNat j) (wd &&& 1#32) }
          have hsnI2 : sI2.rs_n.toNat ≤ s.rs_cap.toNat := by
            dsimp only [sI2]; rw [hsI1_eq, hsI_eq]; exact hrsn
          have hsptI2 : sI2.rs_ptop.toNat ≤ s.rs_pcap.toNat := by
            dsimp only [sI2]; rw [hsI1_eq, hsI_eq]; exact hrspt
          have hsI2_g : GateSame s sI2 := by dsimp only [sI2]; rw [hsI1_eq, hsI_eq]; rfl
          have hPackI : ∀ (sX : ArCtxState) mF P, (arCtxMem cx sX ⋆ P) mF →
              P = (array (t := i32) sI1.bind bindArr ⋆ array (t := i32) sI1.rule_n ruleN ⋆ Fnb) →
              (arCtxMem cx sX ⋆ bytes s.art artBytes ⋆ Frest) mF := by
            intro sX mF P hmF hP
            have hmF' : (arCtxMem cx sX ⋆ array (t := i32) s.bind bindArr ⋆
                array (t := i32) s.rule_n ruleN ⋆ Fnb) mF := by
              subst hP; rw [show sI1.bind = s.bind by rw [hsI1_eq, hsI_eq],
                show sI1.rule_n = s.rule_n by rw [hsI1_eq, hsI_eq]] at hmF
              exact sep_cast hmF (by ac_rfl)
            dsimp only [Frest, Fnb]; rw [← gate_fnb_pack] at hmF'; exact hmF'
          let failI2 := fun {P} mF (hmF : (arCtxMem cx sI2 ⋆ P) mF)
              (hP : P = (array (t := i32) sI1.bind bindArr ⋆
                array (t := i32) sI1.rule_n ruleN ⋆ Fnb)) =>
            hFailPre sI2 mF hsnI2 hsptI2 hposI1' hsI2_g (hPackI sI2 mF P hmF hP)
          (c0_hstep <;> first | contradiction | c0_hsteps_nogrp)
          · exact failI2 _ ‹_› (by try simp only [Std.ExtHashMap.sep_emp]; ac_rfl)
          · have hin_lt : (wd >>> 1#32).toNat < s.n_nets.toNat := by
              rw [show s.n_nets = sI1.n_nets by rw [hsI1_eq, hsI_eq]]; exact Nat.lt_of_not_le hc
            have hin_lt_b : (BitVec.setWidth 64 (wd >>> 1#32)).toNat < bindArr.length := by
              rw [bv64_sw_toNat]; omega
            dsimp only; c0_hsteps_nogrp
            · exact failI2 _ ‹_› (by try simp only [Std.ExtHashMap.sep_emp]; ac_rfl)
            · let sI3 := { sI2 with g_vs := sI2.g_vs.set (BitVec.toNat j) (2#32 * (wd >>> 1#32)) }
              refine hrec2 (nin.toNat - (j + 1).toNat) (true, j + 1, ()) _
                (by rw [bv32_add1_toNat (by omega), hk_2]; omega)
                ⟨rfl, by rw [bv32_add1_toNat (by omega)]; omega, rfl, sI3,
                 by dsimp only [sI3, sI2]; exact hposI1',
                 by dsimp only [sI3, sI2]; rw [hsI1_eq, hsI_eq], fun q hq => ?_,
                 fun q hq => ?_,
                 hPackI sI3 _ _ ‹(arCtxMem cx { sI2 with g_vs := _ } ⋆ _) _›
                   (by try simp only [Std.ExtHashMap.sep_emp]; ac_rfl)⟩
              · dsimp only [sI3, sI2]; rw [bv32_add1_toNat (by omega)] at hq
                rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hq) with rfl | hqlt
                · rw [d_getD_set_eq _ 0#32 _ hj_lt_in]; exact hin_lt
                · rw [getD_set_ne _ 0#32 _ (by omega), hsI1_eq]
                  exact hInsI q hqlt
              · have hj_lt_vs : j.toNat < sI2.g_vs.length := by
                  have := hsI1_ok.g_vs; dsimp only [sI2]; omega
                dsimp only [sI3, sI2]; rw [bv32_add1_toNat (by omega)] at hq
                rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hq) with rfl | hqlt
                · rw [d_getD_set_eq _ 0#32 _ hj_lt_vs, BitVec.toNat_mul,
                    show (2#32 : BitVec 32).toNat = 2 from rfl]
                  have hnn30 := hcm.nn30
                  rw [Nat.mod_eq_of_lt (by omega)]; omega
                · rw [getD_set_ne _ 0#32 _ (by omega), show sI2.g_vs = sI1.g_vs from rfl,
                    hsI1_eq]
                  exact hVsI q hqlt
      · have hj_nlt : ¬ j.toNat < nin.toNat := by simpa [BitVec.ult] using hc
        have hj_eq : j.toNat = nin.toNat := by omega
        rw [hj_eq] at hInsI hVsI; subst hokI
        change wp Γ Q X (gateNlExpr cx kraw nout nin) mI
        exact hNl sI mI hInsI hVsI hposI hsI_eq hmI)
    (fun J2 hJ2 => by
      c0_hsteps
      exact hJ2 nin.toNat (true, 0#32, ()) mO
        ⟨rfl, Nat.zero_le _, Nat.sub_zero _, sO, hposO, by rw [hsO_eq],
         fun _ h => absurd h (Nat.not_lt_zero _),
         fun _ h => absurd h (Nat.not_lt_zero _), hmO⟩)

theorem ar_do_gate_wp (Γ : LeanQbe.T.Env)
    (hNW : ∀ xs m Q X, arNextWordSpec xs m Q X → Γ "ar_next_word" [i64] [.bool, i32] xs m Q X)
    (hMask6 : ∀ xs m Q X, arMask6Spec xs m Q X → Γ "ar_mask6" [i32] [i64] xs m Q X)
    (hTtsim : ∀ xs m Q X, arTtsimSpec xs m Q X →
      Γ "ar_ttsim" [i64, i32, i32, i64] [.bool, i64] xs m Q X)
    (hDzero : ∀ xs m Q X, arDzeroSpec xs m Q X → Γ "ar_dzero" [i64] [] xs m Q X)
    (hDlit : ∀ xs m Q X, arDlitSpec xs m Q X → Γ "ar_dlit" [i64, i32, i32] [] xs m Q X)
    (hDmul : ∀ xs m Q X, arDmulSpec xs m Q X → Γ "ar_dmul" [i64, i64, i64] [] xs m Q X)
    (hDaxpy : ∀ xs m Q X, arDaxpySpec xs m Q X → Γ "ar_daxpy" [i64, i64, i64] [] xs m Q X)
    (hDcanon : ∀ xs m Q X, arDcanonSpec xs m Q X → Γ "ar_dcanon" [i64, i64] [i32] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    (hInstall : ∀ xs m Q X, arInstallRuleSpec xs m Q X →
      Γ "ar_install_rule" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ xs m Q X, arDoGateSpec xs m Q X → Func.wp Γ ar_do_gate_body xs m Q X := by
  rintro ⟨cx, ⟨⟩⟩ m Q X
    ⟨s, g, artBytes, rhs0, rhs1, olit, bindArr, ruleOff, ruleN, partnerArr, flippedArr,
     inNetArr, outRefArr, stkN, stkP, memoN, memoV, dense, gsy, gcl, gch, rsM, rsL, rsH, rsPool,
     R, hsI, hsM, hgM, hnn30, hrcap30, hrpcap32, hart64, hnw4, hsn, hsp, hmn, hmv, hdense,
     hgsy, hgcl, hgch, hmasks, hAig, hBind, hTot, hRsOk, hRsSorted, hAllRep, hm, hQ⟩
  have hRep0 := hAllRep (fun _ => false); have hrn_len := hRep0.2.2.1
  have hrsn := hRep0.2.2.2.1; have hrspt := hRep0.2.2.2.2.1
  have hbind_len := hBind.bind_len; have hnout1 := hBind.out_bounds.1
  let hcm : GateCommon Γ s g artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
      inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool :=
    ⟨hNW, hMask6, hTtsim, hDzero, hDlit, hDmul, hDaxpy, hDcanon, hCadd, hInstall, hsI, hsM, hnn30,
     hrcap30, hrpcap32, hart64, hnw4, hsn, hsp, hmn, hmv, hdense, hgsy, hgcl, hgch, hmasks, hAig,
     hBind, hnout1, hrsn, hrspt, hTot, hRsOk, hRsSorted, hAllRep⟩
  let Frest := gateBodyMem s rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
    inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R
  let Fnb := gateFnbMem s artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr flippedArr
    inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH rsPool R
  let failPre : GateFailPre cx s artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr
      flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH
      rsPool R Q :=
    fun sC mC hsnC hsptC hpos hsC hmC =>
      hQ false sC ruleOff ruleN partnerArr stkN stkP memoN memoV dense gsy gcl gch
        rsM rsL rsH rsPool mC hsnC hsptC hpos hsC rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl (fun h => by cases h) (by
          dsimp only [gateBodyMem] at hmC ⊢
          rw [gate_mem_same_rw hsC]; exact sep_cast hmC (by ac_rfl))
  let failScratch : GateFailScratch cx s artBytes rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr
      flippedArr inNetArr outRefArr stkN stkP memoN memoV dense gsy gcl gch rsM rsL rsH
      rsPool R Q :=
    fun sC sN sP mN mV mC hsnC hsptC hpos hsC hsN hsP hmN hmV hmC =>
      hQ false sC ruleOff ruleN partnerArr sN sP mN mV dense gsy gcl gch rsM rsL rsH rsPool mC
        hsnC hsptC hpos hsC rfl rfl rfl hsN hsP hmN hmV rfl rfl rfl rfl rfl rfl rfl rfl
        (fun h => by cases h) (by
          dsimp only [gateBodyMem] at hmC ⊢
          rw [gate_mem_same_rw hsC]; exact sep_cast hmC (by ac_rfl))
  c0_hsteps_nogrp; refine gate_nw_step (F := Frest) (cx := cx) hNW rfl hart64 hnw4
    (sep_cast hm (by dsimp only [Frest, gateBodyMem]; ac_rfl)) ?_ ?_
  · intro _ m1 hm1
    c0_hstep <;> first | contradiction | (c0_hsteps_nogrp; exact failPre s m1 hrsn hrspt id rfl hm1)
  · intro kraw s1 m1 _ hs1_pos _ hs1_eq hm1
    have hs1_g : GateSame s s1 := by rw [hs1_eq]; rfl
    have hsn1 : s1.rs_n.toNat ≤ s.rs_cap.toNat := by rw [hs1_eq]; exact hrsn
    have hspt1 : s1.rs_ptop.toNat ≤ s.rs_pcap.toNat := by rw [hs1_eq]; exact hrspt
    (c0_hstep <;> first | contradiction | c0_hsteps_nogrp) <;>
      try exact failPre s1 m1 hsn1 hspt1 (fun _ => hs1_pos) hs1_g hm1
    · let kind := kraw &&& 255#32
      refine wp_join_group (ts := [i32]) (fun ⟨nout, _⟩ mn => mn = m1 ∧
        (nout = 1#32 ∨ nout = 2#32) ∧ (kind = 6#32 → nout = 2#32)) ?_ ?_
      · rintro _ ⟨nout, _⟩ mn ⟨hm_n, hnout, hkind6⟩
        rw [hm_n] at *
        refine wp_join_group (ts := [i32]) (fun ⟨nin, _⟩ mni =>
          mni = m1 ∧ (nin = 2#32 ∨ nin = 3#32)) ?_ ?_
        · rintro _ ⟨nin, _⟩ mni ⟨hm_ni, hnin⟩
          rw [hm_ni] at *
          have ho2 : nout.toNat ≤ 2 := by rcases hnout with rfl | rfl <;> decide
          refine wp_loop_group (ts := [.bool, i32]) (fun kj ⟨okO, j, _⟩ mO =>
            okO = true ∧ j.toNat ≤ nout.toNat ∧ kj = nout.toNat - j.toNat ∧ ∃ sO,
              (s.pos.toNat ≤ s.nw.toNat → sO.pos.toNat ≤ s.nw.toNat) ∧
              sO = { s with pos := sO.pos, g_outs := sO.g_outs } ∧
              (∀ q < j.toNat, (sO.g_outs.getD q 0#32).toNat < s.n_nets.toNat) ∧
              (arCtxMem cx sO ⋆ bytes s.art artBytes ⋆ Frest) mO)
            (fun J1 kj ⟨okO, j, _⟩ mO hrec1
                ⟨hokO, hj_le, hk_1, sO, hposO, hsO_eq, hOutsO, hmO⟩ => by
              dsimp only at hrec1 hj_le hposO hOutsO hmO ⊢
              c0_hsteps_nogrp
              · have hj_lt : j.toNat < nout.toNat := by simpa [BitVec.ult] using hc
                have hmO' : (arCtxMem cx sO ⋆ bytes sO.art artBytes ⋆ Frest) mO := by
                  rw [show sO.art = s.art by rw [hsO_eq]]; exact hmO
                refine gate_nw_step (F := Frest) (cx := cx) hNW rfl
                  (by rw [show sO.art = s.art by rw [hsO_eq]]; exact hart64)
                  (by rw [show sO.nw = s.nw by rw [hsO_eq]]; exact hnw4) hmO' ?_ ?_
                · intro _ mO1 hmO1
                  c0_hstep <;> first
                    | contradiction
                    | (c0_hsteps_nogrp; rw [show sO.art = s.art by rw [hsO_eq]] at hmO1
                       exact failPre sO mO1 (by rw [hsO_eq]; exact hrsn)
                         (by rw [hsO_eq]; exact hrspt) hposO (by rw [hsO_eq]; rfl) hmO1)
                · intro outj sO1 mO1 _ hposO1 _ hsO1_eq hmO1
                  have hposO1' : s.pos.toNat ≤ s.nw.toNat → sO1.pos.toNat ≤ s.nw.toNat :=
                    fun _ => by rw [show sO.nw = s.nw by rw [hsO_eq]] at hposO1; exact hposO1
                  have hgo_len : j.toNat < sO1.g_outs.length := by
                    have hgo := (gate_ctx_ok (cx := cx) (s := sO1)
                      (R := bytes sO.art artBytes ⋆ Frest) (sep_cast hmO1 (by ac_rfl))).g_outs
                    omega
                  have hgo_sw : (BitVec.setWidth 64 j).toNat < sO1.g_outs.length := by
                    rw [bv64_sw_toNat]; exact hgo_len
                  rw [show sO.art = s.art by rw [hsO_eq]] at hmO1
                  have hmO1u : (arCtxMem cx sO1 ⋆ array (t := i32) sO1.bind bindArr ⋆
                      array (t := i32) sO1.rule_n ruleN ⋆ Fnb) mO1 := by
                    dsimp only [Frest, Fnb] at hmO1 ⊢; rw [gate_fnb_pack] at hmO1
                    rw [show sO1.bind = s.bind by rw [hsO1_eq, hsO_eq],
                      show sO1.rule_n = s.rule_n by rw [hsO1_eq, hsO_eq]]
                    exact hmO1
                  let sO2 := { sO1 with g_outs := sO1.g_outs.set (BitVec.toNat j) outj }
                  have hsnO2 : sO2.rs_n.toNat ≤ s.rs_cap.toNat := by
                    dsimp [sO2]; rw [hsO1_eq, hsO_eq]; exact hrsn
                  have hsptO2 : sO2.rs_ptop.toNat ≤ s.rs_pcap.toNat := by
                    dsimp [sO2]; rw [hsO1_eq, hsO_eq]; exact hrspt
                  have hsO2_g : GateSame s sO2 := by dsimp only [sO2]; rw [hsO1_eq, hsO_eq]; rfl
                  let hPackO : ∀ (sX : ArCtxState) mF P, (arCtxMem cx sX ⋆ P) mF →
                      P = (array (t := i32) sO1.bind bindArr ⋆
                        array (t := i32) sO1.rule_n ruleN ⋆ Fnb) →
                      (arCtxMem cx sX ⋆ bytes s.art artBytes ⋆ Frest) mF := by
                    intro sX mF P hmF hP
                    have hmF' : (arCtxMem cx sX ⋆ array (t := i32) s.bind bindArr ⋆
                        array (t := i32) s.rule_n ruleN ⋆ Fnb) mF := by
                      subst hP; rw [show sO1.bind = s.bind by rw [hsO1_eq, hsO_eq],
                        show sO1.rule_n = s.rule_n by rw [hsO1_eq, hsO_eq]] at hmF
                      exact sep_cast hmF (by ac_rfl)
                    dsimp only [Frest, Fnb]; rw [← gate_fnb_pack] at hmF'; exact hmF'
                  let failO2 := fun {P} mF (hmF : (arCtxMem cx sO2 ⋆ P) mF)
                      (hP : P = (array (t := i32) sO1.bind bindArr ⋆
                        array (t := i32) sO1.rule_n ruleN ⋆ Fnb)) =>
                    failPre sO2 mF hsnO2 hsptO2 hposO1' hsO2_g (hPackO sO2 mF P hmF hP)
                  (c0_hstep <;> first | contradiction | c0_hsteps_nogrp)
                  · exact failO2 _ ‹_› (by try simp only [Std.ExtHashMap.sep_emp]; ac_rfl)
                  · have houtj_lt : outj.toNat < s.n_nets.toNat := by
                      have h1 : ¬ sO1.n_nets.toNat ≤ outj.toNat := hc
                      rw [show sO1.n_nets = s.n_nets by rw [hsO1_eq, hsO_eq]] at h1; omega
                    have hj_b : (BitVec.setWidth 64 outj).toNat < bindArr.length := by
                      rw [bv64_sw_toNat]; omega
                    have hj_rn : (BitVec.setWidth 64 outj).toNat < ruleN.length := by
                      rw [bv64_sw_toNat]; omega
                    c0_hsteps_nogrp <;> first
                      | exact failO2 _ ‹_› (by try simp only [Std.ExtHashMap.sep_emp]; ac_rfl)
                      | refine wp_join_group (ts := []) (fun _ mF => (arCtxMem cx sO2 ⋆
                          (array (t := i32) sO1.bind bindArr ⋆
                            array (t := i32) sO1.rule_n ruleN ⋆ Fnb)) mF) ?_ ?_
                    · rintro _ ⟨⟩ mF hmF; c0_hsteps_nogrp
                      refine hrec1 (nout.toNat - (j + 1).toNat) (true, j + 1, ()) _
                        (by rw [bv32_add1_toNat (by omega), hk_1]; omega)
                        ⟨rfl, by rw [bv32_add1_toNat (by omega)]; omega, rfl, sO2, hposO1',
                         by dsimp only [sO2]; rw [hsO1_eq, hsO_eq], fun q hq => ?_,
                         hPackO sO2 _ _ hmF rfl⟩
                      dsimp only [sO2]; rw [bv32_add1_toNat (by omega)] at hq
                      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hq) with rfl | hqlt
                      · rw [d_getD_set_eq _ 0#32 _ hgo_len]; exact houtj_lt
                      · rw [getD_set_ne _ 0#32 _ (by omega), hsO1_eq]; exact hOutsO q hqlt
                    · intro Jm hJm; c0_hsteps_nogrp <;> first
                        | exact hJm () _ (sep_cast ‹(arCtxMem cx sO2 ⋆ _) _› (by ac_rfl))
                        | exact failO2 _ ‹_› (by try simp only [Std.ExtHashMap.sep_emp]; ac_rfl)
              · refine wp_join_group (fun _ mU =>
                  mU = mO ∧ (nout.toNat = 2 → sO.g_outs.getD 0 0#32 ≠ sO.g_outs.getD 1 0#32))
                  ?_ (fun Ju hJu => by
                    have hsO_ok := gate_ctx_ok (cx := cx) (s := sO)
                      (R := bytes s.art artBytes ⋆ Frest) (sep_cast hmO (by ac_rfl))
                    have := hsO_ok.g_outs; c0_hsteps_nogrp
                    · exact failPre sO mO (by rw [hsO_eq]; exact hrsn)
                        (by rw [hsO_eq]; exact hrspt) hposO (by rw [hsO_eq]; rfl) hmO
                    · refine hJu () mO ⟨rfl, fun hnout2 => ?_⟩
                      have hne01 : sO.g_outs[0] ≠ sO.g_outs[1] := ‹_›
                      rwa [d_getD_eq_getElem _ _ (by omega), d_getD_eq_getElem _ _ (by omega)]
                    · exact hJu () mO ⟨rfl, fun hn2 =>
                        absurd (BitVec.eq_of_toNat_eq (by simpa using hn2)) hc⟩)
                rintro _ ⟨⟩ mU ⟨hm_u, hneU⟩; rw [hm_u] at *
                have hj_nlt : ¬ j.toNat < nout.toNat := by simpa [BitVec.ult] using hc
                have houts : ∀ q < nout.toNat, (sO.g_outs.getD q 0#32).toNat < s.n_nets.toNat := by
                  rw [show nout.toNat = j.toNat by omega]; exact hOutsO
                subst hokO; change wp Γ Q X (gateInExpr cx kraw nout nin) mO
                exact ar_do_gate_in_wp hcm hnin hposO hsO_eq hmO failPre
                  (fun sI mI hins hvs hposI hsI_eq hmI =>
                    ar_do_gate_nl_wp hcm (fun hk => hkind6 hk) hnout hnin houts hneU hins hvs
                      hposI hsI_eq hmI failPre failScratch
                      (fun ok sC rO rN pa sN sP mN mV dn gy gl gh rM rL rH rP mC h1 h2 h3 h4 h5 h6
                        h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hmC =>
                        hQ ok sC rO rN pa sN sP mN mV dn gy gl gh rM rL rH rP mC h1 h2 h3 h4 h5 h6
                          h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
                          (sep_cast hmC (by dsimp only [gateBodyMem]; ac_rfl))))) ?_
          · intro J1 hJ1; c0_hsteps
            exact hJ1 nout.toNat (true, 0#32, ()) m1 ⟨rfl, Nat.zero_le _, Nat.sub_zero _, s1,
              fun _ => hs1_pos, by rw [hs1_eq], fun _ h => absurd h (Nat.not_lt_zero _), hm1⟩
        · intro Jni hJni; c0_hsteps_nogrp <;> first
            | exact hJni (2#32, ()) m1 ⟨rfl, Or.inl rfl⟩
            | exact hJni (3#32, ()) m1 ⟨rfl, Or.inr rfl⟩
      · intro Jn hJn; c0_hsteps_nogrp
        · exact hJn (2#32, ()) m1 ⟨rfl, Or.inr rfl, fun _ => rfl⟩
        · exact hJn (1#32, ()) m1 ⟨rfl, Or.inl rfl, fun h => by
            dsimp only [kind] at h; exfalso; apply hc
            change BitVec.toNat 6 ≤ (kraw &&& 255#32).toNat; rw [h]; decide⟩

end
end LeanQbe.T.Examples.Arisca.Proof
