/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Driver1
public import LeanQbe.T.Examples.Arisca.Proof.Driver2Base
public import LeanQbe.T.Examples.Arisca.Proof.Parse
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Checker Specs, Arena Collapse & Gate/Cone Loops (`Arisca.Proof.Driver2Loop`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP contracts `arCheckMainSpec` and
`ariscaCheckBytesSpec`, `776`-byte zeroed-workspace conversion (`array_zero776_to_arCtxMem`), full
dynamic+static collapse (`collapse_dyn_and_tables`), and the gate and cone `ar_check_main` loop
phases (`main_gates_loop_wp`, `main_cones_loop_wp`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Header
open LeanQbe.T.Examples.Arisca.Src.Driver

/-! ## 1. Top-Level Specs, Zero State & Bundled Checker State (`@[expose]`) -/

@[expose] public section

/-- WP specification for `arisca_check_aig(cx, art, art_len)` on already-parsed AIG arrays. -/
def ariscaCheckAigSpec : Spec [i64, i64, i64] [.bool] :=
  fun ⟨cx, art, artLen, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (g : Aig) (rhs0 rhs1 olit : List (BitVec 32))
      (artBytes : List UInt8) (R : Mem 64 → Prop),
      0 < s.w.toNat ∧
      s.w.toNat + s.wlen.toNat < 2 ^ 64 ∧
      s.top.toNat = 776 + align8 (4 * g.ands.length) + align8 (4 * g.ands.length) +
        4 * g.outs.length ∧
      s.top.toNat ≤ s.wlen.toNat ∧
      s.rhs0 = s.w + 776#64 ∧
      s.rhs1 = s.w + BitVec.ofNat 64 (776 + align8 (4 * g.ands.length)) ∧
      s.olit = s.w + BitVec.ofNat 64
        (776 + align8 (4 * g.ands.length) + align8 (4 * g.ands.length)) ∧
      AigArraysRep g rhs0 rhs1 olit ∧
      s.M.toNat = g.M ∧ s.I.toNat = g.I ∧
      s.A.toNat = g.ands.length ∧ s.O.toNat = g.outs.length ∧
      s.rs_n = 0#32 ∧ s.rs_ptop = 0#64 ∧ s.rs_cap = 0#32 ∧ s.rs_pcap = 0#64 ∧
      s.ptop = 0#64 ∧ s.tn = 0#32 ∧ s.qn = 0#32 ∧
      s.pc = 0#32 ∧ s.tc = 0#32 ∧ s.cur_nr = 0#32 ∧
      artLen.toNat = artBytes.length ∧
      art.toNat + artBytes.length < 2 ^ 64 ∧
      (arCtxMem cx s ⋆
        arrayPad i32 s.rhs0 rhs0 ⋆
        arrayPad i32 s.rhs1 rhs1 ⋆
        array (t := i32) s.olit olit ⋆
        region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆
        bytes art artBytes ⋆ R) m ∧
      (∀ (ok : Bool) (m' : Mem 64),
        (ok = true → ariscaCircuitProp (BitVec.ofNat 32 (wordAt artBytes 2)) g) →
        (∃ s' : ArCtxState,
          (arCtxMem cx s' ⋆ region (s.w + 776#64) (s.wlen.toNat - 776) ⋆
            bytes art artBytes ⋆ R) m') →
        Q (ok, ⟨⟩) m')

/-- WP specification for `ar_check_main(cx, aig, aig_len, art, art_len)`. -/
def arCheckMainSpec : Spec [i64, i64, i64, i64, i64] [.bool] :=
  fun ⟨cx, aig, aigLen, art, artLen, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (aigBytes artBytes : List UInt8) (R : Mem 64 → Prop),
      0 < s.w.toNat ∧ s.top = 776#64 ∧ 776 ≤ s.wlen.toNat ∧
      s.w.toNat + s.wlen.toNat < 2 ^ 64 ∧
      aigLen.toNat = aigBytes.length ∧
      artLen.toNat = artBytes.length ∧
      art.toNat + artBytes.length < 2 ^ 64 ∧
      s.rs_n = 0#32 ∧ s.rs_ptop = 0#64 ∧ s.rs_cap = 0#32 ∧ s.rs_pcap = 0#64 ∧
      s.ptop = 0#64 ∧ s.tn = 0#32 ∧ s.qn = 0#32 ∧
      s.pc = 0#32 ∧ s.tc = 0#32 ∧ s.cur_nr = 0#32 ∧
      (arCtxMem cx s ⋆ region (s.w + 776#64) (s.wlen.toNat - 776) ⋆
        bytes aig aigBytes ⋆ bytes art artBytes ⋆ R) m ∧
      (∀ (ok : Bool) (m' : Mem 64),
        (ok = true → ∃ g : Aig,
          parseAig (toNatBytes aigBytes) = some g ∧
          ariscaCircuitProp (BitVec.ofNat 32 (wordAt artBytes 2)) g) →
        (∃ s' : ArCtxState,
          (arCtxMem cx s' ⋆ region (s.w + 776#64) (s.wlen.toNat - 776) ⋆
            bytes aig aigBytes ⋆ bytes art artBytes ⋆ R) m') →
        Q (ok, ⟨⟩) m')

/-- WP specification for `arisca_check_bytes(aig_ptr, aig_len, art_ptr, art_len, work_ptr,
work_len)`. -/
def ariscaCheckBytesSpec : Spec [i64, i64, i64, i64, i64, i64] [i64] :=
  fun ⟨aigPtr, aigLen, artPtr, artLen, workPtr, workLen, ⟨⟩⟩ m Q _ =>
    ∃ (aigBytes artBytes : List UInt8) (R : Mem 64 → Prop),
      aigLen.toNat = aigBytes.length ∧
      artLen.toNat = artBytes.length ∧
      (bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆
        region workPtr workLen.toNat ⋆ R) m ∧
      (∀ (ret : BitVec 64) (m' : Mem 64),
        (ret = 20#64 → ∃ g : Aig,
          parseAig (toNatBytes aigBytes) = some g ∧
          ariscaCircuitProp (BitVec.ofNat 32 (wordAt artBytes 2)) g) →
        (bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆
          region workPtr workLen.toNat ⋆ R) m' →
        Q (ret, ⟨⟩) m')

/-- Canonical all-zero `776`-byte `ArCtxState` produced by the `arisca_check_bytes` zeroing loop. -/
def zeroArCtxState : ArCtxState :=
  { w := 0#64, wlen := 0#64, top := 0#64, mlo := 0#64, mhi := 0#64,
    rhs0 := 0#64, rhs1 := 0#64, olit := 0#64, art := 0#64, nw := 0#64, pos := 0#64,
    bind := 0#64, in_net := 0#64, out_ref := 0#64, rule_off := 0#64, rule_n := 0#64,
    partner := 0#64, flipped := 0#64,
    stk_n := 0#64, stk_p := 0#64, memo_n := 0#64, memo_v := 0#64,
    dense := 0#64, gsy := 0#64, gcl := 0#64, gch := 0#64,
    g_lmask := List.replicate 6 0#64, g_tin := List.replicate 3 0#64,
    g_tto := List.replicate 2 0#64,
    rs_m := 0#64, rs_l := 0#64, rs_h := 0#64, rs_pool := 0#64, rs_ptop := 0#64, rs_pcap := 0#64,
    tm := List.replicate 2 0#64, ts := List.replicate 2 0#64, tl := List.replicate 2 0#64,
    th := List.replicate 2 0#64, pool := List.replicate 2 0#64,
    ptop := 0#64, pcap := 0#64, qm := 0#64, qs := 0#64, ql := 0#64, qh := 0#64,
    ix := 0#64, ix2 := 0#64, bx := 0#64, vq_off := 0#64, vq := 0#64, vq_skip := 0#64,
    rm := 0#64, rm2 := 0#64, rl := 0#64, rh := 0#64, rl2 := 0#64, rh2 := 0#64,
    rpool := 0#64, rpcap := 0#64, cur_rm := 0#64, cur_rl := 0#64, cur_rh := 0#64, cur_rp := 0#64,
    n_out := 0#32, M := 0#32, I := 0#32, A := 0#32, O := 0#32, spec := 0#32,
    n_in := 0#32, n_nets := 0#32, n_gates := 0#32, n_cones := 0#32, n_main := 0#32,
    rs_n := 0#32, rs_cap := 0#32, tc := 0#32, tn := 0#32, tcap := 0#32,
    pc := 0#32, qn := 0#32, qcap := 0#32, rcap := 0#32, cur_nr := 0#32,
    g_outs := List.replicate 2 0#32, g_innet := List.replicate 3 0#32,
    g_inneg := List.replicate 3 0#32, g_lnode := List.replicate 6 0#32,
    g_vs := List.replicate 4 0#32, pad_end := 0#32 }

/-- Static AIG/ART/scratch arrays allocated by `ar_parse_aig` + `ar_parse_art_header_and_tables`. -/
structure CmTabArrs where
  rhs0 : List (BitVec 32)
  rhs1 : List (BitVec 32)
  olit : List (BitVec 32)
  bindArr : List (BitVec 32)
  ruleOff : List (BitVec 32)
  ruleN : List (BitVec 32)
  partnerArr : List (BitVec 32)
  flippedArr : List (BitVec 8)
  inNetArr : List (BitVec 32)
  outRefArr : List (BitVec 32)
  stkN : List (BitVec 32)
  stkP : List (BitVec 32)
  memoN : List (BitVec 32)
  memoV : List (BitVec 64)
  dense : List (BitVec 64)
  gsy : List (BitVec 32)
  gcl : List (BitVec 64)
  gch : List (BitVec 64)

/-- Dynamic workspace arrays allocated by `ar_setup_dynamic`. -/
structure CmDynArrs where
  rsM : List (BitVec 32)
  rsL : List (BitVec 64)
  rsH : List (BitVec 64)
  rsPool : List (BitVec 32)
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
  rm : List (BitVec 32)
  rl : List (BitVec 64)
  rh : List (BitVec 64)
  rm2 : List (BitVec 32)
  rl2 : List (BitVec 64)
  rh2 : List (BitVec 64)
  rpool : List (BitVec 32)

/-- Static tables lengths match `(g, s0)`. -/
def CmTabArrs.LenOk (t : CmTabArrs) (g : Aig) (s0 : ArCtxState) : Prop :=
  t.rhs0.length = g.ands.length ∧ t.rhs1.length = g.ands.length ∧ t.olit.length = g.outs.length ∧
  t.bindArr.length = s0.n_nets.toNat ∧ t.ruleOff.length = s0.n_nets.toNat ∧
  t.ruleN.length = s0.n_nets.toNat ∧ t.partnerArr.length = s0.n_nets.toNat ∧
  t.flippedArr.length = s0.n_nets.toNat ∧ t.inNetArr.length = s0.n_in.toNat ∧
  t.outRefArr.length = s0.n_out.toNat ∧
  t.stkN.length = arTTStk ∧ t.stkP.length = arTTStk ∧
  t.memoN.length = arTTMaxAnd ∧ t.memoV.length = arTTMaxAnd ∧
  t.dense.length = 128 ∧ t.gsy.length = 85 ∧ t.gcl.length = 16 ∧ t.gch.length = 16

/-- Dynamic arrays lengths match `(cap, pw = 12 * cap)`. -/
def CmDynArrs.LenOk (d : CmDynArrs) (cap : Nat) : Prop :=
  let pw := 12 * cap
  d.rsM.length = cap ∧ d.rsL.length = cap ∧ d.rsH.length = cap ∧ d.rsPool.length = pw ∧
  d.tm0.length = cap ∧ d.tm1.length = cap ∧
  d.ts0.length = cap ∧ d.tl0.length = cap ∧ d.th0.length = cap ∧
  d.ts1.length = cap ∧ d.tl1.length = cap ∧ d.th1.length = cap ∧
  d.pool0.length = pw ∧ d.pool1.length = pw ∧
  d.qm.length = cap ∧ d.qs.length = cap ∧ d.ql.length = cap ∧ d.qh.length = cap ∧
  d.ix.length = cap ∧ d.ix2.length = cap ∧ d.bx.length = cap ∧
  d.vqOff.length = cap + 1 ∧ d.vq.length = pw ∧ d.vqSkip.length = cap ∧
  d.rm.length = cap ∧ d.rl.length = cap ∧ d.rh.length = cap ∧
  d.rm2.length = cap ∧ d.rl2.length = cap ∧ d.rh2.length = cap ∧ d.rpool.length = pw

/-- Separation predicate for the full arena (`top0..wlen` + static tables + dynamic slabs). -/
def cmArenaMem (s s0 : ArCtxState) (top0 : Nat) (t : CmTabArrs) (d : CmDynArrs) :
    Mem 64 → Prop :=
  aigArraysMem s t.rhs0 t.rhs1 t.olit ⋆
  netTablesMem s t.bindArr t.ruleOff t.ruleN t.partnerArr t.flippedArr t.inNetArr t.outRefArr ⋆
  gateScratchMem s t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
  region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
  rsMem s d.rsM d.rsL d.rsH d.rsPool ⋆
  tMem s d.tm0 d.tm1 d.ts0 d.tl0 d.th0 d.ts1 d.tl1 d.th1 d.pool0 d.pool1 ⋆
  qMem s d.qm d.qs d.ql d.qh d.ix d.ix2 d.bx d.vqOff d.vq d.vqSkip ⋆
  rMem s d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool ⋆
  region (s.w + s.top) (s.wlen.toNat - s.top.toNat)

/-- Static immutable invariants fixed after `ar_setup_dynamic`. -/
structure CmBase (s0 : ArCtxState) (g : Aig) (top0 : Nat)
    (aigBytes artBytes : List UInt8) : Prop where
  w_pos : 0 < s0.w.toNat
  w_fit : s0.w.toNat + s0.wlen.toNat < 2 ^ 64
  top0_ge : 776 ≤ top0
  top0_le_top : top0 ≤ s0.top.toNat
  top_le_wlen : s0.top.toNat ≤ s0.wlen.toNat
  cap_lo : 16 ≤ s0.qcap.toNat
  cap_hi : s0.qcap.toNat ≤ 300000000
  pcap_eq : s0.pcap.toNat = 12 * s0.qcap.toNat
  rs_cap_eq : s0.rs_cap = s0.qcap
  tcap_eq : s0.tcap = s0.qcap
  rcap_eq : s0.rcap = s0.qcap
  rs_pcap_eq : s0.rs_pcap = s0.pcap
  rpcap_eq : s0.rpcap = s0.pcap
  g_M_le : g.M ≤ 0x3FFFFFF0
  s_M : s0.M.toNat = g.M
  s_I : s0.I.toNat = g.I
  s_A : s0.A.toNat = g.ands.length
  s_O : s0.O.toNat = g.outs.length
  art_fit : s0.art.toNat + artBytes.length < 2 ^ 64
  nw4 : 4 * s0.nw.toNat = artBytes.length
  nnets_bd : s0.n_nets.toNat ≤ 0x3FFFFFFF
  spec_bd : s0.spec = 0#32 ∨ s0.spec = 1#32 ∨ s0.spec = 2#32
  spec_word : s0.spec = BitVec.ofNat 32 (wordAt artBytes 2)
  tgeom : TablesGeom s0 g.ands.length g.outs.length
    s0.n_nets.toNat s0.n_in.toNat s0.n_out.toNat top0
  dgeom : DynGeom s0 top0 s0.qcap.toNat
  masks : MasksOk s0.modW s0.mlo s0.mhi

def cmStep64 (e : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  match e with | @Expr.let_ _ _ _ [.bits 64] _ k => k (0#64, ()) | e => e

def cmStep32 (e : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  match e with | @Expr.let_ _ _ _ [.bits 32] _ k => k (0#32, ()) | e => e

def cmStepB (e : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  match e with | @Expr.let_ _ _ _ [.bool] _ k => k (false, ()) | e => e

def cmLoad32 (e : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  match e with | @Expr.load _ _ _ (.bits 32) _ k => k 0#32 | e => e

def cmJnzF (e : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  match e with | .jnz _ _ f => f | e => e

def cmGrpHere (e : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  match e with
  | .group (sig := [[.bits 32]]) b _ => Blocks.get (b ((fun _ _ => False), ())) .here (0#32, ())
  | e => e

def cmAig1 (cx art artLen : Val i64) : Expr Val Cont [.bool] :=
  cmGrpHere (cmStep32 (cmStep32 (cmLoad32 (cmStep64 (cmJnzF (cmStepB (cmStep64 (cmLoad32
    (cmStep64 (cmStep64 (cmStep64 (cmLoad32 (cmStep64 (cmStep64 (cmLoad32 (cmStep64 (cmJnzF
      (cmStepB (cmLoad32 (cmStep64
        (arisca_check_aig_body Val Cont (cx, art, artLen, ()))))))))))))))))))))))

@[irreducible] def cmGatesExpr (cx _aig _aigLen art artLen : Val i64) : Expr Val Cont [.bool] :=
  match cmJnzF (cmStepB (cmLoad32 (cmStep64 (cmGrpHere (cmJnzF (cmStepB (cmLoad32
      (cmStep64 (cmAig1 cx art artLen))))))))) with
  | @Expr.call _ _ _ _ _ [.bool] _ k2 =>
    match k2 (true, ()) with
    | .jnz _ (@Expr.call _ _ _ _ _ [.bool] _ k3) _ =>
      match k3 (true, ()) with
      | .jnz _ e _ => cmStep32 (cmStep32 (cmLoad32 (cmStep64 e)))
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

@[irreducible] def cmConesExpr (cx aig aigLen art artLen : Val i64) : Expr Val Cont [.bool] :=
  match cmGatesExpr cx aig aigLen art artLen with
  | .group (sig := [[.bits 32]]) b _ =>
    cmJnzF (cmStepB (cmLoad32 (cmStep64
      (Blocks.get (b ((fun _ _ => False), ())) .here (0#32, ())))))
  | _ => .ret (Arg.imm false, ())

@[irreducible] def cmSp0Expr (cx aig aigLen art artLen : Val i64) : Expr Val Cont [.bool] :=
  match cmConesExpr cx aig aigLen art artLen with
  | .group (sig := [[.bits 32]]) b _ =>
    cmJnzF (cmStepB (cmLoad32 (cmStep64
      (Blocks.get (b ((fun _ _ => False), ())) .here (0#32, ())))))
  | _ => .ret (Arg.imm false, ())

@[irreducible] def cmMainExpr (cx aig aigLen art artLen : Val i64) : Expr Val Cont [.bool] :=
  match cmSp0Expr cx aig aigLen art artLen with
  | @Expr.call _ _ _ _ _ [.bool] _ k =>
    match k (true, ()) with
    | .jnz _ e _ => e
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

end

/-! ## 2. Zeroed `776 B` Conversion & Arena Collapse -/

public section

private theorem zeroState_u32_blk :
    (zeroArCtxState.u32Blk) = List.replicate 21 0#32 := by
  simp [ArCtxState.u32Blk, zeroArCtxState, List.replicate]

private theorem list_replicate_add {α : Type} (a b : Nat) (x : α) :
    List.replicate (a + b) x = List.replicate a x ++ List.replicate b x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, List.cons_append, ih]

private theorem arCtxMem_zero_split (cx : BitVec 64) :
    (arCtxTree cx zeroArCtxState).eval =
      (array64 cx (List.replicate 77 0#64) ⋆
       array (t := i32) (cx + 616) (List.replicate 40 0#32)) := by
  have hrep64 : List.replicate 77 (0#64 : BitVec 64) =
      List.replicate 26 0#64 ++ List.replicate 6 0#64 ++ List.replicate 3 0#64 ++
      List.replicate 2 0#64 ++ List.replicate 6 0#64 ++ List.replicate 2 0#64 ++
      List.replicate 2 0#64 ++ List.replicate 2 0#64 ++ List.replicate 2 0#64 ++
      List.replicate 2 0#64 ++ List.replicate 24 0#64 := by
    simp only [← list_replicate_add]
  have hrep32 : List.replicate 40 (0#32 : BitVec 32) =
      List.replicate 21 0#32 ++ List.replicate 2 0#32 ++ List.replicate 3 0#32 ++
      List.replicate 3 0#32 ++ List.replicate 6 0#32 ++ List.replicate 4 0#32 ++ [0#32] := by
    have : [0#32] = List.replicate 1 (0#32 : BitVec 32) := rfl
    rw [this]; simp only [← list_replicate_add]
  have hs64 : array64 cx (List.replicate 77 0#64) =
      (array64 cx (List.replicate 26 0#64) ⋆ array64 (cx + 208) (List.replicate 6 0#64) ⋆
       array64 (cx + 256) (List.replicate 3 0#64) ⋆ array64 (cx + 280) (List.replicate 2 0#64) ⋆
       array64 (cx + 296) (List.replicate 6 0#64) ⋆ array64 (cx + 344) (List.replicate 2 0#64) ⋆
       array64 (cx + 360) (List.replicate 2 0#64) ⋆ array64 (cx + 376) (List.replicate 2 0#64) ⋆
       array64 (cx + 392) (List.replicate 2 0#64) ⋆ array64 (cx + 408) (List.replicate 2 0#64) ⋆
       array64 (cx + 424) (List.replicate 24 0#64)) := by
    conv => lhs; rw [hrep64]
    repeat rw [array64_append]
    simp [Nat.reduceAdd, Nat.reduceMul]
  have hs32 : array (t := i32) (cx + 616) (List.replicate 40 0#32) =
      (array (t := i32) (cx + 616) (List.replicate 21 0#32) ⋆
       array (t := i32) (cx + 700) (List.replicate 2 0#32) ⋆
       array (t := i32) (cx + 708) (List.replicate 3 0#32) ⋆
       array (t := i32) (cx + 720) (List.replicate 3 0#32) ⋆
       array (t := i32) (cx + 732) (List.replicate 6 0#32) ⋆
       array (t := i32) (cx + 756) (List.replicate 4 0#32) ⋆
       cell (t := i32) (cx + 772) 0#32) := by
    conv => lhs; rw [hrep32]
    repeat rw [array_append]
    rw [array_cons, array_nil, sep_emp]
    simp [Ty.bytes, Ty.size, ptr_add_ofNat]
  rw [hs64, hs32]
  simp only [arCtxTree, SepTree.eval, zeroArCtxState]
  ac_rfl

private theorem bytesOf_replicate_u8 (n : Nat) :
    bytesOf (t := i8) (List.replicate n (0#8 : Val i8)) = List.replicate n (0 : UInt8) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Int.toBytes 1 ((toBits i8 (0#8 : Val i8)).setWidth 8).toInt ++
      bytesOf (t := i8) (List.replicate n (0#8 : Val i8)) = List.replicate (n + 1) 0
    have h1 : Int.toBytes 1 ((toBits i8 (0#8 : Val i8)).setWidth 8).toInt = [0] := by decide
    rw [ih, h1]; rfl

private theorem bytes64_replicate_zero (n : Nat) :
    bytes64 (List.replicate n (0#64 : BitVec 64)) = List.replicate (8 * n) (0 : UInt8) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Int.toBytes 8 (0#64 : BitVec 64).toInt ++ bytes64 (List.replicate n 0#64) =
      List.replicate (8 * (n + 1)) 0
    rw [ih]
    have h8 : Int.toBytes 8 (0#64 : BitVec 64).toInt = List.replicate 8 (0 : UInt8) := by decide
    rw [h8, ← list_replicate_add, show 8 + 8 * n = 8 * (n + 1) by omega]

private theorem bytesOf_replicate_u32 (n : Nat) :
    bytesOf (t := i32) (List.replicate n (0#32 : Val i32)) =
      List.replicate (4 * n) (0 : UInt8) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Int.toBytes 4 ((toBits i32 (0#32 : Val i32)).setWidth 32).toInt ++
      bytesOf (t := i32) (List.replicate n (0#32 : Val i32)) = List.replicate (4 * (n + 1)) 0
    rw [ih]
    have h4 : Int.toBytes 4 ((toBits i32 (0#32 : Val i32)).setWidth 32).toInt =
        List.replicate 4 (0 : UInt8) := by decide
    rw [h4, ← list_replicate_add, show 4 + 4 * n = 4 * (n + 1) by omega]

theorem array_zero776_to_arCtxMem {cx : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i8) cx (List.replicate 776 (0#8 : BitVec 8)) ⋆ R) m) :
    (arCtxMem cx zeroArCtxState ⋆ R) m := by
  refine sep_mono (fun m0 hm0 => ?_) hm
  have hm_eq := array_eq_bytesOf (t := i8) cx (List.replicate 776 (0#8 : Val i8))
    (by rw [List.length_replicate]; decide) hm0
  rw [bytesOf_replicate_u8, show (776 : Nat) = 8 * 77 + 4 * 40 by decide,
    list_replicate_add, ← bytes64_replicate_zero 77, ← bytesOf_replicate_u32 40] at hm_eq
  have h1 := array64_bytes cx (List.replicate 77 0#64) (by decide)
  have h2 := array_bytes (t := i32) (cx + 616) (List.replicate 40 0#32)
    (by rw [List.length_replicate]; decide)
  have hlen : (bytes64 (List.replicate 77 0#64)).length +
      (bytesOf (t := i32) (List.replicate 40 0#32)).length ≤ 2 ^ 64 := by
    rw [bytes64_length, bytesOf_length, List.length_replicate, List.length_replicate]
    decide
  have hsep := Mem.At_append_sep (bytes64 (List.replicate 77 0#64))
    (bytesOf (t := i32) (List.replicate 40 0#32)) cx hlen
  rw [bytes64_length, List.length_replicate] at hsep
  have hsep0 : (array64 cx (List.replicate 77 0#64) ⋆
      array (t := i32) (cx + 616) (List.replicate 40 0#32)) m0 := by
    have hm_sep : Eq ((bytes64 (List.replicate 77 0#64) ++
        bytesOf (t := i32) (List.replicate 40 0#32)).At cx) m0 := hm_eq.symm
    rw [hsep] at hm_sep
    exact sep_mono2 (fun _ h => h ▸ h1) (fun _ h => h ▸ h2) _ hm_sep
  have hm_tree : (arCtxTree cx zeroArCtxState).eval m0 := by
    rw [arCtxMem_zero_split]; exact hsep0
  exact ⟨⟨by simp [zeroArCtxState], by simp [zeroArCtxState], by simp [zeroArCtxState],
    by simp [zeroArCtxState], by simp [zeroArCtxState], by simp [zeroArCtxState],
    by simp [zeroArCtxState], by simp [zeroArCtxState], by simp [zeroArCtxState],
    by simp [zeroArCtxState], by simp [zeroArCtxState], by simp [zeroArCtxState],
    by simp [zeroArCtxState]⟩, hm_tree⟩

theorem region776_to_array_u8 {a : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region a 776 ⋆ R) m) :
    ∃ xs : List (BitVec 8), xs.length = 776 ∧ (array (t := i8) a xs ⋆ R) m := by
  have hm0 : (region (a + BitVec.ofNat 64 0) 776 ⋆ R) m := by
    simpa only [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using hm
  obtain ⟨xs, hlen, hm1⟩ := region_pop_alloc_u8 776 (by decide) (by decide) hm0
  simp only [align8, Nat.zero_add, Nat.sub_self,
    show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, region_zero, emp_sep, sep_emp] at hm1
  exact ⟨xs, hlen, hm1⟩

theorem collapse_dyn_and_tables {cx aigPtr : BitVec 64} {s s0 : ArCtxState} {top0 : Nat}
    {g : Aig} {aigBytes artBytes : List UInt8} {t : CmTabArrs} {d : CmDynArrs}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hb : CmBase s0 g top0 aigBytes artBytes)
    (htLen : t.LenOk g s0) (hdLen : d.LenOk s0.qcap.toNat)
    (hDyn : DynGeom s top0 s0.qcap.toNat)
    (hs_w : s.w = s0.w) (hs_wlen : s.wlen = s0.wlen)
    (hs_top_le : s.top.toNat ≤ s.wlen.toNat)
    (hs_tgeom : TablesGeom s g.ands.length g.outs.length
      s0.n_nets.toNat s0.n_in.toNat s0.n_out.toNat top0)
    (hm : (arCtxMem cx s ⋆ bytes s0.art artBytes ⋆ cmArenaMem s s0 top0 t d ⋆
      bytes aigPtr aigBytes ⋆ R) m) :
    (arCtxMem cx s ⋆ region (s0.w + 776#64) (s0.wlen.toNat - 776) ⋆
      bytes aigPtr aigBytes ⋆ bytes s0.art artBytes ⋆ R) m := by
  have h1 : (region (s.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
      rsMem s d.rsM d.rsL d.rsH d.rsPool ⋆
      tMem s d.tm0 d.tm1 d.ts0 d.tl0 d.th0 d.ts1 d.tl1 d.th1 d.pool0 d.pool1 ⋆
      qMem s d.qm d.qs d.ql d.qh d.ix d.ix2 d.bx d.vqOff d.vq d.vqSkip ⋆
      rMem s d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool ⋆
      region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆
      (arCtxMem cx s ⋆ aigArraysMem s t.rhs0 t.rhs1 t.olit ⋆
       netTablesMem s t.bindArr t.ruleOff t.ruleN t.partnerArr t.flippedArr t.inNetArr
         t.outRefArr ⋆
       gateScratchMem s t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
       bytes aigPtr aigBytes ⋆ bytes s0.art artBytes ⋆ R)) m := by
    dsimp only [cmArenaMem] at hm; rw [← hs_w] at hm; exact sep_cast hm (by ac_rfl)
  have h2 := dyn_collapse_avail hDyn (le_trans (le_refl top0) (align8_ge top0))
    hs_top_le (by rw [hs_w, hs_wlen]; exact hb.w_fit)
    hdLen.1 hdLen.2.1 hdLen.2.2.1 hdLen.2.2.2.1 hdLen.2.2.2.2.1 hdLen.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.1 hdLen.2.2.2.2.2.2.2.1 hdLen.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.1 hdLen.2.2.2.2.2.2.2.2.2.2.1 hdLen.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.1 hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hdLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h1
  have h3 : (aigArraysMem s t.rhs0 t.rhs1 t.olit ⋆
      netTablesMem s t.bindArr t.ruleOff t.ruleN t.partnerArr t.flippedArr t.inNetArr
        t.outRefArr ⋆
      gateScratchMem s t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
      region (s.w + BitVec.ofNat 64 top0) (s.wlen.toNat - top0) ⋆
      (arCtxMem cx s ⋆ bytes aigPtr aigBytes ⋆ bytes s0.art artBytes ⋆ R)) m :=
    sep_cast h2 (by ac_rfl)
  have h4 := tables_collapse_avail hs_tgeom hb.top0_ge
    (le_trans hb.top0_le_top (hs_wlen ▸ hb.top_le_wlen))
    (by rw [hs_w, hs_wlen]; exact hb.w_fit)
    htLen.1 htLen.2.1 htLen.2.2.1 htLen.2.2.2.1 htLen.2.2.2.2.1 htLen.2.2.2.2.2.1
    htLen.2.2.2.2.2.2.1 htLen.2.2.2.2.2.2.2.1 htLen.2.2.2.2.2.2.2.2.1 htLen.2.2.2.2.2.2.2.2.2.1
    htLen.2.2.2.2.2.2.2.2.2.2.1 htLen.2.2.2.2.2.2.2.2.2.2.2.1 htLen.2.2.2.2.2.2.2.2.2.2.2.2.1
    htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.1 htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h3
  rw [hs_w, hs_wlen] at h4
  exact sep_cast h4 (by ac_rfl)

/-! ## 3. Loop Phases of `ar_check_main` (`gates`, `cones`, `main`) -/

theorem bv32_add1_lt {i n : BitVec 32} (h : i.toNat < n.toNat) :
    (i + 1#32).toNat = i.toNat + 1 := by
  have : i.toNat + 1 < 2 ^ 32 := by have := n.isLt; omega
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt this]

theorem tgeom_rw {s0 s : ArCtxState} {A O nNets nIn nOut top0 : Nat}
    (ht : TablesGeom s0 A O nNets nIn nOut top0)
    (hw : s.w = s0.w) (h1 : s.rhs0 = s0.rhs0) (h2 : s.rhs1 = s0.rhs1) (h3 : s.olit = s0.olit)
    (h4 : s.bind = s0.bind) (h5 : s.rule_off = s0.rule_off) (h6 : s.rule_n = s0.rule_n)
    (h7 : s.partner = s0.partner) (h8 : s.flipped = s0.flipped) (h9 : s.in_net = s0.in_net)
    (h10 : s.out_ref = s0.out_ref) (h11 : s.stk_n = s0.stk_n) (h12 : s.stk_p = s0.stk_p)
    (h13 : s.memo_n = s0.memo_n) (h14 : s.memo_v = s0.memo_v) (h15 : s.dense = s0.dense)
    (h16 : s.gsy = s0.gsy) (h17 : s.gcl = s0.gcl) (h18 : s.gch = s0.gch) :
    TablesGeom s A O nNets nIn nOut top0 :=
  { top_eq := ht.top_eq, rhs0_eq := h1 ▸ hw ▸ ht.rhs0_eq,
    rhs1_eq := h2 ▸ hw ▸ ht.rhs1_eq, olit_eq := h3 ▸ hw ▸ ht.olit_eq,
    bind_eq := h4 ▸ hw ▸ ht.bind_eq, rule_off_eq := h5 ▸ h4 ▸ ht.rule_off_eq,
    rule_n_eq := h6 ▸ h5 ▸ ht.rule_n_eq, partner_eq := h7 ▸ h6 ▸ ht.partner_eq,
    flipped_eq := h8 ▸ h7 ▸ ht.flipped_eq, in_net_eq := h9 ▸ h8 ▸ ht.in_net_eq,
    out_ref_eq := h10 ▸ h9 ▸ ht.out_ref_eq, stk_n_eq := h11 ▸ h10 ▸ ht.stk_n_eq,
    stk_p_eq := h12 ▸ h11 ▸ ht.stk_p_eq, memo_n_eq := h13 ▸ h12 ▸ ht.memo_n_eq,
    memo_v_eq := h14 ▸ h13 ▸ ht.memo_v_eq, dense_eq := h15 ▸ h14 ▸ ht.dense_eq,
    gsy_eq := h16 ▸ h15 ▸ ht.gsy_eq, gcl_eq := h17 ▸ h16 ▸ ht.gcl_eq,
    gch_eq := h18 ▸ h17 ▸ ht.gch_eq }

private theorem arena_unpack_gate {s0 s : ArCtxState} {top0 : Nat} {t : CmTabArrs} {d : CmDynArrs}
    (hs : s = { s0 with
      pos := s.pos, rs_n := s.rs_n, rs_ptop := s.rs_ptop,
      g_lmask := s.g_lmask, g_tin := s.g_tin, g_tto := s.g_tto,
      g_outs := s.g_outs, g_innet := s.g_innet, g_inneg := s.g_inneg,
      g_lnode := s.g_lnode, g_vs := s.g_vs }) :
    cmArenaMem s s0 top0 t d =
      (aigArraysMem s t.rhs0 t.rhs1 t.olit ⋆
       netTablesMem s t.bindArr t.ruleOff t.ruleN t.partnerArr t.flippedArr t.inNetArr
         t.outRefArr ⋆
       gateScratchMem s t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
       rsMem s d.rsM d.rsL d.rsH d.rsPool ⋆
       (region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
        tMem s0 d.tm0 d.tm1 d.ts0 d.tl0 d.th0 d.ts1 d.tl1 d.th1 d.pool0 d.pool1 ⋆
        qMem s0 d.qm d.qs d.ql d.qh d.ix d.ix2 d.bx d.vqOff d.vq d.vqSkip ⋆
        rMem s0 d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool ⋆
        region (s0.w + s0.top) (s0.wlen.toNat - s0.top.toNat))) := by
  dsimp only [cmArenaMem]
  have h1 : tMem s d.tm0 d.tm1 d.ts0 d.tl0 d.th0 d.ts1 d.tl1 d.th1 d.pool0 d.pool1 =
      tMem s0 d.tm0 d.tm1 d.ts0 d.tl0 d.th0 d.ts1 d.tl1 d.th1 d.pool0 d.pool1 := by
    simp only [tMem, show s.tm = s0.tm by rw [hs], show s.ts = s0.ts by rw [hs],
      show s.tl = s0.tl by rw [hs], show s.th = s0.th by rw [hs],
      show s.pool = s0.pool by rw [hs]]
  have h2 : qMem s d.qm d.qs d.ql d.qh d.ix d.ix2 d.bx d.vqOff d.vq d.vqSkip =
      qMem s0 d.qm d.qs d.ql d.qh d.ix d.ix2 d.bx d.vqOff d.vq d.vqSkip := by
    simp only [qMem, show s.qm = s0.qm by rw [hs], show s.qs = s0.qs by rw [hs],
      show s.ql = s0.ql by rw [hs], show s.qh = s0.qh by rw [hs],
      show s.ix = s0.ix by rw [hs], show s.ix2 = s0.ix2 by rw [hs],
      show s.bx = s0.bx by rw [hs], show s.vq_off = s0.vq_off by rw [hs],
      show s.vq = s0.vq by rw [hs], show s.vq_skip = s0.vq_skip by rw [hs]]
  have h3 : rMem s d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool =
      rMem s0 d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool := by
    simp only [rMem, show s.rm = s0.rm by rw [hs], show s.rl = s0.rl by rw [hs],
      show s.rh = s0.rh by rw [hs], show s.rm2 = s0.rm2 by rw [hs],
      show s.rl2 = s0.rl2 by rw [hs], show s.rh2 = s0.rh2 by rw [hs],
      show s.rpool = s0.rpool by rw [hs]]
  rw [h1, h2, h3, show s.w = s0.w by rw [hs], show s.top = s0.top by rw [hs],
    show s.wlen = s0.wlen by rw [hs]]
  ac_rfl

/-- `n_gates` loop of `ar_check_main`. -/
theorem main_gates_loop_wp (Γ : LeanQbe.T.Env)
    (hGate : ∀ xs m Q X, arDoGateSpec xs m Q X → Γ "ar_do_gate" [i64] [.bool] xs m Q X)
    {cx aig aigLen art artLen : Val i64} {Q : Post [.bool]} {X : XPost}
    {s0 : ArCtxState} {g : Aig} {top0 : Nat} {aigBytes artBytes : List UInt8}
    {t0 : CmTabArrs} {d0 : CmDynArrs} {R : Mem 64 → Prop} {m0 : Mem 64}
    (hb : CmBase s0 g top0 aigBytes artBytes)
    (htLen : t0.LenOk g s0) (hdLen : d0.LenOk s0.qcap.toNat)
    (hAig : AigRep g t0.rhs0 t0.rhs1 t0.olit)
    (hBind : BindRep s0 g t0.bindArr t0.inNetArr t0.outRefArr)
    (hpos0 : s0.pos.toNat ≤ s0.nw.toNat)
    (hrsn0 : s0.rs_n.toNat ≤ s0.rs_cap.toNat) (hrspt0 : s0.rs_ptop.toNat ≤ s0.rs_pcap.toNat)
    (hTot0 : monoTotalWords d0.rsPool d0.rsM s0.rs_n.toNat ≤ s0.rs_ptop.toNat)
    (hSy0 : SymsBound d0.rsPool d0.rsM s0.rs_n.toNat s0.n_nets.toNat)
    (hOk0 : ∀ i < s0.rs_n.toNat,
      (d0.rsPool.getD (d0.rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSort0 : RulesSorted d0.rsPool d0.rsM s0.rs_n.toNat)
    (hRep0 : ∀ ρ : Nat → Bool,
      PartnerRep (cSig g ρ t0.bindArr) s0.n_nets.toNat t0.partnerArr ∧
      RulesRep s0.modW (cSig g ρ t0.bindArr) s0 t0.ruleOff t0.ruleN
        d0.rsM d0.rsL d0.rsH d0.rsPool)
    (hm0 : (arCtxMem cx s0 ⋆ bytes s0.art artBytes ⋆ cmArenaMem s0 s0 top0 t0 d0 ⋆
      bytes aig aigBytes ⋆ R) m0)
    (hFail : ∀ (s' : ArCtxState) (m' : Mem 64),
      (arCtxMem cx s' ⋆ region (s0.w + 776#64) (s0.wlen.toNat - 776) ⋆
        bytes aig aigBytes ⋆ bytes s0.art artBytes ⋆ R) m' → Q (false, ⟨⟩) m')
    (hNext : ∀ (s1 : ArCtxState) (t1 : CmTabArrs) (d1 : CmDynArrs) (m1 : Mem 64),
      t1.LenOk g s0 → d1.LenOk s0.qcap.toNat →
      s1 = { s0 with
        pos := s1.pos, rs_n := s1.rs_n, rs_ptop := s1.rs_ptop,
        g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
        g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
        g_lnode := s1.g_lnode, g_vs := s1.g_vs } →
      s1.pos.toNat ≤ s0.nw.toNat →
      s1.rs_n.toNat ≤ s0.rs_cap.toNat → s1.rs_ptop.toNat ≤ s0.rs_pcap.toNat →
      monoTotalWords d1.rsPool d1.rsM s1.rs_n.toNat ≤ s1.rs_ptop.toNat →
      SymsBound d1.rsPool d1.rsM s1.rs_n.toNat s0.n_nets.toNat →
      (∀ i < s1.rs_n.toNat,
        (d1.rsPool.getD (d1.rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      RulesSorted d1.rsPool d1.rsM s1.rs_n.toNat →
      (∀ ρ : Nat → Bool,
        PartnerRep (cSig g ρ t0.bindArr) s0.n_nets.toNat t1.partnerArr ∧
        RulesRep s0.modW (cSig g ρ t0.bindArr) s1 t1.ruleOff t1.ruleN
          d1.rsM d1.rsL d1.rsH d1.rsPool) →
      t1.rhs0 = t0.rhs0 → t1.rhs1 = t0.rhs1 → t1.olit = t0.olit →
      t1.bindArr = t0.bindArr → t1.flippedArr = t0.flippedArr →
      t1.inNetArr = t0.inNetArr → t1.outRefArr = t0.outRefArr →
      d1.tm0 = d0.tm0 → d1.tm1 = d0.tm1 →
      d1.ts0 = d0.ts0 → d1.tl0 = d0.tl0 → d1.th0 = d0.th0 →
      d1.ts1 = d0.ts1 → d1.tl1 = d0.tl1 → d1.th1 = d0.th1 →
      d1.pool0 = d0.pool0 → d1.pool1 = d0.pool1 →
      d1.qm = d0.qm → d1.qs = d0.qs → d1.ql = d0.ql → d1.qh = d0.qh →
      d1.ix = d0.ix → d1.ix2 = d0.ix2 → d1.bx = d0.bx →
      d1.vqOff = d0.vqOff → d1.vq = d0.vq → d1.vqSkip = d0.vqSkip →
      d1.rm = d0.rm → d1.rl = d0.rl → d1.rh = d0.rh →
      d1.rm2 = d0.rm2 → d1.rl2 = d0.rl2 → d1.rh2 = d0.rh2 → d1.rpool = d0.rpool →
      (arCtxMem cx s1 ⋆ bytes s0.art artBytes ⋆ cmArenaMem s1 s0 top0 t1 d1 ⋆
        bytes aig aigBytes ⋆ R) m1 →
      wp Γ Q X (cmConesExpr cx aig aigLen art artLen) m1) :
    wp Γ Q X (cmGatesExpr cx aig aigLen art artLen) m0 := by
  unfold cmGatesExpr
  have hrcap30 : s0.rs_cap.toNat < 2 ^ 30 := by
    rw [hb.rs_cap_eq]; have := hb.cap_hi; omega
  have hrpcap32 : s0.rs_pcap.toNat < 2 ^ 32 := by
    rw [hb.rs_pcap_eq, hb.pcap_eq]; have := hb.cap_hi; omega
  refine wp_loop_group (fun (rem : Nat) (args : Tup Val [i32]) (mL : Mem 64) =>
      let ⟨i, ⟨⟩⟩ := args
      i.toNat ≤ s0.n_gates.toNat ∧ rem = s0.n_gates.toNat - i.toNat ∧
      ∃ (sL : ArCtxState)
        (ro rn pa sn sp mn : List (BitVec 32)) (mv dn : List (BitVec 64))
        (gy : List (BitVec 32)) (gl gh : List (BitVec 64))
        (rm : List (BitVec 32)) (rl rh : List (BitVec 64)) (rp : List (BitVec 32)),
        let tL : CmTabArrs := { t0 with
          ruleOff := ro, ruleN := rn, partnerArr := pa, stkN := sn, stkP := sp,
          memoN := mn, memoV := mv, dense := dn, gsy := gy, gcl := gl, gch := gh }
        let dL : CmDynArrs := { d0 with rsM := rm, rsL := rl, rsH := rh, rsPool := rp }
        ro.length = t0.ruleOff.length ∧ rn.length = t0.ruleN.length ∧
        pa.length = t0.partnerArr.length ∧ sn.length = t0.stkN.length ∧
        sp.length = t0.stkP.length ∧ mn.length = t0.memoN.length ∧
        mv.length = t0.memoV.length ∧ dn.length = t0.dense.length ∧
        gy.length = t0.gsy.length ∧ gl.length = t0.gcl.length ∧ gh.length = t0.gch.length ∧
        rm.length = d0.rsM.length ∧ rl.length = d0.rsL.length ∧
        rh.length = d0.rsH.length ∧ rp.length = d0.rsPool.length ∧
        sL = { s0 with
          pos := sL.pos, rs_n := sL.rs_n, rs_ptop := sL.rs_ptop,
          g_lmask := sL.g_lmask, g_tin := sL.g_tin, g_tto := sL.g_tto,
          g_outs := sL.g_outs, g_innet := sL.g_innet, g_inneg := sL.g_inneg,
          g_lnode := sL.g_lnode, g_vs := sL.g_vs } ∧
        sL.pos.toNat ≤ s0.nw.toNat ∧
        sL.rs_n.toNat ≤ s0.rs_cap.toNat ∧ sL.rs_ptop.toNat ≤ s0.rs_pcap.toNat ∧
        monoTotalWords rp rm sL.rs_n.toNat ≤ sL.rs_ptop.toNat ∧
        SymsBound rp rm sL.rs_n.toNat s0.n_nets.toNat ∧
        (∀ j < sL.rs_n.toNat,
          (rp.getD (rm.getD j 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        RulesSorted rp rm sL.rs_n.toNat ∧
        (∀ ρ : Nat → Bool,
          PartnerRep (cSig g ρ t0.bindArr) s0.n_nets.toNat pa ∧
          RulesRep s0.modW (cSig g ρ t0.bindArr) sL ro rn rm rl rh rp) ∧
        (arCtxMem cx sL ⋆ bytes s0.art artBytes ⋆ cmArenaMem sL s0 top0 tL dL ⋆
          bytes aig aigBytes ⋆ R) mL) ?_ ?_
  · intro J rem ⟨i, ⟨⟩⟩ mL hrec ⟨hi_le, _, sL, ro, rn, pa, sn, sp, mn, mv, dn, gy, gl, gh,
      rm, rl, rh, rp, lro, lrn, lpa, lsn, lsp, lmn, lmv, ldn, lgy, lgl, lgh,
      lrm, lrl, lrh, lrp, hsL, hposL, hrsnL, hrsptL, hTotL, hSyL, hOkL, hSortL, hRepL, hmL⟩
    have hng_eq : sL.n_gates = s0.n_gates := by rw [hsL]
    c0_hsteps_nogrp
    · have hi_lt : i.toNat < s0.n_gates.toNat := by rw [← hng_eq]; exact hc
      have hip1 := bv32_add1_lt hi_lt
      let Rgate : Mem 64 → Prop :=
        region (s0.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
        tMem s0 d0.tm0 d0.tm1 d0.ts0 d0.tl0 d0.th0 d0.ts1 d0.tl1 d0.th1 d0.pool0 d0.pool1 ⋆
        qMem s0 d0.qm d0.qs d0.ql d0.qh d0.ix d0.ix2 d0.bx d0.vqOff d0.vq d0.vqSkip ⋆
        rMem s0 d0.rm d0.rl d0.rh d0.rm2 d0.rl2 d0.rh2 d0.rpool ⋆
        region (s0.w + s0.top) (s0.wlen.toNat - s0.top.toNat) ⋆ bytes aig aigBytes ⋆ R
      have hm_g : (arCtxMem cx sL ⋆ bytes sL.art artBytes ⋆
          aigArraysMem sL t0.rhs0 t0.rhs1 t0.olit ⋆
          netTablesMem sL t0.bindArr ro rn pa t0.flippedArr t0.inNetArr t0.outRefArr ⋆
          gateScratchMem sL sn sp mn mv dn gy gl gh ⋆ rsMem sL rm rl rh rp ⋆ Rgate) mL := by
        rw [arena_unpack_gate hsL] at hmL
        rw [show sL.art = s0.art by rw [hsL]]
        exact sep_cast hmL (by dsimp only [Rgate]; ac_rfl)
      have hBindL : BindRep sL g t0.bindArr t0.inNetArr t0.outRefArr :=
        { nets_le := by rw [show sL.n_nets = s0.n_nets by rw [hsL]]; exact hBind.nets_le,
          bind_len := by rw [show sL.n_nets = s0.n_nets by rw [hsL]]; exact hBind.bind_len,
          bind_bound := by rw [show sL.n_nets = s0.n_nets by rw [hsL]]; exact hBind.bind_bound,
          spec_bd := by rw [show sL.spec = s0.spec by rw [hsL]]; exact hBind.spec_bd,
          in_len := by rw [show sL.n_in = s0.n_in by rw [hsL]]; exact hBind.in_len,
          in_eq := by rw [show sL.n_in = s0.n_in by rw [hsL]]; exact hBind.in_eq,
          i_even := by rw [show sL.spec = s0.spec by rw [hsL]]; exact hBind.i_even,
          in_ok := by
            intro j hj; rw [show sL.n_in = s0.n_in by rw [hsL]] at hj
            rw [show sL.n_nets = s0.n_nets by rw [hsL], show sL.spec = s0.spec by rw [hsL]]
            exact hBind.in_ok j hj,
          out_len := by rw [show sL.n_out = s0.n_out by rw [hsL]]; exact hBind.out_len,
          out_eq := by rw [show sL.n_out = s0.n_out by rw [hsL]]; exact hBind.out_eq,
          out_even := by rw [show sL.spec = s0.spec by rw [hsL]]; exact hBind.out_even,
          out_bounds := by
            rw [show sL.modW = s0.modW by rw [hsL]; rfl]; exact hBind.out_bounds,
          out_ok := by
            intro j hj; rw [show sL.n_out = s0.n_out by rw [hsL]] at hj
            rw [show sL.n_nets = s0.n_nets by rw [hsL], show sL.spec = s0.spec by rw [hsL]]
            exact hBind.out_ok j hj }
      dsimp only [Arg.val]
      apply wp_call_of_spec
      refine hGate _ _ _ _ ⟨sL, g, artBytes, t0.rhs0, t0.rhs1, t0.olit, t0.bindArr,
        ro, rn, pa, t0.flippedArr, t0.inNetArr, t0.outRefArr,
        sn, sp, mn, mv, dn, gy, gl, gh, rm, rl, rh, rp, Rgate,
        by rw [show sL.I = s0.I by rw [hsL]]; exact hb.s_I,
        by rw [show sL.M = s0.M by rw [hsL]]; exact hb.s_M, hb.g_M_le,
        by rw [show sL.n_nets = s0.n_nets by rw [hsL]]; exact hb.nnets_bd,
        by rw [show sL.rs_cap = s0.rs_cap by rw [hsL]]; exact hrcap30,
        by rw [show sL.rs_pcap = s0.rs_pcap by rw [hsL]]; exact hrpcap32,
        by rw [show sL.art = s0.art by rw [hsL]]; exact hb.art_fit,
        by rw [show sL.nw = s0.nw by rw [hsL], hb.nw4]; exact Nat.le_refl _,
        by rw [lsn, htLen.2.2.2.2.2.2.2.2.2.2.1]; decide,
        by rw [lsp, htLen.2.2.2.2.2.2.2.2.2.2.2.1]; decide,
        by rw [lmn, htLen.2.2.2.2.2.2.2.2.2.2.2.2.1]; decide,
        by rw [lmv, htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; decide,
        by rw [ldn, htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; decide,
        by rw [lgy, htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; decide,
        by rw [lgl, htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; decide,
        by rw [lgh, htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]; decide,
        by rw [show sL.modW = s0.modW by rw [hsL]; rfl, show sL.mlo = s0.mlo by rw [hsL],
             show sL.mhi = s0.mhi by rw [hsL]]; exact hb.masks,
        hAig, hBindL, hTotL, hOkL, hSortL,
        fun ρ => by
          rw [show sL.n_nets = s0.n_nets by rw [hsL], show sL.modW = s0.modW by rw [hsL]; rfl]
          exact hRepL ρ,
        hm_g,
        fun ok s' ro' rn' pa' sn' sp' mn' mv' dn' gy' gl' gh' rm' rl' rh' rp' m'
          hrsn' hrspt' hpos' hs' lro' lrn' lpa' lsn' lsp' lmn' lmv' ldn' lgy' lgl' lgh'
          lrm' lrl' lrh' lrp' hok' hm' => ?_⟩
      have hs'_s0 : s' = { s0 with
          pos := s'.pos, rs_n := s'.rs_n, rs_ptop := s'.rs_ptop,
          g_lmask := s'.g_lmask, g_tin := s'.g_tin, g_tto := s'.g_tto,
          g_outs := s'.g_outs, g_innet := s'.g_innet, g_inneg := s'.g_inneg,
          g_lnode := s'.g_lnode, g_vs := s'.g_vs } := by rw [hs', hsL]
      let t' : CmTabArrs := { t0 with
        ruleOff := ro', ruleN := rn', partnerArr := pa', stkN := sn', stkP := sp',
        memoN := mn', memoV := mv', dense := dn', gsy := gy', gcl := gl', gch := gh' }
      let d' : CmDynArrs := { d0 with rsM := rm', rsL := rl', rsH := rh', rsPool := rp' }
      have hdLen' : d'.LenOk s0.qcap.toNat :=
        ⟨lrm'.trans lrm ▸ hdLen.1, lrl'.trans lrl ▸ hdLen.2.1, lrh'.trans lrh ▸ hdLen.2.2.1,
         lrp'.trans lrp ▸ hdLen.2.2.2.1, hdLen.2.2.2.2⟩
      have hm'_arena : (arCtxMem cx s' ⋆ bytes s0.art artBytes ⋆
          cmArenaMem s' s0 top0 t' d' ⋆ bytes aig aigBytes ⋆ R) m' := by
        rw [arena_unpack_gate hs'_s0]
        rw [show s'.art = s0.art by rw [hs'_s0]] at hm'
        exact sep_cast hm' (by dsimp only [Rgate]; ac_rfl)
      cases ok
      · refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
        c0_hstraight
        have htLen' : t'.LenOk g s0 :=
          ⟨htLen.1, htLen.2.1, htLen.2.2.1, htLen.2.2.2.1, lro'.trans lro ▸ htLen.2.2.2.2.1,
           lrn'.trans lrn ▸ htLen.2.2.2.2.2.1, lpa'.trans lpa ▸ htLen.2.2.2.2.2.2.1,
           htLen.2.2.2.2.2.2.2.1, htLen.2.2.2.2.2.2.2.2.1, htLen.2.2.2.2.2.2.2.2.2.1,
           lsn'.trans lsn ▸ htLen.2.2.2.2.2.2.2.2.2.2.1,
           lsp'.trans lsp ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.1,
           lmn'.trans lmn ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.2.1,
           lmv'.trans lmv ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
           ldn'.trans ldn ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
           lgy'.trans lgy ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
           lgl'.trans lgl ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
           lgh'.trans lgh ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
        have hdGeom' : DynGeom s' top0 s0.qcap.toNat :=
          DynGeom.preserve hb.dgeom (by rw [hs'_s0]) (by rw [hs'_s0])
            (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0])
            (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0])
            (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0])
            (by rw [hs'_s0]) (Or.inl ⟨by rw [hs'_s0], by rw [hs'_s0]⟩)
            (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0])
            (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0])
            (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0])
        have htGeom' := tgeom_rw (s := s') hb.tgeom (by rw [hs'_s0]) (by rw [hs'_s0])
          (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0])
          (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0])
          (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0]) (by rw [hs'_s0])
          (by rw [hs'_s0]) (by rw [hs'_s0])
        exact hFail s' m' (collapse_dyn_and_tables hb htLen' hdLen' hdGeom'
          (by rw [hs'_s0]) (by rw [hs'_s0])
          (by rw [show s'.top = s0.top by rw [hs'_s0], show s'.wlen = s0.wlen by rw [hs'_s0]]
              exact hb.top_le_wlen)
          htGeom' hm'_arena)
      · refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
        c0_hstraight
        obtain ⟨hTot', hSy', hOk', hSort', hRep'⟩ := hok' rfl
        have hpos'_s0 : s'.pos.toNat ≤ s0.nw.toNat := by
          rw [show sL.nw = s0.nw by rw [hsL]] at hpos'; exact hpos' hposL
        refine hrec (s0.n_gates.toNat - (i + 1#32).toNat) (i + 1#32, ⟨⟩) m' (by omega)
          ⟨by omega, by rw [hip1], s', ro', rn', pa', sn', sp', mn', mv', dn', gy', gl', gh',
            rm', rl', rh', rp', lro'.trans lro, lrn'.trans lrn, lpa'.trans lpa,
            lsn'.trans lsn, lsp'.trans lsp, lmn'.trans lmn, lmv'.trans lmv, ldn'.trans ldn,
            lgy'.trans lgy, lgl'.trans lgl, lgh'.trans lgh, lrm'.trans lrm, lrl'.trans lrl,
            lrh'.trans lrh, lrp'.trans lrp, hs'_s0, hpos'_s0,
            by rw [show s0.rs_cap = sL.rs_cap by rw [hsL]]; exact hrsn',
            by rw [show s0.rs_pcap = sL.rs_pcap by rw [hsL]]; exact hrspt', hTot',
            by rw [show sL.n_nets = s0.n_nets by rw [hsL]] at hSy'; exact hSy' hSyL,
            hOk', hSort', fun ρ => by
              rw [show sL.n_nets = s0.n_nets by rw [hsL],
                  show s'.modW = s0.modW by rw [hs'_s0]; rfl] at hRep'
              exact hRep' ρ,
            hm'_arena⟩
    · have htLenL : ({ t0 with
          ruleOff := ro, ruleN := rn, partnerArr := pa, stkN := sn, stkP := sp,
          memoN := mn, memoV := mv, dense := dn, gsy := gy, gcl := gl, gch := gh } :
          CmTabArrs).LenOk g s0 :=
        ⟨htLen.1, htLen.2.1, htLen.2.2.1, htLen.2.2.2.1, lro ▸ htLen.2.2.2.2.1,
         lrn ▸ htLen.2.2.2.2.2.1, lpa ▸ htLen.2.2.2.2.2.2.1, htLen.2.2.2.2.2.2.2.1,
         htLen.2.2.2.2.2.2.2.2.1, htLen.2.2.2.2.2.2.2.2.2.1,
         lsn ▸ htLen.2.2.2.2.2.2.2.2.2.2.1, lsp ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.1,
         lmn ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.2.1, lmv ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         ldn ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, lgy ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         lgl ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         lgh ▸ htLen.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
      have hdLenL : ({ d0 with rsM := rm, rsL := rl, rsH := rh, rsPool := rp } :
          CmDynArrs).LenOk s0.qcap.toNat :=
        ⟨lrm ▸ hdLen.1, lrl ▸ hdLen.2.1, lrh ▸ hdLen.2.2.1, lrp ▸ hdLen.2.2.2.1, hdLen.2.2.2.2⟩
      have hExitG := hNext sL _ _ mL htLenL hdLenL hsL hposL hrsnL hrsptL hTotL hSyL hOkL hSortL
        hRepL rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hmL
      unfold cmConesExpr cmGatesExpr at hExitG
      exact hExitG
  · intro J hJ; c0_hsteps
    exact hJ s0.n_gates.toNat (0#32, ⟨⟩) m0 ⟨Nat.zero_le _, Nat.sub_zero _, s0,
      t0.ruleOff, t0.ruleN, t0.partnerArr, t0.stkN, t0.stkP, t0.memoN, t0.memoV, t0.dense,
      t0.gsy, t0.gcl, t0.gch, d0.rsM, d0.rsL, d0.rsH, d0.rsPool,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, hpos0, hrsn0, hrspt0, hTot0, hSy0, hOk0, hSort0, hRep0, hm0⟩

private theorem arena_unpack_cone {s0 s1 s : ArCtxState} {top0 : Nat}
    {t : CmTabArrs} {d : CmDynArrs}
    (hs1 : s1 = { s0 with
      pos := s1.pos, rs_n := s1.rs_n, rs_ptop := s1.rs_ptop,
      g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
      g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
      g_lnode := s1.g_lnode, g_vs := s1.g_vs })
    (hs : s = { s1 with
      pos := s.pos, rs_n := s.rs_n, rs_ptop := s.rs_ptop,
      tc := s.tc, tn := s.tn, pc := s.pc, ptop := s.ptop, qn := s.qn,
      ix := s.ix, ix2 := s.ix2, cur_rm := s.cur_rm, cur_rl := s.cur_rl,
      cur_rh := s.cur_rh, cur_rp := s.cur_rp, cur_nr := s.cur_nr }) :
    cmArenaMem s s0 top0 t d =
      (array (t := i32) s.rule_off t.ruleOff ⋆ array (t := i32) s.rule_n t.ruleN ⋆
       array (t := i32) s.partner t.partnerArr ⋆ rsMem s d.rsM d.rsL d.rsH d.rsPool ⋆
       tMem s d.tm0 d.tm1 d.ts0 d.tl0 d.th0 d.ts1 d.tl1 d.th1 d.pool0 d.pool1 ⋆
       qMem s d.qm d.qs d.ql d.qh d.ix d.ix2 d.bx d.vqOff d.vq d.vqSkip ⋆
       (aigArraysMem s1 t.rhs0 t.rhs1 t.olit ⋆
        arrayPad i32 s1.bind t.bindArr ⋆ u32PadTail s1.rule_off t.ruleOff.length ⋆
        u32PadTail s1.rule_n t.ruleN.length ⋆ u32PadTail s1.partner t.partnerArr.length ⋆
        arrayPad i8 s1.flipped t.flippedArr ⋆ arrayPad i32 s1.in_net t.inNetArr ⋆
        arrayPad i32 s1.out_ref t.outRefArr ⋆
        gateScratchMem s1 t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch ⋆
        region (s1.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
        rMem s1 d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool ⋆
        region (s1.w + s1.top) (s1.wlen.toNat - s1.top.toNat))) := by
  dsimp only [cmArenaMem]
  have h1 : aigArraysMem s t.rhs0 t.rhs1 t.olit = aigArraysMem s1 t.rhs0 t.rhs1 t.olit := by
    simp only [aigArraysMem, show s.rhs0 = s1.rhs0 by rw [hs],
      show s.rhs1 = s1.rhs1 by rw [hs], show s.olit = s1.olit by rw [hs]]
  have h2 : gateScratchMem s t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch =
      gateScratchMem s1 t.stkN t.stkP t.memoN t.memoV t.dense t.gsy t.gcl t.gch := by
    simp only [gateScratchMem, show s.stk_n = s1.stk_n by rw [hs],
      show s.stk_p = s1.stk_p by rw [hs], show s.memo_n = s1.memo_n by rw [hs],
      show s.memo_v = s1.memo_v by rw [hs], show s.dense = s1.dense by rw [hs],
      show s.gsy = s1.gsy by rw [hs], show s.gcl = s1.gcl by rw [hs],
      show s.gch = s1.gch by rw [hs]]
  have h3 : rMem s d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool =
      rMem s1 d.rm d.rl d.rh d.rm2 d.rl2 d.rh2 d.rpool := by
    simp only [rMem, show s.rm = s1.rm by rw [hs], show s.rl = s1.rl by rw [hs],
      show s.rh = s1.rh by rw [hs], show s.rm2 = s1.rm2 by rw [hs],
      show s.rl2 = s1.rl2 by rw [hs], show s.rh2 = s1.rh2 by rw [hs],
      show s.rpool = s1.rpool by rw [hs]]
  rw [h1, h2, h3, netTablesMem_unpack]
  simp only [arrayPad_u32_unfold,
    show s.bind = s1.bind by rw [hs], show s.rule_off = s1.rule_off by rw [hs],
    show s.rule_n = s1.rule_n by rw [hs], show s.partner = s1.partner by rw [hs],
    show s.flipped = s1.flipped by rw [hs], show s.in_net = s1.in_net by rw [hs],
    show s.out_ref = s1.out_ref by rw [hs], show s.w = s1.w by rw [hs],
    show s.top = s1.top by rw [hs], show s.wlen = s1.wlen by rw [hs],
    show s0.w = s1.w by rw [hs1]]
  ac_rfl

/-- `n_cones` loop of `ar_check_main`. -/
theorem main_cones_loop_wp (Γ : LeanQbe.T.Env)
    (hCone : ∀ xs m Q X, arDoConeSpec xs m Q X → Γ "ar_do_cone" [i64] [.bool] xs m Q X)
    {cx aig aigLen art artLen : Val i64} {Q : Post [.bool]} {X : XPost}
    {s0 s1 : ArCtxState} {g : Aig} {top0 : Nat} {aigBytes artBytes : List UInt8}
    {t1 : CmTabArrs} {d1 : CmDynArrs} {R : Mem 64 → Prop} {m1 : Mem 64}
    (hb : CmBase s0 g top0 aigBytes artBytes)
    (htLen : t1.LenOk g s0) (hdLen : d1.LenOk s0.qcap.toNat)
    (hs1 : s1 = { s0 with
      pos := s1.pos, rs_n := s1.rs_n, rs_ptop := s1.rs_ptop,
      g_lmask := s1.g_lmask, g_tin := s1.g_tin, g_tto := s1.g_tto,
      g_outs := s1.g_outs, g_innet := s1.g_innet, g_inneg := s1.g_inneg,
      g_lnode := s1.g_lnode, g_vs := s1.g_vs })
    (hpc1 : s1.pc.toNat < 2) (htc1 : s1.tc.toNat < 2)
    (hpos1 : s1.pos.toNat ≤ s0.nw.toNat)
    (hrsn1 : s1.rs_n.toNat ≤ s0.rs_cap.toNat) (hrspt1 : s1.rs_ptop.toNat ≤ s0.rs_pcap.toNat)
    (hTot1 : monoTotalWords d1.rsPool d1.rsM s1.rs_n.toNat ≤ s1.rs_ptop.toNat)
    (hSy1 : SymsBound d1.rsPool d1.rsM s1.rs_n.toNat s0.n_nets.toNat)
    (hOk1 : ∀ i < s1.rs_n.toNat,
      (d1.rsPool.getD (d1.rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSort1 : RulesSorted d1.rsPool d1.rsM s1.rs_n.toNat)
    (hRep1 : ∀ ρ : Nat → Bool,
      PartnerRep (cSig g ρ t1.bindArr) s0.n_nets.toNat t1.partnerArr ∧
      RulesRep s0.modW (cSig g ρ t1.bindArr) s1 t1.ruleOff t1.ruleN
        d1.rsM d1.rsL d1.rsH d1.rsPool)
    (hm1 : (arCtxMem cx s1 ⋆ bytes s0.art artBytes ⋆ cmArenaMem s1 s0 top0 t1 d1 ⋆
      bytes aig aigBytes ⋆ R) m1)
    (hFail : ∀ (s' : ArCtxState) (m' : Mem 64),
      (arCtxMem cx s' ⋆ region (s0.w + 776#64) (s0.wlen.toNat - 776) ⋆
        bytes aig aigBytes ⋆ bytes s0.art artBytes ⋆ R) m' → Q (false, ⟨⟩) m')
    (hNext : ∀ (s2 : ArCtxState) (t2 : CmTabArrs) (d2 : CmDynArrs) (m2 : Mem 64),
      t2.LenOk g s0 → d2.LenOk s0.qcap.toNat →
      s2 = { s1 with
        pos := s2.pos, rs_n := s2.rs_n, rs_ptop := s2.rs_ptop,
        tc := s2.tc, tn := s2.tn, pc := s2.pc, ptop := s2.ptop, qn := s2.qn,
        ix := s2.ix, ix2 := s2.ix2, cur_rm := s2.cur_rm, cur_rl := s2.cur_rl,
        cur_rh := s2.cur_rh, cur_rp := s2.cur_rp, cur_nr := s2.cur_nr } →
      (s2.ix = s0.ix ∧ s2.ix2 = s0.ix2) ∨ (s2.ix = s0.ix2 ∧ s2.ix2 = s0.ix) →
      s2.pc.toNat < 2 → s2.tc.toNat < 2 → s2.pos.toNat ≤ s0.nw.toNat →
      s2.rs_n.toNat ≤ s0.rs_cap.toNat → s2.rs_ptop.toNat ≤ s0.rs_pcap.toNat →
      monoTotalWords d2.rsPool d2.rsM s2.rs_n.toNat ≤ s2.rs_ptop.toNat →
      SymsBound d2.rsPool d2.rsM s2.rs_n.toNat s0.n_nets.toNat →
      (∀ i < s2.rs_n.toNat,
        (d2.rsPool.getD (d2.rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      RulesSorted d2.rsPool d2.rsM s2.rs_n.toNat →
      (∀ ρ : Nat → Bool,
        PartnerRep (cSig g ρ t1.bindArr) s0.n_nets.toNat t2.partnerArr ∧
        RulesRep s0.modW (cSig g ρ t1.bindArr) s2 t2.ruleOff t2.ruleN
          d2.rsM d2.rsL d2.rsH d2.rsPool) →
      t2.rhs0 = t1.rhs0 → t2.rhs1 = t1.rhs1 → t2.olit = t1.olit →
      t2.bindArr = t1.bindArr → t2.partnerArr = t1.partnerArr →
      t2.flippedArr = t1.flippedArr → t2.inNetArr = t1.inNetArr → t2.outRefArr = t1.outRefArr →
      d2.rm = d1.rm → d2.rl = d1.rl → d2.rh = d1.rh →
      d2.rm2 = d1.rm2 → d2.rl2 = d1.rl2 → d2.rh2 = d1.rh2 → d2.rpool = d1.rpool →
      (arCtxMem cx s2 ⋆ bytes s0.art artBytes ⋆ cmArenaMem s2 s0 top0 t2 d2 ⋆
        bytes aig aigBytes ⋆ R) m2 →
      wp Γ Q X (cmSp0Expr cx aig aigLen art artLen) m2) :
    wp Γ Q X (cmConesExpr cx aig aigLen art artLen) m1 := by
  unfold cmConesExpr cmGatesExpr
  have htcap30 : s0.tcap.toNat < 2 ^ 30 := by
    rw [hb.tcap_eq]; have := hb.cap_hi; omega
  have hqcap32 : s0.qcap.toNat + 16 < 2 ^ 32 := by have := hb.cap_hi; omega
  have hpcap32 : s0.pcap.toNat < 2 ^ 32 := by
    rw [hb.pcap_eq]; have := hb.cap_hi; omega
  have hrcap30 : s0.rs_cap.toNat < 2 ^ 30 := by
    rw [hb.rs_cap_eq]; have := hb.cap_hi; omega
  have hrpcap32 : s0.rs_pcap.toNat < 2 ^ 32 := by
    rw [hb.rs_pcap_eq, hb.pcap_eq]; have := hb.cap_hi; omega
  have hrpcap4g : s0.rs_pcap.toNat ≤ 4000000000 := by
    rw [hb.rs_pcap_eq, hb.pcap_eq]; have := hb.cap_hi; omega
  have h2nn32 : 2 * s0.n_nets.toNat < 2 ^ 32 := by have := hb.nnets_bd; omega
  have hw_s1 : s1.w = s0.w := by rw [hs1]
  have hwl_s1 : s1.wlen = s0.wlen := by rw [hs1]
  have htop_s1 : s1.top = s0.top := by rw [hs1]
  refine wp_loop_group (fun (rem : Nat) (args : Tup Val [i32]) (mL : Mem 64) =>
      let ⟨i, ⟨⟩⟩ := args
      i.toNat ≤ s0.n_cones.toNat ∧ rem = s0.n_cones.toNat - i.toNat ∧
      ∃ (sL : ArCtxState) (ro rn : List (BitVec 32)) (dL : CmDynArrs),
        let tL : CmTabArrs := { t1 with ruleOff := ro, ruleN := rn }
        ro.length = t1.ruleOff.length ∧ rn.length = t1.ruleN.length ∧ dL.LenOk s0.qcap.toNat ∧
        dL.rm = d1.rm ∧ dL.rl = d1.rl ∧ dL.rh = d1.rh ∧
        dL.rm2 = d1.rm2 ∧ dL.rl2 = d1.rl2 ∧ dL.rh2 = d1.rh2 ∧ dL.rpool = d1.rpool ∧
        sL = { s1 with
          pos := sL.pos, rs_n := sL.rs_n, rs_ptop := sL.rs_ptop,
          tc := sL.tc, tn := sL.tn, pc := sL.pc, ptop := sL.ptop, qn := sL.qn,
          ix := sL.ix, ix2 := sL.ix2, cur_rm := sL.cur_rm, cur_rl := sL.cur_rl,
          cur_rh := sL.cur_rh, cur_rp := sL.cur_rp, cur_nr := sL.cur_nr } ∧
        ((sL.ix = s0.ix ∧ sL.ix2 = s0.ix2) ∨ (sL.ix = s0.ix2 ∧ sL.ix2 = s0.ix)) ∧
        sL.pc.toNat < 2 ∧ sL.tc.toNat < 2 ∧ sL.pos.toNat ≤ s0.nw.toNat ∧
        sL.rs_n.toNat ≤ s0.rs_cap.toNat ∧ sL.rs_ptop.toNat ≤ s0.rs_pcap.toNat ∧
        monoTotalWords dL.rsPool dL.rsM sL.rs_n.toNat ≤ sL.rs_ptop.toNat ∧
        SymsBound dL.rsPool dL.rsM sL.rs_n.toNat s0.n_nets.toNat ∧
        (∀ j < sL.rs_n.toNat,
          (dL.rsPool.getD (dL.rsM.getD j 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        RulesSorted dL.rsPool dL.rsM sL.rs_n.toNat ∧
        (∀ ρ : Nat → Bool,
          RulesRep s0.modW (cSig g ρ t1.bindArr) sL ro rn
            dL.rsM dL.rsL dL.rsH dL.rsPool) ∧
        (arCtxMem cx sL ⋆ bytes s0.art artBytes ⋆ cmArenaMem sL s0 top0 tL dL ⋆
          bytes aig aigBytes ⋆ R) mL) ?_ ?_
  · intro J rem ⟨i, ⟨⟩⟩ mL hrec ⟨hi_le, _, sL, ro, rn, dL, lro, lrn, hdL,
      hrm, hrl, hrh, hrm2, hrl2, hrh2, hrp, hsL, hixSw, hpcL, htcL, hposL,
      hrsnL, hrsptL, hTotL, hSyL, hOkL, hSortL, hRepL, hmL⟩
    have hnc_eq : sL.n_cones = s0.n_cones := by rw [hsL, hs1]
    c0_hsteps_nogrp
    · have hi_lt : i.toNat < s0.n_cones.toNat := by rw [← hnc_eq]; exact hc
      have hip1 := bv32_add1_lt hi_lt
      let Rcone : Mem 64 → Prop :=
        aigArraysMem s1 t1.rhs0 t1.rhs1 t1.olit ⋆ arrayPad i32 s1.bind t1.bindArr ⋆
        u32PadTail s1.rule_off ro.length ⋆ u32PadTail s1.rule_n rn.length ⋆
        u32PadTail s1.partner t1.partnerArr.length ⋆ arrayPad i8 s1.flipped t1.flippedArr ⋆
        arrayPad i32 s1.in_net t1.inNetArr ⋆ arrayPad i32 s1.out_ref t1.outRefArr ⋆
        gateScratchMem s1 t1.stkN t1.stkP t1.memoN t1.memoV t1.dense t1.gsy t1.gcl t1.gch ⋆
        region (s1.w + BitVec.ofNat 64 top0) (align8 top0 - top0) ⋆
        rMem s1 d1.rm d1.rl d1.rh d1.rm2 d1.rl2 d1.rh2 d1.rpool ⋆
        region (s1.w + s1.top) (s1.wlen.toNat - s1.top.toNat) ⋆ bytes aig aigBytes ⋆ R
      have hm_c : (arCtxMem cx sL ⋆ bytes sL.art artBytes ⋆
          array (t := i32) sL.rule_off ro ⋆ array (t := i32) sL.rule_n rn ⋆
          array (t := i32) sL.partner t1.partnerArr ⋆ rsMem sL dL.rsM dL.rsL dL.rsH dL.rsPool ⋆
          tMem sL dL.tm0 dL.tm1 dL.ts0 dL.tl0 dL.th0 dL.ts1 dL.tl1 dL.th1 dL.pool0 dL.pool1 ⋆
          qMem sL dL.qm dL.qs dL.ql dL.qh dL.ix dL.ix2 dL.bx dL.vqOff dL.vq dL.vqSkip ⋆
          Rcone) mL := by
        rw [arena_unpack_cone hs1 hsL, hrm, hrl, hrh, hrm2, hrl2, hrh2, hrp] at hmL
        rw [show sL.art = s0.art by rw [hsL, hs1]]
        exact sep_cast hmL (by dsimp only [Rcone]; ac_rfl)
      dsimp only [Arg.val]
      apply wp_call_of_spec
      refine hCone _ _ _ _ ⟨sL, artBytes, ro, rn, t1.partnerArr,
        dL.rsM, dL.rsL, dL.rsH, dL.rsPool, dL.tm0, dL.tm1, dL.ts0, dL.tl0, dL.th0,
        dL.ts1, dL.tl1, dL.th1, dL.pool0, dL.pool1, dL.qm, dL.qs, dL.ql, dL.qh,
        dL.ix, dL.ix2, dL.bx, dL.vqOff, dL.vq, dL.vqSkip,
        fun σ => ∃ ρ : Nat → Bool, σ = cSig g ρ t1.bindArr, Rcone,
        hpcL, htcL,
        by rw [show sL.tcap = s0.tcap by rw [hsL, hs1]]; exact htcap30,
        by rw [show sL.qcap = s0.qcap by rw [hsL, hs1]]; exact hb.cap_lo,
        by rw [show sL.qcap = s0.qcap by rw [hsL, hs1]]; exact hqcap32,
        by rw [show sL.pcap = s0.pcap by rw [hsL, hs1]]; exact hpcap32,
        by rw [show sL.rs_cap = s0.rs_cap by rw [hsL, hs1]]; exact hrcap30,
        by rw [show sL.rs_pcap = s0.rs_pcap by rw [hsL, hs1]]; exact hrpcap32,
        by rw [show sL.rs_pcap = s0.rs_pcap by rw [hsL, hs1]]; exact hrpcap4g,
        by rw [show sL.n_nets = s0.n_nets by rw [hsL, hs1]]; exact hb.nnets_bd,
        by rw [show sL.n_nets = s0.n_nets by rw [hsL, hs1]]; exact h2nn32,
        by rw [show sL.art = s0.art by rw [hsL, hs1]]; exact hb.art_fit,
        by rw [show sL.nw = s0.nw by rw [hsL, hs1], hb.nw4]; exact Nat.le_refl _,
        by rw [show sL.tcap = s0.tcap by rw [hsL, hs1], hb.tcap_eq]
           exact Nat.le_of_eq hdL.2.2.2.2.1.symm,
        by rw [show sL.tcap = s0.tcap by rw [hsL, hs1], hb.tcap_eq]
           exact Nat.le_of_eq hdL.2.2.2.2.2.1.symm,
        by rw [show sL.tcap = s0.tcap by rw [hsL, hs1], hb.tcap_eq]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.1.symm,
        by rw [show sL.tcap = s0.tcap by rw [hsL, hs1], hb.tcap_eq]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.tcap = s0.tcap by rw [hsL, hs1], hb.tcap_eq]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.tcap = s0.tcap by rw [hsL, hs1], hb.tcap_eq]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.tcap = s0.tcap by rw [hsL, hs1], hb.tcap_eq]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.tcap = s0.tcap by rw [hsL, hs1], hb.tcap_eq]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.pcap = s0.pcap by rw [hsL, hs1], hb.pcap_eq]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.pcap = s0.pcap by rw [hsL, hs1], hb.pcap_eq]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.qcap = s0.qcap by rw [hsL, hs1]]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.qcap = s0.qcap by rw [hsL, hs1]]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.qcap = s0.qcap by rw [hsL, hs1]]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.qcap = s0.qcap by rw [hsL, hs1]]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.qcap = s0.qcap by rw [hsL, hs1]]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.qcap = s0.qcap by rw [hsL, hs1]]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
               hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1],
        by rw [show sL.tcap = s0.tcap by rw [hsL, hs1], hb.tcap_eq]
           have := hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega,
        by rw [show sL.qcap = s0.qcap by rw [hsL, hs1]]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.qcap = s0.qcap by rw [hsL, hs1]]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.pcap = s0.pcap by rw [hsL, hs1], hb.pcap_eq]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.qcap = s0.qcap by rw [hsL, hs1]]
           exact Nat.le_of_eq hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
        by rw [show sL.modW = s0.modW by rw [hsL, hs1]; rfl, show sL.mlo = s0.mlo by rw [hsL, hs1],
             show sL.mhi = s0.mhi by rw [hsL, hs1]]; exact hb.masks,
        hTotL, hOkL, hSortL, ⟨cSig g (fun _ => false) t1.bindArr, fun _ => false, rfl⟩,
        fun σ ⟨ρ, hρ⟩ => by
          subst hρ
          rw [show sL.n_nets = s0.n_nets by rw [hsL, hs1],
              show sL.modW = s0.modW by rw [hsL, hs1]; rfl]
          exact ⟨(hRep1 ρ).1, hRepL ρ⟩,
        hm_c,
        fun ok s' ro' rn' rm' rl' rh' rp' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1'
          pool0' pool1' qm' qs' ql' qh' ix' ix2' bx' vqOff' vq' vqSkip' m'
          hpc' htc' hrsn' hrspt' hpos' hs' lro' lrn' lrm' lrl' lrh' lrp'
          ltm0' ltm1' lts0' ltl0' lth0' lts1' ltl1' lth1' lp0' lp1'
          lqm' lqs' lql' lqh' lix' lix2' hix_sw' lbx' lvqo' lvq' lvqs' hok' hm' => ?_⟩
      have hs'_s1 : s' = { s1 with
          pos := s'.pos, rs_n := s'.rs_n, rs_ptop := s'.rs_ptop,
          tc := s'.tc, tn := s'.tn, pc := s'.pc, ptop := s'.ptop, qn := s'.qn,
          ix := s'.ix, ix2 := s'.ix2, cur_rm := s'.cur_rm, cur_rl := s'.cur_rl,
          cur_rh := s'.cur_rh, cur_rp := s'.cur_rp, cur_nr := s'.cur_nr } := by
        rw [hs', hsL]
      have hix_sw0 : (s'.ix = s0.ix ∧ s'.ix2 = s0.ix2) ∨
          (s'.ix = s0.ix2 ∧ s'.ix2 = s0.ix) := by
        rcases hixSw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hix_sw' with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inl ⟨h3.trans h1, h4.trans h2⟩
        · exact Or.inr ⟨h3.trans h2, h4.trans h1⟩
        · exact Or.inr ⟨h3.trans h1, h4.trans h2⟩
        · exact Or.inl ⟨h3.trans h2, h4.trans h1⟩
      let t' : CmTabArrs := { t1 with ruleOff := ro', ruleN := rn' }
      let d' : CmDynArrs := { d1 with
        rsM := rm', rsL := rl', rsH := rh', rsPool := rp',
        tm0 := tm0', tm1 := tm1', ts0 := ts0', tl0 := tl0', th0 := th0',
        ts1 := ts1', tl1 := tl1', th1 := th1', pool0 := pool0', pool1 := pool1',
        qm := qm', qs := qs', ql := ql', qh := qh', ix := ix', ix2 := ix2',
        bx := bx', vqOff := vqOff', vq := vq', vqSkip := vqSkip' }
      have hdLen' : d'.LenOk s0.qcap.toNat :=
        ⟨lrm'.trans hdL.1, lrl'.trans hdL.2.1, lrh'.trans hdL.2.2.1, lrp'.trans hdL.2.2.2.1,
         ltm0'.trans hdL.2.2.2.2.1, ltm1'.trans hdL.2.2.2.2.2.1, lts0'.trans hdL.2.2.2.2.2.2.1,
         ltl0'.trans hdL.2.2.2.2.2.2.2.1, lth0'.trans hdL.2.2.2.2.2.2.2.2.1,
         lts1'.trans hdL.2.2.2.2.2.2.2.2.2.1, ltl1'.trans hdL.2.2.2.2.2.2.2.2.2.2.1,
         lth1'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.1, lp0'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.1,
         lp1'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.1, lqm'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         lqs'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         lql'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         lqh'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         lix'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         lix2'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         lbx'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         lvqo'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         lvq'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         lvqs'.trans hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         hrm ▸ hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         hrl ▸ hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         hrh ▸ hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         hrm2 ▸ hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         hrl2 ▸ hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         hrh2 ▸ hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         hrp ▸ hdL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
      have hm'_arena : (arCtxMem cx s' ⋆ bytes s0.art artBytes ⋆
          cmArenaMem s' s0 top0 t' d' ⋆ bytes aig aigBytes ⋆ R) m' := by
        rw [arena_unpack_cone hs1 hs'_s1, lro', lrn']
        rw [show s'.art = s0.art by rw [hs'_s1, hs1]] at hm'
        exact sep_cast hm' (by dsimp only [Rcone]; ac_rfl)
      cases ok
      · refine head_wp_jnz rfl (fun h => by cases h) (fun _ => ?_)
        c0_hstraight
        have htLen' : t'.LenOk g s0 :=
          ⟨htLen.1, htLen.2.1, htLen.2.2.1, htLen.2.2.2.1, lro'.trans lro ▸ htLen.2.2.2.2.1,
           lrn'.trans lrn ▸ htLen.2.2.2.2.2.1, htLen.2.2.2.2.2.2⟩
        have hdGeom' : DynGeom s' top0 s0.qcap.toNat :=
          DynGeom.preserve hb.dgeom (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
            (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
            (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
            (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
            (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
            (by rw [hs'_s1, hs1]) hix_sw0 (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
            (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
            (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
            (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
        have htGeom' := tgeom_rw (s := s') hb.tgeom (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
          (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
          (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
          (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
          (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
          (by rw [hs'_s1, hs1])
        exact hFail s' m' (collapse_dyn_and_tables hb htLen' hdLen' hdGeom'
          (by rw [hs'_s1, hs1]) (by rw [hs'_s1, hs1])
          (by rw [show s'.top = s0.top by rw [hs'_s1, hs1],
                  show s'.wlen = s0.wlen by rw [hs'_s1, hs1]]; exact hb.top_le_wlen)
          htGeom' hm'_arena)
      · refine head_wp_jnz rfl (fun _ => ?_) (fun h => by cases h)
        c0_hstraight
        obtain ⟨hTot', hSy', hOk', hSort', hRep'⟩ := hok' rfl
        have hpos'_s0 : s'.pos.toNat ≤ s0.nw.toNat := by
          rw [show sL.nw = s0.nw by rw [hsL, hs1]] at hpos'; exact hpos' hposL
        refine hrec (s0.n_cones.toNat - (i + 1#32).toNat) (i + 1#32, ⟨⟩) m' (by omega)
          ⟨by omega, by rw [hip1], s', ro', rn', d', lro'.trans lro, lrn'.trans lrn, hdLen',
            rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs'_s1, hix_sw0, hpc', htc', hpos'_s0,
            by rw [show s0.rs_cap = sL.rs_cap by rw [hsL, hs1]]; exact hrsn',
            by rw [show s0.rs_pcap = sL.rs_pcap by rw [hsL, hs1]]; exact hrspt', hTot',
            by rw [show sL.n_nets = s0.n_nets by rw [hsL, hs1]] at hSy'; exact hSy' hSyL,
            hOk', hSort', fun ρ => by
              rw [show s0.modW = s'.modW by rw [hs'_s1, hs1]; rfl]
              exact hRep' (cSig g ρ t1.bindArr) ⟨ρ, rfl⟩,
            hm'_arena⟩
    · have htLenL : ({ t1 with ruleOff := ro, ruleN := rn } : CmTabArrs).LenOk g s0 :=
        ⟨htLen.1, htLen.2.1, htLen.2.2.1, htLen.2.2.2.1, lro ▸ htLen.2.2.2.2.1,
         lrn ▸ htLen.2.2.2.2.2.1, htLen.2.2.2.2.2.2⟩
      have hExitC := hNext sL _ dL mL htLenL hdL hsL hixSw hpcL htcL hposL hrsnL hrsptL hTotL hSyL
        hOkL hSortL (fun ρ => ⟨(hRep1 ρ).1, hRepL ρ⟩)
        rfl rfl rfl rfl rfl rfl rfl rfl hrm hrl hrh hrm2 hrl2 hrh2 hrp hmL
      unfold cmSp0Expr cmConesExpr cmGatesExpr at hExitC
      exact hExitC
  · intro J hJ; c0_hsteps
    exact hJ s0.n_cones.toNat (0#32, ⟨⟩) m1 ⟨Nat.zero_le _, Nat.sub_zero _, s1,
      t1.ruleOff, t1.ruleN, d1, rfl, rfl, hdLen, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, Or.inl ⟨by rw [hs1], by rw [hs1]⟩, hpc1, htc1, hpos1, hrsn1, hrspt1,
      hTot1, hSy1, hOk1, hSort1, fun ρ => (hRep1 ρ).2, hm1⟩


end

end LeanQbe.T.Examples.Arisca.Proof
