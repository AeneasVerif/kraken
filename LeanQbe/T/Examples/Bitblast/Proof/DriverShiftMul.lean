/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Proof.DriverParsed
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Shift / Rotate / Multiply / CLZ Evaluator Dispatcher WP Proof (`Bitblast.Proof.DriverShiftMul`)

Proves `Γ`-parametric `Func.wp` soundness for `bv_eval_ops_shift_mul` (`BV_OP_ROTL`, `BV_OP_ROTR`,
`BV_OP_ASHRC`, `BV_OP_REVERSE`, `BV_OP_CLZ`, `BV_OP_REPLICATE`, `BV_OP_SHL`, `BV_OP_USHR`,
`BV_OP_ASHR`, `BV_OP_MUL`) against `bvEvalSubSpec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Src.Driver
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg

@[local c0_load] private theorem dsm_load_prog_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 16) = some s.prog_ptr := load_hdr_prog_ptr hm

@[local c0_load] private theorem dsm_load_slice_off_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 48) = some s.slice_off_ptr := load_hdr_slice_off_ptr hm

@[local c0_load] private theorem dsm_load_n_vars {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 80) = some s.n_vars := load_hdr_n_vars hm

@[local c0_load] private theorem dsm_load_n_cwords {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 88) = some s.n_cwords := load_hdr_n_cwords hm

@[local c0_load] private theorem dsm_load_oom {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 120) = some s.oom := load_hdr_oom hm

/-! ## 1. Pure Reindexing & Semantic Closing Helpers -/

private theorem dsm_getLsbD_rotl {w : Nat} (v : BitVec w) (n j : Nat) (hj : j < w) :
    (v.rotateLeft n).getLsbD j =
      v.getLsbD (if j < n % w then w - n % w + j else j - n % w) := by
  rw [BitVec.getLsbD_rotateLeft]; split <;> simp [hj]

private theorem dsm_getLsbD_rotr {w : Nat} (v : BitVec w) (n j : Nat) (hj : j < w) :
    (v.rotateRight n).getLsbD j =
      v.getLsbD (if j < w - n % w then n % w + j else j - (w - n % w)) := by
  rw [BitVec.getLsbD_rotateRight]; split <;> simp [hj]

private theorem dsm_getLsbD_ashrc {w : Nat} (v : BitVec w) (n j : Nat) (hj : j < w) :
    (v.sshiftRight n).getLsbD j =
      v.getLsbD (if n + j < w then n + j else w - 1) := by
  rw [BitVec.getLsbD_sshiftRight]
  simp only [show ¬(w ≤ j) by omega, decide_false, Bool.not_false, Bool.true_and]
  split <;> simp [BitVec.msb_eq_getLsbD_last]

private theorem dsm_getLsbD_reverse {w : Nat} (v : BitVec w) (j : Nat) (hj : j < w) :
    v.reverse.getLsbD j = v.getLsbD (w - 1 - j) := by
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD]; simp [hj]

private theorem dsm_getLsbD_replicate {aw n : Nat} (v : BitVec aw) (j : Nat) (hj : j < aw * n) :
    (v.replicate n).getLsbD j = v.getLsbD (j % aw) := by
  rw [BitVec.getLsbD_replicate]; simp [hj]

private theorem bv_clz_cast {w1 w2 : Nat} (h : w1 = w2) (v : BitVec w1) :
    (BitVec.cast h v).clz = BitVec.cast h v.clz := by
  subst h; rfl

private theorem bv_shl_cast {w1 w2 n1 n2 : Nat} (hw : w1 = w2) (hn : n1 = n2)
    (v : BitVec w1) (s : BitVec n1) :
    BitVec.shiftLeft (BitVec.cast hw v) (BitVec.cast hn s).toNat =
      BitVec.cast hw (BitVec.shiftLeft v s.toNat) := by
  subst hw hn; rfl

private theorem bv_ushr_cast {w1 w2 n1 n2 : Nat} (hw : w1 = w2) (hn : n1 = n2)
    (v : BitVec w1) (s : BitVec n1) :
    BitVec.ushiftRight (BitVec.cast hw v) (BitVec.cast hn s).toNat =
      BitVec.cast hw (BitVec.ushiftRight v s.toNat) := by
  subst hw hn; rfl

private theorem bv_ashr_cast {w1 w2 n1 n2 : Nat} (hw : w1 = w2) (hn : n1 = n2)
    (v : BitVec w1) (s : BitVec n1) :
    BitVec.sshiftRight' (BitVec.cast hw v) (BitVec.cast hn s) =
      BitVec.cast hw (BitVec.sshiftRight' v s) := by
  subst hw hn; rfl

private theorem bv_mul_cast {w1 w2 : Nat} (hw : w1 = w2) (a b : BitVec w1) :
    BitVec.cast hw a * BitVec.cast hw b = BitVec.cast hw (a * b) := by
  subst hw; rfl

private theorem dsm_pure_ok_post {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g : Aig}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp lp1 : List (BitVec 32)}
    {nodeIdx res : BitVec 32} {w : Nat} {e : BVExpr w} {R : Mem 64 → Prop} {m' : Mem 64}
    {Q : Post [.bool]} {idxFn : Nat → Nat}
    (hoom0 : hdr.oom = 0#32) (hoom1 : hdr1.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hw_lt : w < 4294967296) (hok : BVWorkspaceOk cfg hdr ab so aw ht lp)
    (hfr1 : hdr.OpsFrame hdr1) (haig_len1 : hdr1.aig_len = hdr.aig_len)
    (hlp1 : lp1.length = lp.length)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hroom : w ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat)
    (hret : res = hdr.lits_len) (hlen1 : hdr1.lits_len = hdr.lits_len + BitVec.ofNat 32 w)
    (hagree : ∀ p < hdr.lits_len.toNat, lp1.getD p 0#32 = lp.getD p 0#32)
    (hbits : ∀ j < w, lp1.getD (res.toNat + j) 0#32 = lp.getD (idxFn j) 0#32)
    (hbd : ∀ j < w, (lp.getD (idxFn j) 0#32 >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hnd : nodes.get? nodeIdx.toNat = some (.bv w e))
    (hev : ∀ assign : BVExpr.Assignment, ∀ j < w,
      g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec (lp.getD (idxFn j) 0#32)) =
        (e.eval assign).getLsbD j)
    (hm_so : (array (t := i32) hdr.slice_off_ptr (so.set (BitVec.setWidth 64 nodeIdx).toNat res) ⋆
      blastSoRest cfg hdr1 progPtr progBytes ab aw ht lp1 R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  have haig1 := aigInv_of_smOpsFrame hinv.aig_inv hfr1 haig_len1
  have hok1 := bvWorkspaceOk_of_smOpsFrame hok hfr1 haig1 hlp1
  have hlc_eq := bvWorkspaceOk_litsCap_eq hok; have hlen_le := hinv.lits_le_cap
  have hl1_nat : hdr1.lits_len.toNat = hdr.lits_len.toNat + w := by
    have := hok.lcap_lt
    rw [hlen1, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt,
      Nat.mod_eq_of_lt (by omega)]
  refine drv_sub_bv_ok hoom0 hoom1 hni_lt hok hok1 haig1 (Aig.extends_rfl g) hinv
    (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
    (by omega) (by omega) hagree hnd (by rw [hret]; omega)
    (fun j hj => by rw [hbits j hj]; exact hbd j hj) (fun assign => ?_) hm_so hQ
  have hle_lp : res.toNat + w ≤ lp1.length := by rw [hok1.lits_len, hret]; omega
  rw [sliceDenotes_iff hle_lp]
  intro j hj; rw [hbits j hj]; exact hev assign j hj

private theorem dsm_aig_ok_post {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g g1 : Aig}
    {ab so : List (BitVec 32)} {aw aw1 : List (BitVec 64)} {ht ht1 lp lp1 : List (BitVec 32)}
    {nodeIdx res : BitVec 32} {w : Nat} {e : BVExpr w} {R : Mem 64 → Prop} {m' : Mem 64}
    {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hoom1 : hdr1.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hw_lt : w < 4294967296) (hok : BVWorkspaceOk cfg hdr ab so aw ht lp)
    (hok1 : BVWorkspaceOk cfg hdr1 ab so aw1 ht1 lp1)
    (haig1 : AigInv hdr1 g1 aw1 ht1) (hfr1 : hdr.OpsFrame hdr1) (hext1 : g ≤ g1)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hlits_le : hdr.lits_len.toNat ≤ hdr1.lits_len.toNat)
    (hlcap1 : hdr1.lits_len.toNat ≤ hdr1.lits_cap.toNat)
    (hret : res = hdr.lits_len) (hlen1 : hdr1.lits_len = hdr.lits_len + BitVec.ofNat 32 w)
    (hagree : ∀ p < hdr.lits_len.toNat, lp1.getD p 0#32 = lp.getD p 0#32)
    (hwf1 : SliceLitsWf g1 lp1 res.toNat (BitVec.ofNat 32 w).toNat)
    (hnd : nodes.get? nodeIdx.toNat = some (.bv w e))
    (hsd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g1 (atomAssign progBytes assign)
        (litsSlice lp1 res.toNat (BitVec.ofNat 32 w).toNat)
        (BitVec.cast (m := (BitVec.ofNat 32 w).toNat)
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]) (e.eval assign)))
    (hm_so : (array (t := i32) hdr.slice_off_ptr (so.set (BitVec.setWidth 64 nodeIdx).toNat res) ⋆
      blastSoRest cfg hdr1 progPtr progBytes ab aw1 ht1 lp1 R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  have hw32 : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
  have hlc_eq := bvWorkspaceOk_litsCap_eq hok1
  have hl1_nat : hdr1.lits_len.toNat = hdr.lits_len.toNat + w := by
    have hmod : hdr1.lits_len.toNat = (hdr.lits_len.toNat + w) % 2 ^ 32 := by
      rw [hlen1, BitVec.toNat_add, hw32]
    by_cases hlt : hdr.lits_len.toNat + w < 2 ^ 32
    · rw [hmod, Nat.mod_eq_of_lt hlt]
    · have := hdr.lits_len.isLt
      have hlt2 : hdr.lits_len.toNat + w - 2 ^ 32 < 2 ^ 32 := by omega
      have hsum : hdr.lits_len.toNat + w = (hdr.lits_len.toNat + w - 2 ^ 32) + 2 ^ 32 := by omega
      have hwrap : (hdr.lits_len.toNat + w) % 2 ^ 32 = hdr.lits_len.toNat + w - 2 ^ 32 := by
        conv => lhs; rw [hsum]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
      rw [hwrap] at hmod; omega
  refine drv_sub_bv_ok hoom0 hoom1 hni_lt hok hok1 haig1 hext1 hinv
    (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
    hlits_le (by omega) hagree hnd (by rw [hret]; omega)
    (fun j hj => hwf1 j (by omega)) (fun assign => ?_) hm_so hQ
  have h := hsd assign
  have hle_lp : res.toNat + w ≤ lp1.length := by rw [hok1.lits_len, hret]; omega
  rw [sliceDenotes_iff hle_lp]; rw [sliceDenotes_iff (by omega)] at h
  intro j hj; have h1 := h j (by omega); simpa [BitVec.getLsbD_cast] using h1

private theorem dsm_pure_oom {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g : Aig}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp lp1 : List (BitVec 32)}
    {nodeIdx : BitVec 32} {R : Mem 64 → Prop} {m1 : Mem 64} {Q : Post [.bool]}
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) (hfr1 : hdr.OpsFrame hdr1)
    (hal1 : hdr1.aig_len = hdr.aig_len) (hlp1 : lp1.length = lp.length)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hm1 : (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 ab so aw ht lp1 ⋆ R) m1)
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (false, ⟨⟩) m1 := by
  have haig1 := aigInv_of_smOpsFrame hinv.aig_inv hfr1 hal1
  have hok1 := bvWorkspaceOk_of_smOpsFrame hok hfr1 haig1 hlp1
  exact hQ false hdr1 g so aw ht lp1 m1 hok1 haig1 (Aig.extends_rfl g)
    (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
    (fun hf => absurd hf Bool.false_ne_true) hm1

private theorem dsm_aig_oom {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g g1 : Aig}
    {ab so : List (BitVec 32)} {aw aw1 : List (BitVec 64)} {ht ht1 lp lp1 : List (BitVec 32)}
    {nodeIdx : BitVec 32} {R : Mem 64 → Prop} {m1 : Mem 64} {Q : Post [.bool]}
    (hok1 : BVWorkspaceOk cfg hdr1 ab so aw1 ht1 lp1) (haig1 : AigInv hdr1 g1 aw1 ht1)
    (hfr1 : hdr.OpsFrame hdr1) (hext1 : g ≤ g1)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hm1 : (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 ab so aw1 ht1 lp1 ⋆ R) m1)
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (false, ⟨⟩) m1 :=
  hQ false hdr1 g1 so aw1 ht1 lp1 m1 hok1 haig1 hext1
    (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
    (fun hf => absurd hf Bool.false_ne_true) hm1

private theorem dsm_pure_unop_idx {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g : Aig}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp lp1 : List (BitVec 32)}
    {nodeIdx res : BitVec 32} {w : Nat} {e : BVExpr w} {R : Mem 64 → Prop} {m' : Mem 64}
    {Q : Post [.bool]} {idxFn : Nat → Nat} {ok : Bool}
    (hoom0 : hdr.oom = 0#32) (hoom1 : hdr1.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hw_lt : w < 4294967296) (hok : BVWorkspaceOk cfg hdr ab so aw ht lp)
    (hfr1 : hdr.OpsFrame hdr1) (hal1 : hdr1.aig_len = hdr.aig_len) (hlp1 : lp1.length = lp.length)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hgood : ok = true → hdr1.oom = 0#32 ∧ res = hdr.lits_len ∧
      hdr1.lits_len = hdr.lits_len + BitVec.ofNat 32 w ∧
      ∀ j < (BitVec.ofNat 32 w).toNat, lp1.getD (res.toNat + j) 0#32 = lp.getD (idxFn j) 0#32)
    (hbad : ok = false → hdr1.oom = 1#32 ∧ hdr1.lits_len = hdr.lits_len ∧
      res = 0xFFFFFFFF#32 ∧ lp1 = lp)
    (hok_room : ok = true → w ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat)
    (hagree : ∀ p < hdr.lits_len.toNat, lp1.getD p 0#32 = lp.getD p 0#32)
    (hbd : ∀ j < w, (lp.getD (idxFn j) 0#32 >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hnd : nodes.get? nodeIdx.toNat = some (.bv w e))
    (hev : ∀ assign : BVExpr.Assignment, ∀ j < w,
      g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec (lp.getD (idxFn j) 0#32)) =
        (e.eval assign).getLsbD j)
    (hm_so : (array (t := i32) hdr.slice_off_ptr (so.set (BitVec.setWidth 64 nodeIdx).toNat res) ⋆
      blastSoRest cfg hdr1 progPtr progBytes ab aw ht lp1 R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  have hok_t : ok = true := by
    cases hc : ok
    · have := (hbad hc).1; rw [hoom1] at this; cases this
    · rfl
  obtain ⟨_, hret, hlen1, hbits⟩ := hgood hok_t
  have hw32 : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
  exact dsm_pure_ok_post hoom0 hoom1 hni_lt hw_lt hok hfr1 hal1 hlp1 hinv (hok_room hok_t)
    hret hlen1 hagree (fun j hj => hbits j (by omega)) hbd hnd hev hm_so hQ

private theorem dsm_shift_mul_sd {g g1 : Aig} {progBytes : List UInt8}
    {lp lp1 : List (BitVec 32)} {aOff bOff res : BitVec 32} {w nw : Nat}
    {ea : BVExpr w} {eb : BVExpr nw} {e : BVExpr w}
    {sem : BitVec (BitVec.ofNat 32 w).toNat → BitVec (BitVec.ofNat 32 nw).toNat →
      BitVec (BitVec.ofNat 32 w).toNat}
    (hw_lt : w < 4294967296) (hnw_lt : nw < 4294967296)
    (ha_sd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g (atomAssign progBytes assign) (litsSlice lp aOff.toNat w) (ea.eval assign))
    (hb_sd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g (atomAssign progBytes assign) (litsSlice lp bOff.toNat nw) (eb.eval assign))
    (hsem : ∀ (ρ : Nat → Bool) (va : BitVec (BitVec.ofNat 32 w).toNat)
      (vb : BitVec (BitVec.ofNat 32 nw).toNat),
      SliceDenotes g ρ (litsSlice lp aOff.toNat (BitVec.ofNat 32 w).toNat) va →
      SliceDenotes g ρ (litsSlice lp bOff.toNat (BitVec.ofNat 32 nw).toNat) vb →
      SliceDenotes g1 ρ (litsSlice lp1 res.toNat (BitVec.ofNat 32 w).toNat) (sem va vb))
    (hcast : ∀ assign : BVExpr.Assignment,
      sem (BitVec.cast (m := (BitVec.ofNat 32 w).toNat)
            (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]) (ea.eval assign))
        (BitVec.cast (m := (BitVec.ofNat 32 nw).toNat)
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnw_lt]) (eb.eval assign)) =
        BitVec.cast (m := (BitVec.ofNat 32 w).toNat)
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]) (e.eval assign)) :
    ∀ assign : BVExpr.Assignment,
      SliceDenotes g1 (atomAssign progBytes assign)
        (litsSlice lp1 res.toNat (BitVec.ofNat 32 w).toNat)
        (BitVec.cast (m := (BitVec.ofNat 32 w).toNat)
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]) (e.eval assign)) := by
  intro assign; rw [← hcast assign]
  exact hsem (atomAssign progBytes assign) _ _
    (sliceDenotes_cast (w2 := (BitVec.ofNat 32 w).toNat)
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]) (ha_sd assign))
    (sliceDenotes_cast (w2 := (BitVec.ofNat 32 nw).toNat)
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnw_lt]) (hb_sd assign))

local macro "dsm_shift_after" hok:ident hinv:ident hoom0:ident hni_lt:ident hw_lt:ident
    hnw_lt:ident ha_sd:ident hb_sd:ident hnd:ident hQ:ident castLem:term : tactic => `(tactic| (
  intro res hdr1 g1 aw1 ht1 lp1 m1 hfr1 hext1 haig1 hlp1 hlits_le hlcap_fn hpres1 _ _ hok_res hm1
  have hok1 := bvWorkspaceOk_of_smOpsFrame $hok hfr1 haig1 hlp1
  have hm1_b := blast_full_unfocus hok1.hdr_aig hok1.hdr_ht hok1.hdr_lits hm1; clear hm1
  have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr; c0_hsplit
  · c0_hstraight; exact dsm_aig_oom hok1 haig1 hfr1 hext1 $hinv hm1_b $hQ
  · have hoom1 : hdr1.oom = 0#32 := by assumption
    obtain ⟨_, _, _, _, hret, hlen1, hwf1, hsd1⟩ := hok_res hoom1
    have hlcap1 := hlcap_fn (by rw [bvWorkspaceOk_litsCap_eq $hok]; exact ($hinv).lits_le_cap)
    have hm1_so := blast_so_focus hok1.hdr_so hm1_b; clear hm1_b
    rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
    exact dsm_aig_ok_post $hoom0 hoom1 $hni_lt $hw_lt $hok hok1 haig1 hfr1 hext1 $hinv
      hlits_le hlcap1 hret hlen1 hpres1 hwf1 $hnd
      (dsm_shift_mul_sd $hw_lt $hnw_lt $ha_sd $hb_sd hsd1 $castLem) (by assumption) $hQ))

/-! ## 2. `bv_eval_ops_shift_mul_wp` -/

public section

theorem bv_eval_ops_shift_mul_wp (Γ : Env)
    (hRead : ∀ xs m Q X, bvReadU32Spec xs m Q X → Γ "bv_read_u32" [i64, i64] [i32] xs m Q X)
    (hRotl : ∀ xs m Q X, bvBlastRotlSpec xs m Q X →
      Γ "bv_blast_rotl" [i64, i32, i32, i32] [i32] xs m Q X)
    (hRotr : ∀ xs m Q X, bvBlastRotrSpec xs m Q X →
      Γ "bv_blast_rotr" [i64, i32, i32, i32] [i32] xs m Q X)
    (hAshrc : ∀ xs m Q X, bvBlastAshrcSpec xs m Q X →
      Γ "bv_blast_ashrc" [i64, i32, i32, i32] [i32] xs m Q X)
    (hRev : ∀ xs m Q X, bvBlastReverseSpec xs m Q X →
      Γ "bv_blast_reverse" [i64, i32, i32] [i32] xs m Q X)
    (hClz : ∀ xs m Q X, bvBlastClzSpec xs m Q X →
      Γ "bv_blast_clz" [i64, i32, i32] [i32] xs m Q X)
    (hRep : ∀ xs m Q X, bvBlastReplicateSpec xs m Q X →
      Γ "bv_blast_replicate" [i64, i32, i32, i32] [i32] xs m Q X)
    (hShl : ∀ xs m Q X, bvBlastShlSpec xs m Q X →
      Γ "bv_blast_shl" [i64, i32, i32, i32, i32] [i32] xs m Q X)
    (hUshr : ∀ xs m Q X, bvBlastUshrSpec xs m Q X →
      Γ "bv_blast_ushr" [i64, i32, i32, i32, i32] [i32] xs m Q X)
    (hAshr : ∀ xs m Q X, bvBlastAshrSpec xs m Q X →
      Γ "bv_blast_ashr" [i64, i32, i32, i32, i32] [i32] xs m Q X)
    (hMul : ∀ xs m Q X, bvBlastMulSpec xs m Q X →
      Γ "bv_blast_mul" [i64, i32, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvEvalSubSpec xs m Q X → Func.wp Γ bv_eval_ops_shift_mul_body xs m Q X := by
  rintro ⟨h, nodeIdx, ⟨⟩⟩ m Q X
    ⟨cfg, progPtr, progBytes, vars, cwords, nodes, prog, hdr, g, atomBases, sliceOffs,
      aigWords, htSlots, litsPool, R, rfl, hni_lt, hoom0, hinv, hm, hQ⟩
  have hok := hinv.ws_ok; have hp := hinv.parsed; have haig := hinv.aig_inv
  have hfit := hinv.prog_fit; have hn_lt : nodeIdx.toNat < u32At progBytes 3 := hinv.nn_eq ▸ hni_lt
  have hnw0 := drv_node_word0_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq hok.hdr_nv hok.nv_lt hni_lt
  have hnw1 := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq
    hok.hdr_nv hok.nv_lt hni_lt 1 1 rfl (by decide)
  have hnw2 := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq
    hok.hdr_nv hok.nv_lt hni_lt 2 2 rfl (by decide)
  have hnw3 := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq
    hok.hdr_nv hok.nv_lt hni_lt 3 3 rfl (by decide)
  have hfit' : hdr.prog_ptr.toNat + progBytes.length < 2 ^ 64 := hinv.prog_ptr_eq ▸ hfit
  have hm_bytes' : (bytes hdr.prog_ptr progBytes ⋆
      (bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R)) m :=
    hinv.prog_ptr_eq ▸ sep_ac hm
  have hm_hdr := blast_hdr_left hm
  c0_hstraight; c0_call hRead; refine ⟨progBytes, _, hfit', hnw0.2, hm_bytes', ?_⟩
  c0_hstraight; c0_call hRead; refine ⟨progBytes, _, hfit', hnw1.2, hm_bytes', ?_⟩
  c0_hstraight; c0_call hRead; refine ⟨progBytes, _, hfit', hnw2.2, hm_bytes', ?_⟩
  c0_hstraight; c0_call hRead; refine ⟨progBytes, _, hfit', hnw3.2, hm_bytes', ?_⟩
  c0_hstraight; rw [hnw0.1, hnw1.1, hnw2.1, hnw3.1]; clear hnw0 hnw1 hnw2 hnw3 hm_hdr
  generalize hop_eq :
    u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * nodeIdx.toNat) = op
  generalize hw_eq :
    u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * nodeIdx.toNat + 1) = w
  generalize ha_eq :
    u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * nodeIdx.toNat + 2) = a
  generalize hb_eq :
    u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * nodeIdx.toNat + 3) = b
  have hop_lt : op < 4294967296 := hop_eq ▸ u32At_lt ..
  have hw_lt : w < 4294967296 := hw_eq ▸ u32At_lt ..
  have ha_lt : a < 4294967296 := ha_eq ▸ u32At_lt ..
  have hb_lt : b < 4294967296 := hb_eq ▸ u32At_lt ..
  have hlp_cap := bvWorkspaceOk_litsPool_eq_cap hok
  have hw32 : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
  have hb32 : (BitVec.ofNat 32 b).toNat = b := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt]
  have hni_so : (BitVec.setWidth 64 nodeIdx).toNat < sliceOffs.length := by
    rw [bv32_setWidth64_toNat, hok.so_len]; exact hni_lt
  have hm_bytes : (bytes progPtr progBytes ⋆
      (bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R)) m := sep_ac hm
  c0_hsplit
  · -- Case 1: BV_OP_ROTL (11)
    have hop11 : op = opRotL := by unfold opRotL; c0_bv_omega [hop_lt]
    clear hc; have hun := parsed_node_unop hp hn_lt
      (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop11]; unfold opUmod opRotL; decide)
      (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop11]; unfold opCpop opRotL; decide)
    dsimp only at hun; rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hun
    rcases hun with ⟨ha_lt_ni, uop, ea, _, huop, _, _, _, _, _, hga, hnd⟩; rw [huop hop11] at hnd
    obtain ⟨ha_so, _, ha_le, _, ha_wf, _, ha_sd⟩ :=
      drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
    have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
    have hm_hl := blast_hdr_lits_focus hok.hdr_lits (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
    c0_call hRotl; refine ⟨hdr, litsPool, _, hlp_cap, hm_hl, ?_⟩
    intro res hdr1 lp1 m1 hfr1 hal1 hlp1 hpres1 hgood1 hbad1 hm1
    have hm1_b := blast_hdr_lits_unfocus (hfr1.lits_ptr.trans hok.hdr_lits) hm1; clear hm1
    have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr; c0_hsplit
    · c0_hstraight; exact dsm_pure_oom hok hfr1 hal1 hlp1 hinv hm1_b hQ
    · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
      have hm1_so := blast_so_focus (hfr1.slice_off_ptr.trans hok.hdr_so) hm1_b; clear hm1_b
      rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
      refine dsm_pure_unop_idx hoom0 hoom1 hni_lt hw_lt hok hfr1 hal1 hlp1 hinv hgood1 hbad1
        (fun h => by dsimp only at h; rw [decide_eq_true_eq, hw32] at h; exact h.2.2) hpres1
        (fun j hj => by
          simp only [hw32, hb32]; have := Nat.mod_lt b (by omega : 0 < w)
          split <;> exact ha_wf _ (by omega))
        hnd (fun assign j hj => by
          have hsd := (sliceDenotes_iff (by rw [hok.lits_len]; have := hinv.lits_le_cap; omega)).mp
            (ha_sd assign)
          simp only [hw32, hb32, BVExpr.eval, BVUnOp.eval]; rw [dsm_getLsbD_rotl _ b j hj]
          have := Nat.mod_lt b (by omega : 0 < w); split <;> exact hsd _ (by omega))
        (by assumption) hQ
  · clear hc; c0_hstraight; c0_hsplit
    · -- Case 2: BV_OP_ROTR (12)
      have hop12 : op = opRotR := by unfold opRotR; c0_bv_omega [hop_lt]
      clear hc; have hun := parsed_node_unop hp hn_lt
        (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop12]; unfold opUmod opRotR; decide)
        (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop12]; unfold opCpop opRotR; decide)
      dsimp only at hun; rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hun
      rcases hun with ⟨ha_lt_ni, uop, ea, _, _, huop, _, _, _, _, hga, hnd⟩; rw [huop hop12] at hnd
      obtain ⟨ha_so, _, ha_le, _, ha_wf, _, ha_sd⟩ :=
        drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
      have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
      have hm_hl := blast_hdr_lits_focus hok.hdr_lits
        (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
      c0_call hRotr; refine ⟨hdr, litsPool, _, hlp_cap, hm_hl, ?_⟩
      intro res hdr1 lp1 m1 hfr1 hal1 hlp1 hpres1 hgood1 hbad1 hm1
      have hm1_b := blast_hdr_lits_unfocus (hfr1.lits_ptr.trans hok.hdr_lits) hm1; clear hm1
      have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr; c0_hsplit
      · c0_hstraight; exact dsm_pure_oom hok hfr1 hal1 hlp1 hinv hm1_b hQ
      · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
        have hm1_so := blast_so_focus (hfr1.slice_off_ptr.trans hok.hdr_so) hm1_b; clear hm1_b
        rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
        refine dsm_pure_unop_idx hoom0 hoom1 hni_lt hw_lt hok hfr1 hal1 hlp1 hinv hgood1 hbad1
          (fun h => by dsimp only at h; rw [decide_eq_true_eq, hw32] at h; exact h.2.2) hpres1
          (fun j hj => by
            simp only [hw32, hb32]; have := Nat.mod_lt b (by omega : 0 < w)
            split <;> exact ha_wf _ (by omega))
          hnd (fun assign j hj => by
            have hsd := (sliceDenotes_iff
              (by rw [hok.lits_len]; have := hinv.lits_le_cap; omega)).mp (ha_sd assign)
            simp only [hw32, hb32, BVExpr.eval, BVUnOp.eval]; rw [dsm_getLsbD_rotr _ b j hj]
            have := Nat.mod_lt b (by omega : 0 < w); split <;> exact hsd _ (by omega))
          (by assumption) hQ
    · clear hc; c0_hstraight; c0_hsplit
      · -- Case 3: BV_OP_ASHRC (13)
        have hop13 : op = opAshrC := by unfold opAshrC; c0_bv_omega [hop_lt]
        clear hc; have hun := parsed_node_unop hp hn_lt
          (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop13]; unfold opUmod opAshrC; decide)
          (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop13]; unfold opCpop opAshrC; decide)
        dsimp only at hun; rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hun
        rcases hun with ⟨ha_lt_ni, uop, ea, _, _, _, huop, _, _, _, hga, hnd⟩
        rw [huop hop13] at hnd
        obtain ⟨ha_so, _, ha_le, _, ha_wf, _, ha_sd⟩ :=
          drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
        have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
        have hm_hl := blast_hdr_lits_focus hok.hdr_lits
          (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
        c0_call hAshrc; refine ⟨hdr, litsPool, _, hlp_cap, hm_hl, ?_⟩
        intro res hdr1 lp1 m1 hfr1 hal1 hlp1 hpres1 hgood1 hbad1 hm1
        have hm1_b := blast_hdr_lits_unfocus (hfr1.lits_ptr.trans hok.hdr_lits) hm1; clear hm1
        have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr; c0_hsplit
        · c0_hstraight; exact dsm_pure_oom hok hfr1 hal1 hlp1 hinv hm1_b hQ
        · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
          have hm1_so := blast_so_focus (hfr1.slice_off_ptr.trans hok.hdr_so) hm1_b; clear hm1_b
          rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
          refine dsm_pure_unop_idx hoom0 hoom1 hni_lt hw_lt hok hfr1 hal1 hlp1 hinv hgood1 hbad1
            (fun h => by dsimp only at h; rw [decide_eq_true_eq, hw32] at h; exact h.2.2) hpres1
            (fun j hj => by simp only [hw32, hb32]; split <;> exact ha_wf _ (by omega))
            hnd (fun assign j hj => by
              have hsd := (sliceDenotes_iff
                (by rw [hok.lits_len]; have := hinv.lits_le_cap; omega)).mp (ha_sd assign)
              simp only [hw32, hb32, BVExpr.eval, BVUnOp.eval]; rw [dsm_getLsbD_ashrc _ b j hj]
              split <;> exact hsd _ (by omega))
            (by assumption) hQ
      · clear hc; c0_hstraight; c0_hsplit
        · -- Case 4: BV_OP_REVERSE (14)
          have hop14 : op = opReverse := by unfold opReverse; c0_bv_omega [hop_lt]
          clear hc; have hun := parsed_node_unop hp hn_lt
            (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop14]; unfold opUmod opReverse; decide)
            (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop14]; unfold opCpop opReverse; decide)
          dsimp only at hun; rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq] at hun
          rcases hun with ⟨ha_lt_ni, uop, ea, _, _, _, _, huop, _, _, hga, hnd⟩
          rw [huop hop14] at hnd
          obtain ⟨ha_so, _, ha_le, _, ha_wf, _, ha_sd⟩ :=
            drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
          have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
          have hm_hl := blast_hdr_lits_focus hok.hdr_lits
            (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
          c0_call hRev; refine ⟨hdr, litsPool, _, hlp_cap, hm_hl, ?_⟩
          intro res hdr1 lp1 m1 hfr1 hal1 hlp1 hpres1 hgood1 hbad1 hm1
          have hm1_b := blast_hdr_lits_unfocus (hfr1.lits_ptr.trans hok.hdr_lits) hm1; clear hm1
          have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr; c0_hsplit
          · c0_hstraight; exact dsm_pure_oom hok hfr1 hal1 hlp1 hinv hm1_b hQ
          · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
            have hm1_so := blast_so_focus (hfr1.slice_off_ptr.trans hok.hdr_so) hm1_b; clear hm1_b
            rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
            refine dsm_pure_unop_idx hoom0 hoom1 hni_lt hw_lt hok hfr1 hal1 hlp1 hinv hgood1 hbad1
              (fun h => by dsimp only at h; rw [decide_eq_true_eq, hw32] at h; exact h.2.2) hpres1
              (fun j hj => by simp only [hw32]; exact ha_wf _ (by omega)) hnd
              (fun assign j hj => by
                have hsd := (sliceDenotes_iff
                  (by rw [hok.lits_len]; have := hinv.lits_le_cap; omega)).mp (ha_sd assign)
                simp only [hw32, BVExpr.eval, BVUnOp.eval]
                rw [dsm_getLsbD_reverse _ j hj]; exact hsd _ (by omega))
              (by assumption) hQ
        · clear hc; c0_hstraight; c0_hsplit
          · -- Case 5: BV_OP_CLZ (15)
            have hop15 : op = opClz := by unfold opClz; c0_bv_omega [hop_lt]
            clear hc; have hun := parsed_node_unop hp hn_lt
              (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop15]; unfold opUmod opClz; decide)
              (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop15]; unfold opCpop opClz; decide)
            dsimp only at hun; rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq] at hun
            rcases hun with ⟨ha_lt_ni, uop, ea, _, _, _, _, _, huop, _, hga, hnd⟩
            rw [huop hop15] at hnd
            obtain ⟨ha_so, _, _, _, ha_wf, _, ha_sd⟩ :=
              drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
            have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
            have hm_f := blast_full_focus hok.hdr_aig hok.hdr_ht hok.hdr_lits
              (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
            c0_call hClz
            refine ⟨hdr, g, aigWords, htSlots, litsPool, _, haig, hlp_cap,
              fun _ _ => by rw [hw32]; exact ha_wf, hm_f, ?_⟩
            intro res hdr1 g1 aw1 ht1 lp1 m1 hfr1 hext1 haig1 hlp1 hlits_le hlcap_fn hpres1 _ _
              hok_res hm1
            have hok1 := bvWorkspaceOk_of_smOpsFrame hok hfr1 haig1 hlp1
            have hm1_b := blast_full_unfocus hok1.hdr_aig hok1.hdr_ht hok1.hdr_lits hm1; clear hm1
            have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr; c0_hsplit
            · c0_hstraight; exact dsm_aig_oom hok1 haig1 hfr1 hext1 hinv hm1_b hQ
            · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
              obtain ⟨_, _, hret, hlen1, hwf1, hsd1⟩ := hok_res hoom1
              have hlcap1 := hlcap_fn (by rw [bvWorkspaceOk_litsCap_eq hok]; exact hinv.lits_le_cap)
              have hm1_so := blast_so_focus hok1.hdr_so hm1_b; clear hm1_b
              rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
              refine dsm_aig_ok_post hoom0 hoom1 hni_lt hw_lt hok hok1 haig1 hfr1 hext1 hinv
                hlits_le hlcap1 hret hlen1 hpres1 hwf1 hnd (fun assign => ?_) (by assumption) hQ
              have h := hsd1 (atomAssign progBytes assign) _
                (sliceDenotes_cast hw32.symm (ha_sd assign))
              rw [bv_clz_cast] at h; exact h
          · clear hc; c0_hstraight; c0_hsplit
            · -- Case 6: BV_OP_REPLICATE (18)
              have hop18 : op = opReplicate := by unfold opReplicate; c0_bv_omega [hop_lt]
              clear hc; have hrep := parsed_node_replicate hp hn_lt
                (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop18)
              dsimp only at hrep; rw [← hinv.nv_eq, ← hinv.nc_eq, hw_eq, ha_eq, hb_eq] at hrep
              rcases hrep with ⟨ha_lt_ni, haw_mul, ea, hmul_eq, hga, hnd⟩
              obtain ⟨haw_idx, haw_fit⟩ := drv0_node_width_read hinv hok ha_lt ha_lt_ni hni_lt
              have hm_hdr' := blast_hdr_left hm; c0_hstraight; clear hm_hdr'
              rw [hinv.prog_ptr_eq]; c0_call hRead
              refine ⟨progBytes, _, hfit, haw_fit, hm_bytes, ?_⟩; rw [haw_idx]
              let aw_n := u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * a + 1)
              have haw_lt : aw_n < 4294967296 := u32At_lt ..
              have haw32 : (BitVec.ofNat 32 aw_n).toNat = aw_n := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haw_lt]
              obtain ⟨ha_so, _, ha_le, _, ha_wf, _, ha_sd⟩ :=
                drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
              have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
              have hm_hl := blast_hdr_lits_focus hok.hdr_lits
                (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
              c0_call hRep; refine ⟨hdr, litsPool, _, hlp_cap, hm_hl, ?_⟩
              intro res hdr1 lp1 m1 hfr1 hal1 hlp1 hpres1 hgood1 hbad1 hm1
              have hm1_b := blast_hdr_lits_unfocus (hfr1.lits_ptr.trans hok.hdr_lits) hm1; clear hm1
              have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr; c0_hsplit
              · c0_hstraight; exact dsm_pure_oom hok hfr1 hal1 hlp1 hinv hm1_b hQ
              · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
                have hm1_so := blast_so_focus (hfr1.slice_off_ptr.trans hok.hdr_so) hm1_b
                clear hm1_b; rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
                rw [haw32, hb32, haw_mul] at hgood1 hbad1
                have haw_pos : ∀ j < w, 0 < aw_n := fun j hj => by
                  rcases Nat.eq_zero_or_pos aw_n with h0 | hp
                  · dsimp only [aw_n] at h0; rw [h0] at haw_mul; simp at haw_mul; omega
                  · exact hp
                refine dsm_pure_unop_idx hoom0 hoom1 hni_lt hw_lt hok hfr1 hal1 hlp1 hinv hgood1
                  hbad1 (fun h => by dsimp only at h; rw [decide_eq_true_eq] at h; exact h.2.2)
                  hpres1 (fun j hj => ha_wf (j % aw_n) (Nat.mod_lt j (haw_pos j hj))) hnd
                  (fun assign j hj => by
                    have hsd := (sliceDenotes_iff
                      (by rw [hok.lits_len]; have := hinv.lits_le_cap; omega)).mp (ha_sd assign)
                    have hp := haw_pos j hj; subst hmul_eq; simp only [BVExpr.eval]
                    rw [dsm_getLsbD_replicate _ j hj]; exact hsd (j % aw_n) (Nat.mod_lt j hp))
                  (by assumption) hQ
            · clear hc; c0_hstraight; c0_hsplit
              · -- Case 7: BV_OP_SHL (19)
                have hop19 : op = opShl := by unfold opShl; c0_bv_omega [hop_lt]
                clear hc; have hsh := parsed_node_shift hp hn_lt
                  (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop19]
                      unfold opReplicate opShl; decide)
                  (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop19]; unfold opShl opAshr; decide)
                dsimp only at hsh
                rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hsh
                rcases hsh with ⟨ha_lt_ni, hb_lt_ni, ea, eb, hga, hgb, hnd_f, _, _⟩
                have hnd := hnd_f hop19
                obtain ⟨hnw_idx, hnw_fit⟩ := drv0_node_width_read hinv hok hb_lt hb_lt_ni hni_lt
                have hm_hdr' := blast_hdr_left hm; c0_hstraight; clear hm_hdr'
                rw [hinv.prog_ptr_eq]; c0_call hRead
                refine ⟨progBytes, _, hfit, hnw_fit, hm_bytes, ?_⟩; rw [hnw_idx]
                let nw_n := u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * b + 1)
                have hnw_lt : nw_n < 4294967296 := u32At_lt ..
                have hnw32 : (BitVec.ofNat 32 nw_n).toNat = nw_n := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnw_lt]
                obtain ⟨ha_so, _, _, _, ha_wf, _, ha_sd⟩ :=
                  drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
                obtain ⟨hb_so, _, _, _, hb_wf, _, hb_sd⟩ :=
                  drv_child_bv_prep hb_lt hb_lt_ni hoom0 hinv hni_lt hgb
                have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
                have hm_f := blast_full_focus hok.hdr_aig hok.hdr_ht hok.hdr_lits
                  (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
                c0_call hShl; refine ⟨hdr, g, aigWords, htSlots, litsPool, _, haig, hlp_cap,
                  fun hf => absurd hf Bool.false_ne_true,
                  fun _ _ _ _ => ⟨by rw [hw32]; exact ha_wf, by rw [hnw32]; exact hb_wf⟩,
                  hm_f, ?_⟩
                dsm_shift_after hok hinv hoom0 hni_lt hw_lt hnw_lt ha_sd hb_sd hnd hQ
                  (fun _ => bv_shl_cast hw32.symm hnw32.symm ..)
              · clear hc; c0_hstraight; c0_hsplit
                · -- Case 8: BV_OP_USHR (20)
                  have hop20 : op = opUshr := by unfold opUshr; c0_bv_omega [hop_lt]
                  clear hc; have hsh := parsed_node_shift hp hn_lt
                    (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop20]
                        unfold opReplicate opUshr; decide)
                    (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop20]
                        unfold opUshr opAshr; decide)
                  dsimp only at hsh
                  rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hsh
                  rcases hsh with ⟨ha_lt_ni, hb_lt_ni, ea, eb, hga, hgb, _, hnd_f, _⟩
                  have hnd := hnd_f hop20
                  obtain ⟨hnw_idx, hnw_fit⟩ := drv0_node_width_read hinv hok hb_lt hb_lt_ni hni_lt
                  have hm_hdr' := blast_hdr_left hm; c0_hstraight; clear hm_hdr'
                  rw [hinv.prog_ptr_eq]; c0_call hRead
                  refine ⟨progBytes, _, hfit, hnw_fit, hm_bytes, ?_⟩; rw [hnw_idx]
                  let nw_n := u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * b + 1)
                  have hnw_lt : nw_n < 4294967296 := u32At_lt ..
                  have hnw32 : (BitVec.ofNat 32 nw_n).toNat = nw_n := by
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnw_lt]
                  obtain ⟨ha_so, _, _, _, ha_wf, _, ha_sd⟩ :=
                    drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
                  obtain ⟨hb_so, _, _, _, hb_wf, _, hb_sd⟩ :=
                    drv_child_bv_prep hb_lt hb_lt_ni hoom0 hinv hni_lt hgb
                  have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
                  have hm_f := blast_full_focus hok.hdr_aig hok.hdr_ht hok.hdr_lits
                    (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
                  c0_call hUshr; refine ⟨hdr, g, aigWords, htSlots, litsPool, _, haig, hlp_cap,
                    fun hf => absurd hf Bool.false_ne_true,
                    fun _ _ _ _ => ⟨by rw [hw32]; exact ha_wf, by rw [hnw32]; exact hb_wf⟩,
                    hm_f, ?_⟩
                  dsm_shift_after hok hinv hoom0 hni_lt hw_lt hnw_lt ha_sd hb_sd hnd hQ
                    (fun _ => bv_ushr_cast hw32.symm hnw32.symm ..)
                · clear hc; c0_hstraight; c0_hsplit
                  · -- Case 9: BV_OP_ASHR (21)
                    have hop21 : op = opAshr := by unfold opAshr; c0_bv_omega [hop_lt]
                    clear hc; have hsh := parsed_node_shift hp hn_lt
                      (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop21]
                          unfold opReplicate opAshr; decide)
                      (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop21]; unfold opAshr; decide)
                    dsimp only at hsh
                    rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hsh
                    rcases hsh with ⟨ha_lt_ni, hb_lt_ni, ea, eb, hga, hgb, _, _, hnd_f⟩
                    have hnd := hnd_f hop21
                    obtain ⟨hnw_idx, hnw_fit⟩ := drv0_node_width_read hinv hok hb_lt hb_lt_ni hni_lt
                    have hm_hdr' := blast_hdr_left hm; c0_hstraight; clear hm_hdr'
                    rw [hinv.prog_ptr_eq]; c0_call hRead
                    refine ⟨progBytes, _, hfit, hnw_fit, hm_bytes, ?_⟩; rw [hnw_idx]
                    let nw_n := u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * b + 1)
                    have hnw_lt : nw_n < 4294967296 := u32At_lt ..
                    have hnw32 : (BitVec.ofNat 32 nw_n).toNat = nw_n := by
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnw_lt]
                    obtain ⟨ha_so, _, _, _, ha_wf, _, ha_sd⟩ :=
                      drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
                    obtain ⟨hb_so, _, _, _, hb_wf, _, hb_sd⟩ :=
                      drv_child_bv_prep hb_lt hb_lt_ni hoom0 hinv hni_lt hgb
                    have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
                    have hm_f := blast_full_focus hok.hdr_aig hok.hdr_ht hok.hdr_lits
                      (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
                    c0_call hAshr; refine ⟨hdr, g, aigWords, htSlots, litsPool, _, haig, hlp_cap,
                      fun hf => absurd hf Bool.false_ne_true,
                      fun _ _ _ _ => ⟨by rw [hw32]; exact ha_wf, by rw [hnw32]; exact hb_wf⟩,
                      hm_f, ?_⟩
                    dsm_shift_after hok hinv hoom0 hni_lt hw_lt hnw_lt ha_sd hb_sd hnd hQ
                      (fun _ => bv_ashr_cast hw32.symm hnw32.symm ..)
                  · clear hc; c0_hstraight; c0_hsplit
                    · -- Case 10: BV_OP_MUL (7)
                      have hop7 : op = opMul := by unfold opMul; c0_bv_omega [hop_lt]
                      clear hc; have hbin := parsed_node_binop hp hn_lt
                        (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop7]; unfold opMul; decide)
                        (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop7]
                            unfold opMul opUmod; decide)
                      dsimp only at hbin
                      rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hbin
                      rcases hbin with
                        ⟨ha_lt_ni, hb_lt_ni, bop, ea, eb, _, _, _, _, hbop, _, _, hga, hgb, hnd⟩
                      rw [hbop hop7] at hnd
                      obtain ⟨ha_so, _, _, _, ha_wf, _, ha_sd⟩ :=
                        drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
                      obtain ⟨hb_so, _, _, _, hb_wf, _, hb_sd⟩ :=
                        drv_child_bv_prep hb_lt hb_lt_ni hoom0 hinv hni_lt hgb
                      have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
                      have hm_f := blast_full_focus hok.hdr_aig hok.hdr_ht hok.hdr_lits
                        (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
                      c0_call hMul
                      refine ⟨hdr, g, aigWords, htSlots, litsPool, _, haig, hlp_cap,
                        fun hf => absurd hf Bool.false_ne_true,
                        fun _ _ _ _ => ⟨by rw [hw32]; exact ha_wf, by rw [hw32]; exact hb_wf⟩,
                        hm_f, ?_⟩
                      dsm_shift_after hok hinv hoom0 hni_lt hw_lt hw_lt ha_sd hb_sd hnd hQ
                        (fun _ => bv_mul_cast hw32.symm ..)
                    · clear hc; c0_hstraight
                      exact hQ false hdr g sliceOffs aigWords htSlots litsPool m hok haig
                        (Aig.extends_rfl g) hinv.prog_ptr_eq rfl rfl
                        (fun hf => absurd hf Bool.false_ne_true) hm

end

end LeanQbe.T.Examples.Bitblast.Proof
