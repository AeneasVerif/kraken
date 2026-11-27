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
# Core Evaluator Dispatcher WP Proof (`Bitblast.Proof.Driver0`)

Proves `Γ`-parametric `Func.wp` soundness for `bv_eval_ops_core` (`VAR`, `CONST`, `EXTRACT`,
`AND`, `OR`, `XOR`, `ADD`, `NOT`, `APPEND`, `EQ`, `ULT`, `GETLSBD`) against `bvEvalSubSpec`.
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

@[local c0_load] private theorem drv_load_prog_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 16) = some s.prog_ptr := load_hdr_prog_ptr hm

@[local c0_load] private theorem drv_load_atom_base_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 40) = some s.atom_base_ptr := load_hdr_atom_base_ptr hm

@[local c0_load] private theorem drv_load_slice_off_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 48) = some s.slice_off_ptr := load_hdr_slice_off_ptr hm

@[local c0_load] private theorem drv_load_lits_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 56) = some s.lits_ptr := load_hdr_lits_ptr hm

@[local c0_load] private theorem drv_load_n_vars {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 80) = some s.n_vars := load_hdr_n_vars hm

@[local c0_load] private theorem drv_load_n_cwords {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 88) = some s.n_cwords := load_hdr_n_cwords hm

@[local c0_load] private theorem drv_load_oom {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 120) = some s.oom := load_hdr_oom hm

/-! ## 1. `OpsCore` Postcondition Closing Helpers -/

private theorem bv_add_cast {w1 w2 : Nat} (h : w1 = w2) (a b : BitVec w1) :
    BitVec.cast h a + BitVec.cast h b = BitVec.cast h (a + b) := by
  subst h; rfl

private theorem bv_ult_cast {w1 w2 : Nat} (h : w1 = w2) (a b : BitVec w1) :
    BitVec.ult (BitVec.cast h a) (BitVec.cast h b) = BitVec.ult a b := by
  subst h; rfl

private theorem oc_lits_oom {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g : Aig}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp lp1 : List (BitVec 32)}
    {nodeIdx : BitVec 32} {R : Mem 64 → Prop} {m1 : Mem 64} {Q : Post [.bool]}
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) (hfr1 : hdr.BlastFrame hdr1)
    (hal1 : hdr1.aig_len = hdr.aig_len) (hlp1 : lp1.length = lp.length)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hm1 : (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 ab so aw ht lp1 ⋆ R) m1)
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (false, ⟨⟩) m1 := by
  have haig1 := aigInv_of_ocBlastFrame hinv.aig_inv hfr1 hal1
  have hok1 := bvWorkspaceOk_of_ocBlastFrame hok hfr1 haig1 hlp1
  exact hQ false hdr1 g so aw ht lp1 m1 hok1 haig1 (Aig.extends_rfl g)
    (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
    (fun hf => absurd hf Bool.false_ne_true) hm1

private theorem oc_aig_oom {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g g1 : Aig}
    {ab so : List (BitVec 32)} {aw aw1 : List (BitVec 64)} {ht ht1 lp lp1 : List (BitVec 32)}
    {nodeIdx : BitVec 32} {R : Mem 64 → Prop} {m1 : Mem 64} {Q : Post [.bool]}
    (hok1 : BVWorkspaceOk cfg hdr1 ab so aw1 ht1 lp1) (haig1 : AigInv hdr1 g1 aw1 ht1)
    (hext1 : g ≤ g1)
    (hpp : hdr1.prog_ptr = hdr.prog_ptr) (hnc : hdr1.n_cwords = hdr.n_cwords)
    (hrt : hdr1.root_node = hdr.root_node)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hm1 : (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 ab so aw1 ht1 lp1 ⋆ R) m1)
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (false, ⟨⟩) m1 :=
  hQ false hdr1 g1 so aw1 ht1 lp1 m1 hok1 haig1 hext1
    (hpp.trans hinv.prog_ptr_eq) hnc hrt (fun hf => absurd hf Bool.false_ne_true) hm1

private theorem oc_lits_bv_ok {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g : Aig}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp lp1 : List (BitVec 32)}
    {nodeIdx res : BitVec 32} {w : Nat} {e : BVExpr w} {R : Mem 64 → Prop} {m' : Mem 64}
    {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hoom1 : hdr1.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hw_lt : w < 4294967296) (hok : BVWorkspaceOk cfg hdr ab so aw ht lp)
    (hfr1 : hdr.BlastFrame hdr1) (hal1 : hdr1.aig_len = hdr.aig_len) (hlp1 : lp1.length = lp.length)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hroom : w ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat)
    (hret : res = hdr.lits_len) (hlen1 : hdr1.lits_len = hdr.lits_len + BitVec.ofNat 32 w)
    (hagree : ∀ p < hdr.lits_len.toNat, lp1.getD p 0#32 = lp.getD p 0#32)
    (hnd : nodes.get? nodeIdx.toNat = some (.bv w e))
    (hbd : ∀ j < w, (lp1.getD (res.toNat + j) 0#32 >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hsd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g (atomAssign progBytes assign) (litsSlice lp1 res.toNat w) (e.eval assign))
    (hm_so : (array (t := i32) hdr.slice_off_ptr (so.set (BitVec.setWidth 64 nodeIdx).toNat res) ⋆
      blastSoRest cfg hdr1 progPtr progBytes ab aw ht lp1 R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  have haig1 := aigInv_of_ocBlastFrame hinv.aig_inv hfr1 hal1
  have hok1 := bvWorkspaceOk_of_ocBlastFrame hok hfr1 haig1 hlp1
  have hlc_eq := bvWorkspaceOk_litsCap_eq hok; have hlen_le := hinv.lits_le_cap
  have hl1_nat : hdr1.lits_len.toNat = hdr.lits_len.toNat + w := by
    have := hok.lcap_lt
    rw [hlen1, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt,
      Nat.mod_eq_of_lt (by omega)]
  exact drv_sub_bv_ok hoom0 hoom1 hni_lt hok hok1 haig1 (Aig.extends_rfl g) hinv
    (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
    (by omega) (by omega) hagree hnd (by rw [hret]; omega) hbd hsd hm_so hQ

private theorem oc_aig_bv_ok {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g g1 : Aig}
    {ab so : List (BitVec 32)} {aw aw1 : List (BitVec 64)} {ht ht1 lp lp1 : List (BitVec 32)}
    {nodeIdx res : BitVec 32} {w : Nat} {e : BVExpr w} {R : Mem 64 → Prop} {m' : Mem 64}
    {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hoom1 : hdr1.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hw_lt : w < 4294967296) (hok : BVWorkspaceOk cfg hdr ab so aw ht lp)
    (hok1 : BVWorkspaceOk cfg hdr1 ab so aw1 ht1 lp1)
    (haig1 : AigInv hdr1 g1 aw1 ht1) (hfr1 : hdr.BlastFrame hdr1) (hext1 : g ≤ g1)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hroom : w ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat)
    (hret : res = hdr.lits_len) (hlen1 : hdr1.lits_len = hdr.lits_len + BitVec.ofNat 32 w)
    (hagree : ∀ p < hdr.lits_len.toNat, lp1.getD p 0#32 = lp.getD p 0#32)
    (hwf1 : SliceAigWf hdr1.aig_len.toNat lp1 res.toNat (BitVec.ofNat 32 w).toNat)
    (hnd : nodes.get? nodeIdx.toNat = some (.bv w e))
    (hsd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g1 (atomAssign progBytes assign) (litsSlice lp1 res.toNat w) (e.eval assign))
    (hm_so : (array (t := i32) hdr.slice_off_ptr (so.set (BitVec.setWidth 64 nodeIdx).toNat res) ⋆
      blastSoRest cfg hdr1 progPtr progBytes ab aw1 ht1 lp1 R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  have hw32 : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
  have hlc_eq := bvWorkspaceOk_litsCap_eq hok; have hlen_le := hinv.lits_le_cap
  have hl1_nat : hdr1.lits_len.toNat = hdr.lits_len.toNat + w := by
    have := hok.lcap_lt; rw [hlen1, BitVec.toNat_add, hw32, Nat.mod_eq_of_lt (by omega)]
  exact drv_sub_bv_ok hoom0 hoom1 hni_lt hok hok1 haig1 hext1 hinv
    (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
    (by omega) (by omega) hagree hnd (by rw [hret]; omega)
    (fun j hj => by rw [← haig1.aig_len_eq]; exact hwf1 j (by omega)) hsd hm_so hQ

private theorem oc_bitwise_ok {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g g1 : Aig}
    {ab so : List (BitVec 32)} {aw aw1 : List (BitVec 64)} {ht ht1 lp lp1 : List (BitVec 32)}
    {nodeIdx aOff bOff res : BitVec 32} {w : Nat} {ea eb : BVExpr w} {bop : BVBinOp}
    {f : Bool → Bool → Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hoom1 : hdr1.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hw_lt : w < 4294967296) (hok : BVWorkspaceOk cfg hdr ab so aw ht lp)
    (hok1 : BVWorkspaceOk cfg hdr1 ab so aw1 ht1 lp1)
    (haig1 : AigInv hdr1 g1 aw1 ht1) (hfr1 : hdr.BlastFrame hdr1) (hext1 : g ≤ g1)
    (hlp1 : lp1.length = lp.length)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (ha_le : aOff.toNat + w ≤ hdr.lits_len.toNat) (hb_le : bOff.toNat + w ≤ hdr.lits_len.toNat)
    (ha_sd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g (atomAssign progBytes assign) (litsSlice lp aOff.toNat w) (ea.eval assign))
    (hb_sd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g (atomAssign progBytes assign) (litsSlice lp bOff.toNat w) (eb.eval assign))
    (hroom : (BitVec.ofNat 32 w).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat)
    (hret : res = hdr.lits_len) (hlen1 : hdr1.lits_len = hdr.lits_len + BitVec.ofNat 32 w)
    (hagree : ∀ p < hdr.lits_len.toNat, lp1.getD p 0#32 = lp.getD p 0#32)
    (hwf1 : SliceAigWf hdr1.aig_len.toNat lp1 res.toNat (BitVec.ofNat 32 w).toNat)
    (hbits : ∀ j < (BitVec.ofNat 32 w).toNat, ∀ ρ,
      g1.evalLit ρ (UInt32.ofBitVec (lp1.getD (res.toNat + j) 0#32)) =
        f (g.evalLit ρ (UInt32.ofBitVec (lp.getD (aOff.toNat + j) 0#32)))
          (g.evalLit ρ (UInt32.ofBitVec (lp.getD (bOff.toNat + j) 0#32))))
    (hnd : nodes.get? nodeIdx.toNat = some (.bv w (.bin ea bop eb)))
    (hfb : ∀ (assign : BVExpr.Assignment) (j : Nat), j < w →
      ((BVExpr.bin ea bop eb).eval assign).getLsbD j =
        f ((ea.eval assign).getLsbD j) ((eb.eval assign).getLsbD j))
    (hm_so : (array (t := i32) hdr.slice_off_ptr (so.set (BitVec.setWidth 64 nodeIdx).toNat res) ⋆
      blastSoRest cfg hdr1 progPtr progBytes ab aw1 ht1 lp1 R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  have hw32 : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
  have hlc := bvWorkspaceOk_litsCap_eq hok; have hle_c := hinv.lits_le_cap
  refine oc_aig_bv_ok hoom0 hoom1 hni_lt hw_lt hok hok1 haig1 hfr1 hext1 hinv
    (hw32 ▸ hroom) hret hlen1 hagree hwf1 hnd (fun assign => ?_) hm_so hQ
  exact sliceDenotes_binop_bits (by rw [hok.lits_len]; omega) (by rw [hok.lits_len]; omega)
    (by rw [hlp1, hok.lits_len, hret]; omega) (ha_sd assign) (hb_sd assign) (hfb assign)
    (fun j hj => hbits j (by omega) (atomAssign progBytes assign))

private theorem oc_var_const_oom {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr : BVHdrState} {g : Aig}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp : List (BitVec 32)}
    {nodeIdx : BitVec 32} {R : Mem 64 → Prop} {m1 : Mem 64} {Q : Post [.bool]}
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) (haig : AigInv hdr g aw ht)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hm1 : (bvHdrMem cfg.work_base { hdr with oom := 1#32 } ⋆
      (bytes progPtr progBytes ⋆
        (array (t := i32) (cfg.work_base + 128) ab ⋆
          region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
            (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
          array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) so ⋆
          region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
            (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
          array64 cfg.aig_ptr aw ⋆ array (t := i32) cfg.ht_ptr ht ⋆
          array (t := i32) cfg.lits_ptr lp ⋆
          region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
            (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ R))) m1)
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (false, ⟨⟩) m1 := by
  have hm1_blast : (bytes progPtr progBytes ⋆
      bvBlastMem cfg { hdr with oom := 1#32 } ab so aw ht lp ⋆ R) m1 := by
    rw [bvBlastMem_hdr_left]; exact sep_ac hm1
  exact drv0_oom_close hok haig hinv hm1_blast hQ

private theorem oc_extract_ok {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g : Aig}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp lp1 : List (BitVec 32)}
    {nodeIdx bOff res : BitVec 32} {w a bw_n : Nat} {eb : BVExpr bw_n}
    {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hoom1 : hdr1.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hw_lt : w < 4294967296) (ha_lt : a < 4294967296) (hbw_lt : bw_n < 4294967296)
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) (hfr1 : hdr.BlastFrame hdr1)
    (hal1 : hdr1.aig_len = hdr.aig_len) (hlp1 : lp1.length = lp.length)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hb_le : bOff.toNat + bw_n ≤ hdr.lits_len.toNat) (hb_wf : SliceLitsWf g lp bOff.toNat bw_n)
    (hb_sd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g (atomAssign progBytes assign) (litsSlice lp bOff.toNat bw_n) (eb.eval assign))
    (hroom : (BitVec.ofNat 32 w).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat)
    (hret : res = hdr.lits_len) (hlen1 : hdr1.lits_len = hdr.lits_len + BitVec.ofNat 32 w)
    (hagree : ∀ p < hdr.lits_len.toNat, lp1.getD p 0#32 = lp.getD p 0#32)
    (hbits : ∀ j < (BitVec.ofNat 32 w).toNat,
      lp1.getD (res.toNat + j) 0#32 =
        if (BitVec.ofNat 32 a).toNat + j < (BitVec.ofNat 32 bw_n).toNat then
          lp.getD (bOff.toNat + ((BitVec.ofNat 32 a).toNat + j)) 0#32 else 0#32)
    (hnd : nodes.get? nodeIdx.toNat = some (.bv w (.extract a w eb)))
    (hm_so : (array (t := i32) hdr.slice_off_ptr (so.set (BitVec.setWidth 64 nodeIdx).toNat res) ⋆
      blastSoRest cfg hdr1 progPtr progBytes ab aw ht lp1 R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  have hw32 : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
  have ha32 : (BitVec.ofNat 32 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have hbw32 : (BitVec.ofNat 32 bw_n).toNat = bw_n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbw_lt]
  have hlc := bvWorkspaceOk_litsCap_eq hok; have hle_c := hinv.lits_le_cap
  refine oc_lits_bv_ok hoom0 hoom1 hni_lt hw_lt hok hfr1 hal1 hlp1 hinv (hw32 ▸ hroom)
    hret hlen1 hagree hnd (fun j hj => ?_) (fun assign => ?_) hm_so hQ
  · have hb1 := hbits j (by omega); rw [hbw32, ha32] at hb1; rw [hb1]
    split
    · next hlt => exact hb_wf _ hlt
    · simp; omega
  · exact sliceDenotes_extract_eval (by rw [hok.lits_len]; omega)
      (by rw [hlp1, hok.lits_len, hret]; omega) (hb_sd assign)
      fun j hj => by simpa only [hbw32, ha32] using hbits j (by omega)

private theorem oc_append_ok {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g : Aig}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp lp1 : List (BitVec 32)}
    {nodeIdx aOff bOff res : BitVec 32} {w lw_n rw_n : Nat}
    {ea : BVExpr lw_n} {eb : BVExpr rw_n} {hsum_eq : w = lw_n + rw_n}
    {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hoom1 : hdr1.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hw_lt : w < 4294967296) (hlw_lt : lw_n < 4294967296) (hrw_lt : rw_n < 4294967296)
    (hsum_w : lw_n + rw_n = w)
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) (hfr1 : hdr.BlastFrame hdr1)
    (hal1 : hdr1.aig_len = hdr.aig_len) (hlp1 : lp1.length = lp.length)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (ha_le : aOff.toNat + lw_n ≤ hdr.lits_len.toNat)
    (hb_le : bOff.toNat + rw_n ≤ hdr.lits_len.toNat)
    (ha_wf : SliceLitsWf g lp aOff.toNat lw_n) (hb_wf : SliceLitsWf g lp bOff.toNat rw_n)
    (ha_sd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g (atomAssign progBytes assign) (litsSlice lp aOff.toNat lw_n) (ea.eval assign))
    (hb_sd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g (atomAssign progBytes assign) (litsSlice lp bOff.toNat rw_n) (eb.eval assign))
    (hroom : (BitVec.ofNat 32 lw_n).toNat + (BitVec.ofNat 32 rw_n).toNat ≤
      hdr.lits_cap.toNat - hdr.lits_len.toNat)
    (hret : res = hdr.lits_len)
    (hlen1 : hdr1.lits_len = hdr.lits_len + (BitVec.ofNat 32 lw_n + BitVec.ofNat 32 rw_n))
    (hsum32 : (BitVec.ofNat 32 lw_n + BitVec.ofNat 32 rw_n).toNat =
      (BitVec.ofNat 32 lw_n).toNat + (BitVec.ofNat 32 rw_n).toNat)
    (hagree : ∀ p < hdr.lits_len.toNat, lp1.getD p 0#32 = lp.getD p 0#32)
    (hbitsR : ∀ j < (BitVec.ofNat 32 rw_n).toNat,
      lp1.getD (res.toNat + j) 0#32 = lp.getD (bOff.toNat + j) 0#32)
    (hbitsL : ∀ j < (BitVec.ofNat 32 lw_n).toNat,
      lp1.getD (res.toNat + (BitVec.ofNat 32 rw_n).toNat + j) 0#32 = lp.getD (aOff.toNat + j) 0#32)
    (hnd : nodes.get? nodeIdx.toNat = some (.bv w (.append ea eb hsum_eq)))
    (hm_so : (array (t := i32) hdr.slice_off_ptr (so.set (BitVec.setWidth 64 nodeIdx).toNat res) ⋆
      blastSoRest cfg hdr1 progPtr progBytes ab aw ht lp1 R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  have hw32 : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
  have hlw32 : (BitVec.ofNat 32 lw_n).toNat = lw_n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlw_lt]
  have hrw32 : (BitVec.ofNat 32 rw_n).toNat = rw_n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrw_lt]
  have hsum_bv : BitVec.ofNat 32 lw_n + BitVec.ofNat 32 rw_n = BitVec.ofNat 32 w := by
    apply BitVec.eq_of_toNat_eq; rw [hsum32, hlw32, hrw32, hw32, hsum_w]
  rw [hsum_bv] at hlen1; rw [hlw32, hrw32, hsum_w] at hroom
  have hlc := bvWorkspaceOk_litsCap_eq hok; have hle_c := hinv.lits_le_cap
  refine oc_lits_bv_ok hoom0 hoom1 hni_lt hw_lt hok hfr1 hal1 hlp1 hinv hroom hret hlen1 hagree
    hnd (fun j hj => ?_) (fun assign => ?_) hm_so hQ
  · by_cases hjr : j < rw_n
    · rw [hbitsR j (by omega)]; exact hb_wf j hjr
    · have h1 := hbitsL (j - rw_n) (by omega)
      rw [hrw32, show res.toNat + rw_n + (j - rw_n) = res.toNat + j by omega] at h1
      rw [h1]; exact ha_wf (j - rw_n) (by omega)
  · subst hsum_eq
    exact sliceDenotes_append_bits (by rw [hok.lits_len]; omega) (by rw [hok.lits_len]; omega)
      (by rw [hlp1, hok.lits_len, hret, hsum_w]; omega) (ha_sd assign) (hb_sd assign)
      (fun j hj => hbitsR j (by omega))
      (fun j hj => by simpa only [hrw32] using hbitsL j (by omega))

private theorem oc_getlsbd_ok {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g : Aig}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp : List (BitVec 32)}
    {nodeIdx aOff res : BitVec 32} {ew b : Nat} {ea : BVExpr ew}
    {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hoom1 : hdr1.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hew_lt : ew < 4294967296) (hb_lt : b < 4294967296)
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) (hok1 : BVWorkspaceOk cfg hdr1 ab so aw ht lp)
    (haig1 : AigInv hdr1 g aw ht) (hfr1 : hdr.AigFrame hdr1)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (ha_le : aOff.toNat + ew ≤ hdr.lits_len.toNat) (ha_wf : SliceLitsWf g lp aOff.toNat ew)
    (ha_sd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g (atomAssign progBytes assign) (litsSlice lp aOff.toNat ew) (ea.eval assign))
    (hres_eq : res = if BitVec.ofNat 32 b < BitVec.ofNat 32 ew then
      lp.getD (aOff.toNat + (BitVec.ofNat 32 b).toNat) 0#32 else 0#32)
    (hnd : nodes.get? nodeIdx.toNat = some (.bool (.literal (.getLsbD ea b))))
    (hm_so : (array (t := i32) hdr.slice_off_ptr (so.set (BitVec.setWidth 64 nodeIdx).toNat res) ⋆
      blastSoRest cfg hdr1 progPtr progBytes ab aw ht lp R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  have hew32 : (BitVec.ofNat 32 ew).toNat = ew := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hew_lt]
  have hb32 : (BitVec.ofNat 32 b).toNat = b := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt]
  have hlt_iff : (BitVec.ofNat 32 b < BitVec.ofNat 32 ew) ↔ b < ew := by
    rw [BitVec.lt_def, hb32, hew32]
  have hres_n : res = if b < ew then lp.getD (aOff.toNat + b) 0#32 else 0#32 := by
    rw [hres_eq, hb32]; by_cases h : b < ew
    · rw [ite_eq_left (hlt_iff.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hlt_iff.mp h')), ite_eq_right h]
  refine drv_sub_bool_ok hoom0 hoom1 hni_lt hok hok1 haig1 (Aig.extends_rfl g) hinv
    (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node hfr1.lits_len hnd ?_
    (fun assign => ?_) hm_so hQ
  · rw [hres_n]; split
    · next hlt => exact ha_wf b hlt
    · simp; omega
  · rw [hres_n]
    exact sliceDenotes_getLsbD
      (by rw [hok.lits_len]; have := hinv.lits_le_cap; omega) (ha_sd assign)

local macro "oc_bitwise_branch" hOp:ident bitLem:ident hok:ident hinv:ident hoom0:ident hni_lt:ident
    hw_lt:ident hw32:ident ha_lt:ident ha_lt_ni:ident hb_lt:ident hb_lt_ni:ident hga:ident hgb:ident
    hnd:ident haig:ident hcap_le:ident hm:ident hQ:ident : tactic => `(tactic| (
  obtain ⟨ha_so, _, ha_le, ha_wf, _, _, ha_sd⟩ :=
    drv_child_bv_prep $ha_lt $ha_lt_ni $hoom0 $hinv $hni_lt $hga
  obtain ⟨hb_so, _, hb_le, hb_wf, _, _, hb_sd⟩ :=
    drv_child_bv_prep $hb_lt $hb_lt_ni $hoom0 $hinv $hni_lt $hgb
  have hm_so := blast_so_focus ($hok).hdr_so $hm; clear $hm; c0_hstraight
  have hm_f := blast_full_focus ($hok).hdr_aig ($hok).hdr_ht ($hok).hdr_lits
    (blast_so_unfocus ($hok).hdr_so hm_so); clear hm_so
  c0_call $hOp; refine ⟨_, _, _, _, _, _, $haig, $hcap_le,
    fun _ _ _ => ⟨by have h := $hw32; rw [h]; exact ha_wf,
                  by have h := $hw32; rw [h]; exact hb_wf⟩, hm_f, ?_⟩
  intro res hdr1 g1 aw1 ht1 lp1 m1 hfr1 hext1 _ haig1 hlp1 hpres1 _ _ _ _ hok_res _ hm1
  have hok1 := bvWorkspaceOk_of_ocBlastFrame $hok hfr1 haig1 hlp1
  have hm1_b := blast_full_unfocus hok1.hdr_aig hok1.hdr_ht hok1.hdr_lits hm1; clear hm1
  have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr; c0_hsplit
  · c0_hstraight
    exact oc_aig_oom hok1 haig1 hext1 hfr1.prog_ptr hfr1.n_cwords hfr1.root_node $hinv hm1_b $hQ
  · have hoom1 : hdr1.oom = 0#32 := by assumption
    obtain ⟨_, _, _, hroom, hret, hlen1, hwf1, hbits⟩ := hok_res hoom1
    have hm1_so := blast_so_focus hok1.hdr_so hm1_b; clear hm1_b
    rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
    exact oc_bitwise_ok $hoom0 hoom1 $hni_lt $hw_lt $hok hok1 haig1 hfr1 hext1 hlp1 $hinv
      ha_le hb_le ha_sd hb_sd hroom hret hlen1 hpres1 hwf1 hbits $hnd
      (fun _ _ _ => by simp only [BVExpr.eval, BVBinOp.eval]; exact $bitLem) (by assumption) $hQ))

private theorem u32At_ofNat_toNat (bs : List UInt8) (i : Nat) :
    (BitVec.ofNat 32 (u32At bs i)).toNat = u32At bs i := by
  have h := u32At_lt bs i; unfold u32Bound at h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

local macro "oc_cmp_branch" hOp:ident hRead:ident hok:ident hinv:ident hoom0:ident hni_lt:ident
    hfit:ident hm_bytes:ident ha_lt:ident ha_lt_ni:ident hb_lt:ident hb_lt_ni:ident
    hga:ident hgb:ident hnd:ident haig:ident hlen_le_lp:ident hm:ident hQ:ident
    isUlt:ident : tactic => `(tactic| (
  obtain ⟨hew_idx, hew_fit⟩ := drv0_node_width_read $hinv $hok $ha_lt $ha_lt_ni $hni_lt
  c0_hstraight; rw [($hinv).prog_ptr_eq]; c0_call $hRead
  refine ⟨_, _, $hfit, hew_fit, $hm_bytes, ?_⟩; rw [hew_idx]
  obtain ⟨ha_so, _, ha_le, ha_wf, _, _, ha_sd⟩ :=
    drv_child_bv_prep $ha_lt $ha_lt_ni $hoom0 $hinv $hni_lt $hga
  obtain ⟨hb_so, _, hb_le, hb_wf, _, _, hb_sd⟩ :=
    drv_child_bv_prep $hb_lt $hb_lt_ni $hoom0 $hinv $hni_lt $hgb
  have hm_so := blast_so_focus ($hok).hdr_so $hm; clear $hm; c0_hstraight
  have hm_f := blast_full_focus ($hok).hdr_aig ($hok).hdr_ht ($hok).hdr_lits
    (blast_so_unfocus ($hok).hdr_so hm_so); clear hm_so
  c0_call $hOp; refine ⟨_, _, _, _, _, _, $haig, $hlen_le_lp,
    fun _ _ _ => ⟨by rw [u32At_ofNat_toNat]; exact ha_wf,
                  by rw [u32At_ofNat_toNat]; exact hb_wf⟩,
    hm_f, ?_⟩
  intro res hdr1 g1 aw1 ht1 m1 hfr1 hext1 _ haig1 _ _ hok_res _ hm1
  have hok1 := bvWorkspaceOk_of_aigFrame $hok hfr1 haig1
  have hm1_b := blast_full_unfocus hok1.hdr_aig hok1.hdr_ht hok1.hdr_lits hm1; clear hm1
  have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr; c0_hsplit
  · c0_hstraight
    exact oc_aig_oom hok1 haig1 hext1 hfr1.prog_ptr hfr1.n_cwords hfr1.root_node $hinv hm1_b $hQ
  · have hoom1 : hdr1.oom = 0#32 := by assumption
    obtain ⟨_, _, _, hbd1, hev1⟩ := hok_res hoom1
    have hm1_so := blast_so_focus hok1.hdr_so hm1_b; clear hm1_b
    rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
    have hle_c := ($hinv).lits_le_cap
    refine drv_sub_bool_ok $hoom0 hoom1 $hni_lt $hok hok1 haig1 hext1 $hinv
      (hfr1.prog_ptr.trans ($hinv).prog_ptr_eq) hfr1.n_cwords hfr1.root_node
      hfr1.lits_len $hnd (by rw [← haig1.aig_len_eq]; exact hbd1) (fun assign => ?_)
      (by assumption) $hQ
    exact $isUlt (u32At_ofNat_toNat ..)
      ha_le hb_le ha_sd hb_sd hev1 ($hok).lits_len hle_c assign))

private theorem oc_eq_eval {cfg : BVWorkspaceCfg} {progBytes : List UInt8}
    {hdr : BVHdrState} {g g1 : Aig} {lp : List (BitVec 32)} {ew : Nat}
    {aOff bOff res : BitVec 32} {ea eb : BVExpr ew}
    (hew32 : (BitVec.ofNat 32 ew).toNat = ew)
    (ha_le : aOff.toNat + ew ≤ hdr.lits_len.toNat) (hb_le : bOff.toNat + ew ≤ hdr.lits_len.toNat)
    (ha_sd : ∀ a, SliceDenotes g (atomAssign progBytes a)
      (litsSlice lp aOff.toNat ew) (ea.eval a))
    (hb_sd : ∀ a, SliceDenotes g (atomAssign progBytes a)
      (litsSlice lp bOff.toNat ew) (eb.eval a))
    (hev1 : ∀ ρ, g1.evalLit ρ (UInt32.ofBitVec res) = decide (∀ j < (BitVec.ofNat 32 ew).toNat,
      g.evalLit ρ (UInt32.ofBitVec (lp.getD (aOff.toNat + j) 0#32)) =
      g.evalLit ρ (UInt32.ofBitVec (lp.getD (bOff.toNat + j) 0#32))))
    (hl : lp.length = cfg.lits_cap) (hlc : hdr.lits_len.toNat ≤ cfg.lits_cap)
    (assign : BVExpr.Assignment) :
    g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec res) =
      (BVLogicalExpr.literal (.bin ea .eq eb)).eval assign :=
  evalLit_eq_of_slices (by rw [hl]; omega) (by rw [hl]; omega) (ha_sd assign) (hb_sd assign)
    (by simpa only [hew32] using hev1 (atomAssign progBytes assign))

private theorem oc_ult_eval {cfg : BVWorkspaceCfg} {progBytes : List UInt8}
    {hdr : BVHdrState} {g g1 : Aig} {lp : List (BitVec 32)} {ew : Nat}
    {aOff bOff res : BitVec 32} {ea eb : BVExpr ew}
    (hew32 : (BitVec.ofNat 32 ew).toNat = ew)
    (_ : aOff.toNat + ew ≤ hdr.lits_len.toNat) (_ : bOff.toNat + ew ≤ hdr.lits_len.toNat)
    (ha_sd : ∀ a, SliceDenotes g (atomAssign progBytes a)
      (litsSlice lp aOff.toNat ew) (ea.eval a))
    (hb_sd : ∀ a, SliceDenotes g (atomAssign progBytes a)
      (litsSlice lp bOff.toNat ew) (eb.eval a))
    (hev1 : ∀ ρ (va vb : BitVec (BitVec.ofNat 32 ew).toNat),
      SliceDenotes g ρ (litsSlice lp aOff.toNat (BitVec.ofNat 32 ew).toNat) va →
      SliceDenotes g ρ (litsSlice lp bOff.toNat (BitVec.ofNat 32 ew).toNat) vb →
      g1.evalLit ρ (UInt32.ofBitVec res) = BitVec.ult va vb)
    (_ : lp.length = cfg.lits_cap) (_ : hdr.lits_len.toNat ≤ cfg.lits_cap)
    (assign : BVExpr.Assignment) :
    g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec res) =
      (BVLogicalExpr.literal (.bin ea .ult eb)).eval assign := by
  have h := hev1 (atomAssign progBytes assign) _ _
    (sliceDenotes_cast hew32.symm (ha_sd assign))
    (sliceDenotes_cast hew32.symm (hb_sd assign))
  rw [bv_ult_cast] at h; exact h

/-! ## 2. `bv_eval_ops_core_wp` -/

public section

theorem bv_eval_ops_core_wp (Γ : Env)
    (hRead : ∀ xs m Q X, bvReadU32Spec xs m Q X → Γ "bv_read_u32" [i64, i64] [i32] xs m Q X)
    (hLitsAlloc : ∀ xs m Q X, bvLitsAllocSpec xs m Q X →
      Γ "bv_lits_alloc" [i64, i32] [i32] xs m Q X)
    (hExtract : ∀ xs m Q X, bvBlastExtractSpec xs m Q X →
      Γ "bv_blast_extract" [i64, i32, i32, i32, i32] [i32] xs m Q X)
    (hAnd : ∀ xs m Q X, bvBlastAndSpec xs m Q X →
      Γ "bv_blast_and" [i64, i32, i32, i32] [i32] xs m Q X)
    (hOr : ∀ xs m Q X, bvBlastOrSpec xs m Q X →
      Γ "bv_blast_or" [i64, i32, i32, i32] [i32] xs m Q X)
    (hXor : ∀ xs m Q X, bvBlastXorSpec xs m Q X →
      Γ "bv_blast_xor" [i64, i32, i32, i32] [i32] xs m Q X)
    (hAdd : ∀ xs m Q X, bvBlastAddSpec xs m Q X →
      Γ "bv_blast_add" [i64, i32, i32, i32] [i32] xs m Q X)
    (hNot : ∀ xs m Q X, bvBlastNotSpec xs m Q X →
      Γ "bv_blast_not" [i64, i32, i32] [i32] xs m Q X)
    (hAppend : ∀ xs m Q X, bvBlastAppendSpec xs m Q X →
      Γ "bv_blast_append" [i64, i32, i32, i32, i32] [i32] xs m Q X)
    (hEq : ∀ xs m Q X, bvBlastEqSpec xs m Q X →
      Γ "bv_blast_eq" [i64, i32, i32, i32] [i32] xs m Q X)
    (hUlt : ∀ xs m Q X, bvBlastUltSpec xs m Q X →
      Γ "bv_blast_ult" [i64, i32, i32, i32] [i32] xs m Q X)
    (hGetLsbD : ∀ xs m Q X, bvBlastGetLsbDSpec xs m Q X →
      Γ "bv_blast_get_lsb_d" [i64, i32, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvEvalSubSpec xs m Q X → Func.wp Γ bv_eval_ops_core_body xs m Q X := by
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
  have hm_hdr := blast_hdr_left hm
  have hfit' : hdr.prog_ptr.toNat + progBytes.length < 2 ^ 64 := hinv.prog_ptr_eq ▸ hfit
  have hm_bytes' : (bytes hdr.prog_ptr progBytes ⋆
      (bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R)) m :=
    hinv.prog_ptr_eq ▸ sep_ac hm
  c0_hstraight; c0_call hRead; refine ⟨progBytes, _, hfit', hnw0.2, hm_bytes', ?_⟩
  c0_hstraight; c0_call hRead; refine ⟨progBytes, _, hfit', hnw1.2, hm_bytes', ?_⟩
  c0_hstraight; c0_call hRead; refine ⟨progBytes, _, hfit', hnw2.2, hm_bytes', ?_⟩
  c0_hstraight; c0_call hRead; refine ⟨progBytes, _, hfit', hnw3.2, hm_bytes', ?_⟩
  c0_hstraight; rw [hnw0.1, hnw1.1, hnw2.1, hnw3.1]; clear hnw0 hnw1 hnw2 hnw3
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
  have hcap_le : hdr.lits_cap.toNat ≤ litsPool.length :=
    Nat.le_of_eq (bvWorkspaceOk_litsPool_eq_cap hok).symm
  have hlen_le_lp : hdr.lits_len.toNat ≤ litsPool.length := by
    rw [hok.lits_len]; exact hinv.lits_le_cap
  have hw32 : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
  have ha32_nat : (BitVec.ofNat 32 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have hni_so : (BitVec.setWidth 64 nodeIdx).toNat < sliceOffs.length := by
    rw [bv32_setWidth64_toNat, hok.so_len]; exact hni_lt
  have hm_bytes : (bytes progPtr progBytes ⋆
      (bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R)) m := sep_ac hm
  c0_hsplit
  · -- Case 1: BV_OP_VAR (0)
    have hop0 : op = opVar := by unfold opVar; c0_bv_omega [hop_lt]
    clear hc; have hvar := parsed_node_var hp hn_lt
      (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop0)
    dsimp only at hvar; rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hw_eq] at hvar
    rcases hvar with ⟨ha_nv, hw_var, hnd_var⟩
    c0_call hLitsAlloc; refine ⟨hdr, _, hm_hdr, ?_⟩
    by_cases hfit_lits : w ≤ cfg.lits_cap - hdr.lits_len.toNat
    · have ⟨hc_cond, hlits1_len⟩ :=
        drv0_lits_alloc_cond_ok hok hoom0 hinv.lits_le_cap hw_lt hfit_lits
      rw [ite_eq_left hc_cond]; intro m1 hm1
      let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + BitVec.ofNat 32 w }
      have hok1 := bvWorkspaceOk_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) hok
      have hm1_blast : (bytes progPtr progBytes ⋆
          bvBlastMem cfg hdr1 atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m1 := by
        dsimp only [hdr1]; rw [bvBlastMem_hdr_left]; exact sep_ac hm1
      c0_hstraight; c0_hsplit
      · exfalso; exact hc hoom0
      · clear hc; have hm1_ab := blast_ab_focus hok1.hdr_ab hm1_blast
        have ha32 : (BitVec.setWidth 64 (BitVec.ofNat 32 a)).toNat < atomBases.length := by
          rw [bv32_setWidth64_toNat, ha32_nat, hok1.ab_len]; exact ha_nv
        c0_hstraight; have hab_eq := hinv.atom_bases_eq a ha_nv
        have hcnt_a1 := countAtoms_mono_ne_zero (by omega : a + 1 ≤ cfg.n_vars)
          (hinv.nv_eq ▸ hinv.parsed.valid.atoms_ok)
        have hcnt_prev := countAtoms_prev_ne_zero hcnt_a1.1
        have hcnt_lt : countAtoms progBytes cfg.n_vars < bvDimacsBound :=
          hinv.nv_eq ▸ countAtoms_lt progBytes (u32At progBytes 2)
        have ha_idx_get : atomBases[(BitVec.setWidth 64 (BitVec.ofNat 32 a)).toNat]'ha32 =
            atomBases.getD a 0#32 := by
          rw [list_getD_eq_getElem, bv32_setWidth64_toNat, ha32_nat]
        refine wp_while_state (α := Nat × List (BitVec 32))
          (fun s => (BitVec.ofNat 32 s.1, ())) (fun s => w - s.1)
          (drv0VarInv cfg progPtr progBytes hdr hdr1 atomBases sliceOffs
            aigWords htSlots litsPool R w a) ?_ ?_
        · intro J hJ; c0_hsteps
          exact hJ (0, litsPool) m1 ⟨Nat.zero_le w, hok.lits_len, fun _ _ => rfl,
            fun _ hp => by omega, hm1_blast⟩
        · intro J ⟨j, lp⟩ ml ⟨hj_le, hlp_len, hagree, hset, hml⟩ ih
          c0_hstraight; c0_hsplit
          · have hj_lt := drv0_loop_lt hj_le hw_lt hc; clear hc
            obtain ⟨_, _, hj_eq32, hagree', hset'⟩ := drv0_var_step ha32 ha_idx_get hab_eq
              hinv.lits_le_cap hok.lcap_lt hfit_lits hj_lt hw_lt hlp_len hcnt_a1.2 hw_var
              hcnt_prev.2.2.symm hcnt_lt hagree hset rfl
            have hml_lits := blast_lits_focus hok1.hdr_lits hml; clear hml
            c0_hstraight; rw [hj_eq32]
            exact ih (j + 1, _) _ (by omega) ⟨by omega, by simp [hlp_len], hagree', hset',
              blast_lits_unfocus hok1.hdr_lits (by assumption)⟩
          · have hj_eq := drv0_loop_eq hj_le hw_lt hc; clear hc
            have hml_so := blast_so_focus hok1.hdr_so hml; clear hml; c0_hstraight
            exact drv0_var_post hoom0 hni_lt hok haig hinv hfit_lits ha_nv hw_var hnd_var rfl
              hlits1_len hlp_len hagree (hj_eq ▸ hset)
              (blast_so_unfocus hok1.hdr_so (by rw [← bv32_setWidth64_toNat nodeIdx]; assumption))
              hQ
    · rw [ite_eq_right (drv0_lits_alloc_oom_cond hok hw_lt hfit_lits)]; dsimp only
      rw [ite_eq_right (fun h => absurd hoom0 h)]; intro m1 hm1; c0_hstraight; c0_hsplit
      · clear hc; c0_hstraight; exact oc_var_const_oom hok haig hinv hm1 hQ
      · exfalso; cases hc
  · clear hc; c0_hstraight; c0_hsplit
    · -- Case 2: BV_OP_CONST (1)
      have hop1 : op = opConst := by unfold opConst; c0_bv_omega [hop_lt]
      clear hc; have hconst := parsed_node_const hp hn_lt
        (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop1)
      dsimp only at hconst; rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hw_eq] at hconst
      rcases hconst with ⟨hcw_bd, val, _, hconst_bits, hnd_const⟩
      c0_call hLitsAlloc; refine ⟨hdr, _, hm_hdr, ?_⟩
      by_cases hfit_lits : w ≤ cfg.lits_cap - hdr.lits_len.toNat
      · have ⟨hc_cond, hlits1_len⟩ :=
          drv0_lits_alloc_cond_ok hok hoom0 hinv.lits_le_cap hw_lt hfit_lits
        rw [ite_eq_left hc_cond]; intro m1 hm1
        let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + BitVec.ofNat 32 w }
        have hok1 := bvWorkspaceOk_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) hok
        have hm1_blast : (bytes progPtr progBytes ⋆
            bvBlastMem cfg hdr1 atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m1 := by
          dsimp only [hdr1]; rw [bvBlastMem_hdr_left]; exact sep_ac hm1
        c0_hstraight; c0_hsplit
        · exfalso; exact hc hoom0
        · clear hc; c0_hstraight
          refine wp_while_state (α := Nat × BitVec 32 × List (BitVec 32))
            (fun s => (s.2.1, BitVec.ofNat 32 s.1, ())) (fun s => w - s.1)
            (drv0ConstInv cfg progPtr progBytes hdr hdr1 atomBases sliceOffs
              aigWords htSlots litsPool R w a) ?_ ?_
          · intro J hJ; c0_hsteps
            exact hJ (0, 0#32, litsPool) m1 ⟨Nat.zero_le w, fun h => by omega, hok.lits_len,
              fun _ _ => rfl, fun _ hp => by omega, hm1_blast⟩
          · intro J ⟨j, cw, lp⟩ ml ⟨hj_le, hcw_ok, hlp_len, hagree, hset, hml⟩ ih
            c0_hstraight; c0_hsplit
            · have hj_lt := drv0_loop_lt hj_le hw_lt hc; clear hc
              have hj32 : j < 2 ^ 32 := Nat.lt_trans hj_lt hw_lt; c0_hstraight
              refine wp_join_state1 (α := BitVec 32) (fun cw' => cw')
                (fun cw' ml' =>
                  cw'.toNat = u32At progBytes (cwordsOff cfg.n_vars + a + j / 32) ∧
                  (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 atomBases sliceOffs aigWords
                    htSlots lp ⋆ R) ml') ?_ ?_
              · intro J2 cw' ml' ⟨hcw'_eq, hml'⟩
                obtain ⟨_, _, hj_eq32, hcw_next, hagree', hset'⟩ := drv0_const_step_set
                  hok hinv.lits_le_cap hfit_lits hj_lt hw_lt hlp_len hcw'_eq hagree hset
                have hml_lits := blast_lits_focus hok1.hdr_lits hml'; clear hml'
                c0_hstraight; rw [hj_eq32]
                exact ih (j + 1, cw', _) _ (by omega) ⟨by omega, hcw_next, by simp [hlp_len],
                  hagree', hset', blast_lits_unfocus hok1.hdr_lits (by assumption)⟩
              · intro J2 hJ2; c0_hstraight; c0_hsplit
                · clear hc; have hml_hdr := blast_hdr_left hml; c0_hstraight; clear hml_hdr
                  obtain ⟨hcwi_eq, hcwi_fit⟩ := drv0_const_read_idx hinv hok ha_lt hj_lt hw_lt
                    (fun hp => by rw [← hinv.nc_eq]; have := hcw_bd hp; omega)
                  rw [hinv.prog_ptr_eq]; c0_call hRead
                  refine ⟨progBytes,
                    bvBlastMem cfg hdr1 atomBases sliceOffs aigWords htSlots lp ⋆ R,
                    hfit, hcwi_fit, sep_ac hml, ?_⟩
                  rw [hcwi_eq]; c0_hstraight
                  exact hJ2 _ ml ⟨by
                    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (u32At_lt ..), hml⟩
                · have hj_mod : j % 32 ≠ 0 := by
                    intro h0; apply hc; apply BitVec.eq_of_toNat_eq
                    change (BitVec.ofNat 32 j &&& 31#32).toNat = (0#32 : BitVec 32).toNat
                    rw [bv32_and31_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32, h0]; rfl
                  clear hc; have hj_pos : 0 < j := by omega
                  have hcw_eq : cw.toNat = u32At progBytes (cwordsOff cfg.n_vars + a + j / 32) := by
                    rw [← show (j - 1) / 32 = j / 32 by omega]; exact hcw_ok hj_pos
                  c0_hstraight; exact hJ2 cw ml ⟨hcw_eq, hml⟩
            · have hj_eq := drv0_loop_eq hj_le hw_lt hc; clear hc
              have hml_so := blast_so_focus hok1.hdr_so hml; clear hml; c0_hstraight
              exact drv0_const_post hoom0 hni_lt hok haig hinv hfit_lits hconst_bits hnd_const rfl
                hlits1_len hlp_len hagree (hj_eq ▸ hset)
                (blast_so_unfocus hok1.hdr_so (by rw [← bv32_setWidth64_toNat nodeIdx]; assumption))
                hQ
      · rw [ite_eq_right (drv0_lits_alloc_oom_cond hok hw_lt hfit_lits)]; dsimp only
        rw [ite_eq_right (fun h => absurd hoom0 h)]; intro m1 hm1; c0_hstraight; c0_hsplit
        · clear hc; c0_hstraight; exact oc_var_const_oom hok haig hinv hm1 hQ
        · exfalso; cases hc
    · clear hc; c0_hstraight; c0_hsplit
      · -- Case 3: BV_OP_EXTRACT (2)
        have hop2 : op = opExtract := by unfold opExtract; c0_bv_omega [hop_lt]
        clear hc; have hext := parsed_node_extract hp hn_lt
          (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop2)
        dsimp only at hext; rw [← hinv.nv_eq, ← hinv.nc_eq, hw_eq, ha_eq, hb_eq] at hext
        rcases hext with ⟨hb_lt_ni, _, eb, hgb, hnd⟩
        obtain ⟨hbw_idx, hbw_fit⟩ := drv0_node_width_read hinv hok hb_lt hb_lt_ni hni_lt
        c0_hstraight; rw [hinv.prog_ptr_eq]; c0_call hRead
        refine ⟨progBytes, _, hfit, hbw_fit, hm_bytes, ?_⟩; rw [hbw_idx]
        obtain ⟨hb_so, _, hb_le, _, hb_wf, _, hb_sd⟩ :=
          drv_child_bv_prep hb_lt hb_lt_ni hoom0 hinv hni_lt hgb
        have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
        have hm_hl := blast_hdr_lits_focus hok.hdr_lits
          (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
        c0_call hExtract; refine ⟨hdr, litsPool, _, hm_hl, hcap_le, ?_⟩
        intro res hdr1 lp1 m1 hfr1 hal1 hlp1 hpres1 _ _ hok_res _ hm1
        have hm1_b := blast_hdr_lits_unfocus (hfr1.lits_ptr.trans hok.hdr_lits) hm1; clear hm1
        have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr; c0_hsplit
        · c0_hstraight; exact oc_lits_oom hok hfr1 hal1 hlp1 hinv hm1_b hQ
        · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
          obtain ⟨_, _, hroom, hret, hlen1, hbits⟩ := hok_res hoom1
          have hm1_so := blast_so_focus (hfr1.slice_off_ptr.trans hok.hdr_so) hm1_b; clear hm1_b
          rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
          exact oc_extract_ok hoom0 hoom1 hni_lt hw_lt ha_lt (u32At_lt ..) hok hfr1 hal1 hlp1 hinv
            hb_le hb_wf hb_sd hroom hret hlen1 hpres1 hbits hnd (by assumption) hQ
      · clear hc; c0_hstraight; c0_hsplit
        · -- Case 4: BV_OP_AND (3)
          have hop3 : op = opAnd := by unfold opAnd; c0_bv_omega [hop_lt]
          clear hc; have hbin := parsed_node_binop hp hn_lt
            (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop3]; unfold opAnd; decide)
            (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop3]; unfold opAnd opUmod; decide)
          dsimp only at hbin; rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hbin
          rcases hbin with ⟨ha_lt_ni, hb_lt_ni, bop, ea, eb, hbop, _, _, _, _, _, _, hga, hgb, hnd⟩
          rw [hbop hop3] at hnd
          oc_bitwise_branch hAnd BitVec.getLsbD_and hok hinv hoom0 hni_lt hw_lt hw32
            ha_lt ha_lt_ni hb_lt hb_lt_ni hga hgb hnd haig hcap_le hm hQ
        · clear hc; c0_hstraight; c0_hsplit
          · -- Case 5: BV_OP_OR (4)
            have hop4 : op = opOr := by unfold opOr; c0_bv_omega [hop_lt]
            clear hc; have hbin := parsed_node_binop hp hn_lt
              (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop4]; unfold opOr; decide)
              (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop4]; unfold opOr opUmod; decide)
            dsimp only at hbin
            rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hbin
            rcases hbin with
              ⟨ha_lt_ni, hb_lt_ni, bop, ea, eb, _, hbop, _, _, _, _, _, hga, hgb, hnd⟩
            rw [hbop hop4] at hnd
            oc_bitwise_branch hOr BitVec.getLsbD_or hok hinv hoom0 hni_lt hw_lt hw32
              ha_lt ha_lt_ni hb_lt hb_lt_ni hga hgb hnd haig hcap_le hm hQ
          · clear hc; c0_hstraight; c0_hsplit
            · -- Case 6: BV_OP_XOR (5)
              have hop5 : op = opXor := by unfold opXor; c0_bv_omega [hop_lt]
              clear hc; have hbin := parsed_node_binop hp hn_lt
                (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop5]; unfold opXor; decide)
                (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop5]; unfold opXor opUmod; decide)
              dsimp only at hbin
              rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hbin
              rcases hbin with
                ⟨ha_lt_ni, hb_lt_ni, bop, ea, eb, _, _, hbop, _, _, _, _, hga, hgb, hnd⟩
              rw [hbop hop5] at hnd
              oc_bitwise_branch hXor BitVec.getLsbD_xor hok hinv hoom0 hni_lt hw_lt hw32
                ha_lt ha_lt_ni hb_lt hb_lt_ni hga hgb hnd haig hcap_le hm hQ
            · clear hc; c0_hstraight; c0_hsplit
              · -- Case 7: BV_OP_ADD (6)
                have hop6 : op = opAdd := by unfold opAdd; c0_bv_omega [hop_lt]
                clear hc; have hbin := parsed_node_binop hp hn_lt
                  (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop6]; unfold opAdd; decide)
                  (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop6]; unfold opAdd opUmod; decide)
                dsimp only at hbin
                rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hbin
                rcases hbin with
                  ⟨ha_lt_ni, hb_lt_ni, bop, ea, eb, _, _, _, hbop, _, _, _, hga, hgb, hnd⟩
                rw [hbop hop6] at hnd
                obtain ⟨ha_so, _, _, ha_wf, _, _, ha_sd⟩ :=
                  drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
                obtain ⟨hb_so, _, _, hb_wf, _, _, hb_sd⟩ :=
                  drv_child_bv_prep hb_lt hb_lt_ni hoom0 hinv hni_lt hgb
                have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
                have hm_f := blast_full_focus hok.hdr_aig hok.hdr_ht hok.hdr_lits
                  (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
                c0_call hAdd; refine ⟨hdr, g, aigWords, htSlots, litsPool, _, haig, hcap_le,
                  fun _ _ _ => ⟨by rw [hw32]; exact ha_wf, by rw [hw32]; exact hb_wf⟩, hm_f, ?_⟩
                intro res hdr1 g1 aw1 ht1 lp1 m1 hfr1 hext1 _ haig1 hlp1 hpres1 _ _ _ _ _ hok_res
                  _ hm1
                have hok1 := bvWorkspaceOk_of_ocBlastFrame hok hfr1 haig1 hlp1
                have hm1_b := blast_full_unfocus hok1.hdr_aig hok1.hdr_ht hok1.hdr_lits hm1
                clear hm1; have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr
                c0_hsplit
                · c0_hstraight
                  exact oc_aig_oom hok1 haig1 hext1 hfr1.prog_ptr hfr1.n_cwords hfr1.root_node hinv
                    hm1_b hQ
                · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
                  obtain ⟨_, _, _, hroom, hret, hlen1, hwf1, hadd_sd⟩ := hok_res hoom1
                  have hm1_so := blast_so_focus hok1.hdr_so hm1_b; clear hm1_b
                  rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
                  refine oc_aig_bv_ok hoom0 hoom1 hni_lt hw_lt hok hok1 haig1 hfr1 hext1 hinv
                    (hw32 ▸ hroom) hret hlen1 hpres1 hwf1 hnd (fun assign => ?_) (by assumption) hQ
                  have h := hadd_sd (atomAssign progBytes assign) _ _
                    (sliceDenotes_cast hw32.symm (ha_sd assign))
                    (sliceDenotes_cast hw32.symm (hb_sd assign))
                  rw [bv_add_cast] at h; simpa [BitVec.cast_cast] using sliceDenotes_cast hw32 h
              · clear hc; c0_hstraight; c0_hsplit
                · -- Case 8: BV_OP_NOT (10)
                  have hop10 : op = opNot := by unfold opNot; c0_bv_omega [hop_lt]
                  clear hc; have hnot := parsed_node_not hp hn_lt
                    (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop10)
                  dsimp only at hnot; rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hw_eq] at hnot
                  rcases hnot with ⟨ha_lt_ni, _, _, ea, hga, hnd⟩
                  obtain ⟨ha_so, _, ha_le, _, ha_wf, _, ha_sd⟩ :=
                    drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
                  have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
                  have hm_hl := blast_hdr_lits_focus hok.hdr_lits
                    (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
                  c0_call hNot; refine ⟨hdr, litsPool, _, hm_hl, hcap_le, ?_⟩
                  intro res hdr1 lp1 m1 hfr1 hal1 hlp1 hpres1 _ _ hok_res _ hm1
                  have hm1_b := blast_hdr_lits_unfocus (hfr1.lits_ptr.trans hok.hdr_lits) hm1
                  clear hm1; have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr
                  c0_hsplit
                  · c0_hstraight; exact oc_lits_oom hok hfr1 hal1 hlp1 hinv hm1_b hQ
                  · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
                    obtain ⟨_, _, hroom, hret, hlen1, hbits⟩ := hok_res hoom1
                    have hm1_so := blast_so_focus (hfr1.slice_off_ptr.trans hok.hdr_so) hm1_b
                    clear hm1_b; rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
                    have hlc := bvWorkspaceOk_litsCap_eq hok; have hle_c := hinv.lits_le_cap
                    exact oc_lits_bv_ok hoom0 hoom1 hni_lt hw_lt hok hfr1 hal1 hlp1 hinv
                      (hw32 ▸ hroom) hret hlen1 hpres1 hnd
                      (fun j hj => by rw [hbits j (by omega), bv32_xor1_lsr1]; exact ha_wf j hj)
                      (fun assign => sliceDenotes_not_bits (by rw [hok.lits_len]; omega)
                        (by rw [hlp1, hok.lits_len, hret]; omega) (ha_sd assign)
                        fun j hj => hbits j (by omega)) (by assumption) hQ
                · clear hc; c0_hstraight; c0_hsplit
                  · -- Case 9: BV_OP_APPEND (17)
                    have hop17 : op = opAppend := by unfold opAppend; c0_bv_omega [hop_lt]
                    clear hc; have happ := parsed_node_append hp hn_lt
                      (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop17)
                    dsimp only at happ
                    rw [← hinv.nv_eq, ← hinv.nc_eq, hw_eq, ha_eq, hb_eq] at happ
                    rcases happ with ⟨ha_lt_ni, hb_lt_ni, hsum_w, ea, eb, hsum_eq, hga, hgb, hnd⟩
                    obtain ⟨hlw_idx, hlw_fit⟩ := drv0_node_width_read hinv hok ha_lt ha_lt_ni hni_lt
                    obtain ⟨hrw_idx, hrw_fit⟩ := drv0_node_width_read hinv hok hb_lt hb_lt_ni hni_lt
                    c0_hstraight; rw [hinv.prog_ptr_eq]; c0_call hRead
                    refine ⟨progBytes, _, hfit, hlw_fit, hm_bytes, ?_⟩
                    c0_hstraight; rw [hinv.prog_ptr_eq]; c0_call hRead
                    refine ⟨progBytes, _, hfit, hrw_fit, hm_bytes, ?_⟩; rw [hlw_idx, hrw_idx]
                    obtain ⟨ha_so, _, ha_le, _, ha_wf, _, ha_sd⟩ :=
                      drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
                    obtain ⟨hb_so, _, hb_le, _, hb_wf, _, hb_sd⟩ :=
                      drv_child_bv_prep hb_lt hb_lt_ni hoom0 hinv hni_lt hgb
                    have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
                    have hm_hl := blast_hdr_lits_focus hok.hdr_lits
                      (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
                    c0_call hAppend; refine ⟨hdr, litsPool, _, hm_hl, hcap_le, ?_⟩
                    intro res hdr1 lp1 m1 hfr1 hal1 hlp1 hpres1 _ _ hok_res _ hm1
                    have hm1_b := blast_hdr_lits_unfocus (hfr1.lits_ptr.trans hok.hdr_lits) hm1
                    clear hm1; have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr
                    c0_hsplit
                    · c0_hstraight; exact oc_lits_oom hok hfr1 hal1 hlp1 hinv hm1_b hQ
                    · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
                      obtain ⟨_, _, _, hroom, hret, hlen1, hsum32, hbitsR, hbitsL⟩ := hok_res hoom1
                      have hm1_so := blast_so_focus (hfr1.slice_off_ptr.trans hok.hdr_so) hm1_b
                      clear hm1_b; rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
                      exact oc_append_ok hoom0 hoom1 hni_lt hw_lt (u32At_lt ..) (u32At_lt ..)
                        hsum_w hok hfr1 hal1 hlp1 hinv ha_le hb_le ha_wf hb_wf ha_sd hb_sd hroom
                        hret hlen1 hsum32 hpres1 hbitsR hbitsL hnd (by assumption) hQ
                  · clear hc; c0_hstraight; c0_hsplit
                    · -- Case 10: BV_OP_EQ (22)
                      have hop22 : op = opEq := by unfold opEq; c0_bv_omega [hop_lt]
                      clear hc; have heq := parsed_node_eq hp hn_lt
                        (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop22)
                      dsimp only at heq
                      rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hb_eq, hw_eq] at heq
                      rcases heq with ⟨_, ha_lt_ni, hb_lt_ni, _, _, _, ea, eb, hga, hgb, hnd⟩
                      oc_cmp_branch hEq hRead hok hinv hoom0 hni_lt hfit hm_bytes ha_lt ha_lt_ni
                        hb_lt hb_lt_ni hga hgb hnd haig hlen_le_lp hm hQ oc_eq_eval
                    · clear hc; c0_hstraight; c0_hsplit
                      · -- Case 11: BV_OP_ULT (23)
                        have hop23 : op = opUlt := by unfold opUlt; c0_bv_omega [hop_lt]
                        clear hc; have hult := parsed_node_ult hp hn_lt
                          (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop23)
                        dsimp only at hult
                        rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hb_eq, hw_eq] at hult
                        rcases hult with ⟨_, ha_lt_ni, hb_lt_ni, _, ea, eb, hga, hgb, hnd⟩
                        oc_cmp_branch hUlt hRead hok hinv hoom0 hni_lt hfit hm_bytes ha_lt ha_lt_ni
                          hb_lt hb_lt_ni hga hgb hnd haig hlen_le_lp hm hQ oc_ult_eval
                      · clear hc; c0_hstraight; c0_hsplit
                        · -- Case 12: BV_OP_GETLSBD (24)
                          have hop24 : op = opGetLsbD := by unfold opGetLsbD; c0_bv_omega [hop_lt]
                          clear hc; have hget := parsed_node_getlsbd hp hn_lt
                            (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop24)
                          dsimp only at hget
                          rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hb_eq, hw_eq] at hget
                          rcases hget with ⟨_, ha_lt_ni, _, ea, hga, hnd⟩
                          obtain ⟨hew_idx, hew_fit⟩ :=
                            drv0_node_width_read hinv hok ha_lt ha_lt_ni hni_lt
                          c0_hstraight; rw [hinv.prog_ptr_eq]; c0_call hRead
                          refine ⟨progBytes, _, hfit, hew_fit, hm_bytes, ?_⟩; rw [hew_idx]
                          obtain ⟨ha_so, _, ha_le, _, ha_wf, _, ha_sd⟩ :=
                            drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
                          have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
                          have hm_hl := blast_hdr_lits_focus hok.hdr_lits
                            (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
                          c0_call hGetLsbD; refine ⟨hdr, litsPool, _, hm_hl, hlen_le_lp, ?_⟩
                          intro res hdr1 m1 hfr1 hal1 _ _ hok_res _ hm1
                          have hm1_b :=
                            blast_hdr_lits_unfocus (hfr1.lits_ptr.trans hok.hdr_lits) hm1
                          clear hm1; have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight
                          clear hm1_hdr
                          have haig1 := aigInv_aigFrame haig hfr1 hal1
                          have hok1 := bvWorkspaceOk_of_aigFrame hok hfr1 haig1
                          c0_hsplit
                          · c0_hstraight
                            exact oc_aig_oom hok1 haig1 (Aig.extends_rfl g) hfr1.prog_ptr
                              hfr1.n_cwords hfr1.root_node hinv hm1_b hQ
                          · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
                            obtain ⟨_, _, hres_eq⟩ := hok_res hoom1
                            have hm1_so := blast_so_focus hok1.hdr_so hm1_b; clear hm1_b
                            rw [hfr1.slice_off_ptr] at hm1_so; c0_hstraight
                            exact oc_getlsbd_ok hoom0 hoom1 hni_lt (u32At_lt ..) hb_lt hok hok1
                              haig1 hfr1 hinv ha_le ha_wf ha_sd hres_eq hnd (by assumption) hQ
                        · clear hc; c0_hstraight
                          exact hQ false hdr g sliceOffs aigWords htSlots litsPool m hok haig
                            (Aig.extends_rfl g) hinv.prog_ptr_eq rfl rfl
                            (fun hf => absurd hf Bool.false_ne_true) hm

end

end LeanQbe.T.Examples.Bitblast.Proof
