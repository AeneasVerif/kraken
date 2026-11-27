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
# Division & Popcount Evaluator Dispatcher WP Proof (`Bitblast.Proof.DriverDivCpop`)

Proves `Γ`-parametric `Func.wp` soundness for `bv_eval_ops_div_cpop` (`BV_OP_UDIV`,
`BV_OP_UMOD`, `BV_OP_CPOP`) against `bvEvalSubSpec`.
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

@[local c0_load] private theorem ddc_load_prog_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 16) = some s.prog_ptr := load_hdr_prog_ptr hm

@[local c0_load] private theorem ddc_load_slice_off_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 48) = some s.slice_off_ptr := load_hdr_slice_off_ptr hm

@[local c0_load] private theorem ddc_load_n_vars {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 80) = some s.n_vars := load_hdr_n_vars hm

@[local c0_load] private theorem ddc_load_n_cwords {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 88) = some s.n_cwords := load_hdr_n_cwords hm

@[local c0_load] private theorem ddc_load_oom {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 120) = some s.oom := load_hdr_oom hm

private theorem bv_cpop_cast {w1 w2 : Nat} (h : w1 = w2) (v : BitVec w1) :
    (BitVec.cast h v).cpop = BitVec.cast h v.cpop := by
  subst h; rfl

private theorem bv_udiv_cast {w1 w2 : Nat} (h : w1 = w2) (a b : BitVec w1) :
    BitVec.cast h a / BitVec.cast h b = BitVec.cast h (a / b) := by
  subst h; rfl

private theorem bv_umod_cast {w1 w2 : Nat} (h : w1 = w2) (a b : BitVec w1) :
    BitVec.cast h a % BitVec.cast h b = BitVec.cast h (a % b) := by
  subst h; rfl

private theorem ddc_sliceVal_cast {g : Aig} {ρ : Nat → Bool} {lp : List (BitVec 32)}
    {off w : Nat} {v : BitVec w} (hw_lt : w < 4294967296) (hle : off + w ≤ lp.length)
    (hsd : SliceDenotes g ρ (litsSlice lp off w) v) :
    OpsDivCpop.sliceVal g ρ lp off (BitVec.ofNat 32 w).toNat =
      BitVec.cast (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]) v := by
  have hw32 : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
  have hp := (OpsDivCpop.sliceDenotes_iff_of_le hle).mp hsd
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [OpsDivCpop.sliceVal_getLsbD (j := k) hk, BitVec.getLsbD_cast, ← hp,
    OpsDivCpop.sliceVal_getLsbD (j := k) (by omega)]

private theorem ddc_dc_ok_post {cfg : BVWorkspaceCfg} {progPtr : BitVec 64}
    {progBytes : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {hdr hdr1 : BVHdrState} {g g1 : Aig}
    {ab so : List (BitVec 32)} {aw aw1 : List (BitVec 64)} {ht ht1 lp lp1 : List (BitVec 32)}
    {nodeIdx res : BitVec 32} {w : Nat} {e : BVExpr w} {R : Mem 64 → Prop} {m' : Mem 64}
    {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hoom1 : hdr1.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hw_lt : w < 4294967296) (hok : BVWorkspaceOk cfg hdr ab so aw ht lp)
    (hok1 : BVWorkspaceOk cfg hdr1 ab so aw1 ht1 lp1)
    (haig1 : AigInv hdr1 g1 aw1 ht1) (hfr1 : hdr.DcBlastFrame hdr1) (hext1 : g ≤ g1)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hret : res = hdr.lits_len)
    (hlcap1 : hdr1.lits_len.toNat ≤ hdr1.lits_cap.toNat)
    (hagree : ∀ p < hdr.lits_len.toNat, lp1.getD p 0#32 = lp.getD p 0#32)
    (hwf1 : OpsDivCpop.SliceLitsWf hdr1 lp1 res.toNat (BitVec.ofNat 32 w).toNat)
    (hnd : nodes.get? nodeIdx.toNat = some (.bv w e))
    (hval : ∀ assign : BVExpr.Assignment,
      OpsDivCpop.sliceVal g1 (atomAssign progBytes assign) lp1 res.toNat
        (BitVec.ofNat 32 w).toNat =
        BitVec.cast (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]) (e.eval assign))
    (hm_so : (array (t := i32) hdr.slice_off_ptr (so.set (BitVec.setWidth 64 nodeIdx).toNat res) ⋆
      blastSoRest cfg hdr1 progPtr progBytes ab aw1 ht1 lp1 R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  have hw_eq : (BitVec.ofNat 32 w).toNat = w := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
  have hlc_eq : hdr1.lits_cap.toNat = cfg.lits_cap := bvWorkspaceOk_litsCap_eq hok1
  have hres_le : res.toNat + w ≤ hdr1.lits_len.toNat := by rw [← hw_eq]; exact hwf1.1
  have hlits_le : hdr.lits_len.toNat ≤ hdr1.lits_len.toNat := by rw [← hret]; omega
  refine drv_sub_bv_ok hoom0 hoom1 hni_lt hok hok1 haig1 hext1 hinv
    (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
    hlits_le (by omega) hagree hnd hres_le ?_ ?_ hm_so hQ
  · intro j hj; rw [← haig1.aig_len_eq]; exact hwf1.2 j (by omega)
  · intro assign
    have hle_lp : res.toNat + w ≤ lp1.length := by rw [hok1.lits_len]; omega
    rw [OpsDivCpop.sliceDenotes_iff_of_le hle_lp]
    have hv := hval assign
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    have h1 := OpsDivCpop.sliceVal_getLsbD (g := g1) (ρ := atomAssign progBytes assign)
      (lp := lp1) (off := res.toNat) (j := j) (w := w) hj
    have h2 := OpsDivCpop.sliceVal_getLsbD (g := g1) (ρ := atomAssign progBytes assign)
      (lp := lp1) (off := res.toNat) (j := j) (w := (BitVec.ofNat 32 w).toNat) (by omega)
    rw [h1, ← h2, hv, BitVec.getLsbD_cast]

public section

theorem bv_eval_ops_div_cpop_wp (Γ : Env)
    (hRead : ∀ xs m Q X, bvReadU32Spec xs m Q X →
      Γ "bv_read_u32" [i64, i64] [i32] xs m Q X)
    (hUdiv : ∀ xs m Q X, OpsDivCpop.bvBlastUdivSpec xs m Q X →
      Γ "bv_blast_udiv" [i64, i32, i32, i32] [i32] xs m Q X)
    (hUmod : ∀ xs m Q X, OpsDivCpop.bvBlastUmodSpec xs m Q X →
      Γ "bv_blast_umod" [i64, i32, i32, i32] [i32] xs m Q X)
    (hCpop : ∀ xs m Q X, OpsDivCpop.bvBlastCpopSpec xs m Q X →
      Γ "bv_blast_cpop" [i64, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvEvalSubSpec xs m Q X → Func.wp Γ bv_eval_ops_div_cpop_body xs m Q X := by
  rintro ⟨h, nodeIdx, ⟨⟩⟩ m Q X
    ⟨cfg, progPtr, progBytes, vars, cwords, nodes, prog, hdr, g, atomBases, sliceOffs,
      aigWords, htSlots, litsPool, R, rfl, hni_lt, hoom0, hinv, hm, hQ⟩
  have hok := hinv.ws_ok; have hp := hinv.parsed
  have haig := hinv.aig_inv; have hfit := hinv.prog_fit
  have hnw0 := drv_node_word0_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq hok.hdr_nv hok.nv_lt hni_lt
  have hnw1 := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq
    hok.hdr_nv hok.nv_lt hni_lt 1 1 rfl (by decide)
  have hnw2 := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq
    hok.hdr_nv hok.nv_lt hni_lt 2 2 rfl (by decide)
  have hnw3 := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq
    hok.hdr_nv hok.nv_lt hni_lt 3 3 rfl (by decide)
  have hn_lt : nodeIdx.toNat < u32At progBytes 3 := hinv.nn_eq ▸ hni_lt
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
  have hcap_le : hdr.lits_cap.toNat ≤ litsPool.length :=
    Nat.le_of_eq (bvWorkspaceOk_litsPool_eq_cap hok).symm
  have hw32 : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
  have hni_so : (BitVec.setWidth 64 nodeIdx).toNat < sliceOffs.length := by
    rw [bv32_setWidth64_toNat, hok.so_len]; exact hni_lt
  c0_hsplit
  · -- Case 1: BV_OP_UDIV (8)
    have hop8 : op = opUdiv := by unfold opUdiv; c0_bv_omega [hop_lt]
    clear hc
    have hbin := parsed_node_binop hp hn_lt
      (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop8]; unfold opUdiv; decide)
      (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop8]; unfold opUdiv opUmod; decide)
    dsimp only at hbin; rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hbin
    rcases hbin with ⟨ha_lt_ni, hb_lt_ni, bop, ea, eb, _, _, _, _, _, hbop, _, hga, hgb, hnd⟩
    rw [hbop hop8] at hnd
    obtain ⟨ha_so, _, ha_le, _, _, ha_wf, ha_sd⟩ :=
      drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
    obtain ⟨hb_so, _, hb_le, _, _, hb_wf, hb_sd⟩ :=
      drv_child_bv_prep hb_lt hb_lt_ni hoom0 hinv hni_lt hgb
    have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
    have hm_f := blast_full_focus hok.hdr_aig hok.hdr_ht hok.hdr_lits
      (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
    c0_call hUdiv
    refine ⟨hdr, g, aigWords, htSlots, litsPool, _, haig, hcap_le,
      fun _ _ _ _ _ => ⟨by rw [hw32]; exact ha_wf, by rw [hw32]; exact hb_wf⟩, hm_f, ?_⟩
    intro res hdr1 g1 aw1 ht1 lp1 m1 hfr1 hext1 _ haig1 hlp1 hpres1 _ _ _ hok_res hm1
    have hok1 := OpsDivCpop.bvWorkspaceOk_of_blastFrame hok hfr1 haig1 hlp1
    have hm1_b := blast_full_unfocus hok1.hdr_aig hok1.hdr_ht hok1.hdr_lits hm1; clear hm1
    have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr
    c0_hsplit
    · c0_hstraight
      exact hQ false hdr1 g1 sliceOffs aw1 ht1 lp1 m1 hok1 haig1 hext1
        (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
        (fun hf => absurd hf Bool.false_ne_true) hm1_b
    · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
      obtain ⟨hret, _, hlcap1, hwf1, hval1⟩ := hok_res hoom1
      have hso_ptr : hdr1.slice_off_ptr = hdr.slice_off_ptr := hok1.hdr_so.trans hok.hdr_so.symm
      have hm1_so := blast_so_focus hok1.hdr_so hm1_b; clear hm1_b; rw [hso_ptr] at hm1_so
      c0_hstraight
      refine ddc_dc_ok_post hoom0 hoom1 hni_lt hw_lt hok hok1 haig1 hfr1 hext1 hinv hret
        hlcap1 hpres1 hwf1 hnd (fun assign => ?_) (by assumption) hQ
      have hv := hval1 (atomAssign progBytes assign)
      simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hv; rw [hv]
      have ha_c := ddc_sliceVal_cast hw_lt
        (by rw [hok.lits_len]; have := hinv.lits_le_cap; omega) (ha_sd assign)
      have hb_c := ddc_sliceVal_cast hw_lt
        (by rw [hok.lits_len]; have := hinv.lits_le_cap; omega) (hb_sd assign)
      rw [ha_c, hb_c, bv_udiv_cast]; rfl
  · clear hc; c0_hstraight; c0_hsplit
    · -- Case 2: BV_OP_UMOD (9)
      have hop9 : op = opUmod := by unfold opUmod; c0_bv_omega [hop_lt]
      clear hc
      have hbin := parsed_node_binop hp hn_lt
        (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop9]; unfold opUmod; decide)
        (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop9]; unfold opUmod; decide)
      dsimp only at hbin; rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq, hb_eq] at hbin
      rcases hbin with ⟨ha_lt_ni, hb_lt_ni, bop, ea, eb, _, _, _, _, _, _, hbop, hga, hgb, hnd⟩
      rw [hbop hop9] at hnd
      obtain ⟨ha_so, _, ha_le, _, _, ha_wf, ha_sd⟩ :=
        drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
      obtain ⟨hb_so, _, hb_le, _, _, hb_wf, hb_sd⟩ :=
        drv_child_bv_prep hb_lt hb_lt_ni hoom0 hinv hni_lt hgb
      have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
      have hm_f := blast_full_focus hok.hdr_aig hok.hdr_ht hok.hdr_lits
        (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
      c0_call hUmod
      refine ⟨hdr, g, aigWords, htSlots, litsPool, _, haig, hcap_le,
        fun _ _ _ _ _ => ⟨by rw [hw32]; exact ha_wf, by rw [hw32]; exact hb_wf⟩, hm_f, ?_⟩
      intro res hdr1 g1 aw1 ht1 lp1 m1 hfr1 hext1 _ haig1 hlp1 hpres1 _ _ _ hok_res hm1
      have hok1 := OpsDivCpop.bvWorkspaceOk_of_blastFrame hok hfr1 haig1 hlp1
      have hm1_b := blast_full_unfocus hok1.hdr_aig hok1.hdr_ht hok1.hdr_lits hm1; clear hm1
      have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr
      c0_hsplit
      · c0_hstraight
        exact hQ false hdr1 g1 sliceOffs aw1 ht1 lp1 m1 hok1 haig1 hext1
          (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
          (fun hf => absurd hf Bool.false_ne_true) hm1_b
      · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
        obtain ⟨hret, _, hlcap1, hwf1, hval1⟩ := hok_res hoom1
        have hso_ptr : hdr1.slice_off_ptr = hdr.slice_off_ptr := hok1.hdr_so.trans hok.hdr_so.symm
        have hm1_so := blast_so_focus hok1.hdr_so hm1_b; clear hm1_b; rw [hso_ptr] at hm1_so
        c0_hstraight
        refine ddc_dc_ok_post hoom0 hoom1 hni_lt hw_lt hok hok1 haig1 hfr1 hext1 hinv hret
          hlcap1 hpres1 hwf1 hnd (fun assign => ?_) (by assumption) hQ
        have hv := hval1 (atomAssign progBytes assign)
        simp only [ne_eq, show (1#32 : BitVec 32) ≠ 0#32 by decide, not_false_eq_true,
          ↓reduceIte] at hv; rw [hv]
        have ha_c := ddc_sliceVal_cast hw_lt
          (by rw [hok.lits_len]; have := hinv.lits_le_cap; omega) (ha_sd assign)
        have hb_c := ddc_sliceVal_cast hw_lt
          (by rw [hok.lits_len]; have := hinv.lits_le_cap; omega) (hb_sd assign)
        rw [ha_c, hb_c, bv_umod_cast]; rfl
    · clear hc; c0_hstraight; c0_hsplit
      · -- Case 3: BV_OP_CPOP (16)
        have hop16 : op = opCpop := by unfold opCpop; c0_bv_omega [hop_lt]
        clear hc
        have hun := parsed_node_unop hp hn_lt
          (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop16]; unfold opUmod opCpop; decide)
          (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hop16]; unfold opCpop; decide)
        dsimp only at hun; rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, hw_eq, ha_eq] at hun
        rcases hun with ⟨ha_lt_ni, uop, ea, _, _, _, _, _, _, huop, hga, hnd⟩
        rw [huop hop16] at hnd
        obtain ⟨ha_so, _, ha_le, _, _, ha_wf, ha_sd⟩ :=
          drv_child_bv_prep ha_lt ha_lt_ni hoom0 hinv hni_lt hga
        have hm_so := blast_so_focus hok.hdr_so hm; clear hm; c0_hstraight
        have hm_f := blast_full_focus hok.hdr_aig hok.hdr_ht hok.hdr_lits
          (blast_so_unfocus hok.hdr_so hm_so); clear hm_so
        c0_call hCpop
        refine ⟨hdr, g, aigWords, htSlots, litsPool, _, haig, hcap_le,
          fun _ _ _ _ => by rw [hw32]; exact ha_wf, hm_f, ?_⟩
        intro res hdr1 g1 aw1 ht1 lp1 m1 hfr1 hext1 _ haig1 hlp1 hpres1 _ _ _ hok_res hm1
        have hok1 := OpsDivCpop.bvWorkspaceOk_of_blastFrame hok hfr1 haig1 hlp1
        have hm1_b := blast_full_unfocus hok1.hdr_aig hok1.hdr_ht hok1.hdr_lits hm1; clear hm1
        have hm1_hdr := blast_hdr_left hm1_b; c0_hstraight; clear hm1_hdr
        c0_hsplit
        · c0_hstraight
          exact hQ false hdr1 g1 sliceOffs aw1 ht1 lp1 m1 hok1 haig1 hext1
            (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
            (fun hf => absurd hf Bool.false_ne_true) hm1_b
        · have hoom1 : hdr1.oom = 0#32 := hc; clear hc
          obtain ⟨hret, _, hlcap1, hwf1, hval1⟩ := hok_res hoom1
          have hso_ptr : hdr1.slice_off_ptr = hdr.slice_off_ptr := hok1.hdr_so.trans hok.hdr_so.symm
          have hm1_so := blast_so_focus hok1.hdr_so hm1_b; clear hm1_b; rw [hso_ptr] at hm1_so
          c0_hstraight
          refine ddc_dc_ok_post hoom0 hoom1 hni_lt hw_lt hok hok1 haig1 hfr1 hext1 hinv hret
            hlcap1 hpres1 hwf1 hnd (fun assign => ?_) (by assumption) hQ
          rw [hval1 (atomAssign progBytes assign)]
          have ha_c := ddc_sliceVal_cast hw_lt
            (by rw [hok.lits_len]; have := hinv.lits_le_cap; omega) (ha_sd assign)
          rw [ha_c, bv_cpop_cast]; rfl
      · clear hc; c0_hstraight
        exact hQ false hdr g sliceOffs aigWords htSlots litsPool m hok haig
          (Aig.extends_rfl g) hinv.prog_ptr_eq rfl rfl
          (fun hf => absurd hf Bool.false_ne_true) hm

end

end LeanQbe.T.Examples.Bitblast.Proof
