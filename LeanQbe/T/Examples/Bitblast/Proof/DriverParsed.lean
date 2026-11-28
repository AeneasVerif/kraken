/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Proof.DriverHelpers
public import LeanQbe.T.Examples.Bitblast.Proof.Driver0Helpers
public import LeanQbe.T.Examples.Bitblast.Proof.OpsCoreHelpers
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulSpecs
public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpopHelpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.MemLemmas

/-!
# Full 32-Op `ParsedBVP1` Decoders & Dispatch Helpers (`Bitblast.Proof.DriverParsed`)

Provides `ParsedBVP1` decoding lemmas for all remaining `BVP1` opcodes (`extract`, `binop`,
`unop`, `append`, `replicate`, `shift`, `ult`), `bvBlastMem` focusing/unfocusing lemmas for
`OpsCore` / `OpsShiftMul` / `OpsDivCpop`, and shared `BvEvalSubQ` closing helpers.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.BVProg

public section

abbrev blastHdrLitsRest (cfg : BVWorkspaceCfg) (progPtr : BitVec 64) (progBytes : List UInt8)
    (atomBases sliceOffs : List (BitVec 32)) (aigWords : List (BitVec 64))
    (htSlots : List (BitVec 32)) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  bytes progPtr progBytes ⋆
  array (t := i32) (cfg.work_base + 128) atomBases ⋆
  region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
    (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
  array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
  region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
    (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
  array64 cfg.aig_ptr aigWords ⋆
  array (t := i32) cfg.ht_ptr htSlots ⋆
  region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
    (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ R

abbrev blastFullRest (cfg : BVWorkspaceCfg) (progPtr : BitVec 64) (progBytes : List UInt8)
    (atomBases sliceOffs : List (BitVec 32)) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  bytes progPtr progBytes ⋆
  array (t := i32) (cfg.work_base + 128) atomBases ⋆
  region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
    (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
  array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
  region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
    (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
  region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
    (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ R

end

public section

/-! ## 1. `bvBlastMem` Focus/Unfocus & Frame Helpers -/

theorem blast_hdr_lits_focus {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hlits : hdr.lits_ptr = cfg.lits_ptr)
    (hm : (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m) :
    (bvHdrMem cfg.work_base hdr ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆
      blastHdrLitsRest cfg progPtr progBytes atomBases sliceOffs aigWords htSlots R) m := by
  rw [hlits]; unfold bvBlastMem at hm; unfold blastHdrLitsRest; exact sep_ac hm

theorem blast_hdr_lits_unfocus {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hlits : hdr.lits_ptr = cfg.lits_ptr)
    (hm : (bvHdrMem cfg.work_base hdr ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆
      blastHdrLitsRest cfg progPtr progBytes atomBases sliceOffs aigWords htSlots R) m) :
    (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m := by
  rw [hlits] at hm; unfold bvBlastMem; unfold blastHdrLitsRest at hm; exact sep_ac hm

theorem blast_full_focus {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (haig : hdr.aig_ptr = cfg.aig_ptr) (hht : hdr.ht_ptr = cfg.ht_ptr)
    (hlits : hdr.lits_ptr = cfg.lits_ptr)
    (hm : (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m) :
    (bvHdrMem cfg.work_base hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆
      blastFullRest cfg progPtr progBytes atomBases sliceOffs R) m := by
  rw [haig, hht, hlits]; unfold bvBlastMem at hm; unfold blastFullRest; exact sep_ac hm

theorem blast_full_unfocus {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {progPtr : BitVec 64} {progBytes : List UInt8}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords : List (BitVec 64)}
    {htSlots litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (haig : hdr.aig_ptr = cfg.aig_ptr) (hht : hdr.ht_ptr = cfg.ht_ptr)
    (hlits : hdr.lits_ptr = cfg.lits_ptr)
    (hm : (bvHdrMem cfg.work_base hdr ⋆ array64 hdr.aig_ptr aigWords ⋆
      array (t := i32) hdr.ht_ptr htSlots ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆
      blastFullRest cfg progPtr progBytes atomBases sliceOffs R) m) :
    (bytes progPtr progBytes ⋆
      bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m := by
  rw [haig, hht, hlits] at hm; unfold bvBlastMem; unfold blastFullRest at hm; exact sep_ac hm

theorem bvWorkspaceOk_of_ocBlastFrame {cfg : BVWorkspaceCfg} {hdr hdr' : BVHdrState} {g' : Aig}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords aigWords' : List (BitVec 64)}
    {htSlots htSlots' litsPool litsPool' : List (BitVec 32)}
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (hfr : hdr.BlastFrame hdr') (haig' : AigInv hdr' g' aigWords' htSlots')
    (hlp : litsPool'.length = litsPool.length) :
    BVWorkspaceOk cfg hdr' atomBases sliceOffs aigWords' htSlots' litsPool' :=
  hok.of_modifies_aigInv hfr haig' hlp

theorem bvWorkspaceOk_of_smOpsFrame {cfg : BVWorkspaceCfg} {hdr hdr' : BVHdrState} {g' : Aig}
    {atomBases sliceOffs : List (BitVec 32)} {aigWords aigWords' : List (BitVec 64)}
    {htSlots htSlots' litsPool litsPool' : List (BitVec 32)}
    (hok : BVWorkspaceOk cfg hdr atomBases sliceOffs aigWords htSlots litsPool)
    (hfr : hdr.OpsFrame hdr') (haig' : AigInv hdr' g' aigWords' htSlots')
    (hlp : litsPool'.length = litsPool.length) :
    BVWorkspaceOk cfg hdr' atomBases sliceOffs aigWords' htSlots' litsPool' :=
  hok.of_modifies_aigInv hfr haig' hlp

theorem aigInv_of_ocBlastFrame {hdr hdr' : BVHdrState} {g : Aig} {aw : List (BitVec 64)}
    {ht : List (BitVec 32)} (hinv : AigInv hdr g aw ht)
    (hfr : hdr.BlastFrame hdr') (hal : hdr'.aig_len = hdr.aig_len) :
    AigInv hdr' g aw ht :=
  hinv.of_modifies hfr hal

theorem aigInv_of_smOpsFrame {hdr hdr' : BVHdrState} {g : Aig} {aw : List (BitVec 64)}
    {ht : List (BitVec 32)} (hinv : AigInv hdr g aw ht)
    (hfr : hdr.OpsFrame hdr') (hal : hdr'.aig_len = hdr.aig_len) :
    AigInv hdr' g aw ht :=
  hinv.of_modifies hfr hal

theorem bvWorkspaceOk_litsCap_eq {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp : List (BitVec 32)}
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) :
    hdr.lits_cap.toNat = cfg.lits_cap := by
  rw [hok.hdr_lcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hok.lcap_lt]

theorem bvWorkspaceOk_litsPool_eq_cap {cfg : BVWorkspaceCfg} {hdr : BVHdrState}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp : List (BitVec 32)}
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp) :
    lp.length = hdr.lits_cap.toNat := by
  rw [hok.lits_len, bvWorkspaceOk_litsCap_eq hok]

theorem bv32_setWidth64_toNat (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  have := x.isLt; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]

theorem sliceDenotes_cast {g : Aig} {ρ : Nat → Bool} {lp : List (BitVec 32)} {off w1 w2 : Nat}
    (h : w1 = w2) {v : BitVec w1}
    (hs : SliceDenotes g ρ (litsSlice lp off w1) v) :
    SliceDenotes g ρ (litsSlice lp off w2) (BitVec.cast h v) := by
  subst h; exact hs

theorem drv_child_bv_prep {progBytes : List UInt8} {vars : BinTree VarEntry}
    {cwords : BinTree Nat} {nodes : BinTree ProgNode} {prog : BVLogicalExpr}
    {cfg : BVWorkspaceCfg} {progPtr : BitVec 64} {hdr : BVHdrState} {g : Aig}
    {ab so : List (BitVec 32)} {aw : List (BitVec 64)} {ht lp : List (BitVec 32)}
    {nodeIdx : BitVec 32} {a aw_n : Nat} {ea : BVExpr aw_n}
    (ha_lt : a < 4294967296) (ha_lt_ni : a < nodeIdx.toNat) (hoom0 : hdr.oom = 0#32)
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hni_lt : nodeIdx.toNat < cfg.n_nodes) (hga : nodes.get? a = some (.bv aw_n ea)) :
    ∃ ha_so : (BitVec.setWidth 64 (BitVec.ofNat 32 a)).toNat < so.length,
      let off := so[(BitVec.setWidth 64 (BitVec.ofNat 32 a)).toNat]'ha_so
      off = so.getD a 0#32 ∧
      off.toNat + aw_n ≤ hdr.lits_len.toNat ∧
      SliceAigWf hdr.aig_len.toNat lp off.toNat aw_n ∧
      SliceLitsWf g lp off.toNat aw_n ∧
      OpsDivCpop.SliceLitsWf hdr lp off.toNat aw_n ∧
      ∀ assign : BVExpr.Assignment,
        SliceDenotes g (atomAssign progBytes assign) (litsSlice lp off.toNat aw_n)
          (ea.eval assign) := by
  have ha64 : (BitVec.setWidth 64 (BitVec.ofNat 32 a)).toNat = a := by
    rw [bv32_setWidth64_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have ha_so : (BitVec.setWidth 64 (BitVec.ofNat 32 a)).toNat < so.length := by
    rw [hinv.ws_ok.so_len, ha64]; omega
  have hnd_a := hinv.prefix_ok hoom0 a ha_lt_ni
  unfold NodeDenotes at hnd_a; rw [hga] at hnd_a; dsimp only at hnd_a
  rcases hnd_a with ⟨hoff_le, hbd, hsd⟩
  have hget : so[(BitVec.setWidth 64 (BitVec.ofNat 32 a)).toNat]'ha_so = so.getD a 0#32 := by
    rw [list_getD_eq_getElem _ 0#32, ha64]
  refine ⟨ha_so, hget, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hget]; exact hoff_le
  · intro j hj; rw [hget, hinv.aig_inv.aig_len_eq]; exact hbd j hj
  · intro j hj; rw [hget]; exact hbd j hj
  · refine ⟨by rw [hget]; exact hoff_le, fun j hj => ?_⟩
    rw [hget, hinv.aig_inv.aig_len_eq]; exact hbd j hj
  · intro assign; rw [hget]; exact hsd assign

/-! ## 2. Shared `BvEvalSubQ` Closing Lemmas -/

theorem drv_sub_bv_ok {cfg : BVWorkspaceCfg} {progPtr : BitVec 64} {progBytes : List UInt8}
    {vars : BinTree VarEntry} {cwords : BinTree Nat} {nodes : BinTree ProgNode}
    {prog : BVLogicalExpr} {hdr hdr' : BVHdrState} {g g' : Aig}
    {ab so : List (BitVec 32)} {aw aw' : List (BitVec 64)} {ht ht' lp lp' : List (BitVec 32)}
    {nodeIdx res : BitVec 32} {w : Nat} {e : BVExpr w} {R : Mem 64 → Prop} {m' : Mem 64}
    {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hoom' : hdr'.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp)
    (hok' : BVWorkspaceOk cfg hdr' ab so aw' ht' lp')
    (haig' : AigInv hdr' g' aw' ht') (hext : g ≤ g')
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hpp' : hdr'.prog_ptr = progPtr) (hnc' : hdr'.n_cwords = hdr.n_cwords)
    (hrt' : hdr'.root_node = hdr.root_node)
    (hlits_le : hdr.lits_len.toNat ≤ hdr'.lits_len.toNat)
    (hlits_cap : hdr'.lits_len.toNat ≤ cfg.lits_cap)
    (hagree : ∀ p < hdr.lits_len.toNat, lp'.getD p 0#32 = lp.getD p 0#32)
    (hnd : nodes.get? nodeIdx.toNat = some (.bv w e))
    (hres_le : res.toNat + w ≤ hdr'.lits_len.toNat)
    (hres_bd : ∀ j < w, (lp'.getD (res.toNat + j) 0#32 >>> 1).toNat < g'.A + 1 + g'.nodes.size)
    (hres_sd : ∀ assign : BVExpr.Assignment,
      SliceDenotes g' (atomAssign progBytes assign) (litsSlice lp' res.toNat w) (e.eval assign))
    (hm_so : (array (t := i32) hdr.slice_off_ptr (so.set (BitVec.setWidth 64 nodeIdx).toNat res) ⋆
      blastSoRest cfg hdr' progPtr progBytes ab aw' ht' lp' R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  rw [bv32_setWidth64_toNat] at hm_so
  have hso_ptr : hdr'.slice_off_ptr = hdr.slice_off_ptr := hok'.hdr_so.trans hok.hdr_so.symm
  have hok2 := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat res hok'
  refine hQ true hdr' g' (so.set nodeIdx.toNat res) aw' ht' lp' _ hok2 haig' hext
    hpp' hnc' hrt' (fun _ => ⟨hoom', ?_⟩)
    (blast_so_unfocus hok'.hdr_so (by rw [hso_ptr]; exact hm_so))
  refine blastEvalInv_step hoom0 hinv hok2 haig' hext hni_lt hpp' hnc' hrt'
    hlits_le hlits_cap hagree ?_
  exact nodeDenotes_set_bv hnd hres_le hres_bd hres_sd (hok.so_len ▸ hni_lt)

theorem drv_sub_bool_ok {cfg : BVWorkspaceCfg} {progPtr : BitVec 64} {progBytes : List UInt8}
    {vars : BinTree VarEntry} {cwords : BinTree Nat} {nodes : BinTree ProgNode}
    {prog : BVLogicalExpr} {hdr hdr' : BVHdrState} {g g' : Aig}
    {ab so : List (BitVec 32)} {aw aw' : List (BitVec 64)} {ht ht' lp : List (BitVec 32)}
    {nodeIdx res : BitVec 32} {e : BVLogicalExpr} {R : Mem 64 → Prop} {m' : Mem 64}
    {Q : Post [.bool]}
    (hoom0 : hdr.oom = 0#32) (hoom' : hdr'.oom = 0#32) (hni_lt : nodeIdx.toNat < cfg.n_nodes)
    (hok : BVWorkspaceOk cfg hdr ab so aw ht lp)
    (hok' : BVWorkspaceOk cfg hdr' ab so aw' ht' lp)
    (haig' : AigInv hdr' g' aw' ht') (hext : g ≤ g')
    (hinv : BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr g
      ab so aw ht lp nodeIdx.toNat)
    (hpp' : hdr'.prog_ptr = progPtr) (hnc' : hdr'.n_cwords = hdr.n_cwords)
    (hrt' : hdr'.root_node = hdr.root_node) (hlits' : hdr'.lits_len = hdr.lits_len)
    (hnd : nodes.get? nodeIdx.toNat = some (.bool e))
    (hres_bd : (res >>> 1).toNat < g'.A + 1 + g'.nodes.size)
    (hres_ev : ∀ assign : BVExpr.Assignment,
      g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec res) = e.eval assign)
    (hm_so : (array (t := i32) hdr.slice_off_ptr (so.set (BitVec.setWidth 64 nodeIdx).toNat res) ⋆
      blastSoRest cfg hdr' progPtr progBytes ab aw' ht' lp R) m')
    (hQ : BvEvalSubQ cfg progPtr progBytes vars cwords nodes prog hdr g ab nodeIdx R Q) :
    Q (true, ⟨⟩) m' := by
  rw [bv32_setWidth64_toNat] at hm_so
  have hso_ptr : hdr'.slice_off_ptr = hdr.slice_off_ptr := hok'.hdr_so.trans hok.hdr_so.symm
  have hok2 := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat res hok'
  refine hQ true hdr' g' (so.set nodeIdx.toNat res) aw' ht' lp _ hok2 haig' hext
    hpp' hnc' hrt' (fun _ => ⟨hoom', ?_⟩)
    (blast_so_unfocus hok'.hdr_so (by rw [hso_ptr]; exact hm_so))
  refine blastEvalInv_step hoom0 hinv hok2 haig' hext hni_lt hpp' hnc' hrt'
    (by rw [hlits']; exact Nat.le_refl _) (by rw [hlits']; exact hinv.lits_le_cap)
    (fun _ _ => rfl) ?_
  exact nodeDenotes_set_bool hnd hres_bd hres_ev (hok.so_len ▸ hni_lt)

/-! ## 3. `ParsedBVP1` Decoders for Remaining `BVP1` Opcodes -/

theorem parsed_node_extract {bs : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hop : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = opExtract) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let w := u32At bs (nw0 + 5 * k + 1)
    let a := u32At bs (nw0 + 5 * k + 2)
    let b := u32At bs (nw0 + 5 * k + 3)
    let bw := u32At bs (nw0 + 5 * b + 1)
    b < k ∧ u32At bs (nw0 + 5 * b) < opEq ∧
    ∃ eb : BVExpr bw,
      nodes.get? b = some (.bv bw eb) ∧ nodes.get? k = some (.bv w (.extract a w eb)) := by
  have hval := hp.valid.nodes_ok k hk
  rw [validNodeAt_extract hop] at hval; dsimp only at hval
  split at hval
  · cases hval
  · rename_i hge
    generalize hw_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = w
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [hb_eq] at hge hval
    have hb : b < k := by omega
    simp only [decide_eq_true_eq] at hval
    obtain ⟨ndb, hgb, _, hbvb, _⟩ := hp.nodes_step b (by omega)
    obtain ⟨eb, rfl⟩ := hbvb hval
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hop, hw_eq, ha_eq, hb_eq, hc_eq] at hdec
    simp only [decodeNode, opExtract, nat_blt_eq_decide, nat_beq_eq_decide, hgb] at hdec
    injection hdec with heq; subst heq; subst hw_eq ha_eq hb_eq
    exact ⟨hb, hval, eb, hgb, hget⟩

theorem parsed_node_binop {bs : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hgt : 2 < u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k))
    (hle : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) ≤ opUmod) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let op := u32At bs (nw0 + 5 * k)
    let w := u32At bs (nw0 + 5 * k + 1)
    let a := u32At bs (nw0 + 5 * k + 2)
    let b := u32At bs (nw0 + 5 * k + 3)
    a < k ∧ b < k ∧
    ∃ (bop : BVBinOp) (ea eb : BVExpr w),
      (op = opAnd → bop = .and) ∧ (op = opOr → bop = .or) ∧
      (op = opXor → bop = .xor) ∧ (op = opAdd → bop = .add) ∧
      (op = opMul → bop = .mul) ∧ (op = opUdiv → bop = .udiv) ∧
      (op = opUmod → bop = .umod) ∧
      nodes.get? a = some (.bv w ea) ∧ nodes.get? b = some (.bv w eb) ∧
      nodes.get? k = some (.bv w (.bin ea bop eb)) := by
  have hval := hp.valid.nodes_ok k hk
  rw [validNodeAt_binop hgt hle] at hval; dsimp only at hval
  split at hval
  · cases hval
  · rename_i hor
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hor
    simp only [decide_eq_true_eq] at hval
    generalize hop_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = op
    generalize hw_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = w
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [hop_eq] at hgt hle; rw [ha_eq, hb_eq] at hor; rw [ha_eq, hb_eq, hw_eq] at hval
    generalize hwa_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * a + 1) = wa
    generalize hwb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * b + 1) = wb
    rw [hwa_eq, hwb_eq] at hval
    obtain ⟨nda, hga, _, hbva, _⟩ := hp.nodes_step a (by omega)
    rw [hwa_eq] at hbva; obtain ⟨ea, rfl⟩ := hbva hval.1
    obtain ⟨ndb, hgb, _, hbvb, _⟩ := hp.nodes_step b (by omega)
    rw [hwb_eq] at hbvb; obtain ⟨eb, rfl⟩ := hbvb hval.2.1
    have hwa : wa = w := hval.2.2.1; have hwb : wb = w := hval.2.2.2
    clear hwa_eq hwb_eq; subst wa; subst wb
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hop_eq, hw_eq, ha_eq, hb_eq, hc_eq] at hdec
    have hop_c : op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8 ∨ op = 9 := by
      unfold opUmod at hle; omega
    let bop : BVBinOp :=
      if op = 3 then .and else if op = 4 then .or else if op = 5 then .xor
      else if op = 6 then .add else if op = 7 then .mul else if op = 8 then .udiv else .umod
    have hdec_eq : decodeNode vars cwords nodes op w a b c = some (.bv w (.bin ea bop eb)) := by
      rcases hop_c with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [decodeNode, mkBvBin, bop, nat_blt_eq_decide, hga, hgb]
    rw [hdec_eq] at hdec; injection hdec with heq; subst heq
    subst hop_eq hw_eq ha_eq hb_eq
    refine ⟨hor.1, hor.2, bop, ea, eb,
      fun h => by simp [h, bop, opAnd], fun h => by simp [h, bop, opOr],
      fun h => by simp [h, bop, opXor], fun h => by simp [h, bop, opAdd],
      fun h => by simp [h, bop, opMul], fun h => by simp [h, bop, opUdiv],
      fun h => by simp [h, bop, opUmod], hga, hgb, hget⟩

theorem parsed_node_unop {bs : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hgt : opUmod < u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k))
    (hle : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) ≤ opCpop) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let op := u32At bs (nw0 + 5 * k)
    let w := u32At bs (nw0 + 5 * k + 1)
    let a := u32At bs (nw0 + 5 * k + 2)
    let b := u32At bs (nw0 + 5 * k + 3)
    a < k ∧
    ∃ (uop : BVUnOp) (ea : BVExpr w),
      (op = opNot → uop = .not) ∧ (op = opRotL → uop = .rotateLeft b) ∧
      (op = opRotR → uop = .rotateRight b) ∧
      (op = opAshrC → uop = .arithShiftRightConst b) ∧
      (op = opReverse → uop = .reverse) ∧ (op = opClz → uop = .clz) ∧
      (op = opCpop → uop = .cpop) ∧
      nodes.get? a = some (.bv w ea) ∧ nodes.get? k = some (.bv w (.un uop ea)) := by
  have hval := hp.valid.nodes_ok k hk
  rw [validNodeAt_unop hgt hle] at hval; dsimp only at hval
  split at hval
  · cases hval
  · rename_i hge
    generalize hop_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = op
    generalize hw_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = w
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [hop_eq] at hgt hle; rw [ha_eq] at hge; rw [ha_eq, hw_eq] at hval
    have ha : a < k := by omega
    simp only [decide_eq_true_eq] at hval
    generalize hwa_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * a + 1) = wa
    rw [hwa_eq] at hval
    obtain ⟨nda, hga, _, hbva, _⟩ := hp.nodes_step a (by omega)
    rw [hwa_eq] at hbva; obtain ⟨ea, rfl⟩ := hbva hval.1
    have hwa : wa = w := hval.2; clear hwa_eq; subst wa
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hop_eq, hw_eq, ha_eq, hb_eq, hc_eq] at hdec
    have hop_c : op = 10 ∨ op = 11 ∨ op = 12 ∨ op = 13 ∨ op = 14 ∨ op = 15 ∨ op = 16 := by
      unfold opUmod at hgt; unfold opCpop at hle; omega
    let uop : BVUnOp :=
      if op = 10 then .not else if op = 11 then .rotateLeft b
      else if op = 12 then .rotateRight b else if op = 13 then .arithShiftRightConst b
      else if op = 14 then .reverse else if op = 15 then .clz else .cpop
    have hdec_eq : decodeNode vars cwords nodes op w a b c = some (.bv w (.un uop ea)) := by
      rcases hop_c with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [decodeNode, mkBvUn, uop, nat_blt_eq_decide, hga]
    rw [hdec_eq] at hdec; injection hdec with heq; subst heq
    subst hop_eq hw_eq ha_eq hb_eq
    refine ⟨ha, uop, ea,
      fun h => by simp [h, uop, opNot], fun h => by simp [h, uop, opRotL],
      fun h => by simp [h, uop, opRotR], fun h => by simp [h, uop, opAshrC],
      fun h => by simp [h, uop, opReverse], fun h => by simp [h, uop, opClz],
      fun h => by simp [h, uop, opCpop], hga, hget⟩

theorem parsed_node_append {bs : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hop : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = opAppend) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let w := u32At bs (nw0 + 5 * k + 1)
    let a := u32At bs (nw0 + 5 * k + 2)
    let b := u32At bs (nw0 + 5 * k + 3)
    let lw := u32At bs (nw0 + 5 * a + 1)
    let rw_n := u32At bs (nw0 + 5 * b + 1)
    a < k ∧ b < k ∧ lw + rw_n = w ∧
    ∃ (ea : BVExpr lw) (eb : BVExpr rw_n) (hw : w = lw + rw_n),
      nodes.get? a = some (.bv lw ea) ∧ nodes.get? b = some (.bv rw_n eb) ∧
      nodes.get? k = some (.bv w (.append ea eb hw)) := by
  have hval := hp.valid.nodes_ok k hk
  rw [validNodeAt_append hop] at hval; dsimp only at hval
  split at hval
  · cases hval
  · rename_i hor
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hor
    simp only [decide_eq_true_eq] at hval
    generalize hw_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = w
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [ha_eq, hb_eq] at hor; rw [ha_eq, hb_eq, hw_eq] at hval
    obtain ⟨nda, hga, _, hbva, _⟩ := hp.nodes_step a (by omega)
    obtain ⟨ea, rfl⟩ := hbva hval.1
    obtain ⟨ndb, hgb, _, hbvb, _⟩ := hp.nodes_step b (by omega)
    obtain ⟨eb, rfl⟩ := hbvb hval.2.1
    have hsum : w = u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * a + 1) +
        u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * b + 1) := hval.2.2.symm
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hop, hw_eq, ha_eq, hb_eq, hc_eq] at hdec
    simp only [decodeNode, opAppend, nat_blt_eq_decide, nat_beq_eq_decide, hga, hgb,
      hsum, ↓reduceDIte] at hdec
    injection hdec with heq; subst heq; subst hw_eq ha_eq hb_eq
    exact ⟨hor.1, hor.2, hval.2.2, ea, eb, hsum, hga, hgb, hget⟩

theorem parsed_node_replicate {bs : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hop : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = opReplicate) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let w := u32At bs (nw0 + 5 * k + 1)
    let a := u32At bs (nw0 + 5 * k + 2)
    let b := u32At bs (nw0 + 5 * k + 3)
    let aw := u32At bs (nw0 + 5 * a + 1)
    a < k ∧ aw * b = w ∧
    ∃ (ea : BVExpr aw) (hw : w = aw * b),
      nodes.get? a = some (.bv aw ea) ∧ nodes.get? k = some (.bv w (.replicate b ea hw)) := by
  have hval := hp.valid.nodes_ok k hk
  rw [validNodeAt_rep hop] at hval; dsimp only at hval
  split at hval
  · cases hval
  · rename_i hge
    generalize hw_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = w
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [ha_eq] at hge; rw [ha_eq, hb_eq, hw_eq] at hval
    have ha : a < k := by omega
    simp only [decide_eq_true_eq] at hval
    obtain ⟨nda, hga, _, hbva, _⟩ := hp.nodes_step a (by omega)
    obtain ⟨ea, rfl⟩ := hbva hval.1
    have hmul : w = u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * a + 1) * b := hval.2.symm
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hop, hw_eq, ha_eq, hb_eq, hc_eq] at hdec
    simp only [decodeNode, opReplicate, nat_blt_eq_decide, nat_beq_eq_decide, hga,
      hmul, ↓reduceDIte] at hdec
    injection hdec with heq; subst heq; subst hw_eq ha_eq hb_eq
    exact ⟨ha, hval.2, ea, hmul, hga, hget⟩

theorem parsed_node_shift {bs : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hgt : opReplicate < u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k))
    (hle : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) ≤ opAshr) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let op := u32At bs (nw0 + 5 * k)
    let w := u32At bs (nw0 + 5 * k + 1)
    let a := u32At bs (nw0 + 5 * k + 2)
    let b := u32At bs (nw0 + 5 * k + 3)
    let nw := u32At bs (nw0 + 5 * b + 1)
    a < k ∧ b < k ∧
    ∃ (ea : BVExpr w) (eb : BVExpr nw),
      nodes.get? a = some (.bv w ea) ∧ nodes.get? b = some (.bv nw eb) ∧
      (op = opShl → nodes.get? k = some (.bv w (.shiftLeft ea eb))) ∧
      (op = opUshr → nodes.get? k = some (.bv w (.shiftRight ea eb))) ∧
      (op = opAshr → nodes.get? k = some (.bv w (.arithShiftRight ea eb))) := by
  have hval := hp.valid.nodes_ok k hk
  rw [validNodeAt_shift hgt hle] at hval; dsimp only at hval
  split at hval
  · cases hval
  · rename_i hor
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hor
    simp only [decide_eq_true_eq] at hval
    generalize hop_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = op
    generalize hw_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = w
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [hop_eq] at hgt hle; rw [ha_eq, hb_eq] at hor; rw [ha_eq, hb_eq, hw_eq] at hval
    generalize hwa_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * a + 1) = wa
    rw [hwa_eq] at hval
    obtain ⟨nda, hga, _, hbva, _⟩ := hp.nodes_step a (by omega)
    rw [hwa_eq] at hbva; obtain ⟨ea, rfl⟩ := hbva hval.1
    obtain ⟨ndb, hgb, _, hbvb, _⟩ := hp.nodes_step b (by omega)
    obtain ⟨eb, rfl⟩ := hbvb hval.2.1
    have hwa : wa = w := hval.2.2; subst hwa
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hop_eq, hw_eq, ha_eq, hb_eq, hc_eq] at hdec
    have hop_c : op = 19 ∨ op = 20 ∨ op = 21 := by
      unfold opReplicate at hgt; unfold opAshr at hle; omega
    subst hop_eq hw_eq ha_eq hb_eq
    refine ⟨hor.1, hor.2, ea, eb, hga, hgb, ?_, ?_, ?_⟩
    · intro h; simp only [decodeNode, h, opShl, nat_blt_eq_decide, nat_beq_eq_decide,
        hga, hgb, ↓reduceDIte] at hdec; injection hdec with heq; subst heq; exact hget
    · intro h; simp only [decodeNode, h, opUshr, nat_blt_eq_decide, nat_beq_eq_decide,
        hga, hgb, ↓reduceDIte] at hdec; injection hdec with heq; subst heq; exact hget
    · intro h; simp only [decodeNode, h, opAshr, nat_blt_eq_decide, nat_beq_eq_decide,
        hga, hgb, ↓reduceDIte] at hdec; injection hdec with heq; subst heq; exact hget

theorem parsed_node_ult {bs : List UInt8} {vars : BinTree VarEntry} {cwords : BinTree Nat}
    {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hop : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = opUlt) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let w := u32At bs (nw0 + 5 * k + 1)
    let a := u32At bs (nw0 + 5 * k + 2)
    let b := u32At bs (nw0 + 5 * k + 3)
    let ew := u32At bs (nw0 + 5 * a + 1)
    w = 1 ∧ a < k ∧ b < k ∧ u32At bs (nw0 + 5 * b + 1) = ew ∧
    ∃ (ea eb : BVExpr ew),
      nodes.get? a = some (.bv ew ea) ∧ nodes.get? b = some (.bv ew eb) ∧
      nodes.get? k = some (.bool (.literal (.bin ea .ult eb))) := by
  have hval := hp.valid.nodes_ok k hk
  have hw1 : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1 := by
    by_cases h : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1
    · exact h
    · rw [validNodeAt_w_ne1 (by rw [hop]; unfold opAshr opUlt; decide)
        (by rw [hop]; unfold opUlt; decide) h] at hval
      cases hval
  rw [validNodeAt_cmp (by rw [hop]; unfold opAshr opUlt; decide)
    (by rw [hop]; unfold opUlt; decide) hw1] at hval
  dsimp only at hval
  split at hval
  · cases hval
  · rename_i hor
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hor
    simp only [decide_eq_true_eq] at hval
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [ha_eq, hb_eq] at hor hval
    generalize hewa_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * a + 1) = ewa
    generalize hewb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * b + 1) = ewb
    rw [hewa_eq, hewb_eq] at hval
    obtain ⟨nda, hga, _, hbva, _⟩ := hp.nodes_step a (by omega)
    rw [hewa_eq] at hbva; obtain ⟨ea, rfl⟩ := hbva hval.1
    obtain ⟨ndb, hgb, _, hbvb, _⟩ := hp.nodes_step b (by omega)
    rw [hewb_eq] at hbvb; obtain ⟨eb, rfl⟩ := hbvb hval.2.1
    have hweq : ewb = ewa := hval.2.2.symm; subst hweq
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hop, hw1, ha_eq, hb_eq, hc_eq] at hdec
    simp only [decodeNode, mkPredBin, opUlt, nat_blt_eq_decide, nat_beq_eq_decide,
      hga, hgb, ↓reduceDIte] at hdec
    injection hdec with heq; subst heq; subst ha_eq hb_eq hewa_eq
    exact ⟨hw1, hor.1, hor.2, hewb_eq, ea, eb, hga, hgb, hget⟩

end

end LeanQbe.T.Examples.Bitblast.Proof
