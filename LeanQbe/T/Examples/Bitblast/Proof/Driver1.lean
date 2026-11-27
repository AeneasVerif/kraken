/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
import LeanQbe.T.Examples.Bitblast.Proof.DriverHelpers
import LeanQbe.T.Examples.Bitblast.Proof.Validate0
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Node & Program Evaluator WP Proofs (`Bitblast.Proof.Driver1`)

Proves `Γ`-parametric `Func.wp` soundness for:
- `bv_eval_node_wp` (`bvEvalNodeSpec`)
- `bv_eval_program_wp` (`bvEvalProgramSpec`)
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

/-! ## 1. Local Memory Access Helpers (`BVHdr`, `array i32`) -/

@[local c0_load] private theorem drv1_load_prog_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 16) = some s.prog_ptr := load_hdr_prog_ptr hm

@[local c0_load] private theorem drv1_load_slice_off_ptr {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 48) = some s.slice_off_ptr := load_hdr_slice_off_ptr hm

@[local c0_load] private theorem drv1_load_n_vars {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 80) = some s.n_vars := load_hdr_n_vars hm

@[local c0_load] private theorem drv1_load_n_nodes {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 84) = some s.n_nodes := load_hdr_n_nodes hm

@[local c0_load] private theorem drv1_load_n_cwords {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 88) = some s.n_cwords := load_hdr_n_cwords hm

@[local c0_load] private theorem drv1_load_oom {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 120) = some s.oom := load_hdr_oom hm

private theorem drv1_bv32_shl2_add_eq (base : BitVec 64) (idx : BitVec 32) :
    base + (idx.setWidth 64 <<< (2 : Nat)) = base + BitVec.ofNat 64 (4 * idx.toNat) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  have hi32 := idx.isLt
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : idx.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : idx.toNat * 2 ^ 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * idx.toNat < 2 ^ 64)]
  omega

@[local c0_load] private theorem drv1_load_array32_shl2 {base : BitVec 64} {idx : BitVec 32}
    {sh : Nat} {xs : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hsh : sh = 2) (hi : idx.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m) :
    loadVal m i32 (base + (idx.setWidth 64 <<< sh)) = some (xs[idx.toNat]'hi) := by
  subst hsh; rw [drv1_bv32_shl2_add_eq]
  exact loadVal_array (t := i32) (by decide) hi hm

@[local c0_store] private theorem drv1_store_array32_shl2 {base : BitVec 64} {idx : BitVec 32}
    {sh : Nat} {xs : List (BitVec 32)} (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64}
    (hsh : sh = 2) (hi : idx.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m) :
    storeOk m i32 (base + (idx.setWidth 64 <<< sh)) ∧
      (array (t := i32) base (xs.set idx.toNat v) ⋆ R)
        (storeMem m i32 (base + (idx.setWidth 64 <<< sh)) v) := by
  subst hsh; rw [drv1_bv32_shl2_add_eq]
  exact store_array (t := i32) v (by decide) hi hm

/-! ## 2. Pure Boolean `ParsedBVP1` Helpers (`BCONST`, `BNOT`, `GATE_*`, `ITE`) -/

private theorem parsed_node_bconst {bs : List UInt8} {vars : BinTree VarEntry}
    {cwords : BinTree Nat} {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hop : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = opBConst) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let a := u32At bs (nw0 + 5 * k + 2)
    a < 2 ∧ nodes.get? k = some (.bool (.const (Nat.beq a 1))) := by
  have hval := hp.valid.nodes_ok k hk
  have hw1 : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1 := by
    by_cases h : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1
    · exact h
    · rw [validNodeAt_w_ne1 (by rw [hop]; unfold opAshr opBConst; decide)
        (by rw [hop]; unfold opBConst; decide) h] at hval
      cases hval
  rw [validNodeAt_bconst hop hw1] at hval
  simp only [decide_eq_true_eq] at hval
  obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
  simp only [decodeNode, hop, hw1, opBConst, nat_blt_eq_decide, nat_beq_eq_decide, hval] at hdec
  injection hdec with heq
  subst heq
  exact ⟨hval, hget⟩

private theorem parsed_node_bnot {bs : List UInt8} {vars : BinTree VarEntry}
    {cwords : BinTree Nat} {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hop : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = opBNot) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let a := u32At bs (nw0 + 5 * k + 2)
    a < k ∧ opEq ≤ u32At bs (nw0 + 5 * a) ∧
    ∃ ea : BVLogicalExpr,
      nodes.get? a = some (.bool ea) ∧ nodes.get? k = some (.bool (.not ea)) := by
  have hval := hp.valid.nodes_ok k hk
  have hw1 : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1 := by
    by_cases h : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1
    · exact h
    · rw [validNodeAt_w_ne1 (by rw [hop]; unfold opAshr opBNot; decide)
        (by rw [hop]; unfold opBNot; decide) h] at hval
      cases hval
  rw [validNodeAt_bnot hop hw1] at hval
  dsimp only at hval
  split at hval
  · cases hval
  · rename_i hge
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [ha_eq] at hge hval
    have ha : a < k := by omega
    simp only [decide_eq_true_eq] at hval
    obtain ⟨nda, hga, _, _, hbo⟩ := hp.nodes_step a (by omega)
    obtain ⟨ea, rfl⟩ := hbo hval
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hop, hw1, ha_eq, hb_eq, hc_eq] at hdec
    simp only [decodeNode, opBNot, nat_blt_eq_decide, nat_beq_eq_decide, hga] at hdec
    injection hdec with heq
    subst heq
    subst ha_eq
    exact ⟨ha, hval, ea, hga, hget⟩

private theorem parsed_node_gate {bs : List UInt8} {vars : BinTree VarEntry}
    {cwords : BinTree Nat} {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hgt : opBNot < u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k))
    (hle : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) ≤ opGateOr) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let op := u32At bs (nw0 + 5 * k)
    let a := u32At bs (nw0 + 5 * k + 2)
    let b := u32At bs (nw0 + 5 * k + 3)
    a < k ∧ b < k ∧ opEq ≤ u32At bs (nw0 + 5 * a) ∧ opEq ≤ u32At bs (nw0 + 5 * b) ∧
    ∃ (gt : Gate) (ea eb : BVLogicalExpr),
      (op = opGateAnd → gt = .and) ∧
      (op = opGateXor → gt = .xor) ∧
      (op = opGateBeq → gt = .beq) ∧
      (op = opGateOr → gt = .or) ∧
      nodes.get? a = some (.bool ea) ∧ nodes.get? b = some (.bool eb) ∧
      nodes.get? k = some (.bool (.gate gt ea eb)) := by
  have hval := hp.valid.nodes_ok k hk
  have hw1 : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1 := by
    by_cases h : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1
    · exact h
    · rw [validNodeAt_w_ne1 (by unfold opAshr opBNot at *; omega)
        (by unfold opGateOr at *; omega) h] at hval
      cases hval
  rw [validNodeAt_gate hgt hle hw1] at hval
  dsimp only at hval
  split at hval
  · cases hval
  · rename_i hor
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hor
    simp only [decide_eq_true_eq] at hval
    generalize hop_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = op
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [hop_eq] at hgt hle
    rw [ha_eq, hb_eq] at hor hval
    obtain ⟨nda, hga, _, _, hboa⟩ := hp.nodes_step a (by omega)
    obtain ⟨ea, rfl⟩ := hboa hval.1
    obtain ⟨ndb, hgb, _, _, hbob⟩ := hp.nodes_step b (by omega)
    obtain ⟨eb, rfl⟩ := hbob hval.2
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hop_eq, hw1, ha_eq, hb_eq, hc_eq] at hdec
    have hop_c : op = 27 ∨ op = 28 ∨ op = 29 ∨ op = 30 := by
      unfold opBNot at hgt; unfold opGateOr at hle; omega
    let gt : Gate :=
      if op = 27 then .and else if op = 28 then .xor else if op = 29 then .beq else .or
    have hgt_dec : decodeNode vars cwords nodes op 1 a b c = some (.bool (.gate gt ea eb)) := by
      rcases hop_c with rfl | rfl | rfl | rfl <;>
        simp [decodeNode, mkGateNode, gt, nat_blt_eq_decide, hga, hgb]
    rw [hgt_dec] at hdec
    injection hdec with heq
    subst heq
    subst hop_eq ha_eq hb_eq
    refine ⟨hor.1, hor.2, hval.1, hval.2, gt, ea, eb, ?_, ?_, ?_, ?_, hga, hgb, hget⟩
    · intro h; simp [h, gt, opGateAnd]
    · intro h; simp [h, gt, opGateXor]
    · intro h; simp [h, gt, opGateBeq]
    · intro h; simp [h, gt, opGateOr]

private theorem parsed_node_ite {bs : List UInt8} {vars : BinTree VarEntry}
    {cwords : BinTree Nat} {nodes : BinTree ProgNode} {prog : BVLogicalExpr} {k : Nat}
    (hp : ParsedBVP1 bs vars cwords nodes prog) (hk : k < u32At bs 3)
    (hop : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k) = opIte) :
    let nw0 := nodesOff (u32At bs 2) (u32At bs 4)
    let a := u32At bs (nw0 + 5 * k + 2)
    let b := u32At bs (nw0 + 5 * k + 3)
    let c := u32At bs (nw0 + 5 * k + 4)
    a < k ∧ b < k ∧ c < k ∧
    ∃ ea eb ec : BVLogicalExpr,
      nodes.get? a = some (.bool ea) ∧ nodes.get? b = some (.bool eb) ∧
      nodes.get? c = some (.bool ec) ∧ nodes.get? k = some (.bool (.ite ea eb ec)) := by
  have hval := hp.valid.nodes_ok k hk
  have hw1 : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1 := by
    by_cases h : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 1) = 1
    · exact h
    · rw [validNodeAt_w_ne1 (by rw [hop]; unfold opAshr opIte; decide)
        (by rw [hop]; unfold opIte; decide) h] at hval
      cases hval
  rw [validNodeAt_ite (by rw [hop]; unfold opGateOr opIte; decide)
    (by rw [hop]; unfold opIte; decide) hw1] at hval
  dsimp only at hval
  split at hval
  · cases hval
  · rename_i hor
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hor
    simp only [decide_eq_true_eq] at hval
    generalize ha_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 2) = a
    generalize hb_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 3) = b
    generalize hc_eq : u32At bs (nodesOff (u32At bs 2) (u32At bs 4) + 5 * k + 4) = c
    rw [ha_eq, hb_eq, hc_eq] at hor hval
    obtain ⟨nda, hga, _, _, hboa⟩ := hp.nodes_step a (by omega)
    obtain ⟨ea, rfl⟩ := hboa hval.1
    obtain ⟨ndb, hgb, _, _, hbob⟩ := hp.nodes_step b (by omega)
    obtain ⟨eb, rfl⟩ := hbob hval.2.1
    obtain ⟨ndc, hgc, _, _, hboc⟩ := hp.nodes_step c (by omega)
    obtain ⟨ec, rfl⟩ := hboc hval.2.2
    obtain ⟨nd, hget, hdec, _⟩ := hp.nodes_step k hk
    rw [hop, hw1, ha_eq, hb_eq, hc_eq] at hdec
    simp only [decodeNode, opIte, nat_blt_eq_decide, nat_beq_eq_decide, hga, hgb, hgc] at hdec
    injection hdec with heq
    subst heq
    subst ha_eq hb_eq hc_eq
    exact ⟨hor.1.1, hor.1.2, hor.2, ea, eb, ec, hga, hgb, hgc, hget⟩

/-! ## 3. `bv_eval_node_wp` -/

public section

theorem bv_eval_node_wp (Γ : Env)
    (hRead : ∀ xs m Q X, bvReadU32Spec xs m Q X →
      Γ "bv_read_u32" [i64, i64] [i32] xs m Q X)
    (hMkAnd : ∀ xs m Q X, bvMkAndSpec xs m Q X →
      Γ "bv_mk_and" [i64, i32, i32] [i32] xs m Q X)
    (hNot : ∀ xs m Q X, bvAigNotSpec xs m Q X →
      Γ "bv_aig_not" [i32] [i32] xs m Q X)
    (hOr : ∀ xs m Q X, bvAigOrSpec xs m Q X →
      Γ "bv_aig_or" [i64, i32, i32] [i32] xs m Q X)
    (hXor : ∀ xs m Q X, bvAigXorSpec xs m Q X →
      Γ "bv_aig_xor" [i64, i32, i32] [i32] xs m Q X)
    (hBeq : ∀ xs m Q X, bvAigBeqSpec xs m Q X →
      Γ "bv_aig_beq" [i64, i32, i32] [i32] xs m Q X)
    (hIte : ∀ xs m Q X, bvAigIteSpec xs m Q X →
      Γ "bv_aig_ite" [i64, i32, i32, i32] [i32] xs m Q X)
    (hCore : ∀ xs m Q X, bvEvalSubSpec xs m Q X →
      Γ "bv_eval_ops_core" [i64, i32] [.bool] xs m Q X)
    (hShiftMul : ∀ xs m Q X, bvEvalSubSpec xs m Q X →
      Γ "bv_eval_ops_shift_mul" [i64, i32] [.bool] xs m Q X)
    (hDivCpop : ∀ xs m Q X, bvEvalSubSpec xs m Q X →
      Γ "bv_eval_ops_div_cpop" [i64, i32] [.bool] xs m Q X) :
    ∀ xs m Q X, bvEvalNodeSpec xs m Q X → Func.wp Γ bv_eval_node_body xs m Q X := by
  rintro ⟨h, nodeIdx, ⟨⟩⟩ m Q X
    ⟨cfg, progPtr, progBytes, vars, cwords, nodes, prog, hdr, g, atomBases, sliceOffs,
      aigWords, htSlots, litsPool, R, hh_eq, hni_lt, hoom0, hinv, hm, hQ⟩
  subst hh_eq
  have hok := hinv.ws_ok
  have hp := hinv.parsed
  have haig := hinv.aig_inv
  have hfit := hinv.prog_fit
  have hn_lt : nodeIdx.toNat < u32At progBytes 3 := by rw [← hinv.nn_eq]; exact hni_lt
  have hm_bytes : (bytes progPtr progBytes ⋆
      (bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R)) m := sep_ac hm
  have hm_hdr := hm
  rw [bvBlastMem_hdr_left] at hm_hdr
  have hw0 := drv_node_word0_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq
    hok.hdr_nv hok.nv_lt hni_lt
  have hw2 := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq
    hok.hdr_nv hok.nv_lt hni_lt 2 2 rfl (by decide)
  have hw3 := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq
    hok.hdr_nv hok.nv_lt hni_lt 3 3 rfl (by decide)
  have hw4 := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq
    hok.hdr_nv hok.nv_lt hni_lt 4 4 rfl (by decide)
  have hfit' : hdr.prog_ptr.toNat + progBytes.length < 2 ^ 64 := by
    rw [hinv.prog_ptr_eq]; exact hfit
  have hm_bytes' : (bytes hdr.prog_ptr progBytes ⋆
      (bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R)) m := by
    rw [hinv.prog_ptr_eq]; exact hm_bytes
  c0_hstraight
  c0_call hRead
  refine ⟨progBytes, _, hfit', hw0.2, hm_bytes', ?_⟩
  c0_hstraight
  c0_call hRead
  refine ⟨progBytes, _, hfit', hw2.2, hm_bytes', ?_⟩
  c0_hstraight
  c0_call hRead
  refine ⟨progBytes, _, hfit', hw3.2, hm_bytes', ?_⟩
  c0_hstraight
  c0_call hRead
  refine ⟨progBytes, _, hfit', hw4.2, hm_bytes', ?_⟩
  c0_hstraight
  clear hm_bytes hm_bytes' hm_hdr hfit'
  rw [hw0.1, hw2.1, hw3.1, hw4.1]
  clear hw0 hw2 hw3 hw4
  generalize hop_eq : u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat +
    5 * nodeIdx.toNat) = op
  generalize ha_eq : u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat +
    5 * nodeIdx.toNat + 2) = a
  generalize hb_eq : u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat +
    5 * nodeIdx.toNat + 3) = b
  generalize hc_eq : u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat +
    5 * nodeIdx.toNat + 4) = c
  have hop_lt : op < 4294967296 := hop_eq ▸ u32At_lt progBytes _
  have ha_lt : a < 4294967296 := ha_eq ▸ u32At_lt progBytes _
  have hb_lt : b < 4294967296 := hb_eq ▸ u32At_lt progBytes _
  have hc_lt : c < 4294967296 := hc_eq ▸ u32At_lt progBytes _
  c0_hsplit
  · -- Branch 1: op == BV_OP_BCONST (25)
    have hop25 : op = opBConst := by unfold opBConst; c0_bv_omega [hop_lt]
    clear hc
    have hno_op : u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
        5 * nodeIdx.toNat) = opBConst := by
      rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop25
    have hbc := parsed_node_bconst hp hn_lt hno_op
    dsimp only at hbc
    rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq] at hbc
    rcases hbc with ⟨ha_2, hnd_bc⟩
    have hml_so := blast_so_focus hok.hdr_so hm
    clear hm
    have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok.so_len]; exact hni_lt
    c0_hstraight
    let litv : BitVec 32 := BitVec.ofNat 32 a &&& 1#32
    let sliceOffs' := sliceOffs.set nodeIdx.toNat litv
    have hlitv_eq : litv = BitVec.ofNat 32 (a % 2) := by
      dsimp only [litv]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
        show (1 : Nat) % 2 ^ 32 = 1 from rfl, Nat.and_one_is_mod]
      omega
    have hok' := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat litv hok
    have hm' := blast_so_unfocus hok.hdr_so (by assumption)
    refine hQ true hdr g sliceOffs' aigWords htSlots litsPool _ hok' haig
      (Aig.extends_rfl g) hinv.lits_le_cap hinv.prog_ptr_eq rfl rfl (fun _ => ⟨hoom0, ?_⟩)
      (fun _ => ⟨rfl, rfl, by
        dsimp only [sliceOffs']; rw [hlitv_eq, ← ha_eq]⟩) hm'
    refine blastEvalInv_step hoom0 hinv hok' haig (Aig.extends_rfl g) hni_lt hinv.prog_ptr_eq
      rfl rfl (Nat.le_refl _) hinv.lits_le_cap (fun _ _ => rfl) ?_
    refine nodeDenotes_set_bool hnd_bc ?_ (fun assign => ?_) hni_so
    · rw [hlitv_eq, bv32_lsr1_toNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : a % 2 < 2 ^ 32)]
      omega
    · rw [hlitv_eq]
      have ha_cases : a = 0 ∨ a = 1 := by omega
      rcases ha_cases with rfl | rfl
      · simp [BVLogicalExpr.eval, Nat.beq, Aig.evalLit_zero]
      · simp [BVLogicalExpr.eval, Nat.beq, Aig.evalLit_one]
  · have hop_ne25 : op ≠ opBConst := fun h => by
      apply hc; subst h; unfold opBConst; decide
    have hno_ne25 : u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat +
        5 * nodeIdx.toNat) ≠ opBConst := by
      rw [hop_eq]; exact hop_ne25
    clear hc; c0_hstraight; c0_hsplit
    · -- Branch 2: op == BV_OP_BNOT (26)
      have hop26 : op = opBNot := by unfold opBNot; c0_bv_omega [hop_lt]
      clear hc
      have hno_op : u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
          5 * nodeIdx.toNat) = opBNot := by
        rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop26
      have hbn := parsed_node_bnot hp hn_lt hno_op
      dsimp only at hbn
      rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq] at hbn
      rcases hbn with ⟨ha_lt_ni, _, ea, hga, hnd_bn⟩
      have ha_so : (BitVec.ofNat 32 a).toNat < sliceOffs.length := by
        rw [hok.so_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega
      have hnd_a := hinv.prefix_ok hoom0 a ha_lt_ni
      unfold NodeDenotes at hnd_a
      rw [hga] at hnd_a
      rcases hnd_a with ⟨ha_bd, ha_ev⟩
      have hml_so := blast_so_focus hok.hdr_so hm
      clear hm
      have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok.so_len]; exact hni_lt
      c0_hstraight
      c0_call hNot
      dsimp only [bvAigNotSpec]
      let sa := sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so
      let litv := sa ^^^ 1#32
      let sliceOffs' := sliceOffs.set nodeIdx.toNat litv
      c0_hstraight
      have hsa_get : sa = sliceOffs.getD a 0#32 := by
        dsimp only [sa]; rw [list_getD_eq_getElem _ 0#32]
        simp [BitVec.toNat_ofNat]
      have hok' := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat litv hok
      have hm' := blast_so_unfocus hok.hdr_so (by assumption)
      refine hQ true hdr g sliceOffs' aigWords htSlots litsPool _ hok' haig
        (Aig.extends_rfl g) hinv.lits_le_cap hinv.prog_ptr_eq rfl rfl (fun _ => ⟨hoom0, ?_⟩)
        (fun h => absurd h hno_ne25) hm'
      refine blastEvalInv_step hoom0 hinv hok' haig (Aig.extends_rfl g) hni_lt hinv.prog_ptr_eq
        rfl rfl (Nat.le_refl _) hinv.lits_le_cap (fun _ _ => rfl) ?_
      refine nodeDenotes_set_bool hnd_bn ?_ (fun assign => ?_) hni_so
      · dsimp only [litv]; rw [bv32_xor1_lsr1, hsa_get]; exact ha_bd
      · dsimp only [litv]; rw [evalLit_xor1, hsa_get, ha_ev assign]; rfl
    · have hop_ne26 : op ≠ opBNot := fun h => by
        apply hc; subst h; unfold opBNot; decide
      clear hc; c0_hstraight; c0_hsplit
      · -- Branch 3: op == BV_OP_GATE_AND (27)
        have hop27 : op = opGateAnd := by unfold opGateAnd; c0_bv_omega [hop_lt]
        clear hc
        have hno_op : u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
            5 * nodeIdx.toNat) = opGateAnd := by
          rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop27
        have hgt := parsed_node_gate hp hn_lt
          (by rw [hno_op]; unfold opBNot opGateAnd; decide)
          (by rw [hno_op]; unfold opGateAnd opGateOr; decide)
        dsimp only at hgt
        rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, ha_eq, hb_eq] at hgt
        rcases hgt with ⟨ha_lt_ni, hb_lt_ni, _, _, gt, ea, eb, hgt_eq, _, _, _, hga, hgb, hnd_gt⟩
        rw [hgt_eq hop27] at hnd_gt
        have ha_so : (BitVec.ofNat 32 a).toNat < sliceOffs.length := by
          rw [hok.so_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega
        have hb_so : (BitVec.ofNat 32 b).toNat < sliceOffs.length := by
          rw [hok.so_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt]; omega
        have hnd_a := hinv.prefix_ok hoom0 a ha_lt_ni
        unfold NodeDenotes at hnd_a; rw [hga] at hnd_a
        have hnd_b := hinv.prefix_ok hoom0 b hb_lt_ni
        unfold NodeDenotes at hnd_b; rw [hgb] at hnd_b
        have hml_so := blast_so_focus hok.hdr_so hm
        clear hm
        c0_hstraight
        have hml' := blast_so_unfocus hok.hdr_so hml_so
        clear hml_so
        have hml_aig := blast_aig_focus hok.hdr_aig hok.hdr_ht hml'
        clear hml'
        let sa := sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so
        let sb := sliceOffs[(BitVec.ofNat 32 b).toNat]'hb_so
        have hsa_get : sa = sliceOffs.getD a 0#32 := by
          dsimp only [sa]; rw [list_getD_eq_getElem _ 0#32]
          simp [BitVec.toNat_ofNat]
        have hsb_get : sb = sliceOffs.getD b 0#32 := by
          dsimp only [sb]; rw [list_getD_eq_getElem _ 0#32]
          simp [BitVec.toNat_ofNat]
        have hsa_bd : (sa >>> 1).toNat < hdr.aig_len.toNat := by
          rw [haig.aig_len_eq, hsa_get]; exact hnd_a.1
        have hsb_bd : (sb >>> 1).toNat < hdr.aig_len.toNat := by
          rw [haig.aig_len_eq, hsb_get]; exact hnd_b.1
        c0_call hMkAnd
        refine ⟨hdr, g, aigWords, htSlots, _, haig, fun _ => ⟨hsa_bd, hsb_bd⟩, hml_aig, ?_⟩
        intro res hdr1 g1 aw1 hts1 m1 hfr1 hext1 _ haig1 _ _ hres hm1
        have hml1 := blast_aig_unfocus (hfr1.aig_ptr.trans hok.hdr_aig)
          (hfr1.ht_ptr.trans hok.hdr_ht) hm1
        clear hm1
        have hok1 := bvWorkspaceOk_of_aigFrame hok hfr1 haig1
        have hml1_hdr := hml1
        rw [bvBlastMem_hdr_left] at hml1_hdr
        c0_hstraight
        clear hml1_hdr
        c0_hsplit
        · c0_hstraight
          exact hQ false hdr1 g1 sliceOffs aw1 hts1 litsPool m1 hok1 haig1 hext1
            (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
            (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
            (fun hf => absurd hf Bool.false_ne_true) (fun h => absurd h hno_ne25) hml1
        · have hoom1 : hdr1.oom = 0#32 := hc
          clear hc
          have hres1 := hres hoom1
          have hso_ptr : hdr1.slice_off_ptr = hdr.slice_off_ptr :=
            hok1.hdr_so.trans hok.hdr_so.symm
          have hml_so1 := blast_so_focus hok1.hdr_so hml1
          clear hml1
          rw [hso_ptr] at hml_so1
          have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok1.so_len]; exact hni_lt
          c0_hstraight
          let sliceOffs' := sliceOffs.set nodeIdx.toNat res
          have hok2 := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat res hok1
          refine hQ true hdr1 g1 sliceOffs' aw1 hts1 litsPool _ hok2 haig1 hext1
            (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
            (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
            (fun _ => ⟨hoom1, ?_⟩) (fun h => absurd h hno_ne25) ?_
          · refine blastEvalInv_step hoom0 hinv hok2 haig1 hext1 hni_lt
              (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
              (by rw [hfr1.lits_len]; exact Nat.le_refl _)
              (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
              (fun _ _ => rfl) ?_
            refine nodeDenotes_set_bool hnd_gt (by rw [← haig1.aig_len_eq]; exact hres1.1)
              (fun assign => ?_) hni_so
            have hraw := hres1.2 (atomAssign progBytes assign)
            change g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec res) =
              (g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec sa) &&
                g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec sb)) at hraw
            rw [hraw, hsa_get, hsb_get, hnd_a.2 assign, hnd_b.2 assign]
            rfl
          · exact blast_so_unfocus hok1.hdr_so (by rw [hso_ptr]; assumption)
      · have hop_ne27 : op ≠ opGateAnd := fun h => by
          apply hc; subst h; unfold opGateAnd; decide
        clear hc; c0_hstraight; c0_hsplit
        · -- Branch 4: op == BV_OP_GATE_XOR (28)
          have hop28 : op = opGateXor := by unfold opGateXor; c0_bv_omega [hop_lt]
          clear hc
          have hno_op : u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
              5 * nodeIdx.toNat) = opGateXor := by
            rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop28
          have hgt := parsed_node_gate hp hn_lt
            (by rw [hno_op]; unfold opBNot opGateXor; decide)
            (by rw [hno_op]; unfold opGateXor opGateOr; decide)
          dsimp only at hgt
          rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, ha_eq, hb_eq] at hgt
          rcases hgt with ⟨ha_lt_ni, hb_lt_ni, _, _, gt, ea, eb, _, hgt_eq, _, _, hga, hgb, hnd_gt⟩
          rw [hgt_eq hop28] at hnd_gt
          have ha_so : (BitVec.ofNat 32 a).toNat < sliceOffs.length := by
            rw [hok.so_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega
          have hb_so : (BitVec.ofNat 32 b).toNat < sliceOffs.length := by
            rw [hok.so_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt]; omega
          have hnd_a := hinv.prefix_ok hoom0 a ha_lt_ni
          unfold NodeDenotes at hnd_a; rw [hga] at hnd_a
          have hnd_b := hinv.prefix_ok hoom0 b hb_lt_ni
          unfold NodeDenotes at hnd_b; rw [hgb] at hnd_b
          have hml_so := blast_so_focus hok.hdr_so hm
          clear hm
          c0_hstraight
          have hml' := blast_so_unfocus hok.hdr_so hml_so
          clear hml_so
          have hml_aig := blast_aig_focus hok.hdr_aig hok.hdr_ht hml'
          clear hml'
          let sa := sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so
          let sb := sliceOffs[(BitVec.ofNat 32 b).toNat]'hb_so
          have hsa_get : sa = sliceOffs.getD a 0#32 := by
            dsimp only [sa]; rw [list_getD_eq_getElem _ 0#32]
            simp [BitVec.toNat_ofNat]
          have hsb_get : sb = sliceOffs.getD b 0#32 := by
            dsimp only [sb]; rw [list_getD_eq_getElem _ 0#32]
            simp [BitVec.toNat_ofNat]
          have hsa_bd : (sa >>> 1).toNat < hdr.aig_len.toNat := by
            rw [haig.aig_len_eq, hsa_get]; exact hnd_a.1
          have hsb_bd : (sb >>> 1).toNat < hdr.aig_len.toNat := by
            rw [haig.aig_len_eq, hsb_get]; exact hnd_b.1
          c0_call hXor
          refine ⟨hdr, g, aigWords, htSlots, _, haig, fun _ => ⟨hsa_bd, hsb_bd⟩, hml_aig, ?_⟩
          intro res hdr1 g1 aw1 hts1 m1 hfr1 hext1 _ haig1 _ _ hres hm1
          have hml1 := blast_aig_unfocus (hfr1.aig_ptr.trans hok.hdr_aig)
            (hfr1.ht_ptr.trans hok.hdr_ht) hm1
          clear hm1
          have hok1 := bvWorkspaceOk_of_aigFrame hok hfr1 haig1
          have hml1_hdr := hml1
          rw [bvBlastMem_hdr_left] at hml1_hdr
          c0_hstraight
          clear hml1_hdr
          c0_hsplit
          · c0_hstraight
            exact hQ false hdr1 g1 sliceOffs aw1 hts1 litsPool m1 hok1 haig1 hext1
              (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
              (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
              (fun hf => absurd hf Bool.false_ne_true) (fun h => absurd h hno_ne25) hml1
          · have hoom1 : hdr1.oom = 0#32 := hc
            clear hc
            have hres1 := hres hoom1
            have hso_ptr : hdr1.slice_off_ptr = hdr.slice_off_ptr :=
              hok1.hdr_so.trans hok.hdr_so.symm
            have hml_so1 := blast_so_focus hok1.hdr_so hml1
            clear hml1
            rw [hso_ptr] at hml_so1
            have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok1.so_len]; exact hni_lt
            c0_hstraight
            let sliceOffs' := sliceOffs.set nodeIdx.toNat res
            have hok2 := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat res hok1
            refine hQ true hdr1 g1 sliceOffs' aw1 hts1 litsPool _ hok2 haig1 hext1
              (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
              (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
              (fun _ => ⟨hoom1, ?_⟩) (fun h => absurd h hno_ne25) ?_
            · refine blastEvalInv_step hoom0 hinv hok2 haig1 hext1 hni_lt
                (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
                (by rw [hfr1.lits_len]; exact Nat.le_refl _)
                (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
                (fun _ _ => rfl) ?_
              refine nodeDenotes_set_bool hnd_gt (by rw [← haig1.aig_len_eq]; exact hres1.1)
                (fun assign => ?_) hni_so
              have hraw := hres1.2 (atomAssign progBytes assign)
              change g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec res) =
                (g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec sa) ^^
                  g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec sb)) at hraw
              rw [hraw, hsa_get, hsb_get, hnd_a.2 assign, hnd_b.2 assign]
              rfl
            · exact blast_so_unfocus hok1.hdr_so (by rw [hso_ptr]; assumption)
        · have hop_ne28 : op ≠ opGateXor := fun h => by
            apply hc; subst h; unfold opGateXor; decide
          clear hc; c0_hstraight; c0_hsplit
          · -- Branch 5: op == BV_OP_GATE_BEQ (29)
            have hop29 : op = opGateBeq := by unfold opGateBeq; c0_bv_omega [hop_lt]
            clear hc
            have hno_op : u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
                5 * nodeIdx.toNat) = opGateBeq := by
              rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop29
            have hgt := parsed_node_gate hp hn_lt
              (by rw [hno_op]; unfold opBNot opGateBeq; decide)
              (by rw [hno_op]; unfold opGateBeq opGateOr; decide)
            dsimp only at hgt
            rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, ha_eq, hb_eq] at hgt
            rcases hgt with
              ⟨ha_lt_ni, hb_lt_ni, _, _, gt, ea, eb, _, _, hgt_eq, _, hga, hgb, hnd_gt⟩
            rw [hgt_eq hop29] at hnd_gt
            have ha_so : (BitVec.ofNat 32 a).toNat < sliceOffs.length := by
              rw [hok.so_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega
            have hb_so : (BitVec.ofNat 32 b).toNat < sliceOffs.length := by
              rw [hok.so_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt]; omega
            have hnd_a := hinv.prefix_ok hoom0 a ha_lt_ni
            unfold NodeDenotes at hnd_a; rw [hga] at hnd_a
            have hnd_b := hinv.prefix_ok hoom0 b hb_lt_ni
            unfold NodeDenotes at hnd_b; rw [hgb] at hnd_b
            have hml_so := blast_so_focus hok.hdr_so hm
            clear hm
            c0_hstraight
            have hml' := blast_so_unfocus hok.hdr_so hml_so
            clear hml_so
            have hml_aig := blast_aig_focus hok.hdr_aig hok.hdr_ht hml'
            clear hml'
            let sa := sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so
            let sb := sliceOffs[(BitVec.ofNat 32 b).toNat]'hb_so
            have hsa_get : sa = sliceOffs.getD a 0#32 := by
              dsimp only [sa]; rw [list_getD_eq_getElem _ 0#32]
              simp [BitVec.toNat_ofNat]
            have hsb_get : sb = sliceOffs.getD b 0#32 := by
              dsimp only [sb]; rw [list_getD_eq_getElem _ 0#32]
              simp [BitVec.toNat_ofNat]
            have hsa_bd : (sa >>> 1).toNat < hdr.aig_len.toNat := by
              rw [haig.aig_len_eq, hsa_get]; exact hnd_a.1
            have hsb_bd : (sb >>> 1).toNat < hdr.aig_len.toNat := by
              rw [haig.aig_len_eq, hsb_get]; exact hnd_b.1
            c0_call hBeq
            refine ⟨hdr, g, aigWords, htSlots, _, haig, fun _ => ⟨hsa_bd, hsb_bd⟩, hml_aig, ?_⟩
            intro res hdr1 g1 aw1 hts1 m1 hfr1 hext1 _ haig1 _ _ hres hm1
            have hml1 := blast_aig_unfocus (hfr1.aig_ptr.trans hok.hdr_aig)
              (hfr1.ht_ptr.trans hok.hdr_ht) hm1
            clear hm1
            have hok1 := bvWorkspaceOk_of_aigFrame hok hfr1 haig1
            have hml1_hdr := hml1
            rw [bvBlastMem_hdr_left] at hml1_hdr
            c0_hstraight
            clear hml1_hdr
            c0_hsplit
            · c0_hstraight
              exact hQ false hdr1 g1 sliceOffs aw1 hts1 litsPool m1 hok1 haig1 hext1
                (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
                (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
                (fun hf => absurd hf Bool.false_ne_true) (fun h => absurd h hno_ne25) hml1
            · have hoom1 : hdr1.oom = 0#32 := hc
              clear hc
              have hres1 := hres hoom1
              have hso_ptr : hdr1.slice_off_ptr = hdr.slice_off_ptr :=
                hok1.hdr_so.trans hok.hdr_so.symm
              have hml_so1 := blast_so_focus hok1.hdr_so hml1
              clear hml1
              rw [hso_ptr] at hml_so1
              have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok1.so_len]; exact hni_lt
              c0_hstraight
              let sliceOffs' := sliceOffs.set nodeIdx.toNat res
              have hok2 := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat res hok1
              refine hQ true hdr1 g1 sliceOffs' aw1 hts1 litsPool _ hok2 haig1 hext1
                (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
                (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
                (fun _ => ⟨hoom1, ?_⟩) (fun h => absurd h hno_ne25) ?_
              · refine blastEvalInv_step hoom0 hinv hok2 haig1 hext1 hni_lt
                  (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
                  (by rw [hfr1.lits_len]; exact Nat.le_refl _)
                  (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
                  (fun _ _ => rfl) ?_
                refine nodeDenotes_set_bool hnd_gt (by rw [← haig1.aig_len_eq]; exact hres1.1)
                  (fun assign => ?_) hni_so
                have hraw := hres1.2 (atomAssign progBytes assign)
                change g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec res) =
                  (g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec sa) ==
                    g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec sb)) at hraw
                rw [hraw, hsa_get, hsb_get, hnd_a.2 assign, hnd_b.2 assign]
                rfl
              · exact blast_so_unfocus hok1.hdr_so (by rw [hso_ptr]; assumption)
          · have hop_ne29 : op ≠ opGateBeq := fun h => by
              apply hc; subst h; unfold opGateBeq; decide
            clear hc; c0_hstraight; c0_hsplit
            · -- Branch 6: op == BV_OP_GATE_OR (30)
              have hop30 : op = opGateOr := by unfold opGateOr; c0_bv_omega [hop_lt]
              clear hc
              have hno_op : u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
                  5 * nodeIdx.toNat) = opGateOr := by
                rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop30
              have hgt := parsed_node_gate hp hn_lt
                (by rw [hno_op]; unfold opBNot opGateOr; decide)
                (by rw [hno_op]; unfold opGateOr; decide)
              dsimp only at hgt
              rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq, ha_eq, hb_eq] at hgt
              rcases hgt with
                ⟨ha_lt_ni, hb_lt_ni, _, _, gt, ea, eb, _, _, _, hgt_eq, hga, hgb, hnd_gt⟩
              rw [hgt_eq hop30] at hnd_gt
              have ha_so : (BitVec.ofNat 32 a).toNat < sliceOffs.length := by
                rw [hok.so_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega
              have hb_so : (BitVec.ofNat 32 b).toNat < sliceOffs.length := by
                rw [hok.so_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt]; omega
              have hnd_a := hinv.prefix_ok hoom0 a ha_lt_ni
              unfold NodeDenotes at hnd_a; rw [hga] at hnd_a
              have hnd_b := hinv.prefix_ok hoom0 b hb_lt_ni
              unfold NodeDenotes at hnd_b; rw [hgb] at hnd_b
              have hml_so := blast_so_focus hok.hdr_so hm
              clear hm
              c0_hstraight
              have hml' := blast_so_unfocus hok.hdr_so hml_so
              clear hml_so
              have hml_aig := blast_aig_focus hok.hdr_aig hok.hdr_ht hml'
              clear hml'
              let sa := sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so
              let sb := sliceOffs[(BitVec.ofNat 32 b).toNat]'hb_so
              have hsa_get : sa = sliceOffs.getD a 0#32 := by
                dsimp only [sa]; rw [list_getD_eq_getElem _ 0#32]
                simp [BitVec.toNat_ofNat]
              have hsb_get : sb = sliceOffs.getD b 0#32 := by
                dsimp only [sb]; rw [list_getD_eq_getElem _ 0#32]
                simp [BitVec.toNat_ofNat]
              have hsa_bd : (sa >>> 1).toNat < hdr.aig_len.toNat := by
                rw [haig.aig_len_eq, hsa_get]; exact hnd_a.1
              have hsb_bd : (sb >>> 1).toNat < hdr.aig_len.toNat := by
                rw [haig.aig_len_eq, hsb_get]; exact hnd_b.1
              c0_call hOr
              refine ⟨hdr, g, aigWords, htSlots, _, haig, fun _ => ⟨hsa_bd, hsb_bd⟩, hml_aig, ?_⟩
              intro res hdr1 g1 aw1 hts1 m1 hfr1 hext1 _ haig1 _ _ hres hm1
              have hml1 := blast_aig_unfocus (hfr1.aig_ptr.trans hok.hdr_aig)
                (hfr1.ht_ptr.trans hok.hdr_ht) hm1
              clear hm1
              have hok1 := bvWorkspaceOk_of_aigFrame hok hfr1 haig1
              have hml1_hdr := hml1
              rw [bvBlastMem_hdr_left] at hml1_hdr
              c0_hstraight
              clear hml1_hdr
              c0_hsplit
              · c0_hstraight
                exact hQ false hdr1 g1 sliceOffs aw1 hts1 litsPool m1 hok1 haig1 hext1
                  (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
                  (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
                  (fun hf => absurd hf Bool.false_ne_true) (fun h => absurd h hno_ne25) hml1
              · have hoom1 : hdr1.oom = 0#32 := hc
                clear hc
                have hres1 := hres hoom1
                have hso_ptr : hdr1.slice_off_ptr = hdr.slice_off_ptr :=
                  hok1.hdr_so.trans hok.hdr_so.symm
                have hml_so1 := blast_so_focus hok1.hdr_so hml1
                clear hml1
                rw [hso_ptr] at hml_so1
                have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok1.so_len]; exact hni_lt
                c0_hstraight
                let sliceOffs' := sliceOffs.set nodeIdx.toNat res
                have hok2 := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat res hok1
                refine hQ true hdr1 g1 sliceOffs' aw1 hts1 litsPool _ hok2 haig1 hext1
                  (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
                  (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
                  (fun _ => ⟨hoom1, ?_⟩) (fun h => absurd h hno_ne25) ?_
                · refine blastEvalInv_step hoom0 hinv hok2 haig1 hext1 hni_lt
                    (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
                    (by rw [hfr1.lits_len]; exact Nat.le_refl _)
                    (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
                    (fun _ _ => rfl) ?_
                  refine nodeDenotes_set_bool hnd_gt (by rw [← haig1.aig_len_eq]; exact hres1.1)
                    (fun assign => ?_) hni_so
                  have hraw := hres1.2 (atomAssign progBytes assign)
                  change g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec res) =
                    (g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec sa) ||
                      g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec sb)) at hraw
                  rw [hraw, hsa_get, hsb_get, hnd_a.2 assign, hnd_b.2 assign]
                  rfl
                · exact blast_so_unfocus hok1.hdr_so (by rw [hso_ptr]; assumption)
            · have hop_ne30 : op ≠ opGateOr := fun h => by
                apply hc; subst h; unfold opGateOr; decide
              clear hc; c0_hstraight; c0_hsplit
              · -- Branch 7: op == BV_OP_ITE (31)
                have hop31 : op = opIte := by unfold opIte; c0_bv_omega [hop_lt]
                clear hc
                have hno_op : u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
                    5 * nodeIdx.toNat) = opIte := by
                  rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop31
                have hite := parsed_node_ite hp hn_lt hno_op
                dsimp only at hite
                rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hb_eq, hc_eq] at hite
                rcases hite with
                  ⟨ha_lt_ni, hb_lt_ni, hc_lt_ni, ea, eb, ec, hga, hgb, hgc, hnd_ite⟩
                have ha_so : (BitVec.ofNat 32 a).toNat < sliceOffs.length := by
                  rw [hok.so_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega
                have hb_so : (BitVec.ofNat 32 b).toNat < sliceOffs.length := by
                  rw [hok.so_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt]; omega
                have hc_so : (BitVec.ofNat 32 c).toNat < sliceOffs.length := by
                  rw [hok.so_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc_lt]; omega
                have hnd_a := hinv.prefix_ok hoom0 a ha_lt_ni
                unfold NodeDenotes at hnd_a; rw [hga] at hnd_a
                have hnd_b := hinv.prefix_ok hoom0 b hb_lt_ni
                unfold NodeDenotes at hnd_b; rw [hgb] at hnd_b
                have hnd_c := hinv.prefix_ok hoom0 c hc_lt_ni
                unfold NodeDenotes at hnd_c; rw [hgc] at hnd_c
                have hml_so := blast_so_focus hok.hdr_so hm
                clear hm
                c0_hstraight
                have hml' := blast_so_unfocus hok.hdr_so hml_so
                clear hml_so
                have hml_aig := blast_aig_focus hok.hdr_aig hok.hdr_ht hml'
                clear hml'
                let sa := sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so
                let sb := sliceOffs[(BitVec.ofNat 32 b).toNat]'hb_so
                let sc := sliceOffs[(BitVec.ofNat 32 c).toNat]'hc_so
                have hsa_get : sa = sliceOffs.getD a 0#32 := by
                  dsimp only [sa]; rw [list_getD_eq_getElem _ 0#32]
                  simp [BitVec.toNat_ofNat]
                have hsb_get : sb = sliceOffs.getD b 0#32 := by
                  dsimp only [sb]; rw [list_getD_eq_getElem _ 0#32]
                  simp [BitVec.toNat_ofNat]
                have hsc_get : sc = sliceOffs.getD c 0#32 := by
                  dsimp only [sc]; rw [list_getD_eq_getElem _ 0#32]
                  simp [BitVec.toNat_ofNat]
                have hsa_bd : (sa >>> 1).toNat < hdr.aig_len.toNat := by
                  rw [haig.aig_len_eq, hsa_get]; exact hnd_a.1
                have hsb_bd : (sb >>> 1).toNat < hdr.aig_len.toNat := by
                  rw [haig.aig_len_eq, hsb_get]; exact hnd_b.1
                have hsc_bd : (sc >>> 1).toNat < hdr.aig_len.toNat := by
                  rw [haig.aig_len_eq, hsc_get]; exact hnd_c.1
                c0_call hIte
                refine ⟨hdr, g, aigWords, htSlots, _, haig,
                  fun _ => ⟨hsa_bd, hsb_bd, hsc_bd⟩, hml_aig, ?_⟩
                intro res hdr1 g1 aw1 hts1 m1 hfr1 hext1 _ haig1 _ _ hres hm1
                have hml1 := blast_aig_unfocus (hfr1.aig_ptr.trans hok.hdr_aig)
                  (hfr1.ht_ptr.trans hok.hdr_ht) hm1
                clear hm1
                have hok1 := bvWorkspaceOk_of_aigFrame hok hfr1 haig1
                have hml1_hdr := hml1
                rw [bvBlastMem_hdr_left] at hml1_hdr
                c0_hstraight
                clear hml1_hdr
                c0_hsplit
                · c0_hstraight
                  exact hQ false hdr1 g1 sliceOffs aw1 hts1 litsPool m1 hok1 haig1 hext1
                    (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
                    (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
                    (fun hf => absurd hf Bool.false_ne_true) (fun h => absurd h hno_ne25) hml1
                · have hoom1 : hdr1.oom = 0#32 := hc
                  clear hc
                  have hres1 := hres hoom1
                  have hso_ptr : hdr1.slice_off_ptr = hdr.slice_off_ptr :=
                    hok1.hdr_so.trans hok.hdr_so.symm
                  have hml_so1 := blast_so_focus hok1.hdr_so hml1
                  clear hml1
                  rw [hso_ptr] at hml_so1
                  have hni_so : nodeIdx.toNat < sliceOffs.length := by
                    rw [hok1.so_len]; exact hni_lt
                  c0_hstraight
                  let sliceOffs' := sliceOffs.set nodeIdx.toNat res
                  have hok2 := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat res hok1
                  refine hQ true hdr1 g1 sliceOffs' aw1 hts1 litsPool _ hok2 haig1 hext1
                    (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
                    (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
                    (fun _ => ⟨hoom1, ?_⟩) (fun h => absurd h hno_ne25) ?_
                  · refine blastEvalInv_step hoom0 hinv hok2 haig1 hext1 hni_lt
                      (hfr1.prog_ptr.trans hinv.prog_ptr_eq) hfr1.n_cwords hfr1.root_node
                      (by rw [hfr1.lits_len]; exact Nat.le_refl _)
                      (by rw [hfr1.lits_len]; exact hinv.lits_le_cap)
                      (fun _ _ => rfl) ?_
                    refine nodeDenotes_set_bool hnd_ite (by rw [← haig1.aig_len_eq]; exact hres1.1)
                      (fun assign => ?_) hni_so
                    have hraw := hres1.2 (atomAssign progBytes assign)
                    change g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec res) =
                      cond (g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec sa))
                        (g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec sb))
                        (g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec sc)) at hraw
                    rw [hraw, hsa_get, hsb_get, hsc_get,
                      hnd_a.2 assign, hnd_b.2 assign, hnd_c.2 assign]
                    rfl
                  · exact blast_so_unfocus hok1.hdr_so (by rw [hso_ptr]; assumption)
              · -- Branch 8: delegate to core / div_cpop / shift_mul
                have hop_ne31 : op ≠ opIte := fun h => by
                  apply hc; subst h; unfold opIte; decide
                clear hc
                have subCall :
                    (ret : Bool) → (hdr' : BVHdrState) → (g' : Aig) →
                    (sliceOffs' : List (BitVec 32)) → (aigWords' : List (BitVec 64)) →
                    (htSlots' litsPool' : List (BitVec 32)) → (m' : Mem 64) →
                    BVWorkspaceOk cfg hdr' atomBases sliceOffs' aigWords' htSlots' litsPool' →
                    AigInv hdr' g' aigWords' htSlots' → g ≤ g' →
                    hdr'.lits_len.toNat ≤ cfg.lits_cap → hdr'.prog_ptr = progPtr →
                    hdr'.n_cwords = hdr.n_cwords → hdr'.root_node = hdr.root_node →
                    (ret = true → hdr'.oom = 0#32 ∧ BlastEvalInv cfg progPtr progBytes vars cwords
                      nodes prog hdr' g' atomBases sliceOffs' aigWords' htSlots' litsPool'
                      (nodeIdx.toNat + 1)) →
                    (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr' atomBases
                      sliceOffs' aigWords' htSlots' litsPool' ⋆ R) m' →
                    Q (ret, ⟨⟩) m' :=
                  fun ret hdr' g' sliceOffs' aw' hts' lp' m' hok' haig' hext' hlc' hpp'
                    hnc' hrt' htr' hm' =>
                    hQ ret hdr' g' sliceOffs' aw' hts' lp' m' hok' haig' hext' hlc' hpp' hnc' hrt'
                      htr' (fun h => absurd h hno_ne25) hm'
                refine wp_join0 (fun ml => ml = m) ?_ ?_
                · intro _ ml hml; subst hml
                  c0_call hCore
                  exact ⟨cfg, progPtr, progBytes, vars, cwords, nodes, prog, hdr, g, atomBases,
                    sliceOffs, aigWords, htSlots, litsPool, R, rfl, hni_lt, hoom0, hinv, hm,
                    subCall⟩
                · intro J1 hJ1
                  c0_hsteps_nogrp
                  all_goals first
                    | exact hJ1 m rfl
                    | (refine wp_join0 (fun ml => ml = m) ?_ ?_
                       · intro _ ml hml; subst hml
                         c0_call hDivCpop
                         exact ⟨cfg, progPtr, progBytes, vars, cwords, nodes, prog, hdr, g,
                           atomBases, sliceOffs, aigWords, htSlots, litsPool, R, rfl, hni_lt, hoom0,
                           hinv, hm, subCall⟩
                       · intro J2 hJ2
                         c0_hsteps_nogrp
                         all_goals first
                           | exact hJ2 m rfl
                           | (c0_call hShiftMul
                              exact ⟨cfg, progPtr, progBytes, vars, cwords, nodes, prog, hdr, g,
                                atomBases, sliceOffs, aigWords, htSlots, litsPool, R, rfl, hni_lt,
                                hoom0, hinv, hm, subCall⟩))

/-! ## 4. `bv_eval_program_wp` -/

private theorem blastEvalInv_step_n_cwords_eq {hdr hdr' : BVHdrState}
    (h1 : hdr'.n_cwords = hdr.n_cwords) :
    hdr'.n_cwords.toNat = hdr.n_cwords.toNat := congrArg BitVec.toNat h1

theorem bv_eval_program_wp (Γ : Env)
    (hNode : ∀ xs m Q X, bvEvalNodeSpec xs m Q X →
      Γ "bv_eval_node" [i64, i32] [.bool] xs m Q X) :
    ∀ xs m Q X, bvEvalProgramSpec xs m Q X → Func.wp Γ bv_eval_program_body xs m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X
    ⟨cfg, progPtr, progBytes, vars, cwords, nodes, prog, hdr, g, atomBases, sliceOffs,
      aigWords, htSlots, litsPool, R, hh_eq, hoom0, hinv0, hm0, hQ⟩
  subst hh_eq
  have hok0 := hinv0.ws_ok
  have hm0_hdr := hm0
  rw [bvBlastMem_hdr_left] at hm0_hdr
  c0_hstraight
  clear hm0_hdr
  let State := Nat × BVHdrState × Aig × List (BitVec 32) × List (BitVec 64) ×
    List (BitVec 32) × List (BitVec 32)
  refine wp_while_state (α := State)
    (fun st => (BitVec.ofNat 32 st.1, ()))
    (fun st => cfg.n_nodes - st.1)
    (fun st ml =>
      let i := st.1
      let hdr' := st.2.1
      let g' := st.2.2.1
      let so' := st.2.2.2.1
      let aw' := st.2.2.2.2.1
      let hts' := st.2.2.2.2.2.1
      let lp' := st.2.2.2.2.2.2
      i ≤ cfg.n_nodes ∧
      hdr'.oom = 0#32 ∧
      hdr'.prog_ptr = progPtr ∧
      hdr'.n_cwords = hdr.n_cwords ∧
      hdr'.root_node = hdr.root_node ∧
      g ≤ g' ∧
      BlastEvalInv cfg progPtr progBytes vars cwords nodes prog hdr' g'
        atomBases so' aw' hts' lp' i ∧
      ((∀ k < cfg.n_nodes,
          u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * k) = opBConst) →
        g' = g ∧
        ∀ k < i,
          (so'.getD k 0#32).toNat =
            u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * k + 2) % 2) ∧
      (bytes progPtr progBytes ⋆
        bvBlastMem cfg hdr' atomBases so' aw' hts' lp' ⋆ R) ml)
    ?_ ?_
  · intro J hJ
    c0_hstraight
    exact hJ (0, hdr, g, sliceOffs, aigWords, htSlots, litsPool) m
      ⟨Nat.zero_le _, hoom0, hinv0.prog_ptr_eq, rfl, rfl, Aig.extends_rfl g, hinv0,
        fun _ => ⟨rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩, hm0⟩
  · rintro J ⟨i, hdr1, g1, so1, aw1, hts1, lp1⟩ ml
      ⟨hi_le, hoom1, hpp1, hnc1, hrt1, hext1, hinv1, hconst1, hml1⟩ ih
    have hi32 : i < 2 ^ 32 := Nat.lt_of_le_of_lt hi_le hok0.nn_lt
    have hml1_hdr := hml1
    rw [bvBlastMem_hdr_left] at hml1_hdr
    c0_hstraight
    clear hml1_hdr
    c0_hsplit
    · have hi_lt : i < cfg.n_nodes := by
        rw [hok0.hdr_nn, BitVec.toNat_ofNat] at hc
        have hc' : i % 2 ^ 32 < cfg.n_nodes % 2 ^ 32 := hc
        rw [Nat.mod_eq_of_lt hi32, Nat.mod_eq_of_lt hok0.nn_lt] at hc'
        exact hc'
      clear hc
      have hwb1 : cfg.work_base = cfg.work_base := rfl
      have hni32 : (BitVec.ofNat 32 i).toNat < cfg.n_nodes := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32]; exact hi_lt
      c0_call hNode
      refine ⟨cfg, progPtr, progBytes, vars, cwords, nodes, prog, hdr1, g1, atomBases, so1,
        aw1, hts1, lp1, R, hwb1, hni32, hoom1, ?_, hml1, ?_⟩
      · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32] using hinv1
      · intro ret hdr2 g2 so2 aw2 hts2 lp2 m2 hok2 haig2 hext2 _ hpp2 hnc2 hrt2 hret hbc2 hm2
        c0_hstraight
        c0_hsplit
        · have hret_true : ret = true := hc
          clear hc
          obtain ⟨hoom2, hinv2⟩ := hret hret_true
          have hi1_32 : i + 1 < 2 ^ 32 := Nat.lt_of_le_of_lt hi_lt hok0.nn_lt
          have hi_eq32 : BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
              show (1 : BitVec 32).toNat = 1 from rfl,
              Nat.mod_eq_of_lt hi32, Nat.mod_eq_of_lt hi1_32]
          c0_hstraight
          rw [hi_eq32]
          refine ih (i + 1, hdr2, g2, so2, aw2, hts2, lp2) m2 (by omega)
            ⟨hi_lt, hoom2, hpp2, hnc2.trans hnc1, hrt2.trans hrt1,
              Aig.extends_trans hext1 hext2, ?_, fun hall => ?_, hm2⟩
          · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32] using hinv2
          · obtain ⟨hg1, hprev1⟩ := hconst1 hall
            have hbc_i := hbc2 (by
              simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32,
                congrArg BitVec.toNat hnc1]
              exact hall i hi_lt)
            obtain ⟨_, hg2_eq, hso2_eq⟩ := hbc_i
            refine ⟨hg2_eq.trans hg1, fun k hk => ?_⟩
            rw [hso2_eq]
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32,
              congrArg BitVec.toNat hnc1]
            by_cases hki : k = i
            · subst hki
              rw [list_getD_set_self _ _ _ (by rw [hinv1.ws_ok.so_len]; exact hi_lt),
                BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega :
                  u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * k + 2) % 2 <
                    2 ^ 32)]
            · rw [list_getD_set_ne _ _ _ hki]
              exact hprev1 k (by omega)
        · have hret_false : ret = false := by
            cases ret <;> simp_all
          exact hQ false hdr2 g2 so2 aw2 hts2 lp2 m2 hok2 haig2 (Aig.extends_trans hext1 hext2)
            (hrt2.trans hrt1) (fun hf => absurd hf Bool.false_ne_true)
            (fun hall =>
              have htrue := hbc2 (by
                simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32,
                  congrArg BitVec.toNat hnc1]
                exact hall i hi_lt)
              absurd htrue.1 (by rw [hret_false]; decide))
            hm2
    · have hi_eq : i = cfg.n_nodes := by
        rw [hok0.hdr_nn, BitVec.toNat_ofNat] at hc
        have hc' : ¬ (i % 2 ^ 32 < cfg.n_nodes % 2 ^ 32) := hc
        rw [Nat.mod_eq_of_lt hi32, Nat.mod_eq_of_lt hok0.nn_lt] at hc'
        exact Nat.le_antisymm hi_le (Nat.le_of_not_lt hc')
      clear hc
      subst hi_eq
      c0_hstraight
      exact hQ true hdr1 g1 so1 aw1 hts1 lp1 ml hinv1.ws_ok hinv1.aig_inv hext1 hrt1
        (fun _ => ⟨hoom1, hinv1⟩) (fun hall => ⟨rfl, hconst1 hall⟩) hml1

end

end LeanQbe.T.Examples.Bitblast.Proof
