/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
import LeanQbe.T.Examples.Bitblast.Proof.DriverHelpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Evaluator WP Proofs (`Bitblast.Proof.Driver0`)

Proves `Γ`-parametric `Func.wp` soundness for the `5` evaluator functions of
`Bitblast.Src.Driver` against their canonical specs in `Bitblast.Proof.Specs`:
- `bv_eval_ops_shift_mul_wp` (`bvEvalSubSpec`)
- `bv_eval_ops_div_cpop_wp` (`bvEvalSubSpec`)
- `bv_eval_ops_core_wp` (`bvEvalSubSpec`)
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

/-! ## 1. Local Memory Access Helpers (`BVHdr`, `array i32`, `bvBlastMem`) -/

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

@[local c0_load] private theorem drv_load_n_nodes {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 84) = some s.n_nodes := load_hdr_n_nodes hm

@[local c0_load] private theorem drv_load_n_cwords {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 88) = some s.n_cwords := load_hdr_n_cwords hm

@[local c0_load] private theorem drv_load_oom {h : BitVec 64} {s : BVHdrState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 120) = some s.oom := load_hdr_oom hm

private theorem bv32_shl2_add_eq (base : BitVec 64) (idx : BitVec 32) :
    base + (idx.setWidth 64 <<< (2 : Nat)) = base + BitVec.ofNat 64 (4 * idx.toNat) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  have hi32 := idx.isLt
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : idx.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : idx.toNat * 2 ^ 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * idx.toNat < 2 ^ 64)]
  omega

@[local c0_load] private theorem drv_load_array32_shl2 {base : BitVec 64} {idx : BitVec 32}
    {sh : Nat} {xs : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hsh : sh = 2) (hi : idx.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m) :
    loadVal m i32 (base + (idx.setWidth 64 <<< sh)) = some (xs[idx.toNat]'hi) := by
  subst hsh; rw [bv32_shl2_add_eq]
  exact loadVal_array (t := i32) (by decide) hi hm

@[local c0_store] private theorem drv_store_array32_shl2 {base : BitVec 64} {idx : BitVec 32}
    {sh : Nat} {xs : List (BitVec 32)} (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64}
    (hsh : sh = 2) (hi : idx.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m) :
    storeOk m i32 (base + (idx.setWidth 64 <<< sh)) ∧
      (array (t := i32) base (xs.set idx.toNat v) ⋆ R)
        (storeMem m i32 (base + (idx.setWidth 64 <<< sh)) v) := by
  subst hsh; rw [bv32_shl2_add_eq]
  exact store_array (t := i32) v (by decide) hi hm


/-! ## 3. Trivial Stub Evaluator WPs (`bv_eval_ops_shift_mul`, `bv_eval_ops_div_cpop`) -/

public section

theorem bv_eval_ops_shift_mul_wp (Γ : Env) :
    ∀ xs m Q X, bvEvalSubSpec xs m Q X → Func.wp Γ bv_eval_ops_shift_mul_body xs m Q X := by
  rintro ⟨h, nodeIdx, ⟨⟩⟩ m Q X
    ⟨cfg, progPtr, progBytes, vars, cwords, nodes, prog, hdr, g, atomBases, sliceOffs,
      aigWords, htSlots, litsPool, R, _, _, hoom0, hinv, hm, hQ⟩
  c0_hsteps
  exact hQ false hdr g sliceOffs aigWords htSlots litsPool m hinv.ws_ok hinv.aig_inv
    (Aig.extends_rfl g) hinv.lits_le_cap hinv.prog_ptr_eq rfl rfl
    (fun hf => absurd hf Bool.false_ne_true) hm

theorem bv_eval_ops_div_cpop_wp (Γ : Env) :
    ∀ xs m Q X, bvEvalSubSpec xs m Q X → Func.wp Γ bv_eval_ops_div_cpop_body xs m Q X := by
  rintro ⟨h, nodeIdx, ⟨⟩⟩ m Q X
    ⟨cfg, progPtr, progBytes, vars, cwords, nodes, prog, hdr, g, atomBases, sliceOffs,
      aigWords, htSlots, litsPool, R, _, _, hoom0, hinv, hm, hQ⟩
  c0_hsteps
  exact hQ false hdr g sliceOffs aigWords htSlots litsPool m hinv.ws_ok hinv.aig_inv
    (Aig.extends_rfl g) hinv.lits_le_cap hinv.prog_ptr_eq rfl rfl
    (fun hf => absurd hf Bool.false_ne_true) hm


/-! ## 4. `bv_eval_ops_core_wp` -/

theorem bv_eval_ops_core_wp (Γ : Env)
    (hRead : ∀ xs m Q X, bvReadU32Spec xs m Q X →
      Γ "bv_read_u32" [i64, i64] [i32] xs m Q X)
    (hMkAnd : ∀ xs m Q X, bvMkAndSpec xs m Q X →
      Γ "bv_mk_and" [i64, i32, i32] [i32] xs m Q X)
    (hNot : ∀ xs m Q X, bvAigNotSpec xs m Q X →
      Γ "bv_aig_not" [i32] [i32] xs m Q X)
    (hBeq : ∀ xs m Q X, bvAigBeqSpec xs m Q X →
      Γ "bv_aig_beq" [i64, i32, i32] [i32] xs m Q X)
    (hLitsAlloc : ∀ xs m Q X, bvLitsAllocSpec xs m Q X →
      Γ "bv_lits_alloc" [i64, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvEvalSubSpec xs m Q X → Func.wp Γ bv_eval_ops_core_body xs m Q X := by
  rintro ⟨h, nodeIdx, ⟨⟩⟩ m Q X
    ⟨cfg, progPtr, progBytes, vars, cwords, nodes, prog, hdr, g, atomBases, sliceOffs,
      aigWords, htSlots, litsPool, R, rfl, hni_lt, hoom0, hinv, hm, hQ⟩
  have hok := hinv.ws_ok
  have hp := hinv.parsed
  have haig := hinv.aig_inv
  have hfit := hinv.prog_fit
  have hnw0 := drv_node_word0_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq hok.hdr_nv hok.nv_lt hni_lt
  have hnw1 := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq hok.hdr_nv hok.nv_lt hni_lt
    1 1 rfl (by decide)
  have hnw2 := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq hok.hdr_nv hok.nv_lt hni_lt
    2 2 rfl (by decide)
  have hnw3 := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq hok.hdr_nv hok.nv_lt hni_lt
    3 3 rfl (by decide)
  have hn_lt : nodeIdx.toNat < u32At progBytes 3 := hinv.nn_eq ▸ hni_lt
  have hm_bytes : (bytes progPtr progBytes ⋆
      (bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R)) m := sep_ac hm
  have hm_hdr : (bvHdrMem cfg.work_base hdr ⋆ (bytes progPtr progBytes ⋆
      (array (t := i32) (cfg.work_base + 128) atomBases ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
        (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
      array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
      region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
        (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
      array64 cfg.aig_ptr aigWords ⋆
      array (t := i32) cfg.ht_ptr htSlots ⋆
      array (t := i32) cfg.lits_ptr litsPool ⋆
      region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
        (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ R))) m := by
    rw [bvBlastMem_hdr_left] at hm; exact sep_ac hm
  have hfit' : hdr.prog_ptr.toNat + progBytes.length < 2 ^ 64 := by
    rw [hinv.prog_ptr_eq]; exact hfit
  have hm_bytes' : (bytes hdr.prog_ptr progBytes ⋆
      (bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R)) m := by
    rw [hinv.prog_ptr_eq]; exact hm_bytes
  c0_hstraight
  c0_call hRead
  refine ⟨progBytes, _, hfit', hnw0.2, hm_bytes', ?_⟩
  c0_hstraight
  c0_call hRead
  refine ⟨progBytes, _, hfit', hnw1.2, hm_bytes', ?_⟩
  c0_hstraight
  c0_call hRead
  refine ⟨progBytes, _, hfit', hnw2.2, hm_bytes', ?_⟩
  c0_hstraight
  c0_call hRead
  refine ⟨progBytes, _, hfit', hnw3.2, hm_bytes', ?_⟩
  c0_hstraight
  rw [hnw0.1, hnw1.1, hnw2.1, hnw3.1]
  clear hnw0 hnw1 hnw2 hnw3
  generalize hop_eq :
    u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * nodeIdx.toNat) = op
  generalize hw_eq :
    u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * nodeIdx.toNat + 1) = w
  generalize ha_eq :
    u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * nodeIdx.toNat + 2) = a
  generalize hb_eq :
    u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * nodeIdx.toNat + 3) = b
  have hop_lt : op < u32Bound := hop_eq ▸ u32At_lt ..
  have hw_lt : w < u32Bound := hw_eq ▸ u32At_lt ..
  have ha_lt : a < u32Bound := ha_eq ▸ u32At_lt ..
  have hb_lt : b < u32Bound := hb_eq ▸ u32At_lt ..
  unfold u32Bound at hop_lt hw_lt ha_lt hb_lt
  c0_hsplit
  · -- Case 1: op == BV_OP_VAR (0)
    have hop0 : op = opVar := by unfold opVar; c0_bv_omega [hop_lt]
    clear hc
    have hno_op : u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
        5 * nodeIdx.toNat) = opVar := by
      rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop0
    have hvar := parsed_node_var hp hn_lt hno_op
    dsimp only at hvar
    rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hw_eq] at hvar
    rcases hvar with ⟨ha_nv, hw_var, hnd_var⟩
    c0_call hLitsAlloc
    refine ⟨hdr, _, hm_hdr, ?_⟩
    have hl_cap := hinv.lits_le_cap
    by_cases hfit_lits : w ≤ cfg.lits_cap - hdr.lits_len.toNat
    · have hc_cond : hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
          (BitVec.ofNat 32 w).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat := by
        rw [hok.hdr_lcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hok.lcap_lt,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
        exact ⟨hoom0, hl_cap, hfit_lits⟩
      rw [ite_eq_left hc_cond]
      intro m1 hm1
      let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + BitVec.ofNat 32 w }
      have haig1 := aigInv_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) haig
      have hok1 := bvWorkspaceOk_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) hok
      have hoom1 : hdr1.oom = 0#32 := hoom0
      have hlits1_len : hdr1.lits_len.toNat = hdr.lits_len.toNat + w := by
        dsimp only [hdr1]
        have := hinv.lits_le_cap; have := hok.lcap_lt
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt,
          Nat.mod_eq_of_lt (by omega : hdr.lits_len.toNat + w < 2 ^ 32)]
      have hm1_blast : (bytes progPtr progBytes ⋆
          bvBlastMem cfg hdr1 atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m1 := by
        dsimp only [hdr1]; rw [bvBlastMem_hdr_left]; exact sep_ac hm1
      c0_hstraight
      c0_hsplit
      · exfalso
        have hoom1' : hdr.oom = 0#32 := hoom0
        rw [hoom1'] at hc; exact hc rfl
      · clear hc
        have hm1_ab : (array (t := i32) hdr1.atom_base_ptr atomBases ⋆
            (bvHdrMem cfg.work_base hdr1 ⋆ bytes progPtr progBytes ⋆
            region (cfg.work_base + BitVec.ofNat 64 (128 + 4 * cfg.n_vars))
              (cfg.atom_bytes - 4 * cfg.n_vars) ⋆
            array (t := i32) (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes)) sliceOffs ⋆
            region (cfg.work_base + BitVec.ofNat 64 (128 + cfg.atom_bytes + 4 * cfg.n_nodes))
              (cfg.slice_bytes - 4 * cfg.n_nodes) ⋆
            array64 cfg.aig_ptr aigWords ⋆
            array (t := i32) cfg.ht_ptr htSlots ⋆
            array (t := i32) cfg.lits_ptr litsPool ⋆
            region (cfg.lits_ptr + BitVec.ofNat 64 (4 * cfg.lits_cap))
              (cfg.lits_bytes - 4 * cfg.lits_cap) ⋆ R)) m1 := by
          rw [bvBlastMem_ab_focus] at hm1_blast; rw [hok1.hdr_ab]; exact sep_ac hm1_blast
        have ha32 : (BitVec.ofNat 32 a).toNat < atomBases.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt, hok1.ab_len]; exact ha_nv
        c0_hstraight
        have hab_eq : (atomBases.getD a 0#32).toNat = countAtoms progBytes a :=
          hinv.atom_bases_eq a ha_nv
        have hcnt_n := hinv.parsed.valid.atoms_ok
        have hcnt_a1 : countAtoms progBytes (a + 1) ≠ 0 ∧
            countAtoms progBytes (a + 1) ≤ countAtoms progBytes cfg.n_vars :=
          countAtoms_mono_ne_zero (by omega : a + 1 ≤ cfg.n_vars) (hinv.nv_eq ▸ hcnt_n)
        have hcnt_prev := countAtoms_prev_ne_zero hcnt_a1.1
        have hcnt_lt := countAtoms_lt progBytes (u32At progBytes 2)
        have ha_idx_get : atomBases[(BitVec.ofNat 32 a).toNat]'ha32 =
            atomBases.getD a 0#32 := by
          have ha_to : (BitVec.ofNat 32 a).toNat = a := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
          simp [List.getD_eq_getElem?_getD, hok1.ab_len, ha_nv, ha_to]
        refine wp_while_state (α := Nat × List (BitVec 32))
          (fun s => (BitVec.ofNat 32 s.1, ()))
          (fun s => w - s.1)
          (fun s ml => s.1 ≤ w ∧ s.2.length = cfg.lits_cap ∧
            (∀ p < hdr.lits_len.toNat, s.2.getD p 0#32 = litsPool.getD p 0#32) ∧
            (∀ p < s.1, s.2.getD (hdr.lits_len.toNat + p) 0#32 =
              BitVec.ofNat 32 (countAtoms progBytes a + p) <<< 1) ∧
            (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 atomBases sliceOffs aigWords
              htSlots s.2 ⋆ R) ml) ?_ ?_
        · intro J hJ
          c0_hsteps
          exact hJ (0, litsPool) m1 ⟨Nat.zero_le w, hok.lits_len, fun _ _ => rfl,
            fun _ hp => by omega, hm1_blast⟩
        · intro J ⟨j, lp⟩ ml ⟨hj_le, hlp_len, hagree, hset, hml⟩ ih
          dsimp only at hj_le hlp_len hagree hset
          c0_hstraight
          c0_hsplit
          · have hj_lt : j < w := by
              have hj32 : j < 2 ^ 32 := Nat.lt_of_le_of_lt hj_le hw_lt
              simp only [bv_c0, Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt hw_lt] at hc
              exact hc
            clear hc
            let valLit := ((atomBases[(BitVec.ofNat 32 a).toNat]'ha32 +
              BitVec.ofNat 32 j) <<< (1 : Nat))
            let lp' := lp.set (hdr.lits_len + BitVec.ofNat 32 j).toNat valLit
            have hidx_eq : (hdr.lits_len + BitVec.ofNat 32 j).toNat = hdr.lits_len.toNat + j := by
              have := hinv.lits_le_cap; have := hok.lcap_lt
              rw [BitVec.toNat_add, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : j < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : hdr.lits_len.toNat + j < 2 ^ 32)]
            have hidx_lt : (hdr.lits_len + BitVec.ofNat 32 j).toNat < lp.length := by
              rw [hlp_len, hidx_eq]; omega
            have hml_lits := blast_lits_focus hok1.hdr_lits hml
            clear hml
            c0_hstraight
            have hvalLit_eq : valLit = BitVec.ofNat 32 (countAtoms progBytes a + j) <<< 1 := by
              have hlt_a := hcnt_lt
              rw [← hinv.nv_eq] at hlt_a
              have := hcnt_prev.2.2; have := hcnt_a1.2
              unfold bvDimacsBound at hlt_a
              have hax : countAtoms progBytes a + j < 2 ^ 32 := by omega
              dsimp only [valLit]; rw [ha_idx_get]; congr 1; apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_add, hab_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : j < 2 ^ 32), Nat.mod_eq_of_lt hax]
            have hj_eq32 : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
                show (1 : BitVec 32).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : j < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 32)]
            rw [hj_eq32]
            refine ih (j + 1, lp') _ (by omega) ⟨by omega, by simp [lp', hlp_len],
              fun p hp_lt => ?_, fun p hp_lt => ?_,
              blast_lits_unfocus hok1.hdr_lits (by assumption)⟩
            · dsimp only [lp']; rw [list_getD_set_ne _ _ _ (by omega)]; exact hagree p hp_lt
            · dsimp only [lp']
              by_cases hpj : p = j
              · subst hpj; rw [hidx_eq, list_getD_set_self _ _ _ (by rw [hlp_len]; omega)]
                exact hvalLit_eq
              · rw [list_getD_set_ne _ _ _ (by omega)]; exact hset p (by omega)
          · have hj_eq : j = w := by
              have hj32 : j < 2 ^ 32 := Nat.lt_of_le_of_lt hj_le hw_lt
              simp only [bv_c0, Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt hw_lt] at hc
              exact Nat.le_antisymm hj_le (Nat.le_of_not_lt hc)
            clear hc
            have hml_so := blast_so_focus hok1.hdr_so hml
            clear hml
            have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok1.so_len]; exact hni_lt
            c0_hstraight
            let sliceOffs' := sliceOffs.set nodeIdx.toNat hdr.lits_len
            have hok2 := BVWorkspaceOk.set_litsPool hlp_len
              (BVWorkspaceOk.set_sliceOffs nodeIdx.toNat hdr.lits_len hok1)
            have hm_fin := blast_so_unfocus hok1.hdr_so (by assumption)
            have hl_cap' := hinv.lits_le_cap
            refine hQ true hdr1 g sliceOffs' aigWords htSlots lp _ hok2 haig1
              (Aig.extends_rfl g) (by rw [hlits1_len]; omega) hinv.prog_ptr_eq rfl rfl
              (fun _ => ⟨hoom1, ?_⟩) hm_fin
            refine blastEvalInv_step hoom0 hinv hok2 haig1 (Aig.extends_rfl g) hni_lt
              hinv.prog_ptr_eq rfl rfl (by rw [hlits1_len]; omega)
              (by rw [hlits1_len]; omega) hagree ?_
            refine nodeDenotes_set_bv hnd_var (by rw [hlits1_len]; omega)
              (fun k hk => ?_) (fun assign => ?_) (by rw [hok.so_len]; exact hni_lt)
            · have hset_w := hj_eq ▸ hset
              rw [hset_w k hk]
              have hlt_a := hcnt_lt
              rw [← hinv.nv_eq] at hlt_a
              have hax : countAtoms progBytes a + k < 2 ^ 31 := by
                have := hcnt_prev.2.2; have := hcnt_a1.2
                unfold bvDimacsBound at hlt_a; omega
              rw [bv32_shl1_atom_lsr1 hax, hinv.atoms_eq]
              have := hcnt_prev.2.2; have := hcnt_a1.2
              omega
            · have hk' : hdr.lits_len.toNat + w ≤ lp.length := by rw [hlp_len]; omega
              rw [sliceDenotes_iff hk']
              intro k hk
              have hset_w := hj_eq ▸ hset
              have hlt_a2 := hcnt_lt
              rw [← hinv.nv_eq] at hlt_a2
              rw [hset_w k hk, evalLit_shl1_atom g _ (by
                have := hcnt_prev.2.2; have := hcnt_a1.2
                unfold bvDimacsBound at hlt_a2; omega)]
              have ha_bound : 1 ≤ countAtoms progBytes a + k ∧
                  countAtoms progBytes a + k ≤ g.A := by
                have := countAtoms_pos_of_ne_zero (hinv.nv_eq ▸ hcnt_n)
                have hpos_a := countAtoms_mono_ne_zero (Nat.zero_le a) hcnt_prev.1
                simp only [countAtoms] at hpos_a
                have := hcnt_prev.2.2; have := hcnt_a1.2
                rw [hinv.atoms_eq]; omega
              rw [Aig.evalNode_atom g _ ha_bound.1 ha_bound.2,
                atomAssign_eq hcnt_n (hinv.nv_eq ▸ ha_nv) (by omega),
                bvExpr_var_getLsbD _ assign hk]
    · have hc_cond : ¬ (hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
          (BitVec.ofNat 32 w).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) := by
        rw [hok.hdr_lcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hok.lcap_lt,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
        omega
      rw [ite_eq_right hc_cond]
      dsimp only
      rw [ite_eq_right (fun h => absurd hoom0 h)]
      intro m1 hm1
      let hdr1 : BVHdrState := { hdr with oom := 1#32 }
      have hok1 := bvWorkspaceOk_set_oom 1#32 hok
      have haig1 := aigInv_set_oom 1#32 haig
      have hm1_blast : (bytes progPtr progBytes ⋆
          bvBlastMem cfg hdr1 atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m1 := by
        dsimp only [hdr1]; rw [bvBlastMem_hdr_left]; exact sep_ac hm1
      c0_hstraight
      c0_hsplit
      · clear hc
        c0_hstraight
        exact hQ false hdr1 g sliceOffs aigWords htSlots litsPool m1 hok1 haig1
          (Aig.extends_rfl g) hinv.lits_le_cap hinv.prog_ptr_eq rfl rfl
          (fun hf => absurd hf Bool.false_ne_true) hm1_blast
      · exfalso; cases hc
  · have hop_gt0 : 0 < op := by c0_bv_omega [hop_lt]
    clear hc; c0_hstraight; c0_hsplit
    · -- Case 2: op == BV_OP_CONST (1)
      have hop1 : op = opConst := by unfold opConst; c0_bv_omega [hop_lt]
      clear hc
      have hno_op : u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
          5 * nodeIdx.toNat) = opConst := by
        rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop1
      have hconst := parsed_node_const hp hn_lt hno_op
      dsimp only at hconst
      rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hw_eq] at hconst
      rcases hconst with ⟨hcw_bd, val, _, hconst_bits, hnd_const⟩
      c0_call hLitsAlloc
      refine ⟨hdr, _, hm_hdr, ?_⟩
      by_cases hfit_lits : w ≤ cfg.lits_cap - hdr.lits_len.toNat
      · have hc_cond : hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
            (BitVec.ofNat 32 w).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat := by
          rw [hok.hdr_lcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hok.lcap_lt,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
          exact ⟨hoom0, hinv.lits_le_cap, hfit_lits⟩
        rw [ite_eq_left hc_cond]
        intro m1 hm1
        let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + BitVec.ofNat 32 w }
        have haig1 := aigInv_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) haig
        have hok1 := bvWorkspaceOk_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) hok
        have hoom1 : hdr1.oom = 0#32 := hoom0
        have hlits1_len : hdr1.lits_len.toNat = hdr.lits_len.toNat + w := by
          dsimp only [hdr1]
          have := hinv.lits_le_cap; have := hok.lcap_lt
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt,
            Nat.mod_eq_of_lt (by omega : hdr.lits_len.toNat + w < 2 ^ 32)]
        have hm1_blast : (bytes progPtr progBytes ⋆
            bvBlastMem cfg hdr1 atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m1 := by
          dsimp only [hdr1]; rw [bvBlastMem_hdr_left]; exact sep_ac hm1
        c0_hstraight
        c0_hsplit
        · exfalso
          have hoom1' : hdr.oom = 0#32 := hoom0
          rw [hoom1'] at hc; exact hc rfl
        · clear hc
          c0_hstraight
          refine wp_while_state (α := Nat × BitVec 32 × List (BitVec 32))
            (fun s => (s.2.1, BitVec.ofNat 32 s.1, ()))
            (fun s => w - s.1)
            (fun s ml => s.1 ≤ w ∧
              (0 < s.1 → s.2.1.toNat =
                u32At progBytes (cwordsOff cfg.n_vars + a + (s.1 - 1) / 32)) ∧
              s.2.2.length = cfg.lits_cap ∧
              (∀ p < hdr.lits_len.toNat, s.2.2.getD p 0#32 = litsPool.getD p 0#32) ∧
              (∀ p < s.1, s.2.2.getD (hdr.lits_len.toNat + p) 0#32 =
                BitVec.ofNat 32 (if (u32At progBytes
                  (cwordsOff cfg.n_vars + a + p / 32)).testBit (p % 32) then 1 else 0)) ∧
              (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 atomBases sliceOffs aigWords
                htSlots s.2.2 ⋆ R) ml) ?_ ?_
          · intro J hJ
            c0_hsteps
            exact hJ (0, 0#32, litsPool) m1 ⟨Nat.zero_le w, fun h => by omega, hok.lits_len,
              fun _ _ => rfl, fun _ hp => by omega, hm1_blast⟩
          · intro J ⟨j, cw, lp⟩ ml ⟨hj_le, hcw_ok, hlp_len, hagree, hset, hml⟩ ih
            dsimp only at hj_le hcw_ok hlp_len hagree hset
            c0_hstraight
            c0_hsplit
            · have hj_lt : j < w := by
                have hj32 : j < 2 ^ 32 := Nat.lt_of_le_of_lt hj_le hw_lt
                simp only [bv_c0, Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt hw_lt] at hc
                exact hc
              clear hc
              have hj32 : j < 2 ^ 32 := Nat.lt_trans hj_lt hw_lt
              have hnw_pos : 0 < (w + 31) / 32 := by omega
              have hac_bd := hcw_bd hnw_pos
              have hjdiv_lt : j / 32 < (w + 31) / 32 := by omega
              have htot := hp.valid.total_len
              c0_hstraight
              refine wp_join_state1 (α := BitVec 32) (fun cw' => cw')
                (fun cw' ml' =>
                  cw'.toNat = u32At progBytes (cwordsOff cfg.n_vars + a + j / 32) ∧
                  (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 atomBases sliceOffs aigWords
                    htSlots lp ⋆ R) ml') ?_ ?_
              · intro J2 cw' ml' ⟨hcw'_eq, hml'⟩
                let litv := (cw' >>> ((BitVec.ofNat 32 j &&& 31).toNat % 32)) &&& 1
                let lp' := lp.set
                  (hdr.lits_len + BitVec.ofNat 32 j).toNat litv
                have hidx_eq : (hdr.lits_len + BitVec.ofNat 32 j).toNat =
                    hdr.lits_len.toNat + j := by
                  have := hinv.lits_le_cap; have := hok.lcap_lt
                  c0_bv_omega [hj32, hfit_lits]
                have hidx_lt : (hdr.lits_len + BitVec.ofNat 32 j).toNat < lp.length := by
                  rw [hlp_len, hidx_eq]; omega
                have hml_lits := blast_lits_focus hok1.hdr_lits hml'
                clear hml'
                c0_hstraight
                have hj_eq32 : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by
                  apply BitVec.eq_of_toNat_eq; c0_bv_omega [hj32]
                have hsh_eq : (BitVec.ofNat 32 j &&& 31).toNat % 32 = j % 32 := by
                  change (BitVec.ofNat 32 j &&& 31#32).toNat % 32 = j % 32
                  rw [bv32_and31_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32, Nat.mod_mod]
                have hlitv_eq : litv = BitVec.ofNat 32 (if (u32At progBytes
                    (cwordsOff cfg.n_vars + a + j / 32)).testBit (j % 32) then 1 else 0) := by
                  dsimp only [litv]
                  rw [hsh_eq]
                  change ((cw' >>> (j % 32)) &&& 1#32) = _
                  rw [bv32_bit_word, hcw'_eq]
                rw [hj_eq32]
                refine ih (j + 1, cw', lp') _ (by omega) ⟨by omega, fun _ => ?_,
                  by simp [lp', hlp_len], fun p hp_lt => ?_, fun p hp_lt => ?_,
                  blast_lits_unfocus hok1.hdr_lits (by assumption)⟩
                · have hdiv_eq : ((j + 1) - 1) / 32 = j / 32 := by omega
                  rw [hdiv_eq]; exact hcw'_eq
                · dsimp only [lp']; rw [list_getD_set_ne _ _ _ (by omega)]; exact hagree p hp_lt
                · dsimp only [lp']
                  by_cases hpj : p = j
                  · subst hpj; rw [hidx_eq, list_getD_set_self _ _ _ (by rw [hlp_len]; omega)]
                    exact hlitv_eq
                  · rw [list_getD_set_ne _ _ _ (by omega)]; exact hset p (by omega)
              · intro J2 hJ2
                c0_hstraight
                c0_hsplit
                · have hjmod : j % 32 = 0 := by
                    have h := congrArg BitVec.toNat hc
                    change (BitVec.ofNat 32 j &&& 31#32).toNat = (0#32 : BitVec 32).toNat at h
                    rw [bv32_and31_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32] at h
                    exact h
                  clear hc
                  have hml_hdr := hml
                  rw [bvBlastMem_hdr_left] at hml_hdr
                  c0_hstraight
                  clear hml_hdr
                  have hcwi_eq : ((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< 1) +
                      (BitVec.ofNat 32 a).setWidth 64 +
                        (BitVec.ofNat 32 j >>> 5).setWidth 64).toNat =
                      cwordsOff cfg.n_vars + a + j / 32 := by
                    have hnv_eq : hdr.n_vars = BitVec.ofNat 32 cfg.n_vars := hok.hdr_nv
                    have hnv_lt := hok.nv_lt
                    have hlsr : (BitVec.ofNat 32 j >>> 5).toNat = j / 32 := by
                      rw [bv32_lsr5_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32]
                    unfold cwordsOff
                    c0_bv_omega [hnv_eq, hnv_lt, ha_lt, hlsr, hjdiv_lt, hac_bd.1, hac_bd.2]
                  have hcwi_fit : 4 * (((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< 1) +
                      (BitVec.ofNat 32 a).setWidth 64 +
                      (BitVec.ofNat 32 j >>> 5).setWidth 64).toNat + 1) ≤ progBytes.length := by
                    rw [hcwi_eq]
                    have htot' := htot
                    rw [← hinv.nv_eq, ← hinv.nn_eq, ← hinv.nc_eq] at htot'
                    unfold cwordsOff
                    omega
                  rw [hinv.prog_ptr_eq]
                  c0_call hRead
                  refine ⟨progBytes,
                    bvBlastMem cfg hdr1 atomBases sliceOffs aigWords htSlots lp ⋆ R,
                    hfit, hcwi_fit, sep_ac hml, ?_⟩
                  rw [hcwi_eq]
                  let cw' := BitVec.ofNat 32 (u32At progBytes (cwordsOff cfg.n_vars + a + j / 32))
                  c0_hstraight
                  exact hJ2 cw' ml
                    ⟨by
                      dsimp only [cw']; rw [BitVec.toNat_ofNat]
                      exact Nat.mod_eq_of_lt (u32At_lt ..), hml⟩
                · have hjmod : j % 32 ≠ 0 := by
                    intro h0; apply hc; apply BitVec.eq_of_toNat_eq
                    change (BitVec.ofNat 32 j &&& 31#32).toNat = (0#32 : BitVec 32).toNat
                    rw [bv32_and31_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32, h0]; rfl
                  clear hc
                  have hj_pos : 0 < j := by omega
                  have hcw_eq : cw.toNat = u32At progBytes (cwordsOff cfg.n_vars + a + j / 32) := by
                    have hdiv : (j - 1) / 32 = j / 32 := by omega
                    rw [← hdiv]; exact hcw_ok hj_pos
                  c0_hstraight
                  exact hJ2 cw ml ⟨hcw_eq, hml⟩
            · have hj_eq : j = w := by
                have hj32 : j < 2 ^ 32 := Nat.lt_of_le_of_lt hj_le hw_lt
                simp only [bv_c0, Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt hw_lt] at hc
                exact Nat.le_antisymm hj_le (Nat.le_of_not_lt hc)
              clear hc
              have hml_so := blast_so_focus hok1.hdr_so hml
              clear hml
              have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok1.so_len]; exact hni_lt
              c0_hstraight
              let sliceOffs' := sliceOffs.set nodeIdx.toNat hdr.lits_len
              have hok2 := BVWorkspaceOk.set_litsPool hlp_len
                (BVWorkspaceOk.set_sliceOffs nodeIdx.toNat hdr.lits_len hok1)
              have hm_fin := blast_so_unfocus hok1.hdr_so (by assumption)
              have hl_cap' := hinv.lits_le_cap
              refine hQ true hdr1 g sliceOffs' aigWords htSlots lp _ hok2 haig1
                (Aig.extends_rfl g) (by rw [hlits1_len]; omega) hinv.prog_ptr_eq rfl rfl
                (fun _ => ⟨hoom1, ?_⟩) hm_fin
              refine blastEvalInv_step hoom0 hinv hok2 haig1 (Aig.extends_rfl g) hni_lt
                hinv.prog_ptr_eq rfl rfl (by rw [hlits1_len]; omega)
                (by rw [hlits1_len]; omega) hagree ?_
              refine nodeDenotes_set_bv hnd_const (by rw [hlits1_len]; omega)
                (fun k hk => ?_) (fun assign => ?_) (by rw [hok.so_len]; exact hni_lt)
              · have hset_w := hj_eq ▸ hset
                rw [hset_w k hk]
                cases ((u32At progBytes (cwordsOff cfg.n_vars + a + k / 32)).testBit (k % 32)) <;>
                  (simp; omega)
              · have hk' : hdr.lits_len.toNat + w ≤ lp.length := by rw [hlp_len]; omega
                rw [sliceDenotes_iff hk']
                intro k hk
                have hset_w := hj_eq ▸ hset
                rw [hset_w k hk, evalLit_bit01 g (atomAssign progBytes assign),
                  ← hconst_bits k hk]
                rfl
      · have hc_cond : ¬ (hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
            (BitVec.ofNat 32 w).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) := by
          rw [hok.hdr_lcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hok.lcap_lt,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
          omega
        rw [ite_eq_right hc_cond]
        dsimp only
        rw [ite_eq_right (fun h => absurd hoom0 h)]
        intro m1 hm1
        let hdr1 : BVHdrState := { hdr with oom := 1#32 }
        have hok1 := bvWorkspaceOk_set_oom 1#32 hok
        have haig1 := aigInv_set_oom 1#32 haig
        have hm1_blast : (bytes progPtr progBytes ⋆
            bvBlastMem cfg hdr1 atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m1 := by
          dsimp only [hdr1]; rw [bvBlastMem_hdr_left]; exact sep_ac hm1
        c0_hstraight
        c0_hsplit
        · clear hc
          c0_hstraight
          exact hQ false hdr1 g sliceOffs aigWords htSlots litsPool m1 hok1 haig1
            (Aig.extends_rfl g) hinv.lits_le_cap hinv.prog_ptr_eq rfl rfl
            (fun hf => absurd hf Bool.false_ne_true) hm1_blast
        · exfalso; cases hc
    · have hop_gt1 : 1 < op := by c0_bv_omega [hop_lt, hop_gt0]
      clear hc; c0_hstraight; c0_hsplit
      · -- Case 3: op == BV_OP_NOT (2)
        have hop2 : op = opNot := by unfold opNot; c0_bv_omega [hop_lt, hop_gt1]
        clear hc
        have hno_op : u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
            5 * nodeIdx.toNat) = opNot := by
          rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop2
        have hnot := parsed_node_not hp hn_lt hno_op
        dsimp only at hnot
        rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hw_eq] at hnot
        rcases hnot with ⟨ha_lt_ni, _, _, ea, hga, hnd_not⟩
        have hnda := hinv.prefix_ok hoom0 a ha_lt_ni
        unfold NodeDenotes at hnda
        rw [hga] at hnda
        dsimp only at hnda
        rcases hnda with ⟨ha_off_le, ha_bd, ha_sd⟩
        c0_call hLitsAlloc
        refine ⟨hdr, _, hm_hdr, ?_⟩
        by_cases hfit_lits : w ≤ cfg.lits_cap - hdr.lits_len.toNat
        · have hc_cond : hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
              (BitVec.ofNat 32 w).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat := by
            rw [hok.hdr_lcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hok.lcap_lt,
              BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
            exact ⟨hoom0, hinv.lits_le_cap, hfit_lits⟩
          rw [ite_eq_left hc_cond]
          intro m1 hm1
          let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + BitVec.ofNat 32 w }
          have haig1 := aigInv_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) haig
          have hok1 := bvWorkspaceOk_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) hok
          have hoom1 : hdr1.oom = 0#32 := hoom0
          have hlits1_len : hdr1.lits_len.toNat = hdr.lits_len.toNat + w := by
            dsimp only [hdr1]
            have := hinv.lits_le_cap; have := hok.lcap_lt
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt,
              Nat.mod_eq_of_lt (by omega : hdr.lits_len.toNat + w < 2 ^ 32)]
          have hm1_blast : (bytes progPtr progBytes ⋆
              bvBlastMem cfg hdr1 atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m1 := by
            dsimp only [hdr1]; rw [bvBlastMem_hdr_left]; exact sep_ac hm1
          c0_hstraight
          c0_hsplit
          · exfalso
            have hoom1' : hdr.oom = 0#32 := hoom0
            rw [hoom1'] at hc; exact hc rfl
          · clear hc
            have hm1_so := blast_so_focus hok1.hdr_so hm1_blast
            have ha_so : (BitVec.ofNat 32 a).toNat < sliceOffs.length := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt, hok1.so_len]
              exact Nat.lt_trans ha_lt_ni hni_lt
            c0_hstraight
            have hm1_blast' := blast_so_unfocus hok1.hdr_so hm1_so
            clear hm1_so
            have ha_get : sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so = sliceOffs.getD a 0#32 := by
              rw [list_getD_eq_getElem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
            let a_off := sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so
            have ha_off_le' : a_off.toNat + w ≤ hdr.lits_len.toNat := by
              dsimp only [a_off]; rw [ha_get]; exact ha_off_le
            refine wp_while_state (α := Nat × List (BitVec 32))
              (fun s => (BitVec.ofNat 32 s.1, ()))
              (fun s => w - s.1)
              (fun s ml => s.1 ≤ w ∧ s.2.length = cfg.lits_cap ∧
                (∀ p < hdr.lits_len.toNat, s.2.getD p 0#32 = litsPool.getD p 0#32) ∧
                (∀ p < s.1, s.2.getD (hdr.lits_len.toNat + p) 0#32 =
                  litsPool.getD (a_off.toNat + p) 0#32 ^^^ 1#32) ∧
                (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 atomBases sliceOffs aigWords
                  htSlots s.2 ⋆ R) ml) ?_ ?_
            · intro J hJ
              c0_hsteps
              exact hJ (0, litsPool) m1 ⟨Nat.zero_le w, hok.lits_len, fun _ _ => rfl,
                fun _ hp => by omega, hm1_blast'⟩
            · intro J ⟨j, lp⟩ ml ⟨hj_le, hlp_len, hagree, hset, hml⟩ ih
              dsimp only at hj_le hlp_len hagree hset
              c0_hstraight
              c0_hsplit
              · have hj_lt : j < w := by
                  have hj32 : j < 2 ^ 32 := Nat.lt_of_le_of_lt hj_le hw_lt
                  simp only [bv_c0, Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt hw_lt] at hc
                  exact hc
                clear hc
                have hj32 : j < 2 ^ 32 := Nat.lt_trans hj_lt hw_lt
                have ha_j_eq : (a_off + BitVec.ofNat 32 j).toNat = a_off.toNat + j := by
                  have := hinv.lits_le_cap; have := hok.lcap_lt
                  c0_bv_omega [hj32, ha_off_le']
                have ha_j_lt : (a_off + BitVec.ofNat 32 j).toNat < lp.length := by
                  rw [hlp_len, ha_j_eq]; have := hinv.lits_le_cap; omega
                have hml_lits := blast_lits_focus hok1.hdr_lits hml
                clear hml
                c0_hstraight
                c0_call hNot
                dsimp only [bvAigNotSpec]
                let srcLit := lp[(a_off + BitVec.ofNat 32 j).toNat]'ha_j_lt
                let lp' := lp.set (hdr.lits_len + BitVec.ofNat 32 j).toNat
                  (srcLit ^^^ 1#32)
                have hidx_eq : (hdr.lits_len + BitVec.ofNat 32 j).toNat =
                    hdr.lits_len.toNat + j := by
                  have := hinv.lits_le_cap; have := hok.lcap_lt
                  c0_bv_omega [hj32, hfit_lits]
                have hidx_lt : (hdr.lits_len + BitVec.ofNat 32 j).toNat < lp.length := by
                  rw [hlp_len, hidx_eq]; omega
                c0_hstraight
                have hsrc_eq : srcLit = litsPool.getD (a_off.toNat + j) 0#32 := by
                  dsimp only [srcLit]
                  rw [list_getD_eq_getElem _ 0#32, ha_j_eq]
                  exact hagree _ (by omega)
                have hj_eq32 : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by
                  apply BitVec.eq_of_toNat_eq; c0_bv_omega [hj32]
                rw [hj_eq32]
                refine ih (j + 1, lp') _ (by omega) ⟨by omega, by simp [lp', hlp_len],
                  fun p hp_lt => ?_, fun p hp_lt => ?_,
                  blast_lits_unfocus hok1.hdr_lits (by assumption)⟩
                · dsimp only [lp']; rw [list_getD_set_ne _ _ _ (by omega)]; exact hagree p hp_lt
                · dsimp only [lp']
                  by_cases hpj : p = j
                  · subst hpj; rw [hidx_eq, list_getD_set_self _ _ _ (by rw [hlp_len]; omega),
                      hsrc_eq]
                  · rw [list_getD_set_ne _ _ _ (by omega)]; exact hset p (by omega)
              · have hj_eq : j = w := by
                  have hj32 : j < 2 ^ 32 := Nat.lt_of_le_of_lt hj_le hw_lt
                  simp only [bv_c0, Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt hw_lt] at hc
                  exact Nat.le_antisymm hj_le (Nat.le_of_not_lt hc)
                clear hc
                have hml_so := blast_so_focus hok1.hdr_so hml
                clear hml
                have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok1.so_len]; exact hni_lt
                c0_hstraight
                let sliceOffs' := sliceOffs.set nodeIdx.toNat hdr.lits_len
                have hok2 := BVWorkspaceOk.set_litsPool hlp_len
                  (BVWorkspaceOk.set_sliceOffs nodeIdx.toNat hdr.lits_len hok1)
                have hm_fin := blast_so_unfocus hok1.hdr_so (by assumption)
                have hl_cap' := hinv.lits_le_cap
                refine hQ true hdr1 g sliceOffs' aigWords htSlots lp _ hok2 haig1
                  (Aig.extends_rfl g) (by rw [hlits1_len]; omega) hinv.prog_ptr_eq rfl rfl
                  (fun _ => ⟨hoom1, ?_⟩) hm_fin
                refine blastEvalInv_step hoom0 hinv hok2 haig1 (Aig.extends_rfl g) hni_lt
                  hinv.prog_ptr_eq rfl rfl (by rw [hlits1_len]; omega)
                  (by rw [hlits1_len]; omega) hagree ?_
                refine nodeDenotes_set_bv hnd_not (by rw [hlits1_len]; omega)
                  (fun k hk => ?_) (fun assign => ?_) (by rw [hok.so_len]; exact hni_lt)
                · have hset_w := hj_eq ▸ hset
                  rw [hset_w k hk, bv32_xor1_lsr1]
                  dsimp only [a_off]; rw [ha_get]
                  exact ha_bd k hk
                · have hk' : hdr.lits_len.toNat + w ≤ lp.length := by rw [hlp_len]; omega
                  rw [sliceDenotes_iff hk']
                  intro k hk
                  have hset_w := hj_eq ▸ hset
                  rw [hset_w k hk, evalLit_xor1, bvExpr_not_getLsbD _ assign hk]
                  have ha_sd_w := ha_sd assign
                  have hl_ok : (sliceOffs.getD a 0#32).toNat + w ≤ litsPool.length := by
                    rw [hok.lits_len]; have := hinv.lits_le_cap; omega
                  rw [sliceDenotes_iff hl_ok] at ha_sd_w
                  dsimp only [a_off]; rw [ha_get, ha_sd_w k hk]
        · have hc_cond : ¬ (hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
              (BitVec.ofNat 32 w).toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) := by
            rw [hok.hdr_lcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hok.lcap_lt,
              BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt]
            omega
          rw [ite_eq_right hc_cond]
          dsimp only
          rw [ite_eq_right (fun h => absurd hoom0 h)]
          intro m1 hm1
          let hdr1 : BVHdrState := { hdr with oom := 1#32 }
          have hok1 := bvWorkspaceOk_set_oom 1#32 hok
          have haig1 := aigInv_set_oom 1#32 haig
          have hm1_blast : (bytes progPtr progBytes ⋆
              bvBlastMem cfg hdr1 atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m1 := by
            dsimp only [hdr1]; rw [bvBlastMem_hdr_left]; exact sep_ac hm1
          c0_hstraight
          c0_hsplit
          · clear hc
            c0_hstraight
            exact hQ false hdr1 g sliceOffs aigWords htSlots litsPool m1 hok1 haig1
              (Aig.extends_rfl g) hinv.lits_le_cap hinv.prog_ptr_eq rfl rfl
              (fun hf => absurd hf Bool.false_ne_true) hm1_blast
          · exfalso; cases hc
      · have hop_ne2 : op ≠ opNot := fun h => by
          apply hc; subst h; unfold opNot; decide
        clear hc; c0_hstraight; c0_hsplit
        · -- Case 4: op == BV_OP_GETLSBD (17)
          have hop17 : op = opGetLsbD := by unfold opGetLsbD; c0_bv_omega [hop_lt]
          clear hc
          have hno_op : u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
              5 * nodeIdx.toNat) = opGetLsbD := by
            rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop17
          have hget := parsed_node_getlsbd hp hn_lt hno_op
          dsimp only at hget
          rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hb_eq, hw_eq] at hget
          rcases hget with ⟨_, ha_lt_ni, _, ea, hga, hnd_get⟩
          have ha_node_word := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq
            hok.hdr_nv hok.nv_lt
            (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega :
              (BitVec.ofNat 32 a).toNat < cfg.n_nodes)
            1#64 1 rfl (by decide)
          have hm_bytes : (bytes progPtr progBytes ⋆
              bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m := hm
          have hm_hdr' := hm
          rw [bvBlastMem_hdr_left] at hm_hdr'
          c0_hstraight
          clear hm_hdr'
          rw [hinv.prog_ptr_eq]
          c0_call hRead
          have hew_idx : (((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< 1) +
              hdr.n_cwords.setWidth 64) + (BitVec.ofNat 32 a).setWidth 64 * 5 + 1).toNat =
              nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * a + 1 := by
            simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] using ha_node_word.1
          have hew_fit : 4 * ((((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< 1) +
              hdr.n_cwords.setWidth 64) + (BitVec.ofNat 32 a).setWidth 64 * 5 + 1).toNat + 1) ≤
              progBytes.length := ha_node_word.2
          refine ⟨progBytes, bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R,
            hfit, hew_fit, sep_ac hm_bytes, ?_⟩
          rw [hew_idx]
          let ew := u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * a + 1)
          have hew_lt : ew < 2 ^ 32 := u32At_lt ..
          c0_hstraight
          refine wp_join_state1 (α := BitVec 32) (fun resLit => resLit)
            (fun resLit m' => m' = m ∧ (resLit >>> 1).toNat < g.A + 1 + g.nodes.size ∧
              ∀ assign : BVExpr.Assignment,
                g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec resLit) =
                  (ea.eval assign).getLsbD b) ?_ ?_
          · intro J resLit m' ⟨hm_eq, hbd_res, hev_res⟩
            subst hm_eq
            have hm_so := blast_so_focus hok.hdr_so hm
            have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok.so_len]; exact hni_lt
            c0_hstraight
            let sliceOffs' := sliceOffs.set nodeIdx.toNat resLit
            have hok' := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat resLit hok
            have hm_fin := blast_so_unfocus hok.hdr_so (by assumption)
            refine hQ true hdr g sliceOffs' aigWords htSlots litsPool _ hok' haig
              (Aig.extends_rfl g) hinv.lits_le_cap hinv.prog_ptr_eq rfl rfl
              (fun _ => ⟨hoom0, ?_⟩) hm_fin
            refine blastEvalInv_step hoom0 hinv hok' haig (Aig.extends_rfl g) hni_lt
              hinv.prog_ptr_eq rfl rfl (le_refl _) hinv.lits_le_cap (fun _ _ => rfl) ?_
            refine nodeDenotes_set_bool hnd_get hbd_res hev_res (by rw [hok.so_len]; exact hni_lt)
          · intro J hJ
            c0_hstraight
            c0_hsplit
            · have hb_ew : b < ew := by
                have hc' : b % 2 ^ 32 < ew % 2 ^ 32 := hc
                rw [Nat.mod_eq_of_lt hb_lt, Nat.mod_eq_of_lt hew_lt] at hc'
                exact hc'
              clear hc
              have hm_so := blast_so_focus hok.hdr_so hm
              have ha_so : (BitVec.ofNat 32 a).toNat < sliceOffs.length := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt, hok.so_len]
                exact Nat.lt_trans ha_lt_ni hni_lt
              c0_hstraight
              have hm_blast' := blast_so_unfocus hok.hdr_so hm_so
              clear hm_so
              have hnda := hinv.prefix_ok hoom0 a ha_lt_ni
              unfold NodeDenotes at hnda
              rw [hga] at hnda
              dsimp only at hnda
              rcases hnda with ⟨ha_off_le, ha_bd, ha_sd⟩
              have ha_get : sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so = sliceOffs.getD a 0#32 := by
                rw [list_getD_eq_getElem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
              let a_off := sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so
              have ha_off_le' : a_off.toNat + ew ≤ hdr.lits_len.toNat := by
                dsimp only [a_off]; rw [ha_get]; exact ha_off_le
              have ha_b_eq : (a_off + BitVec.ofNat 32 b).toNat = a_off.toNat + b := by
                have := hinv.lits_le_cap; have := hok.lcap_lt
                rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt,
                  Nat.mod_eq_of_lt (by omega)]
              have ha_b_lt : (a_off + BitVec.ofNat 32 b).toNat < litsPool.length := by
                rw [hok.lits_len, ha_b_eq]; dsimp only [a_off]; rw [ha_get]
                have := hinv.lits_le_cap; omega
              have hm_lits := blast_lits_focus hok.hdr_lits hm_blast'
              clear hm_blast'
              c0_hstraight
              let resLit := litsPool[(a_off + BitVec.ofNat 32 b).toNat]'ha_b_lt
              refine hJ resLit m ⟨rfl, ?_, fun assign => ?_⟩
              · dsimp only [resLit]; rw [list_getD_eq_getElem, ha_b_eq]
                dsimp only [a_off]; rw [ha_get]; exact ha_bd b hb_ew
              · dsimp only [resLit]; rw [list_getD_eq_getElem, ha_b_eq]
                dsimp only [a_off]; rw [ha_get]
                have ha_sd_w := ha_sd assign
                have hl_ok : (sliceOffs.getD a 0#32).toNat + ew ≤ litsPool.length := by
                  rw [hok.lits_len]; have := hinv.lits_le_cap; omega
                rw [sliceDenotes_iff hl_ok] at ha_sd_w
                exact ha_sd_w b hb_ew
            · have hb_ge : ew ≤ b := by
                have hc' : ¬ (b % 2 ^ 32 < ew % 2 ^ 32) := hc
                rw [Nat.mod_eq_of_lt hb_lt, Nat.mod_eq_of_lt hew_lt] at hc'
                exact Nat.le_of_not_lt hc'
              clear hc
              c0_hstraight
              refine hJ 0#32 m ⟨rfl, ?_, fun assign => ?_⟩
              · simp; omega
              · rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq,
                  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _)
                    (Nat.pow_le_pow_right (by omega) hb_ge))]
                simp [Aig.evalLit_zero]
        · have hop_ne17 : op ≠ opGetLsbD := fun h => by
            apply hc; subst h; unfold opGetLsbD; decide
          clear hc; c0_hstraight; c0_hsplit
          · -- Case 5: op == BV_OP_EQ (10)
            have hop10 : op = opEq := by unfold opEq; c0_bv_omega [hop_lt]
            clear hc
            have hno_op : u32At progBytes (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
                5 * nodeIdx.toNat) = opEq := by
              rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop10
            have heq := parsed_node_eq hp hn_lt hno_op
            dsimp only at heq
            rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hb_eq, hw_eq] at heq
            rcases heq with ⟨_, ha_lt_ni, hb_lt_ni, _, _, hewb_eq, ea, eb, hga, hgb, hnd_eq⟩
            have ha_node_word := drv_node_word_ok hp hinv.nv_eq hinv.nn_eq hinv.nc_eq
              hok.hdr_nv hok.nv_lt
              (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega :
                (BitVec.ofNat 32 a).toNat < cfg.n_nodes)
              1#64 1 rfl (by decide)
            have hm_bytes : (bytes progPtr progBytes ⋆
                bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m := hm
            have hm_hdr' := hm
            rw [bvBlastMem_hdr_left] at hm_hdr'
            c0_hstraight
            clear hm_hdr'
            rw [hinv.prog_ptr_eq]
            c0_call hRead
            have hew_idx : (((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< 1) +
                hdr.n_cwords.setWidth 64) + (BitVec.ofNat 32 a).setWidth 64 * 5 + 1).toNat =
                nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * a + 1 := by
              simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] using ha_node_word.1
            have hew_fit : 4 * ((((8 : BitVec 64) + (hdr.n_vars.setWidth 64 <<< 1) +
                hdr.n_cwords.setWidth 64) + (BitVec.ofNat 32 a).setWidth 64 * 5 + 1).toNat + 1) ≤
                progBytes.length := ha_node_word.2
            refine ⟨progBytes,
              bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R,
              hfit, hew_fit, sep_ac hm_bytes, ?_⟩
            rw [hew_idx]
            let ew := u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * a + 1)
            have hew_lt : ew < 2 ^ 32 := u32At_lt ..
            have hnda := hinv.prefix_ok hoom0 a ha_lt_ni
            unfold NodeDenotes at hnda; rw [hga] at hnda; dsimp only at hnda
            rcases hnda with ⟨ha_off_le, ha_bd, ha_sd⟩
            have hndb := hinv.prefix_ok hoom0 b hb_lt_ni
            unfold NodeDenotes at hndb; rw [hgb] at hndb; dsimp only at hndb
            rcases hndb with ⟨hb_off_le, hb_bd, hb_sd⟩
            have hm_so := blast_so_focus hok.hdr_so hm
            have ha_so : (BitVec.ofNat 32 a).toNat < sliceOffs.length := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt, hok.so_len]
              exact Nat.lt_trans ha_lt_ni hni_lt
            have hb_so : (BitVec.ofNat 32 b).toNat < sliceOffs.length := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt, hok.so_len]
              exact Nat.lt_trans hb_lt_ni hni_lt
            c0_hstraight
            have hm_blast' := blast_so_unfocus hok.hdr_so hm_so
            clear hm_so
            have ha_get : sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so = sliceOffs.getD a 0#32 := by
              rw [list_getD_eq_getElem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
            have hb_get : sliceOffs[(BitVec.ofNat 32 b).toNat]'hb_so = sliceOffs.getD b 0#32 := by
              rw [list_getD_eq_getElem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt]
            let a_off := sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so
            let b_off := sliceOffs[(BitVec.ofNat 32 b).toNat]'hb_so
            have ha_off_le' : a_off.toNat + ew ≤ hdr.lits_len.toNat := by
              dsimp only [a_off]; rw [ha_get]; exact ha_off_le
            have hb_off_le' : b_off.toNat + ew ≤ hdr.lits_len.toNat := by
              dsimp only [b_off]; rw [hb_get]; exact hb_off_le
            refine wp_while_state
              (α := Nat × BitVec 32 × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32))
              (fun s => (s.2.1, BitVec.ofNat 32 s.1, ()))
              (fun s => ew - s.1)
              (fun s ml =>
                s.1 ≤ ew ∧ s.2.2.1.oom = 0#32 ∧
                BVWorkspaceOk cfg s.2.2.1 atomBases sliceOffs s.2.2.2.2.1 s.2.2.2.2.2 litsPool ∧
                AigInv s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2 ∧
                g ≤ s.2.2.2.1 ∧
                s.2.2.1.prog_ptr = progPtr ∧ s.2.2.1.n_cwords = hdr.n_cwords ∧
                s.2.2.1.root_node = hdr.root_node ∧ s.2.2.1.lits_len = hdr.lits_len ∧
                (s.2.1 >>> 1).toNat < s.2.2.1.aig_len.toNat ∧
                (∀ assign : BVExpr.Assignment,
                  s.2.2.2.1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec s.2.1) =
                    decide (∀ p < s.1, (ea.eval assign).getLsbD p = (eb.eval assign).getLsbD p)) ∧
                (bytes progPtr progBytes ⋆ bvBlastMem cfg s.2.2.1 atomBases sliceOffs
                  s.2.2.2.2.1 s.2.2.2.2.2 litsPool ⋆ R) ml) ?_ ?_
            · intro J hJ
              c0_hsteps
              refine hJ (0, 1#32, hdr, g, aigWords, htSlots) m ⟨Nat.zero_le ew, hoom0, hok, haig,
                Aig.extends_rfl g, hinv.prog_ptr_eq, rfl, rfl, rfl, ?_, fun assign => ?_, hm_blast'⟩
              · dsimp only; rw [haig.aig_len_eq]; simp; omega
              · dsimp only; simp [Aig.evalLit_one]
            · intro J ⟨j, acc, hdr', g', aw', hts'⟩ ml
                ⟨hj_le, hoom', hok', haig', hext', hpp', hnc', hrt', hlits', hacc_lt, hacc_ev, hml⟩
                ih
              dsimp only at hj_le hoom' hok' haig' hext' hpp' hnc' hrt' hlits' hacc_lt
              dsimp only at hacc_ev hml
              c0_hstraight
              c0_hsplit
              · have hj_lt : j < ew := by
                  have hj32 : j < 2 ^ 32 := Nat.lt_of_le_of_lt hj_le hew_lt
                  have hc' : j % 2 ^ 32 < ew % 2 ^ 32 := hc
                  rw [Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt hew_lt] at hc'
                  exact hc'
                clear hc
                have hj32 : j < 2 ^ 32 := Nat.lt_trans hj_lt hew_lt
                have hl_cap := hinv.lits_le_cap
                have hlcap_lt := hok.lcap_lt
                have ha_j_eq : (a_off + BitVec.ofNat 32 j).toNat = a_off.toNat + j := by
                  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32,
                    Nat.mod_eq_of_lt (by omega)]
                have hb_j_eq : (b_off + BitVec.ofNat 32 j).toNat = b_off.toNat + j := by
                  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32,
                    Nat.mod_eq_of_lt (by omega)]
                have ha_j_lt : (a_off + BitVec.ofNat 32 j).toNat < litsPool.length := by
                  rw [hok.lits_len, ha_j_eq]; have := hinv.lits_le_cap; omega
                have hb_j_lt : (b_off + BitVec.ofNat 32 j).toNat < litsPool.length := by
                  rw [hok.lits_len, hb_j_eq]; have := hinv.lits_le_cap; omega
                have hl_ptr : hdr'.lits_ptr = hdr.lits_ptr :=
                  hok'.hdr_lits.trans hok.hdr_lits.symm
                have hml_lits := blast_lits_focus hok'.hdr_lits hml
                clear hml
                rw [hl_ptr] at hml_lits
                c0_hstraight
                rw [← hl_ptr] at hml_lits
                have hml' := blast_lits_unfocus hok'.hdr_lits hml_lits
                clear hml_lits
                have hml_aig := blast_aig_focus hok'.hdr_aig hok'.hdr_ht hml'
                clear hml'
                let la := litsPool[(a_off + BitVec.ofNat 32 j).toNat]'ha_j_lt
                let lb := litsPool[(b_off + BitVec.ofNat 32 j).toNat]'hb_j_lt
                have hla_lt : (la >>> 1).toNat < hdr'.aig_len.toNat := by
                  rw [haig'.aig_len_eq]; dsimp only [la]
                  rw [list_getD_eq_getElem _ 0#32, ha_j_eq]
                  dsimp only [a_off]; rw [ha_get]
                  have := hext'.1; have := hext'.2.1; have := ha_bd j hj_lt; omega
                have hlb_lt : (lb >>> 1).toNat < hdr'.aig_len.toNat := by
                  rw [haig'.aig_len_eq]; dsimp only [lb]
                  rw [list_getD_eq_getElem _ 0#32, hb_j_eq]
                  dsimp only [b_off]; rw [hb_get]
                  have := hext'.1; have := hext'.2.1; have := hb_bd j hj_lt; omega
                c0_call hBeq
                refine ⟨hdr', g', aw', hts', _, haig', fun _ => ⟨hla_lt, hlb_lt⟩, hml_aig, ?_⟩
                intro eqj hdr1 g1 aw1 hts1 m1 hfr1 hext1 _ haig1 _ _ heq_res hm1
                c0_call hMkAnd
                refine ⟨hdr1, g1, aw1, hts1, _, haig1, fun hoom1 => ?_, hm1, ?_⟩
                · have hacc1 : (acc >>> 1).toNat < hdr1.aig_len.toNat := by
                    rw [haig1.aig_len_eq]; rw [haig'.aig_len_eq] at hacc_lt
                    have := hext1.1; have := hext1.2.1; omega
                  exact ⟨hacc1, (heq_res hoom1).1⟩
                · intro acc' hdr2 g2 aw2 hts2 m2 hfr2 hext2 _ haig2 hoom_pr2 _ hand_res hm2
                  have hml2 := blast_aig_unfocus
                    (hfr2.aig_ptr.trans (hfr1.aig_ptr.trans hok'.hdr_aig))
                    (hfr2.ht_ptr.trans (hfr1.ht_ptr.trans hok'.hdr_ht)) hm2
                  clear hm2
                  have hok2 := bvWorkspaceOk_of_aigFrame
                    (bvWorkspaceOk_of_aigFrame hok' hfr1 haig1) hfr2 haig2
                  have hml2_hdr := hml2
                  rw [bvBlastMem_hdr_left] at hml2_hdr
                  c0_hstraight
                  clear hml2_hdr
                  have hext_g'2 : g' ≤ g2 := Aig.extends_trans hext1 hext2
                  have hext_g2 : g ≤ g2 := Aig.extends_trans hext' hext_g'2
                  have hpp2 : hdr2.prog_ptr = progPtr :=
                    hfr2.prog_ptr.trans (hfr1.prog_ptr.trans hpp')
                  have hnc2 : hdr2.n_cwords = hdr.n_cwords :=
                    hfr2.n_cwords.trans (hfr1.n_cwords.trans hnc')
                  have hrt2 : hdr2.root_node = hdr.root_node :=
                    hfr2.root_node.trans (hfr1.root_node.trans hrt')
                  have hlits2 : hdr2.lits_len = hdr.lits_len :=
                    hfr2.lits_len.trans (hfr1.lits_len.trans hlits')
                  c0_hsplit
                  · c0_hstraight
                    exact hQ false hdr2 g2 sliceOffs aw2 hts2 litsPool m2 hok2 haig2
                      hext_g2 (by rw [hlits2]; exact hinv.lits_le_cap) hpp2 hnc2 hrt2
                      (fun hf => absurd hf Bool.false_ne_true) hml2
                  · have hoom2 : hdr2.oom = 0#32 := hc
                    clear hc
                    have hoom1 : hdr1.oom = 0#32 :=
                      Classical.byContradiction fun hne => hoom_pr2 hne hoom2
                    have heq_ok := heq_res hoom1
                    have hand_ok := hand_res hoom2
                    have hj_eq32 : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by
                      apply BitVec.eq_of_toNat_eq
                      simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
                        show (1 : BitVec 32).toNat = 1 from rfl,
                        Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 32)]
                    c0_hstraight
                    rw [hj_eq32]
                    refine ih (j + 1, acc', hdr2, g2, aw2, hts2) m2 (by omega)
                      ⟨by omega, hoom2, hok2, haig2, hext_g2, hpp2, hnc2, hrt2, hlits2,
                        hand_ok.1, fun assign => ?_, hml2⟩
                    have ha_sd_w := ha_sd assign
                    have hla_ok : (sliceOffs.getD a 0#32).toNat + ew ≤ litsPool.length := by
                      rw [hok.lits_len]; have := hinv.lits_le_cap; omega
                    rw [sliceDenotes_iff hla_ok] at ha_sd_w
                    have hb_sd_w := hb_sd assign
                    have hlb_ok : (sliceOffs.getD b 0#32).toNat + ew ≤ litsPool.length := by
                      rw [hok.lits_len]; have := hinv.lits_le_cap; omega
                    rw [sliceDenotes_iff hlb_ok] at hb_sd_w
                    have hla_g : g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec la) =
                        (ea.eval assign).getLsbD j := by
                      dsimp only [la]; rw [list_getD_eq_getElem _ 0#32, ha_j_eq]
                      dsimp only [a_off]; rw [ha_get]; exact ha_sd_w j hj_lt
                    have hlb_g : g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec lb) =
                        (eb.eval assign).getLsbD j := by
                      dsimp only [lb]; rw [list_getD_eq_getElem _ 0#32, hb_j_eq]
                      dsimp only [b_off]; rw [hb_get]; exact hb_sd_w j hj_lt
                    have hla_g' : g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec la) =
                        (ea.eval assign).getLsbD j := by
                      rw [Aig.evalLit_extend_node hext' (by
                        dsimp only [la]; rw [list_getD_eq_getElem _ 0#32, ha_j_eq]
                        dsimp only [a_off]; rw [ha_get]; exact ha_bd j hj_lt)]
                      exact hla_g
                    have hlb_g' : g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec lb) =
                        (eb.eval assign).getLsbD j := by
                      rw [Aig.evalLit_extend_node hext' (by
                        dsimp only [lb]; rw [list_getD_eq_getElem _ 0#32, hb_j_eq]
                        dsimp only [b_off]; rw [hb_get]; exact hb_bd j hj_lt)]
                      exact hlb_g
                    have hacc_g1 : g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec acc) =
                        decide (∀ p < j,
                          (ea.eval assign).getLsbD p = (eb.eval assign).getLsbD p) := by
                      rw [Aig.evalLit_extend_node hext1
                        (by rw [haig'.aig_len_eq] at hacc_lt; exact hacc_lt)]
                      exact hacc_ev assign
                    have heqj_g1 : g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec eqj) =
                        ((ea.eval assign).getLsbD j == (eb.eval assign).getLsbD j) := by
                      have hraw := heq_ok.2 (atomAssign progBytes assign)
                      change g1.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec eqj) =
                        (g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec la) ==
                          g'.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec lb)) at hraw
                      rw [hraw, hla_g', hlb_g']
                    rw [hand_ok.2 (atomAssign progBytes assign), hacc_g1, heqj_g1]
                    by_cases h1 : ∀ p < j,
                        (ea.eval assign).getLsbD p = (eb.eval assign).getLsbD p <;>
                      by_cases h2 : (ea.eval assign).getLsbD j = (eb.eval assign).getLsbD j
                    · rw [decide_eq_true h1,
                        show ((ea.eval assign).getLsbD j == (eb.eval assign).getLsbD j) = true
                          from beq_iff_eq.mpr h2]
                      dsimp only
                      rw [Bool.and_true, eq_comm, decide_eq_true_eq]
                      intro p hp
                      by_cases hpj : p = j
                      · subst hpj; exact h2
                      · exact h1 p (by omega)
                    · rw [decide_eq_true h1,
                        show ((ea.eval assign).getLsbD j == (eb.eval assign).getLsbD j) = false
                          from by simp [h2]]
                      dsimp only
                      rw [Bool.and_false, eq_comm, decide_eq_false_iff_not]
                      exact fun h => h2 (h j (by omega))
                    · rw [decide_eq_false h1]
                      dsimp only
                      rw [Bool.false_and, eq_comm, decide_eq_false_iff_not]
                      exact fun h => h1 (fun p hp => h p (by omega))
                    · rw [decide_eq_false h1]
                      dsimp only
                      rw [Bool.false_and, eq_comm, decide_eq_false_iff_not]
                      exact fun h => h1 (fun p hp => h p (by omega))
              · have hj_eq : j = ew := by
                  have hj32 : j < 2 ^ 32 := Nat.lt_of_le_of_lt hj_le hew_lt
                  have hc' : ¬ (j % 2 ^ 32 < ew % 2 ^ 32) := hc
                  rw [Nat.mod_eq_of_lt hj32, Nat.mod_eq_of_lt hew_lt] at hc'
                  exact Nat.le_antisymm hj_le (Nat.le_of_not_lt hc')
                clear hc
                have hso_ptr : hdr'.slice_off_ptr = hdr.slice_off_ptr :=
                  hok'.hdr_so.trans hok.hdr_so.symm
                have hml_so := blast_so_focus hok'.hdr_so hml
                clear hml
                rw [hso_ptr] at hml_so
                have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok'.so_len]; exact hni_lt
                c0_hstraight
                let sliceOffs' := sliceOffs.set nodeIdx.toNat acc
                have hok2 := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat acc hok'
                refine hQ true hdr' g' sliceOffs' aw' hts' litsPool _ hok2 haig' hext'
                  (by rw [hlits']; exact hinv.lits_le_cap) hpp' hnc' hrt'
                  (fun _ => ⟨hoom', ?_⟩) ?_
                · refine blastEvalInv_step hoom0 hinv hok2 haig' hext' hni_lt hpp' hnc' hrt'
                    (by rw [hlits']; exact Nat.le_refl _) (by rw [hlits']; exact hinv.lits_le_cap)
                    (fun _ _ => rfl) ?_
                  refine nodeDenotes_set_bool hnd_eq ?_ (fun assign => ?_)
                    (by rw [hok.so_len]; exact hni_lt)
                  · rw [← haig'.aig_len_eq]; exact hacc_lt
                  · rw [bvLogical_lit_eq_eval, hacc_ev assign, hj_eq]
                · exact blast_so_unfocus hok'.hdr_so (by rw [hso_ptr]; assumption)
          · clear hc
            c0_hstraight
            exact hQ false hdr g sliceOffs aigWords htSlots litsPool m hok haig
              (Aig.extends_rfl g) hinv.lits_le_cap hinv.prog_ptr_eq rfl rfl
              (fun hf => absurd hf Bool.false_ne_true) hm

end

end LeanQbe.T.Examples.Bitblast.Proof
