/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
import LeanQbe.T.Examples.Bitblast.Proof.DriverHelpers
import LeanQbe.T.Examples.Bitblast.Proof.Driver0Helpers
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
  have hop_lt : op < u32Bound := hop_eq ▸ u32At_lt ..
  have hw_lt : w < u32Bound := hw_eq ▸ u32At_lt ..
  have ha_lt : a < u32Bound := ha_eq ▸ u32At_lt ..
  have hb_lt : b < u32Bound := hb_eq ▸ u32At_lt ..
  unfold u32Bound at hop_lt hw_lt ha_lt hb_lt
  c0_hsplit
  · -- Case 1: op == BV_OP_VAR (0)
    have hop0 : op = opVar := by unfold opVar; c0_bv_omega [hop_lt]
    clear hc
    have hvar := parsed_node_var hp hn_lt (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop0)
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
        have ha32 : (BitVec.ofNat 32 a).toNat < atomBases.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt, hok1.ab_len]; exact ha_nv
        c0_hstraight
        have hab_eq := hinv.atom_bases_eq a ha_nv
        have hcnt_a1 := countAtoms_mono_ne_zero (by omega : a + 1 ≤ cfg.n_vars)
          (hinv.nv_eq ▸ hinv.parsed.valid.atoms_ok)
        have hcnt_prev := countAtoms_prev_ne_zero hcnt_a1.1
        have hcnt_lt : countAtoms progBytes cfg.n_vars < bvDimacsBound :=
          hinv.nv_eq ▸ countAtoms_lt progBytes (u32At progBytes 2)
        have ha_idx_get : atomBases[(BitVec.ofNat 32 a).toNat]'ha32 = atomBases.getD a 0#32 := by
          rw [list_getD_eq_getElem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
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
            obtain ⟨hidx_eq, hidx_lt, hj_eq32, hagree', hset'⟩ := drv0_var_step ha32 ha_idx_get
              hab_eq hinv.lits_le_cap hok.lcap_lt hfit_lits hj_lt hw_lt hlp_len hcnt_a1.2 hw_var
              hcnt_prev.2.2.symm hcnt_lt hagree hset rfl
            have hml_lits := blast_lits_focus hok1.hdr_lits hml; clear hml
            c0_hstraight; rw [hj_eq32]
            exact ih (j + 1, _) _ (by omega) ⟨by omega, by simp [hlp_len], hagree', hset',
              blast_lits_unfocus hok1.hdr_lits (by assumption)⟩
          · have hj_eq := drv0_loop_eq hj_le hw_lt hc; clear hc
            have hml_so := blast_so_focus hok1.hdr_so hml; clear hml
            have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok1.so_len]; exact hni_lt
            c0_hstraight
            exact drv0_var_post hoom0 hni_lt hok haig hinv hfit_lits ha_nv hw_var hnd_var rfl
              hlits1_len hlp_len hagree (hj_eq ▸ hset)
              (blast_so_unfocus hok1.hdr_so (by assumption)) hQ
    · rw [ite_eq_right (drv0_lits_alloc_oom_cond hok hw_lt hfit_lits)]; dsimp only
      rw [ite_eq_right (fun h => absurd hoom0 h)]; intro m1 hm1
      have hm1_blast : (bytes progPtr progBytes ⋆
          bvBlastMem cfg { hdr with oom := 1#32 } atomBases sliceOffs
            aigWords htSlots litsPool ⋆ R) m1 := by
        rw [bvBlastMem_hdr_left]; exact sep_ac hm1
      c0_hstraight; c0_hsplit
      · clear hc; c0_hstraight; exact drv0_oom_close hok haig hinv hm1_blast hQ
      · exfalso; cases hc
  · have hop_gt0 : 0 < op := by c0_bv_omega [hop_lt]
    clear hc; c0_hstraight; c0_hsplit
    · -- Case 2: op == BV_OP_CONST (1)
      have hop1 : op = opConst := by unfold opConst; c0_bv_omega [hop_lt]
      clear hc
      have hconst := parsed_node_const hp hn_lt
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
              have hj32 : j < 2 ^ 32 := Nat.lt_trans hj_lt hw_lt
              c0_hstraight
              refine wp_join_state1 (α := BitVec 32) (fun cw' => cw')
                (fun cw' ml' =>
                  cw'.toNat = u32At progBytes (cwordsOff cfg.n_vars + a + j / 32) ∧
                  (bytes progPtr progBytes ⋆ bvBlastMem cfg hdr1 atomBases sliceOffs aigWords
                    htSlots lp ⋆ R) ml') ?_ ?_
              · intro J2 cw' ml' ⟨hcw'_eq, hml'⟩
                obtain ⟨hidx_eq, hidx_lt, hj_eq32, hcw_next, hagree', hset'⟩ := drv0_const_step_set
                  hok hinv.lits_le_cap hfit_lits hj_lt hw_lt hlp_len hcw'_eq hagree hset
                have hml_lits := blast_lits_focus hok1.hdr_lits hml'; clear hml'
                c0_hstraight; rw [hj_eq32]
                exact ih (j + 1, cw', _) _ (by omega) ⟨by omega, hcw_next, by simp [hlp_len],
                  hagree', hset', blast_lits_unfocus hok1.hdr_lits (by assumption)⟩
              · intro J2 hJ2; c0_hstraight; c0_hsplit
                · clear hc; have hml_hdr := hml; rw [bvBlastMem_hdr_left] at hml_hdr
                  c0_hstraight; clear hml_hdr
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
              have hml_so := blast_so_focus hok1.hdr_so hml; clear hml
              have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok1.so_len]; exact hni_lt
              c0_hstraight
              exact drv0_const_post hoom0 hni_lt hok haig hinv hfit_lits hconst_bits hnd_const rfl
                hlits1_len hlp_len hagree (hj_eq ▸ hset)
                (blast_so_unfocus hok1.hdr_so (by assumption)) hQ
      · rw [ite_eq_right (drv0_lits_alloc_oom_cond hok hw_lt hfit_lits)]; dsimp only
        rw [ite_eq_right (fun h => absurd hoom0 h)]; intro m1 hm1
        have hm1_blast : (bytes progPtr progBytes ⋆
            bvBlastMem cfg { hdr with oom := 1#32 } atomBases sliceOffs
              aigWords htSlots litsPool ⋆ R) m1 := by
          rw [bvBlastMem_hdr_left]; exact sep_ac hm1
        c0_hstraight; c0_hsplit
        · clear hc; c0_hstraight; exact drv0_oom_close hok haig hinv hm1_blast hQ
        · exfalso; cases hc
    · have hop_gt1 : 1 < op := by c0_bv_omega [hop_lt, hop_gt0]
      clear hc; c0_hstraight; c0_hsplit
      · -- Case 3: op == BV_OP_NOT (2)
        have hop2 : op = opNot := by unfold opNot; c0_bv_omega [hop_lt, hop_gt1]
        clear hc
        have hnot := parsed_node_not hp hn_lt
          (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop2)
        dsimp only at hnot; rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hw_eq] at hnot
        rcases hnot with ⟨ha_lt_ni, _, _, ea, hga, hnd_not⟩
        have hnda := hinv.prefix_ok hoom0 a ha_lt_ni
        unfold NodeDenotes at hnda; rw [hga] at hnda; dsimp only at hnda
        rcases hnda with ⟨ha_off_le, ha_bd, ha_sd⟩
        c0_call hLitsAlloc; refine ⟨hdr, _, hm_hdr, ?_⟩
        by_cases hfit_lits : w ≤ cfg.lits_cap - hdr.lits_len.toNat
        · have ⟨hc_cond, hlits1_len⟩ := drv0_lits_alloc_cond_ok hok hoom0 hinv.lits_le_cap
            hw_lt hfit_lits
          rw [ite_eq_left hc_cond]; intro m1 hm1
          let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + BitVec.ofNat 32 w }
          have hok1 := bvWorkspaceOk_set_litsLen (hdr.lits_len + BitVec.ofNat 32 w) hok
          have hm1_blast : (bytes progPtr progBytes ⋆
              bvBlastMem cfg hdr1 atomBases sliceOffs aigWords htSlots litsPool ⋆ R) m1 := by
            dsimp only [hdr1]; rw [bvBlastMem_hdr_left]; exact sep_ac hm1
          c0_hstraight; c0_hsplit
          · exfalso; exact hc hoom0
          · clear hc; have hm1_so := blast_so_focus hok1.hdr_so hm1_blast
            have ha_so : (BitVec.ofNat 32 a).toNat < sliceOffs.length := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt, hok1.so_len]
              exact Nat.lt_trans ha_lt_ni hni_lt
            c0_hstraight; have hm1_blast' := blast_so_unfocus hok1.hdr_so hm1_so; clear hm1_so
            have ha_get : sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so = sliceOffs.getD a 0#32 := by
              rw [list_getD_eq_getElem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
            let a_off := sliceOffs[(BitVec.ofNat 32 a).toNat]'ha_so
            have ha_off_le' : a_off.toNat + w ≤ hdr.lits_len.toNat := by
              dsimp only [a_off]; rw [ha_get]; exact ha_off_le
            refine wp_while_state (α := Nat × List (BitVec 32))
              (fun s => (BitVec.ofNat 32 s.1, ())) (fun s => w - s.1)
              (drv0NotInv cfg progPtr progBytes hdr hdr1 atomBases sliceOffs
                aigWords htSlots litsPool R w a_off) ?_ ?_
            · intro J hJ; c0_hsteps
              exact hJ (0, litsPool) m1 ⟨Nat.zero_le w, hok.lits_len, fun _ _ => rfl,
                fun _ hp => by omega, hm1_blast'⟩
            · intro J ⟨j, lp⟩ ml ⟨hj_le, hlp_len, hagree, hset, hml⟩ ih
              c0_hstraight; c0_hsplit
              · have hj_lt := drv0_loop_lt hj_le hw_lt hc; clear hc
                obtain ⟨ha_j_lt, hidx_eq, hidx_lt, hj_eq32, hagree', hset'⟩ := drv0_not_step hok
                  hinv.lits_le_cap hfit_lits hj_lt hw_lt ha_off_le' hlp_len hagree hset
                have hml_lits := blast_lits_focus hok1.hdr_lits hml; clear hml
                c0_hstraight; c0_call hNot; dsimp only [bvAigNotSpec]; c0_hstraight
                rw [hj_eq32]
                exact ih (j + 1, _) _ (by omega) ⟨by omega, by simp [hlp_len], hagree', hset',
                  blast_lits_unfocus hok1.hdr_lits (by assumption)⟩
              · have hj_eq := drv0_loop_eq hj_le hw_lt hc; clear hc
                have hml_so := blast_so_focus hok1.hdr_so hml; clear hml
                have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok1.so_len]; exact hni_lt
                c0_hstraight
                exact drv0_not_post hoom0 hni_lt hok haig hinv hfit_lits ha_get ha_bd ha_sd
                  hnd_not rfl hlits1_len hlp_len hagree (hj_eq ▸ hset) ha_off_le
                  (blast_so_unfocus hok1.hdr_so (by assumption)) hQ
        · rw [ite_eq_right (drv0_lits_alloc_oom_cond hok hw_lt hfit_lits)]; dsimp only
          rw [ite_eq_right (fun h => absurd hoom0 h)]; intro m1 hm1
          have hm1_blast : (bytes progPtr progBytes ⋆
              bvBlastMem cfg { hdr with oom := 1#32 } atomBases sliceOffs
                aigWords htSlots litsPool ⋆ R) m1 := by
            rw [bvBlastMem_hdr_left]; exact sep_ac hm1
          c0_hstraight; c0_hsplit
          · clear hc; c0_hstraight; exact drv0_oom_close hok haig hinv hm1_blast hQ
          · exfalso; cases hc
      · have hop_ne2 : op ≠ opNot := fun h => by apply hc; subst h; unfold opNot; decide
        clear hc; c0_hstraight; c0_hsplit
        · -- Case 4: op == BV_OP_GETLSBD (17)
          have hop17 : op = opGetLsbD := by unfold opGetLsbD; c0_bv_omega [hop_lt]
          clear hc
          have hget := parsed_node_getlsbd hp hn_lt
            (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop17)
          dsimp only at hget; rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hb_eq, hw_eq] at hget
          rcases hget with ⟨_, ha_lt_ni, _, ea, hga, hnd_get⟩
          obtain ⟨hew_idx, hew_fit⟩ := drv0_node_width_read hinv hok ha_lt ha_lt_ni hni_lt
          have hm_hdr' := hm; rw [bvBlastMem_hdr_left] at hm_hdr'
          c0_hstraight; clear hm_hdr'; rw [hinv.prog_ptr_eq]; c0_call hRead
          refine ⟨progBytes, bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R,
            hfit, hew_fit, sep_ac hm, ?_⟩
          rw [hew_idx]
          let ew := u32At progBytes (nodesOff cfg.n_vars hdr.n_cwords.toNat + 5 * a + 1)
          have hew_lt : ew < 2 ^ 32 := u32At_lt ..
          c0_hstraight
          refine wp_join_state1 (α := BitVec 32) (fun resLit => resLit)
            (fun resLit m' => m' = m ∧ (resLit >>> 1).toNat < g.A + 1 + g.nodes.size ∧
              ∀ assign : BVExpr.Assignment,
                g.evalLit (atomAssign progBytes assign) (UInt32.ofBitVec resLit) =
                  (ea.eval assign).getLsbD b) ?_ ?_
          · intro J resLit m' ⟨hm_eq, hbd_res, hev_res⟩; subst hm_eq
            have hm_so := blast_so_focus hok.hdr_so hm
            have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok.so_len]; exact hni_lt
            c0_hstraight
            have hok' := BVWorkspaceOk.set_sliceOffs nodeIdx.toNat resLit hok
            refine hQ true hdr g _ aigWords htSlots litsPool _ hok' haig (Aig.extends_rfl g)
              hinv.lits_le_cap hinv.prog_ptr_eq rfl rfl (fun _ => ⟨hoom0, ?_⟩)
              (blast_so_unfocus hok.hdr_so (by assumption))
            refine blastEvalInv_step hoom0 hinv hok' haig (Aig.extends_rfl g) hni_lt
              hinv.prog_ptr_eq rfl rfl (le_refl _) hinv.lits_le_cap (fun _ _ => rfl)
              (nodeDenotes_set_bool hnd_get hbd_res hev_res (hok.so_len ▸ hni_lt))
          · intro J hJ; c0_hstraight; c0_hsplit
            · have hb_ew := drv0_lt_of_mod hb_lt hew_lt hc; clear hc
              have hm_so := blast_so_focus hok.hdr_so hm
              have ha_so : (BitVec.ofNat 32 a).toNat < sliceOffs.length := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt, hok.so_len]
                exact Nat.lt_trans ha_lt_ni hni_lt
              c0_hstraight; have hm_blast' := blast_so_unfocus hok.hdr_so hm_so; clear hm_so
              obtain ⟨ha_b_lt, hbd, hev⟩ :=
                drv0_getlsbd_lt_res hinv hok hoom0 ha_lt hb_lt ha_lt_ni hga hb_ew ha_so
              have hm_lits := blast_lits_focus hok.hdr_lits hm_blast'; clear hm_blast'
              c0_hstraight; exact hJ _ m ⟨rfl, hbd, hev⟩
            · have hb_ge := drv0_le_of_not_mod hb_lt hew_lt hc; clear hc; c0_hstraight
              refine hJ 0#32 m ⟨rfl, by simp; omega, fun assign => ?_⟩
              rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq,
                Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _)
                  (Nat.pow_le_pow_right (by omega) hb_ge))]
              simp [Aig.evalLit_zero]
        · have hop_ne17 : op ≠ opGetLsbD := fun h => by
            apply hc; subst h; unfold opGetLsbD; decide
          clear hc; c0_hstraight; c0_hsplit
          · -- Case 5: op == BV_OP_EQ (10)
            have hop10 : op = opEq := by unfold opEq; c0_bv_omega [hop_lt]
            clear hc
            have heq := parsed_node_eq hp hn_lt
              (by rw [← hinv.nv_eq, ← hinv.nc_eq, hop_eq]; exact hop10)
            dsimp only at heq; rw [← hinv.nv_eq, ← hinv.nc_eq, ha_eq, hb_eq, hw_eq] at heq
            rcases heq with ⟨_, ha_lt_ni, hb_lt_ni, _, _, hewb_eq, ea, eb, hga, hgb, hnd_eq⟩
            obtain ⟨hew_idx, hew_fit⟩ := drv0_node_width_read hinv hok ha_lt ha_lt_ni hni_lt
            have hm_hdr' := hm; rw [bvBlastMem_hdr_left] at hm_hdr'
            c0_hstraight; clear hm_hdr'; rw [hinv.prog_ptr_eq]; c0_call hRead
            refine ⟨progBytes,
              bvBlastMem cfg hdr atomBases sliceOffs aigWords htSlots litsPool ⋆ R,
              hfit, hew_fit, sep_ac hm, ?_⟩
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
            c0_hstraight; have hm_blast' := blast_so_unfocus hok.hdr_so hm_so; clear hm_so
            refine wp_while_state
              (α := Nat × BitVec 32 × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32))
              (fun s => (s.2.1, BitVec.ofNat 32 s.1, ())) (fun s => ew - s.1)
              (drv0EqInv cfg progPtr progBytes hdr g atomBases sliceOffs litsPool R ew ea eb) ?_ ?_
            · intro J hJ; c0_hsteps
              refine hJ (0, 1#32, hdr, g, aigWords, htSlots) m ⟨Nat.zero_le ew, hoom0, hok, haig,
                Aig.extends_rfl g, hinv.prog_ptr_eq, rfl, rfl, rfl, ?_, fun assign => ?_, hm_blast'⟩
              · dsimp only; rw [haig.aig_len_eq]; simp; omega
              · dsimp only; simp [Aig.evalLit_one]
            · intro J ⟨j, acc, hdr', g', aw', hts'⟩ ml
                ⟨hj_le, hoom', hok', haig', hext', hpp', hnc', hrt', hlits', hacc_lt, hacc_ev, hml⟩
                ih
              c0_hstraight; c0_hsplit
              · have hj_lt := drv0_loop_lt hj_le hew_lt hc; clear hc
                obtain ⟨ha_j_lt, hb_j_lt, hla_lt, hlb_lt, hev_ab⟩ := drv0_eq_lits_lt hok
                  hinv.lits_le_cap hext' haig' ha_off_le hb_off_le ha_bd hb_bd ha_sd hb_sd ha_so
                  hb_so ha_lt hb_lt hj_lt hew_lt
                have hl_ptr : hdr'.lits_ptr = hdr.lits_ptr := hok'.hdr_lits.trans hok.hdr_lits.symm
                have hml_lits := blast_lits_focus hok'.hdr_lits hml; clear hml
                rw [hl_ptr] at hml_lits; c0_hstraight; rw [← hl_ptr] at hml_lits
                have hml_aig := blast_aig_focus hok'.hdr_aig hok'.hdr_ht
                  (blast_lits_unfocus hok'.hdr_lits hml_lits); clear hml_lits
                c0_call hBeq
                refine ⟨hdr', g', aw', hts', _, haig', fun _ => ⟨hla_lt, hlb_lt⟩, hml_aig, ?_⟩
                intro eqj hdr1 g1 aw1 hts1 m1 hfr1 hext1 _ haig1 _ _ heq_res hm1
                c0_call hMkAnd; refine ⟨hdr1, g1, aw1, hts1, _, haig1, fun hoom1 => ?_, hm1, ?_⟩
                · constructor
                  · have h1 := haig'.aig_len_eq; dsimp only at hacc_lt h1
                    rw [haig1.aig_len_eq]; rw [h1] at hacc_lt
                    have := hext1.1; have := hext1.2.1; omega
                  · exact (heq_res hoom1).1
                · intro acc' hdr2 g2 aw2 hts2 m2 hfr2 hext2 _ haig2 hoom_pr2 _ hand_res hm2
                  have hml2 := blast_aig_unfocus (hfr2.aig_ptr.trans (hfr1.aig_ptr.trans
                    hok'.hdr_aig)) (hfr2.ht_ptr.trans (hfr1.ht_ptr.trans hok'.hdr_ht)) hm2
                  have hml2_hdr := hml2; rw [bvBlastMem_hdr_left] at hml2_hdr
                  c0_hstraight; clear hml2_hdr
                  obtain ⟨hok2, hext_g2, hpp2, hnc2, hrt2, hlits2⟩ := drv0_eq_frame hext' hext1
                    hext2 hpp' hnc' hrt' hlits' hfr1 hfr2 hok' haig1 haig2
                  c0_hsplit
                  · c0_hstraight; exact hQ false hdr2 g2 sliceOffs aw2 hts2 litsPool m2 hok2 haig2
                      hext_g2 (by rw [hlits2]; exact hinv.lits_le_cap) hpp2 hnc2 hrt2
                      (fun hf => absurd hf Bool.false_ne_true) hml2
                  · have hoom2 : hdr2.oom = 0#32 := hc; clear hc
                    obtain ⟨hj_eq32, hacc'_lt, hacc'_ev⟩ := drv0_eq_step_eval hj_lt hew_lt hext1
                      haig' hacc_lt hacc_ev (fun assign => (hev_ab assign).1)
                      (fun assign => (hev_ab assign).2) hoom_pr2 hoom2 heq_res hand_res
                    c0_hstraight; rw [hj_eq32]
                    exact ih (j + 1, acc', hdr2, g2, aw2, hts2) m2 (by omega) ⟨by omega, hoom2,
                      hok2, haig2, hext_g2, hpp2, hnc2, hrt2, hlits2, hacc'_lt, hacc'_ev, hml2⟩
              · have hj_eq := drv0_loop_eq hj_le hew_lt hc; clear hc
                have hso_ptr := hok'.hdr_so.trans hok.hdr_so.symm
                have hml_so := blast_so_focus hok'.hdr_so hml; clear hml
                rw [hso_ptr] at hml_so
                have hni_so : nodeIdx.toNat < sliceOffs.length := by rw [hok'.so_len]; exact hni_lt
                c0_hstraight
                have hni64 : nodeIdx.toNat < 2 ^ 64 := Nat.lt_trans nodeIdx.isLt (by decide)
                dsimp only at hj_eq
                exact drv0_eq_post hoom0 hoom' hni_lt hok hok' haig' hext' hinv hpp' hnc' hrt'
                  hlits' hacc_lt (fun assign => by simpa [hj_eq, ew] using hacc_ev assign) hnd_eq
                  (by simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hni64] using hm) hQ
          · clear hc; c0_hstraight
            exact hQ false hdr g sliceOffs aigWords htSlots litsPool m hok haig
              (Aig.extends_rfl g) hinv.lits_le_cap hinv.prog_ptr_eq rfl rfl
              (fun hf => absurd hf Bool.false_ne_true) hm

end

end LeanQbe.T.Examples.Bitblast.Proof
