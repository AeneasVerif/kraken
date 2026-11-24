/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8XorAssembly
public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM7Transport1
import all LeanQbe.T.Examples.Kissat.FullM7Splice
import LeanQbe.T.Examples.Kissat.FullM6Transport1
import all LeanQbe.T.Examples.Kissat.FullM8XorGauss
import all LeanQbe.T.Examples.Kissat.FullM8XorAssembly
import all LeanQbe.T.Examples.Kissat.FullSpec3
import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Examples.Kissat.FullM6Orch
import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat M8 XOR / $\mathbb{F}_2$ Gauss-Jordan Assembly Proof (`FullM8XorAssemblyProof`)

Complete closed `0`-hook UNSAT-only verification of `FullM8XorAssembly.m8XorFidelityModule`
(`433` functions, `0` externs, `0` exits, `0` edits to `FullM5`–`FullM7`, `std3` axioms only):
1. Parametric `m8ProbeWrap_wp` for `m8ProbeWrapFn` (`"full_probe_m6"`) against canonical
   `FullM6Orch.m6ProbeSpec`.
2. `m8XorFidelityFns_names_nodup`, `m8XorFidelity_acyclic`, closed `m8XorFidelityEnv`,
   `m8XorFidelityEnv_noExit`, and closed `433/433` `m8XorFidelity_moduleOk`.
3. Top-level `kissat_solve_bytes` UNSAT soundness (`m8XorFidelity_solve_bytes_sound`,
   `m8XorFidelity_solve_bytes_host_sound`, `m8XorFidelity_unsat_nv`) and `PatchModule` /
   `FullM7Splice` bridge exports.
4. Genuine non-vacuous concrete `Mem 64` GF(2) UNSAT NV (`XPost := False`):
   - `nvXor5F0`: 5-variable unsatisfiable XOR CNF (`32` 5-literal clauses, each 16-clause half
     individually satisfiable, GF(2) elimination derives `0 = 1`).
   - `nv_m8_xor_rref_concrete`: executes `full_xor_rref` on concrete `nvXor5Mem`
     (`scratch_buf = [31, 0, 63, 0]`) and pins exact post-RREF `FullMem`
     (`scratch_buf = [31, 0, 32, 0]`, deriving `0 = 1`).
   - `nv_m8_xor_emit_mat_concrete` & `nv_m8_xor_rref_then_emit_unsat`: executes `full_xor_emit_mat`
     on the concrete post-RREF image and pins exact `r = 20#64`, `inconsistent = 1#64`,
     `nvXor5F0.Unsat`, and concrete `FullMem`.
-/

set_option autoImplicit false

local elab "c0_hstraight" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 2000

public section

namespace LeanQbe.T.Examples.Kissat.FullM8XorAssembly

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFix
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM8XorGauss
open scoped Full.FullArenaTactics

/-! ## 1. Parametric `m8ProbeWrap_wp` (`full_probe_m6` against `m6ProbeSpec`) -/

private theorem m8ProbeWrap_setWm_ret20 {Γ : Env}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s0 s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hSetWm : ∀ a m' Q' X', m6HdrW2aSpec [i64, i64] [] a m' Q' X' →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m' Q' X')
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hfuel : s.core.fuel.toNat ≤ s0.core.fuel.toNat) (hunsat : F0.Unsat)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X
      (.call (as := [i64, i64, i64]) (bs := []) "m6_hdr_set_watermark"
        (Arg.var c.hdr, Arg.var 0#64, Arg.var s.scratch.search_ticks, ())
        (fun () => .ret (Arg.var 20#64, ()))) m := by
  apply wp_call_of_spec
  dsimp only [vals, Arg.val]
  refine hSetWm _ _ _ _ (m6HdrW2aSpec_of rfl hcfg hext hlen hm
    fun () ext' s' m' hcore' hlen' _ hext' _ hm' => ?_)
  c0_hstraight
  exact hQ 20#64 ext' s' m' hlen' hext' (by rw [hcore']; exact hfuel) (Or.inr rfl)
    (fun _ => hunsat) (fun h => by simp at h) hm'

/-- Parametric `Func.wp` proof that `m8ProbeWrapFn` (`full_probe_m6`) satisfies canonical
`FullM6Orch.m6ProbeSpec`. -/
theorem m8ProbeWrap_wp (Γ : Env)
    (hXorGauss : ∀ a m Q X, fullXorGaussSpec a m Q X →
      Γ "full_xor_gauss" [i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, fullSubstituteSpec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hInner : ∀ a m Q X, m6ProbeSpec a m Q X →
      Γ "full_probe_m7_inner" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeSpec a m Q X → Func.wp Γ full_probe_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m0 Q X hs
  rcases m6ProbeSpec_elim hs with ⟨c, F0, ext0, s0, R, rfl, hinv0, hlvl0, hm0, hQ⟩
  have hm0_f := (fullM6HdrMem_iff c ext0 s0 R m0).mp hm0
  -- Phase 1: pre-probe full_xor_gauss + guarded full_substitute
  c0_hstraight
  apply wp_call_of_spec
  dsimp only [vals, Arg.val]
  refine hXorGauss _ _ _ _
    ⟨c, F0, s0, array64 (c.hdr - 2304) ext0 ⋆ R, rfl, hinv0.sparse, hlvl0, hm0_f,
      fun xr1 s1 m1 hsp1 hlvl1 hfuel1 _ hxr1_20 hm1_f => ?_⟩
  dsimp only
  have hm1 := (fullM6HdrMem_iff c ext0 s1 R m1).mpr hm1_f
  c0_hsplit
  · have h20 : xr1 = 20#64 := by bv_omega
    have hm1_load := (fullM6HdrMem_iff c ext0 s1 R m1).mp hm1
    c0_hstraight
    exact m8ProbeWrap_setWm_ret20 hSetWm hinv0.cfgOk hinv0.extOk hsp1.lengths hfuel1
      (hxr1_20 h20) hm1 hQ
  · let Jp1 : Mem 64 → Prop := fun m2 =>
      ∃ s2 : FullState,
        FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
        s2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullM6HdrMem c ext0 s2 ⋆ R) m2
    refine wp_join0 Jp1 ?_ ?_
    · -- Call full_probe_m7_inner
      rintro _ m2 ⟨s2, hsp2, hlvl2, hfuel2, hm2⟩
      c0_hstraight
      apply wp_call_of_spec
      dsimp only [vals, Arg.val]
      refine hInner _ _ _ _
        (m6ProbeSpec_of (FullM6HdrInv.mk_inv hinv0.cfgOk hinv0.extOk hsp2) hlvl2 hm2
          fun pr ext3 s3 m3 hlen3 hext3 hfuel3 hdom3 hpr20 hpr1 hm3 => ?_)
      dsimp only
      c0_hsplit
      · c0_hstraight
        have h20 : pr = 20#64 := by bv_omega
        exact hQ 20#64 ext3 s3 m3 hlen3 hext3 (Nat.le_trans hfuel3 hfuel2) (Or.inr rfl)
          (fun _ => hpr20 h20) (fun h => by simp at h) hm3
      · have h1 : pr = 1#64 := by
          rcases hdom3 with rfl | rfl
          · rfl
          · exfalso; simp_all
        obtain ⟨hinv3, hlvl3⟩ := hpr1 h1
        have hfuel3_0 : s3.core.fuel.toNat ≤ s0.core.fuel.toNat := Nat.le_trans hfuel3 hfuel2
        -- Phase 2: post-probe full_xor_gauss + guarded full_substitute
        have hm3_f := (fullM6HdrMem_iff c ext3 s3 R m3).mp hm3
        c0_hstraight
        apply wp_call_of_spec
        dsimp only [vals, Arg.val]
        refine hXorGauss _ _ _ _
          ⟨c, F0, s3, array64 (c.hdr - 2304) ext3 ⋆ R, rfl, hinv3.sparse, hlvl3, hm3_f,
            fun xr2 s4 m4 hsp4 hlvl4 hfuel4 _ hxr2_20 hm4_f => ?_⟩
        dsimp only
        have hm4 := (fullM6HdrMem_iff c ext3 s4 R m4).mpr hm4_f
        have hfuel4_0 : s4.core.fuel.toNat ≤ s0.core.fuel.toNat := Nat.le_trans hfuel4 hfuel3_0
        c0_hsplit
        · have h20 : xr2 = 20#64 := by bv_omega
          have hm4_load := (fullM6HdrMem_iff c ext3 s4 R m4).mp hm4
          c0_hstraight
          exact m8ProbeWrap_setWm_ret20 hSetWm hinv3.cfgOk hinv3.extOk hsp4.lengths hfuel4_0
            (hxr2_20 h20) hm4 hQ
        · let Jp2 : Mem 64 → Prop := fun m5 =>
            ∃ s5 : FullState,
              FullSparseInv c F0 s5 ∧ s5.core.cur_level = 0 ∧
              s5.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullM6HdrMem c ext3 s5 ⋆ R) m5
          refine wp_join0 Jp2 ?_ ?_
          · rintro _ m5 ⟨s5, hsp5, hlvl5, hfuel5, hm5⟩
            c0_hstraight
            exact hQ 1#64 ext3 s5 m5 hsp5.lengths hinv3.extOk hfuel5 (Or.inl rfl)
              (fun h => by simp at h)
              (fun _ => ⟨FullM6HdrInv.mk_inv hinv3.cfgOk hinv3.extOk hsp5, hlvl5⟩) hm5
          · intro _ hJp2
            refine wp_join0 (fun m4' => m4' = m4) ?_ ?_
            · rintro _ m4' rfl
              c0_hstraight
              apply wp_call_of_spec
              dsimp only [vals, Arg.val]
              refine hSubst _ _ _ _
                ⟨c, F0, s4, array64 (c.hdr - 2304) ext3 ⋆ R, rfl, hsp4, hm4_f,
                  fun sr2 s5 m5 hsp5 hlvl5 hfuel5 _ hsr2_20 hm5_f => ?_⟩
              dsimp only
              have hm5 := (fullM6HdrMem_iff c ext3 s5 R m5).mpr hm5_f
              have hfuel5_0 : s5.core.fuel.toNat ≤ s0.core.fuel.toNat :=
                Nat.le_trans hfuel5 hfuel4_0
              c0_hsplit
              · have h20 : sr2 = 20#64 := by bv_omega
                have hm5_load := (fullM6HdrMem_iff c ext3 s5 R m5).mp hm5
                c0_hstraight
                exact m8ProbeWrap_setWm_ret20 hSetWm hinv3.cfgOk hinv3.extOk hsp5.lengths
                  hfuel5_0 (hsr2_20 h20) hm5 hQ
              · exact hJp2 m5 ⟨s5, hsp5, hlvl5, hfuel5_0, hm5⟩
            · intro _ hSubst2
              c0_hstraight
              c0_hsplit
              · exact hSubst2 m4 rfl
              · c0_hstraight
                c0_hsplit
                · exact hSubst2 m4 rfl
                · exact hJp2 m4 ⟨s4, hsp4, hlvl4, hfuel4_0, hm4⟩
    · intro _ hJp1
      refine wp_join0 (fun m1' => m1' = m1) ?_ ?_
      · rintro _ m1' rfl
        c0_hstraight
        apply wp_call_of_spec
        dsimp only [vals, Arg.val]
        refine hSubst _ _ _ _
          ⟨c, F0, s1, array64 (c.hdr - 2304) ext0 ⋆ R, rfl, hsp1, hm1_f,
            fun sr1 s2 m2 hsp2 hlvl2 hfuel2 _ hsr1_20 hm2_f => ?_⟩
        dsimp only
        have hm2 := (fullM6HdrMem_iff c ext0 s2 R m2).mpr hm2_f
        have hfuel2_0 : s2.core.fuel.toNat ≤ s0.core.fuel.toNat := Nat.le_trans hfuel2 hfuel1
        c0_hsplit
        · have h20 : sr1 = 20#64 := by bv_omega
          have hm2_load := (fullM6HdrMem_iff c ext0 s2 R m2).mp hm2
          c0_hstraight
          exact m8ProbeWrap_setWm_ret20 hSetWm hinv0.cfgOk hinv0.extOk hsp2.lengths hfuel2_0
            (hsr1_20 h20) hm2 hQ
        · exact hJp1 m2 ⟨s2, hsp2, hlvl2, hfuel2_0, hm2⟩
      · intro _ hSubst1
        c0_hstraight
        c0_hsplit
        · exact hSubst1 m1 rfl
        · c0_hstraight
          c0_hsplit
          · exact hSubst1 m1 rfl
          · exact hJp1 m1 ⟨s1, hsp1, hlvl1, hfuel1, hm1⟩

/-! ## 2. Acyclicity, `PatchModule` Bridges & Closed `M8XorFidelityEnv` (`433/433`) -/

/-- `PatchModule` replacement list for `m8XorFidelityModule`. -/
def m8XorPatchRepls : List Fn := [m8ProbeWrapFn]

/-- `PatchModule` before-insertion list for `m8XorFidelityModule`. -/
def m8XorPatchBefores : List (Sym × List Fn) :=
  [("full_probe_m6", m8XorGaussFns ++ [fullProbeM7InnerFn])]

/-- `PatchModule`-ready `1`-row replacement spec table matching `m8XorPatchRepls`. -/
def m8XorPatchReplRows : List SpecEntry :=
  [⟨"full_probe_m6", [i64, .bool], [i64], m6ProbeSpec, true⟩]

/-- `PatchModule`-ready `20`-row inserted helper spec table matching
`m8XorGaussFns ++ [fullProbeM7InnerFn]`. -/
def m8XorPatchBeforeRows : List SpecEntry :=
  m8XorGaussSpecTable ++ [⟨"full_probe_m7_inner", [i64, .bool], [i64], m6ProbeSpec, true⟩]

theorem m8XorFidelityFns_eq_patchFns :
    m8XorFidelityFns = patchFns m8XorPatchRepls m8XorPatchBefores m7FidelityFns := by
  unfold m8XorFidelityFns m8XorPatchRepls m8XorPatchBefores
  rfl

theorem m8XorPatchReplRows_sigs :
    m8XorPatchReplRows.map (fun e => (e.name, e.as, e.rs)) = m8XorPatchRepls.map Fn.sig := by
  t_kernel_rfl

theorem m8XorPatchBeforeRows_sigs :
    m8XorPatchBeforeRows.map (fun e => (e.name, e.as, e.rs)) =
      (m8XorGaussFns ++ [fullProbeM7InnerFn]).map Fn.sig := by
  have hsigs : m8XorGaussSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      m8XorGaussFns.map Fn.sig := by t_kernel_rfl
  rw [m8XorPatchBeforeRows, List.map_append, List.map_append, hsigs]
  rfl

private def m8XorInsNamesLit : List String :=
  [ "full_xor_sort5", "full_xor_parity_mask", "full_xor_ht_insert"
  , "full_xor_collect_arena", "full_xor_collect_bins", "full_xor_compact_pool"
  , "full_xor_merge_two", "full_xor_chain_merge", "full_xor_uf_find"
  , "full_xor_read_u64", "full_xor_write_u64", "full_xor_swap_rows"
  , "full_xor_xor_rows", "full_xor_set_bit", "full_xor_build_mat"
  , "full_xor_rref", "full_xor_emit_mat", "full_xor_emit_pool_small"
  , "full_xor_gauss", "full_probe_m7_inner" ]

private theorem m8XorIns_names_eq :
    (m8XorGaussFns ++ [fullProbeM7InnerFn]).map Fn.name = m8XorInsNamesLit := by
  t_kernel_rfl

private theorem m8XorGauss_names_eq :
    m8XorGaussSpecTable.map SpecEntry.name = m8XorInsNamesLit.take 19 := rfl

private theorem m8XorIns_names_nodup :
    ((m8XorGaussFns ++ [fullProbeM7InnerFn]).map Fn.name).Nodup := by
  rw [m8XorIns_names_eq]; decide

private theorem m8XorIns_not_in_m7Fid :
    ∀ h ∈ m8XorGaussFns ++ [fullProbeM7InnerFn], h.name ∉ m7FidelityFns.map Fn.name := by
  intro h hh hmem
  have h1 : h.name ∈ m8XorInsNamesLit := by
    rw [← m8XorIns_names_eq]; exact List.mem_map.mpr ⟨h, hh, rfl⟩
  have hdisj : ∀ nm ∈ m8XorInsNamesLit, nm ∉ m7FidelityFns.map Fn.name := by
    intro nm hnm
    have hall : m8XorInsNamesLit.all (fun s => !m7FidelityFns.any (fun f => f.name == s)) = true :=
      by t_kernel_rfl
    have h1' := List.all_eq_true.mp hall nm hnm
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at h1'
    intro hm
    obtain ⟨g, hg, hgn⟩ := List.mem_map.mp hm
    exact h1' g hg hgn
  exact hdisj h.name h1 hmem

private theorem sig_of_map_idx {xs : List Fn} {i : Nat} {s : SigEntry}
    (h : xs[i]?.map Fn.sig = some s) : ∃ f, xs[i]? = some f ∧ f.sig = s := by
  cases hi : xs[i]? with
  | none => simp [hi] at h
  | some f => simp only [hi, Option.map_some, Option.some.injEq] at h; exact ⟨f, rfl, h⟩

private theorem patchInsAt_single_pos {a : Sym} {hs : List Fn} {f : Fn} (h : a = f.name) :
    patchInsAt [(a, hs)] f = hs := by
  simp [patchInsAt, h]

private theorem patchInsAt_single_neg {a : Sym} {hs : List Fn} {f : Fn} (h : a ≠ f.name) :
    patchInsAt [(a, hs)] f = [] := by
  simp [patchInsAt, h]

private theorem m8Xor_repl_sig :
    ∀ r ∈ m8XorPatchRepls, ∀ f ∈ m7FidelityModule.fns, r.name = f.name → r.sig = f.sig := by
  have h404s : m7FidelityFns[404]?.map Fn.sig =
      some ("full_probe_m6", [i64, Ty.bool], [i64]) := by t_kernel_rfl
  obtain ⟨f404, hf404, hs404⟩ := sig_of_map_idx h404s
  intro r hr f hf hnm
  rcases List.mem_singleton.mp hr with rfl
  have hf_eq := fn_eq_of_mem_idx m7FidelityFns_names_nodup hf hf404
    (hnm.symm.trans (congrArg Prod.fst hs404.symm))
  subst hf_eq; exact hs404.symm

/-- Distinct function names across all `433` functions of `m8XorFidelityFns`. -/
theorem m8XorFidelityFns_names_nodup : (m8XorFidelityFns.map Fn.name).Nodup := by
  dsimp only [m8XorFidelityFns]
  refine patchFns_names_nodup m7FidelityFns_names_nodup m8Xor_repl_sig ?_ ?_ ?_
  · intro f _
    by_cases hnm : f.name = "full_probe_m6"
    · rw [patchInsAt_single_pos hnm.symm]; exact m8XorIns_names_nodup
    · rw [patchInsAt_single_neg (Ne.symm hnm)]; exact List.nodup_nil
  · intro f _ h hh
    by_cases hnm : f.name = "full_probe_m6"
    · rw [patchInsAt_single_pos hnm.symm] at hh
      exact m8XorIns_not_in_m7Fid h hh
    · rw [patchInsAt_single_neg (Ne.symm hnm)] at hh; exact nomatch hh
  · intro f1 _ f2 _ hne h hh1 hh2
    by_cases h1 : f1.name = "full_probe_m6"
    · by_cases h2 : f2.name = "full_probe_m6"
      · exact absurd (h1.trans h2.symm) hne
      · rw [patchInsAt_single_neg (Ne.symm h2)] at hh2; exact nomatch hh2
    · rw [patchInsAt_single_neg (Ne.symm h1)] at hh1; exact nomatch hh1

private def m8XorExtSigs : List SigEntry :=
  [ ("full_arena_next", [i64, i32], [i32])
  , ("full_add_clause", [i64, i32, i32, Ty.bool], [i64])
  , ("m6_hdr_set_watermark", [i64, i64, i64], [])
  , ("full_propagate", [i64], [i64])
  , ("full_has_bin", [i64, i32, i32], [Ty.bool])
  , ("full_add_bin", [i64, i32, i32], [i64])
  , ("full_add_unit", [i64, i32], [Ty.bool])
  , ("full_substitute", [i64], [i64])
  , ("full_has_ternary", [i64, i32, i32, i32], [Ty.bool]) ]

private def m8XorInnerCalleesSigs : List SigEntry :=
  [ ("full_probe_dticks_m6_hdr", [i64, Ty.bool], [i64])
  , ("full_log10_q16_m7", [i64], [i64])
  , ("full_scale_delta_m5", [i64, i64], [i64])
  , ("full_vivify_m6_hdr", [i64], [i64])
  , ("full_enter_dense", [i64], [Ty.bool])
  , ("m6_hdr_delaying", [i64, i64], [Ty.bool])
  , ("full_congruence_dense", [i64, i64], [i64])
  , ("full_rebuild_watches", [i64], [i64])
  , ("m6_hdr_set_watermark", [i64, i64, i64], [])
  , ("m6_hdr_reduce_delay", [i64, i64], [])
  , ("m6_hdr_bump_delay", [i64, i64], [])
  , ("full_sweep_dense_m6", [i64, i64, i64], [i64])
  , ("full_substitute", [i64], [i64])
  , ("full_probe_tail_m6", [i64, i64], [i64])
  , ("full_backbone_m6", [i64, i64], [i64])
  , ("full_min_u64", [i64, i64], [i64])
  , ("full_factor", [i64, i64], [i64]) ]

private theorem checkFnsCallsOk_append {exits : List Sym} {seen : List SigEntry}
    {fs1 fs2 : List Fn}
    (h1 : Module.checkFnsCallsOk exits [] seen fs1 = true)
    (h2 : Module.checkFnsCallsOk exits [] (seen ++ fs1.map Fn.sig) fs2 = true) :
    Module.checkFnsCallsOk exits [] seen (fs1 ++ fs2) = true := by
  induction fs1 generalizing seen with
  | nil => simpa using h2
  | cons f fs ih =>
    simp only [List.cons_append, Module.checkFnsCallsOk, Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, ih h1.2 ?_⟩
    simpa [List.append_assoc] using h2

/-- Acyclicity & call-signature check for `FullM8XorAssembly.m8XorFidelityModule` (`433` fns). -/
theorem m8XorFidelity_acyclic : m8XorFidelityModule.checkAcyclic = true := by
  have m7Ext : m7FidelityModule.externs = [] := rfl
  have m7Ex : m7FidelityModule.exits = [] := rfl
  have hnd :
      ((patchFns m8XorPatchRepls m8XorPatchBefores m7FidelityModule.fns).map Fn.name ++
        m7FidelityModule.externs.map Extern.name).Nodup := by
    rw [m7Ext, List.map_nil, List.append_nil]
    exact m8XorFidelityFns_names_nodup
  have hGauss_ok : Module.checkFnsCallsOk [] [] m8XorExtSigs m8XorGaussFns = true := by
    t_kernel_rfl
  have hInner_ok : fullProbeM7InnerFn.checkCallsOk m8XorInnerCalleesSigs [] = true := by
    t_kernel_rfl
  have hWrap_ok :
      m8ProbeWrapFn.checkCallsOk
        (m8XorExtSigs ++ (m8XorGaussFns ++ [fullProbeM7InnerFn]).map Fn.sig) [] = true := by
    t_kernel_rfl
  obtain ⟨g404, hg404, hsg404⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[404]?.map Fn.sig =
      some ("full_probe_m6", [i64, Ty.bool], [i64]))
  obtain ⟨g11, hg11, hsg11⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[11]?.map Fn.sig = some ("full_arena_next", [i64, i32], [i32]))
  obtain ⟨g31, hg31, hsg31⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[31]?.map Fn.sig = some ("full_log10_q16_m7", [i64], [i64]))
  obtain ⟨g32, hg32, hsg32⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[32]?.map Fn.sig =
      some ("full_scale_delta_m5", [i64, i64], [i64]))
  obtain ⟨g40, hg40, hsg40⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[40]?.map Fn.sig =
      some ("full_add_clause", [i64, i32, i32, Ty.bool], [i64]))
  obtain ⟨g66, hg66, hsg66⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[66]?.map Fn.sig =
      some ("m6_hdr_delaying", [i64, i64], [Ty.bool]))
  obtain ⟨g67, hg67, hsg67⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[67]?.map Fn.sig =
      some ("m6_hdr_bump_delay", [i64, i64], []))
  obtain ⟨g68, hg68, hsg68⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[68]?.map Fn.sig =
      some ("m6_hdr_reduce_delay", [i64, i64], []))
  obtain ⟨g71, hg71, hsg71⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[71]?.map Fn.sig =
      some ("m6_hdr_set_watermark", [i64, i64, i64], []))
  obtain ⟨g86, hg86, hsg86⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[86]?.map Fn.sig = some ("full_propagate", [i64], [i64]))
  obtain ⟨g175, hg175, hsg175⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[175]?.map Fn.sig =
      some ("full_has_bin", [i64, i32, i32], [Ty.bool]))
  obtain ⟨g178, hg178, hsg178⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[178]?.map Fn.sig =
      some ("full_add_bin", [i64, i32, i32], [i64]))
  obtain ⟨g181, hg181, hsg181⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[181]?.map Fn.sig =
      some ("full_add_unit", [i64, i32], [Ty.bool]))
  obtain ⟨g218, hg218, hsg218⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[218]?.map Fn.sig = some ("full_vivify_m6_hdr", [i64], [i64]))
  obtain ⟨g226, hg226, hsg226⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[226]?.map Fn.sig =
      some ("full_backbone_m6", [i64, i64], [i64]))
  obtain ⟨g235, hg235, hsg235⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[235]?.map Fn.sig = some ("full_substitute", [i64], [i64]))
  obtain ⟨g236, hg236, hsg236⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[236]?.map Fn.sig =
      some ("full_enter_dense", [i64], [Ty.bool]))
  obtain ⟨g237, hg237, hsg237⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[237]?.map Fn.sig =
      some ("full_rebuild_watches", [i64], [i64]))
  obtain ⟨g243, hg243, hsg243⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[243]?.map Fn.sig =
      some ("full_has_ternary", [i64, i32, i32, i32], [Ty.bool]))
  obtain ⟨g275, hg275, hsg275⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[275]?.map Fn.sig =
      some ("full_congruence_dense", [i64, i64], [i64]))
  obtain ⟨g299, hg299, hsg299⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[299]?.map Fn.sig =
      some ("full_sweep_dense_m6", [i64, i64, i64], [i64]))
  obtain ⟨g353, hg353, hsg353⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[353]?.map Fn.sig = some ("full_factor", [i64, i64], [i64]))
  obtain ⟨g376, hg376, hsg376⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[376]?.map Fn.sig = some ("full_min_u64", [i64, i64], [i64]))
  obtain ⟨g402, hg402, hsg402⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[402]?.map Fn.sig =
      some ("full_probe_dticks_m6_hdr", [i64, Ty.bool], [i64]))
  obtain ⟨g403, hg403, hsg403⟩ := sig_of_map_idx
    (by t_kernel_rfl : m7FidelityFns[403]?.map Fn.sig =
      some ("full_probe_tail_m6", [i64, i64], [i64]))
  have hpfx_sigs : ∀ pre f post, m7FidelityFns = pre ++ f :: post →
      f.name = "full_probe_m6" → ∀ s ∈ m8XorExtSigs, s ∈ pre.map Fn.sig := by
    intro pre f post hsplit hnm s hs
    have hn0 : f.name = g404.name := hnm.trans (congrArg Prod.fst hsg404.symm)
    simp only [m8XorExtSigs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsg11 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg11 (by decide)
    · exact hsg40 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg40 (by decide)
    · exact hsg71 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg71 (by decide)
    · exact hsg86 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg86 (by decide)
    · exact hsg175 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg175 (by decide)
    · exact hsg178 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg178 (by decide)
    · exact hsg181 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg181 (by decide)
    · exact hsg235 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg235 (by decide)
    · exact hsg243 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg243 (by decide)
  have hinner_sigs : ∀ pre f post, m7FidelityFns = pre ++ f :: post →
      f.name = "full_probe_m6" → ∀ s ∈ m8XorInnerCalleesSigs, s ∈ pre.map Fn.sig := by
    intro pre f post hsplit hnm s hs
    have hn0 : f.name = g404.name := hnm.trans (congrArg Prod.fst hsg404.symm)
    simp only [m8XorInnerCalleesSigs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact hsg402 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg402 (by decide)
    · exact hsg31 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg31 (by decide)
    · exact hsg32 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg32 (by decide)
    · exact hsg218 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg218 (by decide)
    · exact hsg236 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg236 (by decide)
    · exact hsg66 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg66 (by decide)
    · exact hsg275 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg275 (by decide)
    · exact hsg237 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg237 (by decide)
    · exact hsg71 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg71 (by decide)
    · exact hsg68 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg68 (by decide)
    · exact hsg67 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg67 (by decide)
    · exact hsg299 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg299 (by decide)
    · exact hsg235 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg235 (by decide)
    · exact hsg403 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg403 (by decide)
    · exact hsg226 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg226 (by decide)
    · exact hsg376 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg376 (by decide)
    · exact hsg353 ▸
        sig_mem_pre_of_lt_idx m7FidelityFns_names_nodup hsplit hg404 hn0 hg353 (by decide)
  dsimp only [m8XorFidelityModule, m8XorFidelityFns]
  refine patchModule_checkAcyclic (M := m7FidelityModule) hnd m7Fidelity_checkAcyclic
    m8Xor_repl_sig ?_ ?_
  · intro pre f post hsplit
    change m7FidelityFns = pre ++ f :: post at hsplit
    rw [m7Ext, m7Ex]
    by_cases hnm : f.name = "full_probe_m6"
    · rw [patchInsAt_single_pos hnm.symm, List.map_nil]
      refine checkFnsCallsOk_append
        (checkFnsCallsOk_mono
          (fun s hs => List.mem_append_left [] (hpfx_sigs pre f post hsplit hnm s hs))
          hGauss_ok) ?_
      simp only [Module.checkFnsCallsOk, Bool.and_true]
      exact fn_checkCallsOk_mono
        (fun s hs =>
          List.mem_append_left [] (List.mem_append_left _ (hinner_sigs pre f post hsplit hnm s hs)))
        hInner_ok
    · rw [patchInsAt_single_neg (Ne.symm hnm)]; rfl
  · intro pre f post r hsplit hr hnm
    rcases List.mem_singleton.mp hr with rfl
    change m7FidelityFns = pre ++ f :: post at hsplit
    have hins_eq :
        patchInsAt [("full_probe_m6", m8XorGaussFns ++ [fullProbeM7InnerFn])] f =
          m8XorGaussFns ++ [fullProbeM7InnerFn] :=
      patchInsAt_single_pos hnm
    rw [hins_eq, m7Ext, m7Ex, List.map_nil, List.append_nil]
    refine fn_checkCallsOk_mono (fun s hs => ?_) hWrap_ok
    rcases List.mem_append.mp hs with hs1 | hs2
    · exact List.mem_append_left _ (hpfx_sigs pre f post hsplit hnm.symm s hs1)
    · exact List.mem_append_right _ hs2

/-- Closed environment extending `m7FidelityEnv` with the `19` `m8XorGaussSpecTable` rows and
`"full_probe_m7_inner"` (`m6ProbeSpec`). -/
inductive M8XorFidelityEnv (Γ : Env) : Env where
  | base {f as bs xs m Q X} :
      Γ f as bs xs m Q X → M8XorFidelityEnv Γ f as bs xs m Q X
  | xorGauss {f as bs xs m Q X} :
      Env.ofTable m8XorGaussSpecTable f as bs xs m Q X →
      M8XorFidelityEnv Γ f as bs xs m Q X
  | probeInner {a m Q X} :
      m6ProbeSpec a m Q X →
      M8XorFidelityEnv Γ "full_probe_m7_inner" [i64, .bool] [i64] a m Q X

/-- Canonical closed `Env` for `m8XorFidelityModule` (`433` fns, `0` externs, `0` exits). -/
def m8XorFidelityEnv : Env := M8XorFidelityEnv m7FidelityEnv

/-- Exit-freedom of `m8XorFidelityEnv`. -/
theorem m8XorFidelityEnv_noExit :
    ∀ f as bs xs m Q X X',
      m8XorFidelityEnv f as bs xs m Q X → m8XorFidelityEnv f as bs xs m Q X' := by
  intro f as bs xs m Q X X' h
  cases h with
  | base hb => exact M8XorFidelityEnv.base (m7FidelityEnv_noExit f as bs xs m Q X X' hb)
  | xorGauss hx =>
    exact M8XorFidelityEnv.xorGauss
      (Env.ofTable_noExit m8XorGaussSpecTable_noExit _ _ _ _ _ _ _ _ hx)
  | probeInner hp => exact M8XorFidelityEnv.probeInner (m6ProbeSpec_monoX hp)

private theorem m8Xor_ofTable_name_mem {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} :
    ∀ {tbl : List SpecEntry},
    Env.ofTable tbl nm as bs xs m Q X → nm ∈ tbl.map SpecEntry.name
  | [], h => False.elim h
  | e :: _, h => by
    by_cases hnm : e.name = nm
    · rw [← hnm]; exact List.mem_cons_self
    · rw [Env.ofTable_cons_ne hnm] at h
      exact List.mem_cons_of_mem _ (m8Xor_ofTable_name_mem h)

private theorem m8Xor_ofTable_sig_elim {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup) {e : SpecEntry} (he : e ∈ tbl)
    {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable tbl e.name as bs xs m Q X) :
    ∃ (has : e.as = as) (hrs : e.rs = bs), e.cast has hrs xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp he with rfl | htl
    · dsimp only [Env.ofTable] at h
      rcases h with ⟨⟨_, has, hrs⟩, hcast⟩ | ⟨_, htl'⟩
      · exact ⟨has, hrs, hcast⟩
      · exact absurd (m8Xor_ofTable_name_mem htl') (by simpa [List.mem_map] using hnd.1)
    · have hne : hd.name ≠ e.name := fun hEq => hnd.1 ⟨e, htl, hEq.symm⟩
      rw [Env.ofTable_cons_ne hne] at h
      exact ih hnd.2 htl h

private def mfExtraNamesLit : List String :=
  [ "m6_hdr_init", "m6_ext_ensure_init", "full_prop_lit_ovf_hot", "full_prop_chrono_hot"
  , "full_has_bin", "full_min_mark", "full_ana_sift_m6", "full_sort_ana_qs_m6"
  , "full_sort_tmp_sift_m7", "full_sort_tmp_heap_m7", "full_sort_tmp"
  , "full_min_lit_dfs_m6", "full_shrink_lower_m6", "full_shrink_blk_bool_m6"
  , "full_walk_cb_inv_m7", "full_walk_init_table_m7", "full_walk_effort_m7"
  , "full_walk_init_vals_m7", "full_walk_collect_m7", "full_walk_build_occ_m7"
  , "full_walk_break_m7", "full_walk_pick_m7", "full_walk_flip_m7"
  , "full_walk_save_min_m7", "full_warmup_m7", "full_add_bin_m6"
  , "full_viv_unreason_m6", "full_viv_watch_rank_m6", "full_viv_best_watch_m6"
  , "full_viv_simplify_m6", "full_viv_commit_m6", "full_viv_mark_garb_m6"
  , "full_viv_subsumes_bin_m6", "full_viv_subsumes_cl_m6", "full_viv_deduce_m6"
  , "full_viv_best_implied_m6", "full_viv_reestablish_m6", "full_viv_inst_check_m6"
  , "full_viv_inst_m6", "full_viv_finish_m6", "full_viv_sort_counts_m6"
  , "full_viv_has_l0_m6", "full_viv_l0_simp_m6", "full_viv_reuse_prefix_m6"
  , "full_viv_clause_m6", "full_viv_tier_match_m6", "full_viv_collect_m6"
  , "full_viv_count_m6", "full_viv_keys_m6", "full_viv_sort_sched_m6"
  , "full_viv_clear_tier_m6"
  , "full_vivify_tier_m6_hdr", "full_compact_needed", "full_walk_m7"
  , "full_bump_analyzed_m6_hdr", "full_walk_warmup_m7", "full_walk"
  , "full_bva_match_large_fid", "full_reorder_sift_fid", "m6_hdr_decide_fid" ]

private theorem mfExtraRows_names_eq : mfExtraRows.map SpecEntry.name = mfExtraNamesLit := by
  t_kernel_rfl

private theorem m8Xor_not_in_m7Env {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (hmem : f ∈ m8XorInsNamesLit) (h : m7FidelityEnv f as bs xs m Q X) : False := by
  cases h with
  | base _ hb =>
    have hm := m8Xor_ofTable_name_mem hb
    have htb_nm : m7FidBaseTable.map SpecEntry.name = m7Fns.map Fn.name := by
      have h1 := congrArg (List.map Prod.fst) m7FidBaseTable_sigs
      simpa only [List.map_map, Function.comp_def, Fn.sig] using h1
    rw [htb_nm] at hm
    have hdisj :
        m8XorInsNamesLit.all (fun s => !m7Fns.any (fun g => g.name == s)) = true :=
      by t_kernel_rfl
    have h1 := List.all_eq_true.mp hdisj f hmem
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at h1
    obtain ⟨g, hg, hgn⟩ := List.mem_map.mp hm
    exact h1 g hg hgn
  | extra he =>
    have hm := m8Xor_ofTable_name_mem he
    rw [mfExtraRows_names_eq] at hm
    have hdisj : ∀ s ∈ m8XorInsNamesLit, s ∉ mfExtraNamesLit := by decide
    exact hdisj f hmem hm

private theorem m8Xor_elim_base {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (hnins : f ∉ m8XorInsNamesLit) (h : m8XorFidelityEnv f as bs xs m Q X) :
    m7FidelityEnv f as bs xs m Q X := by
  cases h with
  | base hb => exact hb
  | xorGauss hx =>
    have hm := m8Xor_ofTable_name_mem hx
    rw [m8XorGauss_names_eq] at hm
    exact False.elim (hnins (List.mem_of_mem_take hm))
  | probeInner _ => exact False.elim (hnins (by decide))

private theorem m8Xor_elim_probeM6 {xs m Q X}
    (hs : m8XorFidelityEnv "full_probe_m6" [i64, .bool] [i64] xs m Q X) :
    m6ProbeSpec xs m Q X := by
  have hm7 := m8Xor_elim_base (by decide) hs
  cases hm7 with
  | base _ hb =>
    exact m6ProbeSpec_monoX
      (m8Xor_ofTable_sig_elim m7FidBaseTable_nodup m7FidBase_probeM6_mem hb).2.2
  | extra he =>
    have hm := m8Xor_ofTable_name_mem he
    rw [mfExtraRows_names_eq] at hm
    exact absurd hm (by decide)

private theorem m8Xor_elim_probeInner {xs m Q X}
    (hs : m8XorFidelityEnv "full_probe_m7_inner" [i64, .bool] [i64] xs m Q X) :
    m6ProbeSpec xs m Q X := by
  cases hs with
  | base hb => exact False.elim (m8Xor_not_in_m7Env (by decide) hb)
  | xorGauss hx =>
    have hm := m8Xor_ofTable_name_mem hx
    rw [m8XorGauss_names_eq] at hm
    exact False.elim (by simp [m8XorInsNamesLit] at hm)
  | probeInner hp => exact hp

private theorem m8Xor_probeInner_wp :
    ∀ xs m Q X, m6ProbeSpec xs m Q X →
      Func.wp m8XorFidelityEnv full_probe_fid2_body xs m Q X := by
  intro xs m Q X hsp
  let probeFn : Fn := ⟨"full_probe_m6", [i64, .bool], [i64], full_probe_fid2_body⟩
  have h404 : m7FidelityFns[404]? = some probeFn := by t_kernel_rfl
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem (List.mem_of_getElem? h404)
  have hfn := (m7Fidelity_moduleOk.fnsOk pre probeFn post hsplit).2.2
  have hm7_row : m7FidelityEnv "full_probe_m6" [i64, .bool] [i64] xs m Q X :=
    M7FidelityEnv.base (by decide)
      (Env.ofTable_of_mem m7FidBase_probeM6_mem m7FidBaseTable_nodup (m6ProbeSpec_monoX hsp))
  exact wp_env_mono (fun _ _ _ _ _ _ _ h => M8XorFidelityEnv.base h) _ m (hfn xs m Q X hm7_row)

private theorem m8Xor_m7_base_row {e : SpecEntry} (he : e ∈ m7FidBaseTable)
    (hne : e.name ∉ mfExclNames) (hx : e.noExit = true := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.spec xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, e.spec xs m Q X → m8XorFidelityEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X hs =>
    M8XorFidelityEnv.base
      (M7FidelityEnv.base hne
        (Env.ofTable_of_mem he m7FidBaseTable_nodup (by
          dsimp only [SpecEntry.eff]; simp only [hx, ↓reduceIte]; exact hno xs m Q X hs)))

/-- Closed `19/19` `TableImpl` for `m8XorGaussFns` inside `m8XorFidelityEnv`. -/
theorem m8XorGauss_tableImpl_in_m8Env :
    TableImpl m8XorFidelityEnv m8XorGaussFns m8XorGaussSpecTable := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hTernMem : (⟨"full_has_ternary", [i64, i32, i32, i32], [.bool],
      Full.fullHasTernarySpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 52 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
  have rArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      m8XorFidelityEnv "full_arena_next" [i64, i32] [i32] a m Q X :=
    m8Xor_m7_base_row hc1.arenaNext (by decide)
  have rHasBin : ∀ a m Q X, fullHasBinSpec a m Q X →
      m8XorFidelityEnv "full_has_bin" [i64, i32, i32] [.bool] a m Q X :=
    fun a m Q X hs =>
      M8XorFidelityEnv.base
        (M7FidelityEnv.extra
          (Env.ofTable_of_mem
            (e := ⟨"full_has_bin", [i64, i32, i32], [Ty.bool], Full.fullHasBinSpec, true⟩)
            (List.mem_of_getElem? (i := 4) rfl) mfExtraRows_nodup hs))
  have rHasTern : ∀ a m Q X, fullHasTernarySpec a m Q X →
      m8XorFidelityEnv "full_has_ternary" [i64, i32, i32, i32] [.bool] a m Q X :=
    m8Xor_m7_base_row hTernMem (by decide)
  have rAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      m8XorFidelityEnv "full_add_unit" [i64, i32] [.bool] a m Q X :=
    m8Xor_m7_base_row hc2.addUnit (by decide)
  have rAddBinM6 : ∀ a m Q X, FullM6VivBackbone.fullAddBinM6Spec a m Q X →
      m8XorFidelityEnv "full_add_bin" [i64, i32, i32] [i64] a m Q X :=
    m8Xor_m7_base_row hc2.addBin (by decide)
  have rAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      m8XorFidelityEnv "full_add_bin" [i64, i32, i32] [i64] a m Q X :=
    FullM6Transport.m6_add_bin_m6_to_canon rAddBinM6
  have rAddClause : ∀ a m Q X, fullAddClauseSpec a m Q X →
      m8XorFidelityEnv "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X :=
    m8Xor_m7_base_row hc1.addClause (by decide)
  have rProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      m8XorFidelityEnv "full_propagate" [i64] [i64] a m Q X :=
    m8Xor_m7_base_row hc1.propagate (by decide)
  exact m8XorGauss_tableImpl_of m8XorFidelityEnv
    (fun e he _ _ _ _ hs => M8XorFidelityEnv.xorGauss
      (Env.ofTable_of_mem he m8XorGaussSpecTable_nodup hs))
    rArenaNext rHasBin rHasTern rAddUnit rAddBin rAddClause rProp

theorem m8XorPatchRepl_tableImpl :
    TableImpl m8XorFidelityEnv m8XorPatchRepls m8XorPatchReplRows := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have rXorGauss : ∀ a m Q X, fullXorGaussSpec a m Q X →
      m8XorFidelityEnv "full_xor_gauss" [i64] [i64] a m Q X :=
    fun a m Q X hs => M8XorFidelityEnv.xorGauss
      (Env.ofTable_of_mem
        (e := ⟨"full_xor_gauss", [i64], [i64], fullXorGaussSpec, true⟩)
        (List.mem_of_getElem? (i := 18) rfl) m8XorGaussSpecTable_nodup hs)
  have rSubst : ∀ a m Q X, fullSubstituteSpec a m Q X →
      m8XorFidelityEnv "full_substitute" [i64] [i64] a m Q X :=
    m8Xor_m7_base_row hc2p.substitute (by decide)
  have rSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      m8XorFidelityEnv "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X :=
    m8Xor_m7_base_row hc1.hdrSetWm (by decide) rfl (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rInner : ∀ a m Q X, m6ProbeSpec a m Q X →
      m8XorFidelityEnv "full_probe_m7_inner" [i64, .bool] [i64] a m Q X :=
    fun _ _ _ _ hs => M8XorFidelityEnv.probeInner hs
  exact ⟨SpecEntry.Impl.of (m8ProbeWrap_wp m8XorFidelityEnv rXorGauss rSubst rSetWm rInner),
    trivial⟩

theorem m8XorPatchBefore_tableImpl :
    TableImpl m8XorFidelityEnv (m8XorGaussFns ++ [fullProbeM7InnerFn]) m8XorPatchBeforeRows :=
  FullM6ProofUtil.tableImpl_append
    (rfl : m8XorGaussFns.length = m8XorGaussSpecTable.length)
    m8XorGauss_tableImpl_in_m8Env ⟨SpecEntry.Impl.of m8Xor_probeInner_wp, trivial⟩

private theorem m8Xor_elim_xorGauss {nm : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hmem : nm ∈ m8XorInsNamesLit) (hnin : nm ≠ "full_probe_m7_inner")
    (hs : m8XorFidelityEnv nm as bs xs m Q X) :
    Env.ofTable m8XorGaussSpecTable nm as bs xs m Q X := by
  cases hs with
  | base hb => exact False.elim (m8Xor_not_in_m7Env hmem hb)
  | xorGauss hx => exact hx
  | probeInner _ => exact False.elim (hnin rfl)

private theorem m8Xor_mem_wp_of_tableImpl :
    ∀ {fs : List Fn} {rs : List SpecEntry},
      TableImpl m8XorFidelityEnv fs rs →
      (∀ e ∈ rs, e ∈ m8XorGaussSpecTable) →
      ∀ f ∈ fs, ∀ xs m Q X,
        m8XorFidelityEnv f.name f.as f.rs xs m Q X →
          Func.wp m8XorFidelityEnv f.body xs m Q X
  | [], [], _, _, _, hf => nomatch hf
  | [], _ :: _, _, _, _, hf => nomatch hf
  | _ :: _, [], ht, _, _, _ => False.elim ht
  | f :: _, r :: _, ⟨h1, h2⟩, hsub, g, hg => by
    intro xs m Q X hs
    rcases List.mem_cons.mp hg with rfl | htl
    · obtain ⟨⟨hnme, has, hrs⟩, himpl⟩ := h1
      have hr_mem : r ∈ m8XorGaussSpecTable := hsub r List.mem_cons_self
      have hm_nm : g.name ∈ m8XorGaussSpecTable.map SpecEntry.name := by
        rw [← hnme]; exact List.mem_map.mpr ⟨r, hr_mem, rfl⟩
      have he_mem : g.name ∈ m8XorInsNamesLit := by
        rw [m8XorGauss_names_eq] at hm_nm
        exact List.mem_of_mem_take hm_nm
      have hnm_not_inner : g.name ≠ "full_probe_m7_inner" := by
        rw [m8XorGauss_names_eq] at hm_nm
        intro heq; rw [heq] at hm_nm; simp [m8XorInsNamesLit] at hm_nm
      have hof : Env.ofTable m8XorGaussSpecTable r.name g.as g.rs xs m Q X := by
        rw [hnme]; exact m8Xor_elim_xorGauss he_mem hnm_not_inner hs
      obtain ⟨_, _, heff⟩ := m8Xor_ofTable_sig_elim m8XorGaussSpecTable_nodup hr_mem hof
      exact himpl xs m Q X heff
    · exact m8Xor_mem_wp_of_tableImpl h2 (fun e he => hsub e (List.mem_cons_of_mem _ he)) g htl
        xs m Q X hs

/-- Closed `433/433` `ModuleOk` for `FullM8XorAssembly.m8XorFidelityModule` (`0` hooks). -/
theorem m8XorFidelity_moduleOk : ModuleOk m8XorFidelityEnv m8XorFidelityModule := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have rXorGauss : ∀ a m Q X, fullXorGaussSpec a m Q X →
      m8XorFidelityEnv "full_xor_gauss" [i64] [i64] a m Q X :=
    fun a m Q X hs => M8XorFidelityEnv.xorGauss
      (Env.ofTable_of_mem
        (e := ⟨"full_xor_gauss", [i64], [i64], fullXorGaussSpec, true⟩)
        (List.mem_of_getElem? (i := 18) rfl) m8XorGaussSpecTable_nodup hs)
  have rSubst : ∀ a m Q X, fullSubstituteSpec a m Q X →
      m8XorFidelityEnv "full_substitute" [i64] [i64] a m Q X :=
    m8Xor_m7_base_row hc2p.substitute (by decide)
  have rSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      m8XorFidelityEnv "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X :=
    m8Xor_m7_base_row hc1.hdrSetWm (by decide) rfl (fun _ _ _ _ h => m6HdrW2aSpec_monoX h)
  have rInner : ∀ a m Q X, m6ProbeSpec a m Q X →
      m8XorFidelityEnv "full_probe_m7_inner" [i64, .bool] [i64] a m Q X :=
    fun _ _ _ _ hs => M8XorFidelityEnv.probeInner hs
  refine patchModule_moduleOk m7Fidelity_moduleOk m8XorFidelity_acyclic
    (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact m8ProbeWrapFn_wf)
    ?_ (fun _ _ _ _ _ _ _ h => M8XorFidelityEnv.base h) ?_ ?_ ?_
  · intro p hp h hh
    rcases List.mem_singleton.mp hp with rfl
    rcases List.mem_append.mp hh with h1 | h2
    · exact m8XorGaussFns_wf _ h1
    · rcases List.mem_singleton.mp h2 with rfl; exact fullProbeM7InnerFn_wf
  · intro g hg _hnone
    refine Or.inr fun xs m Q X hs => m8Xor_elim_base ?_ hs
    intro hmem
    have : g.name ∈ m7FidelityFns.map Fn.name := List.mem_map.mpr ⟨g, hg, rfl⟩
    rw [← m8XorIns_names_eq] at hmem
    obtain ⟨h, hh, hgn⟩ := List.mem_map.mp hmem
    exact m8XorIns_not_in_m7Fid h hh (hgn ▸ this)
  · intro r hr xs m Q X hs
    rcases List.mem_singleton.mp hr with rfl
    exact m8ProbeWrap_wp m8XorFidelityEnv rXorGauss rSubst rSetWm rInner xs m Q X
      (m8Xor_elim_probeM6 hs)
  · intro p hp h hh xs m Q X hs
    rcases List.mem_singleton.mp hp with rfl
    rcases List.mem_append.mp hh with h1 | h2
    · exact m8Xor_mem_wp_of_tableImpl m8XorGauss_tableImpl_in_m8Env (fun _ he => he) h h1
        xs m Q X hs
    · rcases List.mem_singleton.mp h2 with rfl
      exact m8Xor_probeInner_wp xs m Q X (m8Xor_elim_probeInner hs)

/-! ## 3. Top-Level `kissat_solve_bytes` Soundness & Top-Level UNSAT NV -/

/-- `kissat_solve_bytes` is in `m8XorFidelityModule.fns`. -/
theorem m8XorFidelity_solveBytes_mem : m6oSolveBytesFn ∈ m8XorFidelityModule.fns :=
  patchFns_mem_of_ne m7Fidelity_solveBytes_mem fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; decide

/-- Top-level `kissat_solve_bytes` UNSAT soundness on `m8XorFidelityModule` (`433` fns). -/
theorem m8XorFidelity_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8XorFidelityEnv FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m8XorFidelity_solveBytes_mem
  have hfn := (m8XorFidelity_moduleOk.fnsOk pre m6oSolveBytesFn post hsplit).2.2
  have hsb : m6oSolveBytesFn =
      ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
        FullM6Orch.kissat_solve_bytes_body⟩ := rfl
  rw [hsb] at hfn
  refine hfn _ m _ (fun _ _ _ _ => False)
    (M8XorFidelityEnv.base (m7FidelityEnv_solve_bytes
      (m7FidSolveBytesSpec_intro hcfit hwfit hm fun r m' hdom h20 _ hm' => ⟨hdom, h20, hm'⟩)))

/-- Host-framed machine-memory lift for `kissat_solve_bytes` on `m8XorFidelityModule`. -/
theorem m8XorFidelity_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  m7Fidelity_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic UNSAT non-vacuity (`r = 20#64`) for `kissat_solve_bytes` on
`nvM6UnsatInitMem` under closed `m8XorFidelityEnv` (`XPost := False`). -/
theorem m8XorFidelity_unsat_nv :
    Func.wp m8XorFidelityEnv FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m8XorFidelity_solveBytes_mem
  have hfn := (m8XorFidelity_moduleOk.fnsOk pre m6oSolveBytesFn post hsplit).2.2
  have hsb : m6oSolveBytesFn =
      ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
        FullM6Orch.kissat_solve_bytes_body⟩ := rfl
  rw [hsb] at hfn
  have hm0 :
      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
        nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]; exact nvM6UnsatInitMem_sep
  refine hfn _ nvM6UnsatInitMem _ _
    (M8XorFidelityEnv.base (m7FidelityEnv_solve_bytes
      (m7FidSolveBytesSpec_intro (by decide) (by decide) hm0
        fun r m' _ _ htr hm' => ?_)))
  have hr20 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound (by decide)
    nvM6Unsat_header nvM6Unsat_unitTrace
  exact ⟨hr20, nvM6UnsatCnf_unsat, by rwa [Std.ExtHashMap.sep_emp] at hm'⟩

/-! ## 4. Genuine Concrete `Mem 64` GF(2) RREF Elimination & Contradiction NV (`XPost := False`) -/

/-- Concrete 5-variable unsatisfiable XOR CNF (`32` 5-literal clauses encoding
`x0 ⊕ x1 ⊕ x2 ⊕ x3 ⊕ x4 = 0` and `x0 ⊕ x1 ⊕ x2 ⊕ x3 ⊕ x4 = 1`; each 16-clause parity half is
individually satisfiable, and their GF(2) elimination derives `0 = 1`). -/
def nvXor5Clauses : List (List Nat) :=
  (List.range 32).map fun m => xorMaskClause [0, 1, 2, 3, 4] m

def nvXor5F0 : CNF Nat := cnfOfClauses nvXor5Clauses

private theorem nvXor5F0_entails_mask (m : Nat) (hm : m < 32) :
    nvXor5F0.EntailsClause (cnfClause (xorMaskClause [0, 1, 2, 3, 4] m)) :=
  entails_mem_cnfOfClauses
    (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩)

theorem nvXor5F0_xor_zero : XorVarsSound nvXor5F0 [0, 1, 2, 3, 4] false :=
  xorVarsSound_of_parityMask (seen := 0xFFFFFFFF#32) (p := true)
    (by decide) (by decide) (by decide) fun m hm _ => nvXor5F0_entails_mask m hm

theorem nvXor5F0_xor_one : XorVarsSound nvXor5F0 [0, 1, 2, 3, 4] true :=
  xorVarsSound_of_parityMask (seen := 0xFFFFFFFF#32) (p := false)
    (by decide) (by decide) (by decide) fun m hm _ => nvXor5F0_entails_mask m hm

theorem nvXor5F0_unsat : nvXor5F0.Unsat :=
  xorVarsSound_both_unsat nvXor5F0_xor_zero nvXor5F0_xor_one

/-- Concrete 5-variable `FullCfg` (`max_vars = 5`, `scratch_cap = 4`, `avail = 2388`, `slack = 0`).
-/
def nvXor5Cfg : FullCfg where
  hdr := 0x1000#64
  avail := 2388
  mv := 5
  max_vars := 5
  bva_cap := 0
  nc := 32
  arena_cap := 0
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 4
  hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

/-- Concrete pre-RREF `FullScratch`: `work_stk2` maps cols `0..4` to vars `0..4`, and
`scratch_buf = [31#32, 0#32, 63#32, 0#32]` packs row 0 = `x0⊕x1⊕x2⊕x3⊕x4 = 0` (`0b011111`) and
row 1 = `x0⊕x1⊕x2⊕x3⊕x4 = 1` (`0b111111`). -/
def nvXor5Scratch (scr : List (BitVec 32)) : FullScratch where
  heap_len := 0
  scinc := 0#64; rel_period := 0#64; rel_limit := 0#64; rel_wait := 0#64
  rel_u := 0#64; rel_v := 0#64; rel_trigger := 0#64; conflicts := 0#64
  learned_lits := 0#64; min_removed := 0#64; delayed_len := 0; stable := 0#64
  switched := 0#64; mode_count := 0#64; mode_confl_lim := 0#64; mode_tick_lim := 0#64
  mode_saved_ticks := 0#64; search_ticks := 0#64; q_first := 0#64; q_last := 0#64
  q_search_idx := 0#64; q_search_stamp := 0#64; q_cur_stamp := 0#64
  target_assigned := 0#64; best_assigned := 0#64; rephase_limit := 0#64; rephased := 0#64
  reduce_limit := 0#64; reductions := 0#64; tier1 := 0#64; tier2 := 0#64
  restarts := 0#64; restart_limit := 0#64; ema_fast_biased := 0#64; ema_fast_exp := 0#64
  ema_slow_biased := 0#64; ema_slow_exp := 0#64; extend_len := 0; rng_state := 0#64
  chrono_levels := 0#64; otfs_cnt := 0#64; eager_sub_cnt := 0#64; probe_limit := 0#64
  probings := 0#64; elim_limit := 0#64; eliminations := 0#64; elim_bound := 0#64
  iterating := 0#64; hbr_cnt := 0#64; trans_cnt := 0#64; viv_cnt := 0#64
  subst_cnt := 0#64; cong_cnt := 0#64; sweep_cnt := 0#64; bve_cnt := 0#64
  bce_cnt := 0#64; bva_cnt := 0#64; walk_cnt_stat := 0#64; fwd_sub_cnt := 0#64
  fwd_str_cnt := 0#64; ant_sz := 0#64; res_sz := 0#64
  walk_vals := List.replicate 10 0#8
  phases := List.replicate 5 0#8
  phases_target := List.replicate 5 0#8
  phases_best := List.replicate 5 0#8
  walk_best := List.replicate 5 0#8
  heap := List.replicate 5 0#32
  pos := List.replicate 5 0#32
  shrink_stk := List.replicate 5 0#32
  q_prev := List.replicate 5 0#32
  q_next := List.replicate 5 0#32
  q_stamp := List.replicate 5 0#32
  wsort := List.replicate 10 0#32
  work_stk1 := List.replicate 10 0#32
  work_stk2 := [0#32, 1#32, 2#32, 3#32, 4#32, 0#32, 0#32, 0#32, 0#32, 0#32]
  tarjan_mark := List.replicate 10 0#32
  tarjan_reach := List.replicate 10 0#32
  score := List.replicate 5 0#64
  sim_sig := List.replicate 5 0#64
  glue_used := List.replicate 64 0#32
  last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []
  red_refs := []
  extend_stk := []
  scratch_buf := scr

/-- Concrete 5-variable `FullState` parameterized by `inconsistent` and packed GF(2) matrix
`scratch_buf`. -/
def nvXor5MkState (inc : BitVec 64) (scr : List (BitVec 32)) : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 5, unassigned := 5#64
      arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
      first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64, num_binary := 0#64
      unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0
      cur_level := 0, fuel := 0#64, confl_ref := 0#64, confl_type := 0#64
      confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0
      min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
      inconsistent := inc
      vals := List.replicate 10 0#8
      lit_mark := List.replicate 10 0#8
      mrk := List.replicate 5 0#8
      flags := List.replicate 5 0#32
      lvl := List.replicate 5 0#32
      rsns := List.replicate 5 0xFFFFFFFF#32
      trl := List.replicate 5 0#32
      trail_pos := List.replicate 5 0#32
      tmp := List.replicate 5 0#32
      min_clr := List.replicate 5 0#32
      frame_trail := List.replicate 6 0#32
      frame_dec := List.replicate 6 0#32
      wvec := List.replicate 20 0#32
      repr := List.replicate 10 0#32
      min_stk := List.replicate 12 0#32
      arena := []
      wstk := [0#32] }
  scratch := nvXor5Scratch scr

def nvXor5PreState : FullState := nvXor5MkState 0#64 [31#32, 0#32, 63#32, 0#32]
def nvXor5PostRrefState : FullState := nvXor5MkState 0#64 [31#32, 0#32, 32#32, 0#32]
def nvXor5PostEmitState : FullState := nvXor5MkState 1#64 [31#32, 0#32, 32#32, 0#32]

def nvXor5Bytes (inc : BitVec 64) (scr : List (BitVec 32)) : List UInt8 :=
  let s := nvXor5MkState inc scr
  let bHdr := bytes64 [5#64, 32#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvXor5Cfg s)
  let bBytes :=
    (bytesOf (t := i8) s.core.vals ++ List.replicate 6 0) ++
    (bytesOf (t := i8) s.scratch.walk_vals ++ List.replicate 6 0) ++
    (bytesOf (t := i8) s.core.lit_mark ++ List.replicate 6 0) ++
    (bytesOf (t := i8) s.core.mrk ++ List.replicate 3 0) ++
    (bytesOf (t := i8) s.scratch.phases ++ List.replicate 3 0) ++
    (bytesOf (t := i8) s.scratch.phases_target ++ List.replicate 3 0) ++
    (bytesOf (t := i8) s.scratch.phases_best ++ List.replicate 3 0) ++
    (bytesOf (t := i8) s.scratch.walk_best ++ List.replicate 3 0)
  let bU32A :=
    (bytesOf (t := i32) s.core.flags ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.lvl ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.rsns ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.trl ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.trail_pos ++ List.replicate 4 0)
  let bU32B :=
    (bytesOf (t := i32) s.core.tmp ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.scratch.heap ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.scratch.pos ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.min_clr ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.scratch.shrink_stk ++ List.replicate 4 0)
  let bU32C :=
    (bytesOf (t := i32) s.scratch.q_prev ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.scratch.q_next ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.scratch.q_stamp ++ List.replicate 4 0) ++
    (bytesOf (t := i32) s.core.frame_trail ++ List.replicate 0 0) ++
    (bytesOf (t := i32) s.core.frame_dec ++ List.replicate 0 0)
  let bWvec :=
    bytesOf (t := i32) s.core.wvec ++
    bytesOf (t := i32) s.core.repr ++
    bytesOf (t := i32) s.scratch.wsort ++
    bytesOf (t := i32) s.scratch.work_stk1 ++
    bytesOf (t := i32) s.scratch.work_stk2 ++
    bytesOf (t := i32) s.scratch.tarjan_mark ++
    bytesOf (t := i32) s.scratch.tarjan_reach ++
    bytes64 s.scratch.score ++
    bytes64 s.scratch.sim_sig
  let bTail :=
    bytesOf (t := i32) s.core.min_stk ++
    bytesOf (t := i32) s.scratch.glue_used ++
    bytesOf (t := i32) s.scratch.last_learned ++
    bytesOf (t := i32) s.core.arena ++
    bytesOf (t := i32) s.core.wstk ++
    bytesOf (t := i32) s.scratch.delayed ++
    bytesOf (t := i32) s.scratch.red_refs ++
    bytesOf (t := i32) s.scratch.extend_stk ++
    bytesOf (t := i32) s.scratch.scratch_buf ++
    List.replicate 0 0
  bHdr ++ bBytes ++ bU32A ++ bU32B ++ bU32C ++ bWvec ++ bTail

def nvXor5PreMem : Mem 64 := (nvXor5Bytes 0#64 [31#32, 0#32, 63#32, 0#32]).At nvXor5Cfg.hdr

theorem nvXor5PreMem_ok : FullMem nvXor5Cfg nvXor5PreState nvXor5PreMem := by
  let c := nvXor5Cfg; let s := nvXor5PreState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 3 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 5#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 10#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 20#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 24#64 := rfl
  have hHdr := nv_join_pair
    (nv_arr64_p (a := c.hdr) (xs := [5#64, 32#64, 0#64, 0#64]) 32 rfl (by decide))
    (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
      (by rw [Full.hdrTailWords_length]) (by decide))
    (by decide) (by decide)
  have hBytes := by
    have h1 := nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 10 6 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 10 6 rfl
      (by decide)
    have h3 := nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 10 6 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 5 3 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 5 3 rfl (by decide)
    have h6 := nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 5 3
      rfl (by decide)
    have h7 := nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 5 3 rfl
      (by decide)
    have h8 := nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 5 3 rfl
      (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 10#64) 6 ⋆ region (c.pWalkVals + 10#64) 6 ⋆
      region (c.pLitMark + 10#64) 6 ⋆ region (c.pMark + 5#64) 3
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_sep_reorg (nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => nv_zip4 hm
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have hall := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg hall
      (Q := FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
      fun _ hm => by
        have hfin := nv_zip4_tail hm
        unfold FullScrByteArrs FullCfg.padBytes
        rw [hvb, hmb, hmv2, hmv1]
        simpa only [pB1, sep_assoc] using hfin
  have hU32A := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 20 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 20 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 20 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 20 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 20 4 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide))
      (Q := (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
      fun _ hm => by unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 20 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 20 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 20 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 20 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 20 4 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide))
      (Q := (array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
      fun _ hm => by unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 20 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 20 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 20 4 rfl
      (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 24 0 rfl
      (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 24 0 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide))
      (Q := (array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆ array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
      fun _ hm => by unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec := by
    have h1 := nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 80 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 40 rfl (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 40 rfl (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 40 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 40 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 40 rfl
      (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 40 rfl
      (by decide)
    have h8 := nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 40 rfl (by decide)
    have h9 := nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 40 rfl (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h12345678 h9 (by decide) (by decide))
      (Q := (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
      fun _ hm => by unfold FullScrWksArrs; exact sep_ac hm
  have hTail := by
    have h1 := nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 48 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 16 rfl
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := nv_join_pair h12345678 h9 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h123456789 h10 (by decide) (by decide))
      (Q := array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
      fun _ hm => by unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := nv_join_pair h02 hU32B (by decide) (by decide)
  have h04 := nv_join_pair h03 hU32C (by decide) (by decide)
  have h05 := nv_join_pair h04 hWvec (by decide) (by decide)
  exact (nv_sep_reorg (nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => by
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
      FullScrMetaArrs FullCfg.pad dimacsState
    exact sep_ac hm).2

private theorem nvXor5_readU64_env :
    ∀ a m Q X, fullXorReadU64Spec a m Q X →
      m8XorFidelityEnv "full_xor_read_u64" [i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => M8XorFidelityEnv.xorGauss
    (Env.ofTable_of_mem
      (e := ⟨"full_xor_read_u64", [i64, i64], [i64], fullXorReadU64Spec, true⟩)
      (List.mem_of_getElem? (i := 9) rfl) m8XorGaussSpecTable_nodup h)

private theorem nvXor5_xorRows_env :
    ∀ a m Q X, fullXorXorRowsSpec a m Q X →
      m8XorFidelityEnv "full_xor_xor_rows" [i64, i64, i64, i64, i64] [] a m Q X :=
  fun _ _ _ _ h => M8XorFidelityEnv.xorGauss
    (Env.ofTable_of_mem
      (e := ⟨"full_xor_xor_rows", [i64, i64, i64, i64, i64], [], fullXorXorRowsSpec, true⟩)
      (List.mem_of_getElem? (i := 12) rfl) m8XorGaussSpecTable_nodup h)

private theorem nvXor5_rref_scr_pin {scr' : List (BitVec 32)}
    (hlen : scr'.length = 4)
    (hr0 : ∀ i < 2,
      scr'[0 + 0 * 2 + i]? = ([31#32, 0#32, 63#32, 0#32] : List (BitVec 32))[0 + 0 * 2 + i]?)
    (hr1 : rowU64 scr' (0 + 1 * 2) 0 =
      rowU64 [31#32, 0#32, 63#32, 0#32] (0 + 1 * 2) 0 ^^^
      rowU64 [31#32, 0#32, 63#32, 0#32] (0 + 0 * 2) 0) :
    scr' = [31#32, 0#32, 32#32, 0#32] := by
  have h0 : scr'[0]? = some 31#32 := hr0 0 (by decide)
  have h1 : scr'[1]? = some 0#32 := hr0 1 (by decide)
  have hr1_eq : rowU64 scr' 2 0 = 32#64 := by
    have hv : rowU64 [31#32, 0#32, 63#32, 0#32] 2 0 ^^^
        rowU64 [31#32, 0#32, 63#32, 0#32] 0 0 = 32#64 := by decide
    simpa [hv] using hr1
  have h2_lt : 2 < scr'.length := by omega
  have h3_lt : 3 < scr'.length := by omega
  have h2v : scr'[2]'h2_lt = 32#32 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hbit := congrArg (fun x : BitVec 64 => x.getLsbD i) hr1_eq
    unfold rowU64 at hbit
    rw [List.getElem?_eq_getElem h2_lt, List.getElem?_eq_getElem h3_lt, Option.getD_some,
      Option.getD_some, rowU64_lo_hi] at hbit
    simp only [hi, ↓reduceIte] at hbit
    have h32 : (32#64 : BitVec 64).getLsbD i = (32#32 : BitVec 32).getLsbD i := by
      rw [show (32#64 : BitVec 64) = (32#32 : BitVec 32).setWidth 64 from rfl,
        BitVec.getLsbD_setWidth]
      simp [show i < 64 by omega]
    exact hbit.trans h32
  have h3v : scr'[3]'h3_lt = 0#32 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hbit := congrArg (fun x : BitVec 64 => x.getLsbD (i + 32)) hr1_eq
    unfold rowU64 at hbit
    rw [List.getElem?_eq_getElem h2_lt, List.getElem?_eq_getElem h3_lt, Option.getD_some,
      Option.getD_some, rowU64_lo_hi] at hbit
    simp only [show ¬ i + 32 < 32 by omega, ↓reduceIte] at hbit
    have hrhs : (32#64 : BitVec 64).getLsbD (i + 32) = false := by
      have hi32 : (32 : Nat) < 2 ^ (i + 32) := by
        have h2pow : 2 ^ 32 ≤ 2 ^ (i + 32) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      rw [show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, BitVec.getLsbD_ofNat]
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hi32]
    simp only [Nat.add_sub_cancel, hrhs] at hbit
    simpa using hbit
  have h2 : scr'[2]? = some 32#32 := by
    rw [List.getElem?_eq_getElem h2_lt, h2v]
  have h3 : scr'[3]? = some 0#32 := by
    rw [List.getElem?_eq_getElem h3_lt, h3v]
  refine List.ext_getElem (by simp [hlen]) fun i hi _ => ?_
  have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi4 with rfl | rfl | rfl | rfl
  · exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans h0)
  · exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans h1)
  · exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans h2)
  · exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans h3)

/-- Genuine concrete `Mem 64` GF(2) RREF elimination NV (`XPost := False`): runs
`full_xor_rref_body` directly on `nvXor5PreMem` (`[31, 0, 63, 0]` = `x0⊕..⊕x4=0` & `x0⊕..⊕x4=1`)
under closed `m8XorFidelityEnv` and pins the EXACT concrete post-RREF image
`FullMem nvXor5Cfg nvXor5PostRrefState m'` (`[31, 0, 32, 0]`, deriving the `0 = 1` row `0b100000`).
-/
theorem nv_m8_xor_rref_concrete :
    Func.wp m8XorFidelityEnv full_xor_rref_body
      (nvXor5Cfg.pScratchBuf, 0#64, 2#64, 5#64, ()) nvXor5PreMem
      (fun () m' => FullMem nvXor5Cfg nvXor5PostRrefState m')
      (fun _ _ _ _ => False) := by
  have hm0 : (FullMem nvXor5Cfg nvXor5PreState ⋆ emp) nvXor5PreMem := by
    rw [sep_emp]; exact nvXor5PreMem_ok
  have hm0_f := focus_full_scr_buf hm0
  let Rest := FullScrBufRest nvXor5Cfg nvXor5PreState ⋆ emp
  let scr0 : List (BitVec 32) := [31#32, 0#32, 63#32, 0#32]
  let scr1 : List (BitVec 32) := [31#32, 0#32, 32#32, 0#32]
  have hw64_1 : ((5#64 + 64) >>> OfNat.ofNat 6 : BitVec 64) = 1#64 := rfl
  have hru_2 : ((1#64 : BitVec 64) <<< OfNat.ofNat 1 : BitVec 64) = 2#64 := rfl
  c0_hstraight
  rw [hw64_1, hru_2]
  let Jouter : Tup Val [i64, i64] → Mem 64 → Prop := fun (rank, col, ()) m =>
    (rank = 0#64 ∧ col = 0#64 ∧ (array (t := i32) nvXor5Cfg.pScratchBuf scr0 ⋆ Rest) m) ∨
    (rank = 1#64 ∧ 1 ≤ col.toNat ∧ col.toNat ≤ 5 ∧
      (array (t := i32) nvXor5Cfg.pScratchBuf scr1 ⋆ Rest) m)
  refine wp_loop_inv Jouter (fun (_, col, ()) _ => 5 - col.toNat)
    (fun _ h => by
      c0_hstraight
      exact h (0#64, 0#64, ()) nvXor5PreMem (Or.inl ⟨rfl, rfl, hm0_f⟩)) ?_
  rintro _ ⟨rank, col, ⟨⟩⟩ m hJ ih
  rcases hJ with ⟨rfl, rfl, hm⟩ | ⟨rfl, hc1, hc5, hm⟩
  · -- col = 0, rank = 0: pivot at r = 0, eliminate row 1 (63 ^^^ 31 = 32), rank := 1, col := 1
    c0_hsplit
    · c0_hsplit
      · c0_hstraight
        let Jpiv_exit : Tup Val [i64, i64] → Mem 64 → Prop := fun (piv, _, ()) m1 =>
          piv = 0#64 ∧ m1 = m
        refine wp_join_group Jpiv_exit ?_ ?_
        · rintro _ ⟨piv, _, ⟨⟩⟩ m1 ⟨rfl, hm1_eq⟩
          subst m1
          let Jcol_step : Tup Val [i64, i64] → Mem 64 → Prop := fun (rank', _, ()) mc =>
            rank' = 1#64 ∧ (array (t := i32) nvXor5Cfg.pScratchBuf scr1 ⋆ Rest) mc
          refine wp_join_group Jcol_step ?_ ?_
          · rintro _ ⟨rank', _, ⟨⟩⟩ mc ⟨rfl, hmc⟩
            c0_hstraight
            exact ih (1#64, 1#64, ()) mc (by decide)
              (Or.inr ⟨rfl, by decide, by decide, hmc⟩)
          · intro _ hJc
            c0_hsplit
            · refine wp_join0
                (fun m2 => (array (t := i32) nvXor5Cfg.pScratchBuf scr0 ⋆ Rest) m2) ?_ ?_
              · rintro _ m2 hm2
                -- Eliminate loop: r = 0 (skip), r = 1 (read 63 -> xor_rows -> scr1), r = 2 (exit)
                let Jelim : Tup Val [i64] → Mem 64 → Prop := fun (r, ()) me =>
                  (r = 0#64 ∧ (array (t := i32) nvXor5Cfg.pScratchBuf scr0 ⋆ Rest) me) ∨
                  (r = 1#64 ∧ (array (t := i32) nvXor5Cfg.pScratchBuf scr0 ⋆ Rest) me) ∨
                  (r = 2#64 ∧ (array (t := i32) nvXor5Cfg.pScratchBuf scr1 ⋆ Rest) me)
                refine wp_loop_inv Jelim (fun (r, ()) _ => 2 - r.toNat)
                  (fun _ h => by c0_hstraight; exact h (0#64, ()) m2 (Or.inl ⟨rfl, hm2⟩)) ?_
                rintro _ ⟨r, ⟨⟩⟩ me hJe ihe
                rcases hJe with ⟨rfl, hme⟩ | ⟨rfl, hme⟩ | ⟨rfl, hme⟩
                · c0_hsplit
                  · refine wp_join0 (fun me' =>
                        (array (t := i32) nvXor5Cfg.pScratchBuf scr0 ⋆ Rest) me')
                      (fun _ me' hme' => by
                        c0_hstraight
                        exact ihe (1#64, ()) me' (by decide) (Or.inr (Or.inl ⟨rfl, hme'⟩)))
                      (fun _ hJ => by
                        c0_hsplit
                        · exfalso; simp_all
                        · c0_hstraight; exact hJ me hme)
                  · exfalso; bv_omega
                · c0_hsplit
                  · refine wp_join0 (fun me' =>
                        (array (t := i32) nvXor5Cfg.pScratchBuf scr1 ⋆ Rest) me')
                      (fun _ me' hme' => by
                        c0_hstraight
                        exact ihe (2#64, ()) me' (by decide) (Or.inr (Or.inr ⟨rfl, hme'⟩)))
                      (fun _ hJ => by
                        c0_hsplit
                        · c0_hstraight
                          apply wp_call_of_spec
                          dsimp only [vals, Arg.val]
                          refine nvXor5_readU64_env _ _ _ _
                            ⟨scr0, Rest, by decide, by decide, hme, ?_⟩
                          dsimp only
                          have hrw : rowU64 scr0 (0#64 + 1#64 * 2#64 +
                              ((0#64 >>> OfNat.ofNat 6 <<< OfNat.ofNat 1))).toNat 0 = 63#64 := by
                            decide
                          rw [hrw]
                          refine wp_join0 (fun me' =>
                              (array (t := i32) nvXor5Cfg.pScratchBuf scr1 ⋆ Rest) me')
                            (fun _ me' hme' => by c0_hstraight; exact hJ me' hme')
                            fun _ hJx => by
                              c0_hsplit
                              · c0_hstraight
                                apply wp_call_of_spec
                                dsimp only [vals, Arg.val]
                                refine nvXor5_xorRows_env _ _ _ _
                                  ⟨scr0, 2, Rest, by decide, by decide, by decide, by decide,
                                   by decide, hme, fun scr' me' hlen' _ hkeep hxor hme' => ?_⟩
                                have hscreq : scr' = scr1 :=
                                  nvXor5_rref_scr_pin hlen' (hkeep 0 (by decide) (by decide))
                                    (hxor 0 (by decide))
                                rw [hscreq] at hme'
                                c0_hstraight; exact hJx me' hme'
                              · exfalso
                                exact (by
                                  decide :
                                    (63#64 &&& 1#64 <<< ((0#64 &&& 63#64).toNat % 64)) ≠ 0#64)
                                  hc
                        · exfalso; simp_all)
                  · exfalso; bv_omega
                · c0_hsplit
                  · exfalso; bv_omega
                  · c0_hstraight
                    exact hJc (1#64, 2#64, ()) me ⟨rfl, hme⟩
              · intro _ hJsw
                c0_hsplit
                · exfalso; simp_all
                · c0_hstraight; exact hJsw m hm
            · exfalso; bv_omega
        · intro _ hJpiv_exit
          refine wp_loop_inv (fun (r, ()) m1 => r = 0#64 ∧ m1 = m) (fun (r, ()) _ => 2 - r.toNat)
            (fun _ h => by c0_hstraight; exact h (0#64, ()) m ⟨rfl, rfl⟩) ?_
          rintro _ ⟨r, ⟨⟩⟩ m1 ⟨rfl, hm1_eq⟩ _
          subst m1
          c0_hsplit
          · c0_hstraight
            apply wp_call_of_spec
            dsimp only [vals, Arg.val]
            refine nvXor5_readU64_env _ _ _ _ ⟨scr0, Rest, by decide, by decide, hm, ?_⟩
            dsimp only
            have hrw : rowU64 scr0 (0#64 + 0#64 * 2#64 +
                (0#64 >>> OfNat.ofNat 6 <<< OfNat.ofNat 1)).toNat 0 = 31#64 := by decide
            rw [hrw]
            c0_hsplit
            · c0_hstraight; exact hJpiv_exit (0#64, 0#64, ()) m ⟨rfl, rfl⟩
            · exfalso
              exact (by
                decide :
                  (31#64 &&& 1#64 <<< ((0#64 &&& 63#64).toNat % 64)) ≠ 0#64)
                hc
          · exfalso; bv_omega
      · exfalso; bv_omega
    · exfalso; bv_omega
  · -- rank = 1, col ∈ 1..5: row 1 is 32#64 (bit 5 only), so no pivot for col ∈ 1..4; exits at 5
    by_cases hlt5 : col.toNat < 5
    · have hcol4 : col = 1#64 ∨ col = 2#64 ∨ col = 3#64 ∨ col = 4#64 := by
        have : col.toNat = 1 ∨ col.toNat = 2 ∨ col.toNat = 3 ∨ col.toNat = 4 := by omega
        rcases this with h | h | h | h
        · exact Or.inl (BitVec.eq_of_toNat_eq h)
        · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))
        · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))
        · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq h)))
      c0_hsplit
      · c0_hsplit
        · have hwidx_ofNat : (col >>> OfNat.ofNat 6 : BitVec 64) = 0#64 := by
            rcases hcol4 with rfl | rfl | rfl | rfl <;> decide
          c0_hstraight
          let Jpiv_exit : Tup Val [i64, i64] → Mem 64 → Prop := fun (piv, _, ()) m1 =>
            piv = 2#64 ∧ m1 = m
          refine wp_join_group Jpiv_exit ?_ ?_
          · rintro _ ⟨piv, r_piv, ⟨⟩⟩ m1 ⟨rfl, hm1_eq⟩
            subst m1
            let Jcol_step : Tup Val [i64, i64] → Mem 64 → Prop := fun (rank', _, ()) mc =>
              rank' = 1#64 ∧ mc = m
            refine wp_join_group Jcol_step ?_ ?_
            · rintro _ ⟨rank', _, ⟨⟩⟩ mc ⟨rfl, hmc_eq⟩
              subst mc
              c0_hstraight
              have hc1' : (col + 1#64).toNat = col.toNat + 1 := by bv_omega
              exact ih (1#64, col + 1#64, ()) m (by dsimp only; omega)
                (Or.inr ⟨rfl, by omega, by omega, hm⟩)
            · intro _ hJc
              c0_hsplit
              · exfalso; bv_omega
              · c0_hstraight; exact hJc (1#64, r_piv, ()) m ⟨rfl, rfl⟩
          · intro _ hJpiv_exit
            refine wp_loop_inv (fun (r, ()) m1 => (r = 1#64 ∨ r = 2#64) ∧ m1 = m)
              (fun (r, ()) _ => 2 - r.toNat)
              (fun _ h => by c0_hstraight; exact h (1#64, ()) m ⟨Or.inl rfl, rfl⟩) ?_
            rintro _ ⟨r, ⟨⟩⟩ m1 ⟨hr, hm1_eq⟩ ihp
            subst m1
            rcases hr with rfl | rfl
            · c0_hsplit
              · c0_hstraight
                apply wp_call_of_spec
                dsimp only [vals, Arg.val]
                refine nvXor5_readU64_env _ _ _ _
                  ⟨scr1, Rest, by rw [hwidx_ofNat]; decide, by decide, hm, ?_⟩
                dsimp only
                have hrw :
                    rowU64 scr1 (0#64 + 1#64 * 2#64 +
                      (col >>> OfNat.ofNat 6 <<< OfNat.ofNat 1)).toNat 0 = 32#64 := by
                  rw [hwidx_ofNat]; decide
                rw [hrw]
                have hmask0 : (32#64 &&& (1#64 <<< ((col &&& 63#64).toNat % 64))) = 0#64 := by
                  rcases hcol4 with rfl | rfl | rfl | rfl <;> decide
                c0_hsplit
                · exfalso
                  change (32#64 &&& (1#64 <<< ((col &&& 63#64).toNat % 64))) ≠ 0#64 at hc
                  rw [hmask0] at hc; exact hc rfl
                · c0_hstraight
                  exact ihp (2#64, ()) m (by decide) ⟨Or.inr rfl, rfl⟩
              · exfalso; bv_omega
            · c0_hsplit
              · exfalso; bv_omega
              · c0_hstraight; exact hJpiv_exit (2#64, 2#64, ()) m ⟨rfl, rfl⟩
        · exfalso; bv_omega
      · exfalso; bv_omega
    · c0_hsplit
      · exfalso; bv_omega
      · c0_hstraight
        have hm_full := unfocus_full_scr_buf hm
        rw [sep_emp] at hm_full
        exact hm_full

/-- Genuine concrete `Mem 64` contradiction-emission NV (`XPost := False`): runs
`full_xor_emit_mat_body` directly on ANY concrete `m1` backing `nvXor5PostRrefState` (`[31,0,32,0]`)
under closed `m8XorFidelityEnv`, skipping row 0 (`wt = 5 > 4`), detecting row 1 (`wt = 0`,
`rhs_bit = 1`), writing `h->inconsistent = 1`, and returning EXACT `r = 20#64` + `nvXor5F0.Unsat` +
exact pinned `FullMem nvXor5Cfg nvXor5PostEmitState m'`. -/
theorem nv_m8_xor_emit_mat_concrete {m1 : Mem 64}
    (hm1 : FullMem nvXor5Cfg nvXor5PostRrefState m1) :
    Func.wp m8XorFidelityEnv full_xor_emit_mat_body
      (nvXor5Cfg.hdr, 0#64, 2#64, 5#64, ()) m1
      (fun (r, ()) m' =>
        r = 20#64 ∧ nvXor5F0.Unsat ∧ FullMem nvXor5Cfg nvXor5PostEmitState m')
      (fun _ _ _ _ => False) := by
  have hm1e : (FullMem nvXor5Cfg nvXor5PostRrefState ⋆ emp) m1 := by
    rw [sep_emp]; exact hm1
  let scr1 : List (BitVec 32) := [31#32, 0#32, 32#32, 0#32]
  c0_hstraight
  generalize hw64 : ((5#64 + 64) >>> OfNat.ofNat 6 : BitVec 64) = w64
  generalize hru : (w64 <<< OfNat.ofNat 1 : BitVec 64) = wru
  generalize hlw : (5#64 >>> OfNat.ofNat 6 : BitVec 64) = wlast
  have hw64_v : w64 = 1#64 := by rw [← hw64]; decide
  have hru_v : wru = 2#64 := by rw [← hru, hw64_v]; decide
  have hlw_v : wlast = 0#64 := by rw [← hlw]; decide
  clear hw64 hru hlw
  subst hw64_v hru_v hlw_v
  let Jr : Tup Val [i64, i64] → Mem 64 → Prop := fun (_ec, r, ()) mr =>
    (r = 0#64 ∨ r = 1#64) ∧ mr = m1
  refine wp_loop_inv Jr (fun (_, r, ()) _ => 2 - r.toNat)
    (fun _ h => by c0_hstraight; exact h (0#64, 0#64, ()) m1 ⟨Or.inl rfl, rfl⟩) ?_
  rintro _ ⟨ec, r, ⟨⟩⟩ mr ⟨hr, hmr_eq⟩ ihr
  subst mr
  rcases hr with rfl | rfl
  · -- r = 0: rhs_bit = 0, wv = 31, wt = 5 > 4 -> break & skip to r = 1
    c0_hsplit
    · have hm1_f := focus_full_scr_buf hm1e
      c0_hstraight
      apply wp_call_of_spec
      dsimp only [vals, Arg.val]
      refine nvXor5_readU64_env _ _ _ _
        ⟨scr1, FullScrBufRest nvXor5Cfg nvXor5PostRrefState ⋆ emp, by decide, by decide, hm1_f, ?_⟩
      dsimp only
      have hrw0 : rowU64 scr1 0 0 = 31#64 := by decide
      rw [show (0#64 + 0#64 * 2#64 + 0#64 <<< OfNat.ofNat 1).toNat = 0 from rfl, hrw0]
      let Jwt_exit : Tup Val [i64, i64] → Mem 64 → Prop := fun (wt, _, ()) mw =>
        wt = 5#64 ∧ mw = m1
      refine wp_join_group Jwt_exit ?_ ?_
      · rintro _ ⟨wt, _, ⟨⟩⟩ mw ⟨rfl, hmw_eq⟩
        subst mw
        let Jrow : Tup Val [i64, i64] → Mem 64 → Prop := fun (em', _, ()) mrow =>
          mrow = m1
        refine wp_join_group Jrow ?_ ?_
        · rintro _ ⟨em', _, ⟨⟩⟩ mrow hmrow
          subst mrow
          c0_hstraight
          exact ihr (em', 1#64, ()) m1 (by dsimp only; decide) ⟨Or.inr rfl, rfl⟩
        · intro _ hJrow
          c0_hsplit
          · exfalso; bv_omega
          · refine wp_join_group (fun (em', w', ()) m' => em' = ec ∧ m' = m1)
              (fun _ ⟨em', w', ⟨⟩⟩ m' ⟨hem, hm'⟩ => by
                subst hem; cases hm'; c0_hstraight; refine hJrow _ _ rfl) ?_
            intro _ hJle4
            c0_hsplit
            · exfalso; bv_omega
            · c0_hstraight; refine hJle4 _ m1 ⟨rfl, rfl⟩
      · intro _ hJwt_exit
        refine wp_loop_inv (fun (wt, w, ()) mw => wt = 0#64 ∧ w = 0#64 ∧ mw = m1)
          (fun (_, w, ()) _ => 1 - w.toNat)
          (fun _ h => by c0_hstraight; exact h (0#64, 0#64, ()) m1 ⟨rfl, rfl, rfl⟩) ?_
        rintro _ ⟨wt, w, ⟨⟩⟩ mw ⟨rfl, rfl, hmw_eq⟩ _
        subst mw
        c0_hsplit
        · c0_hstraight
          apply wp_call_of_spec
          dsimp only [vals, Arg.val]
          refine nvXor5_readU64_env _ _ _ _
            ⟨scr1, FullScrBufRest nvXor5Cfg nvXor5PostRrefState ⋆ emp, by decide, by decide,
             hm1_f, ?_⟩
          dsimp only
          rw [show (0#64 + 0#64 * 2#64 + 0#64 <<< OfNat.ofNat 1).toNat = 0 from rfl, hrw0]
          refine wp_join_group (fun (wv, ()) mw' => wv = 31#64 ∧ mw' = m1) ?_ ?_
          · rintro _ ⟨wv, ⟨⟩⟩ mw' ⟨rfl, hmw'_eq⟩
            subst mw'
            -- Kernighan weight loop on `31`: `(0,31) → (1,30) → … → (5,0)`, exit at `wt = 5`.
            refine wp_loop_inv
              (fun (wt', wv_t, ()) mk => mk = m1 ∧
                (wt' = 0#64 ∧ wv_t = 31#64 ∨ wt' = 1#64 ∧ wv_t = 30#64 ∨
                 wt' = 2#64 ∧ wv_t = 28#64 ∨ wt' = 3#64 ∧ wv_t = 24#64 ∨
                 wt' = 4#64 ∧ wv_t = 16#64 ∨ wt' = 5#64 ∧ wv_t = 0#64))
              (fun (wt', _, ()) _ => 5 - wt'.toNat)
              (fun _ h => by
                c0_hstraight; exact h (0#64, 31#64, ()) m1 ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩) ?_
            rintro _ ⟨wt', wv_t, ⟨⟩⟩ mk ⟨hmk, hk⟩ ihk
            subst mk
            refine wp_join0 (fun mx => mx = m1 ∧ wt' = 5#64) ?_ ?_
            · rintro _ mx ⟨hmx, rfl⟩
              subst mx
              c0_hsplit
              · c0_hstraight; exact hJwt_exit (5#64, 0#64, ()) m1 ⟨rfl, rfl⟩
              · exfalso; bv_omega
            · intro _ hJx
              rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                ⟨rfl, rfl⟩
              all_goals (c0_hsplit <;> (try c0_hsplit) <;> first
                | (exfalso; bv_omega)
                | (c0_hstraight; exact hJx m1 ⟨rfl, rfl⟩)
                | (c0_hstraight; exact ihk _ m1 (by dsimp only; decide) ⟨rfl, by decide⟩))
          · intro _ hJw
            c0_hsplit
            · c0_hstraight
              refine hJw _ m1 ⟨by decide, rfl⟩
            · exfalso; exact hc trivial
        · exfalso; bv_omega
    · exfalso; bv_omega
  · -- r = 1: row = 32#64 = 0b100000 -> rhs_bit = 1, wv & 31 = 0, wt = 0 -> inconsistent = 1, ret 20
    c0_hsplit
    · have hm1_f := focus_full_scr_buf hm1e
      c0_hstraight
      apply wp_call_of_spec
      dsimp only [vals, Arg.val]
      refine nvXor5_readU64_env _ _ _ _
        ⟨scr1, FullScrBufRest nvXor5Cfg nvXor5PostRrefState ⋆ emp,
         by decide, by decide, hm1_f, ?_⟩
      dsimp only
      have hrw1 : rowU64 scr1 2 0 = 32#64 := by decide
      rw [show (0#64 + 1#64 * 2#64 + 0#64 <<< OfNat.ofNat 1).toNat = 2 from rfl, hrw1]
      let Jwt_exit : Tup Val [i64, i64] → Mem 64 → Prop := fun (wt, _, ()) mw =>
        wt = 0#64 ∧ mw = m1
      refine wp_join_group Jwt_exit ?_ ?_
      · rintro _ ⟨wt, _, ⟨⟩⟩ mw ⟨rfl, hmw_eq⟩
        subst mw
        refine wp_join_group (fun _ _ => False) (fun _ _ _ h => h.elim) ?_
        intro _ _
        c0_hsplit
        · c0_hsplit
          · clear hm1 hm1_f
            c0_hstraight
            try rw [sep_emp] at hm
            exact ⟨rfl, nvXor5F0_unsat, hm⟩
          · exfalso
            exact (by
              decide :
                ((32#64 >>> ((5#64 &&& 63#64).toNat % 64)) &&& 1#64 : BitVec 64) ≠ 0#64)
              hc
        · exfalso; simp_all
      · intro _ hJwt_exit
        refine wp_loop_inv (fun (wt, w, ()) mw => wt = 0#64 ∧ (w = 0#64 ∨ w = 1#64) ∧ mw = m1)
          (fun (_, w, ()) _ => 1 - w.toNat)
          (fun _ h => by c0_hstraight; exact h (0#64, 0#64, ()) m1 ⟨rfl, Or.inl rfl, rfl⟩) ?_
        rintro _ ⟨wt, w, ⟨⟩⟩ mw ⟨rfl, hw, hmw_eq⟩ ihw
        subst mw
        rcases hw with rfl | rfl
        · c0_hsplit
          · c0_hstraight
            apply wp_call_of_spec
            dsimp only [vals, Arg.val]
            refine nvXor5_readU64_env _ _ _ _
              ⟨scr1, FullScrBufRest nvXor5Cfg nvXor5PostRrefState ⋆ emp, by decide, by decide,
               hm1_f, ?_⟩
            dsimp only
            rw [show (0#64 + 1#64 * 2#64 + 0#64 <<< OfNat.ofNat 1).toNat = 2 from rfl, hrw1]
            refine wp_join_group (fun (wv, ()) mw' => wv = 0#64 ∧ mw' = m1) ?_ ?_
            · rintro _ ⟨wv, ⟨⟩⟩ mw' ⟨rfl, hmw'_eq⟩
              subst mw'
              refine wp_loop_inv (fun (wt', wv_t, ()) mk => mk = m1 ∧ wt' = 0#64 ∧ wv_t = 0#64)
                (fun _ _ => 0)
                (fun _ h => by c0_hstraight; exact h (0#64, 0#64, ()) m1 ⟨rfl, rfl, rfl⟩) ?_
              rintro _ ⟨wt', wv_t, ⟨⟩⟩ mk ⟨hmk, rfl, rfl⟩ _
              subst mk
              refine wp_join0 (fun mx => mx = m1) ?_ ?_
              · intro _ mx hmx
                subst mx
                c0_hsplit
                · exfalso; bv_omega
                · c0_hstraight
                  exact ihw (0#64, 0#64 + 1#64, ()) m1 (by decide) ⟨rfl, Or.inr rfl, rfl⟩
              · intro _ hJx
                c0_hsplit
                · exfalso; exact absurd hc (by decide)
                · c0_hstraight; exact hJx m1 rfl
            · intro _ hJw
              c0_hsplit
              · c0_hstraight
                refine hJw _ m1 ⟨by decide, rfl⟩
              · exfalso; exact hc trivial
          · exfalso; bv_omega
        · c0_hsplit
          · exfalso; bv_omega
          · c0_hstraight; exact hJwt_exit (0#64, 1#64, ()) m1 ⟨rfl, rfl⟩
    · exfalso; bv_omega

/-- End-to-end concrete `Mem 64` GF(2) elimination -> contradiction NV (`XPost := False`):
starts from concrete `nvXor5PreMem` (`inconsistent = 0`, `scratch_buf = [31, 0, 63, 0]`), runs
`full_xor_rref` to derive `0 = 1` (`[31, 0, 32, 0]`), then runs `full_xor_emit_mat` to set
`inconsistent = 1` and return EXACT `r = 20#64` + `nvXor5F0.Unsat` + exact pinned
`FullMem nvXor5Cfg nvXor5PostEmitState m'`. -/
theorem nv_m8_xor_rref_then_emit_unsat :
    Func.wp m8XorFidelityEnv full_xor_rref_body
      (nvXor5Cfg.pScratchBuf, 0#64, 2#64, 5#64, ()) nvXor5PreMem
      (fun () m1 =>
        FullMem nvXor5Cfg nvXor5PostRrefState m1 ∧
        Func.wp m8XorFidelityEnv full_xor_emit_mat_body
          (nvXor5Cfg.hdr, 0#64, 2#64, 5#64, ()) m1
          (fun (r, ()) m' =>
            r = 20#64 ∧ nvXor5F0.Unsat ∧ FullMem nvXor5Cfg nvXor5PostEmitState m')
          (fun _ _ _ _ => False))
      (fun _ _ _ _ => False) :=
  wp_mono (fun _ _ hm1 => ⟨hm1, nv_m8_xor_emit_mat_concrete hm1⟩)
    (fun _ _ _ _ h => h) _ nvXor5PreMem nv_m8_xor_rref_concrete

end LeanQbe.T.Examples.Kissat.FullM8XorAssembly
