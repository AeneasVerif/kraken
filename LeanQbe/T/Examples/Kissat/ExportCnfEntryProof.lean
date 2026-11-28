/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.ExportCnfEntryProof0
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# Verified Simplified-CNF Exporter — Shard E3 (`Mem 64` WP & Soundness)

Main entrypoint proof module for `ExportCnfEntry`:
1. `kissat_simplify_export_bytes_wp`: end-to-end `XPost`-polymorphic `Mem 64` WP proof of
   `kissat_simplify_export_bytes`.
2. `exportCnfEntryFns_sound_in` & `exportCnfEntryEnv_moduleOk`: standalone `12`-fn `ModuleOk`.
3. `kissat_simplify_export_bytes_sound` & `kissat_simplify_export_bytes_sound_parsed`:
   whenever `parseDimacs cnfBytes = some F0` and `0 < out_len <= out_cap`, written `outBytes`
   parse via `LratBytes.parseDimacs` to `cnfOut` with `cnfOut.Unsat → F0.Unsat`.

Concrete `Mem 64` non-vacuity witnesses (`<= std3`, `XPost := False`) live in
`LeanQbe.T.Examples.Kissat.ExportCnfEntryProofNv`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.ExportCnfEntryProof

open Std.Sat
open Kraken
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Ref hiding isDimacsWs isDimacsDigit dimacsBound
  skipWsCommentsAux skipWsComments skipWs skipWs1 parseDigitsAux parseNat
  parseHeader parseClauseAux parseClause parseClauses parseDimacs
open LeanQbe.T.Examples.Kissat.Proof.Spec hiding
  fullM6WorkBase fullM6WorkHdr m6ExtAddr_fullM6WorkHdr
  region_work_to_m6_workBase region_work_from_m6_hdrMem
open LeanQbe.T.Examples.Kissat.ExportCnfFmt
open LeanQbe.T.Examples.Kissat.ExportCnfState
open LeanQbe.T.Examples.Kissat.ExportCnfEntry

public section

/-! ## 1. Entrypoint WP Proof (`kissat_simplify_export_bytes_wp`) -/

private theorem wp_join0_cons1 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {b : Tup Cont [[]] → Tup Val [] → Expr Val Cont rs}
    {entry : Tup Cont [[]] → Expr Val Cont rs}
    (P : Mem 64 → Prop)
    (hbody : ∀ (J : Tup Cont [[]]) (m' : Mem 64), P m' → wp Γ Q X (b J ()) m')
    (hentry : ∀ (J : Cont []), (∀ m', P m' → J () m') → wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [[]]) (fun Js => Blocks.cons (b Js) Blocks.nil) entry) m :=
  wp_join0 P (fun J m' hp => hbody (J, ()) m' hp) hentry

private def ExportEntryCallQ
    (cnf_ptr work_ptr fuel outDesc out_ptr : BitVec 64)
    (cnfBytes buf : List UInt8) (wlen : Nat) (R : Mem 64 → Prop)
    (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) (outBytes : List UInt8) (written : Nat) (m' : Mem 64),
    (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
    written < 2 ^ 64 →
    (r = 0#64 → (written = 0 ∨ buf.length < written) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length)
          (BitVec.ofNat 64 written) ⋆
        bytes out_ptr buf ⋆ R) m') →
    (r ≠ 0#64 →
      0 < written ∧ written ≤ buf.length ∧ outBytes.length = written ∧
      (∃ F0 cnfOut, parseDimacs cnfBytes = some F0 ∧
        parseDimacs outBytes = some cnfOut ∧ (cnfOut.Unsat → F0.Unsat)) ∧
      (r = 20#64 → outBytes = unsatDimacsBytes ∧
        ∃ F0, parseDimacs cnfBytes = some F0 ∧ F0.Unsat) ∧
      (r = 10#64 → outBytes = satEmptyDimacsBytes ∧
        ∃ F0, parseDimacs cnfBytes = some F0) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length)
          (BitVec.ofNat 64 written) ⋆
        bytes out_ptr (outBytes ++ buf.drop written) ⋆ R) m') →
    (∀ mv nc i0,
      cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
      fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen →
      fullAlignPad work_ptr + fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 ≤ wlen →
      i0 ≤ cnfBytes.length →
      parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
      UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
      12 ≤ buf.length → r = 20#64) →
    Q (r, ()) m'

private theorem sep_entry_init {A B P Q C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ (P ⋆ Q ⋆ C) ⋆ D ⋆ R) m) : (C ⋆ (A ⋆ B ⋆ P ⋆ Q ⋆ D ⋆ R)) m := sep_ac h

private theorem sep_entry_unfold {A B P Q C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (C ⋆ (A ⋆ B ⋆ P ⋆ Q ⋆ D ⋆ R)) m) : (A ⋆ B ⋆ (P ⋆ Q ⋆ C) ⋆ D ⋆ R) m := sep_ac h

private theorem sep_entry_ptr {A B P Q C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (C ⋆ (A ⋆ B ⋆ P ⋆ Q ⋆ D ⋆ R)) m) : (P ⋆ (A ⋆ B ⋆ Q ⋆ C ⋆ D ⋆ R)) m := sep_ac h

private theorem sep_entry_cap {A B P Q C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (C ⋆ (A ⋆ B ⋆ P ⋆ Q ⋆ D ⋆ R)) m) : (Q ⋆ (A ⋆ B ⋆ P ⋆ C ⋆ D ⋆ R)) m := sep_ac h

private theorem sep_entry_to_work {A W1 W2 W E D R : Mem 64 → Prop} {m : Mem 64}
    (hw : ∀ x, W x → (W1 ⋆ W2) x) (h : (A ⋆ W ⋆ E ⋆ D ⋆ R) m) :
    (A ⋆ W2 ⋆ (W1 ⋆ E ⋆ D ⋆ R)) m :=
  sep_ac (sep_mono hw (sep_ac h : (W ⋆ (A ⋆ E ⋆ D ⋆ R)) m))

private theorem sep_entry_merge_work {A W1 W2 W E D R : Mem 64 → Prop} {m : Mem 64}
    (hw : ∀ x, (W1 ⋆ W2) x → W x) (h : (A ⋆ W2 ⋆ (W1 ⋆ E ⋆ D ⋆ R)) m) :
    (A ⋆ W ⋆ E ⋆ D ⋆ R) m :=
  sep_ac (sep_mono hw (sep_ac h : ((W1 ⋆ W2) ⋆ (A ⋆ E ⋆ D ⋆ R)) m))

private theorem sep_entry_to_loaded {A H W1 E D R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ H ⋆ (W1 ⋆ E ⋆ D ⋆ R)) m) : (A ⋆ H ⋆ E ⋆ D ⋆ (W1 ⋆ R)) m := sep_ac h

private theorem sep_entry_collapse {A H W1 W E Xm R : Mem 64 → Prop} {m : Mem 64}
    (hw : ∀ x, (W1 ⋆ H) x → W x) (hm : (A ⋆ H ⋆ E ⋆ Xm ⋆ (W1 ⋆ R)) m) :
    (A ⋆ W ⋆ E ⋆ Xm ⋆ R) m :=
  sep_ac (sep_mono hw (sep_ac hm : ((W1 ⋆ H) ⋆ (A ⋆ E ⋆ Xm ⋆ R)) m))

private theorem simplify_export_after_mem_init
    {cnf_ptr work_ptr fuel outDesc out_ptr : BitVec 64}
    {cnfBytes buf : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m1 : Mem 64} {Q Q_init : Post [i64]} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hout_ne : outDesc ≠ 0#64) (hout_al : (outDesc &&& 7#64) = 0#64)
    (hout_fit : outDesc.toNat + 24 < 2 ^ 64)
    (hcap : buf.length < 2 ^ 64) (hout_nz : 0 < buf.length → out_ptr ≠ 0#64)
    (hout_fit2 : out_ptr.toNat + buf.length < 2 ^ 64)
    (hw_ge : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen)
    (hm1' : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
      bytes out_ptr buf ⋆ R) m1)
    (hQ : ExportEntryCallQ cnf_ptr work_ptr fuel outDesc out_ptr cnfBytes buf wlen R Q)
    (hk0 : ∀ m2, Q (0#64, ()) m2 → Q_init (0#64, ()) m2)
    (hkl : ∀ hdr m2, hdr ≠ 0#64 →
      (∀ Q_l : Post [i64], (∀ r m3, Q (r, ()) m3 → Q_l (r, ()) m3) →
        kissatSimplifyExportLoadedSpec
          (hdr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, outDesc, ()) m2 Q_l X) →
      Q_init (hdr, ()) m2) :
    fullM6MemInitExactSpec (cnf_ptr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length,
      fullM6WorkBase work_ptr, BitVec.ofNat 64 (wlen - fullAlignPad work_ptr),
      fuel, ()) m1 Q_init X := by
  have hreg_split := sep_entry_to_work
    (fun x hx => region_work_to_m6_workBase hw_ge (by omega) hx) hm1'
  have hpad8 : fullAlignPad work_ptr < 8 := fullAlignPad_lt8 work_ptr
  have hwb_toNat : (fullM6WorkBase work_ptr).toNat = work_ptr.toNat + fullAlignPad work_ptr := by
    change (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr)).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by unfold fullM6HdrTotalBytes at *; omega)]
  have hwb_fit : (fullM6WorkBase work_ptr).toNat +
      (BitVec.ofNat 64 (wlen - fullAlignPad work_ptr)).toNat < 2 ^ 64 := by
    rw [hwb_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold fullAlignPad at *; omega)]
    omega
  have hreg_bv : (bytes cnf_ptr cnfBytes ⋆
      region (fullM6WorkBase work_ptr)
        (BitVec.ofNat 64 (wlen - fullAlignPad work_ptr)).toNat ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆
        exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
        bytes out_ptr buf ⋆ R)) m1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold fullAlignPad at *; omega)]
    exact hreg_split
  refine fullM6MemInitExactSpec_of rfl hcfit hwb_fit hreg_bv (fun m2 hm2 hfail => ?_)
    (fun c ext s j rest m2 hhdr_c hav_c hcfg_c hext_c hph_c hj_le hrest_c hinv_c
      hcv_c hdcur_c hal_c _hwl_c hte_c hprop_c hcl_c _hfuel_c hoom_c hinc_c hprb_c
      hvals_c hwvec_c hm2 => ?_)
  · have hno_ok : ¬ ∃ mv nc i0,
        parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) ∧
        i0 ≤ cnfBytes.length ∧
        fullAlignPad work_ptr + fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 ≤ wlen := by
      rintro ⟨mv, nc, i0, hph0, hi0, hfx0⟩
      rcases hfail with hsmall | hbody
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hsmall; omega
      · have hlt := hbody mv nc (cnfBytes.drop i0) hph0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt; omega
    have heq : fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen := by
      unfold fullAlignPad at *; omega
    have hmerge := fun x => (congrFun (region_merge_eq heq (by omega) (a := work_ptr)) x).mp
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold fullAlignPad at *; omega)] at hm2
    have hm2_rec := sep_entry_merge_work hmerge hm2
    exact hk0 m2 (hQ 0#64 [] 0 m2 (Or.inl rfl) (by decide) (fun _ => ⟨Or.inl rfl, hm2_rec⟩)
      (fun h => absurd rfl h) (fun mv nc i0 _ _ _ _ _ hi0 hph0 _ _ =>
        absurd ⟨mv, nc, i0, hph0, hi0, by omega⟩ hno_ok))
  · have hc_nz : c.hdr ≠ 0#64 := fun h0 => by
      have hpos_hdr : c.hdr.toNat = (fullM6WorkBase work_ptr).toNat + fullM6ExtBytes := by
        rw [hhdr_c, BitVec.toNat_add,
          bv64_ofNat_toNat (by unfold fullM6ExtBytes; omega), hwb_toNat,
          Nat.mod_eq_of_lt (by unfold fullM6HdrTotalBytes fullM6ExtBytes at *; omega)]
      rw [h0] at hpos_hdr
      change 0 = (fullM6WorkBase work_ptr).toNat + fullM6ExtBytes at hpos_hdr
      unfold fullM6ExtBytes at hpos_hdr; omega
    have hc_avail : c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes := by
      rw [hav_c, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold fullAlignPad at *; omega)]
    rw [← hrest_c] at hph_c
    refine hkl c.hdr m2 hc_nz fun Q_l hQl => ?_
    dsimp only [kissatSimplifyExportLoadedSpec]
    refine ⟨c, ext, s, cnf_ptr, out_ptr, cnfBytes, buf, j,
      region work_ptr (fullAlignPad work_ptr) ⋆ R, rfl, rfl, hcfit, hj_le, hph_c, hcfg_c, hext_c,
      hcv_c, hdcur_c, hcl_c, hte_c, hprop_c, hal_c, hoom_c, hprb_c, hinc_c, hvals_c,
      hwvec_c, hinv_c, hout_ne, hout_al, hout_fit, hcap, hout_nz, hout_fit2,
      sep_entry_to_loaded hm2,
      fun r c' ext' s' outBytes written m3 hcmp3 hlen3 hcfg3 hext3 hr3 hwr_lt h0 h1 hut3 => ?_⟩
    have hc'_hdr : c'.hdr = fullM6WorkHdr work_ptr := by
      rw [hcmp3.hdr]; exact hhdr_c
    have hc'_av : c'.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes := by
      rw [hcmp3.avail]; exact hc_avail
    have hw_fun : ∀ x, (region work_ptr (fullAlignPad work_ptr) ⋆ FullM6HdrMem c' ext' s') x →
        region work_ptr wlen x := fun x hx =>
      region_work_from_m6_hdrMem hw_ge (by omega) hc'_hdr hc'_av hcfg3 hext3 hlen3 hx
    refine hQl r m3 (hQ r outBytes written m3 hr3 hwr_lt
      (fun hz => ⟨(h0 hz).1, sep_entry_collapse hw_fun (h0 hz).2⟩)
      (fun hnz => ?_) (fun mv nc i0 _ _ _ _ _ hi0 hph0 hu0 hge12 => ?_))
    · obtain ⟨hpos, hle, hlen_eq, hsnd, h20s, h10s, hm3⟩ := h1 hnz
      exact ⟨hpos, hle, hlen_eq, hsnd, h20s, h10s, sep_entry_collapse hw_fun hm3⟩
    · have hph_eq := hph_c.symm.trans hph0
      simp only [Option.some.injEq, Prod.mk.injEq] at hph_eq
      rcases hph_eq with ⟨hmv_eq, hnc_eq, hdrop_eq⟩
      have hj_eq : j = i0 := by
        have hlen_drop := congrArg List.length hdrop_eq
        simp only [List.length_drop] at hlen_drop; omega
      subst hmv_eq hnc_eq hj_eq
      exact hut3 hu0 hge12

/-- End-to-end `Mem 64` WP correctness of
`kissat_simplify_export_bytes(cnf_ptr, cnf_len, work_ptr, work_cap, fuel, out)`. -/
theorem kissat_simplify_export_bytes_wp (Γ : Env)
    (hMemInit : ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      Γ "full_m6_mem_init" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hLoaded : ∀ a m Q X, kissatSimplifyExportLoadedSpec a m Q X →
      Γ "kissat_simplify_export_loaded" [i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, kissatSimplifyExportBytesSpec args m Q X →
      Func.wp Γ kissat_simplify_export_bytes_body args m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_cap, fuel, outDesc, ⟨⟩⟩ m Q X hs
  obtain ⟨cnfBytes, buf, wlen, out_ptr, old_len, R, rfl, rfl, hcfit, hwfit,
    hout_ne, hout_al, hout_fit, hcap, hout_nz, hout_fit2, hm, hQ_raw⟩ := hs
  have hQ : ExportEntryCallQ cnf_ptr work_ptr fuel outDesc out_ptr cnfBytes buf wlen R Q := hQ_raw
  clear hQ_raw
  unfold Func.wp kissat_simplify_export_bytes_body; dsimp only
  have hret0_old : ∀ m',
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
        bytes out_ptr buf ⋆ R) m' →
      (cnf_ptr = 0#64 ∨ work_ptr = 0#64 ∨ fuel = 0#64 ∨
        wlen < fullAlignPad work_ptr + fullM6HdrTotalBytes) →
      Q (0#64, ()) m' := by
    intro m' hm' hno
    refine hQ 0#64 [] 0 m' (Or.inl rfl) (by decide) (fun _ => ⟨Or.inl rfl, hm'⟩)
      (fun h => absurd rfl h) (fun mv nc i0 hc0 hw0 hf0 hle0 _ _ _ _ _ => ?_)
    rcases hno with h | h | h | h
    · exact absurd h hc0
    · exact absurd h hw0
    · exact absurd (by simp [h] : fuel.toNat = 0) (by omega)
    · exact absurd hle0 (by omega)
  have hout_le_lim : outDesc ≤ BitVec.allOnes 64 - 24#64 := by
    rw [bv64_allOnes_sub 24#64, BitVec.le_def, BitVec.toNat_ofNat]
    have h24 : (24#64 : BitVec 64).toNat = 24 := by decide
    rw [h24, Nat.mod_eq_of_lt (by omega)]; omega
  c0_hsteps_nogrp
  · unfold exportOutMem at hm
    refine wp_store_sep (store_cell64 0#64 (sep_entry_init hm)) fun m1 hm1 => ?_
    change (cell64 (outDesc + 16#64) 0#64 ⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ cell64 outDesc out_ptr ⋆
        cell64 (outDesc + 8#64) (BitVec.ofNat 64 buf.length) ⋆ bytes out_ptr buf ⋆ R)) m1 at hm1
    have hm1' : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
        bytes out_ptr buf ⋆ R) m1 := by
      unfold exportOutMem; exact sep_entry_unfold hm1
    refine wp_load_of (loadVal_cell64 (sep_entry_ptr hm1)) ?_
    refine wp_load_of (loadVal_cell64 (sep_entry_cap hm1)) ?_
    have h_ones : (~~~0#64).toNat = 2 ^ 64 - 1 := by decide
    have h_sub_ones : ∀ x : BitVec 64, (~~~0#64 - x).toNat = 2 ^ 64 - 1 - x.toNat := fun x => by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h_ones]; exact Nat.le_pred_of_lt x.isLt),
        h_ones]
    refine wp_join0_cons1 (fun m' => m' = m1) ?_ (fun _ hJ => by
      c0_hsteps_nogrp
      · exact hJ m1 rfl
      · exact hJ m1 rfl)
    intro _ m_j heq
    cases heq
    c0_hstraight; refine wp_jnz_of ?_ ?_
    · intro hc
      exfalso
      simp only [Arg.val, show (0 : BitVec 64) = 0#64 from rfl] at hc
      rw [BitVec.ult_iff_toNat_lt, h_sub_ones, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hcap] at hc
      omega
    · intro _
      c0_hstraight; refine wp_jnz_of ?_ ?_
      · intro hc
        simp only [Arg.val, beq_iff_eq] at hc
        exact hret0_old m1 hm1' (Or.inr (Or.inr (Or.inl hc)))
      · intro _
        c0_hstraight; refine wp_jnz_of ?_ ?_
        · intro hc
          simp only [Arg.val, beq_iff_eq] at hc
          exact hret0_old m1 hm1' (Or.inl hc)
        · intro _
          c0_hstraight; refine wp_jnz_of ?_ ?_
          · intro hc
            simp only [Arg.val, beq_iff_eq] at hc
            exact hret0_old m1 hm1' (Or.inr (Or.inl hc))
          · intro _
            c0_hstraight; refine wp_jnz_of ?_ ?_
            · intro hc
              exfalso
              simp only [Arg.val, show (0 : BitVec 64) = 0#64 from rfl] at hc
              rw [BitVec.ult_iff_toNat_lt, h_sub_ones, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega)] at hc
              omega
            · intro _
              c0_hstraight; refine wp_jnz_of ?_ ?_
              · intro hc
                exfalso
                simp only [Arg.val, show (0 : BitVec 64) = 0#64 from rfl] at hc
                rw [BitVec.ult_iff_toNat_lt, h_sub_ones, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega)] at hc
                omega
              · intro _
                have hpad8 := fullAlignPad_lt8 work_ptr
                have h3456 : fullAlignPad work_ptr + fullM6HdrTotalBytes < 2 ^ 64 := by
                  unfold fullM6HdrTotalBytes; omega
                have hpad_bv : ((8#64 - (work_ptr &&& 7#64)) &&& 7#64) + 3456#64 =
                    BitVec.ofNat 64 (fullAlignPad work_ptr + fullM6HdrTotalBytes) := by
                  rw [bv64_alignPad]
                  apply BitVec.eq_of_toNat_eq
                  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
                  unfold fullM6HdrTotalBytes at *; omega
                c0_hstraight; refine wp_jnz_of ?_ ?_
                · intro hlt
                  have hw_lt : wlen < fullAlignPad work_ptr + fullM6HdrTotalBytes := by
                    simp only [Arg.val, show (7 : BitVec 64) = 7#64 from rfl,
                      show (8 : BitVec 64) = 8#64 from rfl,
                      show (3456 : BitVec 64) = 3456#64 from rfl] at hlt
                    rw [hpad_bv, BitVec.ult_iff_toNat_lt] at hlt
                    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3456] at hlt
                    rw [Nat.mod_eq_of_lt (by omega)] at hlt
                    exact hlt
                  exact hret0_old m1 hm1' (Or.inr (Or.inr (Or.inr hw_lt)))
                · intro hge
                  have hw_ge : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen :=
                    Nat.le_of_not_lt fun hlt => by
                      simp only [Arg.val, show (7 : BitVec 64) = 7#64 from rfl,
                        show (8 : BitVec 64) = 8#64 from rfl,
                        show (3456 : BitVec 64) = 3456#64 from rfl] at hge
                      rw [Bool.eq_false_iff] at hge
                      apply hge
                      rw [hpad_bv, BitVec.ult_iff_toNat_lt]
                      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3456]
                      rw [Nat.mod_eq_of_lt (by omega)]
                      exact hlt
                  c0_hstraight
                  have hwb_eq : work_ptr + ((8#64 - (work_ptr &&& 7#64)) &&& 7#64) =
                      fullM6WorkBase work_ptr := by rw [bv64_alignPad]; rfl
                  have hav_eq : BitVec.ofNat 64 wlen - ((8#64 - (work_ptr &&& 7#64)) &&& 7#64) =
                      BitVec.ofNat 64 (wlen - fullAlignPad work_ptr) := by
                    rw [bv64_alignPad,
                      bv64_sub_of_le (by omega) (by unfold fullAlignPad at *; omega)]
                  dsimp only [vals_cons, vals_nil, Arg.val]
                  rw [show (7 : BitVec 64) = 7#64 from rfl, show (8 : BitVec 64) = 8#64 from rfl,
                    hwb_eq, hav_eq]
                  refine wp_call_of_spec _ _ (hMemInit _ _ _ _
                    (simplify_export_after_mem_init hcfit hwfit hout_ne hout_al hout_fit
                      hcap hout_nz hout_fit2 hw_ge hm1' hQ ?_ ?_))
                  · intro m2 hm20
                    c0_hstraight; refine wp_jnz_of ?_ ?_
                    · intro _; c0_hstraight; exact hm20
                    · intro hc; exfalso; simp only [Arg.val] at hc
                      exact absurd (rfl : (0#64 == 0) = true) (Bool.eq_false_iff.mp hc)
                  · intro hdr m2 hnz hspec
                    c0_hstraight; refine wp_jnz_of ?_ ?_
                    · intro hc
                      exfalso; simp only [Arg.val, beq_iff_eq] at hc; exact hnz hc
                    · intro _
                      c0_hstraight
                      dsimp only [vals_cons, vals_nil, Arg.val]
                      exact wp_call_of_spec _ _
                        (hLoaded _ _ _ _ (hspec _ fun r m3 hr => by c0_hstraight; exact hr))

/-! ## 2. Closed `ModuleOk` (`exportCnfEntryMod`) & Top-Level UNSAT Soundness -/

private theorem stEnv_byte : ∀ a m Q X, kissatEmitByteSpec a m Q X →
    exportCnfStateEnv "kissat_emit_byte" [i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => by simpa [exportCnfStateEnv, exportCnfFmtEnv] using h

private theorem stEnv_u64 : ∀ a m Q X, kissatEmitU64Spec a m Q X →
    exportCnfStateEnv "kissat_emit_u64" [i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => by simpa [exportCnfStateEnv, exportCnfFmtEnv] using h

private theorem stEnv_lit : ∀ a m Q X, kissatEmitDimacsLitSpec a m Q X →
    exportCnfStateEnv "kissat_emit_dimacs_lit" [i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => by simpa [exportCnfStateEnv, exportCnfFmtEnv] using h

private theorem stEnv_hdr : ∀ a m Q X, kissatEmitDimacsHdrSpec a m Q X →
    exportCnfStateEnv "kissat_emit_dimacs_hdr" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => by simpa [exportCnfStateEnv, exportCnfFmtEnv] using h

private theorem stEnv_backtrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
    exportCnfStateEnv "full_backtrack" [i64, i64] [] a m Q X :=
  fun _ _ _ _ h => by simpa [exportCnfStateEnv] using h

private theorem stEnv_trail_units : ∀ a m Q X, kissatExportTrailUnitsSpec a m Q X →
    exportCnfStateEnv "kissat_export_trail_units" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => by simpa [exportCnfStateEnv] using h

private theorem stEnv_bin_clauses : ∀ a m Q X, kissatExportBinClausesSpec a m Q X →
    exportCnfStateEnv "kissat_export_bin_clauses" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => by simpa [exportCnfStateEnv] using h

private theorem stEnv_arena_clauses : ∀ a m Q X, kissatExportArenaClausesSpec a m Q X →
    exportCnfStateEnv "kissat_export_arena_clauses" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => by simpa [exportCnfStateEnv] using h

private theorem stEnv_arena_next : ∀ a m Q X, kissatExportArenaNextSpec a m Q X →
    exportCnfStateEnv "kissat_export_arena_next" [i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => by simpa [exportCnfStateEnv] using h

private theorem stEnv_cnf_bytes : ∀ a m Q X, kissatExportCnfBytesSpec a m Q X →
    exportCnfStateEnv "kissat_export_cnf_bytes" [i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => by simpa [exportCnfStateEnv] using h

theorem exportCnfEntryEnv_byte :
    ∀ a m Q X, kissatEmitByteSpec a m Q X →
      exportCnfEntryEnv "kissat_emit_byte" [i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (stEnv_byte _ _ _ _ h))))

theorem exportCnfEntryEnv_hdr :
    ∀ a m Q X, kissatEmitDimacsHdrSpec a m Q X →
      exportCnfEntryEnv "kissat_emit_dimacs_hdr" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (stEnv_hdr _ _ _ _ h))))

theorem exportCnfEntryEnv_cnf_bytes :
    ∀ a m Q X, kissatExportCnfBytesSpec a m Q X →
      exportCnfEntryEnv "kissat_export_cnf_bytes" [i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (stEnv_cnf_bytes _ _ _ _ h))))

theorem exportCnfEntryEnv_backtrack :
    ∀ a m Q X, fullBacktrackSpec a m Q X →
      exportCnfEntryEnv "full_backtrack" [i64, i64] [] a m Q X :=
  fun _ _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (stEnv_backtrack _ _ _ _ h))))

theorem exportCnfEntryEnv_mem_init :
    ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      exportCnfEntryEnv "full_m6_mem_init" [i64, i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => Or.inr (Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩)

theorem exportCnfEntryEnv_parse :
    ∀ a m Q X, fullParseBodySpec a m Q X →
      exportCnfEntryEnv "full_parse_body_m6" [i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => Or.inr (Or.inr (Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩))

theorem exportCnfEntryEnv_preprocess :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      exportCnfEntryEnv "full_preprocess_m6" [i64] [i64] a m Q X :=
  fun _ _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩)))

theorem exportCnfEntryEnv_triv :
    ∀ a m Q X, kissatEmitTrivialCnfBytesSpec a m Q X →
      exportCnfEntryEnv "kissat_emit_trivial_cnf_bytes" [i64, i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => Or.inl (by simp [exportCnfEntryOnlyEnv, h])

theorem exportCnfEntryEnv_loaded :
    ∀ a m Q X, kissatSimplifyExportLoadedSpec a m Q X →
      exportCnfEntryEnv "kissat_simplify_export_loaded" [i64, i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => Or.inl (by simp [exportCnfEntryOnlyEnv, h])

theorem exportCnfEntryEnv_simplify :
    ∀ a m Q X, kissatSimplifyExportBytesSpec a m Q X →
      exportCnfEntryEnv "kissat_simplify_export_bytes" [i64, i64, i64, i64, i64, i64] [i64]
        a m Q X :=
  fun _ _ _ _ h => Or.inl (by simp [exportCnfEntryOnlyEnv, h])

private theorem exportCnfEntryOnlyEnv_false_of_ne {f : Sym} {as rs : List Ty}
    (h1 : f ≠ "kissat_emit_trivial_cnf_bytes")
    (h2 : f ≠ "kissat_simplify_export_loaded")
    (h3 : f ≠ "kissat_simplify_export_bytes")
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost} :
    ¬ exportCnfEntryOnlyEnv f as rs xs m Q X := by
  simp [exportCnfEntryOnlyEnv, h1, h2, h3]

theorem exportCnfEntryOnlyEnv_triv :
    exportCnfEntryOnlyEnv "kissat_emit_trivial_cnf_bytes" [i64, i64, i64, i64] [i64] =
      kissatEmitTrivialCnfBytesSpec := by
  funext a m Q X; simp [exportCnfEntryOnlyEnv]

theorem exportCnfEntryOnlyEnv_loaded :
    exportCnfEntryOnlyEnv "kissat_simplify_export_loaded" [i64, i64, i64] [i64] =
      kissatSimplifyExportLoadedSpec := by
  funext a m Q X; simp [exportCnfEntryOnlyEnv]

theorem exportCnfEntryOnlyEnv_bytes :
    exportCnfEntryOnlyEnv "kissat_simplify_export_bytes"
        [i64, i64, i64, i64, i64, i64] [i64] =
      kissatSimplifyExportBytesSpec := by
  funext a m Q X; simp [exportCnfEntryOnlyEnv]

/-- `ModuleOk` soundness for the entire `12`-fn exporter stack inside an arbitrary `Γ : Env`. -/
theorem exportCnfEntryFns_sound_in (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hMemInit : ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      Γ "full_m6_mem_init" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hParse : ∀ a m Q X, fullParseBodySpec a m Q X →
      Γ "full_parse_body_m6" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Γ "full_preprocess_m6" [i64] [i64] a m Q X)
    (hByte : ∀ a m Q X, kissatEmitByteSpec a m Q X →
      Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64] a m Q X)
    (hU64 : ∀ a m Q X, kissatEmitU64Spec a m Q X →
      Γ "kissat_emit_u64" [i64, i64, i64, i64] [i64] a m Q X)
    (hLit : ∀ a m Q X, kissatEmitDimacsLitSpec a m Q X →
      Γ "kissat_emit_dimacs_lit" [i64, i64, i64, i64] [i64] a m Q X)
    (hHdr : ∀ a m Q X, kissatEmitDimacsHdrSpec a m Q X →
      Γ "kissat_emit_dimacs_hdr" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, kissatExportArenaNextSpec a m Q X →
      Γ "kissat_export_arena_next" [i64, i64] [i64] a m Q X)
    (hTrail : ∀ a m Q X, kissatExportTrailUnitsSpec a m Q X →
      Γ "kissat_export_trail_units" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hBin : ∀ a m Q X, kissatExportBinClausesSpec a m Q X →
      Γ "kissat_export_bin_clauses" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hArena : ∀ a m Q X, kissatExportArenaClausesSpec a m Q X →
      Γ "kissat_export_arena_clauses" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hSpecArenaNext : ∀ a m Q X,
      Γ "kissat_export_arena_next" [i64, i64] [i64] a m Q X → kissatExportArenaNextSpec a m Q X)
    (hSpecTrail : ∀ a m Q X,
      Γ "kissat_export_trail_units" [i64, i64, i64, i64, i64] [i64] a m Q X →
        kissatExportTrailUnitsSpec a m Q X)
    (hSpecBin : ∀ a m Q X,
      Γ "kissat_export_bin_clauses" [i64, i64, i64, i64, i64] [i64] a m Q X →
        kissatExportBinClausesSpec a m Q X)
    (hSpecArena : ∀ a m Q X,
      Γ "kissat_export_arena_clauses" [i64, i64, i64, i64, i64] [i64] a m Q X →
        kissatExportArenaClausesSpec a m Q X)
    (hSpecCnf : ∀ a m Q X,
      Γ "kissat_export_cnf_bytes" [i64, i64, i64, i64] [i64] a m Q X →
        kissatExportCnfBytesSpec a m Q X)
    (hExp : ∀ a m Q X, kissatExportCnfBytesSpec a m Q X →
      Γ "kissat_export_cnf_bytes" [i64, i64, i64, i64] [i64] a m Q X)
    (hTriv : ∀ a m Q X, kissatEmitTrivialCnfBytesSpec a m Q X →
      Γ "kissat_emit_trivial_cnf_bytes" [i64, i64, i64, i64] [i64] a m Q X)
    (hLoaded : ∀ a m Q X, kissatSimplifyExportLoadedSpec a m Q X →
      Γ "kissat_simplify_export_loaded" [i64, i64, i64] [i64] a m Q X) :
    ∀ pre fn post, exportCnfEntryAllFns = pre ++ fn :: post →
      fn.Wf ∧ fn.callsOk (pre.map Fn.sig ++ exportCnfEntryMod.externs.map Extern.sig) [] ∧
      ∀ xs m Q X,
        (exportCnfEntryOnlyEnv fn.name fn.as fn.rs xs m Q X ∨
          exportCnfStateEnv fn.name fn.as fn.rs xs m Q X) →
        Func.wp Γ fn.body xs m Q X := by
  intro pre fn post hsplit
  have hfn_mem : fn ∈ exportCnfEntryAllFns := hsplit ▸ List.mem_append_right _ List.mem_cons_self
  have hca := exportCnfEntryMod_checkAcyclic
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hca
  have hcalls : fn.callsOk (pre.map Fn.sig ++ exportCnfEntryMod.externs.map Extern.sig) [] := by
    simpa [exportCnfEntryMod] using Module.checkFnsCallsOk_ok exportCnfEntryMod.exits
      (exportCnfEntryMod.externs.map Extern.sig) [] exportCnfEntryMod.fns pre fn post hca.2 hsplit
  refine ⟨exportCnfEntryAllFns_wf fn hfn_mem, hcalls, fun xs m Q X hspec => ?_⟩
  rcases hspec with hEnt | hSt
  · have hmem : fn ∈ exportCnfEntry_fns := by
      rw [exportCnfEntryAllFns, List.mem_append] at hfn_mem
      refine hfn_mem.elim (fun h_st => False.elim ?_) id
      have hdis : ∀ g ∈ exportCnfStateAllFns,
          g.name ≠ "kissat_emit_trivial_cnf_bytes" ∧
          g.name ≠ "kissat_simplify_export_loaded" ∧
          g.name ≠ "kissat_simplify_export_bytes" := by
        intro g hg
        simp only [exportCnfStateAllFns, exportCnfFmt_fns, exportCnfState_fns,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have ⟨h1, h2, h3⟩ := hdis fn h_st
      exact exportCnfEntryOnlyEnv_false_of_ne h1 h2 h3 hEnt
    simp only [exportCnfEntry_fns, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · dsimp only [kissat_emit_trivial_cnf_bytes] at hEnt ⊢
      rw [exportCnfEntryOnlyEnv_triv] at hEnt
      exact kissat_emit_trivial_cnf_bytes_wp Γ hByte hHdr xs m Q X hEnt
    · dsimp only [kissat_simplify_export_loaded] at hEnt ⊢
      rw [exportCnfEntryOnlyEnv_loaded] at hEnt
      exact kissat_simplify_export_loaded_wp Γ hParse hPre hTriv hExp xs m Q X hEnt
    · dsimp only [kissat_simplify_export_bytes] at hEnt ⊢
      rw [exportCnfEntryOnlyEnv_bytes] at hEnt
      exact kissat_simplify_export_bytes_wp Γ hMemInit hLoaded xs m Q X hEnt
  · have hmem_st : fn ∈ exportCnfStateAllFns := by
      rw [exportCnfEntryAllFns, List.mem_append] at hfn_mem
      refine hfn_mem.elim id fun h_ent => False.elim ?_
      simp only [exportCnfEntry_fns, List.mem_cons, List.not_mem_nil, or_false] at h_ent
      rcases h_ent with rfl | rfl | rfl <;>
        simp [exportCnfStateEnv, exportCnfFmtEnv, kissat_emit_trivial_cnf_bytes,
          kissat_simplify_export_loaded, kissat_simplify_export_bytes] at hSt
    rw [exportCnfStateAllFns, List.mem_append] at hmem_st
    rcases hmem_st with h_fmt | h_st
    · have hEq : ∀ g ∈ exportCnfFmt_fns,
          exportCnfStateEnv g.name g.as g.rs = exportCnfFmtEnv g.name g.as g.rs := by
        intro g hg
        simp only [exportCnfFmt_fns, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;>
          (funext a' m' Q' X'; simp [exportCnfStateEnv, exportCnfFmtEnv,
            kissat_emit_byte, kissat_emit_u64, kissat_emit_dimacs_lit, kissat_emit_dimacs_hdr])
      rw [hEq fn h_fmt] at hSt
      refine exportCnfFmtFns_sound_in Γ (fun g hg a' m' Q' X' hs => ?_) fn h_fmt xs m Q X hSt
      simp only [exportCnfFmt_fns, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact hByte a' m' Q' X' (by simpa [exportCnfFmtEnv, kissat_emit_byte] using hs)
      · exact hU64 a' m' Q' X' (by simpa [exportCnfFmtEnv, kissat_emit_u64] using hs)
      · exact hLit a' m' Q' X' (by simpa [exportCnfFmtEnv, kissat_emit_dimacs_lit] using hs)
      · exact hHdr a' m' Q' X' (by simpa [exportCnfFmtEnv, kissat_emit_dimacs_hdr] using hs)
    · have hGamma : Γ fn.name fn.as fn.rs xs m Q X := by
        simp only [exportCnfState_fns, List.mem_cons, List.not_mem_nil, or_false] at h_st
        rcases h_st with rfl | rfl | rfl | rfl | rfl
        · exact hArenaNext _ _ _ _
            (by simpa [exportCnfStateEnv, kissat_export_arena_next] using hSt)
        · exact hTrail _ _ _ _ (by simpa [exportCnfStateEnv, kissat_export_trail_units] using hSt)
        · exact hBin _ _ _ _ (by simpa [exportCnfStateEnv, kissat_export_bin_clauses] using hSt)
        · exact hArena _ _ _ _
            (by simpa [exportCnfStateEnv, kissat_export_arena_clauses] using hSt)
        · exact hExp _ _ _ _ (by simpa [exportCnfStateEnv, kissat_export_cnf_bytes] using hSt)
      exact exportCnfStateFns_sound_in Γ hBacktrack hByte hLit hHdr hArenaNext hTrail hBin hArena
        hSpecArenaNext hSpecTrail hSpecBin hSpecArena hSpecCnf fn h_st xs m Q X hGamma

private theorem entryEnv_state_of {f : Sym} {as rs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (_hnb : f ≠ "full_backtrack") (hmi : f ≠ "full_m6_mem_init") (hpa : f ≠ "full_parse_body_m6")
    (hpr : f ≠ "full_preprocess_m6") (htr : f ≠ "kissat_emit_trivial_cnf_bytes")
    (hlo : f ≠ "kissat_simplify_export_loaded") (hby : f ≠ "kissat_simplify_export_bytes")
    (h : exportCnfEntryEnv f as rs xs m Q X) : exportCnfStateEnv f as rs xs m Q X := by
  rcases h with hent | h1 | h1 | h1 | hst
  · exfalso; exact exportCnfEntryOnlyEnv_false_of_ne htr hlo hby hent
  · exact absurd h1.1.1 hmi
  · exact absurd h1.1.1 hpa
  · exact absurd h1.1.1 hpr
  · exact hst

private theorem stEnv_arena_next_eq :
    exportCnfStateEnv "kissat_export_arena_next" [i64, i64] [i64] =
      kissatExportArenaNextSpec := by
  funext a m Q X; simp [exportCnfStateEnv]

private theorem stEnv_trail_units_eq :
    exportCnfStateEnv "kissat_export_trail_units" [i64, i64, i64, i64, i64] [i64] =
      kissatExportTrailUnitsSpec := by
  funext a m Q X; simp [exportCnfStateEnv]

private theorem stEnv_bin_clauses_eq :
    exportCnfStateEnv "kissat_export_bin_clauses" [i64, i64, i64, i64, i64] [i64] =
      kissatExportBinClausesSpec := by
  funext a m Q X; simp [exportCnfStateEnv]

private theorem stEnv_arena_clauses_eq :
    exportCnfStateEnv "kissat_export_arena_clauses" [i64, i64, i64, i64, i64] [i64] =
      kissatExportArenaClausesSpec := by
  funext a m Q X; simp [exportCnfStateEnv]

private theorem stEnv_cnf_bytes_eq :
    exportCnfStateEnv "kissat_export_cnf_bytes" [i64, i64, i64, i64] [i64] =
      kissatExportCnfBytesSpec := by
  funext a m Q X; simp [exportCnfStateEnv]

/-- Closed `ModuleOk` theorem for the standalone `12`-fn exporter module `exportCnfEntryMod`. -/
theorem exportCnfEntryEnv_moduleOk : ModuleOk exportCnfEntryEnv exportCnfEntryMod := by
  refine ⟨exportCnfEntryMod_namesNodup, fun pre fn post hsplit => ?_⟩
  have hsound := exportCnfEntryFns_sound_in exportCnfEntryEnv
    exportCnfEntryEnv_backtrack
    exportCnfEntryEnv_mem_init
    exportCnfEntryEnv_parse
    exportCnfEntryEnv_preprocess
    exportCnfEntryEnv_byte
    (fun _ _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (stEnv_u64 _ _ _ _ h)))))
    (fun _ _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (stEnv_lit _ _ _ _ h)))))
    exportCnfEntryEnv_hdr
    (fun _ _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (stEnv_arena_next _ _ _ _ h)))))
    (fun _ _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (stEnv_trail_units _ _ _ _ h)))))
    (fun _ _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (stEnv_bin_clauses _ _ _ _ h)))))
    (fun _ _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (stEnv_arena_clauses _ _ _ _ h)))))
    (fun _ _ _ _ h => by
      have hs := entryEnv_state_of (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h
      rwa [stEnv_arena_next_eq] at hs)
    (fun _ _ _ _ h => by
      have hs := entryEnv_state_of (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h
      rwa [stEnv_trail_units_eq] at hs)
    (fun _ _ _ _ h => by
      have hs := entryEnv_state_of (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h
      rwa [stEnv_bin_clauses_eq] at hs)
    (fun _ _ _ _ h => by
      have hs := entryEnv_state_of (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h
      rwa [stEnv_arena_clauses_eq] at hs)
    (fun _ _ _ _ h => by
      have hs := entryEnv_state_of (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h
      rwa [stEnv_cnf_bytes_eq] at hs)
    exportCnfEntryEnv_cnf_bytes
    exportCnfEntryEnv_triv
    exportCnfEntryEnv_loaded
    pre fn post hsplit
  refine ⟨hsound.1, hsound.2.1, fun xs m Q X hs => hsound.2.2 xs m Q X ?_⟩
  have hf : fn ∈ exportCnfEntryMod.fns := hsplit ▸ List.mem_append_right _ List.mem_cons_self
  change fn ∈ exportCnfEntryAllFns at hf
  have hex_nm : fn.name ≠ "full_backtrack" ∧ fn.name ≠ "full_m6_mem_init" ∧
      fn.name ≠ "full_parse_body_m6" ∧ fn.name ≠ "full_preprocess_m6" := by
    simp only [exportCnfEntryAllFns, exportCnfStateAllFns, exportCnfFmt_fns, exportCnfState_fns,
      exportCnfEntry_fns, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  rcases hs with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · exact absurd h2.1.1 hex_nm.2.1
  · exact absurd h3.1.1 hex_nm.2.2.1
  · exact absurd h4.1.1 hex_nm.2.2.2
  · exact Or.inr h5

/-- Top-level `Mem 64` WP + UNSAT soundness theorem for `kissat_simplify_export_bytes`:
whenever `0 < out_len ∧ out_len ≤ buf.length`, the written bytes `outBytes` parse via
`LratBytes.parseDimacs` to a valid `cnfOut : CNF Nat` satisfying `cnfOut.Unsat → F0.Unsat`
(with `"p cnf 0 1\n0\n"` emitted on `r = 20#64` and `"p cnf 0 0\n"` on `r = 10#64`). -/
theorem kissat_simplify_export_bytes_sound (Γ : Env)
    (hMemInit : ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      Γ "full_m6_mem_init" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hLoaded : ∀ a m Q X, kissatSimplifyExportLoadedSpec a m Q X →
      Γ "kissat_simplify_export_loaded" [i64, i64, i64] [i64] a m Q X)
    {cnf_ptr work_ptr fuel outDesc out_ptr old_len : BitVec 64}
    {cnfBytes buf : List UInt8} {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hout_ne : outDesc ≠ 0#64) (hout_al : (outDesc &&& 7#64) = 0#64)
    (hout_fit : outDesc.toNat + 24 < 2 ^ 64)
    (hcap : buf.length < 2 ^ 64) (hout_nz : 0 < buf.length → out_ptr ≠ 0#64)
    (hout_fit2 : out_ptr.toNat + buf.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) old_len ⋆
      bytes out_ptr buf ⋆ R) m) :
    Func.wp Γ kissat_simplify_export_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr,
        BitVec.ofNat 64 wlen, fuel, outDesc, ()) m
      (fun (r, ()) m' =>
        ∃ (outBytes : List UInt8) (out_len : Nat),
          (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          out_len < 2 ^ 64 ∧
          (0 < out_len ∧ out_len ≤ buf.length ↔ r ≠ 0#64) ∧
          (r = 0#64 →
            (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
              exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length)
                (BitVec.ofNat 64 out_len) ⋆ bytes out_ptr buf ⋆ R) m') ∧
          (0 < out_len ∧ out_len ≤ buf.length →
            outBytes.length = out_len ∧
            (∃ F0 cnfOut, parseDimacs cnfBytes = some F0 ∧
              parseDimacs outBytes = some cnfOut ∧ (cnfOut.Unsat → F0.Unsat)) ∧
            (r = 20#64 → outBytes = unsatDimacsBytes ∧
              ∃ F0, parseDimacs cnfBytes = some F0 ∧ F0.Unsat) ∧
            (r = 10#64 → outBytes = satEmptyDimacsBytes ∧
              ∃ F0, parseDimacs cnfBytes = some F0) ∧
            (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
              exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length)
                (BitVec.ofNat 64 out_len) ⋆
              bytes out_ptr (outBytes ++ buf.drop out_len) ⋆ R) m') ∧
          (∀ mv nc i0,
            cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
            fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen →
            fullAlignPad work_ptr + fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 ≤ wlen →
            i0 ≤ cnfBytes.length →
            parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
            UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
            12 ≤ buf.length → r = 20#64))
      X := by
  refine kissat_simplify_export_bytes_wp Γ hMemInit hLoaded _ m _ X
    ⟨cnfBytes, buf, wlen, out_ptr, old_len, R, rfl, rfl, hcfit, hwfit, hout_ne, hout_al,
      hout_fit, hcap, hout_nz, hout_fit2, hm, fun r outBytes written m' hr hlt h0 h1 hut => ?_⟩
  refine ⟨outBytes, written, hr, hlt, ⟨fun ⟨hpos, hle⟩ hrz => ?_, fun hnz => ?_⟩,
    fun hz => (h0 hz).2, fun ⟨hpos, hle⟩ => ?_, hut⟩
  · rcases (h0 hrz).1 with rfl | hgt <;> omega
  · have ⟨hpos, hle, _⟩ := h1 hnz; exact ⟨hpos, hle⟩
  · have hnz : r ≠ 0#64 := fun hz => by rcases (h0 hz).1 with rfl | hgt <;> omega
    obtain ⟨_, _, hlen, hsnd, h20, h10, hm'⟩ := h1 hnz
    exact ⟨hlen, hsnd, h20, h10, hm'⟩

/-- Explicit parsed-formula phrasing of `kissat_simplify_export_bytes_sound`: given
`parseDimacs cnfBytes = some F0`, any non-empty bounded output `outBytes`
(`0 < out_len ≤ buf.length`)
parses back to `some cnfOut` with `cnfOut.Unsat → F0.Unsat`. -/
theorem kissat_simplify_export_bytes_sound_parsed (Γ : Env)
    (hMemInit : ∀ a m Q X, fullM6MemInitExactSpec a m Q X →
      Γ "full_m6_mem_init" [i64, i64, i64, i64, i64] [i64] a m Q X)
    (hLoaded : ∀ a m Q X, kissatSimplifyExportLoadedSpec a m Q X →
      Γ "kissat_simplify_export_loaded" [i64, i64, i64] [i64] a m Q X)
    {cnf_ptr work_ptr fuel outDesc out_ptr old_len : BitVec 64}
    {cnfBytes buf : List UInt8} {wlen : Nat} {F0 : CNF Nat} {R : Mem 64 → Prop}
    {m : Mem 64} {X : XPost}
    (hparse : parseDimacs cnfBytes = some F0)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hout_ne : outDesc ≠ 0#64) (hout_al : (outDesc &&& 7#64) = 0#64)
    (hout_fit : outDesc.toNat + 24 < 2 ^ 64)
    (hcap : buf.length < 2 ^ 64) (hout_nz : 0 < buf.length → out_ptr ≠ 0#64)
    (hout_fit2 : out_ptr.toNat + buf.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) old_len ⋆
      bytes out_ptr buf ⋆ R) m) :
    Func.wp Γ kissat_simplify_export_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr,
        BitVec.ofNat 64 wlen, fuel, outDesc, ()) m
      (fun (r, ()) m' =>
        ∃ (outBytes : List UInt8) (out_len : Nat),
          (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          out_len < 2 ^ 64 ∧
          (0 < out_len ∧ out_len ≤ buf.length →
            outBytes.length = out_len ∧
            (∃ cnfOut : CNF Nat, parseDimacs outBytes = some cnfOut ∧
              (cnfOut.Unsat → F0.Unsat)) ∧
            (r = 20#64 → outBytes = unsatDimacsBytes ∧ F0.Unsat) ∧
            (r = 10#64 → outBytes = satEmptyDimacsBytes) ∧
            (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
              exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length)
                (BitVec.ofNat 64 out_len) ⋆
              bytes out_ptr (outBytes ++ buf.drop out_len) ⋆ R) m'))
      X := by
  unfold Func.wp
  refine wp_mono (fun ⟨r, _⟩ m' ⟨outBytes, out_len, hr, hlt, _, _, hpos, _⟩ => by
    refine ⟨outBytes, out_len, hr, hlt, fun hb => ?_⟩
    obtain ⟨hlen, ⟨F1, cnfOut, hp1, hpOut, hu⟩, h20, h10, hm'⟩ := hpos hb
    have hF : F1 = F0 := Option.some.inj (hp1.symm.trans hparse)
    subst hF
    exact ⟨hlen, ⟨cnfOut, hpOut, hu⟩,
      fun hr20 => ⟨(h20 hr20).1, by
        have ⟨F2, hp2, hu2⟩ := (h20 hr20).2
        rw [hparse, Option.some.injEq] at hp2; exact hp2 ▸ hu2⟩,
      fun hr10 => (h10 hr10).1, hm'⟩)
    (fun _ _ _ _ h => h) _ m
    (kissat_simplify_export_bytes_sound Γ hMemInit hLoaded
      hcfit hwfit hout_ne hout_al hout_fit hcap hout_nz hout_fit2 hm)

end

end LeanQbe.T.Examples.Kissat.ExportCnfEntryProof
