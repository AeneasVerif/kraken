/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Examples.Arisca.Src.Module
public import LeanQbe.T.Examples.Arisca.Proof.Driver2
import LeanQbe.T.Examples.Arisca.Proof.Poly2
import LeanQbe.T.Examples.Arisca.Proof.Poly2Rule
import LeanQbe.T.Examples.Arisca.Proof.Driver0Base
import LeanQbe.T.Examples.Arisca.Proof.Poly0Base
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.Bytes
import Kraken.Separation

/-!
# End-to-End ARiSCA ART v1 Checker Module Soundness (`Arisca.Proof.Full`)

Assembles all `44` canonical `Func.wp` proofs (`Header` + `Parse` + `Poly` + `Driver`) into flat
`ariscaModule_ok : ModuleOk ariscaEnv ariscaModule`, derives top-level `arisca_check_bytes_sound`
with `XPost := False` matching `ArtSound.checkArt_sound`, and proves concrete `Mem 64`
non-vacuity `arisca_check_bytes_nv` (`<= std3`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Header
open LeanQbe.T.Examples.Arisca.Src.Parse
open LeanQbe.T.Examples.Arisca.Src.Poly
open LeanQbe.T.Examples.Arisca.Src.Driver
open LeanQbe.T.Examples.Arisca.Src.Module

@[expose] public section

/-- Combined WP spec for `ar_mcmp(a, b)` covering shared-array (`Poly`) and disjoint-slice
(`ar_dcanon`) callers. -/
def arMcmpCombSpec : Spec [i64, i64] [i32] :=
  fun xs m Q X => arMcmpSpec xs m Q X ∨ arMcmpSliceSpec xs m Q X

/-- Closed `44`-row specification table for `ariscaModule` (all `noExit = true`). -/
def ariscaSpecTable : List SpecEntry :=
  -- Header (10): indices 0..9
  [ ⟨"ar_rd32", [i64], [i32], arRd32Spec, true⟩
  , ⟨"ar_next_word", [i64], [.bool, i32], arNextWordSpec, true⟩
  , ⟨"ar_aalloc", [i64, i64], [i64], arAallocSpec, true⟩
  , ⟨"u64_mul128", [i64, i64], [i64, i64], u64Mul128Spec, true⟩
  , ⟨"ar_cmul", [i64, i64, i64, i64, i64], [i64, i64], arCmulSpec, true⟩
  , ⟨"ar_cadd", [i64, i64, i64, i64, i64], [i64, i64], arCaddSpec, true⟩
  , ⟨"ar_csub", [i64, i64, i64, i64, i64], [i64, i64], arCsubSpec, true⟩
  , ⟨"ar_cneg", [i64, i64, i64], [i64, i64], arCnegSpec, true⟩
  , ⟨"ar_cfrom_small", [i64, i64], [i64, i64], arCfromSmallSpec, true⟩
  , ⟨"ar_cpow2", [i64, i32], [i64, i64], arCpow2Spec, true⟩
  -- Parse (5): indices 10..14
  , ⟨"ar_pnum", [i64, i64, i64], [.bool, i64, i32], arPnumSpec, true⟩
  , ⟨"ar_pch", [i64, i64, i64, i8], [.bool, i64], arPchSpec, true⟩
  , ⟨"ar_pvarint", [i64, i64, i64], [.bool, i64, i32], arPvarintSpec, true⟩
  , ⟨"ar_parse_aig", [i64, i64, i64], [.bool], arParseAigSpec, true⟩
  , ⟨"ar_parse_art_header_and_tables", [i64, i64, i64], [.bool],
      arParseArtHeaderAndTablesSpec, true⟩
  -- Poly (16): indices 15..30
  , ⟨"ar_mcmp", [i64, i64], [i32], arMcmpCombSpec, true⟩
  , ⟨"ar_mhas_from", [i64, i32, i32], [.bool], arMhasFromSpec, true⟩
  , ⟨"ar_sigbit", [i32], [i64], arSigbitSpec, true⟩
  , ⟨"ar_msig", [i64], [i64], arMsigSpec, true⟩
  , ⟨"ar_mvanish", [i64, i64], [.bool], arMvanishSpec, true⟩
  , ⟨"ar_munion", [i64, i64, i32, i64], [i64], arMunionSpec, true⟩
  , ⟨"ar_compact", [i64], [], arCompactSpec, true⟩
  , ⟨"ar_sort_combine", [i64], [i32], arSortCombineSpec, true⟩
  , ⟨"ar_gallop", [i64, i64, i32, i32, i64], [i32], arGallopSpec, true⟩
  , ⟨"ar_merge_products", [i64, i32], [], arMergeProductsSpec, true⟩
  , ⟨"ar_apply", [i64, i32], [.bool], arApplySpec, true⟩
  , ⟨"ar_add_q", [i64, i32, i32, i32, i64, i64], [.bool], arAddQSpec, true⟩
  , ⟨"ar_build_sp0", [i64], [.bool], arBuildSp0Spec, true⟩
  , ⟨"ar_load_rule", [i64, i32], [.bool], arLoadRuleSpec, true⟩
  , ⟨"ar_store_rule", [i64, i32], [.bool], arStoreRuleSpec, true⟩
  , ⟨"ar_build_R", [i64, i32], [.bool], arBuildRSpec, true⟩
  -- Driver (13): indices 31..43
  , ⟨"ar_ttsim", [i64, i32, i32, i64], [.bool, i64], arTtsimSpec, true⟩
  , ⟨"ar_dzero", [i64], [], arDzeroSpec, true⟩
  , ⟨"ar_dlit", [i64, i32, i32], [], arDlitSpec, true⟩
  , ⟨"ar_dmul", [i64, i64, i64], [], arDmulSpec, true⟩
  , ⟨"ar_daxpy", [i64, i64, i64], [], arDaxpySpec, true⟩
  , ⟨"ar_dcanon", [i64, i64], [i32], arDcanonSpec, true⟩
  , ⟨"ar_install_rule", [i64, i32, i32], [.bool], arInstallRuleSpec, true⟩
  , ⟨"ar_mask6", [i32], [i64], arMask6Spec, true⟩
  , ⟨"ar_do_gate", [i64], [.bool], arDoGateSpec, true⟩
  , ⟨"ar_do_cone", [i64], [.bool], arDoConeSpec, true⟩
  , ⟨"ar_setup_dynamic", [i64], [.bool], arSetupDynamicSpec, true⟩
  , ⟨"ar_check_main", [i64, i64, i64, i64, i64], [.bool], arCheckMainSpec, true⟩
  , ⟨"arisca_check_bytes", [i64, i64, i64, i64, i64, i64], [i64],
      ariscaCheckBytesSpec, true⟩ ]

/-- Closed canonical `Env` for `ariscaModule`. -/
def ariscaEnv : T.Env := T.Env.ofTable ariscaSpecTable

/-- Callee prefix before `arisca_check_bytes` inside `ariscaModule.fns` (`43` fns). -/
def ariscaPre : List Fn :=
  Header.fns ++ Parse.fns ++ Poly.fns ++ Driver.fns.take 12

/-- Top-level `arisca_check_bytes` entry function (`44`th slot of `ariscaModule.fns`). -/
def ariscaCheckBytesFn : Fn :=
  ⟨"arisca_check_bytes", [i64, i64, i64, i64, i64, i64], [i64],
    Driver.arisca_check_bytes_body⟩

/-- Restricted `Env` visible to `arisca_check_bytes` (`43` declared internal callees). -/
def ariscaSolvedEnv : T.Env :=
  T.Env.restrict ariscaEnv (ariscaPre.map Fn.sig ++ ariscaModule.externs.map Extern.sig)

/-- Concrete `1x1` AIGER binary bytes (`aig 3 2 0 1 1\n6\n\x02\x00`, `18` bytes). -/
def nvAigBytes : List UInt8 :=
  [0x61, 0x69, 0x67, 0x20, 0x33, 0x20, 0x32, 0x20, 0x30, 0x20, 0x31, 0x20, 0x31,
   0x0a, 0x36, 0x0a, 0x02, 0x00]

/-- Concrete ART v1 header placeholder bytes (`4` bytes). -/
def nvArtBytes : List UInt8 := [0, 0, 0, 0]

def nvAigPtr : BitVec 64 := 0x100000#64
def nvAigLen : BitVec 64 := 18#64
def nvArtPtr : BitVec 64 := 0x100012#64
def nvArtLen : BitVec 64 := 4#64
def nvWorkPtr : BitVec 64 := 0x100016#64
def nvWorkCap : BitVec 64 := 0x1000#64

/-- Concrete `Mem 64` slab holding `nvAigBytes`, `nvArtBytes`, and `0x1000` scratch bytes. -/
def nvMem : Mem 64 :=
  (nvAigBytes ++ nvArtBytes ++ List.replicate 0x1000 (0 : UInt8)).At nvAigPtr

end

public section

theorem ariscaSpecTable_length : ariscaSpecTable.length = 44 := rfl

theorem ariscaSpecTable_nodup : (ariscaSpecTable.map SpecEntry.name).Nodup := by
  show ([ "ar_rd32", "ar_next_word", "ar_aalloc", "u64_mul128", "ar_cmul", "ar_cadd",
      "ar_csub", "ar_cneg", "ar_cfrom_small", "ar_cpow2"
    , "ar_pnum", "ar_pch", "ar_pvarint", "ar_parse_aig", "ar_parse_art_header_and_tables"
    , "ar_mcmp", "ar_mhas_from", "ar_sigbit", "ar_msig", "ar_mvanish", "ar_munion"
    , "ar_compact", "ar_sort_combine", "ar_gallop", "ar_merge_products", "ar_apply"
    , "ar_add_q", "ar_build_sp0", "ar_load_rule", "ar_store_rule", "ar_build_R"
    , "ar_ttsim", "ar_dzero", "ar_dlit", "ar_dmul", "ar_daxpy", "ar_dcanon"
    , "ar_install_rule", "ar_mask6", "ar_do_gate", "ar_do_cone", "ar_setup_dynamic"
    , "ar_check_main", "arisca_check_bytes" ] : List String).Nodup
  decide

theorem ariscaSpecTable_noExit : ∀ e ∈ ariscaSpecTable, e.noExit = true := by
  intro e he
  simp only [ariscaSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> rfl

theorem ariscaEnv_noExit :
    ∀ f as bs xs m Q X X',
      ariscaEnv f as bs xs m Q X → ariscaEnv f as bs xs m Q X' :=
  T.Env.ofTable_noExit ariscaSpecTable_noExit

theorem ariscaEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : ariscaSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by
      intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → ariscaEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    T.Env.ofTable_of_mem (List.mem_of_getElem? hi) ariscaSpecTable_nodup (hno xs m Q X h)

private theorem ar_mcmp_slice_wp (Γ : T.Env) :
    ∀ xs m Q X, arMcmpSliceSpec xs m Q X → Func.wp Γ ar_mcmp_body xs m Q X := by
  rintro ⟨aPtr, bPtr, ⟨⟩⟩ m Q X ⟨ma, mb, R, hA, hB, hlt32, hm, hQ⟩
  have hmA : (array (t := i32) aPtr ma ⋆ (array (t := i32) bPtr mb ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  have hmB : (array (t := i32) bPtr mb ⋆ (array (t := i32) aPtr ma ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  try c0_hsteps
  · exact wp_load_arr32 (base := aPtr) (off := 0) (i := 0) (by simp) hA.1 hmA (by
      try c0_hsteps
      · exact wp_load_arr32 (base := bPtr) (off := 0) (i := 0) (by simp) hB.1 hmB (by
          c0_hsteps
          · exact hQ (-1#32) (fun heq => absurd heq (by decide))
          · exact hQ 1#32 (fun heq => absurd heq (by decide))
          · have hlen_eq : ma.getD 0 0#32 = mb.getD 0 0#32 := by
              rw [getD_eq_getElem ma 0#32 hA.1, getD_eq_getElem mb 0#32 hB.1]
              exact ‹ma[0 + 0]'hA.1 = mb[0 + 0]'hB.1›
            have hlenNat : (ma.getD 0 0#32).toNat = (mb.getD 0 0#32).toNat :=
              congrArg BitVec.toNat hlen_eq
            refine wp_loop_group (fun rem ⟨i, ⟨⟩⟩ m' =>
                m' = m ∧ 1 ≤ i.toNat ∧ i.toNat ≤ (ma.getD 0 0#32).toNat + 1 ∧
                rem = (ma.getD 0 0#32).toNat + 1 - i.toNat ∧
                (∀ k, 1 ≤ k → k < i.toNat → ma.getD k 0#32 = mb.getD k 0#32))
              ?_ ?_
            · intro J rem ⟨i, ⟨⟩⟩ m' hrec ⟨hm', hi1, hile, hrem, hpref⟩
              subst hm'
              c0_hsteps
              · have hilt : i.toNat ≤ (ma.getD 0 0#32).toNat := by
                  rw [getD_eq_getElem ma 0#32 hA.1]; exact hc
                have hlt_a : i.toNat < ma.length := by have := hA.2; omega
                have hlt_b : i.toNat < mb.length := by have := hB.2; omega
                c0_hsteps
                · exact hQ (-1#32) (fun heq => absurd heq (by decide))
                · exact hQ 1#32 (fun heq => absurd heq (by decide))
                · have hi_eq : ma.getD i.toNat 0#32 = mb.getD i.toNat 0#32 := by
                    rw [getD_eq_getElem ma 0#32 hlt_a, getD_eq_getElem mb 0#32 hlt_b]
                    simpa [Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 64)] using
                      ‹ma[i.toNat % 2 ^ 64] = mb[i.toNat % 2 ^ 64]›
                  have hip1 : (i + 1).toNat = i.toNat + 1 := by
                    rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl,
                      Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
                  exact hrec ((ma.getD 0 0#32).toNat + 1 - (i + 1).toNat)
                    (i + 1, ⟨⟩) m' (by omega)
                    ⟨rfl, by omega, by omega, rfl, fun k hk1 hklt => by
                      by_cases hki : k = i.toNat
                      · subst hki; exact hi_eq
                      · exact hpref k hk1 (by omega)⟩
              · refine hQ 0#32 (fun _ => ?_)
                have hi_eq : i.toNat = (ma.getD 0 0#32).toNat + 1 := by
                  have hlt' := BitVec.not_le.mp hc
                  have h0 : (ma[0 + 0]'(by have := hA.1; omega)).toNat =
                      (ma.getD 0 0#32).toNat := by
                    symm; exact congrArg BitVec.toNat (getD_eq_getElem ma 0#32 hA.1)
                  have hlt_nat : (ma[0 + 0]'(by have := hA.1; omega)).toNat < i.toNat := hlt'
                  omega
                simp only [symListAt, Nat.zero_add, hlenNat]
                apply List.map_congr_left
                intro k hk
                rw [List.mem_range] at hk
                rw [Nat.add_comm 1 k, hpref (k + 1) (by omega) (by omega)]
            · intro J hJ
              c0_hsteps
              have h1_nat : (1#32 : BitVec 32).toNat = 1 := rfl
              exact hJ ((ma.getD 0 0#32).toNat + 1 - 1) (1#32, ⟨⟩) m
                ⟨rfl, by decide, by rw [h1_nat]; omega, rfl, fun k hk1 hklt => by omega⟩))

private theorem ar_mcmp_comb_wp (Γ : T.Env) :
    ∀ xs m Q X, arMcmpCombSpec xs m Q X → Func.wp Γ ar_mcmp_body xs m Q X := by
  intro xs m Q X h
  rcases h with h | h
  · exact ar_mcmp_wp Γ xs m Q X h
  · exact ar_mcmp_slice_wp Γ xs m Q X h

private theorem ariscaModule_fns_nodup : (ariscaModule.fns.map Fn.name).Nodup := by
  have hchk := ariscaModule_checkAcyclic
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem ariscaModule_tableImpl :
    TableImpl ariscaEnv ariscaModule.fns ariscaSpecTable := by
  have hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X →
      ariscaEnv "ar_mcmp" [i64, i64] [i32] xs m Q X :=
    fun xs m Q X h => ariscaEnv_row_at 15 _ (hi := rfl) (hno := fun _ _ _ _ hs => hs)
      xs m Q X (Or.inl h)
  have hMcmpSl : ∀ xs m Q X, arMcmpSliceSpec xs m Q X →
      ariscaEnv "ar_mcmp" [i64, i64] [i32] xs m Q X :=
    fun xs m Q X h => ariscaEnv_row_at 15 _ (hi := rfl) (hno := fun _ _ _ _ hs => hs)
      xs m Q X (Or.inr h)
  dsimp only [ariscaModule, ariscaFns, Header.fns, Parse.fns, Poly.fns, Driver.fns,
    arisca_hdr_fns, arisca_parse_fns, arisca_poly_fns, arisca_driver_fns,
    List.cons_append, List.nil_append, ariscaSpecTable]
  refine ⟨
    -- Header (0..9)
    SpecEntry.Impl.of (ar_rd32_wp ariscaEnv),
    SpecEntry.Impl.of (ar_next_word_wp ariscaEnv (ariscaEnv_row_at 0 _)),
    SpecEntry.Impl.of (ar_aalloc_wp ariscaEnv),
    SpecEntry.Impl.of (u64_mul128_wp ariscaEnv),
    SpecEntry.Impl.of (ar_cmul_wp ariscaEnv (ariscaEnv_row_at 3 _)),
    SpecEntry.Impl.of (ar_cadd_wp ariscaEnv),
    SpecEntry.Impl.of (ar_csub_wp ariscaEnv),
    SpecEntry.Impl.of (ar_cneg_wp ariscaEnv),
    SpecEntry.Impl.of (ar_cfrom_small_wp ariscaEnv),
    SpecEntry.Impl.of (ar_cpow2_wp ariscaEnv),
    -- Parse (10..14)
    SpecEntry.Impl.of (ar_pnum_wp ariscaEnv),
    SpecEntry.Impl.of (ar_pch_wp ariscaEnv),
    SpecEntry.Impl.of (ar_pvarint_wp ariscaEnv),
    SpecEntry.Impl.of (ar_parse_aig_wp ariscaEnv (ariscaEnv_row_at 10 _)
      (ariscaEnv_row_at 11 _) (ariscaEnv_row_at 12 _) (ariscaEnv_row_at 2 _)),
    SpecEntry.Impl.of (ar_parse_art_header_and_tables_wp ariscaEnv
      (ariscaEnv_row_at 1 _) (ariscaEnv_row_at 2 _)),
    -- Poly (15..30)
    SpecEntry.Impl.of (ar_mcmp_comb_wp ariscaEnv),
    SpecEntry.Impl.of (ar_mhas_from_wp ariscaEnv),
    SpecEntry.Impl.of (ar_sigbit_wp ariscaEnv),
    SpecEntry.Impl.of (ar_msig_wp ariscaEnv (ariscaEnv_row_at 17 _)),
    SpecEntry.Impl.of (ar_mvanish_wp ariscaEnv (ariscaEnv_row_at 16 _)),
    SpecEntry.Impl.of (ar_munion_wp ariscaEnv (ariscaEnv_row_at 17 _)),
    SpecEntry.Impl.of (ar_compact_wp ariscaEnv),
    SpecEntry.Impl.of (ar_sort_combine_wp ariscaEnv hMcmp (ariscaEnv_row_at 5 _)),
    SpecEntry.Impl.of (ar_gallop_wp ariscaEnv hMcmp),
    SpecEntry.Impl.of (ar_merge_products_wp ariscaEnv (ariscaEnv_row_at 22 _)
      (ariscaEnv_row_at 23 _) hMcmp (ariscaEnv_row_at 5 _)),
    SpecEntry.Impl.of (ar_apply_wp ariscaEnv (ariscaEnv_row_at 16 _) (ariscaEnv_row_at 17 _)
      (ariscaEnv_row_at 21 _) (ariscaEnv_row_at 19 _) (ariscaEnv_row_at 20 _)
      (ariscaEnv_row_at 4 _) (ariscaEnv_row_at 24 _)),
    SpecEntry.Impl.of (ar_add_q_wp ariscaEnv (ariscaEnv_row_at 19 _) (ariscaEnv_row_at 18 _)),
    SpecEntry.Impl.of (ar_build_sp0_wp ariscaEnv (ariscaEnv_row_at 26 _) (ariscaEnv_row_at 24 _)
      (ariscaEnv_row_at 7 _) (ariscaEnv_row_at 9 _)),
    SpecEntry.Impl.of (ar_load_rule_wp ariscaEnv (ariscaEnv_row_at 18 _)),
    SpecEntry.Impl.of (ar_store_rule_wp ariscaEnv),
    SpecEntry.Impl.of (ar_build_R_wp ariscaEnv hMcmp (ariscaEnv_row_at 7 _)
      (ariscaEnv_row_at 5 _)),
    -- Driver (31..43)
    SpecEntry.Impl.of (ar_ttsim_wp ariscaEnv),
    SpecEntry.Impl.of (ar_dzero_wp ariscaEnv),
    SpecEntry.Impl.of (ar_dlit_wp ariscaEnv (ariscaEnv_row_at 32 _)),
    SpecEntry.Impl.of (ar_dmul_wp ariscaEnv (ariscaEnv_row_at 32 _)),
    SpecEntry.Impl.of (ar_daxpy_wp ariscaEnv),
    SpecEntry.Impl.of (ar_dcanon_wp ariscaEnv (ariscaEnv_row_at 8 _) (ariscaEnv_row_at 5 _)
      hMcmpSl),
    SpecEntry.Impl.of (ar_install_rule_wp ariscaEnv (ariscaEnv_row_at 19 _)),
    SpecEntry.Impl.of (ar_mask6_wp ariscaEnv),
    SpecEntry.Impl.of (ar_do_gate_wp ariscaEnv (ariscaEnv_row_at 1 _) (ariscaEnv_row_at 38 _)
      (ariscaEnv_row_at 31 _) (ariscaEnv_row_at 32 _) (ariscaEnv_row_at 33 _)
      (ariscaEnv_row_at 34 _) (ariscaEnv_row_at 35 _) (ariscaEnv_row_at 36 _)
      (ariscaEnv_row_at 5 _) (ariscaEnv_row_at 37 _)),
    SpecEntry.Impl.of (ar_do_cone_wp ariscaEnv (ariscaEnv_row_at 1 _) (ariscaEnv_row_at 28 _)
      (ariscaEnv_row_at 25 _) (ariscaEnv_row_at 29 _)),
    SpecEntry.Impl.of (ar_setup_dynamic_wp ariscaEnv (ariscaEnv_row_at 2 _)),
    SpecEntry.Impl.of (ar_check_main_wp ariscaEnv (ariscaEnv_row_at 13 _)
      (ariscaEnv_row_at 14 _) (ariscaEnv_row_at 41 _) (ariscaEnv_row_at 39 _)
      (ariscaEnv_row_at 40 _) (ariscaEnv_row_at 27 _) (ariscaEnv_row_at 1 _)
      (ariscaEnv_row_at 30 _) (ariscaEnv_row_at 25 _) (ariscaEnv_row_at 7 _)),
    SpecEntry.Impl.of (arisca_check_bytes_wp ariscaEnv (ariscaEnv_row_at 42 _)),
    trivial⟩

/-- Closed `ModuleOk` for `ariscaModule` against the canonical `44`-row `ariscaEnv`. -/
theorem ariscaModule_ok : ModuleOk ariscaEnv ariscaModule :=
  Module.moduleOk_of_checkAcyclic ariscaModule_checkAcyclic ariscaModule_wf
    (T.Env.ofTable_sound ariscaModule_fns_nodup ariscaModule_tableImpl)

private theorem ariscaModule_fns_split :
    ariscaModule.fns = ariscaPre ++ [ariscaCheckBytesFn] := by
  rfl

/-- Top-level `arisca_check_bytes` ART v1 soundness (`XPost := False`, `<= std3`) restricted to
the `43` declared internal callees. -/
theorem arisca_check_bytes_sound (aigPtr aigLen artPtr artLen workPtr workLen : BitVec 64)
    (m : Mem 64) (Q : Post [i64]) (aigBytes artBytes : List UInt8) (R : Mem 64 → Prop)
    (haig : aigLen.toNat = aigBytes.length)
    (hart : artLen.toNat = artBytes.length)
    (hm : (bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆
      region workPtr workLen.toNat ⋆ R) m)
    (hQ : ∀ (ret : BitVec 64) (m' : Mem 64),
      (ret = 20#64 → ∃ (g : Aig) (signed : Bool),
        parseAig (toNatBytes aigBytes) = some g ∧
        ∀ ρ : Nat → Bool,
          BitVec.ofNat g.outs.length (outWord g ρ) =
            BitVec.ofInt g.outs.length (inWord signed (g.I / 2) ρ 0) *
              BitVec.ofInt g.outs.length (inWord signed (g.I / 2) ρ (g.I / 2))) →
      (bytes aigPtr aigBytes ⋆ bytes artPtr artBytes ⋆
        region workPtr workLen.toNat ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Func.wp ariscaSolvedEnv Driver.arisca_check_bytes_body
      (aigPtr, aigLen, artPtr, artLen, workPtr, workLen, ⟨⟩) m Q (fun _ _ _ _ => False) :=
  ariscaModule_ok.wp_restrict (fn := ariscaCheckBytesFn) ariscaModule_fns_split
    (ariscaEnv_row_at 43 ⟨"arisca_check_bytes", [i64, i64, i64, i64, i64, i64], [i64],
        ariscaCheckBytesSpec, true⟩ (by rfl) (by intro _ _ _ _ h; exact h)
      (aigPtr, aigLen, artPtr, artLen, workPtr, workLen, ⟨⟩) m Q (fun _ _ _ _ => False)
      ⟨aigBytes, artBytes, R, haig, hart, hm, fun ret m' h20 hm' => hQ ret m' h20 hm'⟩)

/-- Concrete `Mem 64` satisfies the separation-logic footprint of `arisca_check_bytes`. -/
theorem nvMem_ok :
    (bytes nvAigPtr nvAigBytes ⋆ bytes nvArtPtr nvArtBytes ⋆
      region nvWorkPtr nvWorkCap.toNat ⋆ (ExtHashMap.emp : Mem 64 → Prop)) nvMem := by
  have hl_aig : nvAigBytes.length = 18 := rfl
  have hl_art : nvArtBytes.length = 4 := rfl
  have hl_rep : (List.replicate 0x1000 (0 : UInt8)).length = 0x1000 := List.length_replicate
  have hlen1 : nvAigBytes.length + (nvArtBytes ++ List.replicate 0x1000 (0 : UInt8)).length ≤
      2 ^ 64 := by
    rw [List.length_append, hl_aig, hl_art, hl_rep]; decide
  have hlen2 : nvArtBytes.length + (List.replicate 0x1000 (0 : UInt8)).length ≤ 2 ^ 64 := by
    rw [hl_art, hl_rep]; decide
  have hsep1 := Mem.At_append_sep nvAigBytes
    (nvArtBytes ++ List.replicate 0x1000 (0 : UInt8)) nvAigPtr hlen1
  have hsep2 := Mem.At_append_sep nvArtBytes
    (List.replicate 0x1000 (0 : UInt8)) nvArtPtr hlen2
  have hadr1 : nvAigPtr + BitVec.ofNat 64 nvAigBytes.length = nvArtPtr := by
    rw [hl_aig]; rfl
  have hadr2 : nvArtPtr + BitVec.ofNat 64 nvArtBytes.length = nvWorkPtr := by
    rw [hl_art]; rfl
  have hself : Eq ((nvAigBytes ++ nvArtBytes ++ List.replicate 0x1000 (0 : UInt8)).At nvAigPtr)
      nvMem := rfl
  rw [List.append_assoc, hsep1, hadr1, hsep2, hadr2] at hself
  have h1 : (bytes nvAigPtr nvAigBytes ⋆ bytes nvArtPtr nvArtBytes ⋆
      region nvWorkPtr nvWorkCap.toNat) nvMem := by
    have h0 : (Eq ((List.replicate 0x1000 (0 : UInt8)).At nvWorkPtr) ⋆
        (Eq (nvAigBytes.At nvAigPtr) ⋆ Eq (nvArtBytes.At nvArtPtr))) nvMem :=
      sep_cast hself (by ac_rfl)
    have h2 := sep_mono (P := Eq ((List.replicate 0x1000 (0 : UInt8)).At nvWorkPtr))
      (P' := region nvWorkPtr nvWorkCap.toNat)
      (fun _ h => ⟨List.replicate 0x1000 (0 : UInt8), hl_rep, h.symm⟩) h0
    exact sep_cast h2 (by ac_rfl)
  simpa [Std.ExtHashMap.sep_emp] using h1

/-- Concrete `Mem 64` non-vacuity witness for `arisca_check_bytes_sound` (`<= std3`). -/
theorem arisca_check_bytes_nv :
    Func.wp ariscaSolvedEnv Driver.arisca_check_bytes_body
      (nvAigPtr, nvAigLen, nvArtPtr, nvArtLen, nvWorkPtr, nvWorkCap, ⟨⟩) nvMem
      (fun r m' =>
        (bytes nvAigPtr nvAigBytes ⋆ bytes nvArtPtr nvArtBytes ⋆
          region nvWorkPtr nvWorkCap.toNat ⋆ (ExtHashMap.emp : Mem 64 → Prop)) m' ∧
        (r.1 = 20#64 → ∃ (g : Aig) (signed : Bool),
          parseAig (toNatBytes nvAigBytes) = some g ∧
          ∀ ρ : Nat → Bool,
            BitVec.ofNat g.outs.length (outWord g ρ) =
              BitVec.ofInt g.outs.length (inWord signed (g.I / 2) ρ 0) *
                BitVec.ofInt g.outs.length (inWord signed (g.I / 2) ρ (g.I / 2))))
      (fun _ _ _ _ => False) :=
  arisca_check_bytes_sound nvAigPtr nvAigLen nvArtPtr nvArtLen nvWorkPtr nvWorkCap nvMem _
    nvAigBytes nvArtBytes ExtHashMap.emp rfl rfl nvMem_ok
    (fun _ _ h20 hm' => ⟨hm', h20⟩)

end

end LeanQbe.T.Examples.Arisca.Proof
