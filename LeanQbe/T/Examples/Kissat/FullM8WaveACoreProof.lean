/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8WaveACoreProof0
meta import LeanQbe.T.Examples.Kissat.FullM8WaveACoreProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 `FullM8WaveACore` Concrete Non-Vacuity Proofs (`FullM8WaveACoreProof`)

Re-exports all parametric `Func.wp` proofs, `waveACoreSpecTable`, `waveACore_moduleOk`, and
`PatchModule` splicing bridges from `FullM8WaveACoreProof0` (same namespace
`LeanQbe.T.Examples.Kissat.FullM8WaveACore`, zero API breakage) and proves concrete `Mem 64`
UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) covering AE-bump Q16 Padé `tanh` + `>= 2^56`
rescale paths, `64`-bin glue histogram, M8 delay slots (`id = 4, 6`), `full_vivify_tier_m6_hdr`,
`full_vivify_m6_hdr`, `m8_eliminate_m6`, and `full_probe_tail_m6`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8WaveACore

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM3Backbone
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

local macro "wac_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 7. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteNonVacuity

private theorem nvWac_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have h0 : (cnfClause [0]).Sat α := (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α := (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1; simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

/-- Parameterized `nvOneLitState` core witness varying unconstrained counts and `dense_mode`. -/
def nvWacState (nr nb un dm eb : BitVec 64) : FullState :=
  { nvOneLitState with
    core := { nvOneLitState.core with
      num_redundant := nr, num_binary := nb, unassigned := un, dense_mode := dm }
    scratch := { nvOneLitState.scratch with elim_bound := eb } }

private theorem nvWac_lengths (nr nb un dm eb : BitVec 64) :
    (nvWacState nr nb un dm eb).LengthsOk nvOneLitCfg :=
  ⟨{ nvOneLit_lengths.core_ok with vals_len := nvOneLit_lengths.core_ok.vals_len },
   { nvOneLit_lengths.scratch_ok with walk_vals_len := nvOneLit_lengths.scratch_ok.walk_vals_len }⟩

private theorem nvWac_witness_of_fields (nr nb un dm eb : BitVec 64) :
    FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] (nvWacState nr nb un dm eb).core := by
  let k : FullCoreState := (nvWacState nr nb un dm eb).core
  change FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] k
  have hcv : k.cur_vars = 1 := rfl
  have hte : k.trail_end = 1 := rfl
  have hcl : k.cur_level = 0 := rfl
  have hr0 : ∀ r, r ∈ fullArenaClauseRefsCore k → False := fun _ hr => by
    rw [show fullArenaClauseRefsCore k = [] from rfl] at hr; cases hr
  have hi0 : ∀ i, i < k.trail_end → i = 0 := fun _ hi => by rw [hte] at hi; omega
  have hL0 : ∀ L, L ≤ k.cur_level → L = 0 := fun _ hL => by rw [hcl] at hL; omega
  have hwat : ModeWatchesInv [[0], [1]] k := by
    by_cases hdm : dm = 0#64
    · have hkdm : k.dense_mode = 0#64 := hdm
      unfold ModeWatchesInv; rw [ite_eq_left hkdm]
      refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
        (fun l1 _ h1 _ _ hp => ?_) (fun l hl => by
          rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact .empty)
      · rw [hcv] at hl
        change fullWatchOffCore nvOneLitState.core l +
            fullWatchSizeCore nvOneLitState.core l ≤ nvOneLitState.core.wlen
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
      · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          simp [fullWatchSizeCore, k, nvWacState, nvOneLitState] at hp
      · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
          simp [fullWatchSizeCore, k, nvWacState, nvOneLitState] at hp
    · have hkdm : k.dense_mode ≠ 0#64 := hdm
      unfold ModeWatchesInv; rw [ite_eq_right hkdm]
      refine DenseWatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
        (fun l1 _ h1 _ _ hp => ?_) (fun l hl => by
          rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
            exact DenseWatchSliceOk.empty)
      · rw [hcv] at hl
        change fullWatchOffCore nvOneLitState.core l +
            fullWatchSizeCore nvOneLitState.core l ≤ nvOneLitState.core.wlen
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
      · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          simp [fullWatchSizeCore, k, nvWacState, nvOneLitState] at hp
      · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
          simp [fullWatchSizeCore, k, nvWacState, nvOneLitState] at hp
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) :=
    CNF.entails_clause_def.mpr fun _ hα =>
      (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim,
        fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by
        rw [hi0 i hi]
        change (nvOneLitState.core.trl[0]?.getD 0#32).toNat <
          2 * nvOneLitState.core.cur_vars
        decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hi0 i hi, hi0 j hj]
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
          simp [k, nvWacState, nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by
        rw [hi0 i hi]
        change (nvOneLitState.core.lvl[(nvOneLitState.core.trl[0]?.getD 0#32).toNat / 2]?.getD
          0#32).toNat ≤ nvOneLitState.core.cur_level
        decide
      dec_earliest := fun _ j _ hj _ hp => by
        rw [hi0 j hj] at hp
        have hp1 : 0 < (nvOneLitState.core.lvl[(nvOneLitState.core.trl[0]?.getD 0#32).toNat /
          2]?.getD 0#32).toNat := hp.1
        exact absurd hp1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hi0 i hi]; exact hent0
      trail_pos_inv := fun i hi => by
        rw [hi0 i hi]
        change (nvOneLitState.core.trail_pos[(nvOneLitState.core.trl[0]?.getD 0#32).toNat /
          2]?.getD 0#32).toNat = 0
        decide
      level0_rsn_none := fun i hi _ => by
        rw [hi0 i hi]
        change nvOneLitState.core.rsns[(nvOneLitState.core.trl[0]?.getD 0#32).toNat /
          2]?.getD 4294967295#32 = 4294967295#32
        decide
      frame_trail_lt := fun L hL => by
        rw [hL0 L hL]
        change (nvOneLitState.core.frame_trail[0]?.getD 0#32).toNat ≤
          nvOneLitState.core.trail_end
        decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hL0 L1 (by omega), hL0 L2 hL2]; exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hi0 i hi] at hne
        change nvOneLitState.core.rsns[(nvOneLitState.core.trl[0]?.getD 0#32).toNat /
          2]?.getD 4294967295#32 ≠ 4294967295#32 at hne
        exact absurd (by decide) hne
      reason_lit_mem := fun i hi hne => by
        rw [hi0 i hi] at hne
        change nvOneLitState.core.rsns[(nvOneLitState.core.trl[0]?.getD 0#32).toNat /
          2]?.getD 4294967295#32 ≠ 4294967295#32 at hne
        exact absurd (by decide) hne }

private theorem nvWac_sparse_of_fields (nr nb un eb : BitVec 64) :
    FullSparseInv nvOneLitCfg nvOneLitF0 (nvWacState nr nb un 0#64 eb) := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hr0 : ∀ r, r ∈ fullArenaClauseRefsCore (nvWacState nr nb un 0#64 eb).core → False :=
    fun _ hr => by
      rw [show fullArenaClauseRefsCore (nvWacState nr nb un 0#64 eb).core = [] from rfl] at hr
      cases hr
  refine ⟨⟨nvWac_lengths nr nb un 0#64 eb, [[0], [1]],
      nvWac_witness_of_fields nr nb un 0#64 eb⟩,
    ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => (hr0 r hr).elim,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvWacState, nvOneLitState, nvOneLitScratch, List.getElem?_replicate,
        show i < 16 by omega, ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

private theorem nvWac_dense_of_fields (nr nb un eb : BitVec 64) :
    FullDenseInv nvOneLitCfg nvOneLitF0 (nvWacState nr nb un 1#64 eb) := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hr0 : ∀ r, r ∈ fullArenaClauseRefsCore (nvWacState nr nb un 1#64 eb).core → False :=
    fun _ hr => by
      rw [show fullArenaClauseRefsCore (nvWacState nr nb un 1#64 eb).core = [] from rfl] at hr
      cases hr
  have hdm : (nvWacState nr nb un 1#64 eb).core.dense_mode ≠ 0#64 :=
    fun h => absurd (show (1#64 : BitVec 64) = 0#64 from h) (by decide)
  refine ⟨⟨nvWac_lengths nr nb un 1#64 eb, [[0], [1]],
      nvWac_witness_of_fields nr nb un 1#64 eb⟩,
    ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => (hr0 r hr).elim,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvWacState, nvOneLitState, nvOneLitScratch, List.getElem?_replicate,
        show i < 16 by omega, ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, ⟨rfl, hdm⟩⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

private theorem nvWac_sparse : FullSparseInv nvOneLitCfg nvOneLitF0 nvOneLitState := by
  have heq : nvWacState 0#64 0#64 0#64 0#64 0#64 = nvOneLitState := by
    simp [nvWacState, nvOneLitState, nvOneLitScratch]
  rw [← heq]; exact nvWac_sparse_of_fields 0#64 0#64 0#64 0#64

private theorem nvWac_hdrMem_emp :
    (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
  rw [sep_emp]; exact nvM6HdrMem_ok

/-- Transparent `288`-word zero-initialized `M6HdrExt` list (`decide`-reducible locally). -/
def nvWacExtWords : List (BitVec 64) :=
  List.replicate fullM6ExtWords 0#64

/-- Transparent concrete `4,060`-byte `nvWacHdrMem` pairing `nvWacExtWords` with `nvOneLitMem`.
-/
def nvWacHdrMem : Mem 64 :=
  (bytes64 nvWacExtWords ++ nvOneLitBytes).At (nvOneLitCfg.hdr - 2304)

private theorem nvWacExtWords_len : nvWacExtWords.length = 288 := by
  unfold nvWacExtWords fullM6ExtWords
  exact List.length_replicate

private theorem nvWacHdrMem_ok :
    FullM6HdrMem nvOneLitCfg nvWacExtWords nvOneLitState nvWacHdrMem := by
  have hb64 : (bytes64 nvWacExtWords).length = 2304 := by
    rw [bytes64_length, nvWacExtWords_len]
  have htw : (Full.hdrTailWords nvOneLitCfg nvOneLitState).length = 140 := rfl
  have hbh : nvBlockHdr.length = 1152 := by
    unfold nvBlockHdr; rw [List.length_append, bytes64_length, bytes64_length, htw]; rfl
  have hi8 : (i8).bytes = 1 := rfl
  have hi32 : (i32).bytes = 4 := rfl
  have hbb : nvBlockBytes.length = 64 := by
    unfold nvBlockBytes
    simp only [List.length_append, bytesOf_length, List.length_replicate, List.length_cons,
      List.length_nil, hi8, nvOneLitState, nvOneLitScratch]
  have hua : nvBlockU32A.length = 40 := by
    unfold nvBlockU32A
    simp only [List.length_append, bytesOf_length, List.length_replicate, List.length_cons,
      List.length_nil, hi32, nvOneLitState]
  have hub : nvBlockU32B.length = 40 := by
    unfold nvBlockU32B
    simp only [List.length_append, bytesOf_length, List.length_replicate, List.length_cons,
      List.length_nil, hi32, nvOneLitState, nvOneLitScratch]
  have huc : nvBlockU32C.length = 40 := by
    unfold nvBlockU32C
    simp only [List.length_append, bytesOf_length, List.length_replicate, List.length_cons,
      List.length_nil, hi32, nvOneLitState, nvOneLitScratch]
  have huw : nvBlockWvec.length = 80 := by
    unfold nvBlockWvec
    simp only [List.length_append, bytesOf_length, bytes64_length, List.length_replicate,
      List.length_cons, List.length_nil, hi32, nvOneLitState, nvOneLitScratch]
  have hut : nvBlockTail.length = 340 := by
    unfold nvBlockTail
    simp only [List.length_append, bytesOf_length, List.length_replicate, List.length_cons,
      List.length_nil, hi32, nvOneLitState, nvOneLitScratch]
  have hol : nvOneLitBytes.length = 1756 := by
    rw [nvOneLitBytes]; simp only [List.length_append, hbh, hbb, hua, hub, huc, huw, hut]
  refine fullM6HdrMem_mk
    (nv_sep_append ?_ ?_ (array64_bytes _ _ (by rw [nvWacExtWords_len]; omega)) nvOneLitMem_ok)
  · rw [hb64]; decide
  · rw [hb64, hol]; omega

/-- Recover `M6HdrExtInitOk ext` directly from public `m6_ext_ensure_init_wp` +
`load_m6Ext_mul8 (i := 0#64)` + pointwise `load_m6Ext_mul8` identification (`0` edits outside the
`4` Wave A files). -/
private theorem fullM6HdrMem_ext_init_of_magic {c : FullCfg} {ext : List (BitVec 64)}
    {s : FullState} {m : Mem 64} (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hlen : s.LengthsOk c) (hm : FullM6HdrMem c ext s m)
    (hmagic : ext[0]'(by rw [hext.len]; decide) = fullM6HdrMagic) :
    M6HdrExtInitOk ext := by
  let Γtrue : Env := fun _ _ _ _ _ _ _ => True
  let Q : Post [] := fun () m' => ∃ ext', M6HdrExtInitOk ext' ∧ FullM6HdrMem c ext' s m'
  have hwp : Func.wp Γtrue m6_ext_ensure_init_body (c.hdr, ()) m Q (fun _ _ _ _ => False) :=
    m6_ext_ensure_init_wp Γtrue (fun _ _ _ _ _ => trivial) (c.hdr, ()) m Q _
      (m6ExtEnsureInitSpec_of hcfg hext hlen (by rw [sep_emp]; exact hm)
        fun ext' m' hinit' _ hm' => ⟨ext', hinit', by rwa [sep_emp] at hm'⟩)
  have hm_emp : (FullM6HdrMem c ext s ⋆ emp) m := by rw [sep_emp]; exact hm
  have hm_e : (FullMem c s ⋆ (array64 (c.hdr - 2304) ext ⋆ emp)) m :=
    (fullM6HdrMem_iff c ext s emp m).mp hm_emp
  have h0 : (0#64 : BitVec 64).toNat < ext.length := by rw [hext.len]; decide
  have hv0 := M6HdrTactics.load_m6Ext_mul8 (i := 0#64) hm_e h0
  unfold Func.wp m6_ext_ensure_init_body at hwp
  specialize hwp (Q, ()) ⟨fun () _ h => h, trivial⟩
  simp only [LeanQbe.T.wp_let_mul_eq, LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_cmp_eq,
    LeanQbe.T.wp_load, LeanQbe.T.wp_jnz, LeanQbe.T.wp_jump, LeanQbe.T.vals_nil,
    LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, LeanQbe.T.Ty.hasFloat,
    LeanQbe.T.evalBits_ne_bne, LeanQbe.T.lift2, LeanQbe.T.liftCmp, cast_eq,
    Bool.false_eq_true, ite_false] at hwp
  rcases hwp with ⟨v, hv, hwp⟩
  have hv0' : loadVal m i64 (c.hdr - 2304 + 0 * 8) = some (ext[(0#64 : BitVec 64).toNat]'h0) :=
    hv0
  rw [hv0'] at hv
  injection hv with hv
  subst v
  have hm0 : ext[(0#64 : BitVec 64).toNat]'h0 = fullM6HdrMagic := hmagic
  have hne_f : ((fullM6HdrMagic != (5563713847938078769 : BitVec 64)) : Bool) = false := by
    decide
  rw [hm0] at hwp
  simp only [hne_f, Bool.false_eq_true, false_implies, true_implies, true_and] at hwp
  obtain ⟨ext', hinit', hm'⟩ := hwp
  have hm_emp' : (FullM6HdrMem c ext' s ⋆ emp) m := by rw [sep_emp]; exact hm'
  have hm_e' : (FullMem c s ⋆ (array64 (c.hdr - 2304) ext' ⋆ emp)) m :=
    (fullM6HdrMem_iff c ext' s emp m).mp hm_emp'
  have heq : ext' = ext := by
    apply List.ext_getElem (by rw [hinit'.toOk.len, hext.len])
    intro i hi1 hi2
    have h288 : i < 288 := by rw [← hext.len]; exact hi2
    have hmod : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
    have h1 := M6HdrTactics.load_m6Ext_mul8 (i := BitVec.ofNat 64 i) hm_e
      (by simpa [BitVec.toNat_ofNat, hmod] using hi2)
    have h2 := M6HdrTactics.load_m6Ext_mul8 (i := BitVec.ofNat 64 i) hm_e'
      (by simpa [BitVec.toNat_ofNat, hmod] using hi1)
    rw [h1] at h2
    have h2v := Option.some.inj h2
    simpa [BitVec.toNat_ofNat, hmod] using h2v.symm
  rwa [← heq]

private theorem nvWac_wp {f : Sym} {as rs : List Ty} {sp : Spec as rs} (idx : Nat)
    (hidx : waveACoreSpecTable[idx]? = some ⟨f, as, rs, sp, true⟩)
    (pre post : List Fn) (fn : Fn)
    (hsplit : waveACoreFns = pre ++ fn :: post) (hname : fn.name = f) (has : fn.as = as)
    (hrs : fn.rs = rs) (body : Func as rs) (hbody : has ▸ hrs ▸ fn.body = body) :
    ∀ (a : Tup Val as) m Q, sp a m Q (fun _ _ _ _ => False) →
      Func.wp waveACoreEnv body a m Q (fun _ _ _ _ => False) := by
  subst has hrs hname hbody
  let ⟨_, _, hwp⟩ := waveACore_moduleOk.fnsOk pre fn post hsplit
  exact fun a m Q hs => hwp a m Q _
    (waveACoreEnv_row idx ⟨fn.name, fn.as, fn.rs, sp, true⟩ hidx a m Q
      (fun _ _ _ _ => False) hs)

/-- Concrete `Mem 64` NV (`XPost := False`) for `m8_log2_q16` on `x = 1#64 <<< 44`,
pinning exact `r = 44#64 <<< 16` and unchanged memory. -/
theorem nv_m8_log2_q16_pow44 :
    Func.wp waveACoreEnv m8_log2_q16_body (1#64 <<< 44, ()) nvOneLitMem
      (fun (r, ()) m' => r = 44#64 <<< 16 ∧ 44 * 65536 ≤ r.toNat ∧
        r.toNat < 45 * 65536 ∧ m' = nvOneLitMem)
      (fun _ _ _ _ => False) := by
  unfold Func.wp m8_log2_q16_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64, i64])
    (fun (b1, v1, ()) m1 => m1 = nvOneLitMem ∧ b1 = 32#64 ∧ v1 = 1#64 <<< 12) ?_
    (fun _ hJ1 => by
      c0_hsteps
      · exact hJ1 (32#64, 1#64 <<< 12, ()) nvOneLitMem ⟨rfl, rfl, rfl⟩
      · exfalso; revert hc; decide)
  rintro _ ⟨_, _, ⟨⟩⟩ m1 ⟨rfl, rfl, rfl⟩
  refine wp_join_group (ts := [i64, i64])
    (fun (b2, v2, ()) m2 => m2 = nvOneLitMem ∧ b2 = 32#64 ∧ v2 = 1#64 <<< 12) ?_
    (fun _ hJ2 => by
      c0_hsteps
      · exfalso; revert hc; decide
      · exact hJ2 (32#64, 1#64 <<< 12, ()) nvOneLitMem ⟨rfl, rfl, rfl⟩)
  rintro _ ⟨_, _, ⟨⟩⟩ m2 ⟨rfl, rfl, rfl⟩
  refine wp_join_group (ts := [i64, i64])
    (fun (b3, v3, ()) m3 => m3 = nvOneLitMem ∧ b3 = 40#64 ∧ v3 = 1#64 <<< 4) ?_
    (fun _ hJ3 => by
      c0_hsteps
      · exact hJ3 (40#64, 1#64 <<< 4, ()) nvOneLitMem ⟨rfl, rfl, rfl⟩
      · exfalso; revert hc; decide)
  rintro _ ⟨_, _, ⟨⟩⟩ m3 ⟨rfl, rfl, rfl⟩
  refine wp_join_group (ts := [i64, i64])
    (fun (b4, v4, ()) m4 => m4 = nvOneLitMem ∧ b4 = 44#64 ∧ v4 = 1#64) ?_
    (fun _ hJ4 => by
      c0_hsteps
      · exact hJ4 (44#64, 1#64, ()) nvOneLitMem ⟨rfl, rfl, rfl⟩
      · exfalso; revert hc; decide)
  rintro _ ⟨_, _, ⟨⟩⟩ m4 ⟨rfl, rfl, rfl⟩
  refine wp_join_group (ts := [i64, i64])
    (fun (b5, v5, ()) m5 => m5 = nvOneLitMem ∧ b5 = 44#64 ∧ v5 = 1#64) ?_
    (fun _ hJ5 => by
      c0_hsteps
      · exfalso; revert hc; decide
      · exact hJ5 (44#64, 1#64, ()) nvOneLitMem ⟨rfl, rfl, rfl⟩)
  rintro _ ⟨_, _, ⟨⟩⟩ m5 ⟨rfl, rfl, rfl⟩
  refine wp_join_group (ts := [i64]) (fun (b6, ()) m6 => m6 = nvOneLitMem ∧ b6 = 44#64) ?_
    (fun _ hJ6 => by c0_hsteps; exact hJ6 (44#64, ()) nvOneLitMem ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m6 ⟨rfl, rfl⟩
  refine wp_join_group (ts := [i64]) (fun (fr, ()) mf => mf = nvOneLitMem ∧ fr = 0#64) ?_
    (fun _ hJf => by c0_hsteps <;> exact hJf (0#64, ()) nvOneLitMem ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ mf ⟨rfl, rfl⟩
  c0_hsteps
  exact ⟨by decide, by decide, by decide, rfl⟩

/-- Concrete `Mem 64` heap exercising the AE-bump Q16 Padé `tanh` path (`scinc = 1#64 <<< 44`). -/
def nvAeTanhState : FullState :=
  { nvOneLitState with scratch := { nvOneLitState.scratch with scinc := 1#64 <<< 44 } }

def nvAeTanhMem : Mem 64 :=
  storeMem nvOneLitMem i64 (nvOneLitCfg.hdr + 256) (1#64 <<< 44)

theorem nvAeTanhMem_ok : FullMem nvOneLitCfg nvAeTanhState nvAeTanhMem := by
  have hm0 : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  have hst := (FullArenaTactics.store_full_scinc (1#64 <<< 44) hm0).2
  rw [sep_emp] at hst; exact hst

private theorem nv_m8_bump_decay_tanh_aux {m0 : Mem 64}
    (hm0 : (FullMem nvOneLitCfg nvAeTanhState ⋆ emp) m0) :
    Func.wp waveACoreEnv m8_ae_bump_decay_body (nvOneLitCfg.hdr, ()) m0
      (fun () m' => ∃ s', s'.core = nvAeTanhState.core ∧
        (1#64 <<< 44).toNat < s'.scratch.scinc.toNat ∧
        PreservesCoreSlice FullState.core nvAeTanhState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvAeTanhState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  unfold Func.wp m8_ae_bump_decay_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (inc1, ()) m1 => m1 = m0 ∧ inc1 = 1#64 <<< 44)
    ?_ (fun _ hJ1 => by
      c0_hsteps
      · exact absurd hc (by decide)
      · exact hJ1 (1#64 <<< 44, ()) m0 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m1 ⟨hm1, rfl⟩; subst m1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (inc2, ()) m2 => m2 = m0 ∧ inc2 = 1#64 <<< 44)
    ?_ (fun _ hJ2 => by
      c0_hsteps
      · exact absurd hc (by decide)
      · exact hJ2 (1#64 <<< 44, ()) m0 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m2 ⟨hm2, rfl⟩; subst m2
  c0_hsteps_nogrp
  wac_call waveACoreEnv_log2
  refine m8Log2Q16Spec_of fun lg _ hlg2 => ?_
  dsimp only [LeanQbe.T.Arg.val_var] at hlg2
  obtain ⟨b, _, _, hlo, hhi, hlg_lo, hlg_hi, _⟩ := hlg2 (by decide)
  have hb44 : b = 44 := by
    have h44 : (1#64 <<< 44).toNat = 2 ^ 44 := by decide
    rw [h44] at hlo hhi
    rcases Nat.lt_trichotomy b 44 with hlt | rfl | hgt
    · have : 2 ^ (b + 1) ≤ 2 ^ 44 := Nat.pow_le_pow_right (by decide) hlt; omega
    · rfl
    · have : 2 ^ 45 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hgt; omega
  subst hb44
  have h20s : ((20 : BitVec 64) <<< (16 : Nat)).toNat = 1310720 := by decide
  have h20l : (20 : BitVec 64) <<< (16 : Nat) ≤ lg := BitVec.le_def.mpr (by rw [h20s]; omega)
  have hrel_eq : (lg - (20 : BitVec 64) <<< (16 : Nat)).toNat = lg.toNat - 1310720 := by
    rw [BitVec.toNat_sub_of_le h20l, h20s]
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (rel, ()) md => md = m0 ∧ 24 * 65536 ≤ rel.toNat ∧ rel.toNat < 25 * 65536)
    ?_ (fun _ hJr => by
      c0_hsteps
      · exact hJr (_, ()) m0 ⟨rfl, by rw [hrel_eq]; omega, by rw [hrel_eq]; omega⟩
      · exfalso; rw [h20s] at hc; omega)
  rintro _ ⟨rel, ⟨⟩⟩ md ⟨hmd, hrel_lo, hrel_hi⟩; subst md
  have h36 : (36#64 : BitVec 64) ≠ 0#64 := by decide
  have h36n : (36 : BitVec 64).toNat = 36 := rfl
  have h65n : (65536 : BitVec 64).toNat = 65536 := rfl
  have hrq_div : (rel / (36 : BitVec 64)).toNat = rel.toNat / 36 := by
    rw [BitVec.toNat_udiv, h36n]
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (rq, ()) mr => mr = m0 ∧ 43690 ≤ rq.toNat ∧ rq.toNat ≤ 45511)
    ?_ (fun _ hJq => by
      c0_hsteps <;>
        first
        | exact hJq (_, ()) m0 ⟨rfl, by rw [hrq_div]; omega, by rw [hrq_div]; omega⟩
        | (exfalso; rw [hrq_div, h65n] at hc; omega))
  rintro _ ⟨rq, ⟨⟩⟩ mr ⟨hmr, hrq_lo, hrq_hi⟩; subst mr
  have hrq_ge : 32768 ≤ rq.toNat := by omega
  have hrq_le : rq.toNat ≤ 65536 := by omega
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (d_dyn, ()) md => md = m0 ∧ 60000 ≤ d_dyn.toNat ∧ d_dyn.toNat ≤ 70000)
    ?_ (fun _ hJd => by
      c0_hsplit
      · exfalso
        have h32k : (32768 : BitVec 64).toNat = 32768 := rfl
        rw [h32k] at hc; omega
      · obtain ⟨_, _, hden_lo, _⟩ := ae_decay_ge_denom hrq_ge hrq_le
        have hden_nz : (27#64 * 65536#64 +
            9#64 * ((((rq - 32768#64) <<< 1) * ((rq - 32768#64) <<< 1)) >>> 16)) ≠ 0#64 :=
          fun hz => by rw [hz] at hden_lo; exact absurd hden_lo (by decide)
        c0_hfast
        obtain ⟨hlo, hhi⟩ := ae_decay_ge_bounds hrq_ge hrq_le
        exact hJd _ m0 ⟨rfl, hlo, hhi⟩)
  rintro _ ⟨d_dyn, ⟨⟩⟩ md ⟨hmd, hd_lo, hd_hi⟩; subst md
  have hd_nz : d_dyn ≠ 0#64 := fun hz => by rw [hz] at hd_lo; exact absurd hd_lo (by decide)
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (ninc, ()) mn => mn = m0 ∧ (1#64 <<< 44).toNat < ninc.toNat ∧ ninc.toNat < 2 ^ 56)
    ?_ (fun _ hJn => by
      c0_hsteps
      · refine hJn (_, ()) m0 ⟨rfl, ?_, ?_⟩ <;> bv_omega
      · refine hJn (_, ()) m0 ⟨rfl, by c0_bound, ?_⟩
        change (((1#64 <<< 44 : BitVec 64) >>> 16) * ((65536 : BitVec 64) <<< 16 / d_dyn) +
          (((1#64 <<< 44 &&& (65535 : BitVec 64)) *
            ((65536 : BitVec 64) <<< 16 / d_dyn)) >>> 16)).toNat < 2 ^ 56
        have hhi_div : (((65536 : BitVec 64) <<< 16) / d_dyn).toNat ≤ 71582 := by
          rw [BitVec.toNat_udiv,
            show ((65536 : BitVec 64) <<< 16).toNat = 4294967296 from rfl]
          have hq : 4294967296 / d_dyn.toNat ≤ 4294967296 / 60000 :=
            Nat.div_le_div_left hd_lo (by decide)
          omega
        have hinc_sh : ((1#64 <<< 44 : BitVec 64) >>> 16).toNat = 2 ^ 28 := by decide
        have hinc_and : ((1#64 <<< 44 : BitVec 64) &&& (65535 : BitVec 64)) = 0#64 := by decide
        rw [hinc_and, BitVec.zero_mul, BitVec.zero_ushiftRight, BitVec.add_zero,
          BitVec.toNat_mul, hinc_sh, Nat.mod_eq_of_lt (by omega)]
        omega)
  rintro _ ⟨ninc, ⟨⟩⟩ mn ⟨hmn, hinc_lt, hn56⟩; subst mn
  c0_hsteps
  · exfalso
    change ((1 : BitVec 64) <<< 56).toNat ≤ ninc.toNat at hc
    rw [show ((1 : BitVec 64) <<< 56).toNat = 2 ^ 56 from by decide] at hc
    omega
  · let s' : FullState :=
      { nvAeTanhState with scratch := { nvAeTanhState.scratch with scinc := ninc } }
    rw [sep_emp] at hm
    exact ⟨s', rfl, hinc_lt, rfl, fullState_with_scinc_len nvOneLit_lengths ninc,
      fullState_with_scinc_pres ninc, nvWac_unsat, hm⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) exercising AE-bump Q16 Padé `tanh`
(`r_q16 >= 32768`) directly under `waveACoreEnv`, pinning `s'.core = nvAeTanhState.core` and
strict growth `s'.scratch.scinc.toNat > (1#64 <<< 44).toNat` without calling `full_rescale`. -/
theorem nv_m8_bump_decay_tanh :
    Func.wp waveACoreEnv m8_ae_bump_decay_body (nvOneLitCfg.hdr, ()) nvAeTanhMem
      (fun () m' => ∃ s', s'.core = nvAeTanhState.core ∧
        (1#64 <<< 44).toNat < s'.scratch.scinc.toNat ∧
        PreservesCoreSlice FullState.core nvAeTanhState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvAeTanhState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_m8_bump_decay_tanh_aux (by rw [sep_emp]; exact nvAeTanhMem_ok)

/-- Concrete `Mem 64` heap exercising the AE-bump `inc >= (1ULL << 56)` -> `full_rescale` path. -/
def nvAeRescaleState : FullState :=
  { nvOneLitState with scratch := { nvOneLitState.scratch with scinc := 1#64 <<< 56 } }

def nvAeRescaleMem : Mem 64 :=
  storeMem nvOneLitMem i64 (nvOneLitCfg.hdr + 256) (1#64 <<< 56)

theorem nvAeRescaleMem_ok : FullMem nvOneLitCfg nvAeRescaleState nvAeRescaleMem := by
  have hm0 : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  have hst := (FullArenaTactics.store_full_scinc (1#64 <<< 56) hm0).2
  rw [sep_emp] at hst; exact hst

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) exercising AE-bump `full_rescale(h)`. -/
theorem nv_m8_bump_decay_rescale :
    Func.wp waveACoreEnv m8_ae_bump_decay_body (nvOneLitCfg.hdr, ()) nvAeRescaleMem
      (fun () m' => ∃ s', PreservesCoreSlice FullState.core nvAeRescaleState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvAeRescaleState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 1 waveACoreSpecTable_at1 (waveACoreFns.take 1) (waveACoreFns.drop 2)
    waveACoreFns[1] rfl rfl rfl rfl
    m8_ae_bump_decay_body rfl _ nvAeRescaleMem _
    ⟨nvOneLitCfg, nvAeRescaleState, emp, rfl,
      nvOneLit_lengths.with_scratch { nvOneLit_lengths.scratch_ok with },
      by rw [sep_emp]; exact nvAeRescaleMem_ok,
      fun () s' m' hcore hlen hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hcore, hlen, hpr, nvWac_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `64`-bin `m8_hdr_recompute_tiers_mode`. -/
theorem nv_m8_recompute_tiers_mode :
    Func.wp waveACoreEnv m8_hdr_recompute_tiers_mode_body (nvOneLitCfg.hdr, 0#64, ()) nvM6HdrMem
      (fun () m' => ∃ ext' s', s'.LengthsOk nvOneLitCfg ∧ M6HdrExtOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 2 waveACoreSpecTable_at2 (waveACoreFns.take 2) (waveACoreFns.drop 3)
    waveACoreFns[2] rfl rfl rfl rfl
    m8_hdr_recompute_tiers_mode_body rfl _ nvM6HdrMem _
    (m6HdrW2aSpec_of rfl nvM6HdrCfg_ok nvM6ExtWords_ok nvOneLit_lengths nvWac_hdrMem_emp
      fun () ext' s' m' _ hlen' _ hext' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hlen', hext', nvWac_unsat, hm'⟩)

/-- Initialized M8 delay extension words: `e[0] = magic`, `delay[6].cnt = 2`, `delay[6].cur = 4`
(non-zero halving `4 >> 1 = 2`). -/
def nvM8DelayExt : List (BitVec 64) :=
  ((nvWacExtWords.set 0 fullM6HdrMagic).set 122 2#64).set 126 4#64

/-- Concrete `Mem 64` image with `e[0] = magic`, `e[122] = 2#64`, and `e[126] = 4#64`. -/
def nvM8DelayMem : Mem 64 :=
  storeMem (storeMem (storeMem nvWacHdrMem i64 (nvOneLitCfg.hdr - 2304) fullM6HdrMagic)
    i64 ((nvOneLitCfg.hdr - 2304) + 976#64) 2#64)
    i64 ((nvOneLitCfg.hdr - 2304) + 1008#64) 4#64

private theorem nvM8DelayExt_len : nvM8DelayExt.length = 288 := by
  simp [nvM8DelayExt, nvWacExtWords_len]

theorem nvM8DelayExt_ok : M6HdrExtOk nvM8DelayExt :=
  M6HdrExtOk.of_len nvM8DelayExt_len

theorem nvM8DelayMem_ok : FullM6HdrMem nvOneLitCfg nvM8DelayExt nvOneLitState nvM8DelayMem := by
  have hm0_emp : (FullM6HdrMem nvOneLitCfg nvWacExtWords nvOneLitState ⋆ emp) nvWacHdrMem := by
    rw [sep_emp]; exact nvWacHdrMem_ok
  have hm0 := (fullM6HdrMem_iff nvOneLitCfg nvWacExtWords nvOneLitState emp nvWacHdrMem).mp hm0_emp
  have h1 := (M6HdrTactics.store_m6Ext_zero fullM6HdrMagic hm0
    (by rw [nvWacExtWords_len]; decide)).2
  have h2 := (M6HdrTactics.store_m6Ext_const (k := 976#64) 2#64 h1 (by decide)
    (by rw [List.length_set, nvWacExtWords_len]; decide)).2
  have h3 := (M6HdrTactics.store_m6Ext_const (k := 1008#64) 4#64 h2 (by decide)
    (by rw [List.length_set, List.length_set, nvWacExtWords_len]; decide)).2
  have hm' := (fullM6HdrMem_iff nvOneLitCfg nvM8DelayExt nvOneLitState emp nvM8DelayMem).mpr h3
  rw [sep_emp] at hm'; exact hm'

private theorem nvM8DelayExt_elem_magic :
    nvM8DelayExt[0]'(by rw [nvM8DelayExt_len]; decide) = fullM6HdrMagic := by
  simp only [nvM8DelayExt,
    List.getElem_set_ne (by decide : 126 ≠ 0), List.getElem_set_ne (by decide : 122 ≠ 0)]
  rw [List.getElem_set_self (by simp [nvWacExtWords_len])]

private theorem nvM8DelayExt_elem_ne {k : Nat} (hk0 : 0 ≠ k) (hk122 : 122 ≠ k)
    (hk126 : 126 ≠ k) (hlt : k < 288) :
    nvM8DelayExt[k]'(by rw [nvM8DelayExt_len]; exact hlt) = 0#64 := by
  simp only [nvM8DelayExt, List.getElem_set_ne hk126, List.getElem_set_ne hk122,
    List.getElem_set_ne hk0]
  simp [nvWacExtWords, List.getElem_replicate]

private theorem nvM8DelayExt_elem122 :
    nvM8DelayExt[122]'(by rw [nvM8DelayExt_len]; decide) = 2#64 := by
  simp only [nvM8DelayExt, List.getElem_set_ne (by decide : 126 ≠ 122)]
  rw [List.getElem_set_self (by simp [nvWacExtWords_len])]

private theorem nvM8DelayExt_elem126 :
    nvM8DelayExt[126]'(by rw [nvM8DelayExt_len]; decide) = 4#64 := by
  simp only [nvM8DelayExt]
  rw [List.getElem_set_self (by simp [nvWacExtWords_len])]

theorem nvM8DelayExt_initOk : M6HdrExtInitOk nvM8DelayExt :=
  fullM6HdrMem_ext_init_of_magic nvM6HdrCfg_ok nvM8DelayExt_ok nvOneLit_lengths nvM8DelayMem_ok
    nvM8DelayExt_elem_magic

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `m8_hdr_record_used` (`glue = 80#64` on
initialized `nvM8DelayMem`), pinning `80 -> 63` write at word `32 + 63 = 95` + `total_used[0] = 1`
without touching M8 words `96..159`. -/
theorem nv_m8_record_used_clamp64 :
    Func.wp waveACoreEnv m8_hdr_record_used_body (nvOneLitCfg.hdr, 80#64, ()) nvM8DelayMem
      (fun () m' => nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ((nvM8DelayExt.set 95 1#64).set 14 1#64) nvOneLitState m')
      (fun _ _ _ _ => False) := by
  unfold Func.wp m8_hdr_record_used_body
  c0_hsteps_nogrp
  wac_call waveACoreEnv_ensureInit
  refine m6ExtEnsureInitSpec_of nvM6HdrCfg_ok nvM8DelayExt_ok nvOneLit_lengths
    (by rw [sep_emp]; exact nvM8DelayMem_ok) fun ext1 m1 _ hpres1 hm1 => ?_
  obtain rfl : ext1 = nvM8DelayExt := hpres1 nvM8DelayExt_initOk
  have hl : nvM8DelayExt.length = 288 := nvM8DelayExt_len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (st, ()) m2 => m2 = m1 ∧ st = 0#64)
    ?_ (fun _ hJs => by c0_hsteps; exact hJs (0#64, ()) m1 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m2 ⟨hm2, rfl⟩; subst m2
  refine wp_join_group (ts := [i64]) (fun (gi, ()) m2 => m2 = m1 ∧ gi = 63#64)
    ?_ (fun _ hJg => by c0_hsteps; exact hJg (63#64, ()) m1 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m2 ⟨hm2, rfl⟩; subst m2
  refine wp_join_group (ts := [i64]) (fun (base, ()) m2 => m2 = m1 ∧ base = 32#64)
    ?_ (fun _ hJb => by c0_hsteps; exact hJb (32#64, ()) m1 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m2 ⟨hm2, rfl⟩; subst m2
  have h95_lt : (95#64 : BitVec 64).toNat < nvM8DelayExt.length := by rw [hl]; decide
  have he95 : nvM8DelayExt[95]'(by rw [hl]; decide) = 0#64 :=
    nvM8DelayExt_elem_ne (by decide) (by decide) (by decide) (by decide)
  have h95eq : (32#64 + 63#64 : BitVec 64).toNat = 95 := rfl
  have h95m : (32 + 63) % 2 ^ 64 = 95 := rfl
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () m2 => (FullMem nvOneLitCfg nvOneLitState ⋆
      (array64 (nvOneLitCfg.hdr - 2304) (nvM8DelayExt.set 95 1#64) ⋆ emp)) m2)
    ?_ (fun _ hJu => by
      c0_hsteps
      · simp only [h95eq, he95] at hm
        exact hJu () _ hm
      · exfalso; simp only [h95m, he95] at hc; revert hc; decide)
  rintro _ ⟨⟩ m2 hm2
  have h14_lt : (14#64 : BitVec 64).toNat < (nvM8DelayExt.set 95 1#64).length := by
    rw [List.length_set, hl]; decide
  have he14 : (nvM8DelayExt.set 95 1#64)[14]'(by rw [List.length_set, hl]; decide) = 0#64 := by
    rw [List.getElem_set_ne (by decide : 95 ≠ 14)]
    exact nvM8DelayExt_elem_ne (by decide) (by decide) (by decide) (by decide)
  have h14eq : (14 + 0#64 : BitVec 64).toNat = 14 := rfl
  have h14m : ((14 : BitVec 64).toNat + 0) % 2 ^ 64 = 14 := rfl
  c0_hsteps
  · simp only [h14eq, he14] at hm
    have hm_f : (FullM6HdrMem nvOneLitCfg ((nvM8DelayExt.set 95 1#64).set 14 1#64)
        nvOneLitState ⋆ emp) m :=
      (fullM6HdrMem_iff nvOneLitCfg ((nvM8DelayExt.set 95 1#64).set 14 1#64) nvOneLitState emp
        m).mpr hm
    rw [sep_emp] at hm_f
    exact ⟨nvWac_unsat, hm_f⟩
  · exfalso; simp only [h14m, he14] at hc; revert hc; decide

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) exercising M8 delay slot `id = 6` (`delaying`),
directly pinning `b = true`, exact `ext' = nvM8DelayExt.set 122 1#64`, and `nvOneLitState`. -/
theorem nv_m8_delay_slot6_delaying :
    Func.wp waveACoreEnv m6_hdr_delaying_body (nvOneLitCfg.hdr, 6#64, ()) nvM8DelayMem
      (fun (b, ()) m' => b = true ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg (nvM8DelayExt.set 122 1#64) nvOneLitState m')
      (fun _ _ _ _ => False) := by
  unfold Func.wp m6_hdr_delaying_body
  c0_hsteps_nogrp
  wac_call waveACoreEnv_ensureInit
  refine m6ExtEnsureInitSpec_of nvM6HdrCfg_ok nvM8DelayExt_ok nvOneLit_lengths
    (by rw [sep_emp]; exact nvM8DelayMem_ok) fun ext1 m1 _ hpres1 hm1 => ?_
  obtain rfl : ext1 = nvM8DelayExt := hpres1 nvM8DelayExt_initOk
  have hl : nvM8DelayExt.length = 288 := nvM8DelayExt_len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (idx, ()) m2 => m2 = m1 ∧ idx = 122#64)
    ?_ (fun _ hJi => by c0_hsteps; exact hJi (122#64, ()) m1 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m2 ⟨hm2, rfl⟩; subst m2
  have h122_lt : (122#64 : BitVec 64).toNat < nvM8DelayExt.length := by rw [hl]; decide
  have he122 : nvM8DelayExt[122]'(by rw [hl]; decide) = 2#64 := nvM8DelayExt_elem122
  have h122eq : (122#64 : BitVec 64).toNat = 122 := rfl
  have h122m : 122 % 2 ^ 64 = 122 := rfl
  c0_hsteps
  · simp only [h122eq, he122] at hm
    have hm_f : (FullM6HdrMem nvOneLitCfg (nvM8DelayExt.set 122 1#64) nvOneLitState ⋆ emp) m :=
      (fullM6HdrMem_iff nvOneLitCfg (nvM8DelayExt.set 122 1#64) nvOneLitState emp m).mpr hm
    rw [sep_emp] at hm_f
    exact ⟨rfl, nvWac_unsat, hm_f⟩
  · exfalso; simp only [h122m, he122] at hc; revert hc; decide

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) exercising M8 `m6_hdr_bump_delay` (`id = 4`),
pinning exact `ext' = (nvM8DelayExt.set 124 1#64).set 120 1#64` and `nvOneLitState`. -/
theorem nv_m8_delay_slot4_bump :
    Func.wp waveACoreEnv m6_hdr_bump_delay_body (nvOneLitCfg.hdr, 4#64, ()) nvM8DelayMem
      (fun () m' => nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ((nvM8DelayExt.set 124 1#64).set 120 1#64) nvOneLitState m')
      (fun _ _ _ _ => False) := by
  unfold Func.wp m6_hdr_bump_delay_body
  c0_hsteps_nogrp
  wac_call waveACoreEnv_ensureInit
  refine m6ExtEnsureInitSpec_of nvM6HdrCfg_ok nvM8DelayExt_ok nvOneLit_lengths
    (by rw [sep_emp]; exact nvM8DelayMem_ok) fun ext1 m1 _ hpres1 hm1 => ?_
  obtain rfl : ext1 = nvM8DelayExt := hpres1 nvM8DelayExt_initOk
  have hl : nvM8DelayExt.length = 288 := nvM8DelayExt_len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (cidx, ()) m2 => m2 = m1 ∧ cidx = 124#64)
    ?_ (fun _ hJc => by c0_hsteps; exact hJc (124#64, ()) m1 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m2 ⟨hm2, rfl⟩; subst m2
  refine wp_join_group (ts := [i64]) (fun (nidx, ()) m3 => m3 = m1 ∧ nidx = 120#64)
    ?_ (fun _ hJn => by c0_hsteps; exact hJn (120#64, ()) m1 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m3 ⟨hm3, rfl⟩; subst m3
  have h124_lt : (124#64 : BitVec 64).toNat < nvM8DelayExt.length := by rw [hl]; decide
  have he124 : nvM8DelayExt[(124#64 : BitVec 64).toNat]'h124_lt = 0#64 :=
    nvM8DelayExt_elem_ne (by decide) (by decide) (by decide) (by decide)
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (cap, ()) m4 => m4 = m1 ∧ cap = 8#64)
    ?_ (fun _ hJp => by c0_hsteps; exact hJp (8#64, ()) m1 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m4 ⟨hm4, rfl⟩; subst m4
  refine wp_join_group (ts := [i64]) (fun (cur, ()) m5 => m5 = m1 ∧ cur = 1#64)
    ?_ (fun _ hJc => by
      c0_hsteps <;>
        first
        | exact hJc (1#64, ()) m1 ⟨rfl, rfl⟩
        | (exfalso
           have h124n : (124 % 2 ^ 64 : Nat) = 124 := rfl
           rw [h124n] at hc
           have h0 : nvM8DelayExt[124]'(by rw [hl]; decide) = 0#64 := he124
           rw [h0] at hc
           exact absurd (by decide : (0#64 : BitVec 64).toNat < 8 % 2 ^ 64) hc))
  rintro _ ⟨_, ⟨⟩⟩ m5 ⟨hm5, rfl⟩; subst m5
  have h120_lt : (120#64 : BitVec 64).toNat < (nvM8DelayExt.set 124 1#64).length := by
    rw [List.length_set, hl]; decide
  c0_hsteps
  rw [show (124#64 : BitVec 64).toNat = 124 from rfl,
    show (120#64 : BitVec 64).toNat = 120 from rfl] at hm
  have hm_f : (FullM6HdrMem nvOneLitCfg ((nvM8DelayExt.set 124 1#64).set 120 1#64)
      nvOneLitState ⋆ emp) m :=
    (fullM6HdrMem_iff nvOneLitCfg ((nvM8DelayExt.set 124 1#64).set 120 1#64) nvOneLitState emp
      m).mpr hm
  rw [sep_emp] at hm_f
  exact ⟨nvWac_unsat, hm_f⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) exercising M8 `m6_hdr_reduce_delay` (`id = 6`),
halving `e[126] = 4#64 -> 2#64` and setting `e[122] := 2#64` on `nvOneLitState`. -/
theorem nv_m8_delay_slot6_reduce :
    Func.wp waveACoreEnv m6_hdr_reduce_delay_body (nvOneLitCfg.hdr, 6#64, ()) nvM8DelayMem
      (fun () m' => nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ((nvM8DelayExt.set 126 2#64).set 122 2#64) nvOneLitState m')
      (fun _ _ _ _ => False) := by
  unfold Func.wp m6_hdr_reduce_delay_body
  c0_hsteps_nogrp
  wac_call waveACoreEnv_ensureInit
  refine m6ExtEnsureInitSpec_of nvM6HdrCfg_ok nvM8DelayExt_ok nvOneLit_lengths
    (by rw [sep_emp]; exact nvM8DelayMem_ok) fun ext1 m1 _ hpres1 hm1 => ?_
  obtain rfl : ext1 = nvM8DelayExt := hpres1 nvM8DelayExt_initOk
  have hl : nvM8DelayExt.length = 288 := nvM8DelayExt_len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (cidx, ()) m2 => m2 = m1 ∧ cidx = 126#64)
    ?_ (fun _ hJc => by c0_hsteps; exact hJc (126#64, ()) m1 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m2 ⟨hm2, rfl⟩; subst m2
  refine wp_join_group (ts := [i64]) (fun (nidx, ()) m3 => m3 = m1 ∧ nidx = 122#64)
    ?_ (fun _ hJn => by c0_hsteps; exact hJn (122#64, ()) m1 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m3 ⟨hm3, rfl⟩; subst m3
  have h126_lt : (126#64 : BitVec 64).toNat < nvM8DelayExt.length := by rw [hl]; decide
  have he126_v : nvM8DelayExt[126]'(by rw [hl]; decide) = 4#64 := nvM8DelayExt_elem126
  have he126 : nvM8DelayExt[126]'(by rw [hl]; decide) >>> (1 : Nat) = 2#64 := by
    rw [he126_v]; decide
  have h122_lt : (122#64 : BitVec 64).toNat <
      (nvM8DelayExt.set (126#64 : BitVec 64).toNat
        (nvM8DelayExt[(126#64 : BitVec 64).toNat]'h126_lt >>> 1)).length := by
    rw [List.length_set, hl]; decide
  have h126eq : (126#64 : BitVec 64).toNat = 126 := rfl
  have h122eq : (122#64 : BitVec 64).toNat = 122 := rfl
  c0_hsteps
  simp only [h126eq, h122eq, he126] at hm
  have hm_f : (FullM6HdrMem nvOneLitCfg ((nvM8DelayExt.set 126 2#64).set 122 2#64)
      nvOneLitState ⋆ emp) m :=
    (fullM6HdrMem_iff nvOneLitCfg ((nvM8DelayExt.set 126 2#64).set 122 2#64) nvOneLitState emp
      m).mpr hm
  rw [sep_emp] at hm_f
  exact ⟨nvWac_unsat, hm_f⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_vivify_tier_m6_hdr`. -/
theorem nv_m8_vivify_tier :
    Func.wp waveACoreEnv full_vivify_tier_m6_hdr_body
      (nvOneLitCfg.hdr, 0#64, 1#64, 100#64, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 7 waveACoreSpecTable_at7 (waveACoreFns.take 7) (waveACoreFns.drop 8)
    waveACoreFns[7] rfl rfl rfl rfl
    full_vivify_tier_m6_hdr_body rfl _ nvM6HdrMem _
    (m8VivifyTierSpec_of nvM6HdrCfg_ok nvM6ExtWords_ok nvWac_sparse nvWac_hdrMem_emp
      fun r ext' s' m' hext' _ hsp' _ _ hnz _ hr hu hm' => by
        rw [sep_emp] at hm'; obtain ⟨hcl, hpr⟩ := hnz (by decide)
        exact ⟨ext', s', hext', hsp', hcl, hpr, hr, hu, hm'⟩)

/-- Witness state with `num_redundant := 1#64` so `full_vivify_m6_hdr` skips the
`h->num_redundant == 0ULL` early exit and enters the `M8_DELAY_VIVIFY_IRR` throttling block. -/
def nvM8VivState : FullState :=
  nvWacState 1#64 0#64 0#64 0#64 0#64

/-- Initialized M8 vivify delay words: `nvM8DelayExt` with `e[120] = 2#64` (`delay[4].cnt = 2`).
-/
def nvM8VivExt : List (BitVec 64) :=
  nvM8DelayExt.set 120 2#64

/-- Concrete `Mem 64` image for `nvM8VivState` and `nvM8VivExt`. -/
def nvM8VivMem : Mem 64 :=
  storeMem (storeMem nvM8DelayMem i64 ((nvOneLitCfg.hdr - 2304) + 960#64) 2#64)
    i64 (nvOneLitCfg.hdr + 496) 1#64

private theorem nvM8VivExt_len : nvM8VivExt.length = 288 := by
  simp [nvM8VivExt, nvM8DelayExt_len]

theorem nvM8VivExt_ok : M6HdrExtOk nvM8VivExt :=
  M6HdrExtOk.of_len nvM8VivExt_len

theorem nvM8VivExt_initOk : M6HdrExtInitOk nvM8VivExt :=
  nvM8DelayExt_initOk.set_pos 2#64 (by decide)

theorem nvM8VivMem_ok : FullM6HdrMem nvOneLitCfg nvM8VivExt nvM8VivState nvM8VivMem := by
  have hm0 : (FullM6HdrMem nvOneLitCfg nvM8DelayExt nvOneLitState ⋆ emp) nvM8DelayMem := by
    rw [sep_emp]; exact nvM8DelayMem_ok
  have hm1 := (fullM6HdrMem_iff ..).mp hm0
  have h1 := (M6HdrTactics.store_m6Ext_const (k := 960#64) 2#64 hm1 (by decide)
    (by rw [nvM8DelayExt_len]; decide)).2
  have h1f := fullM6HdrMem_focus_full ((fullM6HdrMem_iff ..).mpr h1)
  have h2 := (FullArenaTactics.store_full_num_redundant 1#64 h1f).2
  have hm' := fullM6HdrMem_unfocus_full h2
  rw [sep_emp] at hm'
  have hst : nvM8VivState =
      { nvOneLitState with core := { nvOneLitState.core with num_redundant := 1#64 } } := by
    simp [nvM8VivState, nvWacState, nvOneLitState, nvOneLitScratch]
  simpa [nvM8VivExt, nvM8VivMem, hst, Nat.div_self] using hm'

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_vivify_m6_hdr` under `waveACoreEnv`
on mutated `nvM8VivMem` (`num_redundant = 1#64`, `e[120] = 2#64`). -/
theorem nv_m8_vivify :
    Func.wp waveACoreEnv full_vivify_m6_hdr_body (nvOneLitCfg.hdr, ()) nvM8VivMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtInitOk ext' ∧ M6ExtW2bPres nvM8VivExt ext' ∧
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.probing = 0#64 ∧ (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 8 waveACoreSpecTable_at8 (waveACoreFns.take 8) (waveACoreFns.drop 9)
    waveACoreFns[8] rfl rfl rfl rfl
    full_vivify_m6_hdr_body rfl _ nvM8VivMem _
    (m6aVivifySpec_of nvM6HdrCfg_ok nvM8VivExt_ok (nvWac_sparse_of_fields 1#64 0#64 0#64 0#64)
      (by rw [sep_emp]; exact nvM8VivMem_ok)
      fun r ext' s' m' ⟨_, hpr_ext⟩ hsp' ⟨hcl', hpr'⟩ _ hr hu hm' => by
        rw [sep_emp] at hm'
        obtain ⟨hinit', hw2b'⟩ := hpr_ext nvM8VivExt_initOk
        exact ⟨ext', s', hinit', hw2b', hsp', hcl', hpr', hr, hu, hm'⟩)

/-- Witness state with `unassigned := 1#64` and `elim_bound := 4#64` so
`y * 2000ULL < h->unassigned && h->elim_bound >= 4ULL` evaluates true on `m8_eliminate_m6`. -/
def nvM8ElimState : FullState :=
  nvWacState 0#64 0#64 1#64 0#64 4#64

/-- Expected post-state after `m8_eliminate_m6(..., false)` on `nvM8ElimMem`. -/
def nvM8ElimPostState : FullState :=
  { nvM8ElimState with scratch := { nvM8ElimState.scratch with
    eliminations := 1#64, elim_limit := 1000#64 } }

/-- Concrete `Mem 64` image for `nvM8ElimState` and `nvM8DelayExt`. -/
def nvM8ElimMem : Mem 64 :=
  storeMem (storeMem nvM8DelayMem i64 (nvOneLitCfg.hdr + 792) 1#64)
    i64 (nvOneLitCfg.hdr + 1008) 4#64

theorem nvM8ElimMem_ok : FullM6HdrMem nvOneLitCfg nvM8DelayExt nvM8ElimState nvM8ElimMem := by
  have hm0 : (FullM6HdrMem nvOneLitCfg nvM8DelayExt nvOneLitState ⋆ emp) nvM8DelayMem := by
    rw [sep_emp]; exact nvM8DelayMem_ok
  have h1 := (FullArenaTactics.store_full_unassigned 1#64 (fullM6HdrMem_focus_full hm0)).2
  have h2 := (FullArenaTactics.store_full_elim_bound 4#64 h1).2
  have hm' := fullM6HdrMem_unfocus_full h2
  rw [sep_emp] at hm'
  have hst : nvM8ElimState =
      { core := { nvOneLitState.core with unassigned := 1#64 },
        scratch := { nvOneLitState.scratch with elim_bound := 4#64 } } := by
    simp [nvM8ElimState, nvWacState, nvOneLitState, nvOneLitScratch]
  simpa [nvM8ElimMem, hst] using hm'

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `m8_eliminate_m6` (`initial := true`). -/
theorem nv_m8_eliminate_init :
    Func.wp waveACoreEnv m8_eliminate_m6_body (nvOneLitCfg.hdr, true, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 9 waveACoreSpecTable_at9 (waveACoreFns.take 9) (waveACoreFns.drop 10)
    waveACoreFns[9] rfl rfl rfl rfl
    m8_eliminate_m6_body rfl _ nvM6HdrMem _
    (m8EliminateSpec_of nvM6HdrCfg_ok nvM6ExtWords_ok nvWac_sparse rfl nvWac_hdrMem_emp
      fun r ext' s' m' hext' _ hsp' hcl' _ hr' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hext', hsp', hcl', hr', nvWac_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `m8_eliminate_m6` (`initial := false`) on
mutated `nvM8ElimMem` (`unassigned = 1#64`, `elim_bound = 4#64`, initialized `nvM8DelayExt`). -/
theorem nv_m8_eliminate_post :
    Func.wp waveACoreEnv m8_eliminate_m6_body (nvOneLitCfg.hdr, false, ()) nvM8ElimMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtInitOk ext' ∧ M6ExtW2bPres nvM8DelayExt ext' ∧
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 9 waveACoreSpecTable_at9 (waveACoreFns.take 9) (waveACoreFns.drop 10)
    waveACoreFns[9] rfl rfl rfl rfl
    m8_eliminate_m6_body rfl _ nvM8ElimMem _
    (m8EliminateSpec_of nvM6HdrCfg_ok nvM8DelayExt_ok (nvWac_sparse_of_fields 0#64 0#64 1#64 4#64)
      rfl (by rw [sep_emp]; exact nvM8ElimMem_ok)
      fun r ext' s' m' _ hpr_ext hsp' hcl' _ hr' _ hm' => by
        rw [sep_emp] at hm'
        obtain ⟨hinit', hw2b'⟩ := hpr_ext nvM8DelayExt_initOk
        exact ⟨ext', s', hinit', hw2b', hsp', hcl', hr', nvWac_unsat, hm'⟩)

/-- Mutated concrete `FullM6HdrMem` state with `num_binary = 1#64` and `delay[6].cnt = 2#64` so
`full_probe_tail_m6` exercises `M8_DELAY_BACKBONE` and `M8W_BACKBONE_SKIPS` (`e[134]`). -/
def nvM8ProbeTailState : FullState :=
  nvWacState 0#64 1#64 0#64 0#64 0#64

def nvM8ProbeTailMem : Mem 64 :=
  storeMem nvM8DelayMem i64 (nvOneLitCfg.hdr + 504) 1#64

theorem nvM8ProbeTailMem_ok :
    FullM6HdrMem nvOneLitCfg nvM8DelayExt nvM8ProbeTailState nvM8ProbeTailMem := by
  have hm_del : (FullM6HdrMem nvOneLitCfg nvM8DelayExt nvOneLitState ⋆ emp) nvM8DelayMem := by
    rw [sep_emp]; exact nvM8DelayMem_ok
  have hm0 := (fullM6HdrMem_iff nvOneLitCfg nvM8DelayExt nvOneLitState emp nvM8DelayMem).mp hm_del
  have h1 := (FullArenaTactics.store_full_num_binary 1#64 hm0).2
  have hm' :=
    (fullM6HdrMem_iff nvOneLitCfg nvM8DelayExt nvM8ProbeTailState emp nvM8ProbeTailMem).mpr h1
  rw [sep_emp] at hm'
  have hst : nvM8ProbeTailState =
      { nvOneLitState with core := { nvOneLitState.core with num_binary := 1#64 } } := by
    simp [nvM8ProbeTailState, nvWacState, nvOneLitState, nvOneLitScratch]
  simpa [hst] using hm'

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_probe_tail_m6` exercising `delay[6]`
and `M8W_BACKBONE_SKIPS` (`e[134]`). -/
theorem nv_m8_probe_tail_delay6 :
    Func.wp waveACoreEnv full_probe_tail_m6_body (nvOneLitCfg.hdr, 100#64, ()) nvM8ProbeTailMem
      (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 10 waveACoreSpecTable_at10 (waveACoreFns.take 10) [] waveACoreFns[10] rfl rfl rfl rfl
    full_probe_tail_m6_body rfl _ nvM8ProbeTailMem _
    (m6ProbeTailSpec_of (FullM6HdrInv.mk_inv nvM6HdrCfg_ok nvM8DelayExt_ok
      (nvWac_sparse_of_fields 0#64 1#64 0#64 0#64)) rfl (by rw [sep_emp]; exact nvM8ProbeTailMem_ok)
      fun r ext' s' m' _ _ _ hr' hu' h1' hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hr', hu', h1', hm'⟩)

/-- Valid concrete realization of external leaves extending `waveACoreEnv`: each added witness
matches concrete `nvOneLitCfg` admissible outcomes (including `dense_mode = 0 <-> 1`). -/
def nvWacExtWitness : Env := fun f as bs xs m Q X =>
  match f, as, bs, xs with
  | "m6_hdr_sync_legacy_tiers", [.bits 64], [], (h, ()) =>
    h = nvOneLitCfg.hdr ∧ Q () m
  | "m6_hdr_get_watermark", [.bits 64, .bits 64], [.bits 64], (h, _) =>
    h = nvOneLitCfg.hdr ∧ Q (0#64, ()) m
  | "full_viv_collect_m6", [.bits 64, .bits 64], [.bits 64], (h, _) =>
    h = nvOneLitCfg.hdr ∧ Q (0#64, ()) m
  | "full_viv_count_m6", [.bits 64, .bits 64], [], (h, bn, ()) =>
    h = nvOneLitCfg.hdr ∧ bn = 0#64 ∧ Q () m
  | "full_viv_keys_m6", [.bits 64, .bits 64], [], (h, bn, ()) =>
    h = nvOneLitCfg.hdr ∧ bn = 0#64 ∧ Q () m
  | "full_viv_sort_sched_m6", [.bits 64, .bits 64], [], (h, bn, ()) =>
    h = nvOneLitCfg.hdr ∧ bn = 0#64 ∧ Q () m
  | "full_elim_dticks", [.bits 64, .bool], [.bits 64], (h, _) =>
    h = nvOneLitCfg.hdr ∧ Q (0#64, ()) m
  | "full_log10_q16_m7", [.bits 64], [.bits 64], (x, ()) =>
    x = 10#64 ∧ Q (65536#64, ()) m
  | "full_scale_delta", [.bits 64, .bits 64], [.bits 64], (h, d, ()) =>
    h = nvOneLitCfg.hdr ∧ Q (d, ()) m
  | "full_min_u64", [.bits 64, .bits 64], [.bits 64], (a, b, ()) =>
    Q ((if a ≤ b then a else b), ()) m
  | "full_enter_dense", [.bits 64], [.bool], (h, ()) =>
    h = nvOneLitCfg.hdr ∧
      (∃ s R, FullSparseInv nvOneLitCfg nvOneLitF0 s ∧ (FullMem nvOneLitCfg s ⋆ R) m) ∧
      Q (true, ()) (storeMem m i64 (nvOneLitCfg.hdr + 1016) 1#64)
  | "full_forward_sub", [.bits 64, .bits 64], [.bits 64], (h, _) =>
    h = nvOneLitCfg.hdr ∧
      (∃ s R, FullDenseInv nvOneLitCfg nvOneLitF0 s ∧ (FullMem nvOneLitCfg s ⋆ R) m) ∧
      Q (1#64, ()) m
  | "full_elim_bve_m7", [.bits 64, .bits 64], [.bits 64], (h, _) =>
    h = nvOneLitCfg.hdr ∧ Q (1#64, ()) m
  | "full_rebuild_watches", [.bits 64], [.bits 64], (h, ()) =>
    h = nvOneLitCfg.hdr ∧
      (∃ s R, FullDenseInv nvOneLitCfg nvOneLitF0 s ∧ (FullMem nvOneLitCfg s ⋆ R) m) ∧
      Q (1#64, ()) (storeMem m i64 (nvOneLitCfg.hdr + 1016) 0#64)
  | _, _, _, xs => waveACoreEnv f _ _ xs m Q X

/-- Leaf refinement environment: `waveACoreEnv` plus admissible concrete leaf witnesses. -/
def nvWacLeafEnv : Env := fun f as bs xs m Q X =>
  waveACoreEnv f as bs xs m Q X ∨ nvWacExtWitness f as bs xs m Q X

/-- Layered deterministic refinement environment: executes real Wave A C0 bodies for
`m6_hdr_delaying`, `m6_hdr_bump_delay`, `m6_hdr_reduce_delay`, and `full_vivify_tier_m6_hdr`
over `nvWacLeafEnv`. -/
def nvWacDetEnv : Env := fun f as bs xs m Q X =>
  nvWacLeafEnv f as bs xs m Q X ∨
  match f, as, bs, xs with
  | "m6_hdr_delaying", [.bits 64, .bits 64], [.bool], xs =>
    Func.wp nvWacLeafEnv m6_hdr_delaying_body xs m Q X
  | "m6_hdr_bump_delay", [.bits 64, .bits 64], [], xs =>
    Func.wp nvWacLeafEnv m6_hdr_bump_delay_body xs m Q X
  | "m6_hdr_reduce_delay", [.bits 64, .bits 64], [], xs =>
    Func.wp nvWacLeafEnv m6_hdr_reduce_delay_body xs m Q X
  | "full_vivify_tier_m6_hdr", [.bits 64, .bits 64, .bits 64, .bits 64], [.bits 64], xs =>
    Func.wp nvWacLeafEnv full_vivify_tier_m6_hdr_body xs m Q X
  | _, _, _, _ => False

theorem waveACoreEnv_le_nvWacDetEnv : ∀ f as bs xs m Q X,
    waveACoreEnv f as bs xs m Q X → nvWacDetEnv f as bs xs m Q X :=
  fun _ _ _ _ _ _ _ h => Or.inl (Or.inl h)

/-- Tier-0 non-empty candidate extension on `nvWacDetEnv` for exercising `m6_hdr_bump_delay`:
sets `e[118] = 1#64` (`M8W_VIV_LAST_TRIED`) on `full_vivify_tier_m6_hdr(..., 0#64, ...)`,
while still running real `m6_hdr_delaying_body` and `m6_hdr_bump_delay_body`. -/
def nvWacVivBumpEnv : Env := fun f as bs xs m Q X =>
  nvWacDetEnv f as bs xs m Q X ∨
  match f, as, bs, xs with
  | "full_vivify_tier_m6_hdr", [.bits 64, .bits 64, .bits 64, .bits 64], [.bits 64],
      (h, tm, bud, _, ()) =>
    h = nvOneLitCfg.hdr ∧ tm = 0#64 ∧ bud ≠ 0#64 ∧
      Q (1#64, ()) (storeMem m i64 ((nvOneLitCfg.hdr - 2304) + 944#64) 1#64)
  | _, _, _, _ => False

theorem nvWacDetEnv_le_nvWacVivBumpEnv : ∀ f as bs xs m Q X,
    nvWacDetEnv f as bs xs m Q X → nvWacVivBumpEnv f as bs xs m Q X :=
  fun _ _ _ _ _ _ _ h => Or.inl h

private theorem nvWac_det_leaf {f as bs xs m Q X}
    (h : nvWacExtWitness f as bs xs m Q X) : nvWacDetEnv f as bs xs m Q X :=
  Or.inl (Or.inr h)

private theorem nvWac_bump_leaf {f as bs xs m Q X}
    (h : nvWacExtWitness f as bs xs m Q X) : nvWacVivBumpEnv f as bs xs m Q X :=
  Or.inl (Or.inl (Or.inr h))

private theorem nvWac_run_tier_det {ext : List (BitVec 64)} (hlen : ext.length = 288)
    (he118 : ext[118]'(by omega) = 0#64) :
    ∀ tm bud tl m0,
      (FullMem nvOneLitCfg nvM8VivState ⋆ (array64 (nvOneLitCfg.hdr - 2304) ext ⋆ emp)) m0 →
      bud = 0xFFFFFFFF#64 → tm = 1#64 ∨ tm = 3#64 → ∀ (Q0 : Post [i64]),
      (∀ m1, (FullM6HdrMem nvOneLitCfg ext nvM8VivState ⋆ emp) m1 → Q0 (1#64, ()) m1) →
      nvWacDetEnv "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64]
        (nvOneLitCfg.hdr, tm, bud, tl, ()) m0 Q0 (fun _ _ _ _ => False) := by
  intro tm bud tl m0 hm0 hbud htm Q0 hQ0
  subst bud
  refine Or.inr ?_
  change Func.wp nvWacLeafEnv full_vivify_tier_m6_hdr_body
    (nvOneLitCfg.hdr, tm, 0xFFFFFFFF#64, tl, ()) m0 Q0 (fun _ _ _ _ => False)
  unfold Func.wp full_vivify_tier_m6_hdr_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun () m1 => m1 = m0) ?_
    (fun _ hJ1 => by c0_hsteps <;> first | exact hJ1 () m0 rfl | exact absurd hc (by decide))
  rintro _ ⟨⟩ m1 rfl; clear hc
  c0_hsteps_nogrp
  let s2 : FullState :=
    { nvM8VivState with core := { nvM8VivState.core with probing := 1#64 } }
  refine LeanQbe.T.wp_call_of_spec _ _ ?_
  refine Or.inr ⟨rfl, ?_⟩
  refine wp_join_group (ts := [])
    (fun () m5 => (FullMem nvOneLitCfg s2 ⋆
      (array64 (nvOneLitCfg.hdr - 2304) ext ⋆ emp)) m5) ?_ ?_
  · rintro _ ⟨⟩ m5 hm5
    c0_hsteps_nogrp
    refine wp_loop_break_group (brkTs := [i64, i64, i64]) (lpTs := [i64, i64])
      (fun (_b, res_b, bi_b, ()) mb =>
        (FullMem nvOneLitCfg s2 ⋆ (array64 (nvOneLitCfg.hdr - 2304) ext ⋆ emp)) mb ∧
          res_b = 1#64 ∧ bi_b = 0#64)
      (fun rem (_bud, bi, ()) mvi => rem = 0 ∧ bi = 0#64 ∧ mvi = m5) ?_ ?_ ?_
    · rintro _ ⟨_, _, _, ⟨⟩⟩ mb ⟨hmb, rfl, rfl⟩
      refine wp_join_group (ts := []) (fun () m_bt => m_bt = mb) ?_
        (fun _ hJbt => by
          c0_hsteps <;> first | exact hJbt () mb rfl | exact absurd hc (by decide))
      rintro _ ⟨⟩ m_bt hmbt; subst m_bt
      refine wp_join_group (ts := []) (fun () m_w => m_w = mb) ?_
        (fun _ hJw => by
          c0_hsteps <;> first | exact hJw () mb rfl | (exfalso; revert hc; decide))
      rintro _ ⟨⟩ m_w hmw; subst m_w
      have h118_mod : (944#64 : BitVec 64).toNat % 8 = 0 := by decide
      have h118_lt : (944#64 : BitVec 64).toNat / 8 < ext.length := by rw [hlen]; decide
      c0_hsteps
      have hset118 : ext.set 118 0#64 = ext := by
        apply List.ext_getElem (by rw [List.length_set])
        intro i hi _
        by_cases hi118 : i = 118
        · subst hi118
          rw [List.getElem_set_self (by rw [List.length_set, hlen]; decide), he118]
        · rw [List.getElem_set_ne (Ne.symm hi118)]
      rw [show BitVec.toNat (118 : BitVec 64) = 118 from rfl, hset118] at hm
      change (FullMem nvOneLitCfg nvM8VivState ⋆ (array64 (nvOneLitCfg.hdr - 2304) ext ⋆ emp)) m
        at hm
      exact hQ0 _ ((fullM6HdrMem_iff ..).mpr hm)
    · intro B L _ ⟨_, bi, ⟨⟩⟩ _ hB _ ⟨_, hbi, hmvi⟩
      subst hbi hmvi
      c0_hsteps <;>
        first
        | (exfalso; revert hc; decide)
        | exact hB _ _ ⟨hm5, rfl, rfl⟩
    · intro _ _ _ hL; c0_hsteps
      exact hL 0 (0xFFFFFFFF#64, 0#64, ()) m5 ⟨rfl, rfl, rfl⟩
  · intro _ hJ5
    rcases htm with rfl | rfl <;>
      · c0_hsteps
        refine LeanQbe.T.wp_call_of_spec _ _ ?_
        refine Or.inr ⟨rfl, rfl, ?_⟩
        refine LeanQbe.T.wp_call_of_spec _ _ ?_
        refine Or.inr ⟨rfl, rfl, ?_⟩
        refine LeanQbe.T.wp_call_of_spec _ _ ?_
        exact Or.inr ⟨rfl, rfl,
          by first | exact hJ5 () _ hm | (c0_hsteps <;> exact hJ5 () _ hm)⟩

/-- Concrete `Mem 64` C0 execution (`nvWacDetEnv`, `XPost := False`) of `full_vivify_m6_hdr_body`
on `nvM8VivMem` (`num_redundant = 1`, `e[120] = 2`), running real `full_vivify_tier_m6_hdr_body` and
`m6_hdr_delaying_body` and pinning exact `e[120] = 1#64`, `e[133] = 1#64`, `e[118] = 0#64`, and
unchanged `nvM8VivState`. -/
theorem nv_m8_vivify_irr_skip :
    Func.wp nvWacDetEnv full_vivify_m6_hdr_body (nvOneLitCfg.hdr, ()) nvM8VivMem
      (fun (r, ()) m' => r = 1#64 ∧
        FullSparseInv nvOneLitCfg nvOneLitF0 nvM8VivState ∧
        M6HdrExtInitOk ((nvM8VivExt.set 120 1#64).set 133 1#64) ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ((nvM8VivExt.set 120 1#64).set 133 1#64) nvM8VivState m')
      (fun _ _ _ _ => False) := by
  have hm_e : (FullM6HdrMem nvOneLitCfg nvM8VivExt nvM8VivState ⋆ emp) nvM8VivMem := by
    rw [sep_emp]; exact nvM8VivMem_ok
  have hm_s := (fullM6HdrMem_iff ..).mp hm_e
  have hl_v : nvM8VivExt.length = 288 := nvM8VivExt_len
  have he118_v : nvM8VivExt[118]'(by rw [hl_v]; decide) = 0#64 := by
    simp only [nvM8VivExt, List.getElem_set_ne (by decide : 120 ≠ 118)]
    exact nvM8DelayExt_elem_ne (by decide) (by decide) (by decide) (by decide)
  unfold Func.wp full_vivify_m6_hdr_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun () m1 => m1 = nvM8VivMem) ?_
    (fun _ hJ1 => by c0_hsteps; exact hJ1 () nvM8VivMem rfl)
  rintro _ ⟨⟩ m1 rfl
  refine LeanQbe.T.wp_call_of_spec _ _ ?_
  refine nvWac_det_leaf ⟨rfl, ?_⟩
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_call_of_spec _ _ ?_
  refine nvWac_det_leaf ⟨rfl, ?_⟩
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (_, ()) md => md = nvM8VivMem) ?_
    (fun _ hJd => by c0_hsteps <;> exact hJd (_, ()) nvM8VivMem rfl)
  rintro _ ⟨_, ⟨⟩⟩ md rfl; c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (_, ()) me => me = nvM8VivMem) ?_
    (fun _ hJe => by c0_hsteps <;> exact hJe (_, ()) nvM8VivMem rfl)
  rintro _ ⟨_, ⟨⟩⟩ me rfl; c0_hsteps_nogrp
  · exact absurd hc (by decide)
  refine wp_join_group (ts := [i64, i64]) (fun (_w1, w2, ()) mw => mw = nvM8VivMem ∧ w2 = 0#64) ?_
    (fun _ hJw => by
      c0_hsteps <;> first | exact hJw (_, 0#64, ()) _ ⟨rfl, rfl⟩ | (exfalso; revert hc; decide))
  rintro _ ⟨_w1, w2, ⟨⟩⟩ mw ⟨hmw, hw2⟩; subst mw hw2; c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (_, ()) ml1 => ml1 = nvM8VivMem) ?_
    (fun _ hJl1 => by c0_hsteps <;> exact hJl1 (_, ()) nvM8VivMem rfl)
  rintro _ ⟨_, ⟨⟩⟩ ml1 rfl
  refine LeanQbe.T.wp_call_of_spec _ _
    (nvWac_run_tier_det hl_v he118_v 1#64 0xFFFFFFFF#64 _ nvM8VivMem
      hm_s rfl (Or.inl rfl) _ fun m1 hm1 => ?_)
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64, i64])
    (fun (res2, _, ()) mt2 => res2 = 1#64 ∧
      (FullM6HdrMem nvOneLitCfg nvM8VivExt nvM8VivState ⋆ emp) mt2) ?_
    (fun _ hJt2 => by
      c0_hsteps <;> first | exact hJt2 (1#64, _, ()) _ ⟨rfl, hm1⟩ | (exfalso; revert hc; decide))
  rintro _ ⟨res2, _, ⟨⟩⟩ mt2 ⟨rfl, hmt2⟩; c0_hsteps_nogrp
  refine wp_join_group (ts := [i64, i64])
    (fun (res3, _, ()) mt3 => res3 = 1#64 ∧
      (FullM6HdrMem nvOneLitCfg nvM8VivExt nvM8VivState ⋆ emp) mt3) ?_
    (fun _ hJt3 => by
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (_, ()) ml3 => ml3 = mt2) ?_
        (fun _ hJl3 => by c0_hsteps <;> exact hJl3 (_, ()) mt2 rfl)
      rintro _ ⟨_, ⟨⟩⟩ ml3 hml3; subst ml3
      refine LeanQbe.T.wp_call_of_spec _ _
        (nvWac_run_tier_det hl_v he118_v 3#64 0xFFFFFFFF#64 _ mt2
          ((fullM6HdrMem_iff ..).mp hmt2) rfl (Or.inr rfl) _
          fun m2 hm2 => hJt3 (1#64, _, ()) _ ⟨rfl, hm2⟩))
  rintro _ ⟨res3, _, ⟨⟩⟩ mt3 ⟨rfl, hmt3⟩; c0_hsteps_nogrp
  refine wp_join_group (ts := [i64, i64])
    (fun (res0, _, ()) mt0 => res0 = 1#64 ∧
      (FullM6HdrMem nvOneLitCfg ((nvM8VivExt.set 120 1#64).set 133 1#64) nvM8VivState ⋆ emp) mt0)
    ?_ (fun _ hJ0 => by
      c0_hsteps
      refine LeanQbe.T.wp_call_of_spec _ _ ?_
      refine Or.inr ?_; dsimp only
      have he120_v : nvM8VivExt[120]'(by rw [hl_v]; decide) = 2#64 := by
        simp only [nvM8VivExt]
        rw [List.getElem_set_self (by rw [List.length_set, nvM8DelayExt_len]; decide)]
      have hdel : Func.wp waveACoreEnv m6_hdr_delaying_body (nvOneLitCfg.hdr, 4#64, ()) mt3
          (fun (b, ()) m3 => b = true ∧
            FullM6HdrMem nvOneLitCfg (nvM8VivExt.set 120 1#64) nvM8VivState m3)
          (fun _ _ _ _ => False) := by
        unfold Func.wp m6_hdr_delaying_body
        c0_hsteps_nogrp
        wac_call waveACoreEnv_ensureInit
        refine m6ExtEnsureInitSpec_of nvM6HdrCfg_ok nvM8VivExt_ok
          (nvWac_lengths 1#64 0#64 0#64 0#64 0#64) hmt3 fun ext1 m3 _ hpres1 hm3 => ?_
        obtain rfl : ext1 = nvM8VivExt := hpres1 nvM8VivExt_initOk
        rw [fullM6HdrMem_iff] at hm3
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun (idx, ()) m4 => m4 = m3 ∧ idx = 120#64)
          ?_ (fun _ hJi => by c0_hsteps; exact hJi (120#64, ()) m3 ⟨rfl, rfl⟩)
        rintro _ ⟨_, ⟨⟩⟩ m4 ⟨hm4, rfl⟩; subst m4
        have h120_lt : (120#64 : BitVec 64).toNat < nvM8VivExt.length := by rw [hl_v]; decide
        have h120eq : (120#64 : BitVec 64).toNat = 120 := rfl
        have h120m : 120 % 2 ^ 64 = 120 := rfl
        c0_hsteps
        · simp only [h120eq, he120_v] at hm
          have hm_f : (FullM6HdrMem nvOneLitCfg (nvM8VivExt.set 120 1#64) nvM8VivState ⋆ emp) m :=
            (fullM6HdrMem_iff nvOneLitCfg (nvM8VivExt.set 120 1#64) nvM8VivState emp m).mpr hm
          rw [sep_emp] at hm_f
          exact ⟨rfl, hm_f⟩
        · exfalso; simp only [h120m, he120_v] at hc; revert hc; decide
      refine Func.spec_env_mono (fun _ _ _ _ _ _ _ h => Or.inl h) hdel |> fun hw =>
        wp_mono ?_ (fun _ _ _ _ h => h) _ mt3 hw
      rintro ⟨b, ⟨⟩⟩ m3 ⟨rfl, hm3⟩
      c0_hsteps_nogrp
      · have hm3_e :
            (FullM6HdrMem nvOneLitCfg (nvM8VivExt.set 120 1#64) nvM8VivState ⋆ emp) m3 := by
          rw [sep_emp]; exact hm3
        have hm3' := (fullM6HdrMem_iff nvOneLitCfg (nvM8VivExt.set 120 1#64) nvM8VivState emp
          m3).mp hm3_e
        have h133_mod : (1064#64 : BitVec 64).toNat % 8 = 0 := by decide
        have h133_lt : (1064#64 : BitVec 64).toNat / 8 < (nvM8VivExt.set 120 1#64).length := by
          rw [List.length_set, hl_v]; decide
        have he133 : (nvM8VivExt.set 120 1#64)[133]'(by
            rw [List.length_set, hl_v]; decide) = 0#64 := by
          rw [List.getElem_set_ne (by decide : 120 ≠ 133)]
          simp only [nvM8VivExt, List.getElem_set_ne (by decide : 120 ≠ 133)]
          exact nvM8DelayExt_elem_ne (by decide) (by decide) (by decide) (by decide)
        c0_hsteps
        simp only [show (133 : BitVec 64).toNat = 133 from rfl, he133] at hm
        exact hJ0 (1#64, _, ()) _ ⟨rfl, (fullM6HdrMem_iff ..).mpr hm⟩
      · exact absurd (by assumption : true = false) (by decide))
  rintro _ ⟨res0, _, ⟨⟩⟩ mt0 ⟨rfl, hmt0⟩
  rw [fullM6HdrMem_iff] at hmt0
  c0_hsteps
  have hm_f : (FullM6HdrMem nvOneLitCfg ((nvM8VivExt.set 120 1#64).set 133 1#64)
      nvM8VivState ⋆ emp) m :=
    (fullM6HdrMem_iff nvOneLitCfg ((nvM8VivExt.set 120 1#64).set 133 1#64) nvM8VivState emp
      m).mpr hm
  rw [sep_emp] at hm_f
  exact ⟨rfl, nvWac_sparse_of_fields 1#64 0#64 0#64 0#64,
    (nvM8VivExt_initOk.set_pos 1#64 (by decide)).set_pos 1#64 (by decide), nvWac_unsat, hm_f⟩

/-- Concrete `Mem 64` image for `nvM8VivState` and `nvM8DelayExt` (`e[120] = 0#64` so tier 0
executes and triggers `m6_hdr_bump_delay(h, 4)`). -/
def nvM8VivBumpMem : Mem 64 :=
  storeMem nvM8DelayMem i64 (nvOneLitCfg.hdr + 496) 1#64

theorem nvM8VivBumpMem_ok : FullM6HdrMem nvOneLitCfg nvM8DelayExt nvM8VivState nvM8VivBumpMem := by
  have hm0 : (FullM6HdrMem nvOneLitCfg nvM8DelayExt nvOneLitState ⋆ emp) nvM8DelayMem := by
    rw [sep_emp]; exact nvM8DelayMem_ok
  have h1 := (FullArenaTactics.store_full_num_redundant 1#64 (fullM6HdrMem_focus_full hm0)).2
  have hm' := fullM6HdrMem_unfocus_full h1
  rw [sep_emp] at hm'
  have hst : nvM8VivState =
      { nvOneLitState with core := { nvOneLitState.core with num_redundant := 1#64 } } := by
    simp [nvM8VivState, nvWacState, nvOneLitState, nvOneLitScratch]
  simpa [nvM8VivBumpMem, hst] using hm'

private theorem nvWac_viv_bump_delay4_det {m0 : Mem 64}
    (hm0 : (FullMem nvOneLitCfg nvM8VivState ⋆
      (array64 (nvOneLitCfg.hdr - 2304) (nvM8DelayExt.set 118 1#64) ⋆ emp)) m0) :
    Func.wp waveACoreEnv m6_hdr_bump_delay_body (nvOneLitCfg.hdr, 4#64, ()) m0
      (fun () m4 => FullM6HdrMem nvOneLitCfg
        (((nvM8DelayExt.set 118 1#64).set 124 1#64).set 120 1#64) nvM8VivState m4)
      (fun _ _ _ _ => False) := by
  have hl_d : nvM8DelayExt.length = 288 := nvM8DelayExt_len
  have he124 : (nvM8DelayExt.set 118 1#64)[124]'(by
      rw [List.length_set, hl_d]; decide) = 0#64 := by
    rw [List.getElem_set_ne (by decide : 118 ≠ 124)]
    exact nvM8DelayExt_elem_ne (by decide) (by decide) (by decide) (by decide)
  have hm_e' : (FullM6HdrMem nvOneLitCfg (nvM8DelayExt.set 118 1#64) nvM8VivState ⋆ emp) m0 :=
    (fullM6HdrMem_iff ..).mpr hm0
  have hext118_ok : M6HdrExtOk (nvM8DelayExt.set 118 1#64) :=
    M6HdrExtOk.of_len (by rw [List.length_set, hl_d])
  have hext118_init : M6HdrExtInitOk (nvM8DelayExt.set 118 1#64) :=
    nvM8DelayExt_initOk.set_pos 1#64 (by decide)
  unfold Func.wp m6_hdr_bump_delay_body
  c0_hsteps_nogrp
  wac_call waveACoreEnv_ensureInit
  refine m6ExtEnsureInitSpec_of nvM6HdrCfg_ok hext118_ok
    (nvWac_lengths 1#64 0#64 0#64 0#64 0#64) hm_e' fun ext1 m4 _ hpres1 hm4 => ?_
  obtain rfl : ext1 = nvM8DelayExt.set 118 1#64 := hpres1 hext118_init
  rw [fullM6HdrMem_iff] at hm4
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (cidx, ()) m5 => m5 = m4 ∧ cidx = 124#64)
    ?_ (fun _ hJc => by c0_hsteps; exact hJc (124#64, ()) m4 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m5 ⟨hm5, rfl⟩; subst m5
  refine wp_join_group (ts := [i64]) (fun (nidx, ()) m5 => m5 = m4 ∧ nidx = 120#64)
    ?_ (fun _ hJn => by c0_hsteps; exact hJn (120#64, ()) m4 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m5 ⟨hm5, rfl⟩; subst m5
  have h124_lt : (124#64 : BitVec 64).toNat < (nvM8DelayExt.set 118 1#64).length := by
    rw [List.length_set, hl_d]; decide
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (cap, ()) m5 => m5 = m4 ∧ cap = 8#64)
    ?_ (fun _ hJp => by c0_hsteps; exact hJp (8#64, ()) m4 ⟨rfl, rfl⟩)
  rintro _ ⟨_, ⟨⟩⟩ m5 ⟨hm5, rfl⟩; subst m5
  have h124n : (124 % 2 ^ 64 : Nat) = 124 := rfl
  refine wp_join_group (ts := [i64]) (fun (cur, ()) m5 => m5 = m4 ∧ cur = 1#64)
    ?_ (fun _ hJc => by
      c0_hsteps
      · exact hJc (1#64, ()) m4 ⟨rfl, rfl⟩
      · simp only [h124n, he124] at hc
        exact absurd (by decide : (0#64 : BitVec 64).toNat < 8 % 2 ^ 64) hc)
  rintro _ ⟨_, ⟨⟩⟩ m5 ⟨hm5, rfl⟩; subst m5
  have h120_lt : (120#64 : BitVec 64).toNat <
      ((nvM8DelayExt.set 118 1#64).set 124 1#64).length := by
    rw [List.length_set, List.length_set, hl_d]; decide
  c0_hsteps
  rw [show (124#64 : BitVec 64).toNat = 124 from rfl,
    show (120#64 : BitVec 64).toNat = 120 from rfl] at hm
  have hm_f : (FullM6HdrMem nvOneLitCfg
      (((nvM8DelayExt.set 118 1#64).set 124 1#64).set 120 1#64) nvM8VivState ⋆ emp) m :=
    (fullM6HdrMem_iff nvOneLitCfg
      (((nvM8DelayExt.set 118 1#64).set 124 1#64).set 120 1#64) nvM8VivState emp m).mpr hm
  rw [sep_emp] at hm_f; exact hm_f

/-- Concrete `Mem 64` C0 execution (`nvWacVivBumpEnv`, `XPost := False`) exercising tier-0
vivification (`e[118] = 1#64`), low-yield check (`y * 100 < tried`), and real
`m6_hdr_bump_delay_body(h, 4)`, pinning exact `((nvM8DelayExt.set 118 1#64).set 124 1#64).set 120
1#64` and `nvM8VivState`. -/
theorem nv_m8_vivify_irr_bump :
    Func.wp nvWacVivBumpEnv full_vivify_m6_hdr_body (nvOneLitCfg.hdr, ()) nvM8VivBumpMem
      (fun (r, ()) m' => r = 1#64 ∧
        FullSparseInv nvOneLitCfg nvOneLitF0 nvM8VivState ∧
        M6HdrExtInitOk (((nvM8DelayExt.set 118 1#64).set 124 1#64).set 120 1#64) ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg
          (((nvM8DelayExt.set 118 1#64).set 124 1#64).set 120 1#64) nvM8VivState m')
      (fun _ _ _ _ => False) := by
  have hm_e : (FullM6HdrMem nvOneLitCfg nvM8DelayExt nvM8VivState ⋆ emp) nvM8VivBumpMem := by
    rw [sep_emp]; exact nvM8VivBumpMem_ok
  have hm_s := (fullM6HdrMem_iff ..).mp hm_e
  have hl_d : nvM8DelayExt.length = 288 := nvM8DelayExt_len
  have he118_d : nvM8DelayExt[118]'(by rw [hl_d]; decide) = 0#64 :=
    nvM8DelayExt_elem_ne (by decide) (by decide) (by decide) (by decide)
  unfold Func.wp full_vivify_m6_hdr_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun () m1 => m1 = nvM8VivBumpMem) ?_
    (fun _ hJ1 => by c0_hsteps; exact hJ1 () nvM8VivBumpMem rfl)
  rintro _ ⟨⟩ m1 rfl
  refine LeanQbe.T.wp_call_of_spec _ _ ?_
  refine nvWac_bump_leaf ⟨rfl, ?_⟩
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_call_of_spec _ _ ?_
  refine nvWac_bump_leaf ⟨rfl, ?_⟩
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (_, ()) md => md = nvM8VivBumpMem) ?_
    (fun _ hJd => by c0_hsteps <;> exact hJd (_, ()) nvM8VivBumpMem rfl)
  rintro _ ⟨_, ⟨⟩⟩ md rfl; c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (_, ()) me => me = nvM8VivBumpMem) ?_
    (fun _ hJe => by c0_hsteps <;> exact hJe (_, ()) nvM8VivBumpMem rfl)
  rintro _ ⟨_, ⟨⟩⟩ me rfl; c0_hsteps_nogrp
  · exact absurd hc (by decide)
  refine wp_join_group (ts := [i64, i64])
    (fun (_w1, w2, ()) mw => mw = nvM8VivBumpMem ∧ w2 = 0#64) ?_
    (fun _ hJw => by
      c0_hsteps <;> first | exact hJw (_, 0#64, ()) _ ⟨rfl, rfl⟩ | (exfalso; revert hc; decide))
  rintro _ ⟨_w1, w2, ⟨⟩⟩ mw ⟨hmw, hw2⟩; subst mw hw2; c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (_, ()) ml1 => ml1 = nvM8VivBumpMem) ?_
    (fun _ hJl1 => by c0_hsteps <;> exact hJl1 (_, ()) nvM8VivBumpMem rfl)
  rintro _ ⟨_, ⟨⟩⟩ ml1 rfl
  refine LeanQbe.T.wp_call_of_spec _ _
    (nvWacDetEnv_le_nvWacVivBumpEnv _ _ _ _ _ _ _
      (nvWac_run_tier_det hl_d he118_d 1#64 0xFFFFFFFF#64 _ nvM8VivBumpMem
        hm_s rfl (Or.inl rfl) _ fun m1 hm1 => ?_))
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64, i64])
    (fun (res2, _, ()) mt2 => res2 = 1#64 ∧
      (FullM6HdrMem nvOneLitCfg nvM8DelayExt nvM8VivState ⋆ emp) mt2) ?_
    (fun _ hJt2 => by
      c0_hsteps <;> first | exact hJt2 (1#64, _, ()) _ ⟨rfl, hm1⟩ | (exfalso; revert hc; decide))
  rintro _ ⟨res2, _, ⟨⟩⟩ mt2 ⟨rfl, hmt2⟩; c0_hsteps_nogrp
  refine wp_join_group (ts := [i64, i64])
    (fun (res3, _, ()) mt3 => res3 = 1#64 ∧
      (FullM6HdrMem nvOneLitCfg nvM8DelayExt nvM8VivState ⋆ emp) mt3) ?_
    (fun _ hJt3 => by
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (_, ()) ml3 => ml3 = mt2) ?_
        (fun _ hJl3 => by c0_hsteps <;> exact hJl3 (_, ()) mt2 rfl)
      rintro _ ⟨_, ⟨⟩⟩ ml3 hml3; subst ml3
      refine LeanQbe.T.wp_call_of_spec _ _
        (nvWacDetEnv_le_nvWacVivBumpEnv _ _ _ _ _ _ _
          (nvWac_run_tier_det hl_d he118_d 3#64 0xFFFFFFFF#64 _ mt2
            ((fullM6HdrMem_iff ..).mp hmt2) rfl (Or.inr rfl) _
            fun m2 hm2 => hJt3 (1#64, _, ()) _ ⟨rfl, hm2⟩)))
  rintro _ ⟨res3, _, ⟨⟩⟩ mt3 ⟨rfl, hmt3⟩; c0_hsteps_nogrp
  refine wp_join_group (ts := [i64, i64])
    (fun (res0, _, ()) mt0 => res0 = 1#64 ∧
      (FullM6HdrMem nvOneLitCfg (((nvM8DelayExt.set 118 1#64).set 124 1#64).set 120 1#64)
        nvM8VivState ⋆ emp) mt0) ?_
    (fun _ hJ0 => by
      c0_hsteps
      refine LeanQbe.T.wp_call_of_spec _ _ ?_
      refine Or.inl (Or.inr ?_); dsimp only
      have he120_d : nvM8DelayExt[120]'(by rw [hl_d]; decide) = 0#64 :=
        nvM8DelayExt_elem_ne (by decide) (by decide) (by decide) (by decide)
      have hdel : Func.wp waveACoreEnv m6_hdr_delaying_body (nvOneLitCfg.hdr, 4#64, ()) mt3
          (fun (b, ()) m3 => b = false ∧
            (FullM6HdrMem nvOneLitCfg nvM8DelayExt nvM8VivState ⋆ emp) m3)
          (fun _ _ _ _ => False) := by
        unfold Func.wp m6_hdr_delaying_body
        c0_hsteps_nogrp
        wac_call waveACoreEnv_ensureInit
        refine m6ExtEnsureInitSpec_of nvM6HdrCfg_ok nvM8DelayExt_ok
          (nvWac_lengths 1#64 0#64 0#64 0#64 0#64) hmt3 fun ext1 m3 _ hpres1 hm3 => ?_
        obtain rfl : ext1 = nvM8DelayExt := hpres1 nvM8DelayExt_initOk
        rw [fullM6HdrMem_iff] at hm3
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun (idx, ()) m4 => m4 = m3 ∧ idx = 120#64)
          ?_ (fun _ hJi => by c0_hsteps; exact hJi (120#64, ()) m3 ⟨rfl, rfl⟩)
        rintro _ ⟨_, ⟨⟩⟩ m4 ⟨hm4, rfl⟩; subst m4
        have h120_lt : (120#64 : BitVec 64).toNat < nvM8DelayExt.length := by rw [hl_d]; decide
        have h120m : 120 % 2 ^ 64 = 120 := rfl
        c0_hsteps
        · exfalso; simp only [h120m, he120_d] at hc; revert hc; decide
        · exact ⟨rfl, (fullM6HdrMem_iff ..).mpr hm3⟩
      refine Func.spec_env_mono (fun _ _ _ _ _ _ _ h => Or.inl h) hdel |> fun hw =>
        wp_mono ?_ (fun _ _ _ _ h => h) _ mt3 hw
      rintro ⟨b, ⟨⟩⟩ m3 ⟨rfl, hm3⟩
      have hm3' := (fullM6HdrMem_iff ..).mp hm3
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (_, ()) ml0 => ml0 = m3) ?_
        (fun _ hJl0 => by c0_hsteps <;> exact hJl0 (_, ()) m3 rfl)
      rintro _ ⟨_, ⟨⟩⟩ ml0 hml0; subst ml0; c0_hsteps_nogrp
      refine LeanQbe.T.wp_call_of_spec _ _ ?_
      refine Or.inr ?_; dsimp only
      refine ⟨rfl, rfl, by decide, ?_⟩
      have h118_mod : (944#64 : BitVec 64).toNat % 8 = 0 := by decide
      have h118_lt : (944#64 : BitVec 64).toNat / 8 < nvM8DelayExt.length := by rw [hl_d]; decide
      have hm_t0_f : (FullMem nvOneLitCfg nvM8VivState ⋆
          (array64 (nvOneLitCfg.hdr - 2304) (nvM8DelayExt.set 118 1#64) ⋆ emp))
          (storeMem m3 i64 ((nvOneLitCfg.hdr - 2304) + 944#64) 1#64) := by
        have hm_d := (fullM6HdrMem_iff ..).mp hm3
        have hst := (M6HdrTactics.store_m6Ext_const (k := 944#64) 1#64 hm_d h118_mod h118_lt).2
        simpa [show (944#64 : BitVec 64).toNat / 8 = 118 from rfl] using hst
      have he118 : (nvM8DelayExt.set 118 1#64)[118]'(by
          rw [List.length_set, hl_d]; decide) = 1#64 :=
        List.getElem_set_self (by rw [List.length_set, hl_d]; decide)
      c0_hsteps_nogrp
      simp only [show BitVec.toNat (118 : BitVec 64) = 118 from rfl, he118]
      refine wp_join_group (ts := [])
        (fun () mf => (FullM6HdrMem nvOneLitCfg
          (((nvM8DelayExt.set 118 1#64).set 124 1#64).set 120 1#64) nvM8VivState ⋆ emp) mf) ?_
        (fun _ hJv => by
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun (y, ()) my => y = 0#64 ∧
              my = storeMem m3 i64 ((nvOneLitCfg.hdr - 2304) + 944#64) 1#64) ?_
            (fun _ hJy => by c0_hsteps <;> exact hJy (0#64, ()) _ ⟨rfl, rfl⟩)
          rintro _ ⟨y, ⟨⟩⟩ my ⟨rfl, rfl⟩
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun () mf2 => (FullM6HdrMem nvOneLitCfg
              (((nvM8DelayExt.set 118 1#64).set 124 1#64).set 120 1#64) nvM8VivState ⋆ emp) mf2)
            (fun _ ⟨⟩ mf2 hmf2 => hJv () mf2 hmf2)
            (fun _ hJv2 => by
              c0_hsplit
              · refine LeanQbe.T.wp_call_of_spec _ _ ?_
                refine Or.inl (Or.inr ?_); dsimp only
                refine Func.spec_env_mono (fun _ _ _ _ _ _ _ h => Or.inl h)
                  (nvWac_viv_bump_delay4_det hm_t0_f) |> fun hw =>
                  wp_mono ?_ (fun _ _ _ _ h => h) _ _ hw
                intro () m4 hm4
                c0_hsteps
                exact hJv2 () m4 (by rw [sep_emp]; exact hm4)
              · exfalso
                simp only [show nvM8VivState.scratch.viv_cnt = 0#64 from rfl] at *
                exact absurd (by decide : ((0#64 - 0#64 + 0#64) * 100 : BitVec 64).toNat <
                  (1#64 : BitVec 64).toNat % 2 ^ 64) hc))
      rintro _ ⟨⟩ mf hmf
      c0_hsteps
      exact hJ0 (1#64, _, ()) mf ⟨rfl, hmf⟩)
  rintro _ ⟨res0, _, ⟨⟩⟩ mt0 ⟨rfl, hmt0⟩
  rw [fullM6HdrMem_iff] at hmt0
  c0_hsteps
  have hm_f : (FullM6HdrMem nvOneLitCfg
      (((nvM8DelayExt.set 118 1#64).set 124 1#64).set 120 1#64) nvM8VivState ⋆ emp) m :=
    (fullM6HdrMem_iff nvOneLitCfg
      (((nvM8DelayExt.set 118 1#64).set 124 1#64).set 120 1#64) nvM8VivState emp m).mpr hm
  rw [sep_emp] at hm_f
  exact ⟨rfl, nvWac_sparse_of_fields 1#64 0#64 0#64 0#64,
    ((nvM8DelayExt_initOk.set_pos 1#64 (by decide)).set_pos 1#64 (by decide)).set_pos 1#64
      (by decide), nvWac_unsat, hm_f⟩

/-- Concrete `Mem 64` C0 execution (`nvWacDetEnv`, `XPost := False`) of `m8_eliminate_m6_body`
(`initial := false`) on `nvM8ElimMem` (`unassigned = 1`, `elim_bound = 4`), directly entering
`y * 2000ULL < h->unassigned && h->elim_bound >= 4ULL` and pinning `M8W_BVE_STALL` (`e[128] = 1`),
`M8W_BVE_THROTTLED` (`e[119] = 1`), `eliminations = 1`, and `elim_limit = 1000`. -/
theorem nv_m8_eliminate_throttle :
    Func.wp nvWacDetEnv m8_eliminate_m6_body (nvOneLitCfg.hdr, false, ()) nvM8ElimMem
      (fun (r, ()) m' => r = 1#64 ∧
        FullSparseInv nvOneLitCfg nvOneLitF0 nvM8ElimPostState ∧
        M6HdrExtInitOk ((nvM8DelayExt.set 128 1#64).set 119 1#64) ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ((nvM8DelayExt.set 128 1#64).set 119 1#64) nvM8ElimPostState m')
      (fun _ _ _ _ => False) := by
  have hm0 : (FullMem nvOneLitCfg nvM8ElimState ⋆
      (array64 (nvOneLitCfg.hdr - 2304) nvM8DelayExt ⋆ emp)) nvM8ElimMem := by
    have he : (FullM6HdrMem nvOneLitCfg nvM8DelayExt nvM8ElimState ⋆ emp) nvM8ElimMem := by
      rw [sep_emp]; exact nvM8ElimMem_ok
    exact (fullM6HdrMem_iff nvOneLitCfg nvM8DelayExt nvM8ElimState emp nvM8ElimMem).mp he
  have hl_d : nvM8DelayExt.length = 288 := nvM8DelayExt_len
  let s1 : FullState :=
    { nvM8ElimState with scratch :=
      { nvM8ElimState.scratch with eliminations := 1#64, elim_limit := 500#64 } }
  let s1d : FullState := { s1 with core := { s1.core with dense_mode := 1#64 } }
  have hs1d_den : FullDenseInv nvOneLitCfg nvOneLitF0 s1d :=
    fullDenseInv_with_scratch_keep (nvWac_dense_of_fields 0#64 0#64 1#64 4#64)
      { (nvWac_lengths 0#64 0#64 1#64 1#64 4#64).scratch_ok with
        walk_vals_len := (nvWac_lengths 0#64 0#64 1#64 1#64 4#64).scratch_ok.walk_vals_len } rfl rfl
  have hs1_sp : FullSparseInv nvOneLitCfg nvOneLitF0 s1 :=
    fullSparseInv_of_core_eq_wac (nvWac_sparse_of_fields 0#64 0#64 1#64 4#64)
      ((nvWac_lengths 0#64 0#64 1#64 0#64 4#64).with_scratch
        { (nvWac_lengths 0#64 0#64 1#64 0#64 4#64).scratch_ok with }) rfl ⟨rfl, rfl⟩
  unfold Func.wp m8_eliminate_m6_body
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_call_of_spec _ _ ?_
  refine nvWac_det_leaf ⟨rfl, ?_⟩
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () m1 => (FullMem nvOneLitCfg s1 ⋆
      (array64 (nvOneLitCfg.hdr - 2304) nvM8DelayExt ⋆ emp)) m1) ?_
    (fun _ hJ1 => by
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (arg, ()) ma => arg = 10#64 ∧
          (FullMem nvOneLitCfg { nvM8ElimState with scratch :=
            { nvM8ElimState.scratch with eliminations := 1#64 } } ⋆
            (array64 (nvOneLitCfg.hdr - 2304) nvM8DelayExt ⋆ emp)) ma) ?_
        (fun _ hJa => by
          c0_hsteps <;>
            first | exact hJa (10#64, ()) _ ⟨rfl, hm⟩ | (exfalso; revert hc; decide))
      rintro _ ⟨arg, ⟨⟩⟩ ma ⟨rfl, hma⟩
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_call_of_spec _ _ ?_
      refine nvWac_det_leaf ⟨rfl, ?_⟩
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (ec, ()) me => ec = 1#64 ∧
          (FullMem nvOneLitCfg { nvM8ElimState with scratch :=
            { nvM8ElimState.scratch with eliminations := 1#64 } } ⋆
            (array64 (nvOneLitCfg.hdr - 2304) nvM8DelayExt ⋆ emp)) me) ?_
        (fun _ hJe => by
          c0_hsteps <;>
            first | exact hJe (1#64, ()) _ ⟨rfl, hma⟩ | (exfalso; revert hc; decide))
      rintro _ ⟨ec, ⟨⟩⟩ me ⟨rfl, hme⟩
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_call_of_spec _ _ ?_
      refine nvWac_det_leaf ⟨rfl, ?_⟩
      c0_hsteps
      exact hJ1 () m hm)
  rintro _ ⟨⟩ m1 hm1
  c0_hsteps_nogrp
  have hm_den0 : (FullMem nvOneLitCfg s1d ⋆
      (array64 (nvOneLitCfg.hdr - 2304) nvM8DelayExt ⋆ emp))
      (storeMem m1 i64 (nvOneLitCfg.hdr + 1016) 1#64) :=
    (FullArenaTactics.store_full_dense_mode 1#64 hm1).2
  refine LeanQbe.T.wp_call_of_spec _ _ ?_
  refine nvWac_det_leaf ⟨rfl,
    ⟨s1, array64 (nvOneLitCfg.hdr - 2304) nvM8DelayExt ⋆ emp, hs1_sp, hm1⟩, ?_⟩
  c0_hsteps_nogrp
  { refine wp_join_group (ts := [i64])
      (fun (fbud, ()) mf => mf = storeMem m1 i64 (nvOneLitCfg.hdr + 1016) 1#64 ∧ fbud = 128#64) ?_
      (fun _ hJfb => by
        c0_hsteps <;> first | exact hJfb (128#64, ()) _ ⟨rfl, rfl⟩ | cases hc)
    rintro _ ⟨fbud, ⟨⟩⟩ mf ⟨rfl, rfl⟩
    c0_hsteps_nogrp
    refine LeanQbe.T.wp_call_of_spec _ _ ?_
    refine nvWac_det_leaf ?_
    c0_hsteps_nogrp
    refine LeanQbe.T.wp_call_of_spec _ _ ?_
    refine nvWac_det_leaf ⟨rfl,
      ⟨s1d, array64 (nvOneLitCfg.hdr - 2304) nvM8DelayExt ⋆ emp, hs1d_den, hm_den0⟩, ?_⟩
    c0_hsteps_nogrp
    refine wp_loop_group (ts := [i64])
      (fun rem_t (ti, ()) mt => ti.toNat ≤ 1 ∧ rem_t = 1 - ti.toNat ∧
        (FullMem nvOneLitCfg s1d ⋆ (array64 (nvOneLitCfg.hdr - 2304) nvM8DelayExt ⋆ emp)) mt)
      ?_ (fun _ hLt => by
        c0_hsteps
        exact hLt 1 (0#64, ()) _ ⟨Nat.zero_le _, rfl, hm⟩)
    · rintro Lt _ ⟨ti, ⟨⟩⟩ mt hLt ⟨hti_le, _, hmt⟩
      clear m hm
      c0_hsplit
      · have hcv1 : s1d.core.cur_vars = 1 := rfl
        rw [hcv1] at hc
        have hti0 : ti = 0#64 := by bv_omega
        subst hti0
        have htmk_lt : (0#64 : BitVec 64).toNat < s1d.scratch.tarjan_mark.length := by
          rw [show s1d.scratch.tarjan_mark = [0#32, 0#32] from rfl]; decide
        c0_hsteps
        change (FullMem nvOneLitCfg s1d ⋆
          (array64 (nvOneLitCfg.hdr - 2304) nvM8DelayExt ⋆ emp)) m at hm
        exact hLt 0 (1#64, ()) _ (by omega) ⟨by decide, rfl, hm⟩
      · c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun (blim, ()) mb => mb = mt ∧ blim = 2#64) ?_
          (fun _ hJb => by
            c0_hsteps_nogrp
            refine LeanQbe.T.wp_call_of_spec _ _ ?_
            refine nvWac_det_leaf ?_
            dsimp only [nvWacExtWitness]
            c0_hsteps
            exact hJb (2#64, ()) mt ⟨rfl, rfl⟩)
        rintro _ ⟨blim, ⟨⟩⟩ mb ⟨hmb, rfl⟩
        subst mb
        c0_hsteps_nogrp
        refine LeanQbe.T.wp_call_of_spec _ _ ?_
        refine nvWac_det_leaf ⟨rfl, ?_⟩
        c0_hsteps_nogrp
        let s2d : FullState :=
          { s1d with scratch := { s1d.scratch with elim_limit := 1000#64 } }
        have hs2d_den : FullDenseInv nvOneLitCfg nvOneLitF0 s2d :=
          fullDenseInv_with_scratch_keep hs1d_den
            { hs1d_den.1.lengths.scratch_ok with
              walk_vals_len := hs1d_den.1.lengths.scratch_ok.walk_vals_len } rfl rfl
        refine wp_join_group (ts := [])
          (fun () m4t => (FullMem nvOneLitCfg s2d ⋆
            (array64 (nvOneLitCfg.hdr - 2304) ((nvM8DelayExt.set 128 1#64).set 119 1#64) ⋆ emp))
            m4t) ?_
          (fun _ hJt => by
            have h128_mod : (1024#64 : BitVec 64).toNat % 8 = 0 := by decide
            have h128_lt : (1024#64 : BitVec 64).toNat / 8 < nvM8DelayExt.length := by
              rw [hl_d]; decide
            have h119_mod : (952#64 : BitVec 64).toNat % 8 = 0 := by decide
            have h119_lt : (952#64 : BitVec 64).toNat / 8 <
                (nvM8DelayExt.set 128 1#64).length := by
              rw [List.length_set, hl_d]; decide
            have he128 : nvM8DelayExt[128]'(by rw [hl_d]; decide) = 0#64 :=
              nvM8DelayExt_elem_ne (by decide) (by decide) (by decide) (by decide)
            have he119 : (nvM8DelayExt.set 128 1#64)[119]'(by
                rw [List.length_set, hl_d]; decide) = 0#64 := by
              rw [List.getElem_set_ne (by decide : 128 ≠ 119)]
              exact nvM8DelayExt_elem_ne (by decide) (by decide) (by decide) (by decide)
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun (y, ()) my => my = mt ∧ y = 0#64) ?_
              (fun _ hJy => by
                c0_hsteps <;>
                  simp only [show s1d.core.unassigned = 1#64 from rfl] at * <;>
                  first | (exfalso; revert hc; decide) | exact hJy (0#64, ()) mt ⟨rfl, rfl⟩)
            rintro _ ⟨y, ⟨⟩⟩ my ⟨hmy, rfl⟩
            subst my
            c0_hsteps_nogrp
            refine wp_join_group (ts := [])
              (fun () m_x => (FullMem nvOneLitCfg s2d ⋆ (array64 (nvOneLitCfg.hdr - 2304)
                ((nvM8DelayExt.set 128 1#64).set 119 1#64) ⋆ emp)) m_x)
              (by rintro _ ⟨⟩ m_x hm_x; c0_hsteps; exact hJt () m_x hm_x)
              (fun _ hJx => by
                c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun () _ => False)
                  (by rintro _ ⟨⟩ _ h; exact False.elim h)
                  (fun _ _hJo => by
                    c0_hsteps_nogrp
                    · refine wp_join_group (ts := [i64])
                        (fun (st, ()) m_st => m_st = mt ∧ st = 1#64) ?_
                        (fun _ hJst => by
                          repeat clear hc
                          c0_hsteps <;>
                            simp only [show BitVec.toNat (128 : BitVec 64) = 128 from rfl,
                              he128] at * <;>
                            first
                            | exact hJst (1#64, ()) mt ⟨rfl, rfl⟩
                            | (exfalso; revert hc; decide))
                      rintro _ ⟨st, ⟨⟩⟩ m_st ⟨hmst, rfl⟩
                      subst m_st
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [i64])
                        (fun (base_d, ()) m_bd => base_d = 500#64 ∧
                          (FullMem nvOneLitCfg s1d ⋆ (array64 (nvOneLitCfg.hdr - 2304)
                            (nvM8DelayExt.set 128 1#64) ⋆ emp)) m_bd) ?_
                        (fun _ hJbd => by
                          repeat clear hc
                          have h128eq : (1024#64 : BitVec 64).toNat / 8 = 128 := rfl
                          c0_hsteps <;>
                            simp only [show s1d.scratch.elim_limit = 500#64 from rfl,
                              show s1d.scratch.conflicts = 0#64 from rfl, h128eq] at *
                          · exact hJbd (500#64, ()) _ ⟨rfl, hm⟩
                          · exfalso; revert hc; decide)
                      rintro _ ⟨base_d, ⟨⟩⟩ m_bd ⟨rfl, hm_bd⟩
                      clear m hm
                      c0_hsteps
                      simp only [show BitVec.toNat (119 : BitVec 64) = 119 from rfl, he119,
                        show s1d.scratch.conflicts = 0#64 from rfl] at hm
                      change (FullMem nvOneLitCfg s2d ⋆ (array64 (nvOneLitCfg.hdr - 2304)
                        ((nvM8DelayExt.set 128 1#64).set 119 1#64) ⋆ emp)) m at hm
                      exact hJx () _ hm
                    all_goals
                      exfalso
                      simp only [show s1d.core.unassigned = 1#64 from rfl,
                        show s1d.scratch.elim_bound = 4#64 from rfl] at *
                      bv_omega)))
        rintro _ ⟨⟩ m4t hm4t
        have hm_post0 : (FullMem nvOneLitCfg nvM8ElimPostState ⋆ (array64 (nvOneLitCfg.hdr - 2304)
            ((nvM8DelayExt.set 128 1#64).set 119 1#64) ⋆ emp))
            (storeMem m4t i64 (nvOneLitCfg.hdr + 1016) 0#64) := by
          have h1 := (FullArenaTactics.store_full_dense_mode 0#64 hm4t).2
          simpa [show nvM8ElimPostState = { s2d with core := { s2d.core with dense_mode := 0#64 } }
            from by simp [nvM8ElimPostState, s2d, s1d, s1, nvM8ElimState, nvWacState,
              nvOneLitState, nvOneLitScratch]] using h1
        refine LeanQbe.T.wp_call_of_spec _ _ ?_
        refine nvWac_det_leaf ⟨rfl,
          ⟨s2d, array64 (nvOneLitCfg.hdr - 2304) ((nvM8DelayExt.set 128 1#64).set 119 1#64) ⋆ emp,
            hs2d_den, hm4t⟩, ?_⟩
        c0_hsteps
        change (FullMem nvOneLitCfg nvM8ElimPostState ⋆ (array64 (nvOneLitCfg.hdr - 2304)
          ((nvM8DelayExt.set 128 1#64).set 119 1#64) ⋆ emp)) m at hm
        have hsp_post : FullSparseInv nvOneLitCfg nvOneLitF0 nvM8ElimPostState :=
          fullSparseInv_of_core_eq_wac (nvWac_sparse_of_fields 0#64 0#64 1#64 4#64)
            ((nvWac_lengths 0#64 0#64 1#64 0#64 4#64).with_scratch
              { (nvWac_lengths 0#64 0#64 1#64 0#64 4#64).scratch_ok with }) rfl ⟨rfl, rfl⟩
        have hm_f : (FullM6HdrMem nvOneLitCfg ((nvM8DelayExt.set 128 1#64).set 119 1#64)
            nvM8ElimPostState ⋆ emp) m :=
          (fullM6HdrMem_iff nvOneLitCfg ((nvM8DelayExt.set 128 1#64).set 119 1#64)
            nvM8ElimPostState emp m).mpr hm
        rw [sep_emp] at hm_f
        exact ⟨rfl, hsp_post,
          (nvM8DelayExt_initOk.set_pos 1#64 (by decide)).set_pos 1#64 (by decide), nvWac_unsat,
          hm_f⟩ }
  cases hc

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM8WaveACore

end
