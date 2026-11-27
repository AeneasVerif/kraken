/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3SearchRestart
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Spec
public import LeanQbe.T.Examples.Kissat.DimacsLemmas1
public import LeanQbe.T.Examples.Kissat.FullM4Proof1
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Examples.Kissat.FullM4CompactLemmas
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Fidelity Step 13 Shard S3-B Proofs — Part 2 (`FullFidelityStep13S3SearchRestartProof2`)

Callee-parametric (`Γ : Env`, `XPost := False`, `0` SAT model proofs, `0` `Step7..12`
back-imports) `Func.wp` proofs for the final `4` top-level search & entrypoint functions in
`FullFidelityStep13S3SearchRestart`:
1. `full_search_m6_step13_wp` (`FullM6.fullM6SearchSpec`)
2. `kissat_solve_bytes_seeded_step13_wp` (`step13SolveBytesSeededSpec`)
3. `kissat_solve_bytes_m6_step13_wp` (`step13SolveBytesSpec`)
4. `kissat_solve_bytes_step13_wp` (`step13SolveBytesSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open Kraken.Bedrock2.Test
open scoped FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

/-! ## 1. Search Variant & Call Helpers (`SearchStep13`) -/

section SearchStep13

abbrev EnvSpec (Γ : Env) (nm : String) {as rs : List Ty} (sp : Spec as rs) : Prop :=
  ∀ a m Q X, sp a m Q X → Γ nm as rs a m Q X

private def sr2SearchVariant (c : FullCfg) (s : FullState) : Nat :=
  (c.max_vars + 1) * s.core.fuel.toNat + (c.max_vars - s.core.trail_end)

private theorem sr2_variant_dec {c c' : FullCfg} {s s1 s' : FullState}
    (hmveq : c'.max_vars = c.max_vars) (hfu_pos : 0 < s.core.fuel.toNat)
    (hfu_lt : s1.core.fuel.toNat < s.core.fuel.toNat)
    (hfu_le : s'.core.fuel.toNat ≤ s1.core.fuel.toNat)
    (hle_te' : s'.core.trail_end ≤ c'.max_vars) :
    sr2SearchVariant c' s' < sr2SearchVariant c s := by
  unfold sr2SearchVariant; rw [hmveq]
  have h1 : s'.core.fuel.toNat ≤ s.core.fuel.toNat - 1 := by omega
  have hmul : (c.max_vars + 1) * s'.core.fuel.toNat ≤
      (c.max_vars + 1) * (s.core.fuel.toNat - 1) :=
    Nat.mul_le_mul_left (c.max_vars + 1) h1
  have hs_mul : (c.max_vars + 1) * s.core.fuel.toNat =
      (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := by
    have hsub : s.core.fuel.toNat - 1 + 1 = s.core.fuel.toNat := by omega
    calc (c.max_vars + 1) * s.core.fuel.toNat
        = (c.max_vars + 1) * (s.core.fuel.toNat - 1 + 1) := by rw [hsub]
      _ = (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := Nat.mul_succ _ _
  omega

private theorem sr2_variant_dec_fuel {c c' : FullCfg} {s s1 s' : FullState}
    (hmveq : c'.max_vars = c.max_vars) (hfu_pos : 0 < s.core.fuel.toNat)
    (hfu1_pos : 0 < s1.core.fuel.toNat) (hfu1_le : s1.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hfu_le : s'.core.fuel.toNat ≤ s1.core.fuel.toNat - 1)
    (hle_te' : s'.core.trail_end ≤ c'.max_vars) :
    sr2SearchVariant c' s' < sr2SearchVariant c s := by
  unfold sr2SearchVariant; rw [hmveq]
  have h1 : s'.core.fuel.toNat ≤ s.core.fuel.toNat - 1 := by omega
  have hmul : (c.max_vars + 1) * s'.core.fuel.toNat ≤
      (c.max_vars + 1) * (s.core.fuel.toNat - 1) :=
    Nat.mul_le_mul_left (c.max_vars + 1) h1
  have hs_mul : (c.max_vars + 1) * s.core.fuel.toNat =
      (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := by
    have hsub : s.core.fuel.toNat - 1 + 1 = s.core.fuel.toNat := by omega
    calc (c.max_vars + 1) * s.core.fuel.toNat
        = (c.max_vars + 1) * (s.core.fuel.toNat - 1 + 1) := by rw [hsub]
      _ = (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := Nat.mul_succ _ _
  omega

private theorem sr2_upd_fuel_m6Inv {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (hinv : FullM6HdrInv c F0 ext s) (f' : BitVec 64) :
    FullM6HdrInv c F0 ext { s with core := { s.core with fuel := f' } } :=
  FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk
    (FullSparseInv.with_fuel_scratch hinv.sparse
      ⟨{ hinv.sparse.lengths.core_ok with vals_len := hinv.sparse.lengths.core_ok.vals_len },
       hinv.sparse.lengths.scratch_ok⟩ rfl ⟨rfl, rfl⟩)

private theorem sr2_upd_fuel_m6InvW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (f' : BitVec 64) :
    FullM6HdrInvW c F0 F_cur ext { s with core := { s.core with fuel := f' } } :=
  FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
    ⟨⟨{ hinv.sparseW.1.core_ok with vals_len := hinv.sparseW.1.core_ok.vals_len },
       hinv.sparseW.1.scratch_ok⟩,
     { hinv.sparseW.2.1 with
       arena := { hinv.sparseW.2.1.arena with len_ok := hinv.sparseW.2.1.arena.len_ok }
       watches := hinv.sparseW.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
     hinv.sparseW.2.2.1, hinv.sparseW.2.2.2.1, hinv.sparseW.2.2.2.2.1,
     hinv.sparseW.2.2.2.2.2⟩

private theorem sr2_call_bcp {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "full_propagate" step13BcpM6Spec)
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext' s' → FullTrailExt s.core s'.core →
      FullArenaPermEq s.core s'.core → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hΓ _ _ _ X ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hm,
    fun r ext' s' m' hinv' htr' hperm' _ hfu' hdom hr1 hm' =>
      hk r ext' s' m' hinv' htr' hperm' hfu' hdom hr1 hm'⟩

private theorem sr2_call_analyze {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "full_analyze_m6_hdr" m6HdrAnalyzeSpec)
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hcok : FullConflictOkW F_cur s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInvW c F0 F_cur ext' s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_analyze_m6_hdr" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hΓ _ _ _ X (m6HdrAnalyzeSpec_of hinv hcok hm
    fun r ext' s' m' hext' hlen' hr _ hfu _ hu _ h1 hm' =>
      hk r ext' s' m' hext' hlen' hr hfu hu h1 hm')

private theorem sr2_call_reduce {Γ : Env} {force : Bool} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, force, ()))
    (hΓ : EnvSpec Γ "full_reduce_m6" m6ReduceSpec)
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_reduce_m6" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hΓ _ _ _ X (m6ReduceSpec_of hinv hm fun r ext' s' m' hinv' hr _ hfu _ _ _ _ hu _ _ hm' =>
    hk r ext' s' m' hinv' hr hfu hu hm')

private theorem sr2_call_switchMode {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "full_switch_mode_m7" step13SwitchModeM6Spec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext' s' → s'.core = s.core →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_switch_mode_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hΓ _ _ _ X ⟨c, ext, s, R, rfl, hinv.cfgOk, hinv.extOk, hinv.sparse.lengths, hm,
    fun ext' s' m' hc' hl' hp' hext' hm' => ?_⟩
  exact hk ext' s' m' (fullM6HdrInv_with_ext (fullM6HdrInv_of_core_eq hinv hl' hc' hp'.1) hext')
    hc' hm'

private theorem sr2_call_restartDue {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "full_restart_due" Full.fullRestartDueSpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core = s.core →
      (r = 0#64 ∨ r = 1#64) → (FullM6HdrMem c ext s' ⋆ R) m' →
      wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_restart_due" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hΓ _ _ _ X ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse.lengths,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  rintro ⟨r, ⟨⟩⟩ s' m' hcore hlen ⟨hdom, hpres⟩ hm'
  have hceq : s'.core = s.core := @Full.fullCoreState_agrees_with_scratch c s s' hcore
  exact hk r s' m' (fullM6HdrInv_of_core_eq hinv hlen hceq hpres) hceq hdom
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem sr2_call_restart {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "full_restart" Full.fullRestartSpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.cur_level ≤ s.core.cur_level →
      s'.core.fuel = s.core.fuel → (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_restart" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  have hsp := hinv.sparse; have hcore := fullM6HdrInv_to_coreInv hinv
  refine hΓ _ _ _ X ⟨c, F0, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hcore.coreInv,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s' hc' hcl' hpres' hm'
  have hinv' := FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk ⟨hc', ⟨hsp.2.1.1, hsp.2.1.2⟩,
    hsp.2.2.1, ⟨hsp.2.2.2.1.1.of_refs_subset hpres'.1 fun _ hr => hr,
      by change sc'.extend_len ≤ c.extend_cap; rw [hpres'.2]; exact hsp.2.2.2.1.2⟩,
    hsp.2.2.2.2⟩
  exact hk s' m' hinv' hcl' rfl ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem sr2_call_reorder {Γ : Env} {budget : BitVec 64} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, budget, ()))
    (hΓ : EnvSpec Γ "full_reorder_m6" m4ReorderSpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.fuel = s.core.fuel →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_reorder_m6" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hΓ _ _ _ X ⟨c, F0, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r s' m' hsp' _ _ hfu' hm'
  exact hk r s' m' (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hfu'
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem sr2_call_rephase {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "full_rephase" step13RephaseM6Spec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext' s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_rephase" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hΓ _ _ _ X ⟨c, F0, ext, s, R, rfl, hinv, hm,
    fun ext' s' m' hinv' _ _ _ hfu' _ hm' => hk ext' s' m' hinv' hfu' hm'⟩

private theorem sr2_call_simplify {Γ : Env} {dp de : Bool} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, dp, de, ()))
    (hΓ : EnvSpec Γ "full_simplify_m6" fullM6SimplifySpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (c' : FullCfg) (ext' : List (BitVec 64)) (s' : FullState)
      (m' : Mem 64),
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_simplify_m6" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hΓ _ _ _ X (fullM6SimplifySpec_of hinv hm hk)

private theorem sr2_call_decideFid {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : EnvSpec Γ "m6_hdr_decide_fid" m6HdrDecideSpec)
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext' s' → (r = 0#64 ∨ r = 1#64) → s'.core.fuel = s.core.fuel →
      (r = 0#64 → s'.core.cur_level = s.core.cur_level ∧ s'.core.trail_end = s.core.trail_end) →
      (r = 1#64 → s'.core.cur_level = s.core.cur_level + 1 ∧
        s'.core.trail_end = s.core.trail_end + 1) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "m6_hdr_decide_fid" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  have hsp := hinv.sparse; have hcore := fullM6HdrInv_to_coreInv hinv
  refine hΓ _ _ _ X (m6HdrDecideSpec_of hcore hm ?_)
  intro r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' ext' m' s'
    hcore' hpres' hdom h0 h1 hm'
  have hinv' := FullM6HdrInv.mk_inv hcore'.cfgOk hcore'.extOk ⟨hcore'.coreInv,
    ⟨hsp.2.1.1, hsp.2.1.2⟩, hsp.2.2.1,
    ⟨hsp.2.2.2.1.1.of_refs_subset hpres'.1 fun _ hr => hr,
      by change sc'.extend_len ≤ c.extend_cap; rw [hpres'.2]; exact hsp.2.2.2.1.2⟩,
    hsp.2.2.2.2⟩
  exact hk r ext' s' m' hinv' hdom rfl h0 (fun hr1 => ⟨(h1 hr1).1, (h1 hr1).2.1⟩) hm'

private theorem sr2_search_simplify_cont {Γ : Env} {c0 c : FullCfg} {F0 : CNF Nat}
    {s s1 s2 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {sr : BitVec 64} {c3 : FullCfg} {ext3 : List (BitVec 64)} {s3 : FullState} {m3 : Mem 64}
    {cont : Expr Val Cont [i64]}
    (hcompat : FullCfgCompat c0 c) (hcomp3 : FullCfgCompat c c3)
    (hlen3 : s3.LengthsOk c3) (hcfg3 : FullM6HdrCfgOk c3) (hext3 : M6HdrExtOk ext3)
    (hcore2 : s2.core = s1.core)
    (hfu_pos : 0 < s.core.fuel.toNat) (hfu1_pos : 0 < s1.core.fuel.toNat)
    (hfu1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hfu1_pred : (s1.core.fuel - 1#64).toNat = s1.core.fuel.toNat - 1)
    (hfu3 : s3.core.fuel.toNat ≤ (s2.core.fuel - 1#64).toNat)
    (hu3 : sr = 20#64 → F0.Unsat)
    (hs1 : sr = 1#64 → FullM6HdrInv c3 F0 ext3 s3 ∧ s3.core.cur_level = 0)
    (hm3 : (FullM6HdrMem c3 ext3 s3 ⋆ R) m3)
    (hQ : ∀ (r : BitVec 64) (c' : FullCfg) (ext' : List (BitVec 64)) (s' : FullState)
        (m' : Mem 64),
      FullCfgCompat c0 c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m')
    (hcont : FullM6HdrInv c3 F0 ext3 s3 → sr2SearchVariant c3 s3 < sr2SearchVariant c s →
      wp Γ Q X cont m3) :
    wp Γ Q X
      (.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var sr, Arg.imm 20, ())) fun p =>
        .jnz (Arg.var p.fst) (.ret (Arg.imm 20, ()))
          (.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var sr, Arg.imm 1, ())) fun p1 =>
            .jnz (Arg.var p1.fst) (.ret (Arg.imm 0, ())) cont)) m3 := by
  have hcompat3 := hcompat.trans hcomp3
  c0_hsteps_nogrp
  · exact hQ 20#64 c3 ext3 s3 m3 hcompat3 hlen3 hcfg3 hext3
      (Or.inr (Or.inr rfl)) (fun _ => hu3 hc) (fun hc => by cases hc) hm3
  · exact hQ 0#64 c3 ext3 s3 m3 hcompat3 hlen3 hcfg3 hext3
      (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm3
  · obtain ⟨hinv3, _⟩ := hs1 hc
    rw [hcore2, hfu1_pred] at hfu3
    exact hcont hinv3 (sr2_variant_dec_fuel hcomp3.max_vars hfu_pos hfu1_pos hfu1 hfu3
      (Nat.le_trans hinv3.sparse.lengths.core_ok.trail_end_le
        hinv3.sparse.lengths.core_ok.cur_vars_le))

end SearchStep13

/-! ## 2. `full_search_m6` (`FullM6.fullM6SearchSpec`) -/

/-- Step-13 `full_search_m6` (calling `full_update_classify_fid` before `m6_hdr_set_watermark`
and Option-A `FullM6HdrMem`-threaded callees) satisfies `FullM6.fullM6SearchSpec`. -/
theorem full_search_m6_step13_wp (Γ : Env)
    (hLuckyLate : EnvSpec Γ "full_lucky_late_m7" step13LuckyLateM6Spec)
    (hClassify : EnvSpec Γ "full_update_classify_fid" (m6HdrW2aSpec [] []))
    (hSetWm : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hProp : EnvSpec Γ "full_propagate" step13BcpM6Spec)
    (hAnalyze : EnvSpec Γ "full_analyze_m6_hdr" m6HdrAnalyzeSpec)
    (hReduce : EnvSpec Γ "full_reduce_m6" m6ReduceSpec)
    (hSwitch : EnvSpec Γ "full_switch_mode_m7" step13SwitchModeM6Spec)
    (hRstDue : EnvSpec Γ "full_restart_due" Full.fullRestartDueSpec)
    (hRst : EnvSpec Γ "full_restart" Full.fullRestartSpec)
    (hReorder : EnvSpec Γ "full_reorder_m6" m4ReorderSpec)
    (hRephase : EnvSpec Γ "full_rephase" step13RephaseM6Spec)
    (hSimplify : EnvSpec Γ "full_simplify_m6" fullM6SimplifySpec)
    (hDecideFid : EnvSpec Γ "m6_hdr_decide_fid" m6HdrDecideSpec) :
    ∀ a m Q X, fullM6SearchSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_search_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6SearchSpec_elim hs with ⟨c0, F0, ext0, s0, R, rfl, hinv0, _, hm0, hQ⟩
  unfold Func.wp FullFidelityStep13S3.full_search_m6_body; dsimp only
  c0_hsteps_nogrp; c0_call hLuckyLate
  refine ⟨c0, F0, ext0, s0, R, rfl, hinv0, hm0,
    fun lr extL sL mL hlenL hextL hdomL _ _ huL hinvL h10L hmL => ?_⟩
  c0_hsteps_nogrp
  · have hl := hc; rw [hl]
    exact hQ 10#64 c0 extL sL mL (FullCfgCompat.refl c0) hlenL hinv0.cfgOk hextL
      (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ => h10L hl) hmL
  · have hl := hc; rw [hl]
    exact hQ 20#64 c0 extL sL mL (FullCfgCompat.refl c0) hlenL hinv0.cfgOk hextL
      (Or.inr (Or.inr rfl)) (fun _ => huL hl) (fun h => by cases h) hmL
  · have hlkr02 : lr = 0#64 ∨ lr = 2#64 := by
      rcases hdomL with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl (by assumption)
      · exact absurd rfl hc
    have hinv_lk := (hinvL hlkr02).1
    refine wp_m6Hdr_focus_frame hmL fun hmLf => ?_
    c0_hsteps_nogrp
    let sL1 : FullState :=
      { sL with scratch := { sL.scratch with search_ticks := 0#64, mode_saved_ticks := 0#64 } }
    have hspL1 : FullSparseInv c0 F0 sL1 :=
      FullSparseInv.with_fuel_scratch hinv_lk.sparse
        ⟨hinv_lk.sparse.lengths.core_ok, { hinv_lk.sparse.lengths.scratch_ok with }⟩ rfl ⟨rfl, rfl⟩
    have hinvL1 := FullM6HdrInv.mk_inv hinv_lk.cfgOk hinv_lk.extOk hspL1
    refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hClassify _ _ _ _ h)
      hinvL1.cfgOk hinvL1.extOk hinvL1.sparse.lengths (fullM6HdrMem_unfocus (by assumption))
      fun _ extC sC mC hcC hlC hmsC hextC _ hmC => ?_
    have hinvC := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinvL1 hlC hcC hmsC) hextC
    c0_hsteps_nogrp
    refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h)
      hinvC.cfgOk hinvC.extOk hinvC.sparse.lengths hmC
      fun _ extL2 sL2 mL2 hcL2 hlL2 hmsL2 hextL2 _ hmL2 => ?_
    have hinvL2 := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinvC hlL2 hcL2 hmsL2) hextL2
    refine wp_m6Hdr_focus_frame hmL2 fun hmL2f => ?_
    c0_hsteps_nogrp
    let sL3 : FullState := { sL2 with scratch := { sL2.scratch with fwd_str_cnt := 0#64 } }
    have hspL3 : FullSparseInv c0 F0 sL3 :=
      FullSparseInv.with_fuel_scratch hinvL2.sparse
        ⟨hinvL2.sparse.lengths.core_ok, { hinvL2.sparse.lengths.scratch_ok with }⟩ rfl ⟨rfl, rfl⟩
    have hinvL3 := FullM6HdrInv.mk_inv hinvL2.cfgOk hinvL2.extOk hspL3
    have hmL3 : (FullM6HdrMem c0 extL2 sL3 ⋆ R) _ := fullM6HdrMem_unfocus (by assumption)
    clear_value sL3
    clear hspL3 hinvL2 hcL2 hlL2 hmsL2 hextL2 hinvC hcC hlC hmsC hextC hinvL1 hspL1 sL1 hinv_lk
    refine wp_while_state (ts := [i64, i64, i64])
        (α := BitVec 64 × BitVec 64 × BitVec 64 × FullCfg × List (BitVec 64) × FullState)
        (fun ⟨rlim, reord, lrc, _, _, _⟩ => (rlim, reord, lrc, ()))
        (fun ⟨_, _, _, c, _, s⟩ => sr2SearchVariant c s)
        (fun ⟨_, _, _, c, ext, s⟩ ml =>
          FullCfgCompat c0 c ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) ml)
        (fun J hJ => by
          c0_hsteps
          exact hJ (10000#64, 0#64, 0xFFFFFFFFFFFFFFFF#64, c0, extL2, sL3) _
            ⟨FullCfgCompat.refl c0, hinvL3, hmL3⟩)
        ?_
    rintro J ⟨rlim, reord, last_red, c, ext, s⟩ ml ⟨hcompat, hinv, hml⟩ ih
    rw [← hcompat.hdr]
    have hsp := hinv.sparse; have hlen := hsp.lengths
    have hmx := c.hmaxv; unfold LratBytes.dimacsBound at hmx
    have hml_f := fullM6HdrMem_focus hml
    c0_hsplit; rotate_left; · cases hc
    c0_hsteps
    · exact hQ 0#64 c ext s ml hcompat hlen hinv.cfgOk hinv.extOk (Or.inl rfl)
        (fun hc => by cases hc) (fun hc => by cases hc) hml
    · exact hQ 0#64 c ext s ml hcompat hlen hinv.cfgOk hinv.extOk (Or.inl rfl)
        (fun hc => by cases hc) (fun hc => by cases hc) hml
    · have hfu_pos : 0 < s.core.fuel.toNat := by
        have hpos : s.core.fuel.toNat ≠ 0 :=
          fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
        omega
      obtain ⟨F_cur, hinvW⟩ := fullM6HdrInv_exists_witness hinv
      refine sr2_call_bcp rfl hProp hinvW hml ?_
      intro pr ext1 s1 m1 hinvW1 htr1 _ hfu1 hdom1 hr1 hm1
      have hinv1 := hinvW1.toInv; have hlen1 := hinv1.sparse.lengths
      have hm1_f := fullM6HdrMem_focus hm1
      c0_hsteps_nogrp
      · exact hQ 0#64 c ext1 s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inl rfl)
          (fun hc => by cases hc) (fun hc => by cases hc) hm1
      · c0_hstep; c0_hsteps_nogrp
        · obtain ⟨hfu_lt, _, hcok1⟩ := hr1 hc
          refine sr2_call_analyze rfl hAnalyze hinvW1 hcok1 hm1 ?_
          intro ast ext2 s2 m2 hext2 hlen2 hast hfu2 hu2 ha1 hm2
          c0_hsteps
          · exact hQ 20#64 c ext2 s2 m2 hcompat hlen2 hinv1.cfgOk hext2 (Or.inr (Or.inr rfl))
              (fun _ => hu2 hc) (fun hc => by cases hc) hm2
          · exact hQ 0#64 c ext2 s2 m2 hcompat hlen2 hinv1.cfgOk hext2 (Or.inl rfl)
              (fun hc => by cases hc) (fun hc => by cases hc) hm2
          · exact ih (rlim, reord, last_red, c, ext2, s2) m2
              (sr2_variant_dec rfl hfu_pos hfu_lt hfu2 (Nat.le_trans hlen2.core_ok.trail_end_le
                hlen2.core_ok.cur_vars_le))
              ⟨hcompat, (ha1 hc).1.toInv, hm2⟩
        · exact hQ 10#64 c ext1 s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inr (Or.inl rfl))
            (fun hc => by cases hc) (fun _ => hinv1.sparse.2.2.2.1.2) hm1
        · exact hQ 0#64 c ext1 s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inl rfl)
            (fun hc => by cases hc) (fun hc => by cases hc) hm1
        · have hfu1_pos : 0 < s1.core.fuel.toNat :=
            Nat.pos_of_ne_zero fun h0 => ‹s1.core.fuel ≠ 0#64›
              (BitVec.eq_of_toNat_eq (by simpa using h0))
          have hfu1_pred : (s1.core.fuel - 1#64).toNat = s1.core.fuel.toNat - 1 := by c0_bound
          have hmu_rare : ∀ {c' : FullCfg} {ext' : List (BitVec 64)} {s' : FullState},
              c'.max_vars = c.max_vars → s'.core.fuel.toNat ≤ s1.core.fuel.toNat - 1 →
              FullM6HdrInv c' F0 ext' s' → sr2SearchVariant c' s' < sr2SearchVariant c s :=
            fun hmveq hfule hinv' =>
              sr2_variant_dec_fuel hmveq hfu_pos hfu1_pos hfu1 hfule
                (Nat.le_trans hinv'.sparse.lengths.core_ok.trail_end_le
                  hinv'.sparse.lengths.core_ok.cur_vars_le)
          c0_hstep; c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun _ mred => (FullM6HdrMem c ext1 s1 ⋆ R) mred) ?_
            (fun _ hJred => by
              have hm1_f' := fullM6HdrMem_focus hm1
              c0_hsteps_nogrp
              · have hinvW1r := sr2_upd_fuel_m6InvW hinvW1 (s1.core.fuel - 1#64)
                refine sr2_call_reduce rfl hReduce hinvW1r (fullM6HdrMem_unfocus (by assumption)) ?_
                intro rr ext3 s3 m3 hinvW3 _ hfu3 hu3 hm3
                dsimp only at hfu3
                have hinv3 := hinvW3.toInv; have hlen3 := hinv3.sparse.lengths
                c0_hsteps!
                · exact hQ 20#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                    (Or.inr (Or.inr rfl)) (fun _ => hu3 hc) (fun hc => by cases hc) hm3
                · exact hQ 0#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                    (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm3
                · exact ih (rlim, reord, s1.scratch.conflicts, c, ext3, s3) m3
                    (hmu_rare rfl (by rw [hfu1_pred] at hfu3; exact hfu3) hinv3)
                    ⟨hcompat, hinv3, hm3⟩
              · exact hJred () m1 hm1
              · exact hJred () m1 hm1)
          rintro _ _ m1' hm1'
          have hm1_f := fullM6HdrMem_focus hm1'
          c0_hstep; c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
            (fun x => (x, ())) (fun _ => True) ?_
            (fun _ hJmd => by c0_hsteps <;> exact hJmd _ trivial)
          intro _ _ _
          c0_hsplit
          · c0_hsteps
            have hinv1m := sr2_upd_fuel_m6Inv hinv1 (s1.core.fuel - 1#64)
            refine sr2_call_switchMode rfl hSwitch hinv1m
              (fullM6HdrMem_unfocus (by assumption)) ?_
            intro ext2 s2 m2 hinv2 hcore2 hm2
            dsimp only at hcore2; c0_hsteps!
            exact ih (rlim, reord, last_red, c, ext2, s2) m2
              (hmu_rare rfl (by rw [hcore2, hfu1_pred]; exact le_refl _) hinv2)
              ⟨hcompat, hinv2, hm2⟩
          · c0_hstep; c0_hsteps_nogrp
            refine sr2_call_restartDue rfl hRstDue hinv1
              (fullM6HdrMem_unfocus (by assumption)) ?_
            intro rdu s2 m2 hinv2 hcore2 _ hm2
            have hm2_f := fullM6HdrMem_focus hm2
            c0_hsplit
            · c0_hsteps
              have hinv2r := sr2_upd_fuel_m6Inv hinv2 (s2.core.fuel - 1#64)
              refine sr2_call_restart rfl hRst hinv2r (fullM6HdrMem_unfocus (by assumption)) ?_
              intro s3 m3 hinv3 _ hfu3 hm3
              dsimp only at hfu3; c0_hsteps!
              exact ih (rlim, reord, last_red, c, ext1, s3) m3
                (hmu_rare rfl (by rw [hfu3, hcore2, hfu1_pred]; exact le_refl _) hinv3)
                ⟨hcompat, hinv3, hm3⟩
            · c0_hstep; c0_hsteps_nogrp
              refine wp_join_group (ts := []) (fun _ mr => (FullM6HdrMem c ext1 s2 ⋆ R) mr) ?_
                (fun _ hJr => by
                  have hm2_f' := fullM6HdrMem_focus hm2
                  c0_hsteps_nogrp
                  · have hinv2o := sr2_upd_fuel_m6Inv hinv2 (s2.core.fuel - 1#64)
                    refine sr2_call_reorder rfl hReorder hinv2o
                      (fullM6HdrMem_unfocus (by assumption)) ?_
                    intro _ s3 m3 hinv3 hfu3 hm3
                    dsimp only at hfu3; c0_hsteps!
                    exact ih (s2.scratch.conflicts + 10000#64 * (reord + 1#64), reord + 1#64,
                        last_red, c, ext1, s3) m3
                      (hmu_rare rfl (by rw [hfu3, hcore2, hfu1_pred]; exact le_refl _) hinv3)
                      ⟨hcompat, hinv3, hm3⟩
                  · exact hJr () m2 hm2
                  · exact hJr () m2 hm2)
              rintro _ _ mr hmr; c0_hstep
              refine wp_join_group (ts := []) (fun _ mp => (FullM6HdrMem c ext1 s2 ⋆ R) mp) ?_
                (fun _ hJp => by
                  have hm_f := fullM6HdrMem_focus hmr
                  c0_hsteps_nogrp
                  · have hinv2p := sr2_upd_fuel_m6Inv hinv2 (s2.core.fuel - 1#64)
                    refine sr2_call_rephase rfl hRephase hinv2p
                      (fullM6HdrMem_unfocus (by assumption)) ?_
                    intro ext3 s3 m3 hinv3 hfu3 hm3
                    dsimp only at hfu3; c0_hsteps!
                    exact ih (rlim, reord, last_red, c, ext3, s3) m3
                      (hmu_rare rfl (by rw [hcore2, hfu1_pred] at hfu3; exact hfu3) hinv3)
                      ⟨hcompat, hinv3, hm3⟩
                  · exact hJp () mr hmr
                  · exact hJp () mr hmr)
              rintro _ _ mp hmp; c0_hstep
              refine wp_join_group (ts := []) (fun _ mq => (FullM6HdrMem c ext1 s2 ⋆ R) mq) ?_
                (fun _ hJq => by
                  have hm_f := fullM6HdrMem_focus hmp
                  c0_hsteps_nogrp
                  · have hinv2p := sr2_upd_fuel_m6Inv hinv2 (s2.core.fuel - 1#64)
                    refine sr2_call_simplify (dp := true) (de := false) rfl hSimplify hinv2p
                      (fullM6HdrMem_unfocus (by assumption)) ?_
                    intro sr c3 ext3 s3 m3 hcomp3 hlen3 hcfg3 hext3 _ hfu3 hu3 hs1 hm3
                    refine sr2_search_simplify_cont hcompat hcomp3 hlen3 hcfg3 hext3 hcore2
                      hfu_pos hfu1_pos hfu1 hfu1_pred hfu3 hu3 hs1 hm3 hQ fun hinv3 hdec => ?_
                    c0_hsteps!
                    exact ih (rlim, reord, last_red, c3, ext3, s3) m3 hdec
                      ⟨hcompat.trans hcomp3, hinv3, hm3⟩
                  · exact hJq () mp hmp
                  · exact hJq () mp hmp)
              rintro _ _ mq hmq; c0_hstep
              refine wp_join_group (ts := []) (fun _ me => (FullM6HdrMem c ext1 s2 ⋆ R) me) ?_
                (fun _ hJe => by
                  have hm_f := fullM6HdrMem_focus hmq
                  c0_hsteps_nogrp
                  · have hinv2e := sr2_upd_fuel_m6Inv hinv2 (s2.core.fuel - 1#64)
                    refine sr2_call_simplify (dp := false) (de := true) rfl hSimplify hinv2e
                      (fullM6HdrMem_unfocus (by assumption)) ?_
                    intro sr c3 ext3 s3 m3 hcomp3 hlen3 hcfg3 hext3 _ hfu3 hu3 hs1 hm3
                    refine sr2_search_simplify_cont hcompat hcomp3 hlen3 hcfg3 hext3 hcore2
                      hfu_pos hfu1_pos hfu1 hfu1_pred hfu3 hu3 hs1 hm3 hQ fun hinv3 hdec => ?_
                    c0_hsteps!
                    exact ih (rlim, reord, last_red, c3, ext3, s3) m3 hdec
                      ⟨hcompat.trans hcomp3, hinv3, hm3⟩
                  · exact hJe () mq hmq
                  · exact hJe () mq hmq
                  · exact hJe () mq hmq)
              rintro _ _ me hme
              refine sr2_call_decideFid rfl hDecideFid hinv2 hme ?_
              intro dr ext3 s3 m3 hinv3 hdomd hfu3 h0d h1d hm3
              have hlen3 := hinv3.sparse.lengths
              have hm3_f := fullM6HdrMem_focus hm3
              c0_hsteps!
              · exact hQ 10#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                  (Or.inr (Or.inl rfl)) (fun hc => by cases hc)
                  (fun _ => hinv3.sparse.2.2.2.1.2) hm3
              · exact hQ 0#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                  (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm3
              · have hdr1 : dr = 1#64 := hdomd.resolve_left hc
                obtain ⟨_, hte3⟩ := h1d hdr1
                have hte_lt : s.core.trail_end < s3.core.trail_end := by
                  have := htr1.1; rw [hcore2] at hte3; omega
                have hte3_le : s3.core.trail_end ≤ c.max_vars :=
                  Nat.le_trans hlen3.core_ok.trail_end_le hlen3.core_ok.cur_vars_le
                have hmu_dec : sr2SearchVariant c s3 < sr2SearchVariant c s := by
                  unfold sr2SearchVariant; rw [hfu3, hcore2]
                  have hmul : (c.max_vars + 1) * s1.core.fuel.toNat ≤
                      (c.max_vars + 1) * s.core.fuel.toNat :=
                    Nat.mul_le_mul_left (c.max_vars + 1) hfu1
                  have hte0_le : s.core.trail_end ≤ c.max_vars :=
                    Nat.le_trans hlen.core_ok.trail_end_le hlen.core_ok.cur_vars_le
                  omega
                exact ih (rlim, reord, last_red, c, ext3, s3) m3 hmu_dec ⟨hcompat, hinv3, hm3⟩

/-! ## 3. Seeded Entrypoint Helpers (`SolveSeededStep13`) -/

section SolveSeededStep13

private theorem sr2_bv64_ugt_max_sub_false {p : BitVec 64} {n : Nat}
    (hfit : p.toNat + n < 2 ^ 64) :
    ((0xFFFFFFFFFFFFFFFF#64 - p).ult (BitVec.ofNat 64 n)) = false := by
  have hp := p.isLt
  have hmax : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : 0xFFFFFFFFFFFFFFFF#64 - p = BitVec.ofNat 64 (2 ^ 64 - 1 - p.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hmax, bv64_ofNat_toNat (by omega)]; omega
  rw [hsub, bv_ult_eq (by omega) (by omega)]
  simp only [decide_eq_false_iff_not]; omega

private theorem sr2_alignPad_bv_ofNat (p : BitVec 64) :
    ((8 : BitVec 64) - (p &&& 7)) &&& 7 = BitVec.ofNat 64 (fullAlignPad p) := by
  apply BitVec.eq_of_toNat_eq
  rw [show ((8 : BitVec 64) - (p &&& 7)) &&& 7 = (8#64 - (p &&& 7#64)) &&& 7#64 from rfl,
    fullAlignPad_eq, bv64_ofNat_toNat (by have := fullAlignPad_lt8 p; omega)]

private theorem sr2_bytes_hdrMem_to_region {cnf_ptr work_ptr : BitVec 64}
    {cnfBytes : List UInt8} {wlen : Nat} {c : FullCfg} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen) (hfit : wlen ≤ 2 ^ 64)
    (hhdr : c.hdr = fullM6WorkHdr work_ptr)
    (hav : c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes)
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆
      region work_ptr (fullAlignPad work_ptr) ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m := by
  have h1 : ((region work_ptr (fullAlignPad work_ptr) ⋆ FullM6HdrMem c ext s) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  have h2 : (region work_ptr wlen ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m :=
    sep_mono (fun _ g => region_work_from_m6_hdrMem hle hfit hhdr hav hcfg hext hlen g) h1
  exact sep_ac h2

private theorem sr2_satCheckPost_to_region {work_ptr : BitVec 64} {wlen : Nat}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {bva_bv mv' nc' cur' val' cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hw_ge : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hch : c.hdr = fullM6WorkHdr work_ptr)
    (hca : c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes)
    (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
      (array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv) ⋆
        array (t := i8) c.pLitMark s.core.lit_mark ⋆
        array (t := i8) c.pMark s.core.mrk ⋆
        FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
        FullScratchArrays c s.scratch ⋆ c.pad ⋆ array64 (c.hdr - 2304) ext ⋆
        region work_ptr (fullAlignPad work_ptr) ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m := by
  have hmx := c.hmaxv; have ha := c.harena; have hw := c.hwcap
  have hd := c.hdel; have hred := c.hred; have he := c.hext; have hscr := c.hscr
  have hmd := fullMinDepthOf_le c.max_vars
  unfold dimacsBound FullScratchArrays FullScrByteArrs FullScrU32A FullScrWksArrs
    FullScrMetaArrs FullScrDynArrs FullCoreU32A FullCoreU32B FullCoreDynArrs at *
  have hc := hlen.core_ok; have hs := hlen.scratch_ok
  have f8 : ∀ {a : BitVec 64} {xs : List (Val i8)} {n : Nat}, xs.length = n → n ≤ 2 ^ 64 →
      ∀ f, array (t := i8) a xs f → region a n f := fun {a xs n} hn hbd f hf => by
    simpa [Ty.bytes, Ty.size, i8, hn] using
      array_to_region (t := i8) (by simp [Ty.bytes, Ty.size, i8, hn, hbd]) hf
  have f32 : ∀ {a : BitVec 64} {xs : List (Val i32)} {n m0 : Nat}, xs.length = n → 4 * n = m0 →
      m0 ≤ 2 ^ 64 → ∀ f, array (t := i32) a xs f → region a m0 f :=
    fun {a xs n m0} hn hm0 hbd f hf => by
      simpa [Ty.bytes, Ty.size, i32, hn, hm0] using
        array_to_region (t := i32) (by simp [Ty.bytes, Ty.size, i32, hn]; omega) hf
  have f64 : ∀ {a : BitVec 64} {xs : List (BitVec 64)} {n m0 : Nat}, xs.length = n →
      8 * n = m0 → m0 ≤ 2 ^ 64 → ∀ f, array64 a xs f → region a m0 f :=
    fun {a xs n m0} hn hm0 hbd f hf => by
      simpa [Ty.bytes, Ty.size, i64, hn, hm0] using
        array_to_region (t := i64) (a := a) (xs := xs) (by simp [Ty.bytes, Ty.size, i64]; omega)
          ((array64_eq_array a xs) ▸ hf)
  have hm_ac : (((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      (array64 (c.hdr - 2304) ext ⋆ region work_ptr (fullAlignPad work_ptr))) ⋆
      ((dimacsState c.hdr mv' nc' cur' val' ⋆
        array64 (c.hdr + 32) ((Full.hdrTailWords c s).set 94 bva_bv)) ⋆
      ((bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
        (array (t := i8) c.pWalkVals s.scratch.walk_vals ⋆
          (array (t := i8) c.pLitMark s.core.lit_mark ⋆
          (array (t := i8) c.pMark s.core.mrk ⋆
            (array (t := i8) c.pPhases s.scratch.phases ⋆
              (array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
                (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
                  array (t := i8) c.pWalkBest s.scratch.walk_best))))))) ⋆
      ((array (t := i32) c.pFlags s.core.flags ⋆
        (array (t := i32) c.pLevel s.core.lvl ⋆
          (array (t := i32) c.pReason s.core.rsns ⋆
            (array (t := i32) c.pTrail s.core.trl ⋆
              array (t := i32) c.pTrailPos s.core.trail_pos)))) ⋆
      ((array (t := i32) c.pTmp s.core.tmp ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆
          (array (t := i32) c.pPos s.scratch.pos ⋆
            (array (t := i32) c.pMinClr s.core.min_clr ⋆
              array (t := i32) c.pShrinkStk s.scratch.shrink_stk)))) ⋆
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        (array (t := i32) c.pQNext s.scratch.q_next ⋆
          (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
            (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
              array (t := i32) c.pFrameDec s.core.frame_dec)))) ⋆
      ((array (t := i32) c.pWvec s.core.wvec ⋆
        (array (t := i32) c.pRepr s.core.repr ⋆
          (array (t := i32) c.pWsort s.scratch.wsort ⋆
            (array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
              (array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
                (array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
                  (array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
                    (array64 c.pScore s.scratch.score ⋆
                      array64 c.pSimSig s.scratch.sim_sig)))))))) ⋆
      ((array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
          (array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
            (array (t := i32) c.pArena s.core.arena ⋆
              (array (t := i32) c.pWstk s.core.wstk ⋆
                (array (t := i32) c.pDelayed s.scratch.delayed ⋆
                  (array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
                    (array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
                      array (t := i32) c.pScratchBuf s.scratch.scratch_buf)))))))) ⋆
      c.pad)))))))) m := sep_ac hm
  have h1 : (((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      (array64 (c.hdr - 2304) ext ⋆ region work_ptr (fullAlignPad work_ptr))) ⋆
      ((region c.hdr 32 ⋆ region (c.hdr + 32#64) 1120) ⋆
      ((region c.pVals (2 * c.max_vars) ⋆
        (region c.pWalkVals (2 * c.max_vars) ⋆
          (region c.pLitMark (2 * c.max_vars) ⋆
          (region c.pMark c.max_vars ⋆
            (region c.pPhases c.max_vars ⋆
              (region c.pPhasesTarget c.max_vars ⋆
                (region c.pPhasesBest c.max_vars ⋆
                  region c.pWalkBest c.max_vars))))))) ⋆
      ((region c.pFlags (4 * c.max_vars) ⋆
        (region c.pLevel (4 * c.max_vars) ⋆
          (region c.pReason (4 * c.max_vars) ⋆
            (region c.pTrail (4 * c.max_vars) ⋆
              region c.pTrailPos (4 * c.max_vars))))) ⋆
      ((region c.pTmp (4 * c.max_vars) ⋆
        (region c.pHeap (4 * c.max_vars) ⋆
          (region c.pPos (4 * c.max_vars) ⋆
            (region c.pMinClr (4 * c.max_vars) ⋆
              region c.pShrinkStk (4 * c.max_vars))))) ⋆
      ((region c.pQPrev (4 * c.max_vars) ⋆
        (region c.pQNext (4 * c.max_vars) ⋆
          (region c.pQStamp (4 * c.max_vars) ⋆
            (region c.pFrameTrail (4 * (c.max_vars + 1)) ⋆
              region c.pFrameDec (4 * (c.max_vars + 1)))))) ⋆
      ((region c.pWvec (16 * c.max_vars) ⋆
        (region c.pRepr (8 * c.max_vars) ⋆
          (region c.pWsort (8 * c.max_vars) ⋆
            (region c.pWorkStk1 (8 * c.max_vars) ⋆
              (region c.pWorkStk2 (8 * c.max_vars) ⋆
                (region c.pTarjanMark (8 * c.max_vars) ⋆
                  (region c.pTarjanReach (8 * c.max_vars) ⋆
                    (region c.pScore (8 * c.max_vars) ⋆
                      region c.pSimSig (8 * c.max_vars))))))))) ⋆
      ((region c.pMinStk (8 * c.minDepth) ⋆
        (region c.pGlueUsed 256 ⋆
          (region c.pLastLearned 64 ⋆
            (region c.pArena (4 * c.arena_cap) ⋆
              (region c.pWstk (4 * c.wcap) ⋆
                (region c.pDelayed (12 * c.delayed_cap) ⋆
                  (region c.pRedRefs (4 * c.red_cap) ⋆
                    (region c.pExtendStk (4 * c.extend_cap) ⋆
                      region c.pScratchBuf (4 * c.scratch_cap))))))))) ⋆
      c.pad)))))))) m := by
    refine sep_mono_r (sep_mono2 ?_ ?_) hm_ac
    · exact sep_mono2 (fun _ h => dimacsState_to_region h)
        (f64 (by rw [List.length_set, Full.hdrTailWords_length]) rfl (by decide))
    · refine sep_mono2 ?_ (sep_mono2 ?_ (sep_mono2 ?_ (sep_mono2 ?_ (sep_mono2 ?_ (sep_mono2 ?_
        (fun _ hb => hb))))))
      · exact sep_mono2 (fun _ hb => by
            have hb' := bytes_to_region hb; simpa [hc.vals_len] using hb')
          (sep_mono2 (f8 hs.walk_vals_len (by omega))
            (sep_mono2 (f8 hc.lit_mark_len (by omega))
              (sep_mono2 (f8 hc.mrk_len (by omega))
                (sep_mono2 (f8 hs.phases_len (by omega))
                  (sep_mono2 (f8 hs.phases_target_len (by omega))
                    (sep_mono2 (f8 hs.phases_best_len (by omega))
                      (f8 hs.walk_best_len (by omega))))))))
      · exact sep_mono2 (f32 hc.flags_len rfl (by omega))
          (sep_mono2 (f32 hc.lvl_len rfl (by omega))
            (sep_mono2 (f32 hc.rsns_len rfl (by omega))
              (sep_mono2 (f32 hc.trl_len rfl (by omega))
                (f32 hc.trail_pos_len rfl (by omega)))))
      · exact sep_mono2 (f32 hc.tmp_len_arr rfl (by omega))
          (sep_mono2 (f32 hs.heap_len_arr rfl (by omega))
            (sep_mono2 (f32 hs.pos_len rfl (by omega))
              (sep_mono2 (f32 hc.min_clr_len_arr rfl (by omega))
                (f32 hs.shrink_stk_len rfl (by omega)))))
      · exact sep_mono2 (f32 hs.q_prev_len rfl (by omega))
          (sep_mono2 (f32 hs.q_next_len rfl (by omega))
            (sep_mono2 (f32 hs.q_stamp_len rfl (by omega))
              (sep_mono2 (f32 hc.frame_trail_len rfl (by omega))
                (f32 hc.frame_dec_len rfl (by omega)))))
      · exact sep_mono2 (f32 hc.wvec_len (by omega) (by omega))
          (sep_mono2 (f32 hc.repr_len (by omega) (by omega))
            (sep_mono2 (f32 hs.wsort_len (by omega) (by omega))
              (sep_mono2 (f32 hs.work_stk1_len (by omega) (by omega))
                (sep_mono2 (f32 hs.work_stk2_len (by omega) (by omega))
                  (sep_mono2 (f32 hs.tarjan_mark_len (by omega) (by omega))
                    (sep_mono2 (f32 hs.tarjan_reach_len (by omega) (by omega))
                      (sep_mono2 (f64 hs.score_len rfl (by omega))
                        (f64 hs.sim_sig_len rfl (by omega)))))))))
      · exact sep_mono2 (f32 hc.min_stk_len (by unfold FullCfg.minDepth; omega)
          (by unfold FullCfg.minDepth; omega))
          (sep_mono2 (f32 hs.glue_used_len (by decide) (by decide))
            (sep_mono2 (f32 hs.last_learned_len (by decide) (by decide))
              (sep_mono2 (f32 hc.arena_len_arr rfl (by omega))
                (sep_mono2 (f32 hc.wstk_len_arr rfl (by omega))
                  (sep_mono2 (f32 hs.delayed_len_arr (by omega) (by omega))
                    (sep_mono2 (f32 hs.red_refs_len rfl (by omega))
                      (sep_mono2 (f32 hs.extend_stk_len rfl (by omega))
                        (f32 hs.scratch_buf_len rfl (by omega)))))))))
  have h2 : (((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      (array64 (c.hdr - 2304) ext ⋆ region work_ptr (fullAlignPad work_ptr))) ⋆
      region c.hdr c.avail) m := sep_mono_r (fun _ h => c.regions_to_avail (sep_ac h)) h1
  have hext_reg : ∀ f, array64 (c.hdr - 2304) ext f →
      region (fullM6WorkBase work_ptr) fullM6ExtBytes f := by
    intro f hf
    have hwb_eq : c.hdr - 2304 = fullM6WorkBase work_ptr := by
      rw [hch]; unfold fullM6WorkHdr fullM6WorkBase fullM6ExtBytes; bv_omega
    rw [hwb_eq] at hf
    exact f64 hext.len rfl (by decide) f hf
  have hm_wb : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆
        (region (fullM6WorkBase work_ptr) fullM6ExtBytes ⋆ region c.hdr c.avail))) m := by
    have hm_a : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆
        (region work_ptr (fullAlignPad work_ptr) ⋆
          (array64 (c.hdr - 2304) ext ⋆ region c.hdr c.avail))) m := sep_ac h2
    exact sep_mono_r (fun _ h => sep_mono_r (fun _ h' => sep_mono hext_reg h') h) hm_a
  have hsum : fullM6ExtBytes + c.avail = wlen - fullAlignPad work_ptr := by
    rw [hca]; unfold fullM6HdrTotalBytes fullM6ExtBytes at *; omega
  have hm_wb2 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆
        region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr))) m := by
    rw [hch] at hm_wb
    have hmg := region_merge_eq (a := fullM6WorkBase work_ptr) hsum (by omega)
    rw [show fullM6WorkBase work_ptr + BitVec.ofNat 64 fullM6ExtBytes =
      fullM6WorkHdr work_ptr from rfl] at hmg
    rwa [hmg] at hm_wb
  have hmg2 : region work_ptr (fullAlignPad work_ptr) ⋆
      region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr) = region work_ptr wlen :=
    region_merge_eq (a := work_ptr) (by unfold fullM6HdrTotalBytes at hw_ge; omega) (by omega)
  rw [hmg2] at hm_wb2; exact sep_ac hm_wb2

private theorem sr2_parseClauses_vars_pos {mv : Nat} :
    ∀ {n : Nat} {acc : CNF Nat} {bs : List UInt8} {cnf : CNF Nat},
      CnfVarsPos acc → parseClauses mv n acc bs = some cnf → CnfVarsPos cnf
  | 0, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hsw : skipWsComments bs with
    | nil => rw [hsw] at h; cases Option.some.inj h; exact hacc
    | cons _ _ => rw [hsw] at h; cases h
  | n + 1, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hpc : parseClause mv bs with
    | none => rw [hpc] at h; cases h
    | some p =>
      rcases p with ⟨cl, rest⟩; rw [hpc] at h
      exact sr2_parseClauses_vars_pos
        (cnfVarsPos_add hacc (parseClauseAux_vars_pos (by simp) hpc)) h

private theorem sr2_parseDimacs_vars_pos {bs : List UInt8} {cnf : CNF Nat}
    (h : parseDimacs bs = some cnf) : CnfVarsPos cnf := by
  unfold parseDimacs at h
  cases hh : parseHeader bs with
  | none => rw [hh] at h; cases h
  | some p =>
    rcases p with ⟨mv, nc, rest⟩; rw [hh] at h
    exact sr2_parseClauses_vars_pos (by intro _ hc; simp at hc) h

end SolveSeededStep13

/-! ## 4. `kissat_solve_bytes_seeded`, `kissat_solve_bytes_m6`, & `kissat_solve_bytes` -/

/-- Step-13 `kissat_solve_bytes_seeded` satisfies `step13SolveBytesSeededSpec` (UNSAT-only
soundness + `UnitUnsatTrace` for arbitrary `seed : BitVec 64`). -/
theorem kissat_solve_bytes_seeded_step13_wp (Γ : Env)
    (hMemInit : EnvSpec Γ "full_m6_mem_init" fullM6MemInitExactSpec)
    (hParse : EnvSpec Γ "full_parse_body" step13ParseBodyM6Spec)
    (hPre : EnvSpec Γ "full_preprocess_m6" fullM6PreprocessSpec)
    (hSearch : EnvSpec Γ "full_search_m6" fullM6SearchSpec)
    (hExt : EnvSpec Γ "full_extend" Full.fullExtendSpec)
    (hCheck : EnvSpec Γ "kissat_check_model" kissatCheckModelExactSpec) :
    ∀ a m Q X, step13SolveBytesSeededSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.kissat_solve_bytes_seeded_body a m Q X := by
  rintro ⟨cnf_ptr, cnf_len, work_ptr, work_len, fuel, seed, ⟨⟩⟩ m Q X
    ⟨cnfBytes, wlen, R, rfl, rfl, hcfit, hwfit, hm, hQ⟩
  unfold Func.wp FullFidelityStep13S3.kissat_solve_bytes_seeded_body
  have ret0 : ∀ m' (hno : fuel = 0#64 ∨ cnf_ptr = 0#64 ∨ work_ptr = 0#64 ∨
      wlen < fullAlignPad work_ptr + fullM6HdrTotalBytes),
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' → Q (0#64, ()) m' := by
    intro m' hno hm'
    refine hQ 0#64 m' (Or.inl rfl) (fun hc => by cases hc)
      (fun mv nc _ hcn hwk hfu hsz _ _ _ => ?_) hm'
    rcases hno with rfl | rfl | rfl | hlt
    · simp at hfu
    · exact absurd rfl hcn
    · exact absurd rfl hwk
    · have hpad := fullAlignPad_lt8 work_ptr
      unfold fullM6HdrTotalBytes at hlt
      have : fullM6ExtBytes = 2304 := rfl
      have : 1152 ≤ fullFixedBytes mv + nc * 40 + 136 := by unfold fullFixedBytes; omega
      omega
  wp_unfold
  refine ⟨fun hf0 => ret0 m (Or.inl hf0) hm, fun _ => ?_⟩
  refine ⟨fun hcp0 => ret0 m (Or.inr (Or.inl hcp0)) hm, fun _ => ?_⟩
  refine ⟨fun hwp0 => ret0 m (Or.inr (Or.inr (Or.inl hwp0))) hm, fun _ => ?_⟩
  have hnot0 : ~~~(0 : BitVec 64) = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [hnot0, sr2_bv64_ugt_max_sub_false hcfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  rw [sr2_bv64_ugt_max_sub_false hwfit]
  refine ⟨(fun h => by cases h), fun _ => ?_⟩
  have hpad_ofNat := sr2_alignPad_bv_ofNat work_ptr
  have hw_nat : (BitVec.ofNat 64 wlen).toNat = wlen := bv64_ofNat_toNat (by omega)
  have hp_nat : (BitVec.ofNat 64 (fullAlignPad work_ptr)).toNat = fullAlignPad work_ptr :=
    bv64_ofNat_toNat (by have := fullAlignPad_lt8 work_ptr; omega)
  have hfit_p : fullAlignPad work_ptr + fullM6HdrTotalBytes < 2 ^ 64 := by
    have := fullAlignPad_lt8 work_ptr; unfold fullM6HdrTotalBytes; omega
  have hpad_ult : (BitVec.ofNat 64 wlen).ult (((8 - (work_ptr &&& 7)) &&& 7) + 3456) =
      decide (wlen < fullAlignPad work_ptr + fullM6HdrTotalBytes) := by
    rw [hpad_ofNat, show (3456 : BitVec 64) = BitVec.ofNat 64 fullM6HdrTotalBytes from rfl,
      bv_add_ofNat, bv_ult_eq (by omega) (by omega)]
  rw [hpad_ult]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun hlt => ret0 m (Or.inr (Or.inr (Or.inr hlt))) hm, fun hw_ge_not => ?_⟩
  have hw_ge : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen := Nat.le_of_not_lt hw_ge_not
  have hwfit_lt : wlen ≤ 2 ^ 64 := Nat.le_of_lt (by omega)
  have hm_wb : (bytes cnf_ptr cnfBytes ⋆
      region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr) ⋆
      (region work_ptr (fullAlignPad work_ptr) ⋆ R)) m := by
    have hmg : region work_ptr (fullAlignPad work_ptr) ⋆
        region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr) = region work_ptr wlen :=
      region_merge_eq (by unfold fullM6HdrTotalBytes at hw_ge; omega) hwfit_lt
    rw [← hmg] at hm; exact sep_ac hm
  have hwb_fit : (fullM6WorkBase work_ptr).toNat + (wlen - fullAlignPad work_ptr) < 2 ^ 64 := by
    have := fullM6WorkBase_toNat_lt (work_ptr := work_ptr) (wlen := wlen) hw_ge hwfit; omega
  have hwb_bv : work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) = fullM6WorkBase work_ptr := rfl
  have hav_bv : BitVec.ofNat 64 wlen - BitVec.ofNat 64 (fullAlignPad work_ptr) =
      BitVec.ofNat 64 (wlen - fullAlignPad work_ptr) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by
        simp only [BitVec.le_def, hw_nat, hp_nat]; unfold fullM6HdrTotalBytes at hw_ge; omega),
      hw_nat, hp_nat, bv64_ofNat_toNat (by omega)]
  c0_hsteps; c0_call hMemInit
  simp only [hpad_ofNat]
  refine fullM6MemInitExactSpec_of (R := region work_ptr (fullAlignPad work_ptr) ⋆ R) rfl hcfit
    (by rw [hwb_bv, hav_bv, bv64_ofNat_toNat (by omega)]; exact hwb_fit)
    (by rw [hwb_bv, hav_bv, bv64_ofNat_toNat (by omega)]; exact sep_ac hm_wb) ?_ ?_
  · intro m' hm' hbad
    c0_hfast
    · have hm'_orig : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' := by
        have h1 : (region work_ptr (fullAlignPad work_ptr) ⋆
            region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr) ⋆
            (bytes cnf_ptr cnfBytes ⋆ R)) m' := by
          rw [hwb_bv, hav_bv, bv64_ofNat_toNat (by omega)] at hm'; exact sep_ac hm'
        have hmg := region_merge_eq (a := work_ptr)
          (show fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen by
            unfold fullM6HdrTotalBytes at hw_ge; omega) (by omega)
        rw [show work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) =
          fullM6WorkBase work_ptr from rfl] at hmg
        rw [hmg] at h1; exact sep_ac h1
      refine hQ 0#64 m' (Or.inl rfl) (fun hc => by cases hc)
        (fun mv nc i0 _ _ _ hsz hi0 hp hu => ?_) hm'_orig
      rcases hbad with hlt | hcap
      · rw [hav_bv, bv64_ofNat_toNat (by omega)] at hlt
        unfold fullM6HdrTotalBytes at hlt hw_ge; have := fullAlignPad_lt8 work_ptr; omega
      · have hcap' := hcap mv nc (cnfBytes.drop i0) hp
        rw [hav_bv, bv64_ofNat_toNat (by omega)] at hcap'
        have : fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen := hsz
        have := fullAlignPad_lt8 work_ptr; unfold fullFixedBytes at *; omega
    · exact absurd rfl hc
  · intro c0 ext0 s0 j0 rest0 m1 hch0 hca0 hcfg0 hinit0 hp0 hj0 hdrop0 hinv0 hcv0
      hdcur0 hal0 hwlen0 hte0 hprop0 hcl0 hfu0 hoom0 hinc0 hprb0 hvals0 hwvec0 hm1
    have hch0_work : c0.hdr = fullM6WorkHdr work_ptr := by rw [hch0, hwb_bv]; rfl
    have hca0_work : c0.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes := by
      rw [hca0, hav_bv, bv64_ofNat_toNat (by omega)]
    c0_hfast
    · exfalso; have hnz := M6HdrCfgOk_le hcfg0; rw [hc] at hnz; simp at hnz
    · have htake0 : List.take (2 * c0.mv) s0.core.vals = List.replicate (2 * c0.mv) 0#8 := by
        have hle : 2 * c0.mv ≤ 2 * c0.max_vars := by have := c0.hbva; omega
        rw [hvals0, List.take_replicate, Nat.min_eq_left hle]
      c0_call hParse
      refine ⟨c0, ext0, s0, cnf_ptr, cnfBytes, j0, region work_ptr (fullAlignPad work_ptr) ⋆ R,
        rfl, rfl, hcfit, hj0, hdrop0 ▸ hp0, hcv0, hdcur0, hcl0, hte0, hprop0, hal0,
        hoom0, hprb0, hinc0, hvals0, hwvec0, hinv0, hm1, ?_⟩
      intro pr ext1 s1 m2 hlen1 hext1 hdomp _ _ _ hp20 hp1 hunitp hm2
      c0_hfast
      · have hm2_a : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c0 ext1 s1 ⋆
            region work_ptr (fullAlignPad work_ptr) ⋆ R) m2 := sep_ac hm2
        have hm2_reg := sr2_bytes_hdrMem_to_region hw_ge hwfit_lt hch0_work hca0_work hcfg0
          hext1 hlen1 hm2_a
        rcases hdomp with rfl | rfl | rfl
        · exact hQ 0#64 m2 (Or.inl rfl) (fun h => by cases h)
            (fun mv nc i1 _ _ _ _ _ hp1' hu1' => by
              have hinj := Option.some.inj (by rw [← hp1', hp0, hdrop0] :
                some (mv, nc, cnfBytes.drop i1) = some (c0.mv, c0.nc, cnfBytes.drop j0))
              have hmv_eq : mv = c0.mv := congrArg (·.1) hinj
              have hnc_eq : nc = c0.nc := congrArg (·.2.1) hinj
              have hdrop_eq : cnfBytes.drop i1 = cnfBytes.drop j0 := congrArg (·.2.2) hinj
              rw [hmv_eq, hnc_eq, hdrop_eq] at hu1'
              have h20 := hunitp (by simpa [htake0] using hu1'); cases h20) hm2_reg
        · exact absurd rfl hc
        · exact hQ 20#64 m2 (Or.inr (Or.inr rfl)) (fun _ => hp20 rfl)
            (fun _ _ _ _ _ _ _ _ _ _ => rfl) hm2_reg
      · have hpr1 : pr = 1#64 := hc
        obtain ⟨cnf, hparse_cnf, hinv1, hcl1⟩ := hp1 hpr1
        have hcnf_pos : CnfVarsPos cnf := sr2_parseDimacs_vars_pos hparse_cnf
        have hno_utrace : ¬ ∃ mv nc i1,
            parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i1) ∧
            UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i1) nc := by
          rintro ⟨mv, nc, i1, hp1', hu1'⟩
          have hinj := Option.some.inj (by rw [← hp1', hp0, hdrop0] :
            some (mv, nc, cnfBytes.drop i1) = some (c0.mv, c0.nc, cnfBytes.drop j0))
          have hmv_eq : mv = c0.mv := congrArg (·.1) hinj
          have hnc_eq : nc = c0.nc := congrArg (·.2.1) hinj
          have hdrop_eq : cnfBytes.drop i1 = cnfBytes.drop j0 := congrArg (·.2.2) hinj
          rw [hmv_eq, hnc_eq, hdrop_eq] at hu1'
          have h20 := hunitp (by simpa [htake0] using hu1'); rw [hpr1] at h20; cases h20
        have hm2_f := fullM6HdrMem_focus
          (R := bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R) (sep_ac hm2)
        c0_hsteps_nogrp; c0_call hPre
        have hm2_pre : (FullM6HdrMem c0 ext1 s1 ⋆
            (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m2 :=
          sep_ac hm2
        refine fullM6PreprocessSpec_of hinv1 hcl1 hm2_pre (by
          intro ppr c2 ext2 s2 m3 hcomp2 hlen2 hcfg2 hext2 hdom2 _ hpp20 hpp1 hpp10 hm3
          have hm3' : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c2 ext2 s2 ⋆
              region work_ptr (fullAlignPad work_ptr) ⋆ R) m3 := sep_ac hm3
          have hch2_w : c2.hdr = fullM6WorkHdr work_ptr := hcomp2.hdr.trans hch0_work
          have hca2_w : c2.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes :=
            hcomp2.avail.trans hca0_work
          c0_hsteps_nogrp
          · have hm3_reg := sr2_bytes_hdrMem_to_region hw_ge hwfit_lt hch2_w hca2_w
              hcfg2 hext2 hlen2 hm3'
            exact hQ 20#64 m3 (Or.inr (Or.inr rfl))
              (fun _ => ⟨cnf, hparse_cnf, shiftDownCnf_unsat hcnf_pos (hpp20 hc)⟩)
              (fun _ _ _ _ _ _ _ _ hp hu => absurd ⟨_, _, _, hp, hu⟩ hno_utrace) hm3_reg
          · have hpp_ne20 : ppr ≠ 20#64 := hc
            let PreFin : BitVec 64 → FullCfg → List (BitVec 64) → FullState →
                Mem 64 → Prop := fun sr cE extE sE mE =>
              FullCfgCompat c0 cE ∧ FullM6HdrCfgOk cE ∧ M6HdrExtOk extE ∧ sE.LengthsOk cE ∧
              (sr = 0#64 ∨ sr = 10#64 ∨ sr = 20#64) ∧ (sr = 20#64 → cnf.Unsat) ∧
              (sr = 10#64 → sE.scratch.extend_len ≤ cE.extend_cap) ∧
              (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem cE extE sE ⋆
                region work_ptr (fullAlignPad work_ptr) ⋆ R) mE
            c0_to_group
            refine wp_join_group (ts := [i64])
              (fun (sr, _) mE => ∃ cE extE sE, PreFin sr cE extE sE mE) ?_ ?_
            · rintro _ ⟨sr, ⟨⟩⟩ mE ⟨cE, extE, sE, hcompatE, hcfgE, hextE, hlenE,
                hdomE, huE, hext_leE, hmE⟩
              have hchE_w : cE.hdr = fullM6WorkHdr work_ptr := hcompatE.hdr.trans hch0_work
              have hcaE_w : cE.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes :=
                hcompatE.avail.trans hca0_work
              c0_hfast
              · have hext_le : sE.scratch.extend_len ≤ cE.extend_cap := hext_leE hc
                rw [← hcompatE.hdr]; c0_call hExt
                refine ⟨cE, sE, array64 (cE.hdr - 2304) extE ⋆
                    (bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R),
                    ⟨rfl, hext_le⟩, hlenE, ?_, ?_⟩
                · simp only [fullExtendSlice_mem]
                  exact sep_ac (fullM6HdrMem_ext_focus (R := bytes cnf_ptr cnfBytes ⋆
                    region work_ptr (fullAlignPad work_ptr) ⋆ R) (sep_ac hmE))
                · intro ⟨⟩ s4 m4 _ hlen4 _ hm4
                  simp only [fullExtendSlice_mem] at hm4
                  have hm4_f : (FullMem cE s4 ⋆ (array64 (cE.hdr - 2304) extE ⋆
                      bytes cnf_ptr cnfBytes ⋆ region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4 :=
                    sep_ac hm4
                  refine wp_store_sep (full_store_mv_mid (BitVec.ofNat 64 c0.mv) hm4_f) ?_
                  intro m4_1 hm4_1; c0_step
                  refine wp_load_of (full_load_max_vars_mid hm4_1) ?_; c0_step
                  let bva_bv : BitVec 64 := BitVec.ofNat 64 cE.max_vars - BitVec.ofNat 64 c0.mv
                  have hmid_arr : (array64 (cE.hdr + 32) (Full.hdrTailWords cE s4) ⋆
                      (dimacsState cE.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 cE.nc)
                          s4.core.d_cur s4.core.d_val ⋆
                        FullCoreArrays cE s4.core ⋆ FullScratchArrays cE s4.scratch ⋆
                        cE.pad ⋆ array64 (cE.hdr - 2304) extE ⋆ bytes cnf_ptr cnfBytes ⋆
                        region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4_1 := by
                    unfold FullMemShrinkMid at hm4_1; exact sep_ac hm4_1
                  obtain ⟨hst_ok, hm4_bva⟩ := store_array64 (i := 94) bva_bv
                    (by rw [Full.hdrTailWords_length]; decide) hmid_arr
                  have hptr784 : cE.hdr + 32 + BitVec.ofNat 64 (8 * 94) = cE.hdr + 784 := by
                    rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 94) = 784
                      by decide]
                  rw [hptr784] at hst_ok hm4_bva
                  refine wp_store_sep ⟨hst_ok, hm4_bva⟩ ?_
                  intro m4_2 hm4_2
                  have hld_pvals :
                      loadVal m4_2 i64 (cE.hdr + (64 : BitVec 64)) = some cE.pVals := by
                    have haddr64 : cE.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * 4) =
                        cE.hdr + (64 : BitVec 64) := by bv_omega
                    have h4lt : 4 < ((Full.hdrTailWords cE s4).set 94 bva_bv).length := by
                      rw [List.length_set, Full.hdrTailWords_length]; decide
                    have hv := loadVal_array64 h4lt hm4_2; rw [haddr64] at hv
                    have h4val : ((Full.hdrTailWords cE s4).set 94 bva_bv)[4] = cE.pVals := by
                      have hget4 : ((Full.hdrTailWords cE s4).set 94 bva_bv)[4]? =
                          some cE.pVals := rfl
                      have := List.getElem?_eq_getElem h4lt
                      rw [hget4] at this; exact (Option.some.inj this).symm
                    rwa [h4val] at hv
                  c0_hsteps; refine wp_load_of hld_pvals ?_
                  have hm4_2' : (bytes cnf_ptr cnfBytes ⋆
                      dimacsState cE.hdr (BitVec.ofNat 64 c0.mv) (BitVec.ofNat 64 cE.nc)
                        s4.core.d_cur s4.core.d_val ⋆
                      bytes cE.pVals (s4.core.vals.map UInt8.ofBitVec) ⋆
                      (array64 (cE.hdr + 32) ((Full.hdrTailWords cE s4).set 94 bva_bv) ⋆
                        array (t := i8) cE.pLitMark s4.core.lit_mark ⋆
                        array (t := i8) cE.pMark s4.core.mrk ⋆
                        FullCoreU32A cE s4.core ⋆ FullCoreU32B cE s4.core ⋆
                        FullCoreDynArrs cE s4.core ⋆ FullScratchArrays cE s4.scratch ⋆
                        cE.pad ⋆ array64 (cE.hdr - 2304) extE ⋆
                        region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4_2 := by
                    have hb_vals : ∀ f, array (t := i8) cE.pVals s4.core.vals f →
                        bytes cE.pVals (s4.core.vals.map UInt8.ofBitVec) f := fun f hf => by
                      have hb := array_eq_bytesOf (t := i8) cE.pVals s4.core.vals (by
                        have hmx := cE.hmaxv; unfold dimacsBound at hmx
                        simp only [Ty.bytes, Ty.size, i8, hlen4.core_ok.vals_len]; omega) hf
                      rw [bytesOf_i8_eq_map] at hb; exact hb.symm
                    have hm4_2_exp : (array (t := i8) cE.pVals s4.core.vals ⋆
                        (bytes cnf_ptr cnfBytes ⋆ dimacsState cE.hdr (BitVec.ofNat 64 c0.mv)
                            (BitVec.ofNat 64 cE.nc) s4.core.d_cur s4.core.d_val ⋆
                          array64 (cE.hdr + 32) ((Full.hdrTailWords cE s4).set 94 bva_bv) ⋆
                          array (t := i8) cE.pLitMark s4.core.lit_mark ⋆
                          array (t := i8) cE.pMark s4.core.mrk ⋆
                          FullCoreU32A cE s4.core ⋆ FullCoreU32B cE s4.core ⋆
                          FullCoreDynArrs cE s4.core ⋆ FullScratchArrays cE s4.scratch ⋆
                          cE.pad ⋆ array64 (cE.hdr - 2304) extE ⋆
                          region work_ptr (fullAlignPad work_ptr) ⋆ R)) m4_2 := by
                      unfold FullCoreArrays FullCoreByteArrs at hm4_2; exact sep_ac hm4_2
                    exact sep_ac (sep_mono hb_vals hm4_2_exp)
                  have hmxE := cE.hmaxv; unfold dimacsBound at hmxE
                  have hmv0_le : c0.mv ≤ cE.max_vars := by
                    have := c0.hbva; have := hcompatE.max_vars; omega
                  c0_call hCheck
                  refine ⟨BitVec.ofNat 64 c0.mv, BitVec.ofNat 64 cE.nc, s4.core.d_cur,
                    s4.core.d_val, cnfBytes, s4.core.vals.map UInt8.ofBitVec, c0.mv, _,
                    rfl, rfl, hcfit,
                    (by have := c0.hbva; have := c0.hmaxv; unfold dimacsBound at *; omega),
                    by rw [List.length_map, hlen4.core_ok.vals_len]; omega,
                    by rw [List.length_map, hlen4.core_ok.vals_len]; omega, hm4_2', ?_⟩
                  intro ok mv' nc' cur' val' m5 _ hm5
                  have hm5_reg := sr2_satCheckPost_to_region hw_ge hwfit hchE_w hcaE_w
                    hextE hlen4 hm5
                  c0_hsteps_nogrp
                  refine wp_join_state_pure (α := BitVec 64) (fun r => (r, ()))
                    (fun ret => ret = 0#64 ∨ ret = 10#64) ?_ ?_
                  · intro _ ret hret; c0_hsteps
                    rcases hret with rfl | rfl
                    · exact hQ 0#64 m5 (Or.inl rfl) (fun h => by cases h)
                        (fun _ _ _ _ _ _ _ _ hp hu => absurd ⟨_, _, _, hp, hu⟩ hno_utrace) hm5_reg
                    · exact hQ 10#64 m5 (Or.inr (Or.inl rfl)) (fun h => by cases h)
                        (fun _ _ _ _ _ _ _ _ hp hu => absurd ⟨_, _, _, hp, hu⟩ hno_utrace) hm5_reg
                  · intro Jr hJr; c0_hsteps
                    · exact hJr 10#64 (Or.inr rfl)
                    · exact hJr 0#64 (Or.inl rfl)
              · have hmE_reg := sr2_bytes_hdrMem_to_region hw_ge hwfit_lt hchE_w hcaE_w
                  hcfgE hextE hlenE hmE
                c0_hfast
                rcases hdomE with rfl | rfl | rfl
                · exact hQ 0#64 mE (Or.inl rfl) (fun h => by cases h)
                    (fun _ _ _ _ _ _ _ _ hp hu => absurd ⟨_, _, _, hp, hu⟩ hno_utrace) hmE_reg
                · exact absurd rfl hc
                · exact hQ 20#64 mE (Or.inr (Or.inr rfl)) (fun _ => ⟨cnf, hparse_cnf, huE rfl⟩)
                    (fun _ _ _ _ _ _ _ _ _ _ => rfl) hmE_reg
            · intro J_fin hJ_fin
              c0_hsteps_nogrp
              · exact hJ_fin (10#64, ()) m3 ⟨c2, ext2, s2, hcomp2, hcfg2, hext2, hlen2,
                  Or.inr (Or.inl rfl), fun h => absurd h (by decide), fun _ => hpp10 hc, hm3'⟩
              · have hpp_ne10 : ppr ≠ 10#64 := hc
                c0_to_group
                refine wp_join_group (ts := [i64])
                  (fun (sr, _) mE => ∃ cE extE sE, PreFin sr cE extE sE mE)
                  (fun _ ⟨sr, ⟨⟩⟩ mE hpre => hJ_fin (sr, ()) mE hpre) ?_
                intro J_mid hJ_mid
                c0_hsteps_nogrp
                · have hppr1 : ppr = 1#64 := by
                    rcases hdom2 with rfl | rfl | rfl | rfl
                    · exact absurd rfl hc
                    · rfl
                    · exact absurd rfl hpp_ne10
                    · exact absurd rfl hpp_ne20
                  obtain ⟨hinv2, hcl2⟩ := hpp1 hppr1
                  -- Step `h->rng_state = seed & 0xFFFFFFFFULL` before `full_search_m6(h)`
                  have hm3_call : (FullM6HdrMem c2 ext2 s2 ⋆ (bytes cnf_ptr cnfBytes ⋆
                      region work_ptr (fullAlignPad work_ptr) ⋆ R)) m3 := sep_ac hm3'
                  rw [← hcomp2.hdr]
                  refine wp_m6Hdr_focus_frame hm3_call fun hm3f => ?_
                  c0_hsteps_nogrp
                  let s2' : FullState := { s2 with scratch := { s2.scratch with
                    rng_state := seed &&& 0xFFFFFFFF#64 } }
                  have hsp2' : FullSparseInv c2 (shiftDownCnf cnf) s2' :=
                    FullSparseInv.with_fuel_scratch hinv2.sparse
                      ⟨hinv2.sparse.lengths.core_ok, { hinv2.sparse.lengths.scratch_ok with }⟩
                      rfl ⟨rfl, rfl⟩
                  have hinv2' := FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk hsp2'
                  c0_call hSearch
                  refine fullM6SearchSpec_of hinv2' hcl2 (fullM6HdrMem_unfocus (by assumption)) ?_
                  intro sr c3 ext3 s3 m4 hcomp3 hlen3 hcfg3 hext3 hdom3 hs20 hs10 hm4
                  exact hJ_mid (sr, ()) m4 ⟨c3, ext3, s3, hcomp2.trans hcomp3, hcfg3, hext3, hlen3,
                    hdom3, fun h20 => shiftDownCnf_unsat hcnf_pos (hs20 h20), hs10, sep_ac hm4⟩
                · exact hJ_mid (0#64, ()) m3 ⟨c2, ext2, s2, hcomp2, hcfg2, hext2, hlen2,
                    Or.inl rfl, fun h => absurd h (by decide), fun h => absurd h (by decide), hm3'⟩)

/-- Step-13 `kissat_solve_bytes_m6` forwards to `kissat_solve_bytes_seeded(..., 0)` and
satisfies `step13SolveBytesSpec`. -/
theorem kissat_solve_bytes_m6_step13_wp (Γ : Env)
    (hSeeded : EnvSpec Γ "kissat_solve_bytes_seeded" step13SolveBytesSeededSpec) :
    ∀ a m Q X, step13SolveBytesSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.kissat_solve_bytes_m6_body a m Q X := by
  rintro ⟨cp, cl, wp_, wl, fu, ⟨⟩⟩ m Q X hs
  unfold Func.wp FullFidelityStep13S3.kissat_solve_bytes_m6_body
  c0_call hSeeded
  exact hs

/-- Step-13 `kissat_solve_bytes` forwards to `kissat_solve_bytes_seeded(..., 0)` and satisfies
`step13SolveBytesSpec`. -/
theorem kissat_solve_bytes_step13_wp (Γ : Env)
    (hSeeded : EnvSpec Γ "kissat_solve_bytes_seeded" step13SolveBytesSeededSpec) :
    ∀ a m Q X, step13SolveBytesSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.kissat_solve_bytes_body a m Q X := by
  rintro ⟨cp, cl, wp_, wl, fu, ⟨⟩⟩ m Q X hs
  unfold Func.wp FullFidelityStep13S3.kissat_solve_bytes_body
  c0_call hSeeded
  exact hs

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S3
