/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearchProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M7 High-Fidelity Search, Splice & UNSAT Non-Vacuity (`FullM7FidelitySearchProof`)

M1-clean, UNSAT-only proof module (`public section`, `0` `@[expose]`, `0` `@[local]`,
`0` `import all`, `XPost := False`, `0` SAT proofs, `std3` axioms):
1. `full_search_fid_wp` (`FullM6Orch.fullM6SearchSpec`, `search.c:195-223` loop).
2. Closed `26`-row `fidSearchSpecTable`, `fidSearchEnv`, `fidSearch_tableImpl`,
   `fidSearch_moduleOk`, plus `fidSearchPatchRows` / `fidSearchPatch_tableImpl_of`.
3. Spliced `411`-fn `FullM7 + FullM7FidelitySearch` integration over `FullM7.m7Module`:
   `fidSearchSpliced_acyclic`, `fidSearchSpliced_moduleOk`, `fidSearchSpliced_solve_bytes_sound`,
   and `fidSearchSpliced_unsat_nv` (`XPost := False`).
4. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for all `4` functions.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelitySearch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6Transport
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open Kraken.Bedrock2.Test

local macro "fs_jnz" h:ident : tactic =>
  `(tactic| (rw [wp_jnz]; dsimp only [Arg.val]; refine ⟨fun $h => ?_, fun $h => ?_⟩))

local elab "fs_nojnz" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

local elab "fs_nojnz_grp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := true, splitJnz := false } 10000

private theorem fs_bv64_sub1 {x : BitVec 64} (hx : x ≠ 0#64) : (x - 1#64).toNat = x.toNat - 1 := by
  have hpos : 0 < x.toNat := Nat.pos_of_ne_zero fun h0 =>
    hx (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

/-! ## 5. `full_search_fid_wp` (`FullM6Orch.fullM6SearchSpec`) -/

section SearchProof

private def fidSearchVariant (c : FullCfg) (s : FullState) : Nat :=
  (c.max_vars + 1) * s.core.fuel.toNat + (c.max_vars - s.core.trail_end)

private theorem fid_fullM6HdrInv_with_fuel {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (hinv : FullM6HdrInv c F0 ext s)
    (fu' : BitVec 64) :
    FullM6HdrInv c F0 ext { s with core := { s.core with fuel := fu' } } := by
  have hsp := hinv.sparse
  have hlen' : ({ s with core := { s.core with fuel := fu' } } : FullState).LengthsOk c :=
    ⟨{ hsp.lengths.core_ok with }, hsp.lengths.scratch_ok⟩
  exact FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk (hsp.with_fuel_scratch hlen' rfl ⟨rfl, rfl⟩)

private theorem fid_fullM6HdrInvW_with_fuel {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s : FullState}
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (fu' : BitVec 64) :
    FullM6HdrInvW c F0 F_cur ext { s with core := { s.core with fuel := fu' } } := by
  have hsp := hinv.sparseW
  let s' : FullState := { s with core := { s.core with fuel := fu' } }
  have hlen' : s'.LengthsOk c := ⟨{ hsp.1.core_ok with }, hsp.1.scratch_ok⟩
  have hw := hsp.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      cur_level_le := hw.cur_level_le, trail_lits_lt := hw.trail_lits_lt
      trail_vars_nodup := hw.trail_vars_nodup, vals_domain := hw.vals_domain
      vals_true_iff := hw.vals_true_iff, vals_false_iff := hw.vals_false_iff, lvl_le := hw.lvl_le
      dec_earliest := hw.dec_earliest, levels_inhabited := hw.levels_inhabited
      level0_sound := hw.level0_sound, trail_pos_inv := hw.trail_pos_inv
      level0_rsn_none := hw.level0_rsn_none, frame_trail_lt := hw.frame_trail_lt
      frame_trail_mono := hw.frame_trail_mono, frame_trail_before_lt := hw.frame_trail_before_lt
      frame_dec_lt := hw.frame_dec_lt, reason_inv := hw.reason_inv
      reason_lit_mem := hw.reason_lit_mem }
  exact FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
    ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem fid_variant_fuel_lt {c c' : FullCfg} {F0 : CNF Nat}
    {ext' : List (BitVec 64)} {s s' : FullState}
    (hmveq : c'.max_vars = c.max_vars) (hfu_pos : 0 < s.core.fuel.toNat)
    (hfule : s'.core.fuel.toNat ≤ s.core.fuel.toNat - 1) (hinv' : FullM6HdrInv c' F0 ext' s') :
    fidSearchVariant c' s' < fidSearchVariant c s := by
  unfold fidSearchVariant
  rw [hmveq]
  have hmul : (c.max_vars + 1) * s'.core.fuel.toNat ≤
      (c.max_vars + 1) * (s.core.fuel.toNat - 1) :=
    Nat.mul_le_mul_left (c.max_vars + 1) hfule
  have hte' : s'.core.trail_end ≤ c'.max_vars :=
    Nat.le_trans hinv'.sparse.lengths.core_ok.trail_end_le
      hinv'.sparse.lengths.core_ok.cur_vars_le
  have h2 : c.max_vars - s'.core.trail_end ≤ c.max_vars := Nat.sub_le _ _
  have hs_mul : (c.max_vars + 1) * s.core.fuel.toNat =
      (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := by
    have hsub : s.core.fuel.toNat - 1 + 1 = s.core.fuel.toNat := by omega
    calc (c.max_vars + 1) * s.core.fuel.toNat
        = (c.max_vars + 1) * (s.core.fuel.toNat - 1 + 1) := by rw [hsub]
      _ = (c.max_vars + 1) * (s.core.fuel.toNat - 1) + (c.max_vars + 1) := Nat.mul_succ _ _
  omega

private theorem fid_call_luckyLate_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', m7LuckyLateSpec (c.hdr, ()) m Q' X' →
      Γ "full_lucky_late_m7" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = 0#64 →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullM6HdrInv c F0 ext s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_lucky_late_m7" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X (m7LuckyLateSpec_of hinv.sparse ((fullM6HdrMem_iff c ext s R m).mp hm)
    fun r s' m' hlen hr hfu hpr h20 h02 h10 hm' => ?_)
  exact hk r s' m' hlen hr hfu hpr h20
    (fun h => let x := h02 h; ⟨FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk x.1, x.2⟩)
    h10 ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem fid_call_fullPropagate_invW {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', Full.fullPropagateSpec (c.hdr, ()) m Q' X' →
      Γ "full_propagate" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → FullTrailExt s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' s'
    hlen' hw' htr' hperm' hfu' hdom _ hr1 _ _ hm'
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩
  exact hk r s' m' hinv' htr' hfu' hdom hr1 ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem fid_call_m6Analyze_invW {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', m6HdrAnalyzeSpec (c.hdr, ()) m Q' X' →
      Γ "full_analyze_m6_hdr" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hcok : FullConflictOkW F_cur s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInvW c F0 F_cur ext' s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_analyze_m6_hdr" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hΓ _ X (m6HdrAnalyzeSpec_of hinv hcok hm
    fun r ext' s' m' hext' hlen' hr _ hfu _ hu _ h1 hm' =>
      hk r ext' s' m' hext' hlen' hr hfu hu h1 hm')

private theorem fid_call_m6Reduce_invW {Γ : Env} {force : Bool} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, force, ()))
    (hΓ : ∀ Q' X', m6ReduceSpec (c.hdr, force, ()) m Q' X' →
      Γ "full_reduce_m6" [i64, .bool] [i64] (c.hdr, force, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext' s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_reduce_m6" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hΓ _ X (m6ReduceSpec_of hinv hm fun r ext' s' m' hinv' hr _ hfu _ _ _ _ hu _ _ hm' =>
    hk r ext' s' m' hinv' hr hfu hu hm')

private theorem fid_call_m7SwitchMode_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', m7SwitchModeSpec (c.hdr, ()) m Q' X' →
      Γ "full_switch_mode_m7" [i64] [] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core = s.core →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_switch_mode_m7" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X (m7SwitchModeSpec_of hinv.sparse.lengths
    ((fullM6HdrMem_iff c ext s R m).mp hm) fun s' m' hcore hlen hpr _ _ _ hm' => ?_)
  exact hk s' m' (fullM6HdrInv_of_core_eq hinv hlen hcore hpr.1) hcore
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem fid_call_fullRestartDue_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', Full.fullRestartDueSpec (c.hdr, ()) m Q' X' →
      Γ "full_restart_due" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core = s.core →
      (r = 0#64 ∨ r = 1#64) → (FullM6HdrMem c ext s' ⋆ R) m' →
      wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_restart_due" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse.lengths,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  rintro ⟨r, ⟨⟩⟩ s' m' hcore hlen ⟨hdom, hpres⟩ hm'
  have hceq : s'.core = s.core := @Full.fullCoreState_agrees_with_scratch c s s' hcore
  exact hk r s' m' (fullM6HdrInv_of_core_eq hinv hlen hceq hpres) hceq hdom
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem fid_call_fullRestart_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', Full.fullRestartSpec (c.hdr, ()) m Q' X' →
      Γ "full_restart" [i64] [] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.fuel = s.core.fuel →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_restart" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparse
  have hcore := fullM6HdrInv_to_coreInv hinv
  refine hΓ _ X ⟨c, F0, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hcore.coreInv,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro _ _ _ _ _ _ _ _ _ sc' m' s' hc' _ hpres' hm'
  have hlm' : FullLitMarksClear c s' := ⟨hsp.2.1.1, hsp.2.1.2⟩
  have hvn' : FullArenaVarsNodup s' := hsp.2.2.1
  have hwf' : FullLastLearnedWf s' :=
    hsp.2.2.2.1.1.of_refs_subset hpres'.1 fun _ hr => hr
  have hext_sc' : FullExtScratchOk c s' :=
    ⟨hwf', by change sc'.extend_len ≤ c.extend_cap; rw [hpres'.2]; exact hsp.2.2.2.1.2⟩
  let hinv' := FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk ⟨hc', hlm', hvn', hext_sc', hsp.2.2.2.2⟩
  exact hk s' m' hinv' rfl ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem fid_call_m4Reorder_inv {Γ : Env} {budget : BitVec 64} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, budget, ()))
    (hΓ : ∀ Q' X', FullM4.m4ReorderSpec (c.hdr, budget, ()) m Q' X' →
      Γ "full_reorder_m6" [i64, i64] [i64] (c.hdr, budget, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.fuel = s.core.fuel →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_reorder_m6" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X ⟨c, F0, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv.sparse,
    (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r s' m' hsp' _ _ hfu' hm'
  exact hk r s' m' (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hfu'
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem fid_call_m7Rephase_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', m7RephaseSpec (c.hdr, ()) m Q' X' →
      Γ "full_rephase" [i64] [] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_rephase" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X (m7RephaseSpec_of hinv.sparse ((fullM6HdrMem_iff c ext s R m).mp hm) ?_)
  intro vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' cl' prob' unass' unfl'
    wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m' hsp' _ _ _ hfu' _ _ hm'
  exact hk _ m' (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hfu'
    ((fullM6HdrMem_iff c ext _ R m').mpr hm')

private theorem fid_call_m6Simplify_inv {Γ : Env} {dp de : Bool} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool, .bool]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, dp, de, ()))
    (hΓ : ∀ Q' X', fullM6SimplifySpec (c.hdr, dp, de, ()) m Q' X' →
      Γ "full_simplify_m6" [i64, .bool, .bool] [i64] (c.hdr, dp, de, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (c' : FullCfg) (ext' : List (BitVec 64)) (s' : FullState)
      (m' : Mem 64),
      FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_simplify_m6" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hΓ _ X (fullM6SimplifySpec_of hinv hm hk)

private theorem fid_call_m6HdrDecide_inv {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', m6HdrDecideSpec (c.hdr, ()) m Q' X' →
      Γ "m6_hdr_decide_fid" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext' s' → (r = 0#64 ∨ r = 1#64) →
      s'.core.fuel = s.core.fuel →
      (r = 0#64 → s'.core.cur_level = s.core.cur_level ∧ s'.core.trail_end = s.core.trail_end) →
      (r = 1#64 → s'.core.cur_level = s.core.cur_level + 1 ∧
        s'.core.trail_end = s.core.trail_end + 1) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "m6_hdr_decide_fid" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparse
  have hcore := fullM6HdrInv_to_coreInv hinv
  refine hΓ _ X (m6HdrDecideSpec_of hcore hm ?_)
  intro r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' ext' m' s'
    hcore' hpres' hdom h0 h1 hm'
  have hlm' : FullLitMarksClear c s' := ⟨hsp.2.1.1, hsp.2.1.2⟩
  have hvn' : FullArenaVarsNodup s' := hsp.2.2.1
  have hwf' : FullLastLearnedWf s' :=
    hsp.2.2.2.1.1.of_refs_subset hpres'.1 fun _ hr => hr
  have hext_sc' : FullExtScratchOk c s' :=
    ⟨hwf', by change sc'.extend_len ≤ c.extend_cap; rw [hpres'.2]; exact hsp.2.2.2.1.2⟩
  have hinv' : FullM6HdrInv c F0 ext' s' :=
    FullM6HdrInv.mk_inv hcore'.cfgOk hcore'.extOk
      ⟨hcore'.coreInv, hlm', hvn', hext_sc', hsp.2.2.2.2⟩
  exact hk r ext' s' m' hinv' hdom rfl h0 (fun hr1 => ⟨(h1 hr1).1, (h1 hr1).2.1⟩) hm'

private theorem fid_hdrMem_of_focus {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m) :
    (FullM6HdrMem c ext s ⋆ R) m :=
  fullM6HdrMem_unfocus_full hm

/-- Parametric `Func.wp` proof for `full_search_fid` against `FullM6Orch.fullM6SearchSpec`,
moving maintenance into the `pr == 0ULL` `else` branch with `h->fuel` decrement and
`m6_hdr_decide_fid`. -/
theorem full_search_fid_wp (Γ : Env)
    (hLuckyLate : ∀ a m Q X, m7LuckyLateSpec a m Q X →
      Γ "full_lucky_late_m7" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hAnalyze : ∀ a m Q X, m6HdrAnalyzeSpec a m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] a m Q X)
    (hReduce : ∀ a m Q X, m6ReduceSpec a m Q X →
      Γ "full_reduce_m6" [i64, .bool] [i64] a m Q X)
    (hSwitch : ∀ a m Q X, m7SwitchModeSpec a m Q X →
      Γ "full_switch_mode_m7" [i64] [] a m Q X)
    (hRstDue : ∀ a m Q X, Full.fullRestartDueSpec a m Q X →
      Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, Full.fullRestartSpec a m Q X →
      Γ "full_restart" [i64] [] a m Q X)
    (hReorder : ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Γ "full_reorder_m6" [i64, i64] [i64] a m Q X)
    (hRephase : ∀ a m Q X, m7RephaseSpec a m Q X →
      Γ "full_rephase" [i64] [] a m Q X)
    (hSimplify : ∀ a m Q X, fullM6SimplifySpec a m Q X →
      Γ "full_simplify_m6" [i64, .bool, .bool] [i64] a m Q X)
    (hDecide : ∀ a m Q X, m6HdrDecideSpec a m Q X →
      Γ "m6_hdr_decide_fid" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6SearchSpec a m Q X → Func.wp Γ full_search_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6SearchSpec_elim hs with ⟨c0, F0, ext0, s0, R, rfl, hinv0, _, hm0, hQ⟩
  unfold Func.wp full_search_fid_body
  c0_hsteps_nogrp
  refine fid_call_luckyLate_inv rfl (hLuckyLate _ _) hinv0 hm0 ?_
  intro lkr s_lk m_lk hlen_lk hdom_lk _ _ h20_lk h02_lk h10_lk hm_lk
  c0_hsteps_nogrp
  · have hl := hc; rw [hl]
    exact hQ 10#64 c0 ext0 s_lk m_lk (FullCfgCompat.refl c0) hlen_lk hinv0.cfgOk hinv0.extOk
      (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ => h10_lk hl) hm_lk
  · have hl := hc; rw [hl]
    exact hQ 20#64 c0 ext0 s_lk m_lk (FullCfgCompat.refl c0) hlen_lk hinv0.cfgOk hinv0.extOk
      (Or.inr (Or.inr rfl)) (fun _ => h20_lk hl) (fun h => by cases h) hm_lk
  · have hlkr02 : lkr = 0#64 ∨ lkr = 2#64 := by
      rcases hdom_lk with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl (by assumption)
      · exact absurd rfl hc
    have hinv_lk := (h02_lk hlkr02).1
    let LpSt := BitVec 64 × BitVec 64 × BitVec 64 × FullCfg × List (BitVec 64) × FullState
    refine wp_while_state (ts := [i64, i64, i64]) (α := LpSt)
      (fun ⟨rlim, reord, lrc, _, _, _⟩ => (rlim, reord, lrc, ()))
      (fun ⟨_, _, _, c, _, s⟩ => fidSearchVariant c s)
      (fun ⟨_, _, _, c, ext, s⟩ ml =>
        FullCfgCompat c0 c ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) ml)
      (fun J hJ => by
        c0_hsteps
        exact hJ (10000#64, 0#64, 0xFFFFFFFFFFFFFFFF#64, c0, ext0, s_lk) m_lk
          ⟨FullCfgCompat.refl c0, hinv_lk, hm_lk⟩)
      ?_
    rintro J ⟨rlim, reord, lrc, c, ext, s⟩ ml ⟨hcompat, hinv, hml⟩ ih
    rw [Blocks.get_here, ← hcompat.hdr]
    have hsp := hinv.sparse
    have hlen := hsp.lengths
    have hmx : c.max_vars < 2 * 268435456 := Nat.lt_of_lt_of_le c.hmaxv (by decide)
    have hml_f := fullM6HdrMem_focus hml
    c0_hsplit
    rotate_left; · cases hc
    c0_hsteps_nogrp
    · exact hQ 0#64 c ext s ml hcompat hlen hinv.cfgOk hinv.extOk (Or.inl rfl)
        (fun hc => absurd hc (by decide)) (fun hc => absurd hc (by decide)) hml
    · exact hQ 0#64 c ext s ml hcompat hlen hinv.cfgOk hinv.extOk (Or.inl rfl)
        (fun hc => absurd hc (by decide)) (fun hc => absurd hc (by decide)) hml
    · have hfu_pos : 0 < s.core.fuel.toNat := by
        have hpos : s.core.fuel.toNat ≠ 0 :=
          fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
        omega
      obtain ⟨F_cur, hinvW⟩ := fullM6HdrInv_exists_witness hinv
      refine fid_call_fullPropagate_invW rfl (hProp _ _) hinvW hml ?_
      intro pr s1 m1 hinvW1 htr1 hfu1 hdom1 hr1 hm1
      have hinv1 := hinvW1.toInv
      have hlen1 := hinv1.sparse.lengths
      have hm1_f := fullM6HdrMem_focus hm1
      fs_nojnz
      fs_jnz hpr2
      · c0_hsteps_nogrp
        exact hQ 0#64 c ext s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inl rfl)
          (fun hc => by cases hc) (fun hc => by cases hc) hm1
      · fs_nojnz_grp
        fs_jnz hpr1
        · have hpr1 : pr = 1#64 := if h : pr = 1#64 then h else by simp [h] at hpr1
          c0_hsteps_nogrp
          obtain ⟨hfu_lt, _, hcok1⟩ := hr1 hpr1
          refine fid_call_m6Analyze_invW rfl (hAnalyze _ _) hinvW1 hcok1 hm1 ?_
          intro ast ext2 s2 m2 hext2 hlen2 hast hfu2 hu2 ha1 hm2
          c0_hsteps_nogrp
          · exact hQ 20#64 c ext2 s2 m2 hcompat hlen2 hinv1.cfgOk hext2 (Or.inr (Or.inr rfl))
              (fun _ => hu2 hc) (fun hc => by cases hc) hm2
          · exact hQ 0#64 c ext2 s2 m2 hcompat hlen2 hinv1.cfgOk hext2 (Or.inl rfl)
              (fun hc => by cases hc) (fun hc => by cases hc) hm2
          · obtain ⟨hinvW2, _⟩ := ha1 hc
            have hinv2 := hinvW2.toInv
            exact ih (rlim, reord, lrc, c, ext2, s2) m2
              (fid_variant_fuel_lt rfl hfu_pos (by omega) hinv2) ⟨hcompat, hinv2, hm2⟩
        · fs_nojnz
          fs_jnz hun
          · c0_hsteps_nogrp
            exact hQ 10#64 c ext s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inr (Or.inl rfl))
              (fun hc => by cases hc) (fun _ => hinv1.sparse.2.2.2.1.2) hm1
          · fs_nojnz
            fs_jnz hfu
            · c0_hsteps_nogrp
              exact hQ 0#64 c ext s1 m1 hcompat hlen1 hinv1.cfgOk hinv1.extOk (Or.inl rfl)
                (fun hc => by cases hc) (fun hc => by cases hc) hm1
            · have hfu1_ne0 : s1.core.fuel ≠ 0#64 := fun h0 => by simp [h0] at hfu
              have hfu1_m1_lt : (s1.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat - 1 := by
                rw [fs_bv64_sub1 hfu1_ne0]
                have hpos1 : 0 < s1.core.fuel.toNat :=
                  Nat.pos_of_ne_zero fun h0 =>
                    hfu1_ne0 (BitVec.eq_of_toNat_eq (by simpa using h0))
                omega
              let s1f : FullState :=
                { s1 with core := { s1.core with fuel := s1.core.fuel - 1#64 } }
              have hinv1f : FullM6HdrInv c F0 ext s1f := fid_fullM6HdrInv_with_fuel hinv1 _
              have hinvW1f : FullM6HdrInvW c F0 F_cur ext s1f :=
                fid_fullM6HdrInvW_with_fuel hinvW1 _
              have hfu1f_eq : s1f.core.fuel.toNat = s1.core.fuel.toNat - 1 :=
                fs_bv64_sub1 hfu1_ne0
              fs_nojnz_grp
              fs_jnz hred
              · -- `conflicts >= reduce_limit`
                c0_hsteps_nogrp
                refine fid_call_m6Reduce_invW rfl (hReduce _ _) hinvW1f
                  (fid_hdrMem_of_focus (by assumption)) ?_
                intro rr ext3 s3 m3 hinvW3 _ hfu3 hu3 hm3
                have hinv3 := hinvW3.toInv
                have hlen3 := hinv3.sparse.lengths
                c0_hsteps_nogrp
                · exact hQ 20#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                    (Or.inr (Or.inr rfl)) (fun _ => hu3 hc) (fun hc => by cases hc) hm3
                · exact hQ 0#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk hinv3.extOk
                    (Or.inl rfl) (fun hc => by cases hc) (fun hc => by cases hc) hm3
                · exact ih (rlim, reord, s1.scratch.conflicts, c, ext3, s3) m3
                    (fid_variant_fuel_lt rfl hfu_pos (by omega) hinv3) ⟨hcompat, hinv3, hm3⟩
              · -- `(stable == 0) ? (conflicts >= mode_confl_lim) : (search_ticks >= mode_tick_lim)`
                c0_hsteps_nogrp
                let ContInv2 :
                    BitVec 64 × BitVec 64 × FullCfg × List (BitVec 64) × FullState → Mem 64 →
                      Prop :=
                  fun ⟨_, _, cJ, extJ, sJ⟩ mJ =>
                    FullCfgCompat c0 cJ ∧ FullM6HdrInv cJ F0 extJ sJ ∧
                    fidSearchVariant cJ sJ < fidSearchVariant c s ∧
                    (FullM6HdrMem cJ extJ sJ ⋆ R) mJ
                let ContInv3 : FullCfg × List (BitVec 64) × FullState → Mem 64 → Prop :=
                  fun ⟨cJ, extJ, sJ⟩ mJ => ContInv2 (rlim, reord, cJ, extJ, sJ) mJ
                refine wp_join_state (ts := [i64, i64])
                  (α := BitVec 64 × BitVec 64 × FullCfg × List (BitVec 64) × FullState)
                  (fun ⟨r, ro, _, _, _⟩ => (r, ro, ())) ContInv2 ?_ ?_
                · intro _ ⟨rJ, roJ, cJ, extJ, sJ⟩ mJ ⟨hcJ, hinvJ, hmuJ, hmJ⟩
                  rw [Blocks.get_here]; c0_hsteps_nogrp
                  exact ih (rJ, roJ, lrc, cJ, extJ, sJ) mJ hmuJ ⟨hcJ, hinvJ, hmJ⟩
                · intro Js hJs
                  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                    (fun v => (v, ())) (fun _ => True) ?_
                    (fun _ hJmd => by c0_hsteps <;> exact hJmd _ trivial)
                  intro _ mode_due _
                  c0_hsteps_nogrp
                  · refine fid_call_m7SwitchMode_inv rfl (hSwitch _ _) hinv1f
                      (fid_hdrMem_of_focus (by assumption)) ?_
                    intro s3 m3 hinv3 hcore3 hm3
                    c0_hsteps_nogrp
                    exact hJs (rlim, reord, c, ext, s3) m3 ⟨hcompat, hinv3,
                      fid_variant_fuel_lt rfl hfu_pos (by rw [hcore3]; exact hfu1_m1_lt) hinv3, hm3⟩
                  · fs_nojnz_grp
                    refine fid_call_fullRestartDue_inv rfl (hRstDue _ _) hinv1 hm1 ?_
                    intro rdu s2 m2 hinv2 hcore2 _ hm2
                    have hm2_f := fullM6HdrMem_focus hm2
                    let s2f : FullState :=
                      { s2 with core := { s2.core with fuel := s2.core.fuel - 1#64 } }
                    have hinv2f : FullM6HdrInv c F0 ext s2f := fid_fullM6HdrInv_with_fuel hinv2 _
                    have hfu2_ne0 : s2.core.fuel ≠ 0#64 := by rw [hcore2]; exact hfu1_ne0
                    have hfu2_m1 : s2f.core.fuel.toNat ≤ s.core.fuel.toNat - 1 := by
                      change (s2.core.fuel - 1#64).toNat ≤ _
                      rw [fs_bv64_sub1 hfu2_ne0, hcore2, ← fs_bv64_sub1 hfu1_ne0]; exact hfu1_m1_lt
                    c0_hsteps_nogrp
                    · refine fid_call_fullRestart_inv rfl (hRst _ _) hinv2f
                        (fid_hdrMem_of_focus (by assumption)) ?_
                      intro s3 m3 hinv3 hfu3 hm3
                      c0_hsteps_nogrp
                      exact hJs (rlim, reord, c, ext, s3) m3 ⟨hcompat, hinv3,
                        fid_variant_fuel_lt rfl hfu_pos (by rw [hfu3]; exact hfu2_m1) hinv3, hm3⟩
                    · -- Remaining `else if` chain: reorder, rephase, probe, elim, decide
                      refine wp_join_state (ts := [i64, i64])
                        (α := BitVec 64 × BitVec 64 × FullCfg × List (BitVec 64) × FullState)
                        (fun ⟨r, ro, _, _, _⟩ => (r, ro, ())) ContInv2 ?_ ?_
                      · intro _ p mJ h
                        rw [Blocks.get_here]; c0_hsteps_nogrp; exact hJs p mJ h
                      · intro Js_ro hJs_ro
                        refine wp_join0 (fun m_reord => m_reord = m2) ?_ ?_
                        · intro _ m_j hm_eq; rw [hm_eq, Blocks.get_here]
                          refine wp_join_state0 (α := FullCfg × List (BitVec 64) × FullState)
                            ContInv3 ?_ ?_
                          · intro _ ⟨cJ, extJ, sJ⟩ mJ h
                            rw [Blocks.get_here]; c0_hsteps_nogrp
                            exact hJs_ro (rlim, reord, cJ, extJ, sJ) mJ h
                          · intro J_rp hJ_rp
                            refine wp_join0 (fun m_reph => m_reph = m2) ?_ ?_
                            · intro _ m_j2 hm_eq2; rw [hm_eq2, Blocks.get_here]
                              refine wp_join_state0 (α := FullCfg × List (BitVec 64) × FullState)
                                ContInv3 ?_ ?_
                              · intro _ p mJ h
                                rw [Blocks.get_here]; c0_hsteps_nogrp; exact hJ_rp p mJ h
                              · intro J_pr hJ_pr
                                refine wp_join0 (fun m_prb => m_prb = m2) ?_ ?_
                                · intro _ m_j3 hm_eq3; rw [hm_eq3, Blocks.get_here]
                                  refine wp_join_state0
                                    (α := FullCfg × List (BitVec 64) × FullState) ContInv3 ?_ ?_
                                  · intro _ p mJ h
                                    rw [Blocks.get_here]; c0_hsteps_nogrp; exact hJ_pr p mJ h
                                  · intro J_el hJ_el
                                    refine wp_join0 (fun m_el => m_el = m2) ?_ ?_
                                    · intro _ m_j4 hm_eq4; rw [hm_eq4, Blocks.get_here]
                                      refine fid_call_m6HdrDecide_inv rfl (hDecide _ _) hinv2 hm2 ?_
                                      intro dr ext3 s3 m3 hinv3 hdomd hfu3 h0d h1d hm3
                                      have hlen3 := hinv3.sparse.lengths
                                      have hm3_f := fullM6HdrMem_focus hm3
                                      c0_hsteps
                                      · exact hQ 10#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk
                                          hinv3.extOk (Or.inr (Or.inl rfl)) (fun hc => by cases hc)
                                          (fun _ => hinv3.sparse.2.2.2.1.2) hm3
                                      · exact hQ 0#64 c ext3 s3 m3 hcompat hlen3 hinv3.cfgOk
                                          hinv3.extOk (Or.inl rfl) (fun hc => by cases hc)
                                          (fun hc => by cases hc) hm3
                                      · have hdr1 : dr = 1#64 := hdomd.resolve_left hc
                                        obtain ⟨_, hte3⟩ := h1d hdr1
                                        have hte_lt : s.core.trail_end < s3.core.trail_end := by
                                          have := htr1.1; rw [hcore2] at hte3; omega
                                        have hte3_le : s3.core.trail_end ≤ c.max_vars :=
                                          Nat.le_trans hlen3.core_ok.trail_end_le
                                            hlen3.core_ok.cur_vars_le
                                        have hmu_dec :
                                            fidSearchVariant c s3 < fidSearchVariant c s := by
                                          unfold fidSearchVariant
                                          rw [hfu3, hcore2]
                                          have hmul : (c.max_vars + 1) * s1.core.fuel.toNat ≤
                                              (c.max_vars + 1) * s.core.fuel.toNat :=
                                            Nat.mul_le_mul_left (c.max_vars + 1) hfu1
                                          have hte0_le : s.core.trail_end ≤ c.max_vars :=
                                            Nat.le_trans hlen.core_ok.trail_end_le
                                              hlen.core_ok.cur_vars_le
                                          omega
                                        exact hJ_el (c, ext3, s3) m3 ⟨hcompat, hinv3, hmu_dec, hm3⟩
                                    · intro Jnel hJnel; c0_hsteps_nogrp
                                      · refine fid_call_m6Simplify_inv (dp := false) (de := true)
                                          rfl (hSimplify _ _) hinv2f
                                          (fid_hdrMem_of_focus (by assumption)) ?_
                                        intro sr c3 ext3 s3 m3 hcomp3 hlen3 hcfg3 hext3 _hsr hfu3
                                          hu3 hs1 hm3
                                        have hcompat3 := hcompat.trans hcomp3
                                        c0_hsteps_nogrp
                                        · exact hQ 20#64 c3 ext3 s3 m3 hcompat3 hlen3 hcfg3 hext3
                                            (Or.inr (Or.inr rfl)) (fun _ => hu3 hc)
                                            (fun hc => by cases hc) hm3
                                        · exact hQ 0#64 c3 ext3 s3 m3 hcompat3 hlen3 hcfg3 hext3
                                            (Or.inl rfl) (fun hc => by cases hc)
                                            (fun hc => by cases hc) hm3
                                        · obtain ⟨hinv3, _⟩ := hs1 hc
                                          exact hJ_el (c3, ext3, s3) m3 ⟨hcompat3, hinv3,
                                            fid_variant_fuel_lt hcomp3.max_vars hfu_pos
                                              (Nat.le_trans hfu3 hfu2_m1) hinv3, hm3⟩
                                      · exact hJnel m2 rfl
                                      · exact hJnel m2 rfl
                                · intro Jnpb hJnpb; c0_hsteps_nogrp
                                  · refine fid_call_m6Simplify_inv (dp := true) (de := false)
                                      rfl (hSimplify _ _) hinv2f
                                      (fid_hdrMem_of_focus (by assumption)) ?_
                                    intro sr c3 ext3 s3 m3 hcomp3 hlen3 hcfg3 hext3 _hsr hfu3 hu3
                                      hs1 hm3
                                    have hcompat3 := hcompat.trans hcomp3
                                    c0_hsteps_nogrp
                                    · exact hQ 20#64 c3 ext3 s3 m3 hcompat3 hlen3 hcfg3 hext3
                                        (Or.inr (Or.inr rfl)) (fun _ => hu3 hc)
                                        (fun hc => by cases hc) hm3
                                    · exact hQ 0#64 c3 ext3 s3 m3 hcompat3 hlen3 hcfg3 hext3
                                        (Or.inl rfl) (fun hc => by cases hc)
                                        (fun hc => by cases hc) hm3
                                    · obtain ⟨hinv3, _⟩ := hs1 hc
                                      exact hJ_pr (c3, ext3, s3) m3 ⟨hcompat3, hinv3,
                                        fid_variant_fuel_lt hcomp3.max_vars hfu_pos
                                          (Nat.le_trans hfu3 hfu2_m1) hinv3, hm3⟩
                                  · exact hJnpb m2 rfl
                                  · exact hJnpb m2 rfl
                            · intro Jnp hJnp; c0_hsteps_nogrp
                              · refine fid_call_m7Rephase_inv rfl (hRephase _ _) hinv2f
                                  (fid_hdrMem_of_focus (by assumption)) ?_
                                intro s3 m3 hinv3 hfu3 hm3
                                c0_hsteps_nogrp
                                exact hJ_rp (c, ext, s3) m3 ⟨hcompat, hinv3,
                                  fid_variant_fuel_lt rfl hfu_pos (Nat.le_trans hfu3 hfu2_m1) hinv3,
                                  hm3⟩
                              · exact hJnp m2 rfl
                              · exact hJnp m2 rfl
                        · intro Jno hJno; c0_hsteps_nogrp
                          · refine fid_call_m4Reorder_inv rfl (hReorder _ _) hinv2f
                              (fid_hdrMem_of_focus (by assumption)) ?_
                            intro _r s3 m3 hinv3 hfu3 hm3
                            c0_hsteps_nogrp
                            exact hJs_ro (s2.scratch.conflicts + 10000#64 * (reord + 1#64),
                              reord + 1#64, c, ext, s3) m3 ⟨hcompat, hinv3,
                                fid_variant_fuel_lt rfl hfu_pos (by rw [hfu3]; exact hfu2_m1) hinv3,
                                hm3⟩
                          · exact hJno m2 rfl
                          · exact hJno m2 rfl

end SearchProof

/-! ## 6. Closed `26`-Row `fidSearchSpecTable`, `fidSearchEnv`, `TableImpl` & `ModuleOk` -/

section StandaloneModuleOk

private def fidSearchDefRows : List SpecEntry :=
  [ ⟨"full_bump_analyzed_fid", [i64], [], m6aBumpAnalyzedSpec, true⟩
  , ⟨"full_switch_mode_fid", [i64], [], m7SwitchModeSpec, true⟩
  , ⟨"m6_hdr_decide_fid", [i64], [i64], m6HdrDecideSpec, true⟩
  , ⟨"full_search_fid", [i64], [i64], fullM6SearchSpec, true⟩ ]

private def fidSearchExtRows : List SpecEntry :=
  [ ⟨"m6_hdr_dr_allow", [i64], [.bool], m6HdrDrAllowSpec, true⟩
  , ⟨"full_sort_ana_qs_m6", [i64, i64], [], m6SortAnaQsSpec, true⟩
  , ⟨"full_queue_mtf", [i64, i32], [], Full.fullQueueMtfSpec, true⟩
  , ⟨"full_bump_var", [i64, i32], [], Full.fullBumpVarSpec, true⟩
  , ⟨"full_bump_decay", [i64], [], Full.fullBumpDecaySpec, true⟩
  , ⟨"full_m7_set64", [i64, i64, i64], [], m7Set64Spec, true⟩
  , ⟨"full_ema_swap_m7", [i64, i64, i64], [], m7EmaSwapSpec, true⟩
  , ⟨"full_ilog10", [i64], [i64], Full.fullIlog10Spec, true⟩
  , ⟨"full_heap_down", [i64, i32], [], Full.fullHeapDownSpec, true⟩
  , ⟨"full_log10_q16_m7", [i64], [i64], m7Log10Q16Spec, true⟩
  , ⟨"full_decide_m7", [i64], [i64], m7DecideSpec, true⟩
  , ⟨"m6_hdr_dr_init", [i64], [], m6HdrDrMutSpec, true⟩
  , ⟨"full_lucky_late_m7", [i64], [i64], m7LuckyLateSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
  , ⟨"full_analyze_m6_hdr", [i64], [i64], m6HdrAnalyzeSpec, true⟩
  , ⟨"full_reduce_m6", [i64, .bool], [i64], m6ReduceSpec, true⟩
  , ⟨"full_switch_mode_m7", [i64], [], m7SwitchModeSpec, true⟩
  , ⟨"full_restart_due", [i64], [i64], Full.fullRestartDueSpec, true⟩
  , ⟨"full_restart", [i64], [], Full.fullRestartSpec, true⟩
  , ⟨"full_reorder_m6", [i64, i64], [i64], FullM4.m4ReorderSpec, true⟩
  , ⟨"full_rephase", [i64], [], m7RephaseSpec, true⟩
  , ⟨"full_simplify_m6", [i64, .bool, .bool], [i64], fullM6SimplifySpec, true⟩ ]

/-- Closed `26`-row specification table for `fidSearchModule` (`4` defined fns + `22` externs). -/
def fidSearchSpecTable : List SpecEntry := fidSearchDefRows ++ fidSearchExtRows

theorem fidSearchSpecTable_length : fidSearchSpecTable.length = 26 := by rfl

theorem fidSearchSpecTable_sigs :
    fidSearchSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      fidSearchModule.fns.map Fn.sig ++ fidSearchModule.externs.map Extern.sig := by rfl

theorem fidSearchSpecTable_nodup : (fidSearchSpecTable.map SpecEntry.name).Nodup := by
  have heq : fidSearchSpecTable.map SpecEntry.name =
      fidSearchModule.fns.map Fn.name ++ fidSearchModule.externs.map Extern.name := by rfl
  rw [heq]; decide

theorem fidSearchSpecTable_noExit : ∀ e ∈ fidSearchSpecTable, e.noExit = true :=
  fun e he => List.all_eq_true.mp (by rfl : fidSearchSpecTable.all (·.noExit) = true) e he

/-- Closed environment induced by `fidSearchSpecTable`. -/
def fidSearchEnv : Env := Env.ofTable fidSearchSpecTable

theorem fidSearchEnv_noExit : ∀ f as bs xs m Q X X',
    fidSearchEnv f as bs xs m Q X → fidSearchEnv f as bs xs m Q X' :=
  fun _ _ _ _ _ _ _ h => env_ofTable_noExit_all (by rfl) _ _ _ _ _ _ _ h

private theorem fidSearchEnv_row (idx : Nat) (e : SpecEntry)
    (hidx : fidSearchSpecTable[idx]? = some e) (xs : Tup Val e.as) (m : Mem 64) (Q : Post e.rs)
    (X : XPost) (hs : e.eff xs m Q X) : fidSearchEnv e.name e.as e.rs xs m Q X :=
  env_ofTable_row_at hidx fidSearchSpecTable_nodup hs

private theorem fid_erM {i : Nat} {n : Sym} {as rs : List Ty} {sp : Spec as rs}
    (h : fidSearchSpecTable[i]? = some ⟨n, as, rs, sp, true⟩)
    (hm : ∀ a m Q X, sp a m Q X → sp a m Q (fun _ _ _ _ => False) := by exact fun _ _ _ _ h => h) :
    ∀ a m Q X, sp a m Q X → fidSearchEnv n as rs a m Q X := fun a m Q X hs =>
  fidSearchEnv_noExit _ _ _ _ _ _ _ X
    (fidSearchEnv_row i ⟨n, as, rs, sp, true⟩ h a m Q (fun _ _ _ _ => False)
      (by dsimp only [SpecEntry.eff]; rw [ite_eq_left rfl]; exact hm a m Q X hs))

private theorem fid_env_bump_wp : ∀ xs m Q X, m6aBumpAnalyzedSpec xs m Q X →
    Func.wp fidSearchEnv full_bump_analyzed_fid_body xs m Q X :=
  full_bump_analyzed_fid_wp fidSearchEnv
    (fid_erM (i := 4) rfl (fun _ _ _ _ h => m6HdrDrAllowSpec_monoX h))
    (fid_erM (i := 5) rfl (fun _ _ _ _ h => m6SortAnaQsSpec_monoX h))
    (fid_erM (i := 6) rfl) (fid_erM (i := 7) rfl) (fid_erM (i := 8) rfl)

private theorem fid_env_switch_wp : ∀ xs m Q X, m7SwitchModeSpec xs m Q X →
    Func.wp fidSearchEnv full_switch_mode_fid_body xs m Q X :=
  full_switch_mode_fid_wp fidSearchEnv
    (fid_erM (i := 11) rfl) (fid_erM (i := 12) rfl)
    (fid_erM (i := 10) rfl (fun _ _ _ _ h => m7EmaSwapSpec_monoX h))
    (fid_erM (i := 13) rfl (fun _ _ _ _ h => m7Log10Q16Spec_monoX h))
    (fid_erM (i := 9) rfl (fun _ _ _ _ h => m7Set64Spec_monoX h))

private theorem fid_env_decide_wp : ∀ xs m Q X, m6HdrDecideSpec xs m Q X →
    Func.wp fidSearchEnv m6_hdr_decide_fid_body xs m Q X :=
  m6_hdr_decide_fid_wp fidSearchEnv
    (fid_erM (i := 14) rfl (fun _ _ _ _ h => m7DecideSpec_monoX h))
    (fid_erM (i := 15) rfl (fun _ _ _ _ h => m6HdrDrMutSpec_monoX h))

private theorem fid_env_search_wp : ∀ xs m Q X, fullM6SearchSpec xs m Q X →
    Func.wp fidSearchEnv full_search_fid_body xs m Q X :=
  full_search_fid_wp fidSearchEnv
    (fid_erM (i := 16) rfl (fun _ _ _ _ h => m7LuckyLateSpec_monoX h)) (fid_erM (i := 17) rfl)
    (fid_erM (i := 18) rfl (fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h))
    (fid_erM (i := 19) rfl (fun _ _ _ _ h => m6ReduceSpec_monoX h))
    (fid_erM (i := 20) rfl (fun _ _ _ _ h => m7SwitchModeSpec_monoX h))
    (fid_erM (i := 21) rfl) (fid_erM (i := 22) rfl) (fid_erM (i := 23) rfl)
    (fid_erM (i := 24) rfl (fun _ _ _ _ h => m7RephaseSpec_monoX h))
    (fid_erM (i := 25) rfl (fun _ _ _ _ h => fullM6SimplifySpec_monoX h))
    (fid_erM (i := 2) rfl (fun _ _ _ _ h => m6HdrDecideSpec_monoX h))

theorem fidBumpAnalyzedFn_impl : SpecEntry.Impl fidSearchEnv fidBumpAnalyzedFn
    ⟨"full_bump_analyzed_m6_hdr", [i64], [], m6aBumpAnalyzedSpec, true⟩ :=
  SpecEntry.Impl.of fid_env_bump_wp

theorem fidSwitchModeFn_impl : SpecEntry.Impl fidSearchEnv fidSwitchModeFn
    ⟨"full_switch_mode_m7", [i64], [], m7SwitchModeSpec, true⟩ :=
  SpecEntry.Impl.of fid_env_switch_wp

theorem fidHdrDecideFn_impl : SpecEntry.Impl fidSearchEnv fidHdrDecideFn
    ⟨"m6_hdr_decide_fid", [i64], [i64], m6HdrDecideSpec, true⟩ :=
  SpecEntry.Impl.of fid_env_decide_wp

theorem fidSearchM6Fn_impl : SpecEntry.Impl fidSearchEnv fidSearchM6Fn
    ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩ :=
  SpecEntry.Impl.of fid_env_search_wp

theorem fidSearch_tableImpl : TableImpl fidSearchEnv fidSearchFns fidSearchSpecTable :=
  ⟨ SpecEntry.Impl.of fid_env_bump_wp
  , SpecEntry.Impl.of fid_env_switch_wp
  , SpecEntry.Impl.of fid_env_decide_wp
  , SpecEntry.Impl.of fid_env_search_wp
  , trivial ⟩

/-- Closed `ModuleOk` for `fidSearchModule` (`4` defined functions + `22` externs). -/
theorem fidSearch_moduleOk : ModuleOk fidSearchEnv fidSearchModule :=
  Env.ofTable_moduleOk fidSearch_acyclic (FullM6ProofUtil.allFns_of_mem fidSearch_fns_wf)
    fidSearch_tableImpl

/-- `4`-row specification table aligned with `fidSearchPatchFns`. -/
def fidSearchPatchRows : List SpecEntry :=
  [ ⟨"full_bump_analyzed_m6_hdr", [i64], [], m6aBumpAnalyzedSpec, true⟩
  , ⟨"full_switch_mode_m7", [i64], [], m7SwitchModeSpec, true⟩
  , ⟨"m6_hdr_decide_fid", [i64], [i64], m6HdrDecideSpec, true⟩
  , ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩ ]

theorem fidSearchPatchRows_sigs :
    fidSearchPatchRows.map (fun e => (e.name, e.as, e.rs)) =
      fidSearchPatchFns.map Fn.sig := by rfl

theorem fidSearchPatchRows_noExit :
    fidSearchPatchRows.all SpecEntry.noExit = true := by rfl

theorem fidSearchPatch_tableImpl :
    TableImpl fidSearchEnv fidSearchPatchFns fidSearchPatchRows :=
  ⟨fidBumpAnalyzedFn_impl, fidSwitchModeFn_impl, fidHdrDecideFn_impl, fidSearchM6Fn_impl, trivial⟩

/-- Generic `TableImpl` lift for `fidSearchPatchFns` against `fidSearchPatchRows` under any `Γ`.
-/
theorem fidSearchPatch_tableImpl_of (Γ : Env)
    (hDrAllow : EnvSpec Γ "m6_hdr_dr_allow" m6HdrDrAllowSpec)
    (hSortAna : EnvSpec Γ "full_sort_ana_qs_m6" m6SortAnaQsSpec)
    (hQueueMtf : EnvSpec Γ "full_queue_mtf" Full.fullQueueMtfSpec)
    (hBumpVar : EnvSpec Γ "full_bump_var" Full.fullBumpVarSpec)
    (hBumpDecay : EnvSpec Γ "full_bump_decay" Full.fullBumpDecaySpec)
    (hSet64 : EnvSpec Γ "full_m7_set64" m7Set64Spec)
    (hEmaSwap : EnvSpec Γ "full_ema_swap_m7" m7EmaSwapSpec)
    (hIlog : EnvSpec Γ "full_ilog10" Full.fullIlog10Spec)
    (hHeapDown : EnvSpec Γ "full_heap_down" Full.fullHeapDownSpec)
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hDecideM7 : EnvSpec Γ "full_decide_m7" m7DecideSpec)
    (hDrInit : EnvSpec Γ "m6_hdr_dr_init" m6HdrDrMutSpec)
    (hLuckyLate : EnvSpec Γ "full_lucky_late_m7" m7LuckyLateSpec)
    (hProp : EnvSpec Γ "full_propagate" Full.fullPropagateSpec)
    (hAnalyze : EnvSpec Γ "full_analyze_m6_hdr" m6HdrAnalyzeSpec)
    (hReduce : EnvSpec Γ "full_reduce_m6" m6ReduceSpec)
    (hSwitch : EnvSpec Γ "full_switch_mode_m7" m7SwitchModeSpec)
    (hRstDue : EnvSpec Γ "full_restart_due" Full.fullRestartDueSpec)
    (hRst : EnvSpec Γ "full_restart" Full.fullRestartSpec)
    (hReorder : EnvSpec Γ "full_reorder_m6" FullM4.m4ReorderSpec)
    (hRephase : EnvSpec Γ "full_rephase" m7RephaseSpec)
    (hSimplify : EnvSpec Γ "full_simplify_m6" fullM6SimplifySpec)
    (hDecideFid : EnvSpec Γ "m6_hdr_decide_fid" m6HdrDecideSpec) :
    TableImpl Γ fidSearchPatchFns fidSearchPatchRows :=
  ⟨ SpecEntry.Impl.of (full_bump_analyzed_fid_wp Γ hDrAllow hSortAna hQueueMtf hBumpVar hBumpDecay)
  , SpecEntry.Impl.of (full_switch_mode_fid_wp Γ hIlog hHeapDown hEmaSwap hLog10 hSet64)
  , SpecEntry.Impl.of (m6_hdr_decide_fid_wp Γ hDecideM7 hDrInit)
  , SpecEntry.Impl.of (full_search_fid_wp Γ hLuckyLate hProp hAnalyze hReduce hSwitch hRstDue hRst
      hReorder hRephase hSimplify hDecideFid)
  , trivial ⟩

end StandaloneModuleOk

/-! ## 7. `FullM7` Splice (`411` fns) & `FullM7Splice.patchFns`/`patchRows` Integration -/

section SpliceIntegration

/-- `FullM7Splice.patchRows` replacement rows matching `fidSearchPatchRepls`. -/
def fidSearchPatchRowRepls : List SpecEntry :=
  [ ⟨"full_bump_analyzed_m6_hdr", [i64], [], m6aBumpAnalyzedSpec, true⟩
  , ⟨"full_switch_mode_m7", [i64], [], m7SwitchModeSpec, true⟩
  , ⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩ ]

/-- `FullM7Splice.patchRows` anchor-insertion rows matching `fidSearchPatchBefores`. -/
def fidSearchPatchRowBefores : List (Sym × List SpecEntry) :=
  [("full_search_m6", [⟨"m6_hdr_decide_fid", [i64], [i64], m6HdrDecideSpec, true⟩])]

private def fidPatchRowInsAt (befores : List (Sym × List SpecEntry)) (e : SpecEntry) :
    List SpecEntry :=
  (befores.filterMap fun (a, rs) => if a == e.name then some rs else none).flatten

private def fidPatchRows (repls : List SpecEntry) (befores : List (Sym × List SpecEntry))
    (tbl : List SpecEntry) : List SpecEntry :=
  tbl.flatMap fun e => fidPatchRowInsAt befores e ++ [(repls.find? (·.name == e.name)).getD e]

/-- `411`-function `FullM7` list patched with `fidSearchPatchRepls` and `fidSearchPatchBefores`. -/
def fidSearchSplicedFns : List Fn :=
  fidPatchFns fidSearchPatchRepls fidSearchPatchBefores m7Fns

/-- Closed `411`-function `FullM7 + FullM7FidelitySearch` module (`externs := []`, `exits := []`).
-/
def fidSearchSplicedModule : LeanQbe.T.Module :=
  { m7Module with fns := fidSearchSplicedFns }

/-- `411`-row specification table aligned 1-to-1 with `fidSearchSplicedFns`. -/
def fidSearchSplicedTable (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) :
    List SpecEntry :=
  fidPatchRows fidSearchPatchRowRepls fidSearchPatchRowBefores (m7SpecTable tBve solveSpec)

/-- Closed `Env` extending `mkM7Env tBve solveSpec` with `"m6_hdr_decide_fid"`. -/
def fidSearchSplicedEnv (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64] := fullM6SolveBytesSpec) : Env :=
  fun f as bs xs m Q X =>
    if f = "m6_hdr_decide_fid" then
      ∃ (ha : [i64] = as) (hb : [i64] = bs),
        m6HdrDecideSpec (ha ▸ xs) m (hb ▸ Q) (fun _ _ _ _ => False)
    else mkM7Env tBve solveSpec f as bs xs m Q X

private theorem fid_fn_find_name {repls : List Fn} {nm : Sym} {r : Fn}
    (h : repls.find? (fun x => x.name == nm) = some r) : r.name = nm :=
  beq_iff_eq.mp (List.find?_some (p := fun x : Fn => x.name == nm) h)

private theorem fid_row_find_name {repls : List SpecEntry} {nm : Sym} {r : SpecEntry}
    (h : repls.find? (fun x => x.name == nm) = some r) : r.name = nm :=
  beq_iff_eq.mp (List.find?_some (p := fun x : SpecEntry => x.name == nm) h)

private theorem fid_mem_insAt {befores : List (Sym × List Fn)} {g fn : Fn}
    (h : fn ∈ fidPatchInsAt befores g) : ∃ hs, (g.name, hs) ∈ befores ∧ fn ∈ hs := by
  unfold fidPatchInsAt at h
  rcases List.mem_flatten.mp h with ⟨hs, hhs, hfn⟩
  rcases List.mem_filterMap.mp hhs with ⟨⟨a, hs0⟩, hm, hif⟩
  cases hcmp : (a == g.name)
  · simp [hcmp] at hif
  · have ha : a = g.name := beq_iff_eq.mp hcmp
    subst ha; simp at hif; subst hif; exact ⟨hs0, hm, hfn⟩

private theorem fid_mem_rowInsAt {befores : List (Sym × List SpecEntry)} {e₀ e : SpecEntry}
    (h : e ∈ fidPatchRowInsAt befores e₀) : ∃ rs, (e₀.name, rs) ∈ befores ∧ e ∈ rs := by
  unfold fidPatchRowInsAt at h
  rcases List.mem_flatten.mp h with ⟨rs, hrs, he⟩
  rcases List.mem_filterMap.mp hrs with ⟨⟨a, rs0⟩, hm, hif⟩
  cases hcmp : (a == e₀.name)
  · simp [hcmp] at hif
  · have ha : a = e₀.name := beq_iff_eq.mp hcmp
    subst ha; simp at hif; subst hif; exact ⟨rs0, hm, he⟩

private theorem fid_patchRows_sigs {replsR : List SpecEntry}
    {beforesR : List (Sym × List SpecEntry)} {replsF : List Fn} {beforesF : List (Sym × List Fn)} :
    ∀ (tbl : List SpecEntry) (fs : List Fn),
    tbl.map (fun e => (e.name, e.as, e.rs)) = fs.map Fn.sig →
    (∀ r ∈ replsR, ∀ e ∈ tbl, r.name = e.name →
      (r.name, r.as, r.rs) = (e.name, e.as, e.rs)) →
    (∀ r ∈ replsF, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) →
    (∀ e ∈ tbl, ∀ f ∈ fs, e.name = f.name →
      (fidPatchRowInsAt beforesR e).map (fun r => (r.name, r.as, r.rs)) =
        (fidPatchInsAt beforesF f).map Fn.sig) →
    (fidPatchRows replsR beforesR tbl).map (fun e => (e.name, e.as, e.rs)) =
      (fidPatchFns replsF beforesF fs).map Fn.sig
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => by simp at h
  | e :: ts, f :: fs, hsig, hsr, hsf, hins => by
    simp only [List.map_cons, List.cons.injEq] at hsig
    rcases hsig with ⟨hef, hts⟩
    have hrow : ((replsR.find? (fun x => x.name == e.name)).getD e).name = e.name ∧
        (((replsR.find? (fun x => x.name == e.name)).getD e).as,
          ((replsR.find? (fun x => x.name == e.name)).getD e).rs) = (e.as, e.rs) := by
      cases h : replsR.find? (fun x => x.name == e.name) with
      | none => exact ⟨rfl, rfl⟩
      | some r =>
        dsimp only [Option.getD]
        have heq := hsr r (List.mem_of_find?_eq_some h) e List.mem_cons_self (fid_row_find_name h)
        exact ⟨congrArg Prod.fst heq,
          Prod.ext (congrArg (fun p => p.2.1) heq) (congrArg (fun p => p.2.2) heq)⟩
    have hfn : ((replsF.find? (fun x => x.name == f.name)).getD f).sig = f.sig := by
      cases h : replsF.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r =>
        exact hsf r (List.mem_of_find?_eq_some h) f List.mem_cons_self (fid_fn_find_name h)
    have ih := fid_patchRows_sigs (replsR := replsR) (beforesR := beforesR)
      (replsF := replsF) (beforesF := beforesF) ts fs hts
      (fun r hr e' he' => hsr r hr e' (List.mem_cons_of_mem e he'))
      (fun r hr f' hf' => hsf r hr f' (List.mem_cons_of_mem f hf'))
      (fun e' he' f' hf' => hins e' (List.mem_cons_of_mem e he') f' (List.mem_cons_of_mem f hf'))
    unfold fidPatchRows fidPatchFns at ih
    simp only [fidPatchRows, fidPatchFns, List.flatMap_cons, List.map_append, List.map_cons,
      List.map_nil]
    rw [hins e List.mem_cons_self f List.mem_cons_self (congrArg Prod.fst hef), ih]
    rw [show (((replsR.find? (fun x => x.name == e.name)).getD e).name,
        ((replsR.find? (fun x => x.name == e.name)).getD e).as,
        ((replsR.find? (fun x => x.name == e.name)).getD e).rs) =
        ((replsF.find? (fun x => x.name == f.name)).getD f).sig by
      rw [hfn, ← hef]; exact Prod.ext hrow.1 hrow.2]

private theorem fid_idx_118 : m7Fns[118]?.map Fn.sig =
    some ("full_bump_analyzed_m6_hdr", [i64], []) := by
  rw [show (118 : Nat) = 112 + 6 by rfl, m7_get_p2 (by decide)]; t_kernel_rfl
private theorem fid_idx_399 : m7Fns[399]?.map Fn.sig =
    some ("full_switch_mode_m7", [i64], []) := by
  rw [show (399 : Nat) = 276 + 123 by rfl, m7_get_p3]; t_kernel_rfl
private theorem fid_idx_405 : m7Fns[405]?.map Fn.sig =
    some ("full_search_m6", [i64], [i64]) := by
  rw [show (405 : Nat) = 276 + 129 by rfl, m7_get_p3]; t_kernel_rfl

private theorem fid_repls_sig :
    ∀ r ∈ fidSearchPatchRepls, ∀ f ∈ m7Fns, r.name = f.name → r.sig = f.sig := by
  obtain ⟨f118, hf118, hs118⟩ := sig_of_map_idx fid_idx_118
  obtain ⟨f399, hf399, hs399⟩ := sig_of_map_idx fid_idx_399
  obtain ⟨f405, hf405, hs405⟩ := sig_of_map_idx fid_idx_405
  intro r hr f hf hnm
  simp only [fidSearchPatchRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf118
      (hnm.symm.trans (congrArg Prod.fst hs118.symm))
    subst hf0; exact hs118.symm
  · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf399
      (hnm.symm.trans (congrArg Prod.fst hs399.symm))
    subst hf0; exact hs399.symm
  · have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf405
      (hnm.symm.trans (congrArg Prod.fst hs405.symm))
    subst hf0; exact hs405.symm

private theorem fid_decide_fid_not_in_m7_all :
    ("m6_hdr_decide_fid" : Sym) ∉
      (m7Fns.map Fn.name ++ m7Module.externs.map Extern.name) := by
  have h : (m7Fns.map Fn.name ++ m7Module.externs.map Extern.name).contains
      "m6_hdr_decide_fid" = false := by t_kernel_rfl
  intro hm; have hmem := List.contains_iff_mem.mpr hm; rw [hmem] at h; cases h

theorem fidSearchSpliced_acyclic : fidSearchSplicedModule.checkAcyclic = true := by
  t_kernel_rfl

theorem fidSearchSpliced_names_nodup : (fidSearchSplicedFns.map Fn.name).Nodup := by
  have hchk := fidSearchSpliced_acyclic
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hchk
  have hnd := LeanQbe.T.Module.namesNodup_of_checkNamesNodup hchk.1
  change (fidSearchSplicedFns.map Fn.name ++ ([] : List Extern).map Extern.name).Nodup at hnd
  simpa only [List.map_nil, List.append_nil] using hnd

theorem fidSearchSplicedTable_sigs (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig) :
    (fidSearchSplicedTable tBve solveSpec).map (fun e => (e.name, e.as, e.rs)) =
      fidSearchSplicedFns.map Fn.sig := by
  refine fid_patchRows_sigs (m7SpecTable tBve solveSpec) m7Fns
    (m7SpecTable_sigs tBve solveSpec hBveSigs) ?_ fid_repls_sig ?_
  · intro r hr e he hnm
    have he' : (e.name, e.as, e.rs) ∈
        (m7SpecTable tBve solveSpec).map (fun x => (x.name, x.as, x.rs)) :=
      List.mem_map.mpr ⟨e, he, rfl⟩
    rw [m7SpecTable_sigs tBve solveSpec hBveSigs] at he'
    rcases List.mem_map.mp he' with ⟨f, hf, hsigf⟩
    simp only [fidSearchPatchRowRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨f118, hf118, hs118⟩ := sig_of_map_idx fid_idx_118
      have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf118
        ((congrArg Prod.fst hsigf).trans (hnm.symm.trans (congrArg Prod.fst hs118.symm)))
      subst hf0; rw [← hsigf, hs118]
    · obtain ⟨f399, hf399, hs399⟩ := sig_of_map_idx fid_idx_399
      have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf399
        ((congrArg Prod.fst hsigf).trans (hnm.symm.trans (congrArg Prod.fst hs399.symm)))
      subst hf0; rw [← hsigf, hs399]
    · obtain ⟨f405, hf405, hs405⟩ := sig_of_map_idx fid_idx_405
      have hf0 := fn_eq_of_mem_idx m7_names_nodup hf hf405
        ((congrArg Prod.fst hsigf).trans (hnm.symm.trans (congrArg Prod.fst hs405.symm)))
      subst hf0; rw [← hsigf, hs405]
  · intro e _ f _ hnm
    dsimp only [fidPatchRowInsAt, fidPatchInsAt, fidSearchPatchRowBefores, fidSearchPatchBefores]
    rw [hnm]
    by_cases heq : ("full_search_m6" == f.name) = true
    · simp only [List.filterMap, heq, ↓reduceIte]; rfl
    · simp only [List.filterMap, heq, Bool.false_eq_true, ↓reduceIte]; rfl

/-- Opaque host rows from `m7SpecTable` not yet individually exported from `FullM7Proof`. -/
structure M7FidSearchHostRows (tbl : List SpecEntry) : Prop where
  bumpAnalyzed :
    (⟨"full_bump_analyzed_m6_hdr", [i64], [], m6aBumpAnalyzedSpec, true⟩ : SpecEntry) ∈ tbl
  searchM6 : (⟨"full_search_m6", [i64], [i64], fullM6SearchSpec, true⟩ : SpecEntry) ∈ tbl
  sortAnaQs :
    (⟨"full_sort_ana_qs_m6", [i64, i64], [], m6SortAnaQsSpec, true⟩ : SpecEntry) ∈ tbl
  set64 : (⟨"full_m7_set64", [i64, i64, i64], [], m7Set64Spec, true⟩ : SpecEntry) ∈ tbl
  emaSwap : (⟨"full_ema_swap_m7", [i64, i64, i64], [], m7EmaSwapSpec, true⟩ : SpecEntry) ∈ tbl

private theorem fid_mkM7Env_to_spliced {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]} {f : Sym} {as bs : List Ty}
    (hne : f ≠ "m6_hdr_decide_fid") {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : mkM7Env tBve solveSpec f as bs xs m Q X) :
    fidSearchSplicedEnv tBve solveSpec f as bs xs m Q X := by
  dsimp only [fidSearchSplicedEnv]; rw [ite_eq_right hne]; exact h

private theorem fid_spliced_row_mem {tBve : List SpecEntry}
    {solveSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hnd : ((m7SpecTable tBve solveSpec).map SpecEntry.name).Nodup)
    (f : Sym) (as bs : List Ty) (sp : Spec as bs) (hne : f ≠ "m6_hdr_decide_fid")
    (hmem : (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7SpecTable tBve solveSpec)
    (hm : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ xs m Q X, sp xs m Q X → fidSearchSplicedEnv tBve solveSpec f as bs xs m Q X :=
  fun xs m Q X hs =>
    fid_mkM7Env_to_spliced hne (mkM7Env_row_mem hnd f as bs sp hmem hm xs m Q X hs)

/-- `ModuleOk` for `fidSearchSplicedModule` (`411` fns: `FullM7` + `FullM7FidelitySearch`),
inheriting all `407` untouched functions from `mkM7Env_moduleOk`. -/
theorem fidSearchSpliced_moduleOk
    (tBve : List SpecEntry)
    (solveSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hWeaken : ∀ a m Q X, solveSpec a m Q X → fullM6SolveBytesCoreModelSpec a m Q X)
    (hSolveMonoX : ∀ a m Q X X', solveSpec a m Q X → solveSpec a m Q X')
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve solveSpec) m7BveAllFns tBve)
    (hHost : M7FidSearchHostRows (m7SpecTable tBve solveSpec)) :
    ModuleOk (fidSearchSplicedEnv tBve solveSpec) fidSearchSplicedModule := by
  have hm :=
    mkM7Env_moduleOk tBve solveSpec hWeaken hSolveMonoX hBveSigs hBveNoExit hBveSpecs hBveOk
  have hnd0 := m7SpecTable_nodup tBve solveSpec hBveSigs
  have hc1 := m7Part1Callees_of_sub
    (fun e he => m7SpecTable_part1_mem (tBve := tBve) (solveSpec := solveSpec) e he)
  have hc2 := m7Part2Callees_of_sub
    (fun e he => m7SpecTable_part2_mem (tBve := tBve) (solveSpec := solveSpec) e he)
  have hc3 := m7Part3TailCallees_of_sub
    (fun e he => m7SpecTable_part3Pfx_mem (tBve := tBve) (solveSpec := solveSpec) e he)
  have hPfx := m7OrchPfxRows_specs
  have hDecRow : EnvSpec (fidSearchSplicedEnv tBve solveSpec) "m6_hdr_decide_fid" m6HdrDecideSpec :=
    fun xs m Q X hs => by
      dsimp only [fidSearchSplicedEnv]; rw [ite_eq_left rfl]
      exact ⟨rfl, rfl, m6HdrDecideSpec_monoX hs⟩
  have hwfOrig : ∀ f ∈ m7Module.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf; exact (hm.fnsOk pre f post hsplit).1
  have hwfSpl : ∀ f ∈ fidSearchSplicedModule.fns, f.Wf := fun fn hfn => by
    rcases List.mem_flatMap.mp hfn with ⟨g, hg, hmem⟩
    rcases List.mem_append.mp hmem with h_ins | h_rep
    · rcases fid_mem_insAt h_ins with ⟨hs, hm_b, hfn_hs⟩
      exact fidSearchPatchBefores_wf (g.name, hs) hm_b fn hfn_hs
    · rcases List.mem_singleton.mp h_rep with rfl
      cases h : fidSearchPatchRepls.find? (fun x => x.name == g.name) with
      | none => exact hwfOrig g hg
      | some r => exact fidSearchPatchRepls_wf r (List.mem_of_find?_eq_some h)
  refine LeanQbe.T.Module.moduleOk_of_checkAcyclic fidSearchSpliced_acyclic hwfSpl ?_
  intro fn hmem
  rcases List.mem_flatMap.mp hmem with ⟨g, hg, hmem_g⟩
  rcases List.mem_append.mp hmem_g with h_ins | h_rep
  · rcases fid_mem_insAt h_ins with ⟨hs, hm_b, hfn_hs⟩
    simp only [fidSearchPatchBefores, List.mem_singleton] at hm_b
    cases (Prod.mk.inj hm_b).2
    simp only [List.mem_singleton] at hfn_hs; subst hfn_hs
    intro xs m Q X hspec
    dsimp only [fidSearchSplicedEnv, fidHdrDecideFn] at hspec; rw [ite_eq_left rfl] at hspec
    rcases hspec with ⟨_, _, hs'⟩
    exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
      (m6_hdr_decide_fid_wp (fidSearchSplicedEnv tBve solveSpec)
        (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc3.decideM7
          (fun _ _ _ _ h => m7DecideSpec_monoX h))
        (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc1.hdrDrInit
          (fun _ _ _ _ h => m6HdrDrMutSpec_monoX h))
        xs m Q _ hs')
  · rcases List.mem_singleton.mp h_rep with rfl
    have hg_ne : g.name ≠ "m6_hdr_decide_fid" := fun hne =>
      fid_decide_fid_not_in_m7_all (List.mem_append_left _ (hne ▸ List.mem_map_of_mem hg))
    cases h : fidSearchPatchRepls.find? (fun x => x.name == g.name) with
    | some r =>
      dsimp only [Option.getD]
      have hr := List.mem_of_find?_eq_some h
      simp only [fidSearchPatchRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
      intro xs m Q X hs
      rcases hr with rfl | rfl | rfl
      · dsimp only [fidSearchSplicedEnv, fidBumpAnalyzedFn] at hs
        rw [ite_eq_right (by decide)] at hs
        have hs' := mkM7Env_elim_of_mem hHost.bumpAnalyzed hnd0 hs
        dsimp only [SpecEntry.eff] at hs'; rw [ite_eq_left rfl] at hs'
        exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
          (full_bump_analyzed_fid_wp (fidSearchSplicedEnv tBve solveSpec)
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc1.hdrDrAllow
              (fun _ _ _ _ h => m6HdrDrAllowSpec_monoX h))
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hHost.sortAnaQs
              (fun _ _ _ _ h => m6SortAnaQsSpec_monoX h))
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc1.queueMtf)
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc1.bumpVar)
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc1.bumpDecay) xs m Q _ hs')
      · dsimp only [fidSearchSplicedEnv, fidSwitchModeFn] at hs
        rw [ite_eq_right (by decide)] at hs
        have hs' := mkM7Env_elim_of_mem hc3.switchModeM7 hnd0 hs
        dsimp only [SpecEntry.eff] at hs'; rw [ite_eq_left rfl] at hs'
        exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
          (full_switch_mode_fid_wp (fidSearchSplicedEnv tBve solveSpec)
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc1.ilog10)
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc1.heapDown)
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hHost.emaSwap
              (fun _ _ _ _ h => m7EmaSwapSpec_monoX h))
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc1.log10Q16M7
              (fun _ _ _ _ h => m7Log10Q16Spec_monoX h))
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hHost.set64
              (fun _ _ _ _ h => m7Set64Spec_monoX h)) xs m Q _ hs')
      · dsimp only [fidSearchSplicedEnv, fidSearchM6Fn] at hs
        rw [ite_eq_right (by decide)] at hs
        have hs' := mkM7Env_elim_of_mem hHost.searchM6 hnd0 hs
        dsimp only [SpecEntry.eff] at hs'; rw [ite_eq_left rfl] at hs'
        exact wp_mono (fun _ _ h => h) (fun _ _ _ _ (h : False) => h.elim) _ m
          (full_search_fid_wp (fidSearchSplicedEnv tBve solveSpec)
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc3.luckyLateM7
              (fun _ _ _ _ h => m7LuckyLateSpec_monoX h))
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc1.propagate)
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc2.analyzeM6
              (fun _ _ _ _ h => m6HdrAnalyzeSpec_monoX h))
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide)
              (m7SpecTable_pfx_mem _ hPfx.reduceM6) (fun _ _ _ _ h => m6ReduceSpec_monoX h))
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc3.switchModeM7
              (fun _ _ _ _ h => m7SwitchModeSpec_monoX h))
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc2.restartDue)
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc2.restart)
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide)
              (m7SpecTable_pfx_mem _ hPfx.reorderM6))
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide) hc2.rephase
              (fun _ _ _ _ h => m7RephaseSpec_monoX h))
            (fid_spliced_row_mem hnd0 _ _ _ _ (by decide)
              (m7SpecTable_pfx_mem _ hPfx.simplifyM6) (fun _ _ _ _ h => fullM6SimplifySpec_monoX h))
            hDecRow xs m Q _ hs')
    | none =>
      dsimp only [Option.getD]
      intro xs m Q X hgf
      dsimp only [fidSearchSplicedEnv] at hgf; rw [ite_eq_right hg_ne] at hgf
      obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
      have ⟨hwfG, hcallsG, hwpG⟩ := hm.fnsOk pre g post hsplit
      exact wp_env_agree_of_callsOk
        (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units g.as))
        hcallsG (fun f as bs hf_all xs m Q X hf => by
          have hf_ne : f ≠ "m6_hdr_decide_fid" := fun hnm => by
            apply fid_decide_fid_not_in_m7_all
            rcases List.mem_append.mp hf_all with hp | he
            · obtain ⟨f₀, hf₀, hs₀⟩ := List.mem_map.mp hp
              have hf₀_m7 : f₀ ∈ m7Fns := hsplit ▸ List.mem_append_left (g :: post) hf₀
              have hfn : f = f₀.name := (congrArg Prod.fst hs₀).symm
              subst hfn; rw [← hnm]; exact List.mem_append_left _ (List.mem_map_of_mem hf₀_m7)
            · obtain ⟨e₀, he₀, hs₀⟩ := List.mem_map.mp he
              have hen : f = e₀.name := (congrArg Prod.fst hs₀).symm
              subst hen; rw [← hnm]; exact List.mem_append_right _ (List.mem_map_of_mem he₀)
          exact fid_mkM7Env_to_spliced hf_ne hf)
        m (hwpG xs m Q X hgf)

private theorem fidSearchSpliced_solveBytes_mem :
    m6oSolveBytesFn ∈ fidSearchSplicedModule.fns := by
  refine List.mem_flatMap.mpr ⟨m6oSolveBytesFn, m7oSolveBytesFn_mem, List.mem_append_right _ ?_⟩
  cases h : fidSearchPatchRepls.find? (fun x => x.name == m6oSolveBytesFn.name) with
  | none => exact List.mem_singleton_self _
  | some r =>
    have hr := List.mem_of_find?_eq_some h
    have hn : r.name = m6oSolveBytesFn.name := fid_fn_find_name h
    simp only [fidSearchPatchRepls, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [fidBumpAnalyzedFn, fidSwitchModeFn, fidSearchM6Fn,
      m6oSolveBytesFn] at hn

/-- Top-level `kissat_solve_bytes` soundness for `fidSearchSplicedModule` (`411` fns). -/
theorem fidSearchSpliced_solve_bytes_sound
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesSpec) m7BveAllFns tBve)
    (hHost : M7FidSearchHostRows (m7SpecTable tBve fullM6SolveBytesSpec))
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp (fidSearchSplicedEnv tBve fullM6SolveBytesSpec)
      FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  spliceModule_solve_bytes_sound
    (fidSearchSpliced_moduleOk tBve fullM6SolveBytesSpec
      (fun _ _ _ _ h => fullM6SolveBytesCoreModelSpec_of_spec h)
      (fun _ _ _ _ _ h => fullM6SolveBytesSpec_monoX h)
      hBveSigs hBveNoExit hBveSpecs hBveOk hHost)
    fidSearchSpliced_solveBytes_mem
    (fun _ _ _ _ hs => fid_mkM7Env_to_spliced (by decide)
      ((mkM7Env_solve_bytes_iff tBve fullM6SolveBytesSpec hBveSigs).mpr
        (fullM6SolveBytesSpec_monoX hs)))
    hcfit hwfit hm

/-- Concrete deterministic UNSAT non-vacuity (`XPost := False`, `r = 20#64`) for
`fidSearchSplicedModule` (`411` fns). -/
theorem fidSearchSpliced_unsat_nv
    (tBve : List SpecEntry)
    (hBveSigs : tBve.map (fun e => (e.name, e.as, e.rs)) = m7BveAllFns.map Fn.sig)
    (hBveNoExit : tBve.all SpecEntry.noExit = true)
    (hBveSpecs : M7BveAllTblSpecs tBve)
    (hBveOk : TableImpl (mkM7Env tBve fullM6SolveBytesCoreModelSpec) m7BveAllFns tBve)
    (hHost : M7FidSearchHostRows (m7SpecTable tBve fullM6SolveBytesCoreModelSpec)) :
    Func.wp (fidSearchSplicedEnv tBve fullM6SolveBytesCoreModelSpec)
      FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  spliceModule_unsat_nv
    (fidSearchSpliced_moduleOk tBve fullM6SolveBytesCoreModelSpec
      (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => fullM6SolveBytesCoreModelSpec_monoX h)
      hBveSigs hBveNoExit hBveSpecs hBveOk hHost)
    fidSearchSpliced_solveBytes_mem
    (fun _ _ _ _ hs => fid_mkM7Env_to_spliced (by decide)
      ((mkM7Env_solve_bytes_iff tBve fullM6SolveBytesCoreModelSpec hBveSigs).mpr
        (fullM6SolveBytesCoreModelSpec_monoX hs)))

end SpliceIntegration

/-! ## 8. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteNonVacuity

private theorem nvFs_unsat : nvOneLitF0.Unsat := by
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

private theorem nvFs_sparseW :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl; have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hr0 : ∀ r, r ∈ fullArenaClauseRefsCore nvOneLitState.core → False := fun _ hr => by
    rw [show fullArenaClauseRefsCore nvOneLitState.core = [] from rfl] at hr; cases hr
  have hi0 : ∀ i, i < nvOneLitState.core.trail_end → i = 0 := fun _ hi => by rw [hte] at hi; omega
  have hL0 : ∀ L, L ≤ nvOneLitState.core.cur_level → L = 0 := fun _ hL => by rw [hcl] at hL; omega
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact .empty)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, nvOneLitState] at hp
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) :=
    CNF.entails_clause_def.mpr fun _ hα =>
      (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim,
        fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hi0 i hi]; decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hi0 i hi, hi0 j hj]
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hi0 i hi]; exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hp => by rw [hi0 j hj] at hp; exact absurd hp.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hi0 i hi]; exact hent0
      trail_pos_inv := fun i hi => by rw [hi0 i hi]; rfl
      level0_rsn_none := fun i hi _ => by rw [hi0 i hi]; rfl
      frame_trail_lt := fun L hL => by rw [hL0 L hL]; decide
      frame_trail_mono := fun L1 L2 h12 hL2 => by
        rw [hL0 L1 (by omega), hL0 L2 hL2]; exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => absurd rfl (hi0 i hi ▸ hne)
      reason_lit_mem := fun i hi hne => absurd rfl (hi0 i hi ▸ hne) }
  refine ⟨nvOneLit_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => (hr0 r hr).elim,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by simp only [nvOneLitState, nvOneLitScratch,
      List.getElem?_replicate, show i < 16 by omega, ↓reduceIte, Option.getD_some],
      Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

private theorem nvFs_mem_emp : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
  rw [sep_emp]; exact nvOneLitMem_ok

private theorem nvFs_hdrMem_emp :
    (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
  rw [sep_emp]; exact nvM6HdrMem_ok

private theorem nvFs_anaCov : FullAnaMarksCov nvOneLitCfg nvOneLitState := by
  refine ⟨by decide, by decide, fun k hk => ?_, fun v hv hnz => ?_⟩
  · have : k < 0 := hk; omega
  · exfalso; apply hnz
    have hmv : nvOneLitCfg.max_vars = 1 := rfl
    rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bump_analyzed_fid`. -/
theorem nv_fid_bump_analyzed :
    Func.wp fidSearchEnv full_bump_analyzed_fid_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun () m' => ∃ mrk' mcl' sc' ext',
        let c' : FullCoreState :=
          { nvOneLitState.core with mrk := mrk', min_clr_len := mcl' }
        let s' : FullState := { nvOneLitState with core := c', scratch := sc' }
        s'.LengthsOk nvOneLitCfg ∧ FullAnaMarksCov nvOneLitCfg s' ∧ M6HdrExtOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  fidBumpAnalyzedFn_impl.2 _ _ _ _
    (m6aBumpAnalyzedSpec_of nvM6HdrCfg_ok nvM6ExtWords_ok nvOneLit_lengths nvFs_anaCov
      nvFs_hdrMem_emp fun mrk' mcl' sc' ext' m' hlen' hcov' _ _ hext' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨mrk', mcl', sc', ext', hlen', hcov', hext', nvFs_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_switch_mode_fid`. -/
theorem nv_fid_switch_mode :
    Func.wp fidSearchEnv full_switch_mode_fid_body (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun () m' => ∃ s' : FullState,
        s'.core = nvOneLitState.core ∧ s'.LengthsOk nvOneLitCfg ∧
        FullProbeScratchPres nvOneLitState s' ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  fidSwitchModeFn_impl.2 _ _ _ _
    (m7SwitchModeSpec_of nvOneLit_lengths nvFs_mem_emp
      fun s' m' hc hlen hps _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hc, hlen, hps, nvFs_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `m6_hdr_decide_fid`. -/
theorem nv_fid_hdr_decide :
    Func.wp fidSearchEnv m6_hdr_decide_fid_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl'
          sc' ext',
        let s' : FullState :=
          { core := { nvOneLitState.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', frame_trail := ftrl', frame_dec := fdec', trail_end := te',
              cur_level := cl', unassigned := unass', unflushed := unfl' }
            scratch := sc' }
        FullM6HdrCoreInv nvOneLitCfg nvOneLitF0 ext' s' ∧ (r = 0#64 ∨ r = 1#64) ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  fidHdrDecideFn_impl.2 _ _ _ _
    (m6HdrDecideSpec_of (fullM6HdrInv_to_coreInv (FullM6HdrInvW.mk_inv nvM6HdrCfg_ok
        nvM6ExtWords_ok nvFs_sparseW).toInv) nvFs_hdrMem_emp
      fun r _ _ _ _ _ _ _ _ _ _ _ _ _ ext' m' hinv' _ hr _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ext', hinv', hr,
          nvFs_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_search_fid`. -/
theorem nv_fid_search :
    Func.wp fidSearchEnv full_search_fid_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ c' ext' s',
        FullM4Compact.FullCfgCompat nvOneLitCfg c' ∧ s'.LengthsOk c' ∧
        FullM6HdrCfgOk c' ∧ M6HdrExtOk ext' ∧ (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → nvOneLitF0.Unsat) ∧ FullM6HdrMem c' ext' s' m')
      (fun _ _ _ _ => False) :=
  fidSearchM6Fn_impl.2 _ _ _ _
    (fullM6SearchSpec_of (FullM6HdrInvW.mk_inv nvM6HdrCfg_ok nvM6ExtWords_ok nvFs_sparseW).toInv
      rfl nvFs_hdrMem_emp fun r c' ext' s' m' hcmp hlen hcfg hext hr hu _ hm' => by
        rw [sep_emp] at hm'; exact ⟨c', ext', s', hcmp, hlen, hcfg, hext, hr, hu, hm'⟩)

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM7FidelitySearch
