/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep7
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0b
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3b
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof6
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
import all LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0b
import all LeanQbe.T.Examples.Kissat.FullM6BveFwdProof6
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 7 Proofs — Shard 1a (`FullFidelityStep7Proof1a`)

Parametric `(Γ : Env)` UNSAT-only `Func.wp` proofs (`public section`, `XPost`-polymorphic,
`std3` axioms only, `0` SAT model proofs) for items `1..7` of Shard 1:
1. `fidStep7SortBinWatchesFn` (`full_sort_bin_watches_fid`) -> `step7SortBinWatchesSpec`
2. `fidStep7RebuildWatchesFn` (`full_rebuild_watches`) -> `Full.fullRebuildWatchesSpec`
3. `fidStep7VivifyTierM6HdrFn` (`full_vivify_tier_m6_hdr`) -> `FullM6OrchAdapters.m6aVivifyTierSpec`
4. `fidStep7VivifyM6HdrFn` (`full_vivify_m6_hdr`) -> `FullM6OrchAdapters.m6aVivifySpec`
5. `fidStep7BveVarKeyM7Fn` (`full_bve_var_key_m7`) -> `FullM6BveFwd.fullBveVarKeyM6Spec`
   (and `FullM8CoreParity.m8BveVarKeySpec`)
6. `fidStep7EliminateM7Fn` (`full_eliminate_m7`) -> `FullFastSched.schedEliminateSpec`
7. `fidStep7EliminateM6Fn` (`full_eliminate_m6`) -> `FullFastSched.schedEliminateSpec`
-/

set_option autoImplicit false

local elab "s7_steps_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "s7_to_group_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local macro "s7_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep7

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open LeanQbe.T.Examples.Kissat.FullM3Backbone
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM4
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open FullVivTopTactics
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullVivTopTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

/-! ## 1. `step7SortBinWatchesSpec`, `WatchSliceOk.of_bin_perm` & `full_sort_bin_watches_fid` -/

/-- Contract for `full_sort_bin_watches_fid(h)`: in-place Knuth Shellsort of every literal's
binary watch prefix `[off, off+bn)`, preserving `FullSparseInvW`, `WatchesInv`, `core` (all
fields except `wstk`), arena, scratch, and `wstk.length = c.wcap` (`XPost`-polymorphic). -/
@[expose] def step7SortBinWatchesSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (wstk' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with core := { s.core with wstk := wstk' } }
      wstk'.length = c.wcap →
      FullSparseInvW c F0 F_cur s' →
      WatchesInv F_cur s'.core →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem step7SortBinWatchesSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : step7SortBinWatchesSpec xs m Q X) :
    step7SortBinWatchesSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step7SortBinWatchesSpec_noExit :
    ∀ xs m Q X, step7SortBinWatchesSpec xs m Q X →
      step7SortBinWatchesSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step7SortBinWatchesSpec_monoX h

/-- Single binary watch word validity predicate relative to `(F_cur, cur_vars, lit)`. -/
private def BinWatchWordOk (F_cur : List (List Nat)) (cur_vars lit : Nat) (w : BitVec 32) : Prop :=
  (w &&& 0x80000000#32) ≠ 0#32 ∧ w ≠ 0xFFFFFFFF#32 ∧
  (w &&& 0x7FFFFFFF#32).toNat < 2 * cur_vars ∧
  (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat])

private theorem watchSliceOk_bin_prefix_split {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem bn : Nat} (h : WatchSliceOk F_cur k lit p rem) (hbn : bn ≤ rem)
    (hbin : ∀ t < bn, ∃ w, k.wstk[p + t]? = some w ∧ (w &&& 0x80000000#32) ≠ 0#32) :
    (∀ t < bn, ∃ w, k.wstk[p + t]? = some w ∧ BinWatchWordOk F_cur k.cur_vars lit w) ∧
    WatchSliceOk F_cur k lit (p + bn) (rem - bn) := by
  induction bn generalizing p rem with
  | zero => exact ⟨fun _ ht => absurd ht (Nat.not_lt_zero _), by simpa using h⟩
  | succ bn' ih =>
    cases h with
    | empty => omega
    | @large p rem' w0 cref hp _ hflag _ _ _ =>
      obtain ⟨w, hw, hnz⟩ := hbin 0 (Nat.zero_lt_succ _)
      rw [Nat.add_zero, hp] at hw
      exact absurd (Option.some.inj hw ▸ hflag) hnz
    | @bin p rem' w0 hp hflag hne hlt hent hrest =>
      obtain ⟨hwords, htail⟩ := ih hrest (by omega) fun t ht => by
        simpa [Nat.add_assoc, Nat.add_comm 1 t] using hbin (t + 1) (by omega)
      refine ⟨fun t ht => ?_, ?_⟩
      · cases t with
        | zero => exact ⟨w0, by simpa using hp, hflag, hne, hlt, hent⟩
        | succ t' => simpa [Nat.add_assoc, Nat.add_comm 1 t'] using hwords t' (by omega)
      · simpa [Nat.add_assoc, Nat.add_comm 1 bn', Nat.succ_sub_succ] using htail

private theorem watchSliceOk_of_bin_prefix {F_cur : List (List Nat)} {k : FullCoreState}
    {wstk' : List (BitVec 32)} {lit p rem bn : Nat} (hbn : bn ≤ rem)
    (hwords : ∀ t < bn, ∃ w, wstk'[p + t]? = some w ∧ BinWatchWordOk F_cur k.cur_vars lit w)
    (htail : WatchSliceOk F_cur { k with wstk := wstk' } lit (p + bn) (rem - bn)) :
    WatchSliceOk F_cur { k with wstk := wstk' } lit p rem := by
  induction bn generalizing p rem with
  | zero => simpa using htail
  | succ bn' ih =>
    obtain ⟨w0, hp, hflag, hne, hlt, hent⟩ := hwords 0 (Nat.zero_lt_succ _)
    have hrem : rem = (rem - 1) + 1 := by omega
    rw [hrem]
    refine WatchSliceOk.bin (by simpa using hp) hflag hne hlt hent ?_
    refine ih (p := p + 1) (rem := rem - 1) (by omega) (fun t ht => ?_) ?_
    · simpa [Nat.add_assoc, Nat.add_comm 1 t] using hwords (t + 1) (by omega)
    · simpa [Nat.add_assoc, Nat.add_comm 1 bn', show rem - 1 - bn' = rem - (bn' + 1) by omega]
        using htail

/-- Permuting words inside a binary prefix `[p, p+bn)` preserves `WatchSliceOk`. -/
theorem WatchSliceOk.of_bin_perm {F_cur : List (List Nat)} {k : FullCoreState}
    {wstk' : List (BitVec 32)} {lit p rem bn : Nat}
    (h : WatchSliceOk F_cur k lit p rem) (hbn : bn ≤ rem)
    (hbin : ∀ t < bn, ∃ w, k.wstk[p + t]? = some w ∧ (w &&& 0x80000000#32) ≠ 0#32)
    (hperm : List.Perm ((wstk'.drop p).take bn) ((k.wstk.drop p).take bn))
    (hrest : ∀ idx, p + bn ≤ idx → idx < p + rem → wstk'[idx]? = k.wstk[idx]?) :
    WatchSliceOk F_cur { k with wstk := wstk' } lit p rem := by
  obtain ⟨hwords, htail⟩ := watchSliceOk_bin_prefix_split h hbn hbin
  have hlen_k : ((k.wstk.drop p).take bn).length = bn := by
    cases bn with
    | zero => simp
    | succ bn' =>
      obtain ⟨w, hw, _⟩ := hwords bn' (Nat.lt_succ_self _)
      have hlt : p + bn' < k.wstk.length := (List.getElem?_eq_some_iff.mp hw).1
      simp only [List.length_take, List.length_drop]; omega
  have hlen_w : ((wstk'.drop p).take bn).length = bn := hperm.length_eq.trans hlen_k
  have hwords' : ∀ t < bn, ∃ w, wstk'[p + t]? = some w ∧ BinWatchWordOk F_cur k.cur_vars lit w := by
    intro t ht
    have ht_w : t < ((wstk'.drop p).take bn).length := by omega
    let w := ((wstk'.drop p).take bn)[t]'ht_w
    have hw_mem : w ∈ (k.wstk.drop p).take bn := hperm.mem_iff.mp (List.getElem_mem ht_w)
    obtain ⟨t', ht', ht'_eq⟩ := List.mem_iff_getElem.mp hw_mem
    have ht'_lt : t' < bn := by omega
    obtain ⟨w', hw', hok'⟩ := hwords t' ht'_lt
    have hweq : w = w' := by
      have h2 : k.wstk[p + t']? = some ((k.wstk.drop p).take bn)[t'] := by
        rw [List.getElem_take, List.getElem_drop]
        exact List.getElem?_eq_getElem (by
          have : t' < (k.wstk.drop p).length := by
            have := List.length_take (l := k.wstk.drop p) (i := bn); omega
          rw [List.length_drop] at this; omega)
      rw [h2, ht'_eq] at hw'; exact Option.some.inj hw'
    have hwp : wstk'[p + t]? = some w := by
      dsimp only [w]
      rw [List.getElem_take, List.getElem_drop]
      exact List.getElem?_eq_getElem (by
        have : t < (wstk'.drop p).length := by
          have := List.length_take (l := wstk'.drop p) (i := bn); omega
        rw [List.length_drop] at this; omega)
    exact ⟨w, hwp, hweq ▸ hok'⟩
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hm => hm
  have htail' : WatchSliceOk F_cur { k with wstk := wstk' } lit (p + bn) (rem - bn) :=
    WatchSliceOk.mono (k := k) (k' := { k with wstk := wstk' }) hrefl (Nat.le_refl _)
      (fun _ hr => hr) (fun idx h1 h2 => hrest idx h1 (by omega)) htail
  exact watchSliceOk_of_bin_prefix hbn hwords' htail'

private theorem watchesInv_of_bin_prefix {F_cur : List (List Nat)} {k : FullCoreState}
    {wstk' : List (BitVec 32)} {lit bn : Nat}
    (hw : WatchesInv F_cur k) (hl : lit < 2 * k.cur_vars) (hbn : bn ≤ fullWatchSizeCore k lit)
    (hbin : ∀ t < bn, ∃ w, k.wstk[fullWatchOffCore k lit + t]? = some w ∧
      (w &&& 0x80000000#32) ≠ 0#32)
    (hwords : ∀ t < bn, ∃ w, wstk'[fullWatchOffCore k lit + t]? = some w ∧
      BinWatchWordOk F_cur k.cur_vars lit w)
    (hkeep : ∀ idx, (idx < fullWatchOffCore k lit ∨ fullWatchOffCore k lit + bn ≤ idx) →
      wstk'[idx]? = k.wstk[idx]?) :
    WatchesInv F_cur { k with wstk := wstk' } := by
  let k' : FullCoreState := { k with wstk := wstk' }
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hm => hm
  refine WatchesInv.of_slices hw.layout.bounds hw.layout.pos_off hw.layout.disjoint fun l hl' => ?_
  change WatchSliceOk F_cur k' l (fullWatchOffCore k l) (fullWatchSizeCore k l)
  by_cases heq : l = lit
  · subst heq
    obtain ⟨_, htail⟩ := watchSliceOk_bin_prefix_split (hw.slices l hl) hbn hbin
    have htail' : WatchSliceOk F_cur k' l (fullWatchOffCore k l + bn)
        (fullWatchSizeCore k l - bn) :=
      WatchSliceOk.mono (k := k) (k' := k') hrefl (Nat.le_refl _) (fun _ hr => hr)
        (fun idx h1 _ => hkeep idx (Or.inr h1)) htail
    exact watchSliceOk_of_bin_prefix hbn hwords htail'
  · cases hsz : fullWatchSizeCore k l with
    | zero => exact .empty
    | succ sz' =>
      rw [← hsz]
      refine WatchSliceOk.mono (k := k) (k' := k') hrefl (Nat.le_refl _) (fun _ hr => hr)
        (fun idx h1 h2 => ?_) (hw.slices l hl')
      rw [hsz] at h2
      by_cases hbn0 : bn = 0
      · apply hkeep; omega
      · have hdisj := hw.layout.disjoint l lit hl' hl heq (by omega) (by omega)
        apply hkeep; omega

/-- Permuting words inside one literal's binary prefix preserves `WatchesInv`. -/
theorem WatchesInv.of_bin_perm {F_cur : List (List Nat)} {k : FullCoreState}
    {wstk' : List (BitVec 32)} {lit bn : Nat}
    (hw : WatchesInv F_cur k) (hl : lit < 2 * k.cur_vars) (hbn : bn ≤ fullWatchSizeCore k lit)
    (hbin : ∀ t < bn, ∃ w, k.wstk[fullWatchOffCore k lit + t]? = some w ∧
      (w &&& 0x80000000#32) ≠ 0#32)
    (hperm : List.Perm ((wstk'.drop (fullWatchOffCore k lit)).take bn)
      ((k.wstk.drop (fullWatchOffCore k lit)).take bn))
    (hkeep : ∀ idx, (idx < fullWatchOffCore k lit ∨ fullWatchOffCore k lit + bn ≤ idx) →
      wstk'[idx]? = k.wstk[idx]?) :
    WatchesInv F_cur { k with wstk := wstk' } := by
  let k' : FullCoreState := { k with wstk := wstk' }
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hm => hm
  refine WatchesInv.of_slices hw.layout.bounds hw.layout.pos_off hw.layout.disjoint fun l hl' => ?_
  change WatchSliceOk F_cur k' l (fullWatchOffCore k l) (fullWatchSizeCore k l)
  by_cases heq : l = lit
  · subst heq
    exact WatchSliceOk.of_bin_perm (hw.slices l hl) hbn hbin hperm fun idx h1 _ =>
      hkeep idx (Or.inr h1)
  · cases hsz : fullWatchSizeCore k l with
    | zero => exact .empty
    | succ sz' =>
      rw [← hsz]
      refine WatchSliceOk.mono (k := k) (k' := k') hrefl (Nat.le_refl _) (fun _ hr => hr)
        (fun idx h1 h2 => ?_) (hw.slices l hl')
      rw [hsz] at h2
      by_cases hbn0 : bn = 0
      · apply hkeep; omega
      · have hdisj := hw.layout.disjoint l lit hl' hl heq (by omega) (by omega)
        apply hkeep; omega

private theorem fullSparseInvW_with_wstk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {wstk' : List (BitVec 32)} (h : FullSparseInvW c F0 F_cur s)
    (hlen : wstk'.length = c.wcap)
    (hw' : WatchesInv F_cur { s.core with wstk := wstk' }) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with wstk := wstk' } } := by
  let k' : FullCoreState := { s.core with wstk := wstk' }
  have hdm : k'.dense_mode = 0#64 := h.2.2.2.2.2
  have hmw : ModeWatchesInv F_cur k' := by
    unfold ModeWatchesInv; split; exact hw'; exact absurd hdm ‹_›
  exact ⟨⟨{ h.1.core_ok with wstk_len_arr := hlen }, h.1.scratch_ok⟩,
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := hmw },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hdm⟩

private def BinPrefixStateOk (c : FullCfg) (F_cur : List (List Nat)) (k0 : FullCoreState)
    (lit off bn : Nat) (wstk : List (BitVec 32)) : Prop :=
  wstk.length = c.wcap ∧
  (∀ idx, (idx < off ∨ off + bn ≤ idx) → wstk[idx]? = k0.wstk[idx]?) ∧
  (∀ t < bn, ∃ w, wstk[off + t]? = some w ∧ BinWatchWordOk F_cur k0.cur_vars lit w)

private theorem binPrefixStateOk_set {c : FullCfg} {F_cur : List (List Nat)} {k0 : FullCoreState}
    {lit off bn pos : Nat} {wstk : List (BitVec 32)} {w : BitVec 32}
    (h : BinPrefixStateOk c F_cur k0 lit off bn wstk)
    (hpos : pos < bn) (hbnd : off + pos < wstk.length)
    (hw : BinWatchWordOk F_cur k0.cur_vars lit w) :
    BinPrefixStateOk c F_cur k0 lit off bn (wstk.set (off + pos) w) := by
  refine ⟨by rw [List.length_set]; exact h.1, fun idx hidx => ?_, fun t ht => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact h.2.1 idx hidx
  · by_cases heq : t = pos
    · subst heq; exact ⟨w, by rw [List.getElem?_set_self hbnd], hw⟩
    · rw [List.getElem?_set_ne (by omega)]; exact h.2.2 t ht

private theorem bv64_udiv3_toNat (x : BitVec 64) : (x / (3 : BitVec 64)).toNat = x.toNat / 3 := by
  bv_omega

private theorem bv64_mul3_add1_toNat {x : BitVec 64} (hx : 3 * x.toNat + 1 < 2 ^ 64) :
    ((3 : BitVec 64) * x + (1 : BitVec 64)).toNat = 3 * x.toNat + 1 := by
  have h3 : ((3 : BitVec 64)).toNat = 3 := by bv_omega
  have h1 : ((1 : BitVec 64)).toNat = 1 := by bv_omega
  have hmul : ((3 : BitVec 64) * x).toNat = 3 * x.toNat := by
    rw [BitVec.toNat_mul, h3, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, hmul, h1, Nat.mod_eq_of_lt (by omega)]

private theorem s7_getElem_of_some {xs : List (BitVec 32)} {i : Nat} {w : BitVec 32}
    (hi : i < xs.length) (hs : xs[i]? = some w) : xs[i]'hi = w := by
  rw [List.getElem?_eq_getElem hi] at hs; exact Option.some.inj hs

/-- Parametric `Func.wp` proof for `fidStep7SortBinWatchesFn` (`full_sort_bin_watches_fid`)
against `@[expose] def step7SortBinWatchesSpec`. -/
theorem full_sort_bin_watches_fid_step7_wp (Γ : Env) :
    ∀ a m Q X, step7SortBinWatchesSpec a m Q X →
      Func.wp Γ fidStep7SortBinWatchesFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp0, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap
  unfold LratBytes.dimacsBound at hmx hwc
  have hcv_le := hsp0.1.core_ok.cur_vars_le
  have hwlen_le := hsp0.1.core_ok.wlen_le
  have hnl_eq : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  unfold Func.wp fidStep7SortBinWatchesFn full_sort_bin_watches_fid_body
  dsimp only
  s7_to_group_np
  refine wp_while_state (ts := [i64]) (α := BitVec 64 × List (BitVec 32))
    (fun ⟨l, _⟩ => (l, ()))
    (fun ⟨l, _⟩ => 2 * s.core.cur_vars - l.toNat)
    (fun ⟨l, wstk⟩ ml =>
      let st : FullState := { s with core := { s.core with wstk := wstk } }
      l.toNat ≤ 2 * s.core.cur_vars ∧ wstk.length = c.wcap ∧
      FullSparseInvW c F0 F_cur st ∧ (FullMem c st ⋆ R) ml)
    (fun J hJ => by
      s7_to_group_np
      exact hJ (0#64, s.core.wstk) m0 ⟨Nat.zero_le _, hsp0.1.core_ok.wstk_len_arr, hsp0, hm0⟩)
    ?_
  rintro J ⟨l, wstkL⟩ ml ⟨hl_le, hwlenL, hspL, hmL⟩ ihL
  clear hm0
  let sL : FullState := { s with core := { s.core with wstk := wstkL } }
  have hwatL : WatchesInv F_cur sL.core := by
    have hm := hspL.2.1.watches; unfold ModeWatchesInv at hm
    split at hm
    · exact hm
    · exact absurd hspL.2.2.2.2.2 ‹_›
  c0_hsplit
  · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
      have h1 : l.toNat < (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat :=
        BitVec.lt_def.mp hc
      omega
    have hwv0_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
    have hwv1_eq : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1 := by
      rw [BitVec.toNat_add, hwv0_eq]; simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
    have hwv0_lt : (l <<< (1 : Nat)).toNat < sL.core.wvec.length := by
      rw [hspL.1.core_ok.wvec_len, hwv0_eq]; omega
    have hwv1_lt : ((l <<< (1 : Nat)) + 1#64).toNat < sL.core.wvec.length := by
      rw [hspL.1.core_ok.wvec_len, hwv1_eq]; omega
    have hoff_eq0 : ((sL.core.wvec[(l <<< (1 : Nat)).toNat]'hwv0_lt).setWidth 64).toNat =
        fullWatchOffCore sL.core l.toNat := by
      rw [m6_zext32_toNat]; unfold fullWatchOffCore
      rw [List.getElem?_eq_getElem (by rw [hspL.1.core_ok.wvec_len]; omega), Option.getD_some]
      congr 2
    have hsz_eq0 : ((sL.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'hwv1_lt).setWidth 64).toNat =
        fullWatchSizeCore sL.core l.toNat := by
      rw [m6_zext32_toNat]; unfold fullWatchSizeCore
      rw [List.getElem?_eq_getElem (by rw [hspL.1.core_ok.wvec_len]; omega), Option.getD_some]
      congr 2
    have hbounds := hwatL.layout.bounds l.toNat hl_lt
    have hl1_eq : (l + 1#64).toNat = l.toNat + 1 := by c0_bound
    let off64 : BitVec 64 := BitVec.setWidth 64 (sL.core.wvec[(l <<< (1 : Nat)).toNat]'hwv0_lt)
    let sz64 : BitVec 64 :=
      BitVec.setWidth 64 (sL.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'hwv1_lt)
    have hoff_sz_le : off64.toNat + sz64.toNat ≤ c.wcap := by
      rw [hoff_eq0, hsz_eq0]; exact Nat.le_trans hbounds hwlen_le
    s7_to_group_np
    -- Loop 2: `while (bn < sz && (ws[off + bn] & 0x80000000) != 0) { bn++; }`
    refine wp_while_state_pure (ts := [i64]) (α := BitVec 64)
      (fun bn => (bn, ()))
      (fun bn => sz64.toNat - bn.toNat)
      (fun bn => bn.toNat ≤ sz64.toNat ∧
        ∀ t < bn.toNat, ∃ w, wstkL[off64.toNat + t]? = some w ∧ (w &&& 0x80000000#32) ≠ 0#32)
      (fun J2 hJ2 => by
        s7_to_group_np
        exact hJ2 0#64 ⟨Nat.zero_le _, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩)
      ?_
    rintro J2 bn ⟨hbn_le, hbin⟩ ih2
    -- Inner join `J2e` after `while (bn < sz && ...)`
    refine wp_join_group (ts := []) (fun () mb => ml = mb) ?_ ?_
    · rintro _ ⟨⟩ mb rfl
      refine wp_join_group (ts := [])
        (fun () ma => ∃ wstkA : List (BitVec 32), wstkA.length = c.wcap ∧
          FullSparseInvW c F0 F_cur { s with core := { s.core with wstk := wstkA } } ∧
          (FullMem c { s with core := { s.core with wstk := wstkA } } ⋆ R) ma)
        (fun _ () ma ⟨wstkA, hlenA, hspA, hmA⟩ => by
          s7_to_group_np
          exact ihL (l + 1#64, wstkA) ma (by dsimp only; omega) ⟨by omega, hlenA, hspA, hmA⟩)
        ?_
      intro Jif hJif
      c0_hsplit
      · have hbn_gt1 : 1 < bn.toNat := BitVec.lt_def.mp hc
        have hbn_le_s : bn.toNat ≤ fullWatchSizeCore sL.core l.toNat := hsz_eq0 ▸ hbn_le
        have hbin_s : ∀ t < bn.toNat, ∃ w, sL.core.wstk[fullWatchOffCore sL.core l.toNat + t]? =
            some w ∧ (w &&& 0x80000000#32) ≠ 0#32 := by
          simpa only [← hoff_eq0] using hbin
        obtain ⟨hwords0, _⟩ :=
          watchSliceOk_bin_prefix_split (hwatL.slices l.toNat hl_lt) hbn_le_s hbin_s
        have hbp0 : BinPrefixStateOk c F_cur sL.core l.toNat off64.toNat bn.toNat wstkL :=
          ⟨hwlenL, fun _ _ => rfl, by simpa only [← hoff_eq0] using hwords0⟩
        s7_to_group_np
        -- Loop 3: `while (gap < lim) { gap = 3 * gap + 1; }`
        refine wp_while_state_pure (ts := [i64]) (α := BitVec 64)
          (fun gap => (gap, ()))
          (fun gap => (bn / (3 : BitVec 64)).toNat - gap.toNat)
          (fun gap => 1 ≤ gap.toNat ∧ gap.toNat < bn.toNat)
          (fun Jg hJg => by
            s7_to_group_np
            exact hJg 1#64 ⟨by bv_omega, by bv_omega⟩)
          ?_
        rintro Jg gap ⟨hgap_pos, hgap_lt⟩ ihG
        c0_hsplit
        · have hglt : gap.toNat < bn.toNat / 3 := by
            have := BitVec.lt_def.mp hc; rwa [bv64_udiv3_toNat] at this
          have hgnext : ((3 : BitVec 64) * gap + (1 : BitVec 64)).toNat = 3 * gap.toNat + 1 :=
            bv64_mul3_add1_toNat (by omega)
          s7_to_group_np
          exact ihG ((3 : BitVec 64) * gap + (1 : BitVec 64))
            (by rw [bv64_udiv3_toNat, hgnext]; omega) ⟨by omega, by omega⟩
        · -- Loop 4: `while (gap > 0) { ... gap = gap / 3; }`
          s7_to_group_np
          refine wp_while_state (ts := [i64]) (α := BitVec 64 × List (BitVec 32))
            (fun ⟨g, _⟩ => (g, ()))
            (fun ⟨g, _⟩ => g.toNat)
            (fun ⟨g, wstkG⟩ mg => g.toNat < bn.toNat ∧
              BinPrefixStateOk c F_cur sL.core l.toNat off64.toNat bn.toNat wstkG ∧
              (FullMem c { s with core := { s.core with wstk := wstkG } } ⋆ R) mg)
            (fun J4 hJ4 => by
              s7_to_group_np; exact hJ4 (gap, wstkL) ml ⟨hgap_lt, hbp0, hmL⟩)
            ?_
          rintro J4 ⟨g, wstkG⟩ mg ⟨hg_lt, hbpG, hmG⟩ ih4
          clear hmL
          c0_hsplit
          · have hg_pos : 0 < g.toNat := BitVec.lt_def.mp hc
            s7_to_group_np
            -- Loop 5: `while (i < bn) { ... i = i + 1; }`
            refine wp_while_state (ts := [i64]) (α := BitVec 64 × List (BitVec 32))
              (fun ⟨i, _⟩ => (i, ()))
              (fun ⟨i, _⟩ => bn.toNat - i.toNat)
              (fun ⟨i, wstkI⟩ mi => g.toNat ≤ i.toNat ∧ i.toNat ≤ bn.toNat ∧
                BinPrefixStateOk c F_cur sL.core l.toNat off64.toNat bn.toNat wstkI ∧
                (FullMem c { s with core := { s.core with wstk := wstkI } } ⋆ R) mi)
              (fun J5 hJ5 => by
                s7_to_group_np
                exact hJ5 (g, wstkG) mg ⟨Nat.le_refl _, Nat.le_of_lt hg_lt, hbpG, hmG⟩)
              ?_
            rintro J5 ⟨i, wstkI⟩ mi ⟨hi_ge, hi_le, hbpI, hmI⟩ ih5
            clear hmG
            c0_hsplit
            · have hi_lt : i.toNat < bn.toNat := BitVec.lt_def.mp hc
              have hofi_eq : (off64 + i).toNat = off64.toNat + i.toNat := by
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
              have hofi_lt : (off64 + i).toNat < wstkI.length := by
                rw [hbpI.1, hofi_eq]; omega
              obtain ⟨x_w, hx_some, hx_ok⟩ := hbpI.2.2 i.toNat hi_lt
              have hx_eq : wstkI[(off64 + i).toNat]'hofi_lt = x_w :=
                s7_getElem_of_some hofi_lt (by rwa [hofi_eq])
              have hi1_eq : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
              s7_to_group_np
              -- Loop 6: `while (j >= gap && (ws[off + j - gap] & 0x7FFFFFFF) > xo)`
              refine wp_while_state (ts := [i64]) (α := BitVec 64 × List (BitVec 32))
                (fun ⟨j, _⟩ => (j, ()))
                (fun ⟨j, _⟩ => j.toNat)
                (fun ⟨j, wstkJ⟩ mj => j.toNat < bn.toNat ∧
                  BinPrefixStateOk c F_cur sL.core l.toNat off64.toNat bn.toNat wstkJ ∧
                  (FullMem c { s with core := { s.core with wstk := wstkJ } } ⋆ R) mj)
                (fun J6 hJ6 => by
                  s7_to_group_np; exact hJ6 (i, wstkI) mi ⟨hi_lt, hbpI, hmI⟩)
                ?_
              rintro J6 ⟨j, wstkJ⟩ mj ⟨hj_lt, hbpJ, hmJ⟩ ih6
              clear hmI
              refine wp_join_group (ts := []) (fun () me => me = mj) ?_ ?_
              · rintro _ ⟨⟩ me rfl
                have hofj_eq : (off64 + j).toNat = off64.toNat + j.toNat := by
                  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                have hofj_lt : (off64 + j).toNat < wstkJ.length := by
                  rw [hbpJ.1, hofj_eq]; omega
                have hbpJ' : BinPrefixStateOk c F_cur sL.core l.toNat off64.toNat bn.toNat
                    (wstkJ.set (off64 + j).toNat (wstkI[(off64 + i).toNat]'hofi_lt)) := by
                  rw [hofj_eq, hx_eq]
                  exact binPrefixStateOk_set hbpJ hj_lt (by rw [hbpJ.1]; omega) hx_ok
                s7_to_group_np
                exact ih5 (i + 1#64, _) _ (by dsimp only; omega)
                  ⟨by omega, by omega, hbpJ', hm⟩
              · intro J6e hJ6e
                c0_hsplit
                · have hj_ge : g.toNat ≤ j.toNat := BitVec.le_def.mp hc
                  have hofjg_eq : (off64 + j - g).toNat = off64.toNat + (j.toNat - g.toNat) := by
                    have h1 : (off64 + j).toNat = off64.toNat + j.toNat := by
                      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                    rw [BitVec.toNat_sub, h1]; omega
                  have hofjg_lt : (off64 + j - g).toNat < wstkJ.length := by
                    rw [hbpJ.1, hofjg_eq]; omega
                  c0_hsplit
                  · have hofj_eq : (off64 + j).toNat = off64.toNat + j.toNat := by
                      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                    have hofj_lt : (off64 + j).toNat < wstkJ.length := by
                      rw [hbpJ.1, hofj_eq]; omega
                    have hjmg_eq : (j - g).toNat = j.toNat - g.toNat := by
                      rw [BitVec.toNat_sub]; have := j.isLt; omega
                    obtain ⟨wprev, hwprev_some, hwprev_ok⟩ :=
                      hbpJ.2.2 (j.toNat - g.toNat) (by omega)
                    have hwprev_eq : wstkJ[(off64 + j - g).toNat]'hofjg_lt = wprev :=
                      s7_getElem_of_some hofjg_lt (by rwa [hofjg_eq])
                    have hbpJ' : BinPrefixStateOk c F_cur sL.core l.toNat off64.toNat bn.toNat
                        (wstkJ.set (off64 + j).toNat (wstkJ[(off64 + j - g).toNat]'hofjg_lt)) := by
                      rw [hofj_eq, hwprev_eq]
                      exact binPrefixStateOk_set hbpJ hj_lt (by rw [hbpJ.1]; omega) hwprev_ok
                    s7_to_group_np
                    exact ih6 (j - g, _) _ (by dsimp only; omega) ⟨by omega, hbpJ', hm⟩
                  · s7_to_group_np; exact hJ6e () mj rfl
                · s7_to_group_np; exact hJ6e () mj rfl
            · have hg3 : (g / (3 : BitVec 64)).toNat = g.toNat / 3 := bv64_udiv3_toNat g
              s7_to_group_np
              exact ih4 (g / (3 : BitVec 64), wstkI) mi (by dsimp only; omega)
                ⟨by omega, hbpI, hmI⟩
          · have hwatG : WatchesInv F_cur { sL.core with wstk := wstkG } :=
              watchesInv_of_bin_prefix hwatL hl_lt hbn_le_s hbin_s
                (by simpa only [← hoff_eq0] using hbpG.2.2)
                (by simpa only [← hoff_eq0] using hbpG.2.1)
            have hspG : FullSparseInvW c F0 F_cur
                { s with core := { s.core with wstk := wstkG } } :=
              fullSparseInvW_with_wstk (s := sL) hspL hbpG.1 hwatG
            s7_to_group_np
            exact hJif () mg ⟨wstkG, hbpG.1, hspG, hmG⟩
      · s7_to_group_np; exact hJif () ml ⟨wstkL, hwlenL, hspL, hmL⟩
    · intro J2e hJ2e
      c0_hsplit
      · have hbn_lt : bn.toNat < sz64.toNat := by
          have h1 : ((l <<< (1 : Nat)) + 1#64).toNat =
              (2 * l.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := by bv_omega
          dsimp only [sz64]; rw [m6_zext32_toNat]; simpa only [h1] using hc
        have hofb_eq : (off64 + bn).toNat = off64.toNat + bn.toNat := by
          rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        have hofb_lt : (off64 + bn).toNat < wstkL.length := by rw [hwlenL, hofb_eq]; omega
        c0_hsplit
        · have hbn1_eq : (bn + 1#64).toNat = bn.toNat + 1 := by c0_bound
          s7_to_group_np
          refine ih2 (bn + 1#64) (by omega) ⟨by omega, fun t ht => ?_⟩
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hbn1_eq ▸ ht)) with hlt | heq
          · exact hbin t hlt
          · subst heq
            refine ⟨wstkL[(off64 + bn).toNat]'hofb_lt, ?_, hc⟩
            rw [← hofb_eq]; exact List.getElem?_eq_getElem hofb_lt
        · s7_to_group_np; exact hJ2e () ml rfl
      · s7_to_group_np; exact hJ2e () ml rfl
  · change Q () ml
    exact hQ wstkL ml hwlenL hspL hwatL hmL

/-! ## 2. `full_rebuild_watches_step7_wp` (`Full.fullRebuildWatchesSpec`) -/

private def S7RebuildOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) : Prop :=
  FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level = 0 ∧
  s'.core.fuel.toNat ≤ s.core.fuel.toNat

private theorem s7RebuildOk_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hst : S7RebuildOk c F0 F_cur s st)
    {vals' : List (BitVec 8)}
    {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch} :
    let sA : FullState :=
      { st with
        core := { st.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
          wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
          wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core → Full.FullArenaVarsNodup sA →
    FullLastLearnedWf sA → sc'.extend_len = st.scratch.extend_len →
    S7RebuildOk c F0 F_cur s sA := by
  intro sA hlenA hwA hndA hllA hextA
  exact ⟨⟨hlenA, hwA, hst.1.2.2.1, hndA, ⟨hllA, hextA ▸ hst.1.2.2.2.2.1.2⟩, hst.1.2.2.2.2.2⟩,
    hst.2.1, hst.2.2⟩

private theorem s7RebuildOk_bcp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sA : FullState} (hA : S7RebuildOk c F0 F_cur s sA)
    {valsB : List (BitVec 8)}
    {flagsB lvlB rsnsB trlB tpB wvecB arenaB wstkB : List (BitVec 32)}
    {teB propB wlenB : Nat} {unassB unflB wuB fuelB ctypeB crefB c0B c1B oomB ticksB : BitVec 64}
    {wsortB delayedB : List (BitVec 32)} {phasesB : List (BitVec 8)} :
    let sB : FullState :=
      { sA with
        core := { sA.core with
          vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
          trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
          unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB, wlen := wlenB,
          wusable := wuB, fuel := fuelB, confl_type := ctypeB, confl_ref := crefB,
          confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
        scratch := { sA.scratch with
          search_ticks := ticksB, wsort := wsortB, phases := phasesB, delayed := delayedB } }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    FullArenaPermEq sA.core sB.core → fuelB.toNat ≤ sA.core.fuel.toNat →
    S7RebuildOk c F0 F_cur s sB := by
  intro sB hlenB hwB hpermB hfuelB
  have hndB : Full.FullArenaVarsNodup sB := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefs sA := by
      change ref ∈ fullArenaClauseRefsCore sB.core at href
      change ref ∈ fullArenaClauseRefsCore sA.core; rwa [← hpermB.2.1]
    have hp := hpermB.2.2 ref href0
    have hgb : fullArenaClauseGarb sA ref = false := by
      change fullArenaClauseGarbCore sA.core ref = false
      change fullArenaClauseGarbCore sB.core ref = false at hng; rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hA.1.2.2.2.1 ref href0 hgb)
  have hllB : FullLastLearnedWf sB :=
    hA.1.2.2.2.2.1.1.of_refs_subset rfl fun ref href => by
      change ref ∈ fullArenaClauseRefsCore sA.core at href
      change ref ∈ fullArenaClauseRefsCore sB.core; rwa [hpermB.2.1]
  exact ⟨⟨hlenB, hwB, hA.1.2.2.1, hndB, ⟨hllB, hA.1.2.2.2.2.1.2⟩, hA.1.2.2.2.2.2⟩,
    hA.2.1, Nat.le_trans hfuelB hA.2.2⟩

/-- Parametric `Func.wp` proof for `fidStep7RebuildWatchesFn` (`full_rebuild_watches`, calling
`full_sort_bin_watches_fid` right before returning `1ULL`) against `Full.fullRebuildWatchesSpec`. -/
theorem full_rebuild_watches_step7_wp (Γ : Env)
    (hSweep : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSortBin : ∀ a m Q X, step7SortBinWatchesSpec a m Q X →
      Γ "full_sort_bin_watches_fid" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Func.wp Γ fidStep7RebuildWatchesFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hdn, hm0, hQ⟩
  obtain ⟨F_cur, hdw⟩ := hdn.exists_witness
  let s0 : FullState := { s with core := { s.core with dense_mode := 0#64 } }
  have hsp0 : FullSparseInvW c F0 F_cur s0 := hdw.toSparse_clear_dense
  have hok0 : S7RebuildOk c F0 F_cur s s0 := ⟨hsp0, hdw.2.2.2.2.2.1, Nat.le_refl _⟩
  unfold Func.wp fidStep7RebuildWatchesFn full_rebuild_watches_body
  dsimp only
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ st : FullState, S7RebuildOk c F0 F_cur s st ∧ (FullMem c st ⋆ R) m1)
    (fun _ () m1 ⟨st, hok, hm1⟩ => by
      c0_hsteps_nogrp
      s7_call hSortBin
      refine ⟨c, F0, F_cur, st, R, rfl, hok.1, hm1, fun wstk' m2 _ hsp' _ hm2 => ?_⟩
      c0_hsteps_nogrp
      exact hQ 1#64 _ m2 hsp'.toSparse hok.2.1 hok.2.2 (Or.inr (Or.inl rfl))
        (fun h => by cases h) hm2)
    ?_
  intro Jbrk hJbrk
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [])
    (fun rem () ml => ∃ st : FullState, rem = c.max_vars - st.core.trail_end ∧
      S7RebuildOk c F0 F_cur s st ∧ (FullMem c st ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hok_st, hm_st⟩
    dsimp only [Blocks.get]
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    c0_hsteps_nogrp
    s7_call hSweep
    refine ⟨c, F0, F_cur, st, R, rfl, hok_st.1.1, hok_st.1.2.1, hok_st.1.2.2.2.1,
      hok_st.1.2.2.2.2.2, fun hpos => by have := hok_st.2.1; omega, hm_st,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen'
        wlen' wu' fred' ni' nr' nb' oom' sc' mA hlenA hsr_dom hextA _ hllA hwA hndA
        _ _ hsr1 hsr2 _ hmA => ?_⟩
    let sA : FullState :=
      { st with
        core := { st.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
          wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
          wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    have hokA : S7RebuildOk c F0 F_cur s sA := s7RebuildOk_sweep hok_st hlenA hwA hndA hllA hextA
    c0_hsteps_nogrp
    · exact hQ 20#64 sA mA hokA.1.toSparse hokA.2.1 hokA.2.2 (Or.inr (Or.inr rfl))
        (fun _ => (hsr2 hc).2) hmA
    · exact hQ 0#64 sA mA hokA.1.toSparse hokA.2.1 hokA.2.2 (Or.inl rfl)
        (fun h => by cases h) hmA
    · s7_call hProp
      refine ⟨c, F0, F_cur, sA, R, rfl, hlenA, hwA, hokA.1.2.2.2.2.2, hmA,
        fun pr valsB flagsB lvlB rsnsB trlB tpB teB propB unassB unflB wvecB arenaB wstkB
          wlenB wuB fuelB ctypeB crefB c0B c1B oomB ticksB wsortB phasesB delayedB mB
          hlenB hwB htrB hpermB _ hfuelB _ _ hpr1 _ _ hmB => ?_⟩
      let sB : FullState :=
        { sA with
          core := { sA.core with
            vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
            trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
            unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB, wlen := wlenB,
            wusable := wuB, fuel := fuelB, confl_type := ctypeB, confl_ref := crefB,
            confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
          scratch := { sA.scratch with
            search_ticks := ticksB, wsort := wsortB, phases := phasesB, delayed := delayedB } }
      have hokB : S7RebuildOk c F0 F_cur s sB := s7RebuildOk_bcp hokA hlenB hwB hpermB hfuelB
      c0_hsteps_nogrp
      · have hunsat : F0.Unsat :=
          FullVivTopSpecs.level0_unsat_of_conflict_okW hwB hokA.2.1 (hpr1 hc).2.2
        exact hQ 20#64 sB mB hokB.1.toSparse hokB.2.1 hokB.2.2 (Or.inr (Or.inr rfl))
          (fun _ => hunsat) hmB
      · exact hJbrk () mB ⟨sB, hokB, hmB⟩
      · have hsr_eq1 : sr = 1#64 := by
          rcases hsr_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
        obtain ⟨_, hte_lt⟩ := hsr1 hsr_eq1
        have hte_bd : sB.core.trail_end ≤ c.max_vars :=
          Nat.le_trans hlenB.core_ok.trail_end_le hlenB.core_ok.cur_vars_le
        have hteA : sA.core.trail_end = te' := rfl
        have hte_le : sA.core.trail_end ≤ sB.core.trail_end := htrB.1
        exact ih (c.max_vars - sB.core.trail_end) () mB (by omega) ⟨sB, rfl, hokB, hmB⟩
  · intro L hL; c0_hsteps_nogrp
    exact hL (c.max_vars - s0.core.trail_end) () _ ⟨s0, rfl, hok0, by assumption⟩

/-! ## 3. `full_vivify_tier_m6_hdr_step7_wp` (`FullM6OrchAdapters.m6aVivifyTierSpec`) -/

private theorem s7_sparse_with_rr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap) :
    FullSparseInv c F0 { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with red_refs_len := hrr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s7_sparse_with_tr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {tr' : List (BitVec 32)} (htr : tr'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tarjan_reach := tr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with tarjan_reach_len := htr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s7_sparse_with_rr_scr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' scr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap)
    (hscr : scr'.length = c.scratch_cap) :
    FullSparseInv c F0
      { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok,
      { h.1.lengths.scratch_ok with red_refs_len := hrr, scratch_buf_len := hscr }⟩,
    h.1.witness⟩, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s7_sparse_with_res_sz {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (rsz : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with res_sz := rsz } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s7_sparse_with_tier1 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (t1 : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tier1 := t1 } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s7_sparse_with_tier2 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (t2 : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tier2 := t2 } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s7_sparse_with_ticks {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (st : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with search_ticks := st } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s7_sparseInv_of_core_eq {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c) (hcore : s'.core = s.core)
    (hpres : FullM6Hdr.M6HdrScratchPres s s') : FullSparseInv c F0 s' := by
  obtain ⟨hcore_inv, hmc, hvn, hsc, hdm⟩ := h
  refine ⟨⟨hlen', ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨F_cur, hw⟩ := hcore_inv.2
    exact ⟨F_cur, by rw [hcore]; exact hw⟩
  · unfold FullLitMarksClear FullMrkZero; rw [hcore]; exact hmc
  · unfold Full.FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [hcore]; exact hvn
  · exact ⟨fun i hi => by
      have hll : s'.scratch.last_learned[i]? = s.scratch.last_learned[i]? := by
        rw [hpres.extPres.1]
      dsimp only [FullLastLearnedWf] at hsc ⊢
      rw [hll]
      rcases hsc.1 i hi with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (by unfold fullArenaClauseRefs; rw [hcore]; exact h2),
      by rw [hpres.extPres.2]; exact hsc.2⟩
  · rw [hcore]; exact hdm

private theorem s7_sparseInvW_of_prop_canon {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)} {delayed' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                  phases := phases', delayed := delayed' } } :
      FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' })
    (hperm : FullArenaPermEq s.core
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := { s.scratch with
          search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                  phases := phases', delayed := delayed' } }
  have hnd' : Full.FullArenaVarsNodup s' := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  have hrefs : ∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s' := fun ref hr => by
    change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr
  exact FullVivTop.fullSparseInvW_of_prop_state hsp hlen' hw' hnd'
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hrefs

private theorem s7_ext_pres_compose {ext ext1 ext2 : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1)
    (h2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2) :
    M6HdrExtInitOk ext → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext ext2 := fun hi =>
  ⟨(h2 (h1 hi).1).1, (h1 hi).2.trans (h2 (h1 hi).1).2⟩

/-- Parametric `Func.wp` proof for `fidStep7VivifyTierM6HdrFn` (`full_vivify_tier_m6_hdr`,
`do_sort` reverse-scan guard) against `FullM6OrchAdapters.m6aVivifyTierSpec`. -/
theorem full_vivify_tier_m6_hdr_step7_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectFidSpec a m Q X →
      Γ "full_viv_collect_fid" [i64, i64] [i64] a m Q X)
    (hCount : ∀ a m Q X, fullVivCountFidSpec a m Q X →
      Γ "full_viv_count_fid" [i64, i64] [] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortFidSpec a m Q X →
      Γ "full_viv_sort_fid" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, FullM6VivBackbone.fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, FullM6VivBackbone.fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullM6OrchAdapters.m6aVivifyTierSpec a m Q X →
      Func.wp Γ fidStep7VivifyTierM6HdrFn.body a m Q X := by
  rintro ⟨h, tier_mode, budget0, tick_lim, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩ := FullM6OrchAdapters.m6aVivifyTierSpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := hmx
  unfold Func.wp fidStep7VivifyTierM6HdrFn full_vivify_tier_m6_hdr_body; dsimp only; fvt_to_group
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 (fun h => h) (fun h => h) (fun hb => absurd (by c0_bound) hb)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m ⟨s1, hsp1, hcl1, hfl1, hm⟩
    fvt_steps
    let s2 : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp2 : FullSparseInv c F0 s2 := FullVivTop.FullSparseInv.with_probing hsp1 1#64
    have hm2 : (FullMem c s2 ⋆ R) m := hm
    have hfl2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfl1
    clear_value s2
    clear hsp1 hcl1 hfl1
    c0_call hCollect
    refine ⟨c, F0, s2, R, rfl, hsp2, hm2, fun bn rr3 m3 hbn_le hrr3 hok3 hm3 => ?_⟩
    let s3 : FullState := { s2 with scratch := { s2.scratch with red_refs := rr3 } }
    have hsp3 : FullSparseInv c F0 s3 := s7_sparse_with_rr hsp2 hrr3
    let SortJoin : Tup Val [] → Mem 64 → Prop := fun () ms =>
      ∃ (s5 : FullState) (rr5 : List (BitVec 32)),
        FullSparseInv c F0 s5 ∧ s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs s5 = fullArenaClauseRefs s2 ∧
        s5.scratch.red_refs = rr5 ∧ rr5.length = c.red_cap ∧
        (∀ k < bn.toNat, (rr5[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2) ∧
        (FullMem c s5 ⋆ R) ms
    fvt_to_group
    refine wp_join_group (ts := [.bool]) (fun _ md => m3 = md) ?_
      (fun Jd hJd => by fvt_steps <;> exact hJd _ m3 rfl)
    rintro _ ⟨do_sort, ⟨⟩⟩ _ rfl
    fvt_to_group
    refine wp_join_group (ts := []) SortJoin ?_ ?_
    · rintro _ ⟨⟩ m5 ⟨s5, rr5, hsp5, hfl5, hrefs5, hrr5, hrr5_len, hok5', hm5'⟩
      c0_hsteps_nogrp
      refine wp_loop_break_group (brkTs := [i64, i64, i64]) (lpTs := [i64, i64])
        (fun (_budget_b, res_b, bi_b, ()) mb => ∃ sb : FullState,
          FullSparseInv c F0 sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (res_b = 1#64 ∨ res_b = 20#64) ∧ (res_b = 20#64 → F0.Unsat) ∧
          (FullMem c sb ⋆ R) mb)
        (fun rem (budget, bi, ()) mvi => ∃ svi : FullState,
          bi.toNat ≤ bn.toNat ∧ rem = bn.toNat - bi.toNat ∧
          FullSparseInv c F0 svi ∧ svi.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          fullArenaClauseRefs svi = fullArenaClauseRefs s2 ∧
          svi.scratch.red_refs = rr5 ∧ (FullMem c svi ⋆ R) mvi)
        ?_ ?_ ?_
      · rintro _ ⟨_, res_b, bi_b, ⟨⟩⟩ mb ⟨sb, hspb, hflb, hresb, h20b, hmb⟩
        refine wp_join_group (ts := [])
          (fun () m_bt => ∃ sbt : FullState,
            FullSparseInv c F0 sbt ∧ sbt.core.cur_level = 0 ∧
            sbt.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sbt ⋆ R) m_bt) ?_ ?_
        · rintro _ ⟨⟩ m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
          refine wp_join_group (ts := [])
            (fun () m_w => ∃ sw : FullState,
              FullSparseInv c F0 sw ∧ sw.core.cur_level = 0 ∧
              sw.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sw ⋆ R) m_w) ?_ ?_
          · rintro _ ⟨⟩ m_w ⟨sw, hspw, hclw, hflw, hm_w⟩
            fvt_steps
            let sf1 : FullState := { sw with scratch := { sw.scratch with res_sz := bi_b } }
            let sf : FullState := { sf1 with core := { sf1.core with probing := 0#64 } }
            have hspf : FullSparseInv c F0 sf :=
              FullVivTop.FullSparseInv.with_probing (s7_sparse_with_res_sz hspw bi_b) 0#64
            exact hQ res_b sf _ hspf (fun _ => hclw) (fun _ => rfl)
              (fun _ => ⟨hclw, rfl⟩) hflw hresb h20b hm
          · intro Jw hJw
            fvt_steps
            · c0_call hClearTier
              refine ⟨c, F0, sbt, R, rfl, hspbt, hclbt, hm_bt,
                fun sw m_w hspw hclw hflw hm_w =>
                  hJw () m_w ⟨sw, hspw, hclw, by rw [hflw]; exact hflbt, hm_w⟩⟩
            · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
            · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
            · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
        · intro Jbt hJbt
          obtain ⟨F_curb, hswb⟩ := hspb.exists_witness
          have hclb_lt : sb.core.cur_level < 2 ^ 64 := by
            have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
            have := hspb.1.lengths.core_ok.cur_vars_le; omega
          fvt_steps
          · c0_call hBacktrack
            refine ⟨c, sb, R, rfl, hspb.1.lengths, hclb_lt,
              (by intro _
                  have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
                  have := hspb.1.lengths.core_ok.cur_vars_le; omega),
              hswb.2.1.trail_lits_lt, hmb,
              fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                hlen_bt _ _ hcl_bt hpres_bt _ _ _ hw_bt _ hm_bt => ?_⟩
            have hsp_bt : FullSparseInv c F0 _ :=
              FullVivTop.FullSparseInv.of_backtrack hspb (Nat.zero_le _) hlen_bt hpres_bt
                (by simpa using hw_bt F0)
            exact hJbt () m_bt ⟨_, hsp_bt, by rw [hcl_bt]; simp, hflb, hm_bt⟩
          · have hclb0 : sb.core.cur_level = 0 := by
              have h0 : (BitVec.ofNat 64 sb.core.cur_level).toNat = 0 := by rw [hc]; rfl
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclb_lt] at h0
            exact hJbt () mb ⟨sb, hspb, hclb0, hflb, hmb⟩
      · intro B L rem ⟨budget, bi, ⟨⟩⟩ mvi hB hL
          ⟨svi, hbi_le, hrem, hspv, hflv, hrefsv, hrrv, hmvi⟩
        subst hrem
        fvt_to_group
        · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
          have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
          refine wp_join_group (ts := [i64])
            (fun (idx, ()) mi => mvi = mi ∧ idx.toNat < bn.toNat) ?_
            (fun Ji hJi => by
              fvt_steps
              · exact hJi (bi, ()) mvi ⟨rfl, hbi_lt⟩
              · exact hJi (bn - 1#64 - bi, ()) mvi ⟨rfl, by bv_omega⟩)
          rintro _ ⟨idx, ⟨⟩⟩ _ ⟨rfl, hidx_lt⟩
          have hidx_rr : idx.toNat < svi.scratch.red_refs.length := by rw [hrrv, hrr5_len]; omega
          let cr := svi.scratch.red_refs[idx.toNat]'hidx_rr
          have hcr_ref : cr.toNat ∈ fullArenaClauseRefs svi := by
            rw [hrefsv]
            have h := hok5' idx.toNat hidx_lt
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
            have heq : cr = rr5[idx.toNat]'(by omega) := Option.some.inj (by
              rw [← List.getElem?_eq_getElem hidx_rr, hrrv, List.getElem?_eq_getElem (by omega)])
            rwa [heq]
          obtain ⟨F_curv, hswv⟩ := hspv.exists_witness
          fvt_steps
          c0_call hVivClause
          refine ⟨c, F0, F_curv, svi, R, rfl, hswv, hcr_ref, hmvi,
            fun vc s_vc m_vc hsw_vc hfl_vc _ hrefs_vc hrr_vc hvc h20_vc hm_vc => ?_⟩
          have hrefs_vc2 : fullArenaClauseRefs s_vc = fullArenaClauseRefs s2 :=
            hrefs_vc.trans hrefsv
          have hrr_vc5 : s_vc.scratch.red_refs = rr5 := hrr_vc.trans hrrv
          have hfl_vc' : s_vc.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_vc hflv
          fvt_steps
          · exact hB (budget - 1#64, 20#64, bi, ()) m_vc
              ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inr rfl, fun _ => h20_vc (by c0_bound), hm_vc⟩
          · exact hB (budget - 1#64, 1#64, bi, ()) m_vc
              ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inl rfl, (fun h => by cases h), hm_vc⟩
          · have hcl_vc_lt : s_vc.core.cur_level < 2 ^ 64 := by
              have := hsw_vc.2.1.cur_level_le; have := hsw_vc.1.core_ok.trail_end_le
              have := hsw_vc.1.core_ok.cur_vars_le; omega
            have hcl_vc0 : s_vc.core.cur_level = 0 := by
              have h0 : (BitVec.ofNat 64 s_vc.core.cur_level).toNat = 0 := by
                have hc0 : BitVec.ofNat 64 s_vc.core.cur_level = 0#64 := by c0_bound
                rw [hc0]; rfl
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_vc_lt] at h0
            c0_call hProp
            refine ⟨c, F0, F_curv, s_vc, R, rfl, hsw_vc.1, hsw_vc.2.1, hsw_vc.2.2.2.2.2, hm_vc,
              fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
                wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
                ticks_p wsort_p phases_p delayed_p m_p hlen_p hw_p _ hperm_p _ hfl_p _ _ hpr1 _ _
                hm_p => ?_⟩
            let s_p : FullState :=
              { s_vc with
                core := { s_vc.core with
                  vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                  trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                  unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                  arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                  fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                  confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
                scratch := { s_vc.scratch with
                  search_ticks := ticks_p, wsort := wsort_p, phases := phases_p,
                  delayed := delayed_p } }
            have hsw_p : FullSparseInvW c F0 F_curv s_p :=
              s7_sparseInvW_of_prop_canon hsw_vc hlen_p hw_p hperm_p
            have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s_vc := hperm_p.2.1
            have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p hfl_vc'
            fvt_steps
            · have hpr_eq1 : pr = 1#64 := by c0_bound
              have hunsat : F0.Unsat :=
                FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl_vc0 (hpr1 hpr_eq1).2.2
              exact hB (budget - 1#64, 20#64, bi, ()) m_p
                ⟨s_p, hsw_p.toSparse, hfl_p', Or.inr rfl, fun _ => hunsat, hm_p⟩
            · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_p
                (by rw [hbi1]; omega)
                ⟨s_p, by rw [hbi1]; omega, rfl, hsw_p.toSparse, hfl_p',
                  hrefs_p.trans hrefs_vc2, hrr_vc5, hm_p⟩
          · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_vc
              (by rw [hbi1]; omega)
              ⟨s_vc, by rw [hbi1]; omega, rfl, hsw_vc.toSparse, hfl_vc', hrefs_vc2, hrr_vc5, hm_vc⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · intro B L _ hL; fvt_steps
        exact hL bn.toNat (budget0, 0#64, ()) m5
          ⟨s5, Nat.zero_le _, by simp, hsp5, hfl5, hrefs5, hrr5, hm5'⟩
    · intro Js hJs
      fvt_steps
      · c0_call hCount
        refine ⟨c, F0, s3, R, rfl, hsp3, hbn_le, hok3, hm3, fun tr3 m3c htr3 hm3c => ?_⟩
        let s3c : FullState := { s3 with scratch := { s3.scratch with tarjan_reach := tr3 } }
        have hsp3c : FullSparseInv c F0 s3c := s7_sparse_with_tr hsp3 htr3
        c0_call hSort
        refine ⟨c, F0, s3c, R, rfl, hsp3c, hbn_le, hok3, hm3c,
          fun rr4 scr4 m4 hrr4 hscr4 hok4 hm4 => ?_⟩
        let s4 : FullState :=
          { s3c with scratch := { s3c.scratch with red_refs := rr4, scratch_buf := scr4 } }
        have hsp4 : FullSparseInv c F0 s4 := s7_sparse_with_rr_scr hsp3c hrr4 hscr4
        exact hJs () m4 ⟨s4, rr4, hsp4, hfl2, rfl, rfl, hrr4, hok4, hm4⟩
      · exact hJs () m3 ⟨s3, rr3, hsp3, hfl2, rfl, rfl, hrr3, hok3, hm3⟩
  · intro Jc hJc
    obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have hcl0_lt : s.core.cur_level < 2 ^ 64 := by
      have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
      have := hsp0.1.lengths.core_ok.cur_vars_le; omega
    fvt_steps
    · c0_call hBacktrack
      refine ⟨c, s, R, rfl, hsp0.1.lengths, hcl0_lt,
        (by intro _
            have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
            have := hsp0.1.lengths.core_ok.cur_vars_le; omega),
        hsw0.2.1.trail_lits_lt, hm0,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp0 (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJc () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt] at h0
      exact hJc () m0 ⟨s, hsp0, hcl0, Nat.le_refl _, hm0⟩

/-! ## 4. `full_vivify_m6_hdr_step7_wp` (`FullM6OrchAdapters.m6aVivifySpec`) -/

private def S7VivStepInv (c : FullCfg) (F0 : CNF Nat) (ext0 : List (BitVec 64))
    (s0 : FullState) (R : Mem 64 → Prop) (didRun : Prop) :
    Tup Val [i64, i64] → Mem 64 → Prop := fun (r, _lim, ()) mk =>
  ∃ (extk : List (BitVec 64)) (sk : FullState),
    M6HdrExtOk extk ∧ (M6HdrExtInitOk ext0 → M6HdrExtInitOk extk ∧ M6ExtW2bPres ext0 extk) ∧
    FullSparseInv c F0 sk ∧ sk.core.cur_level = 0 ∧
    (didRun → sk.core.probing = 0#64) ∧ (r = 20#64 → sk.core.probing = 0#64) ∧
    sk.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
    (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧
    (FullMem c sk ⋆ (array64 (c.hdr - 2304) extk ⋆ R)) mk

/-- Parametric `Func.wp` proof for `fidStep7VivifyM6HdrFn` (`full_vivify_m6_hdr`,
`m6_hdr_get_tier{1,2}(h, true)` + trailing `m6_hdr_sync_legacy_tiers(h)`) against
`FullM6OrchAdapters.m6aVivifySpec`. -/
theorem full_vivify_m6_hdr_step7_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hGetTier1 : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "m6_hdr_get_tier1" [i64, .bool] [i64] a m Q X)
    (hGetTier2 : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "m6_hdr_get_tier2" [i64, .bool] [i64] a m Q X)
    (hSync : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X)
    (hDelaying : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hGetWm : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hVivTier : ∀ a m Q X, FullM6OrchAdapters.m6aVivifyTierSpec a m Q X →
      Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] a m Q X)
    (hBumpDelay : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullM6OrchAdapters.m6aVivifySpec a m Q X →
      Func.wp Γ fidStep7VivifyM6HdrFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hm, hQ⟩ :=
    FullM6OrchAdapters.m6aVivifySpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  obtain ⟨F_cur, hw0⟩ := hsp.1.witness
  have hco0 := hsp.1.lengths.core_ok
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  have hmax_vars_pos : 0 < s.core.cur_level → 0 < c.max_vars := by
    intro _; have := hw0.cur_level_le; have := hco0.trail_end_le
    have := hco0.cur_vars_le; omega
  rw [FullM6Hdr.fullM6HdrMem_iff] at hm
  unfold Func.wp fidStep7VivifyM6HdrFn full_vivify_m6_hdr_body; dsimp only; fvt_to_group
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m1)
    (fun _ () m1 ⟨s1, hsp1, hcl01, hfu1, hm1⟩ => ?_) (fun _ hJ => ?_)
  · clear hm
    c0_call hGetTier1
    refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg hext hsp1.1.lengths
      ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm1)
      fun ⟨t1, ⟨⟩⟩ ext1a s1a m1a hcore1a hlen1a hsc1a hext1a hw1a hm1a => ?_
    have hsp1a : FullSparseInv c F0 s1a := s7_sparseInv_of_core_eq hsp1 hlen1a hcore1a hsc1a
    rw [FullM6Hdr.fullM6HdrMem_iff] at hm1a
    fvt_to_group
    let s1b : FullState := { s1a with scratch := { s1a.scratch with tier1 := t1 } }
    have hsp1b : FullSparseInv c F0 s1b := s7_sparse_with_tier1 hsp1a t1
    c0_call hGetTier2
    refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg hext1a hsp1b.1.lengths
      ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm)
      fun ⟨t2, ⟨⟩⟩ ext2 s2a m2a hcore2 hlen2 hsc2 hext2 hw2 hm2a => ?_
    have hsp2a : FullSparseInv c F0 s2a := s7_sparseInv_of_core_eq hsp1b hlen2 hcore2 hsc2
    rw [FullM6Hdr.fullM6HdrMem_iff] at hm2a
    fvt_to_group
    let s2 : FullState := { s2a with scratch := { s2a.scratch with tier2 := t2 } }
    have hsp2 : FullSparseInv c F0 s2 := s7_sparse_with_tier2 hsp2a t2
    have hcl02 : s2.core.cur_level = 0 := by
      change s2a.core.cur_level = 0; rw [hcore2]; change s1a.core.cur_level = 0
      rw [hcore1a]; exact hcl01
    have hpres2 := s7_ext_pres_compose hw1a hw2
    have hfl2_le : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by
      change s2a.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hcore2]
      change s1a.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hcore1a]; exact hfu1
    have hm2 : (FullM6HdrMem c ext2 s2 ⋆ R) _ := (FullM6Hdr.fullM6HdrMem_iff ..).mpr hm
    refine wp_join_group (ts := [i64])
      (fun (_w0, ()) m3 => ∃ ext3 s3, M6HdrExtOk ext3 ∧
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext3 ∧ M6ExtW2bPres ext ext3) ∧
        FullSparseInv c F0 s3 ∧ s3.core.cur_level = 0 ∧
        s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullMem c s3 ⋆ (array64 (c.hdr - 2304) ext3 ⋆ R)) m3) ?_
      (fun Jw0 hJw0 => by
        c0_call hDelaying
        refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg hext2 hsp2.1.lengths hm2
          fun ⟨del0, ⟨⟩⟩ ext3 s3 m3 hcore3 hlen3 hsc3 hext3 hw3 hm3 => ?_
        have hsp3 : FullSparseInv c F0 s3 := s7_sparseInv_of_core_eq hsp2 hlen3 hcore3 hsc3
        have hcl03 : s3.core.cur_level = 0 := by rw [hcore3]; exact hcl02
        have hpres3 := s7_ext_pres_compose hpres2 hw3
        have hfl3_le : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcore3]; exact hfl2_le
        rw [FullM6Hdr.fullM6HdrMem_iff] at hm3
        fvt_steps <;> exact hJw0 _ m3 ⟨ext3, s3, hext3, hpres3, hsp3, hcl03, hfl3_le, hm3⟩)
    rintro _ ⟨w0, ⟨⟩⟩ m3 ⟨ext3, s3, hext3, hpres3, hsp3, hcl03, hfl3_le, hm3⟩
    fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ mw1 => m3 = mw1) ?_
      (fun Jw1 hJw1 => by fvt_steps <;> exact hJw1 _ m3 rfl)
    rintro _ ⟨w1_0, ⟨⟩⟩ _ rfl; fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ mw2 => m3 = mw2) ?_
      (fun Jw2 hJw2 => by fvt_steps <;> exact hJw2 _ m3 rfl)
    rintro _ ⟨w2_0, ⟨⟩⟩ _ rfl; fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ mw3 => m3 = mw3) ?_
      (fun Jw3 hJw3 => by fvt_steps <;> exact hJw3 _ m3 rfl)
    rintro _ ⟨w3, ⟨⟩⟩ _ rfl; fvt_to_group
    · fvt_steps
      let s3p : FullState := { s3 with core := { s3.core with probing := 0#64 } }
      have hsp3p : FullSparseInv c F0 s3p := FullVivTop.FullSparseInv.with_probing hsp3 0#64
      exact hQ 1#64 ext3 s3p _ ⟨hext3, hpres3⟩ hsp3p ⟨hcl03, rfl⟩ hfl3_le
        (Or.inl rfl) (fun h => by cases h) ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm)
    · have hsum_nz : w0 + w1_0 + w2_0 + w3 ≠ 0#64 := by c0_bound
      fvt_steps
      c0_call hGetWm
      refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg hext3 hsp3.1.lengths
        ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm3)
        fun ⟨last_p, ⟨⟩⟩ ext4 s4 m4 hcore4 hlen4 hsc4 hext4 hw4 hm4 => ?_
      have hsp4 : FullSparseInv c F0 s4 := s7_sparseInv_of_core_eq hsp3 hlen4 hcore4 hsc4
      have hcl04 : s4.core.cur_level = 0 := by rw [hcore4]; exact hcl03
      have hpres4 := s7_ext_pres_compose hpres3 hw4
      have hfl4_le : s4.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcore4]; exact hfl3_le
      rw [FullM6Hdr.fullM6HdrMem_iff] at hm4
      let start := s3.scratch.search_ticks
      have hbud : (0xFFFFFFFF#64 : BitVec 64) ≠ 0#64 := by bv_omega
      fvt_to_group
      refine wp_join_group (ts := [i64]) (fun _ md => m4 = md) ?_
        (fun Jd hJd => by fvt_steps <;> exact hJd _ m4 rfl)
      rintro _ ⟨delta, ⟨⟩⟩ _ rfl; fvt_to_group
      refine wp_join_group (ts := [i64]) (fun _ me => m4 = me) ?_
        (fun Je hJe => by fvt_steps <;> exact hJe _ m4 rfl)
      rintro _ ⟨eff_ref, ⟨⟩⟩ _ rfl; fvt_to_group
      refine wp_join_group (ts := [i64, i64])
        (fun (w1, w2, ()) mwg => m4 = mwg ∧ w1 + w2 = w1_0 + w2_0) ?_
        (fun Jwg hJwg => by fvt_steps <;> exact hJwg _ m4 ⟨rfl, by bv_omega⟩)
      rintro _ ⟨w1, w2, ⟨⟩⟩ _ ⟨rfl, hw12⟩
      let StepInv (didRun : Prop) := S7VivStepInv c F0 ext s R didRun
      have hTierCall : ∀ (extk : List (BitVec 64)) (sk : FullState) (mk : Mem 64)
          (tm limk : BitVec 64) (didNext : Prop),
          M6HdrExtOk extk → (M6HdrExtInitOk ext → M6HdrExtInitOk extk ∧ M6ExtW2bPres ext extk) →
          FullSparseInv c F0 sk → sk.core.fuel.toNat ≤ s.core.fuel.toNat →
          (FullMem c sk ⋆ (array64 (c.hdr - 2304) extk ⋆ R)) mk →
          ∀ (K : Tup Val [i64] → Mem 64 → Prop),
          (∀ rk mk', StepInv didNext (rk, limk, ()) mk' → K (rk, ()) mk') →
          Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64]
            (c.hdr, tm, 0xFFFFFFFF#64, limk, ()) mk K X := by
        intro extk sk mk tm limk _ hek hpk hspk hfk hmk K hK
        apply hVivTier
        refine FullM6OrchAdapters.m6aVivifyTierSpec_of hspk hmk
          fun rk s' m' hsp' _ _ hbp' hfu' hres' huns' hm' => ?_
        obtain ⟨hcl', hpr'⟩ := hbp' hbud
        exact hK rk m' ⟨extk, s', hek, hpk, hsp', hcl', fun _ => hpr', fun _ => hpr',
          Nat.le_trans hfu' hfk, hres', huns', hm'⟩
      s7_to_group_np
      refine wp_join_group (ts := [i64, i64]) (StepInv (w1 ≠ 0#64)) ?_ ?_
      · rintro _ ⟨r1, lim1, ⟨⟩⟩ m1 ⟨ext1, s1', he1, hp1, hsp1', hcl1, hpr1, hpr1r,
          hfu1', hr1, hu1, hm1'⟩
        s7_to_group_np
        refine wp_join_group (ts := [i64, i64]) (StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64)) ?_ ?_
        · rintro _ ⟨r2, lim2, ⟨⟩⟩ m2 ⟨ext2, s2', he2, hp2, hsp2', hcl2, hpr2, hpr2r,
            hfu2', hr2, hu2, hm2'⟩
          s7_to_group_np
          refine wp_join_group (ts := [i64, i64])
            (StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64)) ?_ ?_
          · rintro _ ⟨r3, lim3, ⟨⟩⟩ m3' ⟨ext3', s3', he3', hp3', hsp3', hcl3, hpr3, hpr3r,
              hfu3', hr3, hu3, hm3'⟩
            s7_to_group_np
            refine wp_join_group (ts := [i64, i64])
              (StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64 ∨ w0 ≠ 0#64)) ?_ ?_
            · rintro _ ⟨r4, _lim4, ⟨⟩⟩ m4' ⟨ext4', s4', he4', hp4', hsp4', hcl4, hpr4, _,
                hfu4', hr4, hu4, hm4'⟩
              have hsome : w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64 ∨ w0 ≠ 0#64 :=
                Classical.byContradiction fun hno => by
                  have h1 : w1 = 0#64 := Classical.byContradiction fun h => hno (Or.inl h)
                  have h2 : w2 = 0#64 := Classical.byContradiction fun h => hno (Or.inr (Or.inl h))
                  have h3 : w3 = 0#64 :=
                    Classical.byContradiction fun h => hno (Or.inr (Or.inr (Or.inl h)))
                  have h0 : w0 = 0#64 :=
                    Classical.byContradiction fun h => hno (Or.inr (Or.inr (Or.inr h)))
                  apply hsum_nz; bv_omega
              have hpr4' : s4'.core.probing = 0#64 := hpr4 hsome
              c0_call hSync
              refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg he4' hsp4'.1.lengths
                ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm4')
                fun () ext5 s5 m5 hcore5 hlen5 hsc5 he5 hw5 hm5 => ?_
              have hsp5 : FullSparseInv c F0 s5 := s7_sparseInv_of_core_eq hsp4' hlen5 hcore5 hsc5
              have hcl5 : s5.core.cur_level = 0 := by rw [hcore5]; exact hcl4
              have hpr5 : s5.core.probing = 0#64 := by rw [hcore5]; exact hpr4'
              have hfu5 : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcore5]; exact hfu4'
              have hp5 := s7_ext_pres_compose hp4' hw5
              rw [FullM6Hdr.fullM6HdrMem_iff] at hm5
              s7_steps_np
              let sfin : FullState :=
                { s5 with scratch := { s5.scratch with search_ticks := start } }
              have hsp_fin : FullSparseInv c F0 sfin := s7_sparse_with_ticks hsp5 start
              exact hQ r4 ext5 sfin _ ⟨he5, hp5⟩ hsp_fin ⟨hcl5, hpr5⟩ hfu5 hr4 hu4
                ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm)
            · intro J0 hJ0
              have hskip0 : (r3 = 20#64 ∨ w0 = 0#64) →
                  StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64 ∨ w0 ≠ 0#64) (r3, lim3, ()) m3' := by
                intro hsk
                refine ⟨ext3', s3', he3', hp3', hsp3', hcl3, ?_, hpr3r, hfu3', hr3, hu3, hm3'⟩
                intro hd
                rcases hsk with rfl | h0
                · exact hpr3r rfl
                · rcases hd with h | h | h | h
                  · exact hpr3 (Or.inl h)
                  · exact hpr3 (Or.inr (Or.inl h))
                  · exact hpr3 (Or.inr (Or.inr h))
                  · exact absurd h0 h
              s7_to_group_np
              · s7_to_group_np
                refine wp_join_group (ts := [i64]) (fun _ ml => m3' = ml) ?_
                  (fun Jl hJl => by s7_steps_np <;> exact hJl _ m3' rfl)
                rintro _ ⟨lim4, ⟨⟩⟩ _ rfl
                s7_to_group_np
                refine wp_call_of_spec _ _ (hTierCall ext3' s3' m3' 0#64 lim4
                  (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64 ∨ w0 ≠ 0#64) he3' hp3' hsp3' hfu3' hm3' _ ?_)
                rintro (r4 : Val i64) m4a ⟨ext4a, s4a, he4a, hp4a, hsp4a, hcl4a, hpr4a, hpr4ar,
                  hfu4a, hr4a, hu4a, hm4a⟩
                c0_hsteps_nogrp
                refine wp_join_group (ts := [])
                  (fun () m4b => StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64 ∨ w0 ≠ 0#64)
                    (r4, lim4, ()) m4b)
                  (fun _ () m4b hm4b => hJ0 (r4, lim4, ()) m4b hm4b)
                  (fun Jif hJif => by
                    c0_hsplit
                    · s7_to_group_np
                      refine wp_join_group (ts := [i64]) (fun _ my => m4a = my) ?_
                        (fun Jy hJy => by s7_steps_np <;> exact hJy _ m4a rfl)
                      rintro _ ⟨_du, ⟨⟩⟩ _ rfl
                      s7_to_group_np
                      refine wp_join_group (ts := [])
                        (fun () md' => StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64 ∨ w0 ≠ 0#64)
                          (r4, lim4, ()) md')
                        (fun _ () md' hmd' => hJif () md' hmd')
                        (fun Jd hJd => by
                          have hBump : wp Γ Q X
                              (Expr.call (as := [i64, i64]) (bs := []) "m6_hdr_bump_delay"
                                (Arg.var c.hdr, Arg.imm 3, ()) fun _ => Expr.jump Jd ()) m4a := by
                            c0_call hBumpDelay
                            refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg he4a hsp4a.1.lengths
                              ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm4a)
                              fun () ext4b s4b m4b hcore4b hlen4b hsc4b he4b hw4b hm4b => ?_
                            have hsp4b := s7_sparseInv_of_core_eq hsp4a hlen4b hcore4b hsc4b
                            exact hJd () m4b ⟨ext4b, s4b, he4b, s7_ext_pres_compose hp4a hw4b,
                              hsp4b, by rw [hcore4b]; exact hcl4a,
                              fun hd => by rw [hcore4b]; exact hpr4a hd,
                              fun hr => by rw [hcore4b]; exact hpr4ar hr,
                              by rw [hcore4b]; exact hfu4a, hr4a, hu4a,
                              (FullM6Hdr.fullM6HdrMem_iff ..).mp hm4b⟩
                          have hRed : wp Γ Q X
                              (Expr.call (as := [i64, i64]) (bs := []) "m6_hdr_reduce_delay"
                                (Arg.var c.hdr, Arg.imm 3, ()) fun _ => Expr.jump Jd ()) m4a := by
                            c0_call hReduceDelay
                            refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg he4a hsp4a.1.lengths
                              ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm4a)
                              fun () ext4b s4b m4b hcore4b hlen4b hsc4b he4b hw4b hm4b => ?_
                            have hsp4b := s7_sparseInv_of_core_eq hsp4a hlen4b hcore4b hsc4b
                            exact hJd () m4b ⟨ext4b, s4b, he4b, s7_ext_pres_compose hp4a hw4b,
                              hsp4b, by rw [hcore4b]; exact hcl4a,
                              fun hd => by rw [hcore4b]; exact hpr4a hd,
                              fun hr => by rw [hcore4b]; exact hpr4ar hr,
                              by rw [hcore4b]; exact hfu4a, hr4a, hu4a,
                              (FullM6Hdr.fullM6HdrMem_iff ..).mp hm4b⟩
                          s7_steps_np <;> first | exact hBump | exact hRed)
                    · exact hJif () m4a
                        ⟨ext4a, s4a, he4a, hp4a, hsp4a, hcl4a, hpr4a, hpr4ar, hfu4a, hr4a, hu4a,
                          hm4a⟩)
              · exact hJ0 (r3, lim3, ()) m3' (hskip0 (Or.inr (by c0_bound)))
              · exact hJ0 (r3, lim3, ()) m3' (hskip0 (Or.inl (by c0_bound)))
          · intro J3 hJ3
            have hskip3 : (r2 = 20#64 ∨ w3 = 0#64) →
                StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64) (r2, lim2, ()) m2 := by
              intro hsk
              refine ⟨ext2, s2', he2, hp2, hsp2', hcl2, ?_, hpr2r, hfu2', hr2, hu2, hm2'⟩
              intro hd
              rcases hsk with rfl | h3
              · exact hpr2r rfl
              · rcases hd with h | h | h
                · exact hpr2 (Or.inl h)
                · exact hpr2 (Or.inr h)
                · exact absurd h3 h
            s7_to_group_np
            · s7_to_group_np
              refine wp_join_group (ts := [i64]) (fun _ ml => m2 = ml) ?_
                (fun Jl hJl => by s7_steps_np <;> exact hJl _ m2 rfl)
              rintro _ ⟨lim3, ⟨⟩⟩ _ rfl
              refine wp_call_of_spec _ _ (hTierCall ext2 s2' m2 3#64 lim3
                (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64) he2 hp2 hsp2' hfu2' hm2' _ ?_)
              intro r3 m3' h3; exact hJ3 (r3, lim3, ()) m3' h3
            · exact hJ3 (r2, lim2, ()) m2 (hskip3 (Or.inr (by c0_bound)))
            · exact hJ3 (r2, lim2, ()) m2 (hskip3 (Or.inl (by c0_bound)))
        · intro J2 hJ2
          have hskip2 : (r1 = 20#64 ∨ w2 = 0#64) →
              StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64) (r1, lim1, ()) m1 := by
            intro hsk
            refine ⟨ext1, s1', he1, hp1, hsp1', hcl1, ?_, hpr1r, hfu1', hr1, hu1, hm1'⟩
            intro hd
            rcases hsk with rfl | h2
            · exact hpr1r rfl
            · rcases hd with h | h
              · exact hpr1 h
              · exact absurd h2 h
          s7_to_group_np
          · s7_to_group_np
            refine wp_join_group (ts := [i64]) (fun _ ml => m1 = ml) ?_
              (fun Jl hJl => by s7_steps_np <;> exact hJl _ m1 rfl)
            rintro _ ⟨lim2, ⟨⟩⟩ _ rfl
            refine wp_call_of_spec _ _ (hTierCall ext1 s1' m1 2#64 lim2
              (w1 ≠ 0#64 ∨ w2 ≠ 0#64) he1 hp1 hsp1' hfu1' hm1' _ ?_)
            intro r2 m2 h2; exact hJ2 (r2, lim2, ()) m2 h2
          · exact hJ2 (r1, lim1, ()) m1 (hskip2 (Or.inr (by c0_bound)))
          · exact hJ2 (r1, lim1, ()) m1 (hskip2 (Or.inl (by c0_bound)))
      · intro J1 hJ1
        s7_to_group_np
        · s7_to_group_np
          refine wp_join_group (ts := [i64]) (fun _ ml => m4 = ml) ?_
            (fun Jl hJl => by s7_steps_np <;> exact hJl _ m4 rfl)
          rintro _ ⟨lim1, ⟨⟩⟩ _ rfl
          refine wp_call_of_spec _ _ (hTierCall ext4 s4 m4 1#64 lim1 (w1 ≠ 0#64)
            hext4 hpres4 hsp4 hfl4_le hm4 _ ?_)
          intro r1 m1 h1; exact hJ1 (r1, lim1, ()) m1 h1
        · have hw1_0 : w1 = 0#64 := by c0_bound
          exact hJ1 (1#64, start, ()) m4
            ⟨ext4, s4, hext4, hpres4, hsp4, hcl04, fun h => absurd hw1_0 h,
             fun h => absurd h (by bv_omega), hfl4_le, Or.inl rfl,
             fun h => absurd h (by bv_omega), hm4⟩
  · fvt_steps
    · c0_call hBacktrack
      refine ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1.lengths, hclv_lt, hmax_vars_pos,
        hw0.trail_lits_lt, hm, fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJ () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at h0
      exact hJ () m ⟨s, hsp, hcl0, Nat.le_refl _, hm⟩

/-! ## 5. `full_bve_var_key_m7_step7_wp` (`fullBveVarKeyM6Spec` & `m8BveVarKeySpec`) -/

private theorem fidStep7BveVarKeyM7_core (Γ : Env) (c : FullCfg) (s : FullState)
    (R : Mem 64 → Prop) (v : BitVec 32) (m0 : Mem 64) (Q : Post [i64]) (X : XPost)
    (hlen : s.LengthsOk c) (hm0 : (FullMem c s ⋆ R) m0) (hQ : ∀ r : BitVec 64, Q (r, ()) m0) :
    Func.wp Γ fidStep7BveVarKeyM7Fn.body (c.hdr, v, ()) m0 Q X := by
  have hmx := c.hmaxv; unfold LratBytes.dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  unfold Func.wp fidStep7BveVarKeyM7Fn full_bve_var_key_m7_body; dsimp only
  c0_hsplit
  · c0_hsteps!; exact hQ 0#64
  · have hv_lt : v.toNat < s.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
    have hwv1 : ((v.setWidth 64 <<< (2 : Nat)) + 1#64).toNat < s.core.wvec.length := by
      rw [hlen.core_ok.wvec_len]; c0_bound
    have hwv3 : ((v.setWidth 64 <<< (2 : Nat)) + 3#64).toNat < s.core.wvec.length := by
      rw [hlen.core_ok.wvec_len]; c0_bound
    have hv_sc : (v.setWidth 64).toNat < s.scratch.score.length := by
      rw [hlen.scratch_ok.score_len, m6_zext32_toNat]; omega
    have hv_qs : (v.setWidth 64).toNat < s.scratch.q_stamp.length := by
      rw [hlen.scratch_ok.q_stamp_len, m6_zext32_toNat]; omega
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ())) (fun _ => True)
      (fun _ _ _ => by
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
              (fun _ => True)
              (fun _ _ _ => by c0_hsteps! <;> exact hQ _)
              (fun Jr hJr => by c0_hsplit <;> (c0_hsteps!; exact hJr _ trivial)))
          (fun Jn hJn => by c0_hsplit <;> (c0_hsteps!; exact hJn _ trivial)))
      (fun Jp hJp => by c0_hsplit <;> (c0_hsteps!; exact hJp _ trivial))

/-- Parametric `Func.wp` proof for `fidStep7BveVarKeyM7Fn` (`full_bve_var_key_m7`,
`sc[v] >> 28` in stable mode) against `FullM6BveFwd.fullBveVarKeyM6Spec`. -/
theorem full_bve_var_key_m7_step7_wp (Γ : Env) :
    ∀ a m Q X, FullM6BveFwd.fullBveVarKeyM6Spec a m Q X →
      Func.wp Γ fidStep7BveVarKeyM7Fn.body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  exact fidStep7BveVarKeyM7_core Γ c s R v m0 Q X hlen hm0 hQ

/-- Sibling `Func.wp` proof for `fidStep7BveVarKeyM7Fn` against
`FullM8CoreParity.m8BveVarKeySpec` (matches `fidEnv` row). -/
theorem full_bve_var_key_m7_m8_step7_wp (Γ : Env) :
    ∀ a m Q X, FullM8CoreParity.m8BveVarKeySpec a m Q X →
      Func.wp Γ fidStep7BveVarKeyM7Fn.body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, s, R, rfl, hlen, hm0, hQ⟩ := FullM8CoreParity.m8BveVarKeySpec_elim hs
  exact fidStep7BveVarKeyM7_core Γ c s R v m0 Q X hlen hm0 hQ

/-! ## 6. `full_eliminate_m7_step7_wp` (`FullFastSched.schedEliminateSpec`) -/

/-- Parametric `Func.wp` proof for `fidStep7EliminateM7Fn` (`full_eliminate_m7`,
`saved_st = search_ticks`, `full_ilog10`, `fbud = dticks / 10`, restoring `search_ticks`)
against `FullFastSched.schedEliminateSpec`. -/
theorem full_eliminate_m7_step7_wp (Γ : Env)
    (hDticks : ∀ a m Q X, FullFastSched.schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog10 : ∀ a m Q X, Full.fullIlog10Spec a m Q X →
      Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub_m7" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Func.wp Γ fidStep7EliminateM7Fn.body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hinv0, hcl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold LratBytes.dimacsBound at hmx
  unfold Func.wp fidStep7EliminateM7Fn full_eliminate_m7_body; dsimp only
  c0_hsteps_nogrp
  c0_call hDticks
  refine ⟨c, s0, R, rfl, hinv0.lengths, hm0, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hinv1, _, hfu1, hm1⟩ => by
      c0_hsteps_nogrp
      c0_call hEnter
      refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
      intro ok s2 m2 hcl2 hfu2 hok_d hfail_s hm2
      c0_hsplit
      · have hden2 : FullDenseInv c F0 s2 := hok_d hc
        c0_hsteps_nogrp
        c0_call hFwd
        refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
        intro fs s3 m3 hden3 hcv3 hfu3 _ huf3 hm3
        have hcv2_le := hden2.lengths.core_ok.cur_vars_le
        let s3r : FullState :=
          { s3 with scratch := { s3.scratch with fwd_sub_cnt := s2.scratch.fwd_sub_cnt } }
        have hden3r : FullDenseInv c F0 s3r :=
          FullM3CongBva.fullDenseInv_with_scratch_keep hden3
            { hden3.lengths.scratch_ok with
              walk_vals_len := hden3.lengths.scratch_ok.walk_vals_len } rfl rfl
        have hfu3r : s3r.core.fuel.toNat ≤ s0.core.fuel.toNat := by
          change s3.core.fuel.toNat ≤ s0.core.fuel.toNat; rw [hfu3]; omega
        c0_hsplit
        · c0_hsteps_nogrp
          c0_call hReb
          refine ⟨c, F0, s3r, R, rfl, hden3r, hm, ?_⟩
          intro _ s4 m4 hsp4 hcl4 hfu4 _ _ hm4
          c0_hsteps!
          exact hQ 20#64 s4 m4 hsp4 hcl4 (by omega) (Or.inr rfl) (fun _ => huf3 hc) hm4
        · let cv3 := s3r.core.cur_vars
          have hcv3_le : cv3 ≤ c.max_vars := hden3r.lengths.core_ok.cur_vars_le
          have htl3 := hden3r.lengths.scratch_ok.tarjan_mark_len
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64])
            (fun rem_t (ti, ()) mt => ∃ tmki : List (BitVec 32),
              tmki.length = 2 * c.max_vars ∧ ti.toNat ≤ cv3 ∧ rem_t = cv3 - ti.toNat ∧
              (∀ k < ti.toNat, tmki[k]?.getD 0#32 = 0#32) ∧
              (FullMem c { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } } ⋆ R) mt)
            ?_ ?_
          · rintro Lt rem_t ⟨ti, ⟨⟩⟩ mt hLt ⟨tmki, htli, hti_le, rfl, hinit, hmt⟩
            c0_hsplit
            · have hti_lt : ti.toNat < cv3 := by
                rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
              have hti_b : ti.toNat < tmki.length := by omega
              have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by c0_bound
              c0_hsteps!
              exact hLt (cv3 - (ti + 1#64).toNat) (ti + 1#64, ()) _ (by omega)
                ⟨tmki.set ti.toNat 0#32, by simp [htli], by omega, rfl, fun k hk => by
                   rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hti1 ▸ hk)) with h | h
                   · rw [List.getElem?_set_ne (by omega)]; exact hinit k h
                   · subst h; rw [List.getElem?_set_self hti_b, Option.getD_some], hm⟩
            · have hti_eq : ti.toNat = cv3 := by
                rw [Nat.mod_eq_of_lt (by omega)] at hc
                change ¬ti.toNat < cv3 at hc; omega
              rw [hti_eq] at hinit
              let s3t : FullState :=
                { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } }
              have hden3t : FullDenseInv c F0 s3t :=
                FullM3CongBva.fullDenseInv_with_scratch_keep hden3r
                  { hden3r.lengths.scratch_ok with tarjan_mark_len := htli } rfl rfl
              have htmk3t : FullDefSweep.TmkZero s3t := fun v hv => hinit v hv
              c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                (fun b => (b, ())) (fun _ => True)
                (fun _ bve_lim _ => by
                  c0_hsteps_nogrp
                  c0_call hBve
                  refine ⟨c, F0, s3t, R, rfl, hden3t, htmk3t, hmt, ?_⟩
                  intro res s4 m4 hden4 _ hfu4 _ hres_u hm4
                  have hfu4' : s4.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                    dsimp only [s3t, s3r] at hfu4
                    have hfu3' : s3.core.fuel.toNat ≤ s0.core.fuel.toNat := hfu3r
                    omega
                  c0_hsteps_nogrp
                  refine wp_join_state0 (α := FullState)
                    (fun sf mf => FullDenseInv c F0 sf ∧
                      sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sf ⋆ R) mf)
                    (fun _ sf mf ⟨hdenf, hfuf, hmf⟩ => by
                      c0_hsteps_nogrp
                      c0_call hReb
                      refine ⟨c, F0, sf, R, rfl, hdenf, hmf, ?_⟩
                      intro rr se me hspe hcle hfue _ hue hme
                      let se' : FullState :=
                        { se with scratch :=
                          { se.scratch with
                            search_ticks := s0.scratch.search_ticks
                            fwd_str_cnt := s0.scratch.search_ticks } }
                      have hspe' : FullSparseInv c F0 se' :=
                        FullM3CongBva.fullSparseInv_with_scratch_keep hspe
                          { hspe.lengths.scratch_ok with
                            walk_vals_len := hspe.lengths.scratch_ok.walk_vals_len } rfl rfl
                      have hfue' : se'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                        change se.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
                      c0_hsteps!
                      · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                          (fun _ => hres_u hc) hm
                      · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                          (fun _ => hue hc) hm
                      · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                          (fun _ => hspe'.inconsistent_unsat hc) hm
                      · exact hQ 1#64 se' _ hspe' hcle hfue' (Or.inl rfl)
                          (fun h => by cases h) hm)
                    (fun Jf hJf => by
                      c0_hsplit
                      · c0_hsteps_nogrp
                        refine wp_join_state0 (α := FullState)
                          (fun sg mg => FullDenseInv c F0 sg ∧
                            sg.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sg ⋆ R) mg)
                          (fun _ sg mg ⟨hdeng, hfug, hmg⟩ => by
                            c0_hsteps_nogrp
                            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                              (fun b => (b, ())) (fun _ => True)
                              (fun _ _ _ => by
                                c0_hsteps_nogrp
                                c0_call hMin; intro fact_bud _
                                c0_hsteps_nogrp
                                let sg0 : FullState :=
                                  { sg with scratch := { sg.scratch with elim_bound := 0#64 } }
                                have hdeng0 : FullDenseInv c F0 sg0 :=
                                  FullM3CongBva.fullDenseInv_with_scratch_keep hdeng
                                    { hdeng.lengths.scratch_ok with
                                      walk_vals_len := hdeng.lengths.scratch_ok.walk_vals_len }
                                    rfl rfl
                                c0_call hFact
                                refine ⟨c, F0, sg0, R, rfl, hdeng0, hm, ?_⟩
                                intro _ sf0 mf0 hdenf0 _ hfuf0 _ hmf0
                                c0_hsteps!
                                let sf1 : FullState :=
                                  { sf0 with scratch :=
                                    { sf0.scratch with elim_bound := sg.scratch.elim_bound } }
                                have hdenf1 : FullDenseInv c F0 sf1 :=
                                  FullM3CongBva.fullDenseInv_with_scratch_keep hdenf0
                                    { hdenf0.lengths.scratch_ok with
                                      walk_vals_len := hdenf0.lengths.scratch_ok.walk_vals_len }
                                    rfl rfl
                                exact hJf sf1 _ ⟨hdenf1, by
                                  change sf0.core.fuel.toNat ≤ s0.core.fuel.toNat
                                  rw [hfuf0]; exact hfug, hm⟩)
                              (fun Jfb hJfb => by
                                c0_hsplit <;> (c0_hsteps!; exact hJfb _ trivial)))
                          (fun Jdo hJdo => by
                            c0_hsteps!
                            · exact hJdo s4 m4 ⟨hden4, hfu4', hm4⟩
                            · exact hJdo s4 m4 ⟨hden4, hfu4', hm4⟩
                            · exact hJf s4 m4 ⟨hden4, hfu4', hm4⟩)
                      · c0_hsteps!; exact hJf s4 m4 ⟨hden4, hfu4', hm4⟩))
                (fun Jb hJb => by
                  c0_hsplit
                  · c0_hsteps!; exact hJb _ trivial
                  · c0_hsteps_nogrp; c0_call hMin; intro b _; c0_hsteps!; exact hJb b trivial)
          · intro Lt hLt; c0_hsteps!
            exact hLt cv3 (0#64, ()) _
              ⟨s3r.scratch.tarjan_mark, htl3, Nat.zero_le _, by simp,
               fun _ h => by simp at h, hm⟩
      · have hsp2 : FullSparseInv c F0 s2 := hfail_s hc
        let s2' : FullState :=
          { s2 with scratch := { s2.scratch with fwd_str_cnt := s2.scratch.search_ticks } }
        have hsp2' : FullSparseInv c F0 s2' := FullM3CongBva.fullSparseInv_with_scratch_keep hsp2
          { hsp2.lengths.scratch_ok with walk_vals_len := hsp2.lengths.scratch_ok.walk_vals_len }
          rfl rfl
        have hfu2' : s2'.core.fuel.toNat ≤ s0.core.fuel.toNat := Nat.le_trans hfu2 hfu1
        c0_hsteps!
        · exact hQ 20#64 s2' _ hsp2' hcl2 hfu2' (Or.inr rfl)
            (fun _ => hsp2'.inconsistent_unsat hc) hm
        · exact hQ 1#64 s2' _ hsp2' hcl2 hfu2' (Or.inl rfl) (fun h => by cases h) hm)
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps!; exact hJ1 s0 m0 ⟨hinv0, hcl0, Nat.le_refl _, hm0⟩
      · c0_hsteps_nogrp
        let s0a : FullState :=
          { s0 with scratch := { s0.scratch with eliminations := s0.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c := ⟨hinv0.lengths.core_ok,
          { hinv0.lengths.scratch_ok with walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len }⟩
        c0_call hIlog10; intro loge _ _; c0_hsteps_nogrp
        c0_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, fun delta => ?_⟩; c0_hsteps!
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b := FullM3CongBva.fullSparseInv_with_scratch_keep hinv0
          { hinv0.lengths.scratch_ok with walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len }
          rfl rfl
        exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

/-! ## 7. `full_eliminate_m6_step7_wp` (`FullFastSched.schedEliminateSpec`) -/

/-- Parametric `Func.wp` proof for `fidStep7EliminateM6Fn` (`full_eliminate_m6`,
`saved_st = search_ticks`, `fbase = max(dticks, 10000000)`, callee `full_forward_sub_m7`,
restoring `search_ticks`) against `FullFastSched.schedEliminateSpec`. -/
theorem full_eliminate_m6_step7_wp (Γ : Env)
    (hDticks : ∀ a m Q X, FullFastSched.schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hLog : ∀ a m Q X, FullM7Search.m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub_m7" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Func.wp Γ fidStep7EliminateM6Fn.body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hinv0, hcl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold LratBytes.dimacsBound at hmx
  unfold Func.wp fidStep7EliminateM6Fn full_eliminate_m6_body; dsimp only
  c0_hsteps_nogrp
  c0_call hDticks
  refine ⟨c, s0, R, rfl, hinv0.lengths, hm0, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hinv1, _, hfu1, hm1⟩ => by
      c0_hsteps_nogrp
      c0_call hEnter
      refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
      intro ok s2 m2 hcl2 hfu2 hok_d hfail_s hm2
      c0_hsplit
      · have hden2 : FullDenseInv c F0 s2 := hok_d hc
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun b => (b, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps_nogrp
            c0_call hFwd
            refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
            intro fs s3 m3 hden3 hcv3 hfu3 _ huf3 hm3
            have hcv2_le := hden2.lengths.core_ok.cur_vars_le
            let s3r : FullState :=
              { s3 with scratch := { s3.scratch with fwd_sub_cnt := s2.scratch.fwd_sub_cnt } }
            have hden3r : FullDenseInv c F0 s3r :=
              FullM3CongBva.fullDenseInv_with_scratch_keep hden3
                { hden3.lengths.scratch_ok with
                  walk_vals_len := hden3.lengths.scratch_ok.walk_vals_len } rfl rfl
            have hfu3r : s3r.core.fuel.toNat ≤ s0.core.fuel.toNat := by
              change s3.core.fuel.toNat ≤ s0.core.fuel.toNat; rw [hfu3]; omega
            c0_hsplit
            · c0_hsteps_nogrp
              c0_call hReb
              refine ⟨c, F0, s3r, R, rfl, hden3r, hm, ?_⟩
              intro _ s4 m4 hsp4 hcl4 hfu4 _ _ hm4
              c0_hsteps!
              exact hQ 20#64 s4 m4 hsp4 hcl4 (by omega) (Or.inr rfl) (fun _ => huf3 hc) hm4
            · let cv3 := s3r.core.cur_vars
              have hcv3_le : cv3 ≤ c.max_vars := hden3r.lengths.core_ok.cur_vars_le
              have htl3 := hden3r.lengths.scratch_ok.tarjan_mark_len
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i64])
                (fun rem_t (ti, ()) mt => ∃ tmki : List (BitVec 32),
                  tmki.length = 2 * c.max_vars ∧ ti.toNat ≤ cv3 ∧ rem_t = cv3 - ti.toNat ∧
                  (∀ k < ti.toNat, tmki[k]?.getD 0#32 = 0#32) ∧
                  (FullMem c { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } } ⋆
                    R) mt)
                ?_ ?_
              · rintro Lt rem_t ⟨ti, ⟨⟩⟩ mt hLt ⟨tmki, htli, hti_le, rfl, hinit, hmt⟩
                c0_hsplit
                · have hti_lt : ti.toNat < cv3 := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                  have hti_b : ti.toNat < tmki.length := by omega
                  have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by c0_bound
                  c0_hsteps!
                  exact hLt (cv3 - (ti + 1#64).toNat) (ti + 1#64, ()) _ (by omega)
                    ⟨tmki.set ti.toNat 0#32, by simp [htli], by omega, rfl, fun k hk => by
                       rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hti1 ▸ hk)) with h | h
                       · rw [List.getElem?_set_ne (by omega)]; exact hinit k h
                       · subst h; rw [List.getElem?_set_self hti_b, Option.getD_some], hm⟩
                · have hti_eq : ti.toNat = cv3 := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc
                    change ¬ti.toNat < cv3 at hc; omega
                  rw [hti_eq] at hinit
                  let s3t : FullState :=
                    { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } }
                  have hden3t : FullDenseInv c F0 s3t :=
                    FullM3CongBva.fullDenseInv_with_scratch_keep hden3r
                      { hden3r.lengths.scratch_ok with tarjan_mark_len := htli } rfl rfl
                  have htmk3t : FullDefSweep.TmkZero s3t := fun v hv => hinit v hv
                  c0_hsteps_nogrp
                  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                    (fun b => (b, ())) (fun _ => True)
                    (fun _ base_t _ => by
                      c0_hsteps_nogrp
                      c0_call hBve
                      refine ⟨c, F0, s3t, R, rfl, hden3t, htmk3t, hmt, ?_⟩
                      intro res s4 m4 hden4 _ hfu4 _ hres_u hm4
                      have hfu4' : s4.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                        dsimp only [s3t, s3r] at hfu4
                        have hfu3' : s3.core.fuel.toNat ≤ s0.core.fuel.toNat := hfu3r
                        omega
                      c0_hsteps_nogrp
                      c0_call hReb
                      refine ⟨c, F0, s4, R, rfl, hden4, hm4, ?_⟩
                      intro rr se me hspe hcle hfue _ hue hme
                      let se' : FullState :=
                        { se with scratch :=
                          { se.scratch with
                            search_ticks := s0.scratch.search_ticks
                            fwd_str_cnt := s0.scratch.search_ticks } }
                      have hspe' : FullSparseInv c F0 se' :=
                        FullM3CongBva.fullSparseInv_with_scratch_keep hspe
                          { hspe.lengths.scratch_ok with
                            walk_vals_len := hspe.lengths.scratch_ok.walk_vals_len } rfl rfl
                      have hfue' : se'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                        change se.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
                      c0_hsteps!
                      · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                          (fun _ => hres_u hc) hm
                      · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                          (fun _ => hue hc) hm
                      · exact hQ 20#64 se' _ hspe' hcle hfue' (Or.inr rfl)
                          (fun _ => hspe'.inconsistent_unsat hc) hm
                      · exact hQ 1#64 se' _ hspe' hcle hfue' (Or.inl rfl)
                          (fun h => by cases h) hm)
                    (fun Jb hJb => by c0_hsplit <;> (c0_hsteps!; exact hJb _ trivial))
              · intro Lt hLt; c0_hsteps!
                exact hLt cv3 (0#64, ()) _
                  ⟨s3r.scratch.tarjan_mark, htl3, Nat.zero_le _, by simp,
                   fun _ h => by simp at h, hm⟩)
          (fun Jfb hJfb => by c0_hsplit <;> (c0_hsteps!; exact hJfb _ trivial))
      · have hsp2 : FullSparseInv c F0 s2 := hfail_s hc
        let s2' : FullState :=
          { s2 with scratch := { s2.scratch with fwd_str_cnt := s2.scratch.search_ticks } }
        have hsp2' : FullSparseInv c F0 s2' := FullM3CongBva.fullSparseInv_with_scratch_keep hsp2
          { hsp2.lengths.scratch_ok with walk_vals_len := hsp2.lengths.scratch_ok.walk_vals_len }
          rfl rfl
        have hfu2' : s2'.core.fuel.toNat ≤ s0.core.fuel.toNat := Nat.le_trans hfu2 hfu1
        c0_hsteps!
        · exact hQ 20#64 s2' _ hsp2' hcl2 hfu2' (Or.inr rfl)
            (fun _ => hsp2'.inconsistent_unsat hc) hm
        · exact hQ 1#64 s2' _ hsp2' hcl2 hfu2' (Or.inl rfl) (fun h => by cases h) hm)
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps!; exact hJ1 s0 m0 ⟨hinv0, hcl0, Nat.le_refl _, hm0⟩
      · c0_hsteps_nogrp
        let s0a : FullState :=
          { s0 with scratch := { s0.scratch with eliminations := s0.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c := ⟨hinv0.lengths.core_ok,
          { hinv0.lengths.scratch_ok with walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len }⟩
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun b => (b, ())) (fun _ => True)
          (fun _ arg _ => by
            c0_hsteps_nogrp
            c0_call hLog
            refine m7Log10Q16Spec_of fun qlog _ _ => ?_
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
              (fun b => (b, ())) (fun _ => True)
              (fun _ ec _ => by
                c0_hsteps_nogrp
                c0_call hScale
                refine ⟨c, s0a, R, rfl, hlen0a, hm, fun delta => ?_⟩
                c0_hsteps!
                let s0b : FullState :=
                  { s0a with
                    scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
                have hinv0b : FullSparseInv c F0 s0b :=
                  FullM3CongBva.fullSparseInv_with_scratch_keep hinv0
                    { hinv0.lengths.scratch_ok with
                      walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len } rfl rfl
                exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)
              (fun Jec hJec => by c0_hsplit <;> (c0_hsteps!; exact hJec _ trivial)))
          (fun Jarg hJarg => by c0_hsplit <;> (c0_hsteps!; exact hJarg _ trivial)))

end LeanQbe.T.Examples.Kissat.FullFidelityStep7

end
