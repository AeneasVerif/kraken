/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullReduceLemmas3
import all Kraken.Mem
import all Kraken.Separation

/-!
# Stage-4 (`D-Full`) GC / Sweep `Func.wp` Proofs — Part 4 (Compaction & `full_rewatch_arena`)

Pure arena-compaction, trail-reason uniqueness, and non-root reason-remapping preservation lemmas,
followed by:
9. `full_rewatch_arena` (`Full2.lean:106-147`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full.FullReduceSpecs
open LeanQbe.T.Examples.Kissat.Full.FullReduceHelpers
open scoped FullArenaTactics FullReduceTactics

namespace FullReduceHelpers

theorem fullWitness_reason_unique {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {i1 i2 src : Nat}
    (hi1 : i1 < k.trail_end) (hi2 : i2 < k.trail_end) (hsrc_lt : src < 0x80000000)
    (hr1 : k.rsns[(k.trl[i1]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src)
    (hr2 : k.rsns[(k.trl[i2]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src) :
    i1 = i2 := by
  have hne : BitVec.ofNat 32 src ≠ 0xFFFFFFFF#32 := fun h => by
    have := congrArg BitVec.toNat h; rw [bv32_ofNat_toNat (by omega)] at this; simp at this; omega
  have hlg : (BitVec.ofNat 32 src &&& 0x80000000#32) = 0#32 :=
    (bv32_lt_highbit_iff _).mp (by rw [bv32_ofNat_toNat (by omega)]; exact hsrc_lt)
  have hgo : ∀ a b, a < k.trail_end → b < k.trail_end → a < b →
      k.rsns[(k.trl[a]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src →
      k.rsns[(k.trl[b]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src →
      False := fun a b ha hb hab hra hrb => by
    have hri := hw.reason_inv a ha (by rw [hra]; exact hne)
    rw [hra, ite_eq_right (fun h => h hlg)] at hri
    have hmem := hw.reason_lit_mem b hb (by rw [hrb]; exact hne) (by rw [hrb]; exact hlg)
    rw [hrb] at hmem
    rcases hri.2.2 _ hmem with heq | ⟨m, hm, hmeq, _⟩
    · have := hw.trail_vars_nodup b a hb ha (by rw [heq]); omega
    · have := hw.trail_vars_nodup m b (by omega) hb (by rw [hmeq, fullInv_var_xor1]); omega
  rcases lt_trichotomy i1 i2 with h | rfl | h
  · exact False.elim (hgo i1 i2 hi1 hi2 h hr1 hr2)
  · rfl
  · exact False.elim (hgo i2 i1 hi2 hi1 h hr2 hr1)

theorem compactArena_append_block {c : FullCfg} {F_cur : List (List Nat)} {k k' : FullCoreState}
    {dst new_sz : Nat}
    (ha : FullArenaClausesInv c F_cur { k with arena_len := dst })
    (hno_old : ∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      (fullArenaHdrCore k r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarbCore k r = false)
    (hcv : k'.cur_vars = k.cur_vars) (hge3 : 3 ≤ new_sz)
    (hlen_ar : k.arena.length = c.arena_cap) (hlen_ar' : k'.arena.length = c.arena_cap)
    (hdst_le : dst + 3 + new_sz ≤ c.arena_cap) (hhold : PrefixAgrees dst k.arena k'.arena)
    (hnoshrk : (k'.arena[dst]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnogarb : (k'.arena[dst]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hsz : (k'.arena[dst + 2]?.getD 0#32).toNat = new_sz)
    (hlits_lt : ∀ j < new_sz, (k'.arena[dst + 3 + j]?.getD 0#32).toNat < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((k'.arena.drop (dst + 3)).take new_sz).map BitVec.toNat))) :
    let kn := { k' with arena_len := dst + 3 + new_sz }
    fullArenaClauseRefsCore kn = fullArenaClauseRefsCore { k with arena_len := dst } ++ [dst] ∧
    FullArenaClausesInv c F_cur kn ∧
    (∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      fullArenaClauseSizeCore kn r = fullArenaClauseSizeCore { k with arena_len := dst } r ∧
      fullArenaClauseGarbCore kn r = fullArenaClauseGarbCore { k with arena_len := dst } r ∧
      fullArenaClauseLitsCore kn r = fullArenaClauseLitsCore { k with arena_len := dst } r) ∧
    (∀ r ∈ fullArenaClauseRefsCore kn,
      (fullArenaHdrCore kn r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarbCore kn r = false) := by
  intro kn
  have hnxt_hold := ha.arenaNextOff_extend (arena' := k'.arena) (alen' := dst + 3 + new_sz)
    (by dsimp; omega) (fun i hi => hhold i hi)
  have hrefs : fullArenaClauseRefsCore kn =
      fullArenaClauseRefsCore { k with arena_len := dst } ++ [dst] :=
    fullArenaClauseRefsCore_append (k := { k with arena_len := dst }) (k' := kn) ha hge3 rfl
      (fun i hi => hhold i hi) hnoshrk hsz
  have hold_cl : ∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      fullArenaClauseSizeCore kn r = fullArenaClauseSizeCore { k with arena_len := dst } r ∧
      fullArenaClauseGarbCore kn r = fullArenaClauseGarbCore { k with arena_len := dst } r ∧
      fullArenaClauseLitsCore kn r = fullArenaClauseLitsCore { k with arena_len := dst } r :=
    fun r hr => by
      have hwf := ha.refs_wf r hr; dsimp at hwf
      have hszr : fullArenaClauseSizeCore kn r =
          fullArenaClauseSizeCore { k with arena_len := dst } r := by
        unfold fullArenaClauseSizeCore kn; simp [hhold (r + 2) (by omega)]
      refine ⟨hszr,
        by unfold fullArenaClauseGarbCore fullArenaHdrCore kn; simp [hhold r (by omega)],
        fullArenaClauseLitsCore_eq_of_hold (by dsimp; omega) (by dsimp [kn]; omega) hszr
          fun j hj => hhold (r + 3 + j) (by omega)⟩
  have hno_new : ∀ r ∈ fullArenaClauseRefsCore kn,
      (fullArenaHdrCore kn r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarbCore kn r = false := by
    intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · have hr3 := (ha.refs_wf r hr).1; dsimp at hr3
      have h0 := hhold r (by omega); have ho := hno_old r hr
      exact ⟨by unfold fullArenaHdrCore kn; rw [h0]; exact ho.1,
        by unfold fullArenaClauseGarbCore fullArenaHdrCore kn; rw [h0]; exact ho.2⟩
    · exact ⟨hnoshrk, by unfold fullArenaClauseGarbCore fullArenaHdrCore kn; simp [hnogarb]⟩
  have hnew_lits_lt : ∀ l ∈ fullArenaClauseLitsCore kn dst, l < 2 * kn.cur_vars := by
    intro l hl
    have hbd : dst + 3 + fullArenaClauseSizeCore kn dst ≤ kn.arena.length := by
      rw [show fullArenaClauseSizeCore kn dst = new_sz from hsz]; dsimp [kn]; omega
    obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl
    rw [show fullArenaClauseSizeCore kn dst = new_sz from hsz] at hj
    have hj_lt : dst + 3 + j < k'.arena.length := by omega
    have := hlits_lt j hj
    rw [List.getElem?_eq_getElem hj_lt, Option.getD_some] at this; dsimp [kn]; omega
  have ha' : FullArenaClausesInv c F_cur kn := by
    refine ⟨Or.inr (by dsimp [kn]; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | hr_dst
      · have hwf := ha.refs_wf r hr; dsimp at hwf
        rw [hnxt_hold r hr, (hold_cl r hr).1]
        exact ⟨by dsimp [kn]; omega, hwf.2.1, hwf.2.2.1, by dsimp [kn]; omega, Or.inr (by
          rcases hwf.2.2.2.2 with he | h3 <;> dsimp [kn] <;> omega)⟩
      · subst r
        have hnxt_d : fullArenaNextOff kn.arena kn.arena_len dst = dst + 3 + new_sz := by
          unfold fullArenaNextOff kn
          simp only [show ¬ (dst + 3 > dst + 3 + new_sz) by omega, ↓reduceIte, hsz,
            show ¬ (dst + 3 + new_sz > dst + 3 + new_sz) by omega, hnoshrk, ne_eq,
            not_true_eq_false]
        rw [hnxt_d, show fullArenaClauseSizeCore kn dst = new_sz from hsz]
        exact ⟨by dsimp [kn]; omega, hge3, by omega, by dsimp [kn]; omega, Or.inl (by dsimp [kn])⟩
    · intro r hr hsh; exact absurd (hno_new r hr).1 hsh
    · intro r hr hng l hl; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | hr_dst
      · rw [(hold_cl r hr).2.1] at hng; rw [(hold_cl r hr).2.2] at hl
        have := ha.lits_lt r hr hng l hl; dsimp [kn] at this ⊢; omega
      · subst r; exact hnew_lits_lt l hl
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | hr_dst
      · rw [(hold_cl r hr).2.1] at hng; rw [(hold_cl r hr).2.2]; exact ha.entails r hr hng
      · subst r; unfold fullArenaClauseLitsCore
        rw [show fullArenaClauseSizeCore kn dst = new_sz from hsz]; exact hent
  exact ⟨hrefs, ha', hold_cl, hno_new⟩

theorem fullArenaClausesInv_zero {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState} :
    FullArenaClausesInv c F_cur { k with arena_len := 0 } := by
  have hrefs : fullArenaClauseRefsCore { k with arena_len := 0 } = [] := by
    simp [fullArenaClauseRefsCore, fullArenaScanRefs]
  exact ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
    fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩

theorem fullWitnessInv_arena_len_zero {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hbin : BinOnlyWatchesInv F_cur k)
    (hcl0 : k.cur_level = 0) : FullWitnessInv c F0 F_cur { k with arena_len := 0 } :=
  { hw with
    arena := fullArenaClausesInv_zero
    watches := (hbin.with_core (k' := { k with arena_len := 0 }) rfl rfl rfl rfl).toModeWatchesInv
    reason_inv := fun i hi h =>
      absurd (hw.level0_rsn_none i hi (by have := hw.lvl_le i hi; omega)) h
    reason_lit_mem := fun i hi h =>
      absurd (hw.level0_rsn_none i hi (by have := hw.lvl_le i hi; omega)) h }

theorem fullWitnessInv_append_root {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {ar' : List (BitVec 32)} {dst new_sz : Nat}
    (hw : FullWitnessInv c F0 F_cur { k with arena_len := dst })
    (hbin : BinOnlyWatchesInv F_cur k) (hcl0 : k.cur_level = 0)
    (ha' : FullArenaClausesInv c F_cur
      { { k with arena := ar' } with arena_len := dst + 3 + new_sz }) :
    FullWitnessInv c F0 F_cur { { k with arena := ar' } with arena_len := dst + 3 + new_sz } :=
  { hw with
    arena := ha'
    watches := (hbin.with_core
      (k' := { { k with arena := ar' } with arena_len := dst + 3 + new_sz })
      rfl rfl rfl rfl).toModeWatchesInv
    reason_inv := fun i hi h => absurd (hw.level0_rsn_none i hi (by
      have := hw.lvl_le i hi
      change (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level at this
      change (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0; omega)) h
    reason_lit_mem := fun i hi h => absurd (hw.level0_rsn_none i hi (by
      have := hw.lvl_le i hi
      change (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level at this
      change (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0; omega)) h }

/-- Non-root (`0 < cur_level`) reason-remapping invariant across arena compaction. -/
def SweepReasonMapInv (k0 kL : FullCoreState) (src dst : Nat) : Prop :=
  ∀ idx < k0.trail_end,
    let v := (k0.trl[idx]?.getD 0#32).toNat / 2
    let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32
    let rL := kL.rsns[v]?.getD 0xFFFFFFFF#32
    if r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32 then rL = r0
    else if r0.toNat < src then
      rL.toNat < dst ∧ rL.toNat < 0x80000000 ∧ rL ≠ 0xFFFFFFFF#32 ∧
      (rL &&& 0x80000000#32) = 0#32 ∧
      rL.toNat ∈ fullArenaClauseRefsCore { kL with arena_len := dst } ∧
      fullArenaClauseGarbCore { kL with arena_len := dst } rL.toNat = false ∧
      fullArenaClauseLitsCore { kL with arena_len := dst } rL.toNat =
        fullArenaClauseLitsCore k0 r0.toNat
    else rL = r0

theorem SweepReasonMapInv.init {k0 : FullCoreState} : SweepReasonMapInv k0 k0 0 0 := by
  intro idx _; dsimp only; split; · rfl
  · split; · omega
    · rfl

theorem SweepReasonMapInv.skip {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k0 kL : FullCoreState} {src nsrc dst : Nat}
    (hw0 : FullWitnessInv c F0 F_cur k0) (hsrc_ref : src ∈ fullArenaClauseRefsCore k0)
    (hnsrc : nsrc = fullArenaNextOff k0.arena k0.arena_len src)
    (hskip : fullArenaClauseGarbCore k0 src = true ∨ fullArenaClauseSizeCore k0 src < 3 ∨
      k0.arena_len < src + 3 + fullArenaClauseSizeCore k0 src)
    (hrm : SweepReasonMapInv k0 kL src dst) : SweepReasonMapInv k0 kL nsrc dst := by
  intro idx hidx; have h := hrm idx hidx; dsimp only at h ⊢
  let v := (k0.trl[idx]?.getD 0#32).toNat / 2; let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32
  change (if r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32 then _ else _) at h ⊢
  split at h
  · rename_i hc1; simp only [hc1, ↓reduceIte]; exact h
  · rename_i hc1; simp only [hc1, ↓reduceIte]
    have hne : r0 ≠ 0xFFFFFFFF#32 := fun he => hc1 (Or.inl he)
    have hlg : (r0 &&& 0x80000000#32) = 0#32 :=
      Classical.byContradiction fun h0 => hc1 (Or.inr h0)
    have hri := hw0.reason_inv idx hidx hne; rw [ite_eq_right (fun h0 => h0 hlg)] at hri
    have hwf := hw0.arena.refs_wf r0.toNat hri.1
    split at h
    · have hb := fullArenaNextOff_bounds (ar := k0.arena) (hw0.arena.refs_wf src hsrc_ref).1
      split; · exact h
      · dsimp only [r0, v] at *; omega
    · rename_i hge
      have hne_src : r0.toNat ≠ src := fun heq => by
        rw [heq] at hri hwf; rcases hskip with hg | h3 | hgt
        · rw [hri.2.1] at hg; cases hg
        · have := hwf.2.1; omega
        · have := hwf.2.2.1; have := hwf.2.2.2.1; omega
      have hdisj := fullArenaScanRefs_disjoint hsrc_ref hri.1
        (by change ¬ r0.toNat < src at hge; dsimp only [r0, v] at *; omega)
      split; · dsimp only [r0, v] at *; omega
      · exact h

theorem SweepReasonMapInv.keep_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k0 kL : FullCoreState} {ar' rsns' : List (BitVec 32)} {src nsrc dst new_sz : Nat}
    (hw0 : FullWitnessInv c F0 F_cur k0) (hsrc_ref : src ∈ fullArenaClauseRefsCore k0)
    (hnsrc : nsrc = fullArenaNextOff k0.arena k0.arena_len src)
    (hdst_le_src : dst ≤ src) (hsrc_lt8 : src < 0x80000000)
    (hrm : SweepReasonMapInv k0 kL src dst)
    (happend :
      let kn : FullCoreState :=
        { kL with arena := ar', rsns := rsns', arena_len := dst + 3 + new_sz }
      fullArenaClauseRefsCore kn = fullArenaClauseRefsCore { kL with arena_len := dst } ++ [dst] ∧
      (∀ r ∈ fullArenaClauseRefsCore { kL with arena_len := dst },
        fullArenaClauseGarbCore kn r = fullArenaClauseGarbCore { kL with arena_len := dst } r ∧
        fullArenaClauseLitsCore kn r = fullArenaClauseLitsCore { kL with arena_len := dst } r) ∧
      fullArenaClauseGarbCore kn dst = false ∧
      fullArenaClauseLitsCore kn dst = fullArenaClauseLitsCore k0 src)
    (hrsns_other : ∀ idx < k0.trail_end,
      k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ BitVec.ofNat 32 src →
      rsns'[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        kL.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
    (hrsns_src : ∀ idx < k0.trail_end,
      k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src →
      rsns'[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 dst) :
    SweepReasonMapInv k0 { kL with arena := ar', rsns := rsns' } nsrc (dst + 3 + new_sz) := by
  intro idx hidx; have h := hrm idx hidx; dsimp only at h ⊢
  let v := (k0.trl[idx]?.getD 0#32).toNat / 2; let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32
  have hr_oth : r0 ≠ BitVec.ofNat 32 src →
      rsns'[v]?.getD 0xFFFFFFFF#32 = kL.rsns[v]?.getD 0xFFFFFFFF#32 := hrsns_other idx hidx
  have hr_eq : r0 = BitVec.ofNat 32 src →
      rsns'[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 dst := hrsns_src idx hidx
  change (if r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32 then _ else _) at h ⊢
  split at h
  · rename_i hc1; simp only [hc1, ↓reduceIte]
    have hne_s : r0 ≠ BitVec.ofNat 32 src := fun heq => by
      rcases hc1 with hff | hhi
      · rw [hff] at heq; have := congrArg BitVec.toNat heq
        rw [bv32_ofNat_toNat (by omega)] at this; simp at this; omega
      · rw [heq] at hhi
        exact hhi ((bv32_lt_highbit_iff _).mp
          (by rw [bv32_ofNat_toNat (by omega)]; exact hsrc_lt8))
    rw [hr_oth hne_s]; exact h
  · rename_i hc1; simp only [hc1, ↓reduceIte]
    have hne : r0 ≠ 0xFFFFFFFF#32 := fun he => hc1 (Or.inl he)
    have hlg : (r0 &&& 0x80000000#32) = 0#32 :=
      Classical.byContradiction fun h0 => hc1 (Or.inr h0)
    have hri := hw0.reason_inv idx hidx hne; rw [ite_eq_right (fun h0 => h0 hlg)] at hri
    have hb := fullArenaNextOff_bounds (ar := k0.arena) (hw0.arena.refs_wf src hsrc_ref).1
    split at h
    · split
      · have hne_s : r0 ≠ BitVec.ofNat 32 src := fun heq => by
          have := congrArg BitVec.toNat heq
          rw [bv32_ofNat_toNat (by omega)] at this
          dsimp only [r0, v] at *; omega
        rw [hr_oth hne_s]; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
        obtain ⟨hrefs', hhold', _, _⟩ := happend
        exact ⟨by dsimp only [v] at *; omega, h2, h3, h4,
          by rw [hrefs', List.mem_append]; exact Or.inl h5,
          (hhold' _ h5).1.trans h6, (hhold' _ h5).2.trans h7⟩
      · dsimp only [r0, v] at *; omega
    · rename_i hge
      by_cases hreq : r0.toNat = src
      · have hr_bv : r0 = BitVec.ofNat 32 src :=
          BitVec.eq_of_toNat_eq (by rw [hreq, bv32_ofNat_toNat (by omega)])
        split
        · rw [hr_eq hr_bv]
          have hdst_bv : (BitVec.ofNat 32 dst).toNat = dst := bv32_ofNat_toNat (by omega)
          have hdst_ne : BitVec.ofNat 32 dst ≠ 0xFFFFFFFF#32 := fun he => by
            have := congrArg BitVec.toNat he; rw [hdst_bv] at this; simp at this; omega
          obtain ⟨hrefs', _, hng_d, hlits_d⟩ := happend
          exact ⟨by omega, by omega, hdst_ne,
            (bv32_lt_highbit_iff _).mp (by rw [hdst_bv]; omega),
            by rw [hdst_bv, hrefs', List.mem_append, List.mem_singleton]; exact Or.inr rfl,
            by rw [hdst_bv]; exact hng_d, by rw [hdst_bv, hreq]; exact hlits_d⟩
        · dsimp only [r0, v] at *; omega
      · have hdisj := fullArenaScanRefs_disjoint hsrc_ref hri.1
          (by change ¬ r0.toNat < src at hge; dsimp only [r0, v] at *; omega)
        split; · dsimp only [r0, v] at *; omega
        · have hne_s : r0 ≠ BitVec.ofNat 32 src := fun heq => hreq (by
            have := congrArg BitVec.toNat heq; rwa [bv32_ofNat_toNat (by omega)] at this)
          rw [hr_oth hne_s]; exact h

theorem SweepReasonMapInv.congr_rsns_arena {k0 k1 k2 : FullCoreState} {nsrc ndst : Nat}
    (har : k2.arena = k1.arena) (hrs : k2.rsns = k1.rsns)
    (h : SweepReasonMapInv k0 k1 nsrc ndst) : SweepReasonMapInv k0 k2 nsrc ndst := by
  intro idx hidx; have h1 := h idx hidx; dsimp only at h1 ⊢
  unfold fullArenaClauseRefsCore fullArenaClauseGarbCore fullArenaHdrCore
    fullArenaClauseLitsCore fullArenaClauseSizeCore at h1 ⊢
  dsimp only at h1 ⊢; rw [har, hrs]; exact h1

def CompactPrefixOk (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (k : FullCoreState) (dst : Nat) : Prop :=
  let kCmp : FullCoreState := { k with arena_len := dst }
  FullArenaClausesInv c F_cur kCmp ∧
  (∀ r ∈ fullArenaClauseRefsCore kCmp,
    (fullArenaHdrCore kCmp r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarbCore kCmp r = false) ∧
  (FullArenaVarsNodup s →
    ∀ r ∈ fullArenaClauseRefsCore kCmp, ((fullArenaClauseLitsCore kCmp r).map (· / 2)).Nodup)

def CompactPrefixCongr (k k' : FullCoreState) (dst : Nat) : Prop :=
  fullArenaClauseRefsCore { k' with arena_len := dst } =
    fullArenaClauseRefsCore { k with arena_len := dst } ∧
  (∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
    fullArenaClauseGarbCore { k' with arena_len := dst } r =
      fullArenaClauseGarbCore { k with arena_len := dst } r ∧
    fullArenaClauseLitsCore { k' with arena_len := dst } r =
      fullArenaClauseLitsCore { k with arena_len := dst } r)

theorem arenaPrefix_preserves_compact {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {k k' : FullCoreState} {dst : Nat}
    (hcmp : CompactPrefixOk c F_cur s k dst) (hcv : k'.cur_vars = k.cur_vars)
    (hlen : k.arena.length = c.arena_cap) (hlen' : k'.arena.length = c.arena_cap)
    (hdst_le : dst ≤ c.arena_cap) (hpre : PrefixAgrees dst k.arena k'.arena) :
    CompactPrefixOk c F_cur s k' dst ∧ CompactPrefixCongr k k' dst := by
  obtain ⟨ha, hno, hnd⟩ := hcmp
  have hnxt := ha.arenaNextOff_extend (arena' := k'.arena) (alen' := dst) (Nat.le_refl _)
    (fun i hi => hpre i hi)
  have hrefs : fullArenaClauseRefsCore { k' with arena_len := dst } =
      fullArenaClauseRefsCore { k with arena_len := dst } := fullArenaClauseRefsCore_congr rfl hnxt
  have hcl : ∀ r ∈ fullArenaClauseRefsCore { k with arena_len := dst },
      fullArenaHdrCore { k' with arena_len := dst } r =
        fullArenaHdrCore { k with arena_len := dst } r ∧
      fullArenaClauseSizeCore { k' with arena_len := dst } r =
        fullArenaClauseSizeCore { k with arena_len := dst } r ∧
      fullArenaClauseGarbCore { k' with arena_len := dst } r =
        fullArenaClauseGarbCore { k with arena_len := dst } r ∧
      fullArenaClauseLitsCore { k' with arena_len := dst } r =
        fullArenaClauseLitsCore { k with arena_len := dst } r := fun r hr => by
    have hwf := ha.refs_wf r hr; dsimp at hwf
    have h0 := hpre r (by omega); have h2 := hpre (r + 2) (by omega)
    have hsz : fullArenaClauseSizeCore { k' with arena_len := dst } r =
        fullArenaClauseSizeCore { k with arena_len := dst } r := by
      unfold fullArenaClauseSizeCore; dsimp; rw [h2]
    refine ⟨by unfold fullArenaHdrCore; dsimp; rw [h0], hsz,
      by unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp; rw [h0],
      fullArenaClauseLitsCore_eq_of_hold (by dsimp; have := hwf.2.2.1; have := hwf.2.2.2.1; omega)
        (by dsimp; have := hwf.2.2.1; have := hwf.2.2.2.1; omega) hsz
        fun j hj => hpre (r + 3 + j) (by have := hwf.2.2.1; have := hwf.2.2.2.1; omega)⟩
  refine ⟨⟨⟨ha.len_ok, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩,
    hrefs, fun r hr => ⟨(hcl r hr).2.2.1, (hcl r hr).2.2.2⟩⟩
  · intro r hr; rw [hrefs] at hr; have h := ha.refs_wf r hr
    dsimp at hnxt h ⊢; rw [hnxt r hr, (hcl r hr).2.1]; exact h
  · intro r hr hsh; rw [hrefs] at hr; rw [(hcl r hr).1] at hsh; exact absurd (hno r hr).1 hsh
  · intro r hr hng l hl; rw [hrefs] at hr
    rw [(hcl r hr).2.2.1] at hng; rw [(hcl r hr).2.2.2] at hl
    have := ha.lits_lt r hr hng l hl; dsimp at this ⊢; omega
  · intro r hr hng; rw [hrefs] at hr
    rw [(hcl r hr).2.2.1] at hng; rw [(hcl r hr).2.2.2]; exact ha.entails r hr hng
  · intro r hr; rw [hrefs] at hr
    exact ⟨(hcl r hr).1.symm ▸ (hno r hr).1, (hcl r hr).2.2.1.trans (hno r hr).2⟩
  · intro hnd_s r hr; rw [hrefs] at hr; rw [(hcl r hr).2.2.2]; exact hnd hnd_s r hr

theorem CompactPrefixOk.with_rsns {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {k : FullCoreState} {arH rsnsR : List (BitVec 32)} {dst : Nat}
    (h : CompactPrefixOk c F_cur s { k with arena := arH } dst) :
    CompactPrefixOk c F_cur s { k with arena := arH, rsns := rsnsR } dst := by
  let k1 : FullCoreState := { k with arena := arH, arena_len := dst }
  let k2 : FullCoreState := { k with arena := arH, rsns := rsnsR, arena_len := dst }
  have hrefs : fullArenaClauseRefsCore k2 = fullArenaClauseRefsCore k1 :=
    fullArenaClauseRefsCore_congr rfl (fun _ _ => rfl)
  obtain ⟨ha, hno, hnd⟩ := h
  refine ⟨⟨ha.len_ok, ?_, ?_, ?_, ?_⟩, fun r hr => hno r (hrefs ▸ hr),
    fun hs r hr => hnd hs r (hrefs ▸ hr)⟩
  · intro r hr; rw [hrefs] at hr; exact ha.refs_wf r hr
  · intro r hr hsh; rw [hrefs] at hr; exact ha.shrk_term r hr hsh
  · intro r hr hng l hl; rw [hrefs] at hr; exact ha.lits_lt r hr hng l hl
  · intro r hr hng; rw [hrefs] at hr; exact ha.entails r hr hng

theorem SweepReasonMapInv.toFullWitnessInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k0 kL : FullCoreState} {dst : Nat}
    (hw0 : FullWitnessInv c F0 F_cur k0)
    (ha' : FullArenaClausesInv c F_cur { kL with arena_len := dst })
    (hbin : BinOnlyWatchesInv F_cur kL)
    (hvals : kL.vals = k0.vals) (hlvl : kL.lvl = k0.lvl) (htrl : kL.trl = k0.trl)
    (htp : kL.trail_pos = k0.trail_pos) (hte : kL.trail_end = k0.trail_end)
    (hcl : kL.cur_level = k0.cur_level) (hcv : kL.cur_vars = k0.cur_vars)
    (hft : kL.frame_trail = k0.frame_trail) (hfd : kL.frame_dec = k0.frame_dec)
    (hinc : kL.inconsistent = k0.inconsistent) (hrm : SweepReasonMapInv k0 kL k0.arena_len dst) :
    FullWitnessInv c F0 F_cur { kL with arena_len := dst } := by
  let kn : FullCoreState := { kL with arena_len := dst }
  have hrm_get : ∀ idx < k0.trail_end,
      let v := (k0.trl[idx]?.getD 0#32).toNat / 2
      let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32; let rL := kL.rsns[v]?.getD 0xFFFFFFFF#32
      (r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32 → rL = r0) ∧
      (r0 ≠ 0xFFFFFFFF#32 → (r0 &&& 0x80000000#32) = 0#32 →
        rL.toNat < dst ∧ rL.toNat < 0x80000000 ∧ rL ≠ 0xFFFFFFFF#32 ∧
        (rL &&& 0x80000000#32) = 0#32 ∧ rL.toNat ∈ fullArenaClauseRefsCore kn ∧
        fullArenaClauseGarbCore kn rL.toNat = false ∧
        fullArenaClauseLitsCore kn rL.toNat = fullArenaClauseLitsCore k0 r0.toNat) := by
    intro idx hidx; have h := hrm idx hidx; dsimp only at h ⊢; constructor
    · intro hc1; split at h
      · exact h
      · exact absurd hc1 ‹_›
    · intro hne hlg
      have hc1 : ¬ (k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          0xFFFFFFFF#32 ∨ (k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
            0x80000000#32) ≠ 0#32) := fun hc => hc.elim hne (fun h0 => h0 hlg)
      split at h
      · exact absurd ‹_› hc1
      · have hri := hw0.reason_inv idx hidx hne; rw [ite_eq_right (fun h0 => h0 hlg)] at hri
        have hlt : (k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat <
            k0.arena_len := by have := (hw0.arena.refs_wf _ hri.1).1; omega
        split at h
        · exact h
        · exact absurd hlt ‹_›
  refine {
    ext_sound := by dsimp [kn]; rw [hcv]; exact hw0.ext_sound
    inconsistent_sound := by dsimp [kn]; rw [hinc]; exact hw0.inconsistent_sound
    arena := ha'
    watches := (hbin.with_core (k' := kn) rfl rfl rfl rfl).toModeWatchesInv
    cur_level_le := by dsimp [kn]; rw [hcl, hte]; exact hw0.cur_level_le
    trail_lits_lt := fun i hi => by
      dsimp [kn] at hi ⊢; rw [htrl, hcv]; exact hw0.trail_lits_lt i (hte ▸ hi)
    trail_vars_nodup := fun i j hi hj hveq => by
      dsimp [kn] at hi hj hveq; rw [htrl] at hveq
      exact hw0.trail_vars_nodup i j (hte ▸ hi) (hte ▸ hj) hveq
    vals_domain := fun l hl => by
      dsimp [kn] at hl ⊢; rw [hvals]; exact hw0.vals_domain l (hcv ▸ hl)
    vals_true_iff := fun l hl => by
      dsimp [kn] at hl ⊢; rw [hvals, hte, htrl]; exact hw0.vals_true_iff l (hcv ▸ hl)
    vals_false_iff := fun l hl => by
      dsimp [kn] at hl ⊢; rw [hvals, hte, htrl]; exact hw0.vals_false_iff l (hcv ▸ hl)
    lvl_le := fun i hi => by
      dsimp [kn] at hi ⊢; rw [hlvl, htrl, hcl]; exact hw0.lvl_le i (hte ▸ hi)
    dec_earliest := fun i j hi hj hlt hdec => by
      dsimp [kn] at hi hj hlt hdec ⊢; rw [hlvl, htrl] at hlt hdec
      have hr0_ff :
          k0.rsns[(k0.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
        obtain ⟨h1, h2⟩ := hrm_get j (hte ▸ hj)
        by_cases hc1 : k0.rsns[(k0.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
            0xFFFFFFFF#32 ∨
            (k0.rsns[(k0.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠
              0#32
        · exact (h1 hc1).symm.trans hdec.2
        · exact absurd hdec.2 (h2 (fun h => hc1 (Or.inl h))
            (Classical.byContradiction fun h0 => hc1 (Or.inr h0))).2.2.1
      exact hw0.dec_earliest i j (hte ▸ hi) (hte ▸ hj) hlt ⟨hdec.1, hr0_ff⟩
    levels_inhabited := fun L h1 h2 => by
      dsimp [kn] at h2 ⊢; rw [hte, hlvl, htrl]; exact hw0.levels_inhabited L h1 (hcl ▸ h2)
    level0_sound := fun i hi h0 => by
      dsimp [kn] at hi h0 ⊢; rw [hlvl, htrl] at h0; rw [htrl]
      exact hw0.level0_sound i (hte ▸ hi) h0
    trail_pos_inv := fun i hi => by
      dsimp [kn] at hi ⊢; rw [htp, htrl]; exact hw0.trail_pos_inv i (hte ▸ hi)
    level0_rsn_none := fun idx hidx h0 => by
      dsimp [kn] at hidx h0 ⊢; rw [hlvl, htrl] at h0; rw [htrl]
      have hr0 := hw0.level0_rsn_none idx (hte ▸ hidx) h0
      exact (hrm_get idx (hte ▸ hidx)).1 (Or.inl hr0) |>.trans hr0
    frame_trail_lt := fun L hL => by
      dsimp [kn] at hL ⊢; rw [hft, hte]; exact hw0.frame_trail_lt L (hcl ▸ hL)
    frame_trail_mono := fun L1 L2 h1 h2 => by
      dsimp [kn] at h2 ⊢; rw [hft]; exact hw0.frame_trail_mono L1 L2 h1 (hcl ▸ h2)
    frame_trail_before_lt := fun L h1 h2 i hi => by
      dsimp [kn] at h2 hi ⊢; rw [hft] at hi; rw [hlvl, htrl]
      exact hw0.frame_trail_before_lt L h1 (hcl ▸ h2) i hi
    frame_dec_lt := fun L h1 h2 => by
      dsimp [kn] at h2 ⊢; rw [hfd, hcv]; exact hw0.frame_dec_lt L h1 (hcl ▸ h2)
    reason_inv := fun idx hidx hne => by
      dsimp only [kn] at hidx hne ⊢; rw [htrl] at hne ⊢
      have hidx0 : idx < k0.trail_end := hte ▸ hidx; obtain ⟨h1, h2⟩ := hrm_get idx hidx0
      let v := (k0.trl[idx]?.getD 0#32).toNat / 2; let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32
      by_cases hc1 : r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32
      · have hreq : kL.rsns[v]?.getD 0xFFFFFFFF#32 = r0 := h1 hc1
        change kL.rsns[v]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 at hne; rw [hreq] at hne
        have hri := hw0.reason_inv idx hidx0 hne
        rcases hc1 with hff | hhi
        · exact absurd hff hne
        · rw [ite_eq_left hhi] at hri
          change if (kL.rsns[v]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then _ else _
          rw [hreq, ite_eq_left hhi, hcv, hlvl]; exact hri
      · have hne0 : r0 ≠ 0xFFFFFFFF#32 := fun h => hc1 (Or.inl h)
        have hlg0 : (r0 &&& 0x80000000#32) = 0#32 :=
          Classical.byContradiction fun h0 => hc1 (Or.inr h0)
        obtain ⟨_, _, _, hlgL, hrefL, hngL, hlitsL⟩ := h2 hne0 hlg0
        have hri := hw0.reason_inv idx hidx0 hne0
        rw [ite_eq_right (fun h0 => h0 hlg0)] at hri; rw [ite_eq_right (fun h0 => h0 hlgL)]
        refine ⟨hrefL, hngL, fun q hq => ?_⟩
        change q ∈ fullArenaClauseLitsCore kn _ at hq; rw [hlitsL] at hq
        rw [hlvl]; exact hri.2.2 q hq
    reason_lit_mem := fun idx hidx hne hlgL => by
      dsimp only [kn] at hidx hne hlgL ⊢; rw [htrl] at hne hlgL ⊢
      have hidx0 : idx < k0.trail_end := hte ▸ hidx; obtain ⟨h1, h2⟩ := hrm_get idx hidx0
      let v := (k0.trl[idx]?.getD 0#32).toNat / 2; let r0 := k0.rsns[v]?.getD 0xFFFFFFFF#32
      by_cases hc1 : r0 = 0xFFFFFFFF#32 ∨ (r0 &&& 0x80000000#32) ≠ 0#32
      · have hreq : kL.rsns[v]?.getD 0xFFFFFFFF#32 = r0 := h1 hc1
        change kL.rsns[v]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 at hne
        change (kL.rsns[v]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 at hlgL
        rw [hreq] at hne hlgL; rcases hc1 with hff | hhi
        · exact absurd hff hne
        · exact absurd hlgL hhi
      · have hne0 : r0 ≠ 0xFFFFFFFF#32 := fun h => hc1 (Or.inl h)
        have hlg0 : (r0 &&& 0x80000000#32) = 0#32 :=
          Classical.byContradiction fun h0 => hc1 (Or.inr h0)
        obtain ⟨_, _, _, _, _, _, hlitsL⟩ := h2 hne0 hlg0
        change (k0.trl[idx]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore kn _
        rw [hlitsL]; exact hw0.reason_lit_mem idx hidx0 hne0 hlg0 }

theorem fullLastLearnedWf_of_all_sentinel {s : FullState}
    (hall : ∀ i < 16, s.scratch.last_learned[i]? = some 0xFFFFFFFF#32) : FullLastLearnedWf s :=
  fun i hi => Or.inl (by rw [hall i (by omega), Option.getD_some])

theorem sweep_copy_new_props {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s0 sL sC : FullState} {src dst st : BitVec 64} {old_sz : BitVec 32} {at_root : Bool}
    (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hbinL : BinOnlyWatchesInv F_cur sL.core)
    (hout : fullSweepCopyOutcome c F0 F_cur sL sC src dst old_sz at_root st)
    (hdec : ∀ b : Bool, at_root = b ↔ (if b then s.core.cur_level = 0 else 0 < s.core.cur_level))
    (hcvL : sL.core.cur_vars = s.core.cur_vars)
    (hcvC : sC.core.cur_vars = sL.core.cur_vars)
    (hsz3 : 3 ≤ old_sz.toNat) (harL_len : sL.core.arena.length = c.arena_cap)
    (harC_len : sC.core.arena.length = c.arena_cap)
    (hsrc_fit : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap)
    (hdst_src : dst.toNat ≤ src.toNat)
    (hsrc_ref : src.toNat ∈ fullArenaClauseRefs s0)
    (hng_src : fullArenaClauseGarbCore s0.core src.toNat = false)
    (hsrc_lits : ((sL.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat =
      fullArenaClauseLitsCore s0.core src.toNat)
    (hlits_lt : ∀ j < old_sz.toNat,
      (sL.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hne_e : st ≠ 0xFFFFFFFE#64) (hne_d : st ≠ 0xFFFFFFFD#64)
    (hne_1 : st ≠ 1#64) (hne_f : st ≠ 0xFFFFFFFF#64) :
    3 ≤ st.toNat ∧ st.toNat ≤ old_sz.toNat ∧
    (∀ j < st.toNat, (sC.core.arena[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    List.Sublist (((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat)
      (fullArenaClauseLitsCore s0.core src.toNat) ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat)) ∧
    BinOnlyWatchesInv F_cur sC.core := by
  by_cases hcl0 : s.core.cur_level = 0
  · obtain ⟨_, hbinC, _, hcases, _, _, _, _, hge3⟩ := hout.2 ((hdec true).mpr hcl0)
    have hrange : 3 ≤ st.toNat ∧ st.toNat ≤ old_sz.toNat := by
      rcases hcases with h | h | h | h | h
      · exact absurd h hne_e
      · exact absurd h hne_d
      · exact absurd h hne_1
      · exact absurd h hne_f
      · exact h
    obtain ⟨hl, hs, he⟩ := hge3 hrange
    exact ⟨hrange.1, hrange.2, fun j hj => hcvL ▸ hl j hj, by rwa [hsrc_lits] at hs, he, hbinC⟩
  · obtain ⟨hst_eq, _, _, _, _, _, _, _, _, _, hwv, hws, hwl, _, _, _, _, _, hcp⟩ :=
      hout.1 ((hdec false).mpr (Nat.pos_of_ne_zero hcl0))
    have hst_nat : st.toNat = old_sz.toNat := by rw [hst_eq, zext_toNat _ (by decide)]
    have hcopy_eq : ((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat =
        fullArenaClauseLitsCore s0.core src.toNat := by
      rw [← hsrc_lits, hst_nat]; congr 1
      apply List.ext_getElem (by simp [harL_len, harC_len]; omega)
      intro j hj1 _; have hj : j < old_sz.toNat := by simp [harC_len] at hj1; omega
      simp only [List.getElem_take, List.getElem_drop]
      have h1 := hcp j hj
      rw [List.getElem?_eq_getElem (by omega : dst.toNat + 3 + j < sC.core.arena.length),
        List.getElem?_eq_getElem (by omega : src.toNat + 3 + j < sL.core.arena.length)] at h1
      exact Option.some.inj h1
    exact ⟨by omega, by omega,
      fun j hj => by rw [hcp j (by omega)]; exact hlits_lt j (by omega),
      by rw [hcopy_eq]; exact List.Sublist.refl _,
      by rw [hcopy_eq]; exact hw0.arena.entails src.toNat hsrc_ref hng_src,
      hbinL.with_core hcvC hwv hws hwl⟩

theorem sweep_pos_lits_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sL sC : FullState} {arH : List (BitVec 32)} {src dst st : BitVec 64}
    {old_sz : BitVec 32} {at_root : Bool}
    (hout : fullSweepCopyOutcome c F0 F_cur sL sC src dst old_sz at_root st)
    (hdec : at_root = false)
    (harL_len : sL.core.arena.length = c.arena_cap)
    (harC_len : sC.core.arena.length = c.arena_cap)
    (hsrc_fit : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap)
    (hdst_src : dst.toNat ≤ src.toNat)
    (hsrc_lits : ((sL.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat =
      fullArenaClauseLitsCore s0.core src.toNat)
    (hszH : (arH[dst.toNat + 2]?.getD 0#32).toNat = st.toNat)
    (hdropH : ((arH.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat =
      ((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat) :
    st.toNat = old_sz.toNat ∧
    sC.core.vals = sL.core.vals ∧ sC.core.lvl = sL.core.lvl ∧ sC.core.rsns = sL.core.rsns ∧
    sC.core.trl = sL.core.trl ∧ sC.core.trail_pos = sL.core.trail_pos ∧
    sC.core.trail_end = sL.core.trail_end ∧
    fullArenaClauseLitsCore { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat }
      dst.toNat = fullArenaClauseLitsCore s0.core src.toNat := by
  obtain ⟨hst_eq, hvC, _, hlC, hrC, htC, htpC, hteC, _, _, _, _, _, _, _, _, _, _, hcp⟩ :=
    hout.1 hdec
  have hst_n : st.toNat = old_sz.toNat := by rw [hst_eq, zext_toNat _ (by decide)]
  refine ⟨hst_n, hvC, hlC, hrC, htC, htpC, hteC, ?_⟩
  rw [show fullArenaClauseLitsCore
        { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat } dst.toNat =
        ((arH.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat by
      unfold fullArenaClauseLitsCore
      rw [show fullArenaClauseSizeCore
          { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat } dst.toNat =
          st.toNat from hszH],
    hdropH, ← hsrc_lits, hst_n]
  congr 1; apply List.ext_getElem (by simp [harL_len, harC_len]; omega)
  intro j hj1 _; have hj : j < old_sz.toNat := by simp [harC_len] at hj1; omega
  simp only [List.getElem_take, List.getElem_drop]
  have h1 := hcp j hj
  rw [List.getElem?_eq_getElem (by omega : dst.toNat + 3 + j < sC.core.arena.length),
    List.getElem?_eq_getElem (by omega : src.toNat + 3 + j < sL.core.arena.length)] at h1
  exact Option.some.inj h1

theorem sweep_rsn_hit_false_at_root {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sC : FullState} {litI : BitVec 32} {src dst : Nat}
    (hwC : FullWitnessInv c F0 F_cur { sC.core with arena_len := dst })
    (hcl0 : sC.core.cur_level = 0) (hlitI_lt : litI.toNat < 2 * sC.core.cur_vars)
    (hlitI_v : litI.toNat < sC.core.vals.length) (_hrsns_len : sC.core.rsns.length = c.max_vars)
    (_hcv_le : sC.core.cur_vars ≤ c.max_vars) (_hsrc_lt8 : src < 0x80000000)
    (hval_gt0 : (0#32).slt ((sC.core.vals[litI.toNat]'hlitI_v).signExtend 32) = true)
    (hrsn_eq : (sC.core.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32).toNat = src) : False := by
  have hv1 : sC.core.vals[litI.toNat]?.getD 0#8 = 1#8 := by
    have hdom := hwC.vals_domain litI.toNat hlitI_lt
    have hg : sC.core.vals[litI.toNat]?.getD 0#8 = sC.core.vals[litI.toNat]'hlitI_v := by
      rw [List.getElem?_eq_getElem hlitI_v, Option.getD_some]
    rw [hg] at hdom ⊢; exact (bv8_gt0_of_dom hdom).1.mp hval_gt0
  obtain ⟨idx, hidx, hieq⟩ := (hwC.vals_true_iff litI.toNat hlitI_lt).mp hv1
  have hr_ff := hwC.level0_rsn_none idx hidx
    (by have hlv := hwC.lvl_le idx hidx; change _ ≤ sC.core.cur_level at hlv; omega)
  rw [hieq] at hr_ff; rw [hr_ff] at hrsn_eq; simp at hrsn_eq; omega

end FullReduceHelpers

/-! ## 9. `full_rewatch_arena_wp` (`Full2.lean:106-147`) -/

private theorem rewatch_body_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {p sz : Nat} {ar0 ar1 : List (BitVec 32)}
    (hlenL : sL.LengthsOk c) (hp_ref0 : p ∈ fullArenaClauseRefs s) (har0 : ar0.length = c.arena_cap)
    (hw0 : FullWitnessInv c F0 F_cur { sL.core with arena := ar0 })
    (hrefs0 : fullArenaClauseRefs { sL with core := { sL.core with arena := ar0 } } =
      fullArenaClauseRefs s)
    (hno0 : ∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr { sL with core := { sL.core with arena := ar0 } } r &&& 0x00800000#32) = 0#32 ∧
      fullArenaClauseGarb { sL with core := { sL.core with arena := ar0 } } r = false)
    (hsz0 : fullArenaClauseSize { sL with core := { sL.core with arena := ar0 } } p = sz)
    (hnd0 : FullArenaVarsNodup s →
      FullArenaVarsNodup { sL with core := { sL.core with arena := ar0 } })
    (har1 : ar1.length = c.arena_cap)
    (hout : OutsideSliceAgrees (p + 1) (p + 3 + sz) ar0 ar1) (h2eq : ar1[p + 2]? = ar0[p + 2]?)
    (hperm : List.Perm (fullArenaClauseLitsCore { sL.core with arena := ar1 } p)
      (fullArenaClauseLitsCore { sL.core with arena := ar0 } p)) :
    let s1 : FullState := { sL with core := { sL.core with arena := ar1 } }
    ar1.length = c.arena_cap ∧ s1.LengthsOk c ∧ FullWitnessInv c F0 F_cur s1.core ∧
    fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧ p ∈ fullArenaClauseRefsCore s1.core ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr s1 r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb s1 r = false) ∧
    fullArenaClauseSize s1 p = sz ∧ (FullArenaVarsNodup s → FullArenaVarsNodup s1) := by
  intro s1
  let s0 : FullState := { sL with core := { sL.core with arena := ar0 } }
  have hlen0 : s0.core.LengthsOk c := { hlenL.core_ok with arena_len_arr := har0 }
  have href0 : p ∈ fullArenaClauseRefsCore s0.core := by
    change p ∈ fullArenaClauseRefs s0; rw [hrefs0]; exact hp_ref0
  have hsz1 : fullArenaClauseSizeCore s1.core p = fullArenaClauseSizeCore s0.core p := by
    unfold fullArenaClauseSizeCore s1 s0; exact congrArg (fun o => (o.getD 0#32).toNat) h2eq
  obtain ⟨hrefs1, hmeta1, hlits_oth1, hw1⟩ := modifyClauseBody_preserves_witness hlen0 hw0 href0
    (ar' := ar1) har1 (by rw [show fullArenaClauseSizeCore s0.core p = sz from hsz0]; exact hout)
    h2eq (fun l => hperm.mem_iff)
  refine ⟨har1, ⟨{ hlenL.core_ok with arena_len_arr := har1 }, hlenL.scratch_ok⟩, hw1,
    hrefs1.trans hrefs0, by rw [hrefs1]; exact href0,
    fun r hr => ?_, hsz1.trans hsz0, fun hnd => ?_⟩
  · have hr0 : r ∈ fullArenaClauseRefsCore s0.core := by
      change r ∈ fullArenaClauseRefs s0; rw [hrefs0]; exact hr
    have hm := hmeta1 r hr0; have ho := hno0 r hr
    exact ⟨by change (fullArenaHdrCore s1.core r &&& 0x00800000#32) = 0#32; rw [hm.1]; exact ho.1,
      by change fullArenaClauseGarbCore s1.core r = false; rw [hm.2.2]; exact ho.2⟩
  · intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefsCore s0.core := by
      change r ∈ fullArenaClauseRefsCore s1.core at hr; rw [hrefs1] at hr; exact hr
    by_cases hrp : r = p
    · subst r; exact (hperm.map (· / 2)).nodup_iff.mpr (hnd0 hnd p href0 (hno0 p hp_ref0).2)
    · change ((fullArenaClauseLitsCore s1.core r).map (· / 2)).Nodup; rw [hlits_oth1 r hr0 hrp]
      exact hnd0 hnd r hr0 (by change fullArenaClauseGarbCore s0.core r = false
                               rw [← (hmeta1 r hr0).2.2]; exact hng)

private theorem rewatch_swap_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {p sz a b : Nat} {ar0 : List (BitVec 32)}
    (hlenL : sL.LengthsOk c) (hp_ref0 : p ∈ fullArenaClauseRefs s)
    (hsz_fit : p + 3 + sz ≤ s.core.arena_len) (hal_le : s.core.arena_len ≤ c.arena_cap)
    (har0 : ar0.length = c.arena_cap)
    (hw0 : FullWitnessInv c F0 F_cur { sL.core with arena := ar0 })
    (hrefs0 : fullArenaClauseRefs { sL with core := { sL.core with arena := ar0 } } =
      fullArenaClauseRefs s)
    (hno0 : ∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr { sL with core := { sL.core with arena := ar0 } } r &&& 0x00800000#32) = 0#32 ∧
      fullArenaClauseGarb { sL with core := { sL.core with arena := ar0 } } r = false)
    (hsz0 : fullArenaClauseSize { sL with core := { sL.core with arena := ar0 } } p = sz)
    (hnd0 : FullArenaVarsNodup s →
      FullArenaVarsNodup { sL with core := { sL.core with arena := ar0 } })
    (ha : a < sz) (hb : b < sz) :
    let pa := p + 3 + a; let pb := p + 3 + b
    let ar1 := (ar0.set pa (ar0[pb]'(by omega))).set pb (ar0[pa]'(by omega))
    let s1 : FullState := { sL with core := { sL.core with arena := ar1 } }
    ar1.length = c.arena_cap ∧ FullWitnessInv c F0 F_cur s1.core ∧
    fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr s1 r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb s1 r = false) ∧
    fullArenaClauseSize s1 p = sz ∧ (FullArenaVarsNodup s → FullArenaVarsNodup s1) := by
  intro pa pb ar1 s1
  have h2eq : ar1[p + 2]? = ar0[p + 2]? := by
    dsimp only [ar1, pa, pb]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hsz1 : fullArenaClauseSizeCore s1.core p = sz := by
    unfold fullArenaClauseSizeCore s1; rw [h2eq]; exact hsz0
  have hperm : List.Perm (fullArenaClauseLitsCore s1.core p)
      (fullArenaClauseLitsCore { sL.core with arena := ar0 } p) := by
    unfold fullArenaClauseLitsCore; rw [hsz1, show fullArenaClauseSizeCore _ p = sz from hsz0]
    exact swapClauseLits_perm ha hb (by omega)
  obtain ⟨h1, _, h3, h4, _, h6, h7, h8⟩ := rewatch_body_step hlenL hp_ref0 har0 hw0 hrefs0 hno0 hsz0
    hnd0 (ar1 := ar1) (by simp [ar1, har0])
    (fun idx hidx => by
      dsimp only [ar1, pa, pb]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
    h2eq hperm
  exact ⟨h1, h3, h4, h6, h7, h8⟩

private theorem rewatch_lit_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {p sz : Nat} (hsz_fit : p + 3 + sz ≤ k.arena.length)
    (hw : FullWitnessInv c F0 F_cur k) (href : p ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k p = false) (hsz : fullArenaClauseSizeCore k p = sz)
    {j : Nat} (hj : j < sz) : (k.arena[p + 3 + j]?.getD 0#32).toNat < 2 * k.cur_vars := by
  have hbd : p + 3 + fullArenaClauseSizeCore k p ≤ k.arena.length := by rw [hsz]; omega
  have hmem := (mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨j, by rw [hsz]; exact hj, rfl⟩
  have hlt := hw.arena.lits_lt p href hng _ hmem
  rwa [List.getElem?_eq_getElem (by omega : p + 3 + j < k.arena.length), Option.getD_some]

private theorem rewatch_set_saved_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {p : BitVec 64} {sz : Nat} {arA : List (BitVec 32)}
    (hlenL : sL.LengthsOk c) (hp_ref0 : p.toNat ∈ fullArenaClauseRefs s)
    (hsz_fit : p.toNat + 3 + sz ≤ s.core.arena_len) (hal_le : s.core.arena_len ≤ c.arena_cap)
    (harA : arA.length = c.arena_cap)
    (hwA : FullWitnessInv c F0 F_cur { sL.core with arena := arA })
    (hrefsA : fullArenaClauseRefs { sL with core := { sL.core with arena := arA } } =
      fullArenaClauseRefs s)
    (hnoA : ∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr { sL with core := { sL.core with arena := arA } } r &&& 0x00800000#32) = 0#32 ∧
      fullArenaClauseGarb { sL with core := { sL.core with arena := arA } } r = false)
    (hszA : fullArenaClauseSize { sL with core := { sL.core with arena := arA } } p.toNat = sz)
    (hndA : FullArenaVarsNodup s →
      FullArenaVarsNodup { sL with core := { sL.core with arena := arA } })
    (hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1) :
    let arB := arA.set (p + (1 : BitVec 64)).toNat 2#32
    let sB : FullState := { sL with core := { sL.core with arena := arB } }
    arB.length = c.arena_cap ∧ sB.LengthsOk c ∧ FullWitnessInv c F0 F_cur sB.core ∧
    fullArenaClauseRefs sB = fullArenaClauseRefs s ∧ p.toNat ∈ fullArenaClauseRefsCore sB.core ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr sB r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb sB r = false) ∧
    (FullArenaVarsNodup s → FullArenaVarsNodup sB) := by
  intro arB sB
  have h2eq : arB[p.toNat + 2]? = arA[p.toNat + 2]? := List.getElem?_set_ne (by omega)
  have hszA' : fullArenaClauseSizeCore { sL.core with arena := arA } p.toNat = sz := hszA
  have hszB : fullArenaClauseSizeCore sB.core p.toNat = sz := by
    unfold fullArenaClauseSizeCore sB; rw [h2eq]; exact hszA'
  have hlitsB : fullArenaClauseLitsCore sB.core p.toNat =
      fullArenaClauseLitsCore { sL.core with arena := arA } p.toNat :=
    fullArenaClauseLitsCore_eq_of_hold
      (by rw [hszA']; change p.toNat + 3 + sz ≤ arA.length; omega)
      (by rw [hszA']; change p.toNat + 3 + sz ≤ arB.length
          have harB' : arB.length = c.arena_cap := by simp [arB, harA]
          omega)
      (hszB.trans hszA'.symm) (fun j _ => List.getElem?_set_ne (by omega))
  obtain ⟨h1, h2, h3, h4, h5, h6, _, h8⟩ := rewatch_body_step hlenL hp_ref0 harA hwA hrefsA hnoA
    hszA hndA (ar1 := arB) (by simp [arB, harA])
    (fun idx hidx => List.getElem?_set_ne (by omega)) h2eq (hlitsB ▸ List.Perm.refl _)
  exact ⟨h1, h2, h3, h4, h5, h6, h8⟩

private theorem list_swap_eq_of_idx {α : Type} {xs : List α} {i j i' j' : Nat}
    (hi : i = i') (hj : j = j') (hi_lt : i < xs.length) (hj_lt : j < xs.length)
    (hi'_lt : i' < xs.length) (hj'_lt : j' < xs.length) :
    (xs.set i (xs[j]'hj_lt)).set j (xs[i]'hi_lt) =
    (xs.set i' (xs[j']'hj'_lt)).set j' (xs[i']'hi'_lt) := by
  subst hi hj; rfl

private theorem rewatch_push_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit w0 w1 : BitVec 32} {ok : Bool} {wvec' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' : BitVec 64}
    (hw : FullWitnessInv c F0 F_cur k) (hdm : k.dense_mode = 0#64)
    (hlay' : WatchStackLayout { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                       wusable := wu' })
    (hw0 : (w0 &&& 0x80000000#32) = 0#32) (hw1_lt : w1.toNat < 0x80000000)
    (href : w1.toNat ∈ fullArenaClauseRefsCore k)
    (hoth : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } l =
        fullWatchSizeCore k l ∧
      ∀ i < fullWatchSizeCore k l,
        wstk'[fullWatchOffCore { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                        wusable := wu' } l + i]? =
          k.wstk[fullWatchOffCore k l + i]?)
    (hokt : ok = true →
      lit.toNat < 2 * k.cur_vars ∧ (2 = 1 ∨ 2 = 2) ∧
      fullWatchSizeCore { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
          lit.toNat = fullWatchSizeCore k lit.toNat + 2 ∧
      (∀ i < fullWatchSizeCore k lit.toNat,
        wstk'[fullWatchOffCore { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                        wusable := wu' } lit.toNat + i]? =
          k.wstk[fullWatchOffCore k lit.toNat + i]?) ∧
      wstk'[fullWatchOffCore { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                      wusable := wu' } lit.toNat + fullWatchSizeCore k lit.toNat]? =
        some w0 ∧
      (2 = 2 →
        wstk'[fullWatchOffCore { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                        wusable := wu' } lit.toNat +
          fullWatchSizeCore k lit.toNat + 1]? = some w1))
    (hokf : ok = false →
      lit.toNat < 2 * k.cur_vars →
      fullWatchSizeCore { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
          lit.toNat = fullWatchSizeCore k lit.toNat ∧
      ∀ i < fullWatchSizeCore k lit.toNat,
        wstk'[fullWatchOffCore { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                        wusable := wu' } lit.toNat + i]? =
          k.wstk[fullWatchOffCore k lit.toNat + i]?) :
    FullWitnessInv c F0 F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := fullWatchPush_preserves_modeWatchesInv (cnt := 2#32) hw.watches hlay' rfl rfl
      (fun _ hr => hr) (fun hc => by exfalso; revert hc; decide)
      (fun _ => ⟨hw0, fun h => absurd hdm h, hw1_lt, href⟩) hoth
      (fun h => by simpa using hokt h) hokf }

private def RewatchLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (arg : Tup Val [i64]) (mL : Mem 64) : Prop :=
  let (p, ()) := arg
  p.toNat ≤ s.core.arena_len ∧ (p.toNat < s.core.arena_len → p.toNat ∈ fullArenaClauseRefs s) ∧
  ∃ arL wvecL wstkL wlenL wuL wsL,
    let sL : FullState :=
      { core := { s.core with arena := arL, wvec := wvecL, wstk := wstkL, wlen := wlenL,
                              wusable := wuL }
        scratch := { s.scratch with wsort := wsL } }
    sL.LengthsOk c ∧ FullWitnessInv c F0 F_cur sL.core ∧
    fullArenaClauseRefs sL = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr sL r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb sL r = false) ∧
    (FullArenaVarsNodup s → FullArenaVarsNodup sL) ∧ (FullMem c sL ⋆ R) mL

private def RewatchSwapInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sL : FullState) (R : Mem 64 → Prop) (p : BitVec 64) (sz32 : BitVec 32)
    (_ : Tup Val []) (mA : Mem 64) : Prop :=
  ∃ arA : List (BitVec 32), arA.length = c.arena_cap ∧
    let sA : FullState := { sL with core := { sL.core with arena := arA } }
    FullWitnessInv c F0 F_cur sA.core ∧ fullArenaClauseRefs sA = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr sA r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb sA r = false) ∧
    fullArenaClauseSize sA p.toNat = sz32.toNat ∧
    (FullArenaVarsNodup s → FullArenaVarsNodup sA) ∧ (FullMem c sA ⋆ R) mA

theorem full_rewatch_arena_wp (Γ : Env)
    (hrank : ∀ a m Q X, fullLitRankSpec a m Q X →
      Γ "full_lit_rank" [i64, i64, i32] [i64] a m Q X)
    (hpush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullRewatchArenaSpec a m Q X → Func.wp Γ full_rewatch_arena_body a m Q X := by
  rintro ⟨h, dst, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hdst_eq, hw, hdm0, hno_sg, hm, hQ⟩
  change fullRewatchArenaPost c F0 F_cur s R Q at hQ
  have hcap_lt : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hal_le := hlen.core_ok.arena_len_le
  have hcv_le := hlen.core_ok.cur_vars_le
  have hv_len := hlen.core_ok.vals_len
  have hl_len := hlen.core_ok.lvl_len
  fr_steps
  refine wp_loop_inv (RewatchLoopInv c F0 F_cur s R)
    (fun (p, ()) _ => s.core.arena_len - p.toNat) (fun JL hLoopL => ?_) ?_
  · fr_steps
    refine hLoopL (0#64, ()) m
      ⟨Nat.zero_le _, fun hpos => fullArenaClauseRefs_zero_mem hw.arena hpos,
       s.core.arena, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable, s.scratch.wsort,
       hlen, hw, rfl, hno_sg, id, hm⟩
  · rintro JL ⟨p, ⟨⟩⟩ mL
      ⟨hp_le, hp_mem, arL, wvecL, wstkL, wlenL, wuL, wsL, hlenL, hwL, hrefsL, hnoL, hndL, hmL⟩
      hLoopL
    let sL : FullState :=
      { core := { s.core with arena := arL, wvec := wvecL, wstk := wstkL, wlen := wlenL,
                              wusable := wuL }
        scratch := { s.scratch with wsort := wsL } }
    have harL_len : arL.length = c.arena_cap := hlenL.core_ok.arena_len_arr
    fr_split
    · have hp_lt : p.toNat < s.core.arena_len := by
        have : p.toNat < dst.toNat := by c0_bound
        omega
      have hp_ref0 : p.toNat ∈ fullArenaClauseRefs s := hp_mem hp_lt
      have hp_ref : p.toNat ∈ fullArenaClauseRefsCore sL.core := by
        change p.toNat ∈ fullArenaClauseRefs sL; rw [hrefsL]; exact hp_ref0
      have hpwf := hwL.arena.refs_wf p.toNat hp_ref
      have hp_no := hnoL p.toNat hp_ref0
      have hsz_ge3 : 3 ≤ fullArenaClauseSizeCore sL.core p.toNat := hpwf.2.1
      have hsz_fit : p.toNat + 3 + fullArenaClauseSizeCore sL.core p.toNat ≤ s.core.arena_len := by
        have h1 : p.toNat + 3 + fullArenaClauseSizeCore sL.core p.toNat ≤
            fullArenaNextOff arL s.core.arena_len p.toNat := hpwf.2.2.1
        have h2 : fullArenaNextOff arL s.core.arena_len p.toNat ≤ s.core.arena_len := hpwf.2.2.2.1
        omega
      have hp2_eq : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := bv64_add2 (by omega)
      have hp2_lt : (p + (2 : BitVec 64)).toNat < arL.length := by omega
      let sz32 := arL[(p + (2 : BitVec 64)).toNat]'hp2_lt
      have hsz_eq : sz32.toNat = fullArenaClauseSizeCore sL.core p.toNat := by
        have h1 : sz32 = arL[p.toNat + 2]'(by omega) := by dsimp only [sz32]; simp only [hp2_eq]
        unfold fullArenaClauseSizeCore sL
        simp [h1, List.getElem?_eq_getElem (by omega : p.toNat + 2 < arL.length)]
      have hsz_fit2 : p.toNat + 3 + sz32.toNat ≤ s.core.arena_len := by rw [hsz_eq]; exact hsz_fit
      have hsz_ge32 : 3 ≤ sz32.toNat := by omega
      have hnext_eq : fullArenaNextOff arL s.core.arena_len p.toNat = p.toNat + 3 + sz32.toNat := by
        have h1 : (arL[p.toNat]?.getD 0#32 &&& 0x00800000#32) = 0#32 := hp_no.1
        have h2 : (arL[p.toNat + 2]?.getD 0#32).toNat = sz32.toNat := by
          rw [hsz_eq]; rfl
        simp [fullArenaNextOff, show ¬ (p.toNat + 3 > s.core.arena_len) by omega, h2,
          show ¬ (p.toNat + 3 + sz32.toNat > s.core.arena_len) by omega, h1]
      have hnext_mem : p.toNat + 3 + sz32.toNat = s.core.arena_len ∨
          p.toNat + 3 + sz32.toNat ∈ fullArenaClauseRefs s := by
        have h := fullArenaClauseRefs_next_or_end hwL.arena hp_ref
        change _ = s.core.arena_len ∨ _ ∈ fullArenaClauseRefs sL at h
        rwa [show fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat =
          p.toNat + 3 + sz32.toNat from hnext_eq, hrefsL] at h
      clear hnext_eq
      fr_to_group
      refine wp_join_group (RewatchSwapInv c F0 F_cur s sL R p sz32) ?_ ?_
      · rintro _ ⟨⟩ mA ⟨arA, harA, hwA, hrefsA, hnoA, hszA, hndA, hmA⟩
        -- Set `ar[p + 1] = 2u`, then push 2 large watches `(l0, l1 & mask, p)` & `(l1, l0 & mask)`
        clear hrank hwL hrefsL hnoL hndL hp_ref hp_no hpwf hsz_fit hsz_eq harL_len hmL
        have hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := bv64_add1 (by omega)
        have hp1_lt : (p + (1 : BitVec 64)).toNat < arA.length := by omega
        let arB := arA.set (p + (1 : BitVec 64)).toNat 2#32
        let sB : FullState := { sL with core := { sL.core with arena := arB } }
        obtain ⟨harB, hlenB, hwB, hrefsB_s, hrefB, hnoB, hndB⟩ :=
          rewatch_set_saved_step hlenL hp_ref0 hsz_fit2 hal_le harA hwA hrefsA hnoA hszA hndA hp1_eq
        have harB_len : arB.length = c.arena_cap := harB
        have hp3_eq : (p + (3 : BitVec 64)).toNat = p.toNat + 3 := bv64_add3 (by omega)
        have hp4_eq : (p + (4 : BitVec 64)).toNat = p.toNat + 4 := bv64_add4 (by omega)
        have hp3_lt : (p + (3 : BitVec 64)).toNat < arB.length := by omega
        have hp4_lt : (p + (4 : BitVec 64)).toNat < arB.length := by omega
        let l0 := arB[(p + (3 : BitVec 64)).toNat]'hp3_lt
        let l1 := arB[(p + (4 : BitVec 64)).toNat]'hp4_lt
        have hp32_eq : (p.setWidth 32).toNat = p.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        have hp32_lt : (p.setWidth 32).toNat < 0x80000000 := by omega
        have hp32_ne : p.setWidth 32 ≠ 0xFFFFFFFF#32 := fun h => by
          have := congrArg BitVec.toNat h; simp at this; omega
        have hlw0 := bv32_large_word_props l1
        have hlw1 := bv32_large_word_props l0
        have hwB_sp : WatchesInv F_cur sB.core := modeWatchesInv_to_sparse hwB.watches hdm0
        fr_steps; c0_call hpush
        refine ⟨c, sB, R, rfl, hlenB, hwB_sp.layout, fun h => by exfalso; revert h; decide,
          fun _ => ⟨hlw0.2, hp32_ne⟩, hm,
          fun ok1 wvec1 wstk1 wlen1 wu1 ws1 m1 hlen1 hlay1 hoth1 hok1t hok1f hm1 => ?_⟩
        have hw1 := rewatch_push_step hwB hdm0 hlay1 hlw0.1 hp32_lt (by rw [hp32_eq]; exact hrefB)
          hoth1 hok1t hok1f
        clear hoth1 hok1t hok1f hwB_sp hlw0 hlenB hm
        fr_split
        · -- `ok1 = true`: push second large watch
          fr_steps; c0_call hpush
          refine ⟨c, { core := { sB.core with wvec := wvec1, wstk := wstk1, wlen := wlen1,
                                              wusable := wu1 }
                       scratch := { s.scratch with wsort := ws1 } }, R, rfl, hlen1, hlay1,
            fun h => by exfalso; revert h; decide, fun _ => ⟨hlw1.2, hp32_ne⟩, hm1,
            fun ok2 wvec2 wstk2 wlen2 wu2 ws2 m2 hlen2 hlay2 hoth2 hok2t hok2f hm2 => ?_⟩
          have hw2 := rewatch_push_step hw1 hdm0 hlay2 hlw1.1 hp32_lt
            (by rw [hp32_eq]; exact hrefB) hoth2 hok2t hok2f
          clear hoth2 hok2t hok2f hlw1 hlen1 hlay1 hm1 hpush
          fr_split
          · -- `ok2 = true`: advance `p := p + 3 + sz`
            have hp_next_eq : (p + (3 : BitVec 64) + sz32.setWidth 64).toNat =
                p.toNat + 3 + sz32.toNat := bv64_add3_zext_toNat (by omega)
            fr_steps
            refine hLoopL (p + (3 : BitVec 64) + sz32.setWidth 64, ()) m2
              (by dsimp only; rw [hp_next_eq]; omega)
              ⟨by rw [hp_next_eq]; omega, fun hlt => ?_, arB, wvec2, wstk2, wlen2, wu2, ws2,
               hlen2, hw2, hrefsB_s, hnoB, hndB, hm2⟩
            rw [hp_next_eq] at hlt ⊢
            rcases hnext_mem with he | hmem
            · omega
            · exact hmem
          · -- `ok2 = false`: OOM, return `false`
            fr_steps
            exact hQ false arB wvec2 wstk2 wlen2 wu2 1#64 ws2 m
              ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩ (fullWitnessInv_with_oom hw2)
              hrefsB_s hndB (fun h => Bool.noConfusion h) (fun _ => rfl) (fullMem_cast hm rfl)
        · -- `ok1 = false`: OOM, return `false`
          fr_steps
          exact hQ false arB wvec1 wstk1 wlen1 wu1 1#64 ws1 m
            ⟨{ hlen1.core_ok with }, hlen1.scratch_ok⟩ (fullWitnessInv_with_oom hw1)
            hrefsB_s hndB (fun h => Bool.noConfusion h) (fun _ => rfl) (fullMem_cast hm rfl)
      · -- Entry to `!at_root && sz >= 3` swap block
        intro JA hJA
        clear hLoopL JL hQ hpush hnext_mem hw hlen hno_sg hdst_eq hdm0 hp_le hp_mem hsz_ge3
          hsz_fit hp2_eq
        fr_split
        · -- `at_root = true`: skip swap block
          fr_steps; exact hJA () mL ⟨arL, harL_len, hwL, hrefsL, hnoL, hsz_eq.symm, hndL, hmL⟩
        · -- `at_root = false`: check `sz ≥ 3`
          fr_split
          · -- `sz ≥ 3`: find best `i0`, swap `0 ↔ i0`, find best `i1`, swap `1 ↔ i1`
            have hp3_eq : (p + (3 : BitVec 64)).toNat = p.toNat + 3 := bv64_add3 (by omega)
            have hp3_lt : (p + (3 : BitVec 64)).toNat < arL.length := by omega
            have hl0_lt : (arL[(p + (3 : BitVec 64)).toNat]'hp3_lt).toNat <
                2 * s.core.cur_vars := by
              have h1 : arL[(p + (3 : BitVec 64)).toNat]'hp3_lt = arL[p.toNat + 3]'(by omega) := by
                simp only [hp3_eq]
              have := rewatch_lit_lt (k := sL.core) (by change _ ≤ arL.length; omega)
                hwL hp_ref hp_no.2 hsz_eq.symm (j := 0) (by omega)
              rw [Nat.add_zero, List.getElem?_eq_getElem (by omega : p.toNat + 3 < arL.length),
                Option.getD_some] at this; rwa [h1]
            fr_steps; c0_call hrank
            refine ⟨s.core.vals, s.core.lvl, FullValsLvlRest c sL ⋆ R, by omega, by omega,
              focus_full_vals_lvl hmL, fun r0 => ?_⟩
            fr_steps
            -- Loop 1: find best `i0 ∈ [0, sz)`
            refine wp_loop_inv
              (fun (i0, _r0, i, ()) m1 =>
                mL = m1 ∧ i0.toNat < sz32.toNat ∧ 1 ≤ i.toNat ∧ i.toNat ≤ sz32.toNat)
              (fun (_, _, i, ()) _ => sz32.toNat - i.toNat)
              (fun J1 hLoop1 => by
                fr_steps; exact hLoop1 (0#32, r0, 1#32, ()) mL
                  ⟨rfl, by simp; omega, by decide, by simp; omega⟩)
              (fun J1 (i0, r0c, i, ()) _ ⟨rfl, hi0_lt, hi1, hi_le⟩ hLoop1 => ?_)
            fr_split
            · have hi_lt : i.toNat < sz32.toNat := by c0_bound
              have hi_next : (i + (1 : BitVec 32)).toNat = i.toNat + 1 :=
                bv32_add1 (by omega)
              have hpi_eq : (p + (3 : BitVec 64) + i.setWidth 64).toNat =
                  p.toNat + 3 + i.toNat := bv64_add3_zext_toNat (by omega)
              have hpi_lt : (p + (3 : BitVec 64) + i.setWidth 64).toNat < arL.length := by omega
              have hli_lt : (arL[(p + (3 : BitVec 64) + i.setWidth 64).toNat]'hpi_lt).toNat <
                  2 * s.core.cur_vars := by
                have h1 : arL[(p + (3 : BitVec 64) + i.setWidth 64).toNat]'hpi_lt =
                    arL[p.toNat + 3 + i.toNat]'(by omega) := by simp only [hpi_eq]
                have := rewatch_lit_lt (k := sL.core) (by change _ ≤ arL.length; omega)
                  hwL hp_ref hp_no.2 hsz_eq.symm hi_lt
                rw [List.getElem?_eq_getElem (by omega : p.toNat + 3 + i.toNat < arL.length),
                  Option.getD_some] at this; rwa [h1]
              fr_steps; c0_call hrank
              refine ⟨s.core.vals, s.core.lvl, FullValsLvlRest c sL ⋆ R, by omega, by omega,
                focus_full_vals_lvl hmL, fun rk => ?_⟩
              fr_steps
              · exact hLoop1 (i, rk, i + (1 : BitVec 32), ()) mL
                  (by dsimp only; rw [hi_next]; omega)
                  ⟨rfl, hi_lt, by rw [hi_next]; omega, by rw [hi_next]; omega⟩
              · exact hLoop1 (i0, r0c, i + (1 : BitVec 32), ()) mL
                  (by dsimp only; rw [hi_next]; omega)
                  ⟨rfl, hi0_lt, by rw [hi_next]; omega, by rw [hi_next]; omega⟩
            · -- Exit loop 1: optional swap `0 ↔ i0`, then loop 2 + optional swap `1 ↔ i1`
              clear hLoop1 J1
              fr_to_group
              refine wp_join_group (RewatchSwapInv c F0 F_cur s sL R p sz32) ?_ ?_
              · rintro _ ⟨⟩ m1 ⟨ar1, har1, hw1, hrefs1, hno1, hsz1, hnd1, hm1⟩
                clear hwL hrefsL hnoL hndL hp_ref hp_no hpwf harL_len hp3_eq hp3_lt hl0_lt r0 hmL
                let s1 : FullState := { sL with core := { sL.core with arena := ar1 } }
                have hp_ref1 : p.toNat ∈ fullArenaClauseRefsCore s1.core := by
                  change p.toNat ∈ fullArenaClauseRefs s1; rw [hrefs1]; exact hp_ref0
                have hp4_eq : (p + (4 : BitVec 64)).toNat = p.toNat + 4 := bv64_add4 (by omega)
                have hp4_lt : (p + (4 : BitVec 64)).toNat < ar1.length := by omega
                have hl1_lt : (ar1[(p + (4 : BitVec 64)).toNat]'hp4_lt).toNat <
                    2 * s.core.cur_vars := by
                  have h1 : ar1[(p + (4 : BitVec 64)).toNat]'hp4_lt = ar1[p.toNat + 4]'(by omega) :=
                    by simp only [hp4_eq]
                  have := rewatch_lit_lt (k := s1.core) (by change _ ≤ ar1.length; omega)
                    hw1 hp_ref1 (hno1 _ hp_ref0).2 hsz1 (j := 1) (by omega)
                  rw [show p.toNat + 3 + 1 = p.toNat + 4 by omega,
                    List.getElem?_eq_getElem (by omega : p.toNat + 4 < ar1.length),
                    Option.getD_some] at this; rwa [h1]
                fr_steps; c0_call hrank
                refine ⟨s.core.vals, s.core.lvl, FullValsLvlRest c s1 ⋆ R, by omega, by omega,
                  focus_full_vals_lvl hm1, fun r1 => ?_⟩
                fr_steps
                refine wp_loop_inv
                  (fun (i, i1, _r1, ()) m2 =>
                    m1 = m2 ∧ i1.toNat < sz32.toNat ∧ 2 ≤ i.toNat ∧ i.toNat ≤ sz32.toNat)
                  (fun (i, _, _, ()) _ => sz32.toNat - i.toNat)
                  (fun J2 hLoop2 => by
                    fr_steps; exact hLoop2 (2#32, 1#32, r1, ()) m1
                      ⟨rfl, by simp; omega, by decide, by simp; omega⟩)
                  (fun J2 (i, i1, r1c, ()) _ ⟨rfl, hi1_lt, hi2, hi_le2⟩ hLoop2 => ?_)
                fr_split
                · have hi_lt : i.toNat < sz32.toNat := by c0_bound
                  have hi_next : (i + (1 : BitVec 32)).toNat = i.toNat + 1 :=
                    bv32_add1 (by omega)
                  have hpi_eq : (p + (3 : BitVec 64) + i.setWidth 64).toNat =
                      p.toNat + 3 + i.toNat := bv64_add3_zext_toNat (by omega)
                  have hpi_lt : (p + (3 : BitVec 64) + i.setWidth 64).toNat < ar1.length := by omega
                  have hli_lt : (ar1[(p + (3 : BitVec 64) + i.setWidth 64).toNat]'hpi_lt).toNat <
                      2 * s.core.cur_vars := by
                    have h1 : ar1[(p + (3 : BitVec 64) + i.setWidth 64).toNat]'hpi_lt =
                        ar1[p.toNat + 3 + i.toNat]'(by omega) := by simp only [hpi_eq]
                    have := rewatch_lit_lt (k := s1.core) (by change _ ≤ ar1.length; omega)
                      hw1 hp_ref1 (hno1 _ hp_ref0).2 hsz1 hi_lt
                    rw [List.getElem?_eq_getElem (by omega : p.toNat + 3 + i.toNat < ar1.length),
                      Option.getD_some] at this; rwa [h1]
                  fr_steps; c0_call hrank
                  refine ⟨s.core.vals, s.core.lvl, FullValsLvlRest c s1 ⋆ R, by omega, by omega,
                    focus_full_vals_lvl hm1, fun rk => ?_⟩
                  fr_steps
                  · exact hLoop2 (i + (1 : BitVec 32), i, rk, ()) m1
                      (by dsimp only; rw [hi_next]; omega)
                      ⟨rfl, hi_lt, by rw [hi_next]; omega, by rw [hi_next]; omega⟩
                  · exact hLoop2 (i + (1 : BitVec 32), i1, r1c, ()) m1
                      (by dsimp only; rw [hi_next]; omega)
                      ⟨rfl, hi1_lt, by rw [hi_next]; omega, by rw [hi_next]; omega⟩
                · -- Optional swap `1 ↔ i1`
                  clear hLoop2 J2 hrank
                  fr_split
                  · have hpi1_eq : (p + (3 : BitVec 64) + i1.setWidth 64).toNat =
                        p.toNat + 3 + i1.toNat := bv64_add3_zext_toNat (by omega)
                    have hpi1_lt : (p + (3 : BitVec 64) + i1.setWidth 64).toNat < ar1.length := by
                      omega
                    fr_steps
                    obtain ⟨har2, hw2, hrefs2, hno2, hsz2, hnd2⟩ :=
                      rewatch_swap_step hlenL hp_ref0 hsz_fit2 hal_le har1 hw1 hrefs1 hno1 hsz1 hnd1
                        (a := 1) (b := i1.toNat) (by omega) hi1_lt
                    let ar2 :=
                      (ar1.set (p.toNat + 3 + 1) (ar1[p.toNat + 3 + i1.toNat]'(by omega))).set
                        (p.toNat + 3 + i1.toNat) (ar1[p.toNat + 3 + 1]'(by omega))
                    have hm_eq := list_swap_eq_of_idx (xs := ar1) hp4_eq
                      hpi1_eq hp4_lt hpi1_lt (by omega) (by omega)
                    exact hJA () m
                      ⟨ar2, har2, hw2, hrefs2, hno2, hsz2, hnd2,
                        fullMem_cast hm (by rw [hm_eq])⟩
                  · fr_steps
                    exact hJA () m1 ⟨ar1, har1, hw1, hrefs1, hno1, hsz1, hnd1, hm1⟩
              · intro J1s hJ1s
                clear hrank r0 hl0_lt hp_no hpwf
                fr_split
                · have hpi0_eq : (p + (3 : BitVec 64) + i0.setWidth 64).toNat =
                      p.toNat + 3 + i0.toNat := bv64_add3_zext_toNat (by omega)
                  have hpi0_lt : (p + (3 : BitVec 64) + i0.setWidth 64).toNat < arL.length := by
                    omega
                  fr_steps
                  obtain ⟨har1, hw1, hrefs1, hno1, hsz1, hnd1⟩ :=
                    rewatch_swap_step hlenL hp_ref0 hsz_fit2 hal_le harL_len hwL hrefsL hnoL
                      hsz_eq.symm hndL (a := 0) (b := i0.toNat) (by omega) hi0_lt
                  let ar1 :=
                    (arL.set (p.toNat + 3 + 0) (arL[p.toNat + 3 + i0.toNat]'(by omega))).set
                      (p.toNat + 3 + i0.toNat) (arL[p.toNat + 3 + 0]'(by omega))
                  have hm_eq := list_swap_eq_of_idx (xs := arL) hp3_eq
                    hpi0_eq hp3_lt hpi0_lt (by omega) (by omega)
                  exact hJ1s () m
                    ⟨ar1, har1, hw1, hrefs1, hno1, hsz1, hnd1,
                      fullMem_cast hm (by rw [hm_eq])⟩
                · fr_steps
                  exact hJ1s () mL ⟨arL, harL_len, hwL, hrefsL, hnoL, hsz_eq.symm, hndL, hmL⟩
          · -- `sz < 3`: unreachable, still safe
            fr_steps; exact hJA () mL ⟨arL, harL_len, hwL, hrefsL, hnoL, hsz_eq.symm, hndL, hmL⟩
    · -- Exit outer loop (`p = dst`): return `true`
      fr_steps
      exact hQ true arL wvecL wstkL wlenL wuL s.core.oom wsL mL hlenL hwL hrefsL hndL
        (fun _ => rfl) (fun h => Bool.noConfusion h) hmL

end LeanQbe.T.Examples.Kissat.Full
