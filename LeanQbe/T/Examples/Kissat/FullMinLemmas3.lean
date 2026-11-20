module

public import LeanQbe.T.Examples.Kissat.FullMinLemmas2
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for Kissat `D-Full` Minimization (`Stage 4`, Part 3)

Proves the parametric `(Γ : Env)` `Func.wp` contract for `full_min_lit`:
- `full_min_lit` (`FullMinSpecs.fullMinLitSpec`, `full_min_lit_wp`)
Uses `lvl_le_root` in `MinLitStkInv` (derived from `FullWitnessInv.reason_inv`) in place of
`trail_mono`, and preserves `mrk` above `cur_vars`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullArenaTactics
open FullMinSpecs

open scoped FullMinTactics

/-! ## 1. Iterative `full_min_lit` stack & DFS invariants -/

private def minLitRsnLit (k : FullCoreState) (rsn : BitVec 32) (pos : Nat) : Nat :=
  if (rsn &&& 0x80000000#32) ≠ 0#32 then (rsn &&& 0x7FFFFFFF#32).toNat
  else (k.arena[rsn.toNat + 3 + pos]?.getD 0#32).toNat

private def FrameCov (k : FullCoreState) (mrk1 : List (BitVec 8)) (idx lim : Nat) : Prop :=
  let p := (k.trl[idx]?.getD 0#32).toNat
  let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
  rsn ≠ 0xFFFFFFFF#32 ∧
  if (rsn &&& 0x80000000#32) ≠ 0#32 then
    let ot := (rsn &&& 0x7FFFFFFF#32).toNat
    ot < 2 * k.cur_vars ∧
    (0 < lim →
      ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
        ((k.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8))
  else
    rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
    3 ≤ fullArenaClauseSizeCore k rsn.toNat ∧
    ∀ pos < lim, pos < fullArenaClauseSizeCore k rsn.toNat →
      let q := (k.arena[rsn.toNat + 3 + pos]?.getD 0#32).toNat
      q = p ∨ ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((k.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)

private def EdgeChild (k : FullCoreState) (idx pos cidx : Nat) : Prop :=
  let p := (k.trl[idx]?.getD 0#32).toNat
  let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
  let l := minLitRsnLit k rsn pos
  cidx < idx ∧ (k.trl[cidx]?.getD 0#32).toNat = l ^^^ 1

private theorem frameCov_zero {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) (mrk1 : List (BitVec 8)) {idx : Nat}
    (hi : idx < s.core.trail_end)
    (hne : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
      0xFFFFFFFF#32) :
    FrameCov s.core mrk1 idx 0 := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  have hrs := hw.reason_inv idx hi hne
  refine ⟨hne, ?_⟩
  split at hrs <;> split
  · exact ⟨hrs.1, fun h => by omega⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · have hwf := hw.arena.refs_wf _ hrs.1
    exact ⟨hrs.1, hrs.2.1, hwf.2.1, fun _ h => by omega⟩

private theorem frameCov_arena_lits_bd {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore s.core) :
    cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  have hwf := hw.arena.refs_wf cref href
  have := hwf.2.2.1; have := hwf.2.2.2.1
  have := hcore.lengths.core_ok.arena_len_le; have := hcore.lengths.core_ok.arena_len_arr; omega

private theorem frameCov_arena_lits_mem {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {cref pos : Nat} (href : cref ∈ fullArenaClauseRefsCore s.core)
    (hp : pos < fullArenaClauseSizeCore s.core cref) :
    (s.core.arena[cref + 3 + pos]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s.core cref := by
  have hbd := frameCov_arena_lits_bd hcore href
  rw [mem_fullArenaClauseLitsCore_iff hbd]
  exact ⟨pos, hp, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩

private theorem frameCov_mono {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)}
    (hmono : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {idx lim : Nat} (hcov : FrameCov s.core mrk1 idx lim) : FrameCov s.core mrk2 idx lim := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  rcases hcov with ⟨hne, hif⟩
  refine ⟨hne, ?_⟩
  split at hif <;> split
  · refine ⟨hif.1, fun hl => ?_⟩
    obtain ⟨j, hj, hjeq, hdep⟩ := hif.2 hl
    exact ⟨j, hj, hjeq, hdep.elim Or.inl fun h2 => Or.inr (hmono _ (by omega) h2)⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · refine ⟨hif.1, hif.2.1, hif.2.2.1, fun pos hp1 hp2 => ?_⟩
    rcases hif.2.2.2 pos hp1 hp2 with heq | ⟨j, hj, hjeq, hdep⟩
    · exact Or.inl heq
    · have hqlt := hw.arena.lits_lt _ hif.1 hif.2.1 _ (frameCov_arena_lits_mem hcore hif.1 hp2)
      exact Or.inr ⟨j, hj, hjeq, hdep.elim Or.inl fun h2 => Or.inr (hmono _ (by omega) h2)⟩

private theorem frameCov_step {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mrk1 : List (BitVec 8)} {idx pos : Nat}
    (hi : idx < s.core.trail_end) (hcov : FrameCov s.core mrk1 idx pos)
    (hlt : pos < if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hstep :
      let p := (s.core.trl[idx]?.getD 0#32).toNat
      let rsn := s.core.rsns[p / 2]?.getD 0xFFFFFFFF#32
      let q := minLitRsnLit s.core rsn pos
      q / 2 = p / 2 ∨
      ∃ j < idx, (s.core.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)) :
    FrameCov s.core mrk1 idx (pos + 1) := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  dsimp only [FrameCov] at hcov ⊢
  rcases hcov with ⟨hne, hif⟩
  have hrs := hw.reason_inv idx hi hne
  refine ⟨hne, ?_⟩
  dsimp only [minLitRsnLit] at hstep ⊢
  dsimp only at hif hrs hlt hstep ⊢
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif hrs hlt hstep ⊢
    refine ⟨hif.1, fun _ => ?_⟩
    rcases hstep with hvar | ⟨j, hj, hjeq, hdep⟩
    · obtain ⟨j, hj, hjeq, _⟩ := hrs.2.2
      have hln := litVar_litNeg (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat
      unfold litVar litNeg at hln
      have hjp : j = idx := hw.trail_vars_nodup j idx (by omega) hi (by rw [hjeq, hln]; exact hvar)
      omega
    · exact ⟨j, hj, hjeq, hdep⟩
  · simp only [eq_false hbin, ↓reduceIte] at hif hrs hlt hstep ⊢
    refine ⟨hif.1, hif.2.1, hif.2.2.1, fun j hj1 hj2 => ?_⟩
    by_cases hjp : j < pos
    · exact hif.2.2.2 j hjp hj2
    · have hjeq : j = pos := by omega
      subst hjeq
      rcases hstep with hvar | hok
      · have hmem := frameCov_arena_lits_mem hcore hif.1 hj2
        rcases hrs.2.2 _ hmem with hqeq | ⟨k, hk, hkeq, _⟩
        · exact Or.inl hqeq
        · have hln := litVar_litNeg (s.core.arena[(s.core.rsns[(s.core.trl[idx]?.getD
            0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat + 3 + j]?.getD 0#32).toNat
          unfold litVar litNeg at hln
          have hkp : k = idx := hw.trail_vars_nodup k idx (by omega) hi
            (by rw [hkeq, hln]; exact hvar)
          omega
      · exact Or.inr hok

private theorem frameCov_to_hrsn {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mrk1 : List (BitVec 8)} {idx lim : Nat}
    (hcov : FrameCov s.core mrk1 idx lim)
    (hlim : (if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat) ≤ lim) :
    let p0 := (s.core.trl[idx]?.getD 0#32).toNat
    let rsn := s.core.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 ∧
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * s.core.cur_vars ∧
      ∃ j < idx, (s.core.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
        ((s.core.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    else
      rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
      fullArenaClauseGarbCore s.core rsn.toNat = false ∧
      ∀ q ∈ fullArenaClauseLitsCore s.core rsn.toNat,
        q = p0 ∨ ∃ j < idx, (s.core.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
          ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  dsimp only [FrameCov] at hcov
  rcases hcov with ⟨hne, hif⟩
  refine ⟨hne, ?_⟩
  dsimp only at hif hlim ⊢
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif hlim ⊢
    exact ⟨hif.1, hif.2 (by omega)⟩
  · simp only [eq_false hbin, ↓reduceIte] at hif hlim ⊢
    refine ⟨hif.1, hif.2.1, fun q hq => ?_⟩
    have hbd := frameCov_arena_lits_bd hcore hif.1
    obtain ⟨j, hj, hjeq⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hq
    have hq' := hif.2.2.2 j (by omega) hj
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, hjeq] at hq'

private theorem frameCov_edge_exists {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mrk1 : List (BitVec 8)} {idx pos : Nat}
    (hi : idx < s.core.trail_end) (hcov : FrameCov s.core mrk1 idx pos)
    (hlt : pos < if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hneq : minLitRsnLit s.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32) pos / 2 ≠
      (s.core.trl[idx]?.getD 0#32).toNat / 2) :
    let q := minLitRsnLit s.core
      (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32) pos
    q < 2 * s.core.cur_vars ∧
    ∃ cidx < idx, (s.core.trl[cidx]?.getD 0#32).toNat = q ^^^ 1 ∧
      (s.core.lvl[q / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  dsimp only [FrameCov, minLitRsnLit] at hcov hlt hneq ⊢
  rcases hcov with ⟨hne, hif⟩
  have hrs := hw.reason_inv idx hi hne
  dsimp only at hif hrs hlt hneq ⊢
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif hrs hlt hneq ⊢
    exact ⟨hrs.1, hrs.2.2⟩
  · simp only [eq_false hbin, ↓reduceIte] at hif hrs hlt hneq ⊢
    have hmem := frameCov_arena_lits_mem hcore hif.1 hlt
    have hqlt := hw.arena.lits_lt _ hif.1 hif.2.1 _ hmem
    refine ⟨hqlt, ?_⟩
    rcases hrs.2.2 _ hmem with heq | hex
    · exact absurd (by rw [heq]) hneq
    · exact hex

private theorem dec_chain_lt : ∀ {idxs : List Nat} {i j : Nat},
    (∀ k (hk : k + 1 < idxs.length), idxs[k + 1] < idxs[k]) →
    i < j → (hi : i < idxs.length) → (hj : j < idxs.length) → idxs[j] < idxs[i] := by
  intro idxs i j hdec hij hi hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hj_lt := hdec j hj
    by_cases heq : i = j
    · subst heq; exact hj_lt
    · exact Nat.lt_trans hj_lt (ih (by omega) (by omega))

private structure MinLitStkInv (k : FullCoreState) (mstk1 : List (BitVec 32))
    (mrk1 : List (BitVec 8)) (sp idx0 : Nat) (idxs : List Nat) (reqCov : Bool) : Prop where
  len : idxs.length = sp + 1
  idx0_eq : idxs[0]? = some idx0
  bd : ∀ j (hj : j < idxs.length), idxs[j] < k.trail_end
  dec : ∀ j (hj : j + 1 < idxs.length), idxs[j + 1] < idxs[j]
  lvl_le_root : ∀ j (hj : j < idxs.length),
    (k.lvl[(k.trl[idxs[j]]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (k.lvl[(k.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  slot : ∀ j (hj : j < idxs.length),
    let vj := (k.trl[idxs[j]]?.getD 0#32).toNat / 2
    (mstk1[2 * j]?.getD 0#32).toNat = vj ∧ (1 ≤ j → mrk1[vj]?.getD 0#8 = 0#8)
  cov : reqCov = true → ∀ j (hj : j < idxs.length),
    let posj := (mstk1[2 * j + 1]?.getD 0#32).toNat
    let rsn := k.rsns[(k.trl[idxs[j]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
    (∀ _hj1 : j + 1 < idxs.length, 1 ≤ posj ∧
      posj ≤ (if (rsn &&& 0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore k rsn.toNat) ∧
      EdgeChild k idxs[j] (posj - 1) idxs[j + 1]) ∧
    FrameCov k mrk1 idxs[j] (if j + 1 = idxs.length then posj else posj - 1)

private theorem minLitStkInv_drop_cov {k : FullCoreState} {mstk1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {sp idx0 : Nat} {idxs : List Nat}
    (h : MinLitStkInv k mstk1 mrk1 sp idx0 idxs true) :
    MinLitStkInv k mstk1 mrk1 sp idx0 idxs false :=
  ⟨h.len, h.idx0_eq, h.bd, h.dec, h.lvl_le_root, h.slot, fun hc => by cases hc⟩

private theorem minLitStkInv_var_ne {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mstk1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {sp idx0 : Nat} {idxs : List Nat} {req}
    (h : MinLitStkInv s.core mstk1 mrk1 sp idx0 idxs req)
    {i j : Nat} (hi : i < idxs.length) (hj : j < idxs.length) (hne : i ≠ j) :
    (s.core.trl[idxs[i]]?.getD 0#32).toNat / 2 ≠ (s.core.trl[idxs[j]]?.getD 0#32).toNat / 2 := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  intro heq
  have hij := hw.trail_vars_nodup idxs[i] idxs[j] (h.bd i hi) (h.bd j hj) heq
  rcases Nat.lt_or_gt_of_ne hne with h1 | h2
  · have := dec_chain_lt h.dec h1 hi hj; omega
  · have := dec_chain_lt h.dec h2 hj hi; omega

private theorem minLitStkInv_poison_other {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mstk1 mclr1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {sp idx0 u_idx mcl1 : Nat} {mcf1 : BitVec 64}
    {idxs : List Nat} (h : MinLitStkInv s.core mstk1 mrk1 sp idx0 idxs false)
    (hu_idx : ∀ j (hj : j < idxs.length), u_idx < idxs[j])
    (hmrk_eq : ∀ w < s.core.cur_vars, w ≠ (s.core.trl[u_idx]?.getD 0#32).toNat / 2 →
      mrk1[w]?.getD 0#8 = (fullMinMarkCore
        (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core
        ((s.core.trl[u_idx]?.getD 0#32).toNat / 2) 4#8).mrk[w]?.getD 0#8) :
    MinLitStkInv s.core mstk1
      (fullMinMarkCore (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core
        ((s.core.trl[u_idx]?.getD 0#32).toNat / 2) 4#8).mrk sp idx0 idxs false := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  refine ⟨h.len, h.idx0_eq, h.bd, h.dec, h.lvl_le_root, fun j hj => ?_, fun hc => by cases hc⟩
  refine ⟨(h.slot j hj).1, fun hj1 => ?_⟩
  have hvj : (s.core.trl[idxs[j]]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
    have := hw.trail_lits_lt idxs[j] (h.bd j hj); omega
  have hne : (s.core.trl[idxs[j]]?.getD 0#32).toNat / 2 ≠
      (s.core.trl[u_idx]?.getD 0#32).toNat / 2 := fun heq => by
    have hlt := hu_idx j hj
    have := hw.trail_vars_nodup idxs[j] u_idx (h.bd j hj) (Nat.lt_trans hlt (h.bd j hj)) heq
    omega
  rw [← hmrk_eq _ hvj hne]
  exact (h.slot j hj).2 hj1

private theorem minLitStkInv_step_top {c : FullCfg} {k : FullCoreState}
    {mstk1 : List (BitVec 32)} {mrk1 : List (BitVec 8)} {sp idx0 : Nat} {idxs : List Nat}
    (h : MinLitStkInv k mstk1 mrk1 sp idx0 idxs true)
    (hmstk_len : mstk1.length = 2 * c.minDepth) (hsp : sp < c.minDepth) (newPos : BitVec 32)
    (hcov_top : ∀ hk : sp < idxs.length, FrameCov k mrk1 idxs[sp] newPos.toNat) :
    MinLitStkInv k (mstk1.set (2 * sp + 1) newPos) mrk1 sp idx0 idxs true := by
  have hlt_stk : 2 * sp + 1 < mstk1.length := by omega
  refine ⟨h.len, h.idx0_eq, h.bd, h.dec, h.lvl_le_root, fun j hj => ?_, fun _ j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact h.slot j hj
  · have hlen := h.len
    by_cases htop : j = sp
    · subst htop
      rw [List.getElem?_set_self hlt_stk, Option.getD_some]
      refine ⟨fun hk1 => by omega, ?_⟩
      simp only [show j + 1 = idxs.length by omega, ↓reduceIte]
      exact hcov_top hj
    · have hne_len : ¬ (j + 1 = idxs.length) := by omega
      rw [List.getElem?_set_ne (by omega)]
      simpa only [hne_len, ↓reduceIte] using h.cov rfl j hj

private theorem minLitStkInv_push {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mstk1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {sp idx0 u_idx : Nat} {idxs : List Nat}
    (h : MinLitStkInv s.core mstk1 mrk1 sp idx0 idxs true)
    (hmstk_len : mstk1.length = 2 * c.minDepth) (hsp1 : sp + 1 < c.minDepth)
    {u_bv pos_bv : BitVec 32}
    (hpos_eq : pos_bv.toNat = (mstk1[2 * sp + 1]?.getD 0#32).toNat + 1)
    (hu_bd : u_idx < idxs[sp]'(by have := h.len; omega))
    (hu_eq : u_bv.toNat = (s.core.trl[u_idx]?.getD 0#32).toNat / 2)
    (hu_lvl : (s.core.lvl[(s.core.trl[u_idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hpos_lt : (mstk1[2 * sp + 1]?.getD 0#32).toNat <
      (if (s.core.rsns[(s.core.trl[idxs[sp]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1
        else fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idxs[sp]'(by
          have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat))
    (hmrk_u : mrk1[u_bv.toNat]?.getD 0#8 = 0#8)
    (hrsn_u : s.core.rsns[u_bv.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hedge : EdgeChild s.core (idxs[sp]'(by have := h.len; omega))
      (mstk1[2 * sp + 1]?.getD 0#32).toNat u_idx) :
    let mstk2 := ((mstk1.set (2 * sp + 1) pos_bv).set (2 * (sp + 1)) u_bv).set
      (2 * (sp + 1) + 1) 0#32
    MinLitStkInv s.core mstk2 mrk1 (sp + 1) idx0 (idxs ++ [u_idx]) true := by
  intro mstk2
  have hlen := h.len
  have hb1 : 2 * sp + 1 < mstk1.length := by omega
  have hb2 : 2 * (sp + 1) < (mstk1.set (2 * sp + 1) pos_bv).length := by simp [hmstk_len]; omega
  have hb3 : 2 * (sp + 1) + 1 <
      ((mstk1.set (2 * sp + 1) pos_bv).set (2 * (sp + 1)) u_bv).length := by
    simp [hmstk_len]; omega
  have idx_lt : ∀ j (hj : j < idxs.length), (idxs ++ [u_idx])[j]'(by simp; omega) = idxs[j] :=
    fun j hj => List.getElem_append_left hj
  have idx_last : (idxs ++ [u_idx])[idxs.length]'(by simp) = u_idx := by simp
  refine ⟨by simp [hlen], ?_, ?_, ?_, ?_, fun j hj => ?_, fun _ j hj => ?_⟩
  · rw [List.getElem?_append_left (by omega)]; exact h.idx0_eq
  · intro j hj
    by_cases hjl : j < idxs.length
    · rw [idx_lt j hjl]; exact h.bd j hjl
    · have hjeq : j = idxs.length := by simp at hj; omega
      subst j; rw [idx_last]; exact Nat.lt_trans hu_bd (h.bd sp (by omega))
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjl : j + 1 < idxs.length
    · rw [idx_lt j (by omega), idx_lt (j + 1) hjl]; exact h.dec j hjl
    · have hjeq : j = sp := by omega
      subst j
      rw [idx_lt sp (by omega), List.getElem_append_right (by omega : idxs.length ≤ sp + 1)]
      simp only [hlen, Nat.sub_self, List.getElem_cons_zero]; exact hu_bd
  · intro j hj
    by_cases hjl : j < idxs.length
    · rw [idx_lt j hjl]; exact h.lvl_le_root j hjl
    · have hjeq : j = idxs.length := by simp at hj; omega
      subst j; rw [idx_last]; exact hu_lvl
  · by_cases hjl : j < idxs.length
    · rw [idx_lt j hjl]; dsimp only [mstk2]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega)]
      exact h.slot j hjl
    · have hjeq : j = idxs.length := by simp at hj; omega
      subst j; rw [idx_last]; dsimp only [mstk2]
      rw [List.getElem?_set_ne (by omega), show 2 * idxs.length = 2 * (sp + 1) by omega,
        List.getElem?_set_self hb2, Option.getD_some]
      exact ⟨hu_eq, fun _ => by rwa [← hu_eq]⟩
  · by_cases hjl : j < idxs.length
    · rw [idx_lt j hjl]
      by_cases htop : j = sp
      · subst j; dsimp only [mstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self hb1, Option.getD_some]
        refine ⟨fun _ => ?_, ?_⟩
        · rw [hpos_eq]; refine ⟨by omega, by omega, ?_⟩
          rw [List.getElem_append_right (by omega : idxs.length ≤ sp + 1)]
          simp only [hlen, Nat.sub_self, List.getElem_cons_zero]; exact hedge
        · have hne : sp + 1 ≠ (idxs ++ [u_idx]).length := by
            rw [List.length_append, List.length_singleton, hlen]; omega
          simp only [hne, ↓reduceIte, hpos_eq, Nat.add_sub_cancel]
          have hcov_sp := (h.cov rfl sp hjl).2
          have heq_sp : sp + 1 = idxs.length := by omega
          simpa only [heq_sp, ↓reduceIte] using hcov_sp
      · have hj1 : j + 1 < idxs.length := by omega
        dsimp only [mstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega)]
        have hprev := h.cov rfl j hjl
        have hne1 : j + 1 ≠ (idxs ++ [u_idx]).length := by
          rw [List.length_append, List.length_singleton, hlen]; omega
        have hne2 : j + 1 ≠ idxs.length := by omega
        simp only [hne1, hne2, ↓reduceIte] at hprev ⊢
        refine ⟨fun _ => ?_, hprev.2⟩
        rw [idx_lt (j + 1) hj1]; exact hprev.1 hj1
    · have hjeq : j = idxs.length := by simp at hj; omega
      subst j; rw [idx_last]; dsimp only [mstk2]
      rw [show 2 * idxs.length + 1 = 2 * (sp + 1) + 1 by omega, List.getElem?_set_self hb3,
        Option.getD_some]
      refine ⟨fun hk1 => by simp only [List.length_append, List.length_singleton] at hk1; omega,
        ?_⟩
      simp only [List.length_append, List.length_singleton, ↓reduceIte, BitVec.toNat_ofNat]
      exact frameCov_zero hcore mrk1 (Nat.lt_trans hu_bd (h.bd sp (by omega)))
        (by rw [← hu_eq]; exact hrsn_u)

private theorem minLitStkInv_pop {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mstk1 : List (BitVec 32)} {mrk1 mrk2 : List (BitVec 8)}
    {sp idx0 : Nat} {idxs : List Nat}
    (h : MinLitStkInv s.core mstk1 mrk1 sp idx0 idxs true) (hsp : 0 < sp)
    (hmono : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hmrk_top : (mrk2[(s.core.trl[idxs[sp]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD
      0#8 &&& 2#8) ≠ 0#8)
    (hmrk_keep : ∀ j (hj : j < sp),
      mrk2[(s.core.trl[idxs[j]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD 0#8 =
        mrk1[(s.core.trl[idxs[j]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD 0#8) :
    MinLitStkInv s.core mstk1 mrk2 (sp - 1) idx0 (idxs.take sp) true := by
  have hlen := h.len
  have htake_len : (idxs.take sp).length = sp := by rw [List.length_take, hlen]; omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, fun j hj => ?_, fun _ j hj => ?_⟩
  · rw [← h.idx0_eq]; exact List.getElem?_take_of_lt hsp
  · intro j hj; rw [List.getElem_take]; exact h.bd j (by omega)
  · intro j hj; rw [List.getElem_take, List.getElem_take]; exact h.dec j (by omega)
  · intro j hj; rw [List.getElem_take]; exact h.lvl_le_root j (by omega)
  · rw [List.getElem_take]
    refine ⟨(h.slot j (by omega)).1, fun hj1 => ?_⟩
    rw [hmrk_keep j (by omega)]; exact (h.slot j (by omega)).2 hj1
  · rw [List.getElem_take]
    have hprev := h.cov rfl j (by omega)
    have hne : j + 1 ≠ idxs.length := by omega
    simp only [hne, ↓reduceIte] at hprev
    by_cases hntop : j = sp - 1
    · subst j
      refine ⟨fun hk1 => by omega, ?_⟩
      simp only [htake_len, show sp - 1 + 1 = sp by omega, ↓reduceIte]
      have hpos1 : 1 ≤ (mstk1[2 * (sp - 1) + 1]?.getD 0#32).toNat := (hprev.1 (by omega)).1
      have hpos_le := (hprev.1 (by omega)).2.1
      have hedge := (hprev.1 (by omega)).2.2
      simp only [show sp - 1 + 1 = sp by omega] at hedge
      have hcov_m := frameCov_mono hcore hmono hprev.2
      dsimp only [EdgeChild] at hedge
      have hsz_lt : (mstk1[2 * (sp - 1) + 1]?.getD 0#32).toNat - 1 <
          if (s.core.rsns[(s.core.trl[idxs[sp - 1]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
              0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
            (s.core.rsns[(s.core.trl[idxs[sp - 1]]?.getD 0#32).toNat / 2]?.getD
              0xFFFFFFFF#32).toNat := by omega
      have hstep := frameCov_step hcore (h.bd (sp - 1) (by omega)) hcov_m hsz_lt ?_
      · simpa only [show (mstk1[2 * (sp - 1) + 1]?.getD 0#32).toNat - 1 + 1 =
          (mstk1[2 * (sp - 1) + 1]?.getD 0#32).toNat by omega] using hstep
      · have hdec_sp : idxs[sp]'(by omega) < idxs[sp - 1]'(by omega) := by
          simpa [show sp - 1 + 1 = sp by omega] using h.dec (sp - 1) (by omega)
        refine Or.inr ⟨idxs[sp]'(by omega), hdec_sp, hedge.2, Or.inr ?_⟩
        have hvar : (minLitRsnLit s.core
            (s.core.rsns[(s.core.trl[idxs[sp - 1]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
            ((mstk1[2 * (sp - 1) + 1]?.getD 0#32).toNat - 1)) / 2 =
            (s.core.trl[idxs[sp]]?.getD 0#32).toNat / 2 := by
          have hl := litVar_litNeg (minLitRsnLit s.core
            (s.core.rsns[(s.core.trl[idxs[sp - 1]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
            ((mstk1[2 * (sp - 1) + 1]?.getD 0#32).toNat - 1))
          unfold litVar litNeg at hl; rw [← hl, ← hedge.2]
        rwa [hvar]
    · have hne2 : j + 1 ≠ (idxs.take sp).length := by omega
      simp only [hne2, ↓reduceIte]
      refine ⟨fun _ => ?_, frameCov_mono hcore hmono hprev.2⟩
      rw [List.getElem_take]; exact hprev.1 (by omega)

private structure MinLitStInv (c : FullCfg) (s : FullState) (keepSet : List Nat)
    (mrk1 : List (BitVec 8)) (mstk1 mclr1 : List (BitVec 32))
    (mcl1 : Nat) (mcf1 : BitVec 64) : Prop where
  mrk_len : mrk1.length = c.max_vars
  mstk_len : mstk1.length = 2 * c.minDepth
  mclr_len : mclr1.length = c.max_vars
  mcl_le : mcl1 ≤ c.max_vars
  mrk_above : ∀ w, s.core.cur_vars ≤ w → mrk1[w]? = s.core.mrk[w]?
  min_inv : FullMinMarkInv (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core keepSet
  mono2 : ∀ w < s.core.cur_vars,
    (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8
  bit8 : ∀ w < s.core.cur_vars,
    (mrk1[w]?.getD 0#8 &&& 8#8) = (s.core.mrk[w]?.getD 0#8 &&& 8#8)

private theorem MinLitStInv.core {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64} (hcore : FullCoreInv c F0 s)
    (h : MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1) :
    FullCoreInv c F0 (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) :=
  fullCoreInv_with_min hcore h.mrk_len h.mstk_len h.mclr_len h.mcl_le

private theorem minLitStInv_with_mstk {c : FullCfg} {s : FullState} {keepSet : List Nat}
    {mrk1 : List (BitVec 8)} {mstk1 mclr1 mstk' : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64}
    (h : MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1)
    (hmstk' : mstk'.length = 2 * c.minDepth) :
    MinLitStInv c s keepSet mrk1 mstk' mclr1 mcl1 mcf1 :=
  { h with
    mstk_len := hmstk'
    min_inv := fullMinMarkInv_with_mstk h.min_inv mstk' }

private theorem minLitStInv_mark {c : FullCfg} {s : FullState} {keepSet : List Nat}
    {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64}
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hsi : MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1)
    {v : Nat} (hv : v < s.core.cur_vars) (hz : mrk1[v]?.getD 0#8 = 0#8) (tag : BitVec 8)
    (htag : tag = 2#8 ∨ tag = 4#8)
    (hmin' : FullMinMarkInv
      (fullMinMarkCore (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core v tag) keepSet) :
    let k_p := (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core
    let k' := fullMinMarkCore k_p v tag
    MinLitStInv c s keepSet k'.mrk mstk1 k'.min_clr k'.min_clr_len k'.min_clr_full ∧
    (∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (k'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  intro k_p k'
  have hv_max : v < c.max_vars := by omega
  have hmono_prev : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (k'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
    intro w _ hw2; dsimp only [k', fullMinMarkCore]
    by_cases hweq : w = v
    · subst w; rw [hz] at hw2; exact absurd rfl hw2
    · rwa [List.getElem?_set_ne (Ne.symm hweq)]
  have hbit8' : ∀ w < s.core.cur_vars,
      (k'.mrk[w]?.getD 0#8 &&& 8#8) = (s.core.mrk[w]?.getD 0#8 &&& 8#8) := by
    intro w hw; dsimp only [k', fullMinMarkCore]
    by_cases hweq : w = v
    · subst w
      rw [List.getElem?_set_self (by rw [hsi.mrk_len]; exact hv_max), Option.getD_some]
      have hz' : k_p.mrk[v]?.getD 0#8 = 0#8 := hz
      rw [hz', ← hsi.bit8 v hv, hz']
      rcases htag with rfl | rfl <;> decide
    · rw [List.getElem?_set_ne (Ne.symm hweq)]; exact hsi.bit8 w hw
  have hab' : ∀ w, s.core.cur_vars ≤ w → k'.mrk[w]? = s.core.mrk[w]? := fun w hw => by
    dsimp only [k', fullMinMarkCore]
    rw [List.getElem?_set_ne (by omega)]; exact hsi.mrk_above w hw
  have hmclr' : k'.min_clr.length = c.max_vars := by
    dsimp only [k', k_p, fullMinMarkCore]; split <;> simp [hsi.mclr_len]
  have hmcl' : k'.min_clr_len ≤ c.max_vars := by
    have hmcl_le := hsi.mcl_le; dsimp only [k', k_p, fullMinMarkCore]; split <;> omega
  have hmrk' : k'.mrk.length = c.max_vars := by
    dsimp only [k', k_p, fullMinMarkCore]; rw [List.length_set]; exact hsi.mrk_len
  refine ⟨⟨hmrk', hsi.mstk_len, hmclr', hmcl', hab', hmin',
    fun w hw hws => hmono_prev w hw (hsi.mono2 w hw hws), hbit8'⟩, hmono_prev⟩

private theorem fullMinMarkSpec_zero_inv {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64} {m1 : Mem 64} {Q' : Post []} {X' : XPost}
    (hcore : FullCoreInv c F0 s) (hmrk : mrk1.length = c.max_vars)
    (hmstk : mstk1.length = 2 * c.minDepth) (hmclr : mclr1.length = c.max_vars)
    (hmcl : mcl1 ≤ c.max_vars)
    (hm1 : (FullMem c (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) ⋆ R) m1)
    {v : BitVec 32} (hv : v.toNat < s.core.cur_vars) (hz : mrk1[v.toNat]?.getD 0#8 = 0#8)
    (tag : BitVec 8)
    (hpost : ∀ m',
      let k1 := (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core
      let k2 := fullMinMarkCore k1 v.toNat tag
      (FullMem c (minLitState s k2.mrk mstk1 k2.min_clr k2.min_clr_len k2.min_clr_full) ⋆ R)
        m' → Q' () m') :
    fullMinMarkSpec (c.hdr, v, tag, ()) m1 Q' X' := by
  let st1 := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
  have hlen1 : st1.LengthsOk c :=
    (fullCoreInv_with_min hcore hmrk hmstk hmclr hmcl).lengths
  refine ⟨c, st1, R, rfl, hlen1, hm1, ?_⟩
  dsimp only
  have hc1 : ¬ (st1.core.cur_vars ≤ v.toNat ∨ (st1.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8) :=
    fun h => h.elim (fun hle => by dsimp only [st1, minLitState] at hle; omega) fun hne => by
      change (mrk1[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8 at hne; rw [hz] at hne; simp at hne
  have hc2 : ¬ (st1.core.mrk[v.toNat]?.getD 0#8 ≠ 0#8) := fun h => h hz
  simp only [eq_false hc1, eq_false hc2, ↓reduceIte]
  have hzor : (0#8 : BitVec 8) ||| tag = tag := BitVec.zero_or
  by_cases hlt : mcl1 < s.core.cur_vars
  · have hlt' : st1.core.min_clr_len < st1.core.cur_vars := hlt
    simp only [eq_true hlt', ↓reduceIte]
    intro m' hm'
    have hp := hpost m'
    dsimp only [fullMinMarkCore, minLitState] at hp ⊢
    have hmcl1' : mcl1 < s.core.cur_vars := hlt
    simp only [hz, hmcl1', and_self, not_true_eq_false, and_false, ↓reduceIte, hzor] at hp
    have hv_eq : BitVec.ofNat 32 v.toNat = v := bv_ofNat_toNat_eq v
    dsimp only [st1, minLitState] at hm'
    rw [hz, hzor] at hm'; rw [hv_eq] at hp; exact hp hm'
  · have hlt' : ¬ st1.core.min_clr_len < st1.core.cur_vars := hlt
    simp only [eq_false hlt', ↓reduceIte]
    intro m' hm'
    have hp := hpost m'
    dsimp only [fullMinMarkCore, minLitState] at hp ⊢
    have hmcl1' : ¬ mcl1 < s.core.cur_vars := hlt
    simp only [hz, hmcl1', and_self, and_false, not_false_eq_true, ↓reduceIte, hzor] at hp
    dsimp only [st1, minLitState] at hm'
    rw [hz, hzor] at hm'; exact hp hm'

private theorem minLit_maxSteps_toNat {c : FullCfg} {s : FullState}
    (hle : s.core.arena_len ≤ c.arena_cap) (hcv : s.core.cur_vars ≤ c.max_vars) :
    ((BitVec.ofNat 64 s.core.arena_len + BitVec.ofNat 64 s.core.cur_vars) * 4 + 64).toNat =
      (s.core.arena_len + s.core.cur_vars) * 4 + 64 := by
  have hmx := c.hmaxv; have har := c.harena; unfold dimacsBound at hmx har
  have hbd : (s.core.arena_len + s.core.cur_vars) * 4 + 64 < 2 ^ 64 := by omega
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  have h64 : (64 : BitVec 64).toNat = 64 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4, h64]
  rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : s.core.arena_len + s.core.cur_vars < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (s.core.arena_len + s.core.cur_vars) * 4 < 2 ^ 64),
    Nat.mod_eq_of_lt hbd]

theorem bv8_c0_bit_ne0 {a : BitVec 8} {n : BitVec 32}
    (h : (a.setWidth 32 &&& (n.setWidth 8).setWidth 32 !=
      ((0 : BitVec 32).setWidth 8).setWidth 32) = true) :
    (a &&& n.setWidth 8) ≠ 0#8 := by
  have h0 : ((0 : BitVec 32).setWidth 8).setWidth 32 = (0#32 : BitVec 32) := rfl
  rw [h0] at h; c0_cond h; exact h

theorem bv8_c0_bit_eq0 {a : BitVec 8} {n : BitVec 32}
    (h : (a.setWidth 32 &&& (n.setWidth 8).setWidth 32 !=
      ((0 : BitVec 32).setWidth 8).setWidth 32) = false) :
    (a &&& n.setWidth 8) = 0#8 := by
  have h0 : ((0 : BitVec 32).setWidth 8).setWidth 32 = (0#32 : BitVec 32) := rfl
  rw [h0] at h; c0_cond h; exact h

theorem bv8_c0_and8_eq0 {a : BitVec 8}
    (h : (a.setWidth 32 &&& ((8 : BitVec 32).setWidth 8).setWidth 32 ==
      ((0 : BitVec 32).setWidth 8).setWidth 32) = true) : (a &&& 8#8) = 0#8 := by
  have h0 : ((0 : BitVec 32).setWidth 8).setWidth 32 = (0#32 : BitVec 32) := rfl
  have h8 : ((8 : BitVec 32).setWidth 8).setWidth 32 = (8#8).setWidth 32 := rfl
  rw [h0, h8] at h; c0_cond h; exact h

theorem bv8_c0_and8_ne0 {a : BitVec 8}
    (h : (a.setWidth 32 &&& ((8 : BitVec 32).setWidth 8).setWidth 32 ==
      ((0 : BitVec 32).setWidth 8).setWidth 32) = false) : (a &&& 8#8) ≠ 0#8 := by
  have h0 : ((0 : BitVec 32).setWidth 8).setWidth 32 = (0#32 : BitVec 32) := rfl
  have h8 : ((8 : BitVec 32).setWidth 8).setWidth 32 = (8#8).setWidth 32 := rfl
  rw [h0, h8] at h; c0_cond h; exact h

theorem shrink_arena_lits_mem {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {cref pos : Nat} (href : cref ∈ fullArenaClauseRefsCore s.core)
    (hp : pos < fullArenaClauseSizeCore s.core cref) :
    (s.core.arena[cref + 3 + pos]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s.core cref := by
  obtain ⟨_, hw⟩ := hcore.witness
  have hwf := hw.arena.refs_wf cref href
  have hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
    have := hwf.2.2.1; have := hwf.2.2.2.1
    have := hcore.lengths.core_ok.arena_len_le; have := hcore.lengths.core_ok.arena_len_arr; omega
  rw [mem_fullArenaClauseLitsCore_iff hbd]
  exact ⟨pos, hp, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩

theorem shrink_rsn_loop_done {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mrk : List (BitVec 8)} {idx : Nat}
    (hi : idx < s.core.trail_end)
    (hrs : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
      0xFFFFFFFF#32)
    (hcov :
      let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      let is_bin := (rsn &&& 0x80000000#32) ≠ 0#32
      let csz := if is_bin then 1 else fullArenaClauseSizeCore s.core rsn.toNat
      ∀ j < csz,
        let q := if is_bin then (rsn &&& 0x7FFFFFFF#32).toNat
                 else (s.core.arena[rsn.toNat + 3 + j]?.getD 0#32).toNat
        q = (s.core.trl[idx]?.getD 0#32).toNat ∨ ∃ m < idx,
          (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
          ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
            (mrk[q / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)) :
    ShrinkResolved s.core mrk idx := by
  obtain ⟨_, hw⟩ := hcore.witness
  have hr := hw.reason_inv idx hi hrs
  dsimp only [ShrinkResolved, RsnCov] at hr hcov ⊢
  refine ⟨hrs, ?_⟩
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hr hcov ⊢
    refine ⟨hr.1, ?_⟩
    rcases hcov 0 (by omega) with heq | hex
    · exfalso; obtain ⟨m, hm, hmeq, _⟩ := hr.2.2
      have hln := litVar_litNeg (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat
      unfold litVar litNeg at hln
      have hmi := hw.trail_vars_nodup m idx (by omega) hi (by rw [hmeq, hln, heq]); omega
    · exact hex
  · simp only [eq_false hbin, ↓reduceIte] at hr hcov ⊢
    refine ⟨hr.1, hr.2.1, fun q hq => ?_⟩
    have hwf := hw.arena.refs_wf _ hr.1
    have hbd : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat + 3 +
        fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32).toNat ≤ s.core.arena.length := by
      have := hwf.2.2.1; have := hwf.2.2.2.1
      have := hcore.lengths.core_ok.arena_len_le; have := hcore.lengths.core_ok.arena_len_arr; omega
    obtain ⟨j, hj, hjeq⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hq
    have hqj := hcov j hj
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, hjeq] at hqj

/-! ## 2. Exported `full_min_lit_wp` -/

theorem full_min_lit_wp (Γ : Env)
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X) :
    ∀ args m Q X, fullMinLitSpec args m Q X →
      Func.wp Γ full_min_lit_body args m Q X := by
  rintro ⟨h, root_lit, ⟨⟩⟩ m Q X
    ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hrl, hval, hno8, hm, hQ⟩
  unfold Func.wp full_min_lit_body; dsimp only [full_min_lit_body]
  have hlen0 := hcore.lengths.core_ok
  have hmx := c.hmaxv; have har := c.harena; unfold dimacsBound at hmx har
  have hcv := hlen0.cur_vars_le
  ml_ld load_full_cur_vars hm
  ml_lets; ml_jnz; refine ⟨fun hge => ?_, fun _ => ?_⟩
  · exfalso; c0_cond hge; bv_omega
  · ml_ld load_full_min_depth hm
    ml_lets; ml_jnz; refine ⟨fun hz => ?_, fun _ => ?_⟩
    · exfalso; c0_cond hz; have := fullMinDepthOf_pos c.max_vars
      have := fullMinDepthOf_le c.max_vars; unfold FullCfg.minDepth at *; bv_omega
    · ml_ld load_full_reason_ptr hm
      ml_ld c0_load_full_rsns (i := (root_lit >>> 1).setWidth 64)
        (by rw [hlen0.rsns_len]; bv_omega) hm
      ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hrsn_some => ?_⟩
      · ml_lets; rw [wp]
        exact hQ false s.core.mrk s.core.min_stk s.core.min_clr s.core.min_clr_len
          s.core.min_clr_full m hcore.lengths (fun _ _ => rfl) (fun _ _ h => h)
          (fun _ _ => rfl) hmin (fun hc => by cases hc) hm
      · ml_ld load_full_mark_ptr hm
        ml_ld load_full_level_ptr hm
        ml_ld load_full_arena_ptr hm
        ml_ld load_full_min_stk_ptr hm
        have hmd_pos := fullMinDepthOf_pos c.max_vars
        have hmstkl := hlen0.min_stk_len
        ml_lets; rw [wp]
        obtain ⟨hok0, hm0⟩ := store_full_min_stk (i := 0) (root_lit >>> 1)
          (by unfold FullCfg.minDepth at *; omega) hm
        refine ⟨by simpa using hok0, ?_⟩
        ml_lets; rw [wp]
        obtain ⟨hok1, hm1⟩ := store_full_min_stk (i := 1) 0#32
          (by simp [hmstkl]; unfold FullCfg.minDepth at *; omega) hm0
        refine ⟨by simpa using hok1, ?_⟩
        ml_ld load_full_arena_len hm1
        ml_lets
        obtain ⟨F_cur0, hw0⟩ := hcore.witness
        obtain ⟨idx0, hi0, hi0_eq⟩ := (hw0.vals_false_iff root_lit.toNat hrl).mp hval
        have hrv_root : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2 := by
          have hl := litVar_litNeg root_lit.toNat; unfold litVar litNeg at hl; rw [hi0_eq, hl]
        have hrsn_ne0 : s.core.rsns[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
            0xFFFFFFFF#32 := by
          have hrl_lt : (root_lit >>> 1).toNat < s.core.rsns.length := by
            rw [hlen0.rsns_len]; bv_omega
          rw [hrv_root, ← bv32_lshr_1, List.getElem?_eq_getElem hrl_lt, Option.getD_some]
          intro heq; c0_cond hrsn_some
          apply hrsn_some; simp only [← bv32_lshr_1]; exact heq.trans rfl
        let maxSteps := (s.core.arena_len + s.core.cur_vars) * 4 + 64
        let BrkPost : Tup Val [i64, .bool, i64] → Mem 64 → Prop :=
          fun (sp, ok, _steps, ()) m' =>
            ∃ mrk1 mstk1 mclr1 mcl1 mcf1,
              let st := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
              MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1 ∧
              (FullMem c st ⋆ R) m' ∧
              if ok then
                ∃ idx0_w < s.core.trail_end,
                  (s.core.trl[idx0_w]?.getD 0#32).toNat = root_lit.toNat ^^^ 1 ∧
                  ∃ lim,
                    (if (s.core.rsns[(s.core.trl[idx0_w]?.getD 0#32).toNat / 2]?.getD
                        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1
                     else fullArenaClauseSizeCore s.core
                       (s.core.rsns[(s.core.trl[idx0_w]?.getD 0#32).toNat / 2]?.getD
                         0xFFFFFFFF#32).toNat) ≤ lim ∧
                    FrameCov s.core mrk1 idx0_w lim
              else
                sp.toNat < c.minDepth ∧
                ∃ idxs, MinLitStkInv s.core mstk1 mrk1 sp.toNat idx0 idxs false
        let LpInv : Nat → Tup Val [i64, i64] → Mem 64 → Prop :=
          fun n (sp, steps, ()) m' =>
            sp.toNat < c.minDepth ∧ steps.toNat ≤ maxSteps ∧ n = maxSteps - steps.toNat ∧
            ∃ mrk1 mstk1 mclr1 mcl1 mcf1 idxs,
              let st := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
              MinLitStInv c s keepSet mrk1 mstk1 mclr1 mcl1 mcf1 ∧
              (FullMem c st ⋆ R) m' ∧
              MinLitStkInv s.core mstk1 mrk1 sp.toNat idx0 idxs true
        refine wp_loop_break_group (brkTs := [i64, .bool, i64]) (lpTs := [i64, i64])
          BrkPost LpInv ?_ ?_ ?_
        · rintro B ⟨sp, ok, steps, ⟨⟩⟩ m' ⟨mrk1, mstk1, mclr1, mcl1, mcf1, hsi, hm', hrest⟩
          rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hok => ?_, fun hnok => ?_⟩
          · ml_lets; rw [wp]
            rw [hok] at hrest; simp only [↓reduceIte] at hrest
            obtain ⟨idx0_w, hi0_w, hroot_w, lim, hlim_w, hcov_w⟩ := hrest
            have hcore1 := hsi.core hcore
            have hh := frameCov_to_hrsn hcore hcov_w hlim_w
            have hrv_w : (s.core.trl[idx0_w]?.getD 0#32).toNat / 2 = root_lit.toNat / 2 := by
              have hl := litVar_litNeg root_lit.toNat; unfold litVar litNeg at hl
              rw [hroot_w, hl]
            refine hQ true mrk1 mstk1 mclr1 mcl1 mcf1 m' hcore1.lengths hsi.mrk_above hsi.mono2
              hsi.bit8 hsi.min_inv (fun _ => ⟨fun keep' hsub => ?_, ?_⟩) hm'
            · refine fullMinMarkInv_drop hcore1 hsi.min_inv hsub hi0_w hroot_w ?_
              simp only [hroot_w] at hh; exact hh
            · have hno8_w :
                  (mrk1[(s.core.trl[idx0_w]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8 := by
                rw [hrv_w, hsi.bit8 _ (by omega)]; exact hno8 _ (by omega) (le_refl _)
              have hmrk := fullMinMarkInv_mark_rem hcore1 hsi.min_inv hi0_w hno8_w hh
              simpa only [hrv_w] using hmrk
          · rw [hnok] at hrest; simp only [Bool.false_eq_true, ↓reduceIte] at hrest
            obtain ⟨hsp_lt, idxs, hstk⟩ := hrest
            ml_lets
            let AfterInv : Nat → Tup Val [i64] → Mem 64 → Prop :=
              fun n' (j, ()) m2 =>
                1 ≤ j.toNat ∧ j.toNat ≤ sp.toNat + 1 ∧ n' = sp.toNat + 1 - j.toNat ∧
                ∃ mrk2 mclr2 mcl2 mcf2,
                  let st2 := minLitState s mrk2 mstk1 mclr2 mcl2 mcf2
                  MinLitStInv c s keepSet mrk2 mstk1 mclr2 mcl2 mcf2 ∧
                  (FullMem c st2 ⋆ R) m2 ∧
                  ∀ k (hk : k < idxs.length), j.toNat ≤ k →
                    mrk2[(s.core.trl[idxs[k]]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
            refine wp_loop_group (ts := [i64]) AfterInv ?_ ?_
            · rintro J n' ⟨j, ⟨⟩⟩ m2 hJ ⟨hj1, hj_le, rfl,
                mrk2, mclr2, mcl2, mcf2, hsi2, hm2, hzero2⟩
              rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hj_ule => ?_, fun _ => ?_⟩
              · have hj_le_sp : j.toNat ≤ sp.toNat := by c0_cond hj_ule; bv_omega
                have hj_idxs : j.toNat < idxs.length := by rw [hstk.len]; omega
                have hmd_le : c.minDepth ≤ 1000 := fullMinDepthOf_le c.max_vars
                have hj_stk : (j <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
                    mstk1.length := by rw [bv64_shl1_toNat (by omega), hsi2.mstk_len]; omega
                ml_ld c0_load_full_min_stk (s := minLitState s mrk2 mstk1 mclr2 mcl2 mcf2)
                  (i := j <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) hj_stk hm2
                ml_lets
                let v_bv := mstk1[(j <<<
                  ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat]'hj_stk
                have hv_nat : v_bv.toNat =
                    (s.core.trl[idxs[j.toNat]'hj_idxs]?.getD 0#32).toNat / 2 := by
                  have hsh := bv64_shl1_toNat (x := j) (by omega)
                  have hslot := (hstk.slot j.toNat hj_idxs).1
                  rw [List.getElem?_eq_getElem (by rw [hsi2.mstk_len]; omega), Option.getD_some]
                    at hslot
                  dsimp only [v_bv]; simp only [hsh]; exact hslot
                have hv_lt : v_bv.toNat < s.core.cur_vars := by
                  rw [hv_nat]; have := hw0.trail_lits_lt _ (hstk.bd j.toNat hj_idxs); omega
                have hz_bv : mrk2[v_bv.toNat]?.getD 0#8 = 0#8 := by
                  rw [hv_nat]; exact hzero2 j.toNat hj_idxs (le_refl _)
                apply wp_call_of_spec; apply hMm
                refine fullMinMarkSpec_zero_inv hcore hsi2.mrk_len hsi2.mstk_len hsi2.mclr_len
                  hsi2.mcl_le hm2 hv_lt hz_bv ((4 : BitVec 32).setWidth 8) fun m3 hm3 => ?_
                ml_lets; rw [wp]
                let st2 := minLitState s mrk2 mstk1 mclr2 mcl2 mcf2
                let k3 := fullMinMarkCore st2.core v_bv.toNat 4#8
                have h4_eq : (4 : BitVec 32).setWidth 8 = 4#8 := rfl
                rw [h4_eq] at hm3
                have hcore2 := hsi2.core hcore
                have hno8_v : (st2.core.mrk[v_bv.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
                  have hz2 : st2.core.mrk[v_bv.toNat]?.getD 0#8 = 0#8 := hz_bv
                  rw [hz2]; rfl
                have hmin3 := fullMinMarkInv_poison hcore2 hsi2.min_inv hv_lt hno8_v
                obtain ⟨hsi3, _⟩ := minLitStInv_mark hcv hsi2 hv_lt hz_bv 4#8 (Or.inr rfl) hmin3
                have hj1_nat : (j + 1).toNat = j.toNat + 1 := min_bv64_add1 (by omega)
                refine hJ (sp.toNat + 1 - (j + 1).toNat) (j + 1, ()) m3 (by omega)
                  ⟨by omega, by omega, rfl,
                    k3.mrk, k3.min_clr, k3.min_clr_len, k3.min_clr_full,
                    hsi3, hm3, fun k hk hjk => ?_⟩
                have hne_k : (s.core.trl[idxs[k]]?.getD 0#32).toNat / 2 ≠ v_bv.toNat := by
                  rw [hv_nat]; exact minLitStkInv_var_ne hcore hstk hk hj_idxs (by omega)
                dsimp only [k3, fullMinMarkCore]
                rw [List.getElem?_set_ne (Ne.symm hne_k)]
                exact hzero2 k hk (by omega)
              · ml_lets; rw [wp]
                have hcore2 := hsi2.core hcore
                exact hQ false mrk2 mstk1 mclr2 mcl2 mcf2 m2 hcore2.lengths hsi2.mrk_above
                  hsi2.mono2 hsi2.bit8 hsi2.min_inv (fun hc => by cases hc) hm2
            · intro J hJ; wp_unfold
              exact hJ sp.toNat (1#64, ()) m' ⟨le_refl _, Nat.succ_le_of_lt (by omega), rfl,
                mrk1, mclr1, mcl1, mcf1, hsi, hm', fun k hk hk1 => (hstk.slot k hk).2 hk1⟩
        · rintro B L n ⟨sp, steps, ⟨⟩⟩ m' hB hL
            ⟨hsp_lt, hsteps_le, rfl, mrk1, mstk1, mclr1, mcl1, mcf1, idxs, hsi, hm', hstk⟩
          rw [Blocks.get_here]; ml_lets; ml_jnz; refine ⟨fun hlt_st => ?_, fun _ => ?_⟩
          · have hms_eq := minLit_maxSteps_toNat hlen0.arena_len_le hcv
            rw [BitVec.ult, decide_eq_true_eq] at hlt_st
            dsimp only [maxSteps] at hms_eq hlt_st
            rw [hms_eq] at hlt_st
            have hsteps1 : (steps + 1).toNat = steps.toNat + 1 := min_bv64_add1 (by omega)
            have hdec_n : maxSteps - (steps + 1).toNat < maxSteps - steps.toNat := by omega
            have hmd_le : c.minDepth ≤ 1000 := fullMinDepthOf_le c.max_vars
            have hstk_ev :
                (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
                  mstk1.length := by rw [bv64_shl1_toNat (by omega), hsi.mstk_len]; omega
            have hstk_od :
                (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat <
                  mstk1.length := by rw [bv64_shl1_add1_toNat (by omega), hsi.mstk_len]; omega
            have hsp_idxs : sp.toNat < idxs.length := by rw [hstk.len]; omega
            ml_ld c0_load_full_min_stk (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
              (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) hstk_ev hm'
            ml_ld c0_load_full_min_stk (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
              (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1) hstk_od hm'
            let v := mstk1[(sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat]'
              hstk_ev
            let pos := mstk1[(sp <<<
              ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat]'hstk_od
            have hv_nat : v.toNat =
                (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
              have hslot := (hstk.slot sp.toNat hsp_idxs).1
              rw [List.getElem?_eq_getElem (by rw [hsi.mstk_len]; omega), Option.getD_some] at hslot
              dsimp only [v]; simp only [bv64_shl1_toNat (x := sp) (by omega)]; exact hslot
            have hv_lt : v.toNat < s.core.cur_vars := by
              rw [hv_nat]; have := hw0.trail_lits_lt _ (hstk.bd sp.toNat hsp_idxs); omega
            have hpos_nat : pos.toNat = (mstk1[2 * sp.toNat + 1]?.getD 0#32).toNat := by
              dsimp only [pos]; simp only [bv64_shl1_add1_toNat (x := sp) (by omega)]
              rw [List.getElem?_eq_getElem (by rw [hsi.mstk_len]; omega), Option.getD_some]
            ml_lets; ml_jnz; refine ⟨fun hv_ge => ?_, fun _ => ?_⟩
            · exfalso
              change (BitVec.ofNat 64 s.core.cur_vars).ule (v.setWidth 64) = true at hv_ge
              c0_cond hv_ge; bv_omega
            · have hv_rsns : (v.setWidth 64).toNat <
                  (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core.rsns.length := by
                dsimp only [minLitState]; rw [hlen0.rsns_len]; bv_omega
              ml_ld c0_load_full_rsns (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
                (i := v.setWidth 64) hv_rsns hm'
              let rsn := s.core.rsns[(v.setWidth 64).toNat]'hv_rsns
              have hrsn_eq : rsn = s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
                  0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
                have hvl : v.toNat < s.core.rsns.length := by rw [hlen0.rsns_len]; omega
                have hvw : (v.setWidth 64).toNat = v.toNat := bv_c0_zext32_64 v
                dsimp only [rsn]
                rw [List.getElem?_eq_getElem (by rw [← hv_nat]; exact hvl), Option.getD_some]
                congr 1
              have hcov_sp : FrameCov s.core mrk1 (idxs[sp.toNat]'hsp_idxs) pos.toNat := by
                have hc := (hstk.cov rfl sp.toNat hsp_idxs).2
                have htop_eq : sp.toNat + 1 = idxs.length := by rw [hstk.len]
                simpa only [htop_eq, ↓reduceIte, ← hpos_nat] using hc
              ml_lets; ml_jnz; refine ⟨fun hrsn_none => ?_, fun _ => ?_⟩
              · exfalso; change (rsn == 0xFFFFFFFF#32) = true at hrsn_none
                c0_cond hrsn_none; exact hcov_sp.1 (by rwa [← hrsn_eq])
              · ml_lets
                let SzPost : Tup Val [i32] → Mem 64 → Prop := fun (sz, ()) m2 =>
                  m2 = m' ∧
                  sz.toNat = (if (rsn &&& 0x80000000#32) ≠ 0#32 then 1
                    else fullArenaClauseSizeCore s.core rsn.toNat) ∧ 1 ≤ sz.toNat
                refine wp_join_group (ts := [i32]) SzPost ?_ ?_
                · rintro Jsz ⟨sz, ⟨⟩⟩ m2 ⟨hm2_eq, hsz_eq, _⟩
                  subst m2
                  rw [Blocks.get_here]; ml_lets; ml_jnz
                  refine ⟨fun hpos_lt => ?_, fun hpos_ge => ?_⟩
                  · change pos.ult sz = true at hpos_lt
                    rw [BitVec.ult, decide_eq_true_eq] at hpos_lt
                    have hpos_add1 : (pos + 1).toNat = pos.toNat + 1 :=
                      bv32_add1_toNat (by have := sz.isLt; omega)
                    ml_lets; rw [wp]
                    obtain ⟨hok_p, hm_p⟩ := c0_store_full_min_stk
                      (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
                      (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1)
                      (pos + 1) hstk_od hm'
                    refine ⟨hok_p, ?_⟩
                    let mstk2 := mstk1.set (2 * sp.toNat + 1) (pos + 1)
                    let m_p := storeMem m' i32 (c.pMinStk +
                      (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1) *
                        (4 : BitVec 64)) (pos + 1)
                    have hm_p' :
                        (FullMem c (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1) ⋆ R) m_p := by
                      rw [bv64_shl1_add1_toNat (x := sp) (by omega)] at hm_p; exact hm_p
                    have hmstk2_len : mstk2.length = 2 * c.minDepth := by
                      simp [mstk2, hsi.mstk_len]
                    have hsi_p := minLitStInv_with_mstk hsi hmstk2_len
                    have hstk2_drop : MinLitStkInv s.core mstk2 mrk1 sp.toNat idx0 idxs false := by
                      refine ⟨hstk.len, hstk.idx0_eq, hstk.bd, hstk.dec, hstk.lvl_le_root,
                        fun k hk => ?_, fun hc => by cases hc⟩
                      dsimp only [mstk2]; rw [List.getElem?_set_ne (by omega)]
                      exact hstk.slot k hk
                    ml_lets
                    let LitPost : Tup Val [i32] → Mem 64 → Prop := fun (lit, ()) m3 =>
                      m3 = m_p ∧ lit.toNat = minLitRsnLit s.core rsn pos.toNat
                    refine wp_join_group (ts := [i32]) LitPost ?_ ?_
                    · rintro Jl ⟨lit, ⟨⟩⟩ m3 ⟨rfl, hlit_eq⟩
                      rw [Blocks.get_here]; ml_lets
                      have hcore_p := hsi_p.core hcore
                      have hcov_sz : pos.toNat < if (s.core.rsns[(s.core.trl[idxs[sp.toNat]'
                          hsp_idxs]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
                          0x80000000#32) ≠ 0#32 then 1 else fullArenaClauseSizeCore s.core
                            (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat /
                              2]?.getD 0xFFFFFFFF#32).toNat := by
                        rw [← hrsn_eq, ← hsz_eq]; exact hpos_lt
                      have hu_bd_lt : (lit >>> 1).toNat < s.core.cur_vars := by
                        dsimp only [FrameCov] at hcov_sp
                        rcases hcov_sp with ⟨_, hif⟩
                        rw [bv32_lshr_1, hlit_eq]; dsimp only [minLitRsnLit]
                        by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
                        · simp only [← hrsn_eq, eq_true hbin, ↓reduceIte] at hif ⊢; omega
                        · simp only [← hrsn_eq, eq_false hbin, ↓reduceIte] at hif hsz_eq ⊢
                          have hpos_ac : pos.toNat < fullArenaClauseSizeCore s.core rsn.toNat := by
                            omega
                          have hmem := frameCov_arena_lits_mem hcore hif.1 hpos_ac
                          have hllt := hw0.arena.lits_lt _ hif.1 hif.2.1 _ hmem; omega
                      ml_jnz; refine ⟨fun hu_ge => ?_, fun _ => ?_⟩
                      · exfalso; c0_cond hu_ge; bv_omega
                      · ml_lets; ml_jnz; refine ⟨fun huv => ?_, fun huv_ne => ?_⟩
                        · c0_cond huv
                          refine hL (maxSteps - (steps + 1).toNat) (sp, steps + 1, ()) _ hdec_n
                            ⟨hsp_lt, by omega, rfl, mrk1, mstk2, mclr1, mcl1, mcf1, idxs,
                              hsi_p, hm_p', ?_⟩
                          refine minLitStkInv_step_top (c := c) hstk hsi.mstk_len hsp_lt (pos + 1)
                            fun _ => ?_
                          rw [hpos_add1]
                          refine frameCov_step hcore (hstk.bd sp.toNat hsp_idxs) hcov_sp hcov_sz
                            (Or.inl ?_)
                          rw [← hrsn_eq, ← hlit_eq, ← hv_nat, ← bv32_lshr_1, huv]
                        · have hu_ne_v : minLitRsnLit s.core
                              (s.core.rsns[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat /
                                2]?.getD 0xFFFFFFFF#32) pos.toNat / 2 ≠
                              (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
                            rw [← hrsn_eq, ← hlit_eq, ← hv_nat, ← bv32_lshr_1]
                            c0_cond huv_ne
                            intro heq; apply huv_ne; exact BitVec.eq_of_toNat_eq heq
                          obtain ⟨_, u_idx, hu_idx_lt, hu_idx_eq, hu_lvl_le⟩ := frameCov_edge_exists
                            hcore (hstk.bd sp.toNat hsp_idxs) hcov_sp hcov_sz hu_ne_v
                          have hu_lvl_len : ((lit >>> 1).setWidth 64).toNat <
                              (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).core.lvl.length := by
                            dsimp only [minLitState]; rw [hlen0.lvl_len]; bv_omega
                          ml_ld c0_load_full_lvl
                            (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                            (i := (lit >>> 1).setWidth 64) hu_lvl_len hm_p'
                          ml_lets; ml_jnz; refine ⟨fun hlvl0 => ?_, fun _ => ?_⟩
                          · c0_cond hlvl0
                            refine hL (maxSteps - (steps + 1).toNat) (sp, steps + 1, ()) _ hdec_n
                              ⟨hsp_lt, by omega, rfl, mrk1, mstk2, mclr1, mcl1, mcf1, idxs,
                                hsi_p, hm_p', ?_⟩
                            refine minLitStkInv_step_top (c := c) hstk hsi.mstk_len hsp_lt (pos + 1)
                              fun _ => ?_
                            rw [hpos_add1]
                            refine frameCov_step hcore (hstk.bd sp.toNat hsp_idxs) hcov_sp hcov_sz
                              (Or.inr ⟨u_idx, hu_idx_lt, hu_idx_eq, Or.inl ?_⟩)
                            rw [← hrsn_eq, ← hlit_eq]
                            have hlw : lit.toNat / 2 < s.core.lvl.length := by
                              rw [hlen0.lvl_len, ← bv32_lshr_1]; omega
                            rw [List.getElem?_eq_getElem hlw, Option.getD_some, hlvl0]; rfl
                          · have hu_mrk_len : ((lit >>> 1).setWidth 64).toNat <
                                (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).core.mrk.length := by
                              dsimp only [minLitState]; rw [hsi.mrk_len]; bv_omega
                            ml_ld c0_load_full_mrk
                              (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                              (i := (lit >>> 1).setWidth 64) hu_mrk_len hm_p'
                            let mu := mrk1[((lit >>> 1).setWidth 64).toNat]'hu_mrk_len
                            have hmu_eq : mu = mrk1[(lit >>> 1).toNat]?.getD 0#8 := by
                              have hvw := bv_c0_zext32_64 (lit >>> 1)
                              dsimp only [mu]
                              rw [List.getElem?_eq_getElem (by rw [hsi.mrk_len]; omega),
                                Option.getD_some]
                              congr 1
                            ml_lets; ml_jnz; refine ⟨fun hmu2 => ?_, fun hmu_n2 => ?_⟩
                            · have hmu_is2 : (mu &&& 2#8) ≠ 0#8 := bv8_c0_bit_ne0 hmu2
                              refine hL (maxSteps - (steps + 1).toNat) (sp, steps + 1, ()) _ hdec_n
                                ⟨hsp_lt, by omega, rfl, mrk1, mstk2, mclr1, mcl1, mcf1, idxs,
                                  hsi_p, hm_p', ?_⟩
                              refine minLitStkInv_step_top (c := c) hstk hsi.mstk_len hsp_lt
                                (pos + 1) fun _ => ?_
                              rw [hpos_add1]
                              refine frameCov_step hcore (hstk.bd sp.toNat hsp_idxs) hcov_sp hcov_sz
                                (Or.inr ⟨u_idx, hu_idx_lt, hu_idx_eq, Or.inr ?_⟩)
                              rw [← hrsn_eq, ← hlit_eq, ← bv32_lshr_1, ← hmu_eq]; exact hmu_is2
                            · ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hmu_n4 => ?_⟩
                              · ml_lets; apply hB
                                exact ⟨mrk1, mstk2, mclr1, mcl1, mcf1, hsi_p, hm_p',
                                  ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                              · have hu_nat_idx : (lit >>> 1).toNat =
                                    (s.core.trl[u_idx]?.getD 0#32).toNat / 2 := by
                                  have hl := litVar_litNeg (minLitRsnLit s.core rsn pos.toNat)
                                  unfold litVar litNeg at hl
                                  have hu_idx_eq' := hu_idx_eq; rw [← hrsn_eq] at hu_idx_eq'
                                  rw [bv32_lshr_1, hlit_eq, ← hl, ← hu_idx_eq']
                                have hu_lvl_root : (s.core.lvl[(s.core.trl[u_idx]?.getD
                                      0#32).toNat / 2]?.getD 0#32).toNat ≤
                                    (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD
                                      0#32).toNat := by
                                  have h1 : (s.core.trl[u_idx]?.getD 0#32).toNat / 2 =
                                      minLitRsnLit s.core (s.core.rsns[(s.core.trl[idxs[sp.toNat]'
                                        hsp_idxs]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
                                        pos.toNat / 2 := by
                                    rw [← hu_nat_idx, bv32_lshr_1, hlit_eq, ← hrsn_eq]
                                  rw [h1]
                                  exact Nat.le_trans hu_lvl_le (hstk.lvl_le_root sp.toNat hsp_idxs)
                                have hno8_u :
                                    (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
                                  rw [hsi.bit8 _ hu_bd_lt]
                                  refine hno8 _ hu_bd_lt ?_
                                  rw [hu_nat_idx, ← hrv_root]; exact hu_lvl_root
                                have hmu0 : mu = 0#8 := by
                                  have h2z : (mu &&& 2#8) = 0#8 := bv8_c0_bit_eq0 hmu_n2
                                  have h4z : (mu &&& 4#8) = 0#8 := bv8_c0_bit_eq0 hmu_n4
                                  have hdom := hsi.min_inv.mrk_dom (lit >>> 1).toNat hu_bd_lt
                                  rw [← hmu_eq] at hdom hno8_u
                                  exact bv8_zero_of_masks24 mu hdom hno8_u h2z h4z
                                have hu_rsns_len : ((lit >>> 1).setWidth 64).toNat <
                                    (minLitState s mrk1 mstk2 mclr1 mcl1
                                      mcf1).core.rsns.length := by
                                  dsimp only [minLitState]; rw [hlen0.rsns_len]; bv_omega
                                ml_ld c0_load_full_rsns
                                  (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                                  (i := (lit >>> 1).setWidth 64) hu_rsns_len hm_p'
                                ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hur_some => ?_⟩
                                · ml_lets; apply wp_call_of_spec; apply hMm
                                  have hz_u : mrk1[(lit >>> 1).toNat]?.getD 0#8 = 0#8 := by
                                    rw [← hmu_eq]; exact hmu0
                                  refine fullMinMarkSpec_zero_inv hcore hsi.mrk_len hmstk2_len
                                    hsi.mclr_len hsi.mcl_le hm_p' hu_bd_lt hz_u
                                    ((4 : BitVec 32).setWidth 8) fun m4 hm4 => ?_
                                  ml_lets; apply hB
                                  have h4_eq : (4 : BitVec 32).setWidth 8 = 4#8 := rfl
                                  rw [h4_eq] at hm4
                                  let st_p := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1
                                  let k4 := fullMinMarkCore st_p.core (lit >>> 1).toNat 4#8
                                  have hmin4 : FullMinMarkInv k4 keepSet :=
                                    fullMinMarkInv_poison hcore_p hsi_p.min_inv hu_bd_lt
                                      (by change (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) = 0#8
                                          rw [hz_u]; rfl)
                                  obtain ⟨hsi4, _⟩ := minLitStInv_mark hcv hsi_p hu_bd_lt hz_u 4#8
                                    (Or.inr rfl) hmin4
                                  have hstk4 := minLitStkInv_poison_other hcore hstk2_drop
                                    (u_idx := u_idx) (mclr1 := mclr1) (mcl1 := mcl1) (mcf1 := mcf1)
                                    (fun k hk => by
                                      have := hstk.len
                                      by_cases hksp : k = sp.toNat
                                      · subst hksp; exact hu_idx_lt
                                      · exact Nat.lt_trans hu_idx_lt
                                          (dec_chain_lt hstk.dec (by omega) hk hsp_idxs))
                                    (fun w _ hne => by
                                      dsimp only [fullMinMarkCore]
                                      rw [List.getElem?_set_ne (Ne.symm hne)])
                                  rw [← hu_nat_idx] at hstk4
                                  exact ⟨k4.mrk, mstk2, k4.min_clr, k4.min_clr_len,
                                    k4.min_clr_full, hsi4, hm4, ⟨hsp_lt, idxs, hstk4⟩⟩
                                · ml_ld load_full_min_depth
                                    (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1) hm_p'
                                  ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun hdepth_ok => ?_⟩
                                  · ml_lets; apply hB
                                    exact ⟨mrk1, mstk2, mclr1, mcl1, mcf1, hsi_p, hm_p',
                                      ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                                  · c0_cond hdepth_ok
                                    have hsp1_lt : sp.toNat + 1 < c.minDepth := by bv_omega
                                    have hsp1_nat : (sp + 1).toNat = sp.toNat + 1 :=
                                      min_bv64_add1 (by omega)
                                    have hstk_ev1 :
                                        ((sp + 1) <<< ((BitVec.signExtend 64
                                          (1 : BitVec 32)).toNat % 64)).toNat < mstk2.length := by
                                      rw [bv64_shl1_toNat (x := sp + 1) (by omega), hmstk2_len]
                                      omega
                                    have hstk_od1 :
                                        ((sp + 1) <<< ((BitVec.signExtend 64
                                          (1 : BitVec 32)).toNat % 64) + 1).toNat <
                                          mstk2.length := by
                                      rw [bv64_shl1_add1_toNat (x := sp + 1) (by omega), hmstk2_len]
                                      omega
                                    ml_lets; rw [wp]
                                    obtain ⟨hok_u, hm_u⟩ := c0_store_full_min_stk
                                      (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                                      (i := (sp + 1) <<<
                                        ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64))
                                      (lit >>> 1) hstk_ev1 hm_p'
                                    refine ⟨hok_u, ?_⟩
                                    ml_lets; rw [wp]
                                    let mstk_mid := mstk2.set (2 * (sp.toNat + 1)) (lit >>> 1)
                                    have hm_u' := hm_u
                                    rw [bv64_shl1_toNat (x := sp + 1) (by omega), hsp1_nat] at hm_u'
                                    have hmstk_mid_len : mstk_mid.length = 2 * c.minDepth := by
                                      simp [mstk_mid, hmstk2_len]
                                    obtain ⟨hok_z, hm_z⟩ := c0_store_full_min_stk
                                      (s := minLitState s mrk1 mstk_mid mclr1 mcl1 mcf1)
                                      (i := (sp + 1) <<<
                                        ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1)
                                      (0 : BitVec 32)
                                      (by dsimp only [minLitState]
                                          rw [hmstk_mid_len, ← hmstk2_len]; exact hstk_od1) hm_u'
                                    refine ⟨hok_z, ?_⟩
                                    ml_lets
                                    let mstk3 := ((mstk1.set (2 * sp.toNat + 1) (pos + 1)).set
                                      (2 * (sp.toNat + 1)) (lit >>> 1)).set
                                      (2 * (sp.toNat + 1) + 1) 0#32
                                    have hmstk3_len : mstk3.length = 2 * c.minDepth := by
                                      simp [mstk3, hsi.mstk_len]
                                    have hm_z' := hm_z
                                    rw [bv64_shl1_add1_toNat (x := sp + 1) (by omega), hsp1_nat]
                                      at hm_z'
                                    have hrsn_u_ne : s.core.rsns[(lit >>> 1).toNat]?.getD
                                        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                                      have hvw := bv_c0_zext32_64 (lit >>> 1)
                                      have hrlu : ((lit >>> 1).setWidth 64).toNat <
                                          s.core.rsns.length := by
                                        rw [hlen0.rsns_len, hvw]; omega
                                      rw [← hvw, List.getElem?_eq_getElem hrlu, Option.getD_some]
                                      dsimp only [minLitState] at hur_some
                                      intro heq
                                      have ht : (s.core.rsns[((lit >>> 1).setWidth 64).toNat] ==
                                          (4294967295 : BitVec 32)) = true := beq_iff_eq.mpr heq
                                      rw [ht] at hur_some; cases hur_some
                                    have hz_u : mrk1[(lit >>> 1).toNat]?.getD 0#8 = 0#8 := by
                                      rw [← hmu_eq]; exact hmu0
                                    have hstk3 := minLitStkInv_push hcore hstk hsi.mstk_len hsp1_lt
                                      (u_bv := lit >>> 1) (pos_bv := pos + 1)
                                      (by rw [hpos_add1, hpos_nat]) hu_idx_lt hu_nat_idx hu_lvl_root
                                      (by rwa [← hpos_nat]) hz_u hrsn_u_ne
                                      ⟨hu_idx_lt, by rw [← hpos_nat]; exact hu_idx_eq⟩
                                    exact hL (maxSteps - (steps + 1).toNat) (sp + 1, steps + 1, ())
                                      _ hdec_n ⟨by bv_omega, by omega, rfl, mrk1, mstk3, mclr1,
                                        mcl1, mcf1, idxs ++ [u_idx],
                                        minLitStInv_with_mstk hsi hmstk3_len, hm_z',
                                        by rwa [hsp1_nat]⟩
                    · rintro Jl hJl; ml_lets; ml_jnz; refine ⟨fun hbin => ?_, fun hbig => ?_⟩
                      · ml_lets; apply hJl; refine ⟨rfl, ?_⟩
                        change ((rsn &&& 0x80000000#32) != 0#32) = true at hbin
                        c0_cond hbin; dsimp only [minLitRsnLit]
                        simp only [eq_true hbin, ↓reduceIte, BitVec.toNat_and]
                        simp only [rsn, bv_c0_zext32_64]; rfl
                      · have hbin_f : ¬ (rsn &&& 0x80000000#32) ≠ 0#32 := by
                          change ((rsn &&& 0x80000000#32) != 0#32) = false at hbig
                          c0_cond hbig; intro hne; exact hne hbig
                        dsimp only [FrameCov] at hcov_sp; rcases hcov_sp with ⟨_, hif⟩
                        simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte] at hif hsz_eq
                        have har_bd : (rsn.setWidth 64 + 3 + pos.setWidth 64).toNat <
                            (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).core.arena.length := by
                          have hbd := frameCov_arena_lits_bd hcore hif.1
                          rw [bv64_zext32_add3_add]; dsimp only [minLitState]; omega
                        ml_ld c0_load_full_arena (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                          (i := rsn.setWidth 64 + 3 + pos.setWidth 64) har_bd hm_p'
                        ml_lets; apply hJl; refine ⟨rfl, ?_⟩
                        have har_bd' : rsn.toNat + 3 + pos.toNat < s.core.arena.length := by
                          rw [← bv64_zext32_add3_add]; exact har_bd
                        dsimp only [minLitRsnLit]
                        simp only [eq_false hbin_f, ↓reduceIte, bv64_zext32_add3_add]
                        rw [List.getElem?_eq_getElem har_bd', Option.getD_some]; rfl
                  · have hpos_ge' : sz.toNat ≤ pos.toNat := by
                      change pos.ult sz = false at hpos_ge
                      rw [BitVec.ult, decide_eq_false_iff_not, not_lt] at hpos_ge; exact hpos_ge
                    ml_lets; ml_jnz; refine ⟨fun hsp0 => ?_, fun hsp_pos => ?_⟩
                    · ml_lets; apply hB; c0_cond hsp0
                      have hsp0' : sp.toNat = 0 := congrArg BitVec.toNat hsp0
                      have hi0_eq_w : idxs[0]'(by rw [hstk.len]; omega) = idx0 := by
                        have he := hstk.idx0_eq
                        rw [List.getElem?_eq_getElem (by rw [hstk.len]; omega)] at he
                        exact Option.some.inj he
                      simp only [hsp0', hi0_eq_w] at hcov_sp hrsn_eq
                      exact ⟨mrk1, mstk1, mclr1, mcl1, mcf1, hsi, hm',
                        ⟨idx0, hi0, hi0_eq, pos.toNat,
                          by rw [← hrsn_eq, ← hsz_eq]; exact hpos_ge', hcov_sp⟩⟩
                    · c0_cond hsp_pos
                      have hsp_gt0 : 0 < sp.toNat := by bv_omega
                      ml_lets; apply wp_call_of_spec; apply hMm
                      have hz_v : mrk1[v.toNat]?.getD 0#8 = 0#8 := by
                        rw [hv_nat]; exact (hstk.slot sp.toNat hsp_idxs).2 (by omega)
                      refine fullMinMarkSpec_zero_inv hcore hsi.mrk_len hsi.mstk_len hsi.mclr_len
                        hsi.mcl_le hm' hv_lt hz_v ((2 : BitVec 32).setWidth 8) fun m4 hm4 => ?_
                      ml_lets
                      have h2_eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl
                      rw [h2_eq] at hm4
                      let st_p := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
                      let k4 := fullMinMarkCore st_p.core v.toNat 2#8
                      have hcore_p := hsi.core hcore
                      have hhrsn := frameCov_to_hrsn hcore hcov_sp
                        (by rw [← hrsn_eq, ← hsz_eq]; exact hpos_ge')
                      have hno8_v : (st_p.core.mrk[(s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD
                          0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8 := by
                        have h1 : st_p.core.mrk[v.toNat]?.getD 0#8 = 0#8 := hz_v
                        rw [← hv_nat, h1]; rfl
                      have hv_eq' : (s.core.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 =
                          v.toNat := hv_nat.symm
                      have hmin4 : FullMinMarkInv k4 keepSet := by
                        simpa only [k4, hv_eq'] using
                          fullMinMarkInv_mark_rem hcore_p hsi.min_inv
                            (hstk.bd sp.toNat hsp_idxs) hno8_v hhrsn
                      obtain ⟨hsi4, hmono_step⟩ := minLitStInv_mark hcv hsi hv_lt hz_v 2#8
                        (Or.inl rfl) hmin4
                      have hstk4 := minLitStkInv_pop hcore hstk hsp_gt0 hmono_step
                        (by rw [← hv_nat]; dsimp only [k4, fullMinMarkCore]
                            rw [List.getElem?_set_self (by rw [hsi.mrk_len]; omega),
                              Option.getD_some, hz_v]; decide)
                        (fun k hk => by
                          have hne : (s.core.trl[idxs[k]]?.getD 0#32).toNat / 2 ≠ v.toNat := by
                            rw [hv_nat]
                            exact minLitStkInv_var_ne hcore hstk (by rw [hstk.len]; omega)
                              hsp_idxs (by omega)
                          dsimp only [k4, fullMinMarkCore]
                          rw [List.getElem?_set_ne (Ne.symm hne)])
                      have hsp_m1 : (sp - 1).toNat = sp.toNat - 1 := min_bv64_sub1 (by omega)
                      exact hL (maxSteps - (steps + 1).toNat) (sp - 1, steps + 1, ()) m4 hdec_n
                        ⟨by bv_omega, by omega, rfl, k4.mrk, mstk1, k4.min_clr,
                          k4.min_clr_len, k4.min_clr_full, idxs.take sp.toNat, hsi4, hm4,
                          by rwa [hsp_m1]⟩
                · rintro Jsz hJsz; ml_lets; ml_jnz; refine ⟨fun hbin => ?_, fun hbig => ?_⟩
                  · ml_lets; apply hJsz
                    have hbin' : (rsn &&& 0x80000000#32) ≠ 0#32 := by
                      change ((rsn &&& 0x80000000#32) != 0#32) = true at hbin
                      c0_cond hbin; exact hbin
                    exact ⟨rfl, by simp only [eq_true hbin', ↓reduceIte]; rfl, le_refl _⟩
                  · have hbin_f : ¬ (rsn &&& 0x80000000#32) ≠ 0#32 := by
                      change ((rsn &&& 0x80000000#32) != 0#32) = false at hbig
                      c0_cond hbig; intro hne; exact hne hbig
                    dsimp only [FrameCov] at hcov_sp; rcases hcov_sp with ⟨_, hif⟩
                    simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte] at hif
                    have hwf := hw0.arena.refs_wf _ hif.1
                    ml_ld load_full_arena_len (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) hm'
                    ml_lets; ml_jnz; refine ⟨fun har1 => ?_, fun _ => ?_⟩
                    · exfalso
                      dsimp only [minLitState] at har1
                      have hlt1 := bv64_lt_zext32_add3 (by have := hlen0.arena_len_le; omega) rsn
                        har1
                      have := hwf.1; omega
                    · have har2 : (rsn.setWidth 64 + 2).toNat <
                          (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).core.arena.length := by
                        rw [bv64_zext32_add2]
                        have := hwf.1; have := hlen0.arena_len_le; have := hlen0.arena_len_arr
                        dsimp only [minLitState]; omega
                      ml_ld c0_load_full_arena (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
                        (i := rsn.setWidth 64 + 2) har2 hm'
                      let sz := s.core.arena[(rsn.setWidth 64 + 2).toNat]'har2
                      have har2_s : (rsn.setWidth 64 + 2).toNat < s.core.arena.length := har2
                      have hsz_e : sz.toNat = fullArenaClauseSizeCore s.core rsn.toNat := by
                        have hopt : s.core.arena[(rsn.setWidth 64 + 2).toNat]? =
                            s.core.arena[rsn.toNat + 2]? := by rw [bv64_zext32_add2]
                        rw [List.getElem?_eq_getElem har2_s] at hopt
                        exact congrArg (fun o => (o.getD 0#32).toNat) hopt
                      ml_lets; ml_jnz; refine ⟨fun hsz3 => ?_, fun _ => ?_⟩
                      · exfalso; rw [BitVec.ult, decide_eq_true_eq] at hsz3
                        have h3 : (3 : BitVec 32).toNat = 3 := rfl
                        rw [h3, hsz_e] at hsz3; have := hwf.2.1; omega
                      · ml_ld load_full_arena_len
                          (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) hm'
                        ml_lets; ml_jnz; refine ⟨fun har_oob => ?_, fun _ => ?_⟩
                        · exfalso
                          dsimp only [minLitState] at har_oob
                          have hlt2 := bv64_lt_zext32_add3_add
                            (by have := hlen0.arena_len_le; omega) rsn sz har_oob
                          have := hwf.2.2.1; have := hwf.2.2.2.1; rw [hsz_e] at hlt2; omega
                        · ml_lets; apply hJsz
                          refine ⟨rfl, ?_, ?_⟩
                          · simp only [eq_false hbin_f, ↓reduceIte, Arg.val_var]; exact hsz_e
                          · simp only [Arg.val_var]; rw [hsz_e]; have := hwf.2.1; omega
          · ml_lets; apply hB
            exact ⟨mrk1, mstk1, mclr1, mcl1, mcf1, hsi, hm',
              ⟨hsp_lt, idxs, minLitStkInv_drop_cov hstk⟩⟩
        · rintro B L hB hL; ml_lets
          let mstk0 := (s.core.min_stk.set 0 (root_lit >>> 1)).set 1 0#32
          have hmstkl' : mstk0.length = 2 * c.minDepth := by simp [mstk0, hmstkl]
          have hstk0 : MinLitStkInv s.core mstk0 s.core.mrk 0 idx0 [idx0] true := by
            refine ⟨rfl, rfl, fun k hk => ?_, fun k hk => by simp at hk, fun k hk => ?_,
              fun k hk => ?_, fun _ k hk => ?_⟩
            · have hk0 : k = 0 := by simp at hk; omega
              subst k; exact hi0
            · have hk0 : k = 0 := by simp at hk; omega
              subst k; exact le_refl _
            · have hk0 : k = 0 := by simp at hk; omega
              subst k
              rw [List.getElem?_set_ne (by decide), List.getElem?_set_self
                (by unfold FullCfg.minDepth at *; omega), Option.getD_some]
              refine ⟨?_, fun h1 => by omega⟩
              have hl := litVar_litNeg root_lit.toNat; unfold litVar litNeg at hl
              simp only [List.getElem_cons_zero]; rw [hi0_eq, hl, bv32_lshr_1]
            · have hk0 : k = 0 := by simp at hk; omega
              subst k
              rw [List.getElem?_set_self (by simp; unfold FullCfg.minDepth at *; omega),
                Option.getD_some]
              refine ⟨fun hk1 => by simp at hk1, ?_⟩
              simp only [List.length_singleton, ↓reduceIte, BitVec.toNat_ofNat]
              exact frameCov_zero hcore s.core.mrk hi0 hrsn_ne0
          have hsi0 : MinLitStInv c s keepSet s.core.mrk mstk0 s.core.min_clr
              s.core.min_clr_len s.core.min_clr_full :=
            ⟨hlen0.mrk_len, hmstkl', hlen0.min_clr_len_arr, hlen0.min_clr_len_le,
              fun _ _ => rfl, fullMinMarkInv_with_mstk hmin mstk0,
              fun _ _ h => h, fun _ _ => rfl⟩
          have hm1' : (FullMem c (minLitState s s.core.mrk mstk0 s.core.min_clr
              s.core.min_clr_len s.core.min_clr_full) ⋆ R) (storeMem (storeMem m i32
                (c.pMinStk + (BitVec.signExtend 64 (0 : BitVec 32) : BitVec 64) * 4)
                (root_lit >>> 1)) i32
                (c.pMinStk + (BitVec.signExtend 64 (1 : BitVec 32) : BitVec 64) * 4) 0) := by
            have h0 : (BitVec.signExtend 64 (0 : BitVec 32) : BitVec 64) * (4 : BitVec 64) =
                0#64 := rfl
            have h1 : (BitVec.signExtend 64 (1 : BitVec 32) : BitVec 64) * (4 : BitVec 64) =
                BitVec.ofNat 64 (4 * 1) := rfl
            rw [h0, h1]; exact hm1
          exact hL maxSteps (0#64, 0#64, ()) _
            ⟨hmd_pos, Nat.zero_le _, rfl, s.core.mrk, mstk0, s.core.min_clr,
              s.core.min_clr_len, s.core.min_clr_full, [idx0], hsi0, hm1', hstk0⟩

end LeanQbe.T.Examples.Kissat.Full
