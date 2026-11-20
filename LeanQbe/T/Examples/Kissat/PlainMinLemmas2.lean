module

public import LeanQbe.T.Examples.Kissat.PlainMinLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for Kissat `D-Plain` Minimization (`Wave 2b Shard 5`, Part 2)

Proves parametric `(Γ : Env)` `Func.wp` contract for `plain_min_lit` matching `PlainSpec.lean`:
- `plain_min_lit` (`plainMinLitSpec`, `plain_min_lit_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open scoped PlainMinTactics

/-! ## 1. Iterative `plain_min_lit` stack & DFS invariants -/

private def minLitRsnLit (s : PlainState) (rsn : BitVec 32) (pos : Nat) : Nat :=
  if (rsn &&& 0x80000000#32) ≠ 0#32 then (rsn &&& 0x7FFFFFFF#32).toNat
  else (s.arena[rsn.toNat + 3 + pos]?.getD 0#32).toNat

private def FrameCov (c : PlainCfg) (s : PlainState) (mrk1 : List (BitVec 8))
    (idx lim : Nat) : Prop :=
  let p := (s.trl[idx]?.getD 0#32).toNat
  let rsn := s.rsns[p / 2]?.getD 0xFFFFFFFF#32
  rsn ≠ 0xFFFFFFFF#32 ∧
  if (rsn &&& 0x80000000#32) ≠ 0#32 then
    let ot := (rsn &&& 0x7FFFFFFF#32).toNat
    ot < 2 * c.mv ∧
    (0 < lim →
      ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
        ((s.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8))
  else
    rsn.toNat ∈ arenaClauseRefs s ∧ arenaClauseGarb s rsn.toNat = false ∧
    3 ≤ arenaClauseSize s rsn.toNat ∧
    ∀ pos < lim, pos < arenaClauseSize s rsn.toNat →
      let q := (s.arena[rsn.toNat + 3 + pos]?.getD 0#32).toNat
      q = p ∨ ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)

private def EdgeChild (s : PlainState) (idx pos cidx : Nat) : Prop :=
  let p := (s.trl[idx]?.getD 0#32).toNat
  let rsn := s.rsns[p / 2]?.getD 0xFFFFFFFF#32
  let l := minLitRsnLit s rsn pos
  cidx < idx ∧ (s.trl[cidx]?.getD 0#32).toNat = l ^^^ 1

private theorem frameCov_zero {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) (mrk1 : List (BitVec 8)) {idx : Nat}
    (hi : idx < s.trail_end)
    (hne : s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    FrameCov c s mrk1 idx 0 := by
  have hrs := hcore.reason_inv idx hi hne
  refine ⟨hne, ?_⟩
  split at hrs <;> split
  · exact ⟨hrs.1, fun h => by omega⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · have hwf := hcore.arena.refs_wf _ hrs.1
    exact ⟨hrs.1, hrs.2.1, hwf.2.1, fun _ h => by omega⟩

private theorem frameCov_arena_lits_mem {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {cref pos : Nat} (href : cref ∈ arenaClauseRefs s)
    (hp : pos < arenaClauseSize s cref) :
    (s.arena[cref + 3 + pos]?.getD 0#32).toNat ∈ arenaClauseLits s cref := by
  have hwf := hcore.arena.refs_wf cref href
  have hbd : cref + 3 + arenaClauseSize s cref ≤ s.arena.length := by
    have := hwf.2.2.1; have := hwf.2.2.2.1
    have := hcore.lengths.arena_len_le; have := hcore.lengths.arena_len_arr; omega
  rw [mem_arenaClauseLits_iff hbd]
  refine ⟨pos, hp, ?_⟩
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

private theorem frameCov_arena_lits_bd {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {cref : Nat} (href : cref ∈ arenaClauseRefs s) :
    cref + 3 + arenaClauseSize s cref ≤ s.arena.length := by
  have hwf := hcore.arena.refs_wf cref href
  have := hwf.2.2.1; have := hwf.2.2.2.1
  have := hcore.lengths.arena_len_le; have := hcore.lengths.arena_len_arr; omega

private theorem frameCov_mono {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)}
    (hmono : ∀ w < c.mv,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {idx lim : Nat} (hcov : FrameCov c s mrk1 idx lim) : FrameCov c s mrk2 idx lim := by
  rcases hcov with ⟨hne, hif⟩
  refine ⟨hne, ?_⟩
  split at hif <;> split
  · refine ⟨hif.1, fun hl => ?_⟩
    obtain ⟨k, hk, hkeq, hdep⟩ := hif.2 hl
    exact ⟨k, hk, hkeq, hdep.elim Or.inl fun h2 => Or.inr (hmono _ (by omega) h2)⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · refine ⟨hif.1, hif.2.1, hif.2.2.1, fun pos hp1 hp2 => ?_⟩
    rcases hif.2.2.2 pos hp1 hp2 with heq | ⟨k, hk, hkeq, hdep⟩
    · exact Or.inl heq
    · have hqlt := hcore.arena.lits_lt _ hif.1 hif.2.1 _ (frameCov_arena_lits_mem hcore hif.1 hp2)
      exact Or.inr ⟨k, hk, hkeq, hdep.elim Or.inl fun h2 => Or.inr (hmono _ (by omega) h2)⟩

private theorem frameCov_step {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk1 : List (BitVec 8)} {idx pos : Nat}
    (hi : idx < s.trail_end) (hcov : FrameCov c s mrk1 idx pos)
    (hlt : pos < if (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else arenaClauseSize s
        (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hstep :
      let p := (s.trl[idx]?.getD 0#32).toNat
      let rsn := s.rsns[p / 2]?.getD 0xFFFFFFFF#32
      let q := minLitRsnLit s rsn pos
      q / 2 = p / 2 ∨
      ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)) :
    FrameCov c s mrk1 idx (pos + 1) := by
  dsimp only [FrameCov] at hcov ⊢
  rcases hcov with ⟨hne, hif⟩
  have hrs := hcore.reason_inv idx hi hne
  refine ⟨hne, ?_⟩
  dsimp only [minLitRsnLit] at hstep ⊢
  dsimp only at hif hrs hlt hstep ⊢
  by_cases hbin : (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif hrs hlt hstep ⊢
    refine ⟨hif.1, fun _ => ?_⟩
    rcases hstep with hvar | ⟨k, hk, hkeq, hdep⟩
    · obtain ⟨k, hk, hkeq⟩ := hrs.2.2
      have hln := litVar_litNeg
        (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat
      unfold litVar litNeg at hln
      have hkp : k = idx := hcore.trail_vars_nodup k idx (by omega) hi (by
        rw [hkeq, hln]; exact hvar)
      omega
    · exact ⟨k, hk, hkeq, hdep⟩
  · simp only [eq_false hbin, ↓reduceIte] at hif hrs hlt hstep ⊢
    refine ⟨hif.1, hif.2.1, hif.2.2.1, fun j hj1 hj2 => ?_⟩
    by_cases hjp : j < pos
    · exact hif.2.2.2 j hjp hj2
    · have hjeq : j = pos := by omega
      subst hjeq
      rcases hstep with hvar | hok
      · have hmem := frameCov_arena_lits_mem hcore hif.1 hj2
        rcases hrs.2.2 _ hmem with hqeq | ⟨k, hk, hkeq⟩
        · exact Or.inl hqeq
        · have hln := litVar_litNeg (s.arena[(s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32).toNat + 3 + j]?.getD 0#32).toNat
          unfold litVar litNeg at hln
          have hkp : k = idx := hcore.trail_vars_nodup k idx (by omega) hi (by
            rw [hkeq, hln]; exact hvar)
          omega
      · exact Or.inr hok

private theorem frameCov_to_hrsn {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk1 : List (BitVec 8)} {idx lim : Nat}
    (hi : idx < s.trail_end) (hcov : FrameCov c s mrk1 idx lim)
    (hlim : (if (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else arenaClauseSize s
        (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat) ≤ lim) :
    let p0 := (s.trl[idx]?.getD 0#32).toNat
    let rsn := s.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 ∧
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * c.mv ∧ F0.EntailsClause (cnfClause [p0, ot]) ∧
      ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
        ((s.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    else
      rsn.toNat ∈ arenaClauseRefs s ∧ arenaClauseGarb s rsn.toNat = false ∧
      ∀ q ∈ arenaClauseLits s rsn.toNat,
        q = p0 ∨ ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
          ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk1[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  dsimp only [FrameCov] at hcov
  rcases hcov with ⟨hne, hif⟩
  have hrs := hcore.reason_inv idx hi hne
  refine ⟨hne, ?_⟩
  dsimp only at hif hrs hlim ⊢
  by_cases hbin : (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif hrs hlim ⊢
    exact ⟨hif.1, hrs.2.1, hif.2 (by omega)⟩
  · simp only [eq_false hbin, ↓reduceIte] at hif hrs hlim ⊢
    refine ⟨hif.1, hif.2.1, fun q hq => ?_⟩
    have hbd := frameCov_arena_lits_bd hcore hif.1
    obtain ⟨j, hj, hjeq⟩ := (mem_arenaClauseLits_iff hbd).mp hq
    have hq' := hif.2.2.2 j (by omega) hj
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, hjeq] at hq'

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

private theorem dec_chain_le {idxs : List Nat} {i j : Nat}
    (hdec : ∀ k (hk : k + 1 < idxs.length), idxs[k + 1] < idxs[k])
    (hij : i ≤ j) (hi : i < idxs.length) (hj : j < idxs.length) :
    idxs[j] ≤ idxs[i] := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (dec_chain_lt hdec hlt hi hj)

private structure MinLitStkInv (c : PlainCfg) (s : PlainState) (mstk1 : List (BitVec 32))
    (mrk1 : List (BitVec 8)) (sp idx0 : Nat) (idxs : List Nat) (reqCov : Bool) : Prop where
  len : idxs.length = sp + 1
  idx0_eq : idxs[0]? = some idx0
  bd : ∀ k (hk : k < idxs.length), idxs[k] < s.trail_end
  dec : ∀ k (hk : k + 1 < idxs.length), idxs[k + 1] < idxs[k]
  slot : ∀ k (hk : k < idxs.length),
    let vk := (s.trl[idxs[k]]?.getD 0#32).toNat / 2
    (mstk1[2 * k]?.getD 0#32).toNat = vk ∧ (1 ≤ k → mrk1[vk]?.getD 0#8 = 0#8)
  cov : reqCov = true → ∀ k (hk : k < idxs.length),
    let posk := (mstk1[2 * k + 1]?.getD 0#32).toNat
    let rsn := s.rsns[(s.trl[idxs[k]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
    (∀ _hk1 : k + 1 < idxs.length, 1 ≤ posk ∧
      posk ≤ (if (rsn &&& 0x80000000#32) ≠ 0#32 then 1 else arenaClauseSize s rsn.toNat) ∧
      EdgeChild s idxs[k] (posk - 1) idxs[k + 1]) ∧
    FrameCov c s mrk1 idxs[k] (if k + 1 = idxs.length then posk else posk - 1)

private theorem minLitStkInv_drop_cov {c : PlainCfg} {s : PlainState}
    {mstk1 : List (BitVec 32)} {mrk1 : List (BitVec 8)} {sp idx0 : Nat} {idxs : List Nat}
    (h : MinLitStkInv c s mstk1 mrk1 sp idx0 idxs true) :
    MinLitStkInv c s mstk1 mrk1 sp idx0 idxs false :=
  ⟨h.len, h.idx0_eq, h.bd, h.dec, h.slot, fun hc => by cases hc⟩

private theorem minLitStkInv_var_ne {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mstk1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {sp idx0 : Nat} {idxs : List Nat} {req}
    (h : MinLitStkInv c s mstk1 mrk1 sp idx0 idxs req)
    {i j : Nat} (hi : i < idxs.length) (hj : j < idxs.length) (hne : i ≠ j) :
    (s.trl[idxs[i]]?.getD 0#32).toNat / 2 ≠ (s.trl[idxs[j]]?.getD 0#32).toNat / 2 := by
  intro heq
  have hij := hcore.trail_vars_nodup idxs[i] idxs[j] (h.bd i hi) (h.bd j hj) heq
  rcases Nat.lt_or_gt_of_ne hne with h1 | h2
  · have := dec_chain_lt h.dec h1 hi hj; omega
  · have := dec_chain_lt h.dec h2 hj hi; omega

private theorem minLitStkInv_poison_other {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mstk1 mclr1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {sp idx0 u_idx mcl1 : Nat} {mcf1 : BitVec 64}
    {idxs : List Nat}
    (h : MinLitStkInv c s mstk1 mrk1 sp idx0 idxs false)
    (hu_idx : ∀ k (hk : k < idxs.length), u_idx < idxs[k])
    (hmrk_eq : ∀ w < c.mv, w ≠ (s.trl[u_idx]?.getD 0#32).toNat / 2 →
      mrk1[w]?.getD 0#8 = (plainMinMarkState c
        { s with mrk := mrk1, min_stk := mstk1, min_clr := mclr1,
                 min_clr_len := mcl1, min_clr_full := mcf1 }
        ((s.trl[u_idx]?.getD 0#32).toNat / 2) 4#8).mrk[w]?.getD 0#8) :
    MinLitStkInv c s mstk1
      (plainMinMarkState c
        { s with mrk := mrk1, min_stk := mstk1, min_clr := mclr1,
                 min_clr_len := mcl1, min_clr_full := mcf1 }
        ((s.trl[u_idx]?.getD 0#32).toNat / 2) 4#8).mrk sp idx0 idxs false := by
  refine ⟨h.len, h.idx0_eq, h.bd, h.dec, fun k hk => ?_, fun hc => by cases hc⟩
  refine ⟨(h.slot k hk).1, fun hk1 => ?_⟩
  have hvk : (s.trl[idxs[k]]?.getD 0#32).toNat / 2 < c.mv := by
    have := hcore.trail_lits_lt idxs[k] (h.bd k hk); omega
  have hne : (s.trl[idxs[k]]?.getD 0#32).toNat / 2 ≠
      (s.trl[u_idx]?.getD 0#32).toNat / 2 := fun heq => by
    have hlt := hu_idx k hk
    have hu_te : u_idx < s.trail_end := Nat.lt_trans hlt (h.bd k hk)
    have := hcore.trail_vars_nodup idxs[k] u_idx (h.bd k hk) hu_te heq
    omega
  rw [← hmrk_eq _ hvk hne]
  exact (h.slot k hk).2 hk1

private theorem minLitStkInv_step_top {c : PlainCfg} {s : PlainState}
    {mstk1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {sp idx0 : Nat} {idxs : List Nat}
    (h : MinLitStkInv c s mstk1 mrk1 sp idx0 idxs true)
    (hmstk_len : mstk1.length = 2 * c.minDepth) (hsp : sp < c.minDepth)
    (newPos : BitVec 32)
    (hnp : newPos.toNat = (mstk1[2 * sp + 1]?.getD 0#32).toNat + 1)
    (hcov_top : ∀ hk : sp < idxs.length, FrameCov c s mrk1 idxs[sp] newPos.toNat) :
    MinLitStkInv c s (mstk1.set (2 * sp + 1) newPos) mrk1 sp idx0 idxs true := by
  have hlt_stk : 2 * sp + 1 < mstk1.length := by omega
  refine ⟨h.len, h.idx0_eq, h.bd, h.dec, fun k hk => ?_, fun _ k hk => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]
    exact h.slot k hk
  · have hlen := h.len
    by_cases htop : k = sp
    · subst htop
      rw [List.getElem?_set_self hlt_stk, Option.getD_some]
      refine ⟨fun hk1 => by omega, ?_⟩
      simp only [show k + 1 = idxs.length by omega, ↓reduceIte]
      exact hcov_top hk
    · have hklt : k + 1 < idxs.length := by omega
      have hne_len : ¬ (k + 1 = idxs.length) := by omega
      rw [List.getElem?_set_ne (by omega)]
      simpa only [hne_len, ↓reduceIte] using h.cov rfl k hk

private theorem minLitStkInv_push {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mstk1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {sp idx0 u_idx : Nat} {idxs : List Nat}
    (h : MinLitStkInv c s mstk1 mrk1 sp idx0 idxs true)
    (hmstk_len : mstk1.length = 2 * c.minDepth) (hsp1 : sp + 1 < c.minDepth)
    {u_bv pos_bv : BitVec 32}
    (hpos_eq : pos_bv.toNat = (mstk1[2 * sp + 1]?.getD 0#32).toNat + 1)
    (hu_bd : u_idx < idxs[sp]'(by have := h.len; omega))
    (hu_eq : u_bv.toNat = (s.trl[u_idx]?.getD 0#32).toNat / 2)
    (hpos_lt : (mstk1[2 * sp + 1]?.getD 0#32).toNat <
      (if (s.rsns[(s.trl[idxs[sp]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1
        else arenaClauseSize s (s.rsns[(s.trl[idxs[sp]'(by have := h.len; omega)]?.getD
          0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat))
    (hmrk_u : mrk1[u_bv.toNat]?.getD 0#8 = 0#8)
    (hrsn_u : s.rsns[u_bv.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hedge : EdgeChild s (idxs[sp]'(by have := h.len; omega))
      (mstk1[2 * sp + 1]?.getD 0#32).toNat u_idx) :
    let mstk2 := ((mstk1.set (2 * sp + 1) pos_bv).set (2 * (sp + 1)) u_bv).set
      (2 * (sp + 1) + 1) 0#32
    MinLitStkInv c s mstk2 mrk1 (sp + 1) idx0 (idxs ++ [u_idx]) true := by
  intro mstk2
  have hlen := h.len
  have hb1 : 2 * sp + 1 < mstk1.length := by omega
  have hb2 : 2 * (sp + 1) < (mstk1.set (2 * sp + 1) pos_bv).length := by simp [hmstk_len]; omega
  have hb3 : 2 * (sp + 1) + 1 <
      ((mstk1.set (2 * sp + 1) pos_bv).set (2 * (sp + 1)) u_bv).length := by
    simp [hmstk_len]; omega
  have idx_append_lt : ∀ k (hk : k < idxs.length),
      (idxs ++ [u_idx])[k]'(by simp; omega) = idxs[k] := fun k hk =>
    List.getElem_append_left hk
  have idx_append_last : (idxs ++ [u_idx])[idxs.length]'(by simp) = u_idx := by simp
  refine ⟨by simp [hlen], ?_, ?_, ?_, fun k hk => ?_, fun _ k hk => ?_⟩
  · rw [List.getElem?_append_left (by omega)]; exact h.idx0_eq
  · intro k hk
    by_cases hkl : k < idxs.length
    · rw [idx_append_lt k hkl]; exact h.bd k hkl
    · have hkeq : k = idxs.length := by simp at hk; omega
      subst k; rw [idx_append_last]
      exact Nat.lt_trans hu_bd (h.bd sp (by omega))
  · intro k hk
    simp only [List.length_append, List.length_singleton] at hk
    by_cases hkl : k + 1 < idxs.length
    · rw [idx_append_lt k (by omega), idx_append_lt (k + 1) hkl]; exact h.dec k hkl
    · have hkeq : k = sp := by omega
      subst k
      rw [idx_append_lt sp (by omega),
        List.getElem_append_right (by omega : idxs.length ≤ sp + 1)]
      simp only [hlen, Nat.sub_self, List.getElem_cons_zero]
      exact hu_bd
  · by_cases hkl : k < idxs.length
    · rw [idx_append_lt k hkl]
      have hne1 : 2 * (sp + 1) + 1 ≠ 2 * k := by omega
      have hne2 : 2 * (sp + 1) ≠ 2 * k := by omega
      have hne3 : 2 * sp + 1 ≠ 2 * k := by omega
      dsimp only [mstk2]
      rw [List.getElem?_set_ne hne1, List.getElem?_set_ne hne2, List.getElem?_set_ne hne3]
      exact h.slot k hkl
    · have hkeq : k = idxs.length := by simp at hk; omega
      subst k; rw [idx_append_last]
      dsimp only [mstk2]
      rw [List.getElem?_set_ne (by omega), show 2 * idxs.length = 2 * (sp + 1) by omega,
        List.getElem?_set_self hb2, Option.getD_some]
      exact ⟨hu_eq, fun _ => by rwa [← hu_eq]⟩
  · by_cases hkl : k < idxs.length
    · have hklt : k + 1 < (idxs ++ [u_idx]).length := by simp; omega
      rw [idx_append_lt k hkl]
      by_cases htop : k = sp
      · subst k
        dsimp only [mstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self hb1, Option.getD_some]
        refine ⟨fun _ => ?_, ?_⟩
        · rw [hpos_eq]; refine ⟨by omega, by omega, ?_⟩
          rw [List.getElem_append_right (by omega : idxs.length ≤ sp + 1)]
          simp only [hlen, Nat.sub_self, List.getElem_cons_zero]
          exact hedge
        · have hne : sp + 1 ≠ (idxs ++ [u_idx]).length := by
            rw [List.length_append, List.length_singleton, hlen]; omega
          simp only [hne, ↓reduceIte, hpos_eq, Nat.add_sub_cancel]
          have hcov_sp := (h.cov rfl sp hkl).2
          have heq_sp : sp + 1 = idxs.length := by omega
          simpa only [heq_sp, ↓reduceIte] using hcov_sp
      · have hk1 : k + 1 < idxs.length := by omega
        dsimp only [mstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega)]
        have hprev := h.cov rfl k hkl
        have hne1 : k + 1 ≠ (idxs ++ [u_idx]).length := by
          rw [List.length_append, List.length_singleton, hlen]; omega
        have hne2 : k + 1 ≠ idxs.length := by omega
        simp only [hne1, hne2, ↓reduceIte] at hprev ⊢
        refine ⟨fun _ => ?_, hprev.2⟩
        rw [idx_append_lt (k + 1) hk1]
        exact hprev.1 hk1
    · have hkeq : k = idxs.length := by simp at hk; omega
      subst k; rw [idx_append_last]
      dsimp only [mstk2]
      rw [show 2 * idxs.length + 1 = 2 * (sp + 1) + 1 by omega, List.getElem?_set_self hb3,
        Option.getD_some]
      refine ⟨fun hk1 => by simp only [List.length_append, List.length_singleton] at hk1; omega,
        ?_⟩
      simp only [List.length_append, List.length_singleton, ↓reduceIte, BitVec.toNat_ofNat]
      have hu_te : u_idx < s.trail_end := Nat.lt_trans hu_bd (h.bd sp (by omega))
      exact frameCov_zero hcore mrk1 hu_te (by rw [← hu_eq]; exact hrsn_u)

private theorem minLitStkInv_pop {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mstk1 : List (BitVec 32)} {mrk1 mrk2 : List (BitVec 8)}
    {sp idx0 : Nat} {idxs : List Nat}
    (h : MinLitStkInv c s mstk1 mrk1 sp idx0 idxs true) (hsp : 0 < sp)
    (hmono : ∀ w < c.mv,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hmrk_top : (mrk2[(s.trl[idxs[sp]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD
      0#8 &&& 2#8) ≠ 0#8)
    (hmrk_keep : ∀ k (hk : k < sp),
      mrk2[(s.trl[idxs[k]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD 0#8 =
        mrk1[(s.trl[idxs[k]'(by have := h.len; omega)]?.getD 0#32).toNat / 2]?.getD 0#8) :
    MinLitStkInv c s mstk1 mrk2 (sp - 1) idx0 (idxs.take sp) true := by
  have hlen := h.len
  have htake_len : (idxs.take sp).length = sp := by rw [List.length_take, hlen]; omega
  refine ⟨by omega, ?_, ?_, ?_, fun k hk => ?_, fun _ k hk => ?_⟩
  · rw [← h.idx0_eq]; exact List.getElem?_take_of_lt hsp
  · intro k hk
    rw [List.getElem_take]; exact h.bd k (by omega)
  · intro k hk
    rw [List.getElem_take, List.getElem_take]; exact h.dec k (by omega)
  · rw [List.getElem_take]
    have hlt_sp : k < sp := by omega
    refine ⟨(h.slot k (by omega)).1, fun hk1 => ?_⟩
    rw [hmrk_keep k hlt_sp]
    exact (h.slot k (by omega)).2 hk1
  · rw [List.getElem_take]
    have hlt_sp : k < sp := by omega
    have hprev := h.cov rfl k (by omega)
    have hne : k + 1 ≠ idxs.length := by omega
    simp only [hne, ↓reduceIte] at hprev
    by_cases hntop : k = sp - 1
    · subst k
      refine ⟨fun hk1 => by omega, ?_⟩
      simp only [htake_len, show sp - 1 + 1 = sp by omega, ↓reduceIte]
      have hpos1 : 1 ≤ (mstk1[2 * (sp - 1) + 1]?.getD 0#32).toNat := (hprev.1 (by omega)).1
      have hpos_le := (hprev.1 (by omega)).2.1
      have hedge := (hprev.1 (by omega)).2.2
      simp only [show sp - 1 + 1 = sp by omega] at hedge
      have hcov_m := frameCov_mono hcore hmono hprev.2
      dsimp only [EdgeChild] at hedge
      have hsz_lt : (mstk1[2 * (sp - 1) + 1]?.getD 0#32).toNat - 1 <
          if (s.rsns[(s.trl[idxs[sp - 1]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
              0x80000000#32) ≠ 0#32 then 1 else arenaClauseSize s
            (s.rsns[(s.trl[idxs[sp - 1]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
        omega
      have hstep := frameCov_step hcore (h.bd (sp - 1) (by omega)) hcov_m hsz_lt ?_
      · simpa only [show (mstk1[2 * (sp - 1) + 1]?.getD 0#32).toNat - 1 + 1 =
          (mstk1[2 * (sp - 1) + 1]?.getD 0#32).toNat by omega] using hstep
      · have hdec_sp : idxs[sp]'(by omega) < idxs[sp - 1]'(by omega) := by
          simpa [show sp - 1 + 1 = sp by omega] using h.dec (sp - 1) (by omega)
        refine Or.inr ⟨idxs[sp]'(by omega), hdec_sp, hedge.2, Or.inr ?_⟩
        have hvar : (minLitRsnLit s
            (s.rsns[(s.trl[idxs[sp - 1]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
            ((mstk1[2 * (sp - 1) + 1]?.getD 0#32).toNat - 1)) / 2 =
            (s.trl[idxs[sp]]?.getD 0#32).toNat / 2 := by
          have hl := litVar_litNeg (minLitRsnLit s
            (s.rsns[(s.trl[idxs[sp - 1]]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
            ((mstk1[2 * (sp - 1) + 1]?.getD 0#32).toNat - 1))
          unfold litVar litNeg at hl
          rw [← hl, ← hedge.2]
        rwa [hvar]
    · have hk1 : k + 1 < sp := by omega
      have hne2 : k + 1 ≠ (idxs.take sp).length := by omega
      simp only [hne2, ↓reduceIte]
      refine ⟨fun _ => ?_, frameCov_mono hcore hmono hprev.2⟩
      rw [List.getElem_take]
      exact hprev.1 (by omega)

private theorem frameCov_edge_exists {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk1 : List (BitVec 8)} {idx pos : Nat}
    (hi : idx < s.trail_end) (hcov : FrameCov c s mrk1 idx pos)
    (hlt : pos < if (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32 then 1 else arenaClauseSize s
        (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hneq : minLitRsnLit s (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32) pos / 2 ≠
      (s.trl[idx]?.getD 0#32).toNat / 2) :
    let q := minLitRsnLit s (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32) pos
    q < 2 * c.mv ∧ ∃ cidx < idx, (s.trl[cidx]?.getD 0#32).toNat = q ^^^ 1 := by
  dsimp only [FrameCov, minLitRsnLit] at hcov hlt hneq ⊢
  rcases hcov with ⟨hne, hif⟩
  have hrs := hcore.reason_inv idx hi hne
  dsimp only at hif hrs hlt hneq ⊢
  by_cases hbin : (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hif hrs hlt hneq ⊢
    exact ⟨hrs.1, hrs.2.2⟩
  · simp only [eq_false hbin, ↓reduceIte] at hif hrs hlt hneq ⊢
    have hmem := frameCov_arena_lits_mem hcore hif.1 hlt
    have hqlt := hcore.arena.lits_lt _ hif.1 hif.2.1 _ hmem
    refine ⟨hqlt, ?_⟩
    rcases hrs.2.2 _ hmem with heq | hex
    · exact absurd (by rw [heq]) hneq
    · exact hex

private structure MinLitStInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (keepSet : List Nat) (mrk1 : List (BitVec 8)) (mstk1 mclr1 : List (BitVec 32))
    (mcl1 : Nat) (mcf1 : BitVec 64) : Prop where
  mrk_len : mrk1.length = c.mv
  mstk_len : mstk1.length = 2 * c.minDepth
  mclr_len : mclr1.length = c.mv
  mcl_le : mcl1 ≤ c.mv
  min_inv : PlainMinMarkInv c F0 (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) keepSet
  mono2 : ∀ w < c.mv,
    (s.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8
  bit8 : ∀ w < c.mv,
    (mrk1[w]?.getD 0#8 &&& 8#8) = (s.mrk[w]?.getD 0#8 &&& 8#8)

private theorem MinLitStInv.core {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64}
    (hcore : PlainCoreInv c F0 s)
    (h : MinLitStInv c F0 s keepSet mrk1 mstk1 mclr1 mcl1 mcf1) :
    PlainCoreInv c F0 (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) :=
  coreInv_with_min hcore (mcf1 := mcf1) h.mrk_len h.mstk_len h.mclr_len h.mcl_le

private theorem minLitStInv_with_mstk {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {mstk1 mclr1 mstk' : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64}
    (h : MinLitStInv c F0 s keepSet mrk1 mstk1 mclr1 mcl1 mcf1)
    (hmstk' : mstk'.length = 2 * c.minDepth) :
    MinLitStInv c F0 s keepSet mrk1 mstk' mclr1 mcl1 mcf1 :=
  { h with
    mstk_len := hmstk'
    min_inv := minMarkInv_with_mstk h.min_inv mstk' }

private theorem minLitStInv_mark {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keepSet : List Nat} {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64}
    (hsi : MinLitStInv c F0 s keepSet mrk1 mstk1 mclr1 mcl1 mcf1)
    {v : Nat} (hv : v < c.mv) (hz : mrk1[v]?.getD 0#8 = 0#8) (tag : BitVec 8)
    (htag : tag = 2#8 ∨ tag = 4#8)
    (hmin' : PlainMinMarkInv c F0
      (plainMinMarkState c (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) v tag) keepSet) :
    let st_p := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
    let st' := plainMinMarkState c st_p v tag
    MinLitStInv c F0 s keepSet st'.mrk mstk1 st'.min_clr st'.min_clr_len st'.min_clr_full ∧
    (∀ w < c.mv,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (st'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  intro st_p st'
  have hmono_prev : ∀ w < c.mv,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (st'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
    intro w hw hw2
    dsimp only [st', plainMinMarkState]
    by_cases hweq : w = v
    · subst w; rw [hz] at hw2; exact absurd rfl hw2
    · rwa [List.getElem?_set_ne (Ne.symm hweq)]
  have hbit8' : ∀ w < c.mv,
      (st'.mrk[w]?.getD 0#8 &&& 8#8) = (s.mrk[w]?.getD 0#8 &&& 8#8) := by
    intro w hw
    dsimp only [st', plainMinMarkState]
    by_cases hweq : w = v
    · subst w
      rw [List.getElem?_set_self (by rw [hsi.mrk_len]; exact hv), Option.getD_some]
      have hz' : st_p.mrk[v]?.getD 0#8 = 0#8 := hz
      rw [hz', ← hsi.bit8 v hv, hz']
      rcases htag with rfl | rfl <;> decide
    · rw [List.getElem?_set_ne (Ne.symm hweq)]; exact hsi.bit8 w hw
  have hmclr' : st'.min_clr.length = c.mv := by
    dsimp only [st', st_p, plainMinMarkState]; split <;> simp [hsi.mclr_len]
  have hmcl' : st'.min_clr_len ≤ c.mv := by
    have hmcl_le := hsi.mcl_le
    dsimp only [st', plainMinMarkState]; split <;> omega
  have hmrk' : st'.mrk.length = c.mv := by
    dsimp only [st', st_p, plainMinMarkState]; rw [List.length_set]; exact hsi.mrk_len
  refine ⟨⟨hmrk', hsi.mstk_len, hmclr', hmcl', hmin',
    fun w hw hws => hmono_prev w hw (hsi.mono2 w hw hws), hbit8'⟩, hmono_prev⟩

private theorem bv64_rsn_add3_pos {rsn pos : BitVec 32} :
    (rsn.setWidth 64 + BitVec.signExtend 64 (3 : BitVec 32) + pos.setWidth 64).toNat =
      rsn.toNat + 3 + pos.toNat := by
  have h3 : (BitVec.signExtend 64 (3 : BitVec 32) : BitVec 64).toNat = 3 := by decide
  have hr : rsn.toNat < 2 ^ 32 := rsn.isLt
  have hp : pos.toNat < 2 ^ 32 := pos.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, h3]
  omega

private theorem bv64_rsn_add2 {rsn : BitVec 32} :
    (rsn.setWidth 64 + BitVec.signExtend 64 (2 : BitVec 32)).toNat = rsn.toNat + 2 := by
  have h2 : (BitVec.signExtend 64 (2 : BitVec 32) : BitVec 64).toNat = 2 := by decide
  have hr : rsn.toNat < 2 ^ 32 := rsn.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, h2]
  omega

private theorem plainMinMarkSpec_zero_inv {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {R : Mem 64 → Prop} {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64} {m1 : Mem 64} {Q' : Post []} {X' : XPost}
    (hcore : PlainCoreInv c F0 s)
    (hmrk : mrk1.length = c.mv) (hmstk : mstk1.length = 2 * c.minDepth)
    (hmclr : mclr1.length = c.mv) (hmcl : mcl1 ≤ c.mv)
    (hm1 : (PlainMem c (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) ⋆ R) m1)
    {v : BitVec 32} (hv : v.toNat < c.mv) (hz : mrk1[v.toNat]?.getD 0#8 = 0#8)
    (tag : BitVec 8)
    (hpost : ∀ m',
      let st1 := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
      let st2 := plainMinMarkState c st1 v.toNat tag
      (PlainMem c (minLitState s st2.mrk mstk1 st2.min_clr st2.min_clr_len st2.min_clr_full) ⋆ R)
        m' → Q' () m') :
    plainMinMarkSpec (c.hdr, v, tag, ()) m1 Q' X' := by
  let st1 := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
  have hlen1 : st1.LengthsOk c :=
    (coreInv_with_min hcore (mcf1 := mcf1) hmrk hmstk hmclr hmcl).lengths
  refine ⟨c, st1, R, rfl, hlen1, hm1, ?_⟩
  dsimp only
  have hc1 : ¬ (c.mv ≤ v.toNat ∨ (st1.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8) := fun h => by
    rcases h with h | h
    · exact (by omega : ¬ c.mv ≤ v.toNat) h
    · change (mrk1[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8 at h
      rw [hz] at h; simp at h
  have hc2 : ¬ (st1.mrk[v.toNat]?.getD 0#8 ≠ 0#8) := fun h => h hz
  simp only [eq_false hc1, eq_false hc2, ↓reduceIte]
  have hzor : (0#8 : BitVec 8) ||| tag = tag := BitVec.zero_or
  by_cases hlt : mcl1 < c.mv
  · have hlt' : st1.min_clr_len < c.mv := hlt
    simp only [eq_true hlt', ↓reduceIte]
    intro m' hm'
    have hp := hpost m'
    dsimp only [plainMinMarkState, minLitState] at hp ⊢
    have hmcl1' : mcl1 < c.mv := hlt
    simp only [hz, hmcl1', and_self, not_true_eq_false, and_false, ↓reduceIte, hzor] at hp
    have hv_eq : BitVec.ofNat 32 v.toNat = v := bv_ofNat_toNat_eq v
    dsimp only [st1, minLitState] at hm'
    rw [hz, hzor] at hm'
    rw [hv_eq] at hp
    exact hp hm'
  · have hlt' : ¬ st1.min_clr_len < c.mv := hlt
    simp only [eq_false hlt', ↓reduceIte]
    intro m' hm'
    have hp := hpost m'
    dsimp only [plainMinMarkState, minLitState] at hp ⊢
    have hmcl1' : ¬ mcl1 < c.mv := hlt
    simp only [hz, hmcl1', and_self, and_false, not_false_eq_true, ↓reduceIte, hzor] at hp
    dsimp only [st1, minLitState] at hm'
    rw [hz, hzor] at hm'
    exact hp hm'

private theorem minLit_u32_add1_toNat {a b : BitVec 32} (h : a.toNat < b.toNat) :
    (a + 1#32).toNat = a.toNat + 1 := by
  have hb := b.isLt; bv_omega

private theorem minLit_maxSteps_toNat {c : PlainCfg} {s : PlainState}
    (hle : s.arena_len ≤ c.arena_cap) :
    ((BitVec.ofNat 64 s.arena_len + BitVec.ofNat 64 c.mv) * 4 + 64).toNat =
      (s.arena_len + c.mv) * 4 + 64 := by
  have hmv := c.hmv; have har := c.harena; unfold dimacsBound at hmv har
  have hbd : (s.arena_len + c.mv) * 4 + 64 < 2 ^ 64 := by omega
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  have h64 : (64 : BitVec 64).toNat = 64 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4, h64]
  rw [Nat.mod_eq_of_lt (by omega : s.arena_len < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : s.arena_len + c.mv < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (s.arena_len + c.mv) * 4 < 2 ^ 64),
    Nat.mod_eq_of_lt hbd]

/-! ## 2. `plain_min_lit_wp` -/

theorem plain_min_lit_wp (Γ : Env)
    (hMm : ∀ args m Q X, plainMinMarkSpec args m Q X →
      Γ "plain_min_mark" [i64, i32, i8] [] args m Q X) :
    ∀ args m Q X, plainMinLitSpec args m Q X →
      Func.wp Γ plain_min_lit_body args m Q X := by
  rintro ⟨h, root_lit, ⟨⟩⟩ m Q X ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hrl, hval, hno8, hm, hQ⟩
  unfold Func.wp plain_min_lit_body
  dsimp only [plain_min_lit_body]
  rw [wp]; refine ⟨_, load_arena_mv hm, ?_⟩; ml_lets
  ml_jnz; refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · exfalso; c0_cond hge; have hmv := c.hmv; unfold dimacsBound at hmv; bv_omega
  · ml_lets; rw [wp]; refine ⟨_, load_arena_min_depth hm, ?_⟩; ml_lets
    ml_jnz; refine ⟨fun hz => ?_, fun hnz => ?_⟩
    · exfalso; c0_cond hz; have := plainMinDepthOf_pos c.mv
      have := plainMinDepthOf_le c.mv; unfold PlainCfg.minDepth at *; bv_omega
    · ml_lets; rw [wp]; refine ⟨_, load_arena_reason hm, ?_⟩; ml_lets
      rw [wp]; refine ⟨_, c0_load_arena_rsns (i := (root_lit >>> 1).setWidth 64) ?_ hm, ?_⟩
      · have hrsns := hcore.lengths.rsns_len; have hmv := c.hmv; unfold dimacsBound at hmv
        bv_omega
      · ml_lets; ml_jnz; refine ⟨fun hrsn_none => ?_, fun hrsn_some => ?_⟩
        · ml_lets; rw [wp]
          exact hQ false s.mrk s.min_stk s.min_clr s.min_clr_len s.min_clr_full m
            hcore.lengths (fun _ _ h => h) (fun _ _ => rfl) hmin (fun h => by cases h) hm
        · ml_lets; rw [wp]; refine ⟨_, load_arena_mark hm, ?_⟩
          ml_lets; rw [wp]; refine ⟨_, load_arena_level hm, ?_⟩
          ml_lets; rw [wp]; refine ⟨_, load_arena_arena_ptr hm, ?_⟩
          ml_lets; rw [wp]; refine ⟨_, load_arena_min_stk_ptr hm, ?_⟩
          ml_lets; rw [wp]
          have hmd_pos := plainMinDepthOf_pos c.mv
          have hmstkl := hcore.lengths.min_stk_len
          obtain ⟨hok0, hm0⟩ := store_arena_min_stk (i := 0) (root_lit >>> 1)
            (by unfold PlainCfg.minDepth at *; omega) hm
          refine ⟨by simpa using hok0, ?_⟩
          ml_lets; rw [wp]
          obtain ⟨hok1, hm1⟩ := store_arena_min_stk (i := 1) 0#32
            (by simp [hmstkl]; unfold PlainCfg.minDepth at *; omega) hm0
          refine ⟨by simpa using hok1, ?_⟩
          ml_lets; rw [wp]; refine ⟨_, load_arena_len hm1, ?_⟩
          ml_lets
          obtain ⟨idx0, hi0, hi0_eq⟩ := (hcore.vals_false_iff root_lit.toNat hrl).mp hval
          have hrv_root : (s.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2 := by
            have hl := litVar_litNeg root_lit.toNat; unfold litVar litNeg at hl
            rw [hi0_eq, hl]
          have hrsn_ne0 : s.rsns[(s.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
              0xFFFFFFFF#32 := by
            have hrl_lt : (root_lit >>> 1).toNat < s.rsns.length := by
              rw [hcore.lengths.rsns_len]; bv_omega
            rw [hrv_root, ← bv32_lshr_1, List.getElem?_eq_getElem hrl_lt, Option.getD_some]
            intro heq
            c0_cond hrsn_some
            simp only [Nat.mod_eq_of_lt (by bv_omega : root_lit.toNat / 2 < 2 ^ 64)] at hrsn_some
            apply hrsn_some
            simp only [← bv32_lshr_1]
            exact heq.trans rfl
          let maxSteps := (s.arena_len + c.mv) * 4 + 64
          let BrkPost : Tup Val [i64, .bool, i64] → Mem 64 → Prop :=
            fun (sp, ok, _steps, ()) m' =>
              ∃ mrk1 mstk1 mclr1 mcl1 mcf1,
                let st := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
                MinLitStInv c F0 s keepSet mrk1 mstk1 mclr1 mcl1 mcf1 ∧
                (PlainMem c st ⋆ R) m' ∧
                if ok then
                  ∃ idx0_w < s.trail_end,
                    (s.trl[idx0_w]?.getD 0#32).toNat = root_lit.toNat ^^^ 1 ∧
                    ∃ lim,
                      (if (s.rsns[(s.trl[idx0_w]?.getD 0#32).toNat / 2]?.getD
                          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then 1
                       else arenaClauseSize s
                         (s.rsns[(s.trl[idx0_w]?.getD 0#32).toNat / 2]?.getD
                           0xFFFFFFFF#32).toNat) ≤ lim ∧
                      FrameCov c s mrk1 idx0_w lim
                else
                  sp.toNat < c.minDepth ∧
                  ∃ idxs, MinLitStkInv c s mstk1 mrk1 sp.toNat idx0 idxs false
          let LpInv : Nat → Tup Val [i64, i64] → Mem 64 → Prop :=
            fun n (sp, steps, ()) m' =>
              sp.toNat < c.minDepth ∧ steps.toNat ≤ maxSteps ∧ n = maxSteps - steps.toNat ∧
              ∃ mrk1 mstk1 mclr1 mcl1 mcf1 idxs,
                let st := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
                MinLitStInv c F0 s keepSet mrk1 mstk1 mclr1 mcl1 mcf1 ∧
                (PlainMem c st ⋆ R) m' ∧
                MinLitStkInv c s mstk1 mrk1 sp.toNat idx0 idxs true
          refine wp_loop_break_group (brkTs := [i64, .bool, i64]) (lpTs := [i64, i64])
            BrkPost LpInv ?_ ?_ ?_
          · rintro B ⟨sp, ok, steps, ⟨⟩⟩ m' ⟨mrk1, mstk1, mclr1, mcl1, mcf1,
              hsi, hm', hrest⟩
            rw [Blocks.get_here]; ml_lets
            ml_jnz; refine ⟨fun hok => ?_, fun hnok => ?_⟩
            · ml_lets; rw [wp]
              rw [hok] at hrest; simp only [↓reduceIte] at hrest
              obtain ⟨idx0_w, hi0_w, hroot_w, lim, hlim_w, hcov_w⟩ := hrest
              have hcore1 := hsi.core hcore
              have hh := frameCov_to_hrsn hcore hi0_w hcov_w hlim_w
              have hrv_w : (s.trl[idx0_w]?.getD 0#32).toNat / 2 = root_lit.toNat / 2 := by
                have hl := litVar_litNeg root_lit.toNat; unfold litVar litNeg at hl
                rw [hroot_w, hl]
              refine hQ true mrk1 mstk1 mclr1 mcl1 mcf1 m' hcore1.lengths hsi.mono2 hsi.bit8
                hsi.min_inv (fun _ => ⟨fun keep' hsub => ?_, ?_⟩) hm'
              · refine plainMinMarkInv_drop hcore1 hsi.min_inv hsub hi0_w hroot_w ?_
                simp only [hroot_w] at hh; exact hh
              · have hno8_w :
                    (mrk1[(s.trl[idx0_w]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8 := by
                  rw [hrv_w, hsi.bit8 _ (by omega)]
                  exact hno8 _ (by omega) (le_refl _)
                have hmrk := plainMinMarkInv_mark_rem hcore1 hsi.min_inv hi0_w hno8_w hh
                simpa only [hrv_w] using hmrk
            · rw [hnok] at hrest; simp only [Bool.false_eq_true, ↓reduceIte] at hrest
              obtain ⟨hsp_lt, idxs, hstk⟩ := hrest
              ml_lets
              let AfterInv : Nat → Tup Val [i64] → Mem 64 → Prop :=
                fun n' (j, ()) m2 =>
                  1 ≤ j.toNat ∧ j.toNat ≤ sp.toNat + 1 ∧ n' = sp.toNat + 1 - j.toNat ∧
                  ∃ mrk2 mclr2 mcl2 mcf2,
                    let st2 := minLitState s mrk2 mstk1 mclr2 mcl2 mcf2
                    MinLitStInv c F0 s keepSet mrk2 mstk1 mclr2 mcl2 mcf2 ∧
                    (PlainMem c st2 ⋆ R) m2 ∧
                    ∀ k (hk : k < idxs.length), j.toNat ≤ k →
                      mrk2[(s.trl[idxs[k]]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
              refine wp_loop_group (ts := [i64]) AfterInv ?_ ?_
              · rintro J n' ⟨j, ⟨⟩⟩ m2 hJ ⟨hj1, hj_le, rfl,
                  mrk2, mclr2, mcl2, mcf2, hsi2, hm2, hzero2⟩
                rw [Blocks.get_here]; ml_lets
                ml_jnz; refine ⟨fun hj_ule => ?_, fun hj_gt => ?_⟩
                · have hj_le_sp : j.toNat ≤ sp.toNat := by c0_cond hj_ule; bv_omega
                  have hj_idxs : j.toNat < idxs.length := by rw [hstk.len]; omega
                  have hmd_le : c.minDepth ≤ 1000 := plainMinDepthOf_le c.mv
                  have hj_stk :
                      (j <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
                        mstk1.length := by
                    rw [bv64_shl1_toNat (by omega), hsi2.mstk_len]; omega
                  ml_lets; rw [wp]
                  refine ⟨_, c0_load_arena_min_stk
                    (s := minLitState s mrk2 mstk1 mclr2 mcl2 mcf2)
                    (i := j <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64))
                    hj_stk hm2, ?_⟩
                  ml_lets; rw [wp]
                  let v_bv := mstk1[(j <<<
                    ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat]'hj_stk
                  have hv_nat : v_bv.toNat =
                      (s.trl[idxs[j.toNat]'hj_idxs]?.getD 0#32).toNat / 2 := by
                    have hsh :
                        (j <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat =
                          2 * j.toNat :=
                      bv64_shl1_toNat (by omega)
                    have hslot := (hstk.slot j.toNat hj_idxs).1
                    rw [List.getElem?_eq_getElem (by rw [hsi2.mstk_len]; omega),
                      Option.getD_some] at hslot
                    dsimp only [v_bv]; simp only [hsh]; exact hslot
                  have hv_lt : v_bv.toNat < c.mv := by
                    rw [hv_nat]; have := hcore.trail_lits_lt _ (hstk.bd j.toNat hj_idxs); omega
                  have hz_bv : mrk2[v_bv.toNat]?.getD 0#8 = 0#8 := by
                    rw [hv_nat]; exact hzero2 j.toNat hj_idxs (le_refl _)
                  apply wp_call_of_spec; apply hMm
                  refine plainMinMarkSpec_zero_inv hcore hsi2.mrk_len hsi2.mstk_len hsi2.mclr_len
                    hsi2.mcl_le hm2 hv_lt hz_bv ((4 : BitVec 32).setWidth 8) fun m3 hm3 => ?_
                  ml_lets; rw [wp]
                  let st2 := minLitState s mrk2 mstk1 mclr2 mcl2 mcf2
                  let st3 := plainMinMarkState c st2 v_bv.toNat 4#8
                  have h4_eq : (4 : BitVec 32).setWidth 8 = 4#8 := rfl
                  rw [h4_eq] at hm3
                  have hcore2 := hsi2.core hcore
                  have hno8_v : (st2.mrk[v_bv.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
                    have hz2 : st2.mrk[v_bv.toNat]?.getD 0#8 = 0#8 := hz_bv
                    rw [hz2]; rfl
                  have hmin3 := plainMinMarkInv_poison hcore2 hsi2.min_inv hv_lt hno8_v
                  obtain ⟨hsi3, _⟩ := minLitStInv_mark hsi2 hv_lt hz_bv 4#8 (Or.inr rfl) hmin3
                  have hj1_nat : (j + 1).toNat = j.toNat + 1 := by
                    have h1 : (1 : BitVec 64).toNat = 1 := rfl
                    rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
                  refine hJ (sp.toNat + 1 - (j + 1).toNat) (j + 1, ()) m3
                    (by rw [hj1_nat]; omega)
                    ⟨by omega, by omega, rfl,
                      st3.mrk, st3.min_clr, st3.min_clr_len, st3.min_clr_full,
                      hsi3, hm3, fun k hk hjk => ?_⟩
                  have hne_k : (s.trl[idxs[k]]?.getD 0#32).toNat / 2 ≠ v_bv.toNat := by
                    rw [hv_nat]
                    exact minLitStkInv_var_ne hcore hstk hk hj_idxs (by omega)
                  dsimp only [st3, plainMinMarkState]
                  rw [List.getElem?_set_ne (Ne.symm hne_k)]
                  exact hzero2 k hk (by omega)
                · ml_lets; rw [wp]
                  have hcore2 := hsi2.core hcore
                  exact hQ false mrk2 mstk1 mclr2 mcl2 mcf2 m2 hcore2.lengths hsi2.mono2
                    hsi2.bit8 hsi2.min_inv (fun h => by cases h) hm2
              · intro J hJ
                wp_unfold
                exact hJ sp.toNat (1#64, ()) m' ⟨le_refl _, Nat.succ_le_of_lt (by omega), rfl,
                  mrk1, mclr1, mcl1, mcf1, hsi, hm',
                  fun k hk hk1 => (hstk.slot k hk).2 hk1⟩
          · rintro B L n ⟨sp, steps, ⟨⟩⟩ m' hB hL
              ⟨hsp_lt, hsteps_le, rfl, mrk1, mstk1, mclr1, mcl1, mcf1, idxs,
                hsi, hm', hstk⟩
            rw [Blocks.get_here]; ml_lets
            ml_jnz; refine ⟨fun hlt_st => ?_, fun hge_st => ?_⟩
            · have hms_eq : ((BitVec.ofNat 64 s.arena_len + BitVec.ofNat 64 c.mv) * 4 + 64).toNat =
                  maxSteps := minLit_maxSteps_toNat hcore.lengths.arena_len_le
              rw [BitVec.ult, decide_eq_true_eq] at hlt_st
              dsimp only [maxSteps] at hms_eq hlt_st
              rw [hms_eq] at hlt_st
              have hsteps1 : (steps + 1).toNat = steps.toNat + 1 := by
                have hmv := c.hmv; have har := c.harena; unfold dimacsBound at hmv har
                have h1 : (1 : BitVec 64).toNat = 1 := rfl
                rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
              have hdec_n : maxSteps - (steps + 1).toNat < maxSteps - steps.toNat := by omega
              have hmd_le : c.minDepth ≤ 1000 := plainMinDepthOf_le c.mv
              have hstk_ev :
                  (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
                    mstk1.length := by
                rw [bv64_shl1_toNat (by omega), hsi.mstk_len]; omega
              have hstk_od :
                  (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat <
                    mstk1.length := by
                rw [bv64_shl1_add1_toNat (by omega), hsi.mstk_len]; omega
              have hsp_idxs : sp.toNat < idxs.length := by rw [hstk.len]; omega
              ml_lets; rw [wp]
              refine ⟨_, c0_load_arena_min_stk (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
                (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) hstk_ev hm', ?_⟩
              ml_lets; rw [wp]
              refine ⟨_, c0_load_arena_min_stk (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
                (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1)
                hstk_od hm', ?_⟩
              let v := mstk1[(sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat]'
                hstk_ev
              let pos := mstk1[(sp <<<
                ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat]'hstk_od
              have hv_nat : v.toNat =
                  (s.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
                have hslot := (hstk.slot sp.toNat hsp_idxs).1
                rw [List.getElem?_eq_getElem (by rw [hsi.mstk_len]; omega), Option.getD_some]
                  at hslot
                dsimp only [v]; simp only [bv64_shl1_toNat (x := sp) (by omega)]; exact hslot
              have hv_lt : v.toNat < c.mv := by
                rw [hv_nat]; have := hcore.trail_lits_lt _ (hstk.bd sp.toNat hsp_idxs); omega
              have hpos_nat : pos.toNat = (mstk1[2 * sp.toNat + 1]?.getD 0#32).toNat := by
                dsimp only [pos]
                simp only [bv64_shl1_add1_toNat (x := sp) (by omega)]
                rw [List.getElem?_eq_getElem (by rw [hsi.mstk_len]; omega), Option.getD_some]
              ml_lets; ml_jnz; refine ⟨fun hv_ge => ?_, fun _ => ?_⟩
              · exfalso
                change (BitVec.ofNat 64 c.mv).ule (v.setWidth 64) = true at hv_ge
                c0_cond hv_ge; bv_omega
              · have hv_rsns : (v.setWidth 64).toNat <
                    (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).rsns.length := by
                  dsimp only [minLitState]; rw [hcore.lengths.rsns_len]; bv_omega
                ml_lets; rw [wp]
                refine ⟨_, c0_load_arena_rsns (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
                  (i := v.setWidth 64) hv_rsns hm', ?_⟩
                let rsn := s.rsns[(v.setWidth 64).toNat]'hv_rsns
                have hrsn_eq : rsn = s.rsns[(s.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat /
                    2]?.getD 0xFFFFFFFF#32 := by
                  have hvl : v.toNat < s.rsns.length := by rw [hcore.lengths.rsns_len]; omega
                  have hvw : (v.setWidth 64).toNat = v.toNat := bv_c0_zext32_64 v
                  dsimp only [rsn]
                  rw [List.getElem?_eq_getElem (by rw [← hv_nat]; exact hvl), Option.getD_some]
                  congr 1; first | done | (rw [hvw]; exact hv_nat)
                have hcov_sp : FrameCov c s mrk1 (idxs[sp.toNat]'hsp_idxs) pos.toNat := by
                  have hc := (hstk.cov rfl sp.toNat hsp_idxs).2
                  have htop_eq : sp.toNat + 1 = idxs.length := by rw [hstk.len]
                  simpa only [htop_eq, ↓reduceIte, ← hpos_nat] using hc
                ml_lets; ml_jnz; refine ⟨fun hrsn_none => ?_, fun _ => ?_⟩
                · exfalso
                  change (rsn == 0xFFFFFFFF#32) = true at hrsn_none
                  c0_cond hrsn_none
                  exact hcov_sp.1 (by rwa [← hrsn_eq])
                · ml_lets
                  let is_bin := rsn &&& 0x80000000#32 != 0#32
                  let SzPost : Tup Val [i32] → Mem 64 → Prop := fun (sz, ()) m2 =>
                    m2 = m' ∧
                    sz.toNat = (if (rsn &&& 0x80000000#32) ≠ 0#32 then 1
                      else arenaClauseSize s rsn.toNat) ∧ 1 ≤ sz.toNat
                  refine wp_join_group (ts := [i32]) SzPost ?_ ?_
                  · rintro Jsz ⟨sz, ⟨⟩⟩ m2 ⟨hm2_eq, hsz_eq, hsz1⟩
                    subst m2
                    rw [Blocks.get_here]; ml_lets
                    ml_jnz; refine ⟨fun hpos_lt => ?_, fun hpos_ge => ?_⟩
                    · change pos.ult sz = true at hpos_lt
                      rw [BitVec.ult, decide_eq_true_eq] at hpos_lt
                      have hpos_add1 : (pos + 1).toNat = pos.toNat + 1 :=
                        minLit_u32_add1_toNat hpos_lt
                      ml_lets; rw [wp]
                      obtain ⟨hok_p, hm_p⟩ := c0_store_arena_min_stk
                        (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
                        (i := sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1)
                        (pos + 1) hstk_od hm'
                      refine ⟨hok_p, ?_⟩
                      let mstk2 := mstk1.set (2 * sp.toNat + 1) (pos + 1)
                      let m_p := storeMem m' i32 (c.pMinStk +
                        (sp <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1) *
                          (4 : BitVec 64)) (pos + 1)
                      have hm_p' :
                          (PlainMem c (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1) ⋆ R) m_p := by
                        rw [bv64_shl1_add1_toNat (x := sp) (by omega)] at hm_p
                        exact hm_p
                      have hmstk2_len : mstk2.length = 2 * c.minDepth := by
                        simp [mstk2, hsi.mstk_len]
                      have hsi_p := minLitStInv_with_mstk hsi hmstk2_len
                      have hstk2_drop : MinLitStkInv c s mstk2 mrk1 sp.toNat idx0 idxs false := by
                        refine ⟨hstk.len, hstk.idx0_eq, hstk.bd, hstk.dec, fun k hk => ?_,
                          fun hc => by cases hc⟩
                        dsimp only [mstk2]
                        rw [List.getElem?_set_ne (by omega)]
                        exact hstk.slot k hk
                      ml_lets
                      let LitPost : Tup Val [i32] → Mem 64 → Prop := fun (lit, ()) m3 =>
                        m3 = m_p ∧ lit.toNat = minLitRsnLit s rsn pos.toNat
                      refine wp_join_group (ts := [i32]) LitPost ?_ ?_
                      · rintro Jl ⟨lit, ⟨⟩⟩ m3 ⟨rfl, hlit_eq⟩
                        rw [Blocks.get_here]; ml_lets
                        have hcore_p := hsi_p.core hcore
                        have hcov_sz : pos.toNat < if (s.rsns[(s.trl[idxs[sp.toNat]'hsp_idxs]?.getD
                            0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
                            then 1 else arenaClauseSize s (s.rsns[(s.trl[idxs[sp.toNat]'
                              hsp_idxs]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
                          rw [← hrsn_eq, ← hsz_eq]; exact hpos_lt
                        have hu_bd_lt : (lit >>> 1).toNat < c.mv := by
                          dsimp only [FrameCov] at hcov_sp
                          rcases hcov_sp with ⟨_, hif⟩
                          rw [bv32_lshr_1, hlit_eq]
                          dsimp only [minLitRsnLit]
                          by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
                          · simp only [← hrsn_eq, eq_true hbin, ↓reduceIte] at hif ⊢; omega
                          · simp only [← hrsn_eq, eq_false hbin, ↓reduceIte] at hif hsz_eq ⊢
                            have hpos_ac : pos.toNat < arenaClauseSize s rsn.toNat := by omega
                            have hmem := frameCov_arena_lits_mem hcore hif.1 hpos_ac
                            have hllt := hcore.arena.lits_lt _ hif.1 hif.2.1 _ hmem
                            omega
                        ml_jnz; refine ⟨fun hu_ge => ?_, fun _ => ?_⟩
                        · exfalso; c0_cond hu_ge; bv_omega
                        · ml_lets; ml_jnz; refine ⟨fun huv => ?_, fun huv_ne => ?_⟩
                          · c0_cond huv
                            refine hL (maxSteps - (steps + 1).toNat)
                              (sp, steps + 1, ()) _ hdec_n
                              ⟨hsp_lt, by omega, rfl, mrk1, mstk2, mclr1, mcl1, mcf1, idxs,
                                hsi_p, hm_p', ?_⟩
                            refine minLitStkInv_step_top hstk hsi.mstk_len hsp_lt (pos + 1)
                              (by rw [hpos_add1, hpos_nat]) fun _ => ?_
                            rw [hpos_add1]
                            refine frameCov_step hcore (hstk.bd sp.toNat hsp_idxs)
                              hcov_sp hcov_sz (Or.inl ?_)
                            rw [← hrsn_eq, ← hlit_eq, ← hv_nat, ← bv32_lshr_1, huv]
                          · have hu_ne_v : minLitRsnLit s
                                (s.rsns[(s.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat /
                                  2]?.getD 0xFFFFFFFF#32) pos.toNat / 2 ≠
                                (s.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 := by
                              rw [← hrsn_eq, ← hlit_eq, ← hv_nat, ← bv32_lshr_1]
                              c0_cond huv_ne
                              intro heq; apply huv_ne; exact BitVec.eq_of_toNat_eq heq
                            obtain ⟨hql_lt, u_idx, hu_idx_lt, hu_idx_eq⟩ := frameCov_edge_exists
                              hcore (hstk.bd sp.toNat hsp_idxs) hcov_sp hcov_sz hu_ne_v
                            have hu_lvl_len : ((lit >>> 1).setWidth 64).toNat <
                                (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).lvl.length := by
                              dsimp only [minLitState]; rw [hcore.lengths.lvl_len]; bv_omega
                            ml_lets; rw [wp]
                            refine ⟨_, c0_load_arena_lvl
                              (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                              (i := (lit >>> 1).setWidth 64) hu_lvl_len hm_p', ?_⟩
                            ml_lets; ml_jnz; refine ⟨fun hlvl0 => ?_, fun hlvl_nz => ?_⟩
                            · c0_cond hlvl0
                              refine hL (maxSteps - (steps + 1).toNat)
                                (sp, steps + 1, ()) _ hdec_n
                                ⟨hsp_lt, by omega, rfl, mrk1, mstk2, mclr1, mcl1, mcf1, idxs,
                                  hsi_p, hm_p', ?_⟩
                              refine minLitStkInv_step_top hstk hsi.mstk_len hsp_lt (pos + 1)
                                (by rw [hpos_add1, hpos_nat]) fun _ => ?_
                              rw [hpos_add1]
                              refine frameCov_step hcore (hstk.bd sp.toNat hsp_idxs)
                                hcov_sp hcov_sz (Or.inr ⟨u_idx, hu_idx_lt, ?_,
                                  Or.inl ?_⟩)
                              · exact hu_idx_eq
                              · rw [← hrsn_eq, ← hlit_eq, ← bv32_lshr_1]
                                have hlw : (lit >>> 1).toNat < s.lvl.length := by
                                  rw [hcore.lengths.lvl_len]; exact hu_bd_lt
                                have hidx : lit.toNat / 2 % 2 ^ 64 = (lit >>> 1).toNat := by
                                  rw [Nat.mod_eq_of_lt (by bv_omega : lit.toNat / 2 < 2 ^ 64),
                                    bv32_lshr_1]
                                have hget : s.lvl[(lit >>> 1).toNat]? = some 0#32 := by
                                  have hget0 : s.lvl[lit.toNat / 2 % 2 ^ 64]? = some 0#32 := by
                                    rw [List.getElem?_eq_getElem (by rw [hidx]; exact hlw)]
                                    exact congrArg some hlvl0
                                  simpa only [hidx] using hget0
                                rw [hget]; rfl
                            · have hu_mrk_len : ((lit >>> 1).setWidth 64).toNat <
                                  (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).mrk.length := by
                                dsimp only [minLitState]; rw [hsi.mrk_len]; bv_omega
                              ml_lets; rw [wp]
                              refine ⟨_, c0_load_arena_mrk
                                (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                                (i := (lit >>> 1).setWidth 64) hu_mrk_len hm_p', ?_⟩
                              let mu := mrk1[((lit >>> 1).setWidth 64).toNat]'hu_mrk_len
                              have hmu_eq : mu = mrk1[(lit >>> 1).toNat]?.getD 0#8 := by
                                have hvw : ((lit >>> 1).setWidth 64).toNat = (lit >>> 1).toNat := by
                                  bv_omega
                                dsimp only [mu]
                                rw [List.getElem?_eq_getElem (by rw [hsi.mrk_len]; exact hu_bd_lt),
                                  Option.getD_some]
                                congr 1
                              ml_lets; ml_jnz; refine ⟨fun hmu2 => ?_, fun hmu_n2 => ?_⟩
                              · change (mu.setWidth 32 &&& 2#32 != 0#32) = true at hmu2
                                have hmu_is2 : (mu &&& 2#8) ≠ 0#8 := by
                                  rw [show (2#32 : BitVec 32) = (2#8).setWidth 32 from rfl] at hmu2
                                  c0_cond hmu2; exact hmu2
                                refine hL (maxSteps - (steps + 1).toNat)
                                  (sp, steps + 1, ()) _ hdec_n
                                  ⟨hsp_lt, by omega, rfl, mrk1, mstk2, mclr1, mcl1, mcf1, idxs,
                                    hsi_p, hm_p', ?_⟩
                                refine minLitStkInv_step_top hstk hsi.mstk_len hsp_lt
                                  (pos + 1) (by rw [hpos_add1, hpos_nat]) fun _ => ?_
                                rw [hpos_add1]
                                refine frameCov_step hcore (hstk.bd sp.toNat hsp_idxs)
                                  hcov_sp hcov_sz (Or.inr ⟨u_idx, hu_idx_lt, ?_,
                                    Or.inr ?_⟩)
                                · exact hu_idx_eq
                                · rw [← hrsn_eq, ← hlit_eq, ← bv32_lshr_1, ← hmu_eq]
                                  exact hmu_is2
                              · change (mu.setWidth 32 &&& 2#32 != 0#32) = false at hmu_n2
                                ml_lets; ml_jnz; refine ⟨fun hmu4 => ?_, fun hmu_n4 => ?_⟩
                                · ml_lets; apply hB
                                  refine ⟨mrk1, mstk2, mclr1, mcl1, mcf1,
                                    hsi_p, hm_p', ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                                · change (mu.setWidth 32 &&& 4#32 != 0#32) = false at hmu_n4
                                  have hu_nat_idx : (lit >>> 1).toNat =
                                      (s.trl[u_idx]?.getD 0#32).toNat / 2 := by
                                    have hl := litVar_litNeg (minLitRsnLit s rsn pos.toNat)
                                    unfold litVar litNeg at hl
                                    have hu_idx_eq' := hu_idx_eq
                                    rw [← hrsn_eq] at hu_idx_eq'
                                    rw [bv32_lshr_1, hlit_eq, ← hl, ← hu_idx_eq']
                                  have hu_lt_idx0 : u_idx < idx0 := by
                                    have hle0 := dec_chain_le hstk.dec (Nat.zero_le sp.toNat)
                                      (by rw [hstk.len]; omega) hsp_idxs
                                    have hi0w : idxs[0]'(by rw [hstk.len]; omega) = idx0 := by
                                      have he := hstk.idx0_eq
                                      rw [List.getElem?_eq_getElem (by rw [hstk.len]; omega)] at he
                                      exact Option.some.inj he
                                    omega
                                  have hno8_u : (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) =
                                      0#8 := by
                                    have hml := hcore.trail_mono u_idx idx0
                                      (le_of_lt hu_lt_idx0) hi0
                                    rw [← hu_nat_idx, hrv_root] at hml
                                    rw [hsi.bit8 _ hu_bd_lt]
                                    exact hno8 _ hu_bd_lt hml
                                  have hmu0 : mu = 0#8 := by
                                    rw [show (2#32 : BitVec 32) = (2#8).setWidth 32 from rfl]
                                      at hmu_n2
                                    rw [show (4#32 : BitVec 32) = (4#8).setWidth 32 from rfl]
                                      at hmu_n4
                                    c0_cond hmu_n2; c0_cond hmu_n4
                                    have hdom := hsi.min_inv.mrk_dom (lit >>> 1).toNat hu_bd_lt
                                    rw [← hmu_eq] at hdom hno8_u
                                    exact bv8_zero_of_masks24 mu hdom hno8_u hmu_n2 hmu_n4
                                  have hu_rsns_len : ((lit >>> 1).setWidth 64).toNat <
                                      (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).rsns.length := by
                                    dsimp only [minLitState]; rw [hcore.lengths.rsns_len]; bv_omega
                                  ml_lets; rw [wp]
                                  refine ⟨_, c0_load_arena_rsns
                                    (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                                    (i := (lit >>> 1).setWidth 64) hu_rsns_len hm_p', ?_⟩
                                  ml_lets; ml_jnz
                                  refine ⟨fun hur_none => ?_, fun hur_some => ?_⟩
                                  · ml_lets; apply wp_call_of_spec; apply hMm
                                    have hz_u : mrk1[(lit >>> 1).toNat]?.getD 0#8 = 0#8 := by
                                      rw [← hmu_eq]; exact hmu0
                                    refine plainMinMarkSpec_zero_inv hcore hsi.mrk_len hmstk2_len
                                      hsi.mclr_len hsi.mcl_le hm_p' hu_bd_lt hz_u
                                      ((4 : BitVec 32).setWidth 8) fun m4 hm4 => ?_
                                    ml_lets; apply hB
                                    have h4_eq : (4 : BitVec 32).setWidth 8 = 4#8 := rfl
                                    rw [h4_eq] at hm4
                                    let st_p := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1
                                    let st4 := plainMinMarkState c st_p (lit >>> 1).toNat 4#8
                                    have hmin4 : PlainMinMarkInv c F0 st4 keepSet :=
                                      plainMinMarkInv_poison hcore_p hsi_p.min_inv hu_bd_lt
                                        (by change (mrk1[(lit >>> 1).toNat]?.getD 0#8 &&& 8#8) =
                                            0#8; rw [hz_u]; rfl)
                                    obtain ⟨hsi4, _⟩ := minLitStInv_mark hsi_p hu_bd_lt hz_u 4#8
                                      (Or.inr rfl) hmin4
                                    have hstk4 := minLitStkInv_poison_other hcore hstk2_drop
                                      (u_idx := u_idx) (mclr1 := mclr1) (mcl1 := mcl1)
                                      (mcf1 := mcf1)
                                      (fun k hk => by
                                        have := hstk.len
                                        by_cases hksp : k = sp.toNat
                                        · subst hksp; exact hu_idx_lt
                                        · exact Nat.lt_trans hu_idx_lt
                                            (dec_chain_lt hstk.dec (by omega) hk hsp_idxs))
                                      (fun w hw hne => by
                                        dsimp only [plainMinMarkState]
                                        rw [List.getElem?_set_ne (Ne.symm hne)])
                                    rw [← hu_nat_idx] at hstk4
                                    exact ⟨st4.mrk, mstk2, st4.min_clr, st4.min_clr_len,
                                      st4.min_clr_full, hsi4, hm4, ⟨hsp_lt, idxs, hstk4⟩⟩
                                  · ml_lets; rw [wp]
                                    refine ⟨_, load_arena_min_depth
                                      (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1) hm_p', ?_⟩
                                    ml_lets; ml_jnz
                                    refine ⟨fun hdepth => ?_, fun hdepth_ok => ?_⟩
                                    · ml_lets; apply hB
                                      exact ⟨mrk1, mstk2, mclr1, mcl1, mcf1,
                                        hsi_p, hm_p', ⟨hsp_lt, idxs, hstk2_drop⟩⟩
                                    · c0_cond hdepth_ok
                                      have hsp1_lt : sp.toNat + 1 < c.minDepth := by bv_omega
                                      have h1 : (1 : BitVec 64).toNat = 1 := rfl
                                      have hsp1_nat : (sp + 1).toNat = sp.toNat + 1 := by
                                        rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
                                      have hstk_ev1 :
                                          ((sp + 1) <<<
                                            ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)
                                            ).toNat < mstk2.length := by
                                        rw [bv64_shl1_toNat (x := sp + 1) (by omega), hmstk2_len]
                                        omega
                                      have hstk_od1 : ((sp + 1) <<<
                                          ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) +
                                          1).toNat < mstk2.length := by
                                        rw [bv64_shl1_add1_toNat (x := sp + 1) (by omega),
                                          hmstk2_len]
                                        omega
                                      ml_lets; rw [wp]
                                      obtain ⟨hok_u, hm_u⟩ := c0_store_arena_min_stk
                                        (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                                        (i := (sp + 1) <<<
                                          ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64))
                                        (lit >>> 1) hstk_ev1 hm_p'
                                      refine ⟨hok_u, ?_⟩
                                      ml_lets; rw [wp]
                                      let mstk_mid := mstk2.set (2 * (sp.toNat + 1)) (lit >>> 1)
                                      have hm_u' := hm_u
                                      rw [bv64_shl1_toNat (x := sp + 1) (by omega), hsp1_nat]
                                        at hm_u'
                                      have hmstk_mid_len : mstk_mid.length = 2 * c.minDepth := by
                                        simp [mstk_mid, hmstk2_len]
                                      obtain ⟨hok_z, hm_z⟩ := c0_store_arena_min_stk
                                        (s := minLitState s mrk1 mstk_mid mclr1 mcl1 mcf1)
                                        (i := (sp + 1) <<<
                                          ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1)
                                        (0 : BitVec 32)
                                        (by dsimp only [minLitState]
                                            rw [hmstk_mid_len, ← hmstk2_len]; exact hstk_od1)
                                        hm_u'
                                      refine ⟨hok_z, ?_⟩
                                      ml_lets
                                      let mstk3 := ((mstk1.set (2 * sp.toNat + 1) (pos + 1)).set
                                        (2 * (sp.toNat + 1)) (lit >>> 1)).set
                                        (2 * (sp.toNat + 1) + 1) 0#32
                                      have hmstk3_len : mstk3.length = 2 * c.minDepth := by
                                        simp [mstk3, hsi.mstk_len]
                                      have hm_z' := hm_z
                                      rw [bv64_shl1_add1_toNat (x := sp + 1) (by omega),
                                        hsp1_nat] at hm_z'
                                      have hrsn_u_ne : s.rsns[(lit >>> 1).toNat]?.getD
                                          0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                                        have hvw : ((lit >>> 1).setWidth 64).toNat =
                                            (lit >>> 1).toNat := by bv_omega
                                        have hrlu : ((lit >>> 1).setWidth 64).toNat <
                                            s.rsns.length := by
                                          rw [hcore.lengths.rsns_len, hvw]; exact hu_bd_lt
                                        rw [← hvw, List.getElem?_eq_getElem hrlu, Option.getD_some]
                                        dsimp only [minLitState] at hur_some
                                        intro heq
                                        have ht : (s.rsns[((lit >>> 1).setWidth 64).toNat] ==
                                            (4294967295 : BitVec 32)) = true := beq_iff_eq.mpr heq
                                        rw [ht] at hur_some; cases hur_some
                                      have hz_u : mrk1[(lit >>> 1).toNat]?.getD 0#8 = 0#8 := by
                                        rw [← hmu_eq]; exact hmu0
                                      have hstk3 := minLitStkInv_push hcore hstk hsi.mstk_len
                                        hsp1_lt (u_bv := lit >>> 1) (pos_bv := pos + 1)
                                        (by rw [hpos_add1, hpos_nat]) hu_idx_lt hu_nat_idx
                                        (by rwa [← hpos_nat]) hz_u hrsn_u_ne
                                        ⟨hu_idx_lt, by rw [← hpos_nat]; exact hu_idx_eq⟩
                                      exact hL (maxSteps - (steps + 1).toNat)
                                        (sp + 1, steps + 1, ()) _ hdec_n
                                        ⟨by bv_omega, by omega, rfl, mrk1, mstk3, mclr1,
                                          mcl1, mcf1, idxs ++ [u_idx],
                                          minLitStInv_with_mstk hsi hmstk3_len, hm_z',
                                          by rwa [hsp1_nat]⟩
                      · rintro Jl hJl; ml_lets
                        ml_jnz; refine ⟨fun hbin => ?_, fun hbig => ?_⟩
                        · ml_lets; apply hJl
                          refine ⟨rfl, ?_⟩
                          change ((rsn &&& 0x80000000#32) != 0#32) = true at hbin
                          c0_cond hbin
                          dsimp only [minLitRsnLit]
                          simp only [eq_true hbin, ↓reduceIte, BitVec.toNat_and]
                          simp only [rsn, bv_c0_zext32_64]; rfl
                        · have hbin_f : ¬ (rsn &&& 0x80000000#32) ≠ 0#32 := by
                            change ((rsn &&& 0x80000000#32) != 0#32) = false at hbig
                            c0_cond hbig; intro hne; exact hne hbig
                          dsimp only [FrameCov] at hcov_sp
                          rcases hcov_sp with ⟨_, hif⟩
                          simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte] at hif hsz_eq
                          have har_bd : (rsn.setWidth 64 + BitVec.signExtend 64 (3 : BitVec 32) +
                              pos.setWidth 64).toNat <
                              (minLitState s mrk1 mstk2 mclr1 mcl1 mcf1).arena.length := by
                            have hwf := hcore.arena.refs_wf _ hif.1
                            rw [bv64_rsn_add3_pos]
                            have := hwf.2.2.1; have := hcore.lengths.arena_len_le
                            dsimp only [minLitState]; have := hcore.lengths.arena_len_arr; omega
                          ml_lets; rw [wp]
                          refine ⟨_, c0_load_arena_arena
                            (s := minLitState s mrk1 mstk2 mclr1 mcl1 mcf1)
                            (i := rsn.setWidth 64 + BitVec.signExtend 64 (3 : BitVec 32) +
                              pos.setWidth 64) har_bd hm_p', ?_⟩
                          ml_lets; apply hJl
                          refine ⟨rfl, ?_⟩
                          have har_bd' : rsn.toNat + 3 + pos.toNat < s.arena.length := by
                            rw [← bv64_rsn_add3_pos]; exact har_bd
                          dsimp only [minLitRsnLit]
                          simp only [eq_false hbin_f, ↓reduceIte, bv64_rsn_add3_pos]
                          rw [List.getElem?_eq_getElem har_bd', Option.getD_some]; rfl
                    · have hpos_ge' : sz.toNat ≤ pos.toNat := by
                        change pos.ult sz = false at hpos_ge
                        rw [BitVec.ult, decide_eq_false_iff_not, not_lt] at hpos_ge; exact hpos_ge
                      ml_lets; ml_jnz; refine ⟨fun hsp0 => ?_, fun hsp_pos => ?_⟩
                      · ml_lets; apply hB
                        c0_cond hsp0
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
                        refine plainMinMarkSpec_zero_inv hcore hsi.mrk_len hsi.mstk_len hsi.mclr_len
                          hsi.mcl_le hm' hv_lt hz_v ((2 : BitVec 32).setWidth 8) fun m4 hm4 => ?_
                        ml_lets
                        have h2_eq : (2 : BitVec 32).setWidth 8 = 2#8 := rfl
                        rw [h2_eq] at hm4
                        let st_p := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
                        let st4 := plainMinMarkState c st_p v.toNat 2#8
                        have hcore_p := hsi.core hcore
                        have hhrsn := frameCov_to_hrsn hcore (hstk.bd sp.toNat hsp_idxs)
                          hcov_sp (by rw [← hrsn_eq, ← hsz_eq]; exact hpos_ge')
                        have hno8_v : (st_p.mrk[(s.trl[idxs[sp.toNat]'hsp_idxs]?.getD
                            0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8 := by
                          have h1 : st_p.mrk[v.toNat]?.getD 0#8 = 0#8 := hz_v
                          rw [← hv_nat, h1]; rfl
                        have hv_eq' : (s.trl[idxs[sp.toNat]'hsp_idxs]?.getD 0#32).toNat / 2 =
                            v.toNat := hv_nat.symm
                        have hmin4 : PlainMinMarkInv c F0 st4 keepSet := by
                          simpa only [st4, hv_eq'] using
                            plainMinMarkInv_mark_rem hcore_p hsi.min_inv
                              (hstk.bd sp.toNat hsp_idxs) hno8_v hhrsn
                        obtain ⟨hsi4, hmono_step⟩ := minLitStInv_mark hsi hv_lt hz_v 2#8
                          (Or.inl rfl) hmin4
                        have hstk4 := minLitStkInv_pop hcore hstk hsp_gt0 hmono_step
                          (by rw [← hv_nat]; dsimp only [st4, plainMinMarkState]
                              rw [List.getElem?_set_self (by rw [hsi.mrk_len]; exact hv_lt)]
                              rw [Option.getD_some, hz_v]; decide)
                          (fun k hk => by
                            have hne : (s.trl[idxs[k]]?.getD 0#32).toNat / 2 ≠ v.toNat := by
                              rw [hv_nat]
                              exact minLitStkInv_var_ne hcore hstk (by rw [hstk.len]; omega)
                                hsp_idxs (by omega)
                            dsimp only [st4, plainMinMarkState]
                            rw [List.getElem?_set_ne (Ne.symm hne)])
                        have hsp_m1 : (sp - 1).toNat = sp.toNat - 1 := by
                          have h1 : (1 : BitVec 64).toNat = 1 := rfl
                          rw [BitVec.toNat_sub]; bv_omega
                        exact hL (maxSteps - (steps + 1).toNat) (sp - 1, steps + 1, ()) m4 hdec_n
                          ⟨by bv_omega, by omega, rfl, st4.mrk, mstk1, st4.min_clr,
                            st4.min_clr_len, st4.min_clr_full, idxs.take sp.toNat,
                            hsi4, hm4, by rwa [hsp_m1]⟩
                  · rintro Jsz hJsz; ml_lets
                    ml_jnz; refine ⟨fun hbin => ?_, fun hbig => ?_⟩
                    · ml_lets; apply hJsz
                      have hbin' : (rsn &&& 0x80000000#32) ≠ 0#32 := by
                        change ((rsn &&& 0x80000000#32) != 0#32) = true at hbin
                        c0_cond hbin; exact hbin
                      exact ⟨rfl, by simp only [eq_true hbin', ↓reduceIte]; rfl, le_refl _⟩
                    · have hbin_f : ¬ (rsn &&& 0x80000000#32) ≠ 0#32 := by
                        change ((rsn &&& 0x80000000#32) != 0#32) = false at hbig
                        c0_cond hbig; intro hne; exact hne hbig
                      dsimp only [FrameCov] at hcov_sp
                      rcases hcov_sp with ⟨_, hif⟩
                      simp only [← hrsn_eq, eq_false hbin_f, ↓reduceIte] at hif
                      have hwf := hcore.arena.refs_wf _ hif.1
                      ml_lets; rw [wp]; refine ⟨_, load_arena_len hm', ?_⟩
                      ml_lets; ml_jnz; refine ⟨fun har1 => ?_, fun _ => ?_⟩
                      · exfalso
                        change (BitVec.ofNat 64 s.arena_len).ult
                          (rsn.setWidth 64 + BitVec.signExtend 64 (3 : BitVec 32)) = true at har1
                        have h3 : (BitVec.signExtend 64 (3 : BitVec 32) : BitVec 64).toNat = 3 := by
                          decide
                        c0_cond har1
                        rw [h3] at har1
                        have := hwf.2.2.1; have := hwf.2.2.2.1; have := hwf.2.1
                        have := hcore.lengths.arena_len_le; have := c.harena
                        unfold dimacsBound at *; have := rsn.isLt; bv_omega
                      · have har2 : (rsn.setWidth 64 + BitVec.signExtend 64 (2 : BitVec 32)).toNat <
                            (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1).arena.length := by
                          rw [bv64_rsn_add2]
                          have := hwf.2.2.1; have := hcore.lengths.arena_len_le
                          dsimp only [minLitState]; have := hcore.lengths.arena_len_arr; omega
                        ml_lets; rw [wp]
                        refine ⟨_, c0_load_arena_arena
                          (s := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1)
                          (i := rsn.setWidth 64 + BitVec.signExtend 64 (2 : BitVec 32))
                          har2 hm', ?_⟩
                        let sz := s.arena[(rsn.setWidth 64 +
                          BitVec.signExtend 64 (2 : BitVec 32)).toNat]'har2
                        have har2_s : (rsn.setWidth 64 +
                            BitVec.signExtend 64 (2 : BitVec 32)).toNat < s.arena.length := har2
                        have hsz_e : sz.toNat = arenaClauseSize s rsn.toNat := by
                          have hopt : s.arena[(rsn.setWidth 64 +
                              BitVec.signExtend 64 (2 : BitVec 32)).toNat]? =
                              s.arena[rsn.toNat + 2]? := by rw [bv64_rsn_add2]
                          rw [List.getElem?_eq_getElem har2_s] at hopt
                          exact congrArg (fun o => (o.getD 0#32).toNat) hopt
                        ml_lets; ml_jnz; refine ⟨fun hsz3 => ?_, fun _ => ?_⟩
                        · exfalso
                          rw [BitVec.ult, decide_eq_true_eq] at hsz3
                          have h3 : (3 : BitVec 32).toNat = 3 := rfl
                          rw [h3, hsz_e] at hsz3
                          have := hwf.2.1; omega
                        · ml_lets; rw [wp]; refine ⟨_, load_arena_len hm', ?_⟩
                          ml_lets; ml_jnz; refine ⟨fun har_oob => ?_, fun _ => ?_⟩
                          · exfalso
                            change (BitVec.ofNat 64 s.arena_len).ult
                              (rsn.setWidth 64 + 3 + sz.setWidth 64) = true at har_oob
                            have := hwf.2.2.1; have := hwf.2.2.2.1
                            have := hcore.lengths.arena_len_le; have := c.harena
                            unfold dimacsBound at *; have := rsn.isLt; have := sz.isLt
                            c0_cond har_oob; rw [hsz_e] at har_oob; bv_omega
                          · ml_lets; apply hJsz
                            have har2' : rsn.toNat + 2 < s.arena.length := by
                              rw [← bv64_rsn_add2]; exact har2
                            refine ⟨rfl, ?_, ?_⟩
                            · simp only [eq_false hbin_f, ↓reduceIte, Arg.val_var]
                              exact hsz_e
                            · simp only [Arg.val_var]
                              rw [hsz_e]; have := hwf.2.1; omega
            · ml_lets; apply hB
              exact ⟨mrk1, mstk1, mclr1, mcl1, mcf1, hsi, hm',
                ⟨hsp_lt, idxs, minLitStkInv_drop_cov hstk⟩⟩
          · rintro B L hB hL; ml_lets
            have hmd := plainMinDepthOf_pos c.mv
            have hms_lt : ((BitVec.ofNat 64 s.arena_len + BitVec.ofNat 64 c.mv) * 4 + 64).toNat =
                maxSteps := minLit_maxSteps_toNat hcore.lengths.arena_len_le
            let mstk0 := (s.min_stk.set 0 (root_lit >>> 1)).set 1 0#32
            have hmstkl' : mstk0.length = 2 * c.minDepth := by simp [mstk0, hmstkl]
            have hstk0 : MinLitStkInv c s mstk0 s.mrk 0 idx0 [idx0] true := by
              refine ⟨rfl, rfl, fun k hk => ?_, fun k hk => by simp at hk, fun k hk => ?_,
                fun _ k hk => ?_⟩
              · have hk0 : k = 0 := by simp at hk; omega
                subst k; exact hi0
              · have hk0 : k = 0 := by simp at hk; omega
                subst k
                rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by
                  unfold PlainCfg.minDepth at *; omega), Option.getD_some]
                refine ⟨?_, fun h1 => by omega⟩
                have hl := litVar_litNeg root_lit.toNat; unfold litVar litNeg at hl
                simp only [List.getElem_cons_zero]
                rw [hi0_eq, hl, bv32_lshr_1]
              · have hk0 : k = 0 := by simp at hk; omega
                subst k
                rw [List.getElem?_set_self (by simp; unfold PlainCfg.minDepth at *; omega),
                  Option.getD_some]
                refine ⟨fun hk1 => by simp at hk1, ?_⟩
                simp only [List.length_singleton, ↓reduceIte, BitVec.toNat_ofNat]
                exact frameCov_zero hcore s.mrk hi0 hrsn_ne0
            have hsi0 : MinLitStInv c F0 s keepSet s.mrk mstk0 s.min_clr s.min_clr_len
                s.min_clr_full :=
              ⟨hcore.lengths.mrk_len, hmstkl', hcore.lengths.min_clr_len_arr,
                hcore.lengths.min_clr_len_le, minMarkInv_with_mstk hmin mstk0,
                fun _ _ h => h, fun _ _ => rfl⟩
            have hm1' : (PlainMem c (minLitState s s.mrk mstk0 s.min_clr s.min_clr_len
                s.min_clr_full) ⋆ R) (storeMem (storeMem m i32
                  (c.pMinStk + (BitVec.signExtend 64 (0 : BitVec 32) : BitVec 64) * 4)
                  (root_lit >>> 1)) i32
                  (c.pMinStk + (BitVec.signExtend 64 (1 : BitVec 32) : BitVec 64) * 4) 0) := by
              have h0 : (BitVec.signExtend 64 (0 : BitVec 32) : BitVec 64) * (4 : BitVec 64) =
                  0#64 := rfl
              have h1 : (BitVec.signExtend 64 (1 : BitVec 32) : BitVec 64) * (4 : BitVec 64) =
                  BitVec.ofNat 64 (4 * 1) := rfl
              rw [h0, h1]
              exact hm1
            exact hL maxSteps (0#64, 0#64, ()) _
              ⟨hmd, Nat.zero_le _, rfl, s.mrk, mstk0,
                s.min_clr, s.min_clr_len, s.min_clr_full, [idx0],
                hsi0, hm1', hstk0⟩

end LeanQbe.T.Examples.Kissat.Plain
