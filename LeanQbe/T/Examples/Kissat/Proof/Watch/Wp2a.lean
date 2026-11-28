/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Helpers
public import LeanQbe.T.Examples.Kissat.Src.Watch

import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1

/-! # Watch WP Proofs Part 2a: Helper Lemmas and Invariants for `full_wstack_defrag_m6`

Self-contained pure/separation/invariant helpers imported by `Proof.Watch.Wp2`. -/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec

public section

/-! ## 1. Pure Array, Separation, & Defrag Math Helpers -/

theorem array32_split_4 {a : BitVec 64} {xs : List (Val i32)} {k1 k2 k3 : Nat}
    (h1 : k1 ≤ k2) (h2 : k2 ≤ k3) (h3 : k3 ≤ xs.length) :
    array a xs =
      (array a (xs.take k1) ⋆
       array (a + BitVec.ofNat 64 (4 * k1)) ((xs.drop k1).take (k2 - k1)) ⋆
       array (a + BitVec.ofNat 64 (4 * k2)) ((xs.drop k2).take (k3 - k2)) ⋆
       array (a + BitVec.ofNat 64 (4 * k3)) (xs.drop k3)) := by
  have ha := array_i32_split_at (a := a) (xs := xs) k1
  rw [show (xs.take k1).length = k1 by rw [List.length_take]; omega] at ha
  have hb := array_i32_split_at (a := a + BitVec.ofNat 64 (4 * k1)) (xs := xs.drop k1) (k2 - k1)
  rw [show ((xs.drop k1).take (k2 - k1)).length = k2 - k1 by
      rw [List.length_take, List.length_drop]; omega,
    List.drop_drop, show k1 + (k2 - k1) = k2 by omega, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * k1 + 4 * (k2 - k1) = 4 * k2 by omega] at hb
  have hc := array_i32_split_at (a := a + BitVec.ofNat 64 (4 * k2)) (xs := xs.drop k2) (k3 - k2)
  rw [show ((xs.drop k2).take (k3 - k2)).length = k3 - k2 by
      rw [List.length_take, List.length_drop]; omega,
    List.drop_drop, show k2 + (k3 - k2) = k3 by omega, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * k2 + 4 * (k3 - k2) = 4 * k3 by omega] at hc
  rw [ha, hb, hc, sep_assoc, sep_assoc]

theorem wsort_extract_swap_step {wvec ws : List (BitVec 32)} {e n : Nat}
    (hmax : FullWsortMaxHeap wvec ws 0 (e + 1))
    (hsp : SplitLe (Spec.fullWvecOff wvec) ws (e + 1) n)
    (hsrt : Spec.SortedRange (Spec.fullWvecOff wvec) ws (e + 1) n)
    (he_pos : 0 < e) (he_lt : e < n) (hn_len : n ≤ ws.length) :
    FullWsortMaxHeap wvec (swapIdx ws 0 e) 1 e ∧
    SplitLe (Spec.fullWvecOff wvec) (swapIdx ws 0 e) e n ∧
    Spec.SortedRange (Spec.fullWvecOff wvec) (swapIdx ws 0 e) e n := by
  let ws' := swapIdx ws 0 e
  have hsw (k : Nat) : Spec.wsVal ws' k =
      if k = 0 then Spec.wsVal ws e else if k = e then Spec.wsVal ws 0 else Spec.wsVal ws k :=
    wsVal_swap (by omega) (by omega)
  have hroot := wsortMaxHeap_root_ge hmax (Nat.succ_pos e)
  refine ⟨fun i hi1 hi2 => ?_, fun i hi j hj1 hj2 => ?_, fun i j hi hij hj => ?_⟩
  · have hhi := hmax i (by omega) (by omega)
    change (2 * i + 1 < e → Spec.fullWvecOff wvec (Spec.wsVal ws' (2 * i + 1)) ≤
        Spec.fullWvecOff wvec (Spec.wsVal ws' i)) ∧
      (2 * i + 2 < e → Spec.fullWvecOff wvec (Spec.wsVal ws' (2 * i + 2)) ≤
        Spec.fullWvecOff wvec (Spec.wsVal ws' i))
    rw [hsw i, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact ⟨fun hc1 => by
        rw [hsw _, ite_eq_right (by omega), ite_eq_right (by omega)]; exact hhi.1 (by omega),
      fun hc2 => by
        rw [hsw _, ite_eq_right (by omega), ite_eq_right (by omega)]; exact hhi.2 (by omega)⟩
  · by_cases hje : j = e
    · rw [hje, hsw e, ite_eq_right (by omega), ite_eq_left rfl, hsw i]
      by_cases hi0 : i = 0
      · simp [hi0, hroot e (by omega)]
      · rw [ite_eq_right hi0, ite_eq_right (by omega)]; exact hroot i (by omega)
    · rw [hsw j, ite_eq_right (by omega), ite_eq_right hje, hsw i]
      split
      · exact hsp e (by omega) j (by omega) hj2
      · rw [ite_eq_right (by omega)]; exact hsp i (by omega) j (by omega) hj2
  · by_cases hie : i = e
    · by_cases hje : j = e
      · rw [hie, hje]; exact Nat.le_refl _
      · rw [hie, hsw e, ite_eq_right (by omega), ite_eq_left rfl,
          hsw j, ite_eq_right (by omega), ite_eq_right hje]
        exact hsp 0 (Nat.succ_pos e) j (by omega) hj
    · rw [hsw i, ite_eq_right (by omega), ite_eq_right hie,
        hsw j, ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hsrt i j (by omega) hij hj

theorem wsort_extract_perm_post {key : Nat → Nat} {ws' wsSwap : List (BitVec 32)}
    {e n : Nat} (hsuf : ∀ i, e ≤ i → ws'[i]? = wsSwap[i]?)
    (hsp : SplitLe key wsSwap e n) (hsrt : Spec.SortedRange key wsSwap e n)
    (hperm : (ws'.take e).Perm (wsSwap.take e)) (he_le : e ≤ ws'.length)
    (he_le_sw : e ≤ wsSwap.length) :
    SplitLe key ws' e n ∧ Spec.SortedRange key ws' e n := by
  have hval_eq (i : Nat) (hi : e ≤ i) : Spec.wsVal ws' i = Spec.wsVal wsSwap i := by
    unfold Spec.wsVal; rw [hsuf i hi]
  refine ⟨fun i hi j hj1 hj2 => ?_, fun i j hi hij hj => ?_⟩
  · have hin : ws'[i]'(by omega) ∈ wsSwap.take e :=
      hperm.mem_iff.mp (by
        have hmem := List.getElem_mem (l := ws'.take e)
          (by rw [List.length_take]; omega : i < (ws'.take e).length)
        simpa [List.getElem_take] using hmem)
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hin
    have hke : k < e := by simp [he_le_sw] at hk; exact hk
    rw [List.getElem_take] at hkeq
    have hvk : Spec.wsVal ws' i = Spec.wsVal wsSwap k := by
      unfold Spec.wsVal
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), hkeq]
    rw [hvk, hval_eq j hj1]; exact hsp k hke j hj1 hj2
  · rw [hval_eq i hi, hval_eq j (by omega)]; exact hsrt i j hi hij hj

theorem defrag_sorted_gap {s : FullState} {wsort2 : List (BitVec 32)} {i j n : Nat}
    (hlay : WatchStackLayout s.core)
    (hcov : WsCovers wsort2 n (2 * s.core.cur_vars) (fullWatchSize s))
    (hsrt : Spec.SortedRange (fullWatchOff s) wsort2 0 n) (hij : i < j) (hjn : j < n) :
    fullWatchOff s (Spec.wsVal wsort2 i) + fullWatchSize s (Spec.wsVal wsort2 i) ≤
      fullWatchOff s (Spec.wsVal wsort2 j) := by
  have hi_cov := hcov.1 i (by omega); have hj_cov := hcov.1 j hjn
  have hle := hsrt i j (Nat.zero_le _) (by omega) hjn
  have hdisj := hlay.disjoint _ _ hi_cov.1 hj_cov.1
    (hcov.2.1 i (by omega) j hjn (by omega)) hi_cov.2 hj_cov.2
  dsimp only [fullWatchOff, fullWatchSize] at hle ⊢
  rcases hdisj with h | h
  · exact h
  · have := hj_cov.2; unfold fullWatchSize at this; omega

@[expose] def DefragCopied (s : FullState) (wvec wstk wsort2 : List (BitVec 32))
    (p i n : Nat) : Prop :=
  (∀ j < 2 * s.core.cur_vars, (wvec[2 * j + 1]?.getD 0#32).toNat = fullWatchSize s j) ∧
  (∀ j < 2 * s.core.cur_vars, fullWatchSize s j = 0 → (wvec[2 * j]?.getD 0#32).toNat = 0) ∧
  (∀ j < i, let l := Spec.wsVal wsort2 j; let off := (wvec[2 * l]?.getD 0#32).toNat
    1 ≤ off ∧ off + fullWatchSize s l ≤ p ∧
    ∀ k < fullWatchSize s l, wstk[off + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
  (∀ a < i, ∀ b < i, a ≠ b →
    let la := Spec.wsVal wsort2 a; let lb := Spec.wsVal wsort2 b
    (wvec[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤ (wvec[2 * lb]?.getD 0#32).toNat ∨
    (wvec[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤ (wvec[2 * la]?.getD 0#32).toNat) ∧
  (∀ j, i ≤ j → j < n → let l := Spec.wsVal wsort2 j
    (wvec[2 * l]?.getD 0#32).toNat = fullWatchOff s l ∧
    ∀ k < fullWatchSize s l, wstk[fullWatchOff s l + k]? = s.core.wstk[fullWatchOff s l + k]?)

theorem defrag_finalize {s : FullState} {wvecC wstkC wsort2 : List (BitVec 32)}
    {n p : Nat} (hlay : WatchStackLayout s.core)
    (hcov : WsCovers wsort2 n (2 * s.core.cur_vars) (fullWatchSize s)) (_hp1 : 1 ≤ p)
    (hcop : DefragCopied s wvecC wstkC wsort2 p n n) :
    let k' : FullCoreState :=
      { s.core with wvec := wvecC, wstk := wstkC, wlen := p, wusable := 0#64 }
    WatchStackLayout k' ∧
    ∀ l < 2 * s.core.cur_vars, fullWatchSizeCore k' l = fullWatchSize s l ∧
      ∀ k < fullWatchSize s l, k'.wstk[fullWatchOffCore k' l + k]? =
        s.core.wstk[fullWatchOff s l + k]? := by
  intro k'
  obtain ⟨hszC, hzeroC, hdoneC, hdisjC, _⟩ := hcop
  have hof_done := hcov.2.2
  have hslice_eq : ∀ l < 2 * s.core.cur_vars,
      ∀ k < fullWatchSize s l, k'.wstk[fullWatchOffCore k' l + k]? =
        s.core.wstk[fullWatchOff s l + k]? := fun l hl k hk => by
    obtain ⟨j, hj, rfl⟩ := hof_done l hl (by omega); exact (hdoneC j hj).2.2 k hk
  refine ⟨⟨fun l hl => ?_, fun l hl hp => ?_, fun l1 l2 h1 h2 hne hp1' hp2' => ?_,
    fun l hl idx hidx => ?_⟩, fun l hl => ⟨hszC l hl, hslice_eq l hl⟩⟩
  · rw [show fullWatchSizeCore k' l = fullWatchSize s l from hszC l hl]
    by_cases hzp : fullWatchSize s l = 0
    · rw [hzp, Nat.add_zero]; unfold fullWatchOffCore; rw [hzeroC l hl hzp]; omega
    · obtain ⟨j, hj, rfl⟩ := hof_done l hl (by omega); exact (hdoneC j hj).2.1
  · rw [show fullWatchSizeCore k' l = fullWatchSize s l from hszC l hl] at hp
    obtain ⟨j, hj, rfl⟩ := hof_done l hl hp; exact (hdoneC j hj).1
  · rw [show fullWatchSizeCore k' l1 = fullWatchSize s l1 from hszC l1 h1] at hp1' ⊢
    rw [show fullWatchSizeCore k' l2 = fullWatchSize s l2 from hszC l2 h2] at hp2' ⊢
    obtain ⟨ja, hja, rfl⟩ := hof_done l1 h1 hp1'
    obtain ⟨jb, hjb, rfl⟩ := hof_done l2 h2 hp2'
    exact hdisjC ja hja jb hjb (fun h => hne (by rw [h]))
  · rw [show fullWatchSizeCore k' l = fullWatchSize s l from hszC l hl] at hidx
    rw [hslice_eq l hl idx hidx]; exact hlay.no_sentinel l hl idx hidx

@[expose] def FullWvecWsortRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  array (t := i32) c.pWstk s.core.wstk ⋆ FullRestNoWatch c s

theorem fullMem_eq_wvec_wsort_rest (c : FullCfg) (s : FullState) :
    FullMem c s = (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆ FullWvecWsortRest c s) := by
  rw [fullMem_eq_wvec_wsort_wstk]; unfold FullWvecWsortRest; rw [sep_assoc]

theorem focus_wvec_wsort {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pWsort s.scratch.wsort ⋆
      (FullWvecWsortRest c s ⋆ R)) m := by
  have heq : (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆ FullWvecWsortRest c s ⋆ R) =
      (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pWsort s.scratch.wsort ⋆
        (FullWvecWsortRest c s ⋆ R)) := by ac_rfl
  rw [fullMem_eq_wvec_wsort_rest, sep_assoc] at hm
  exact heq ▸ hm

theorem unfocus_wvec_wsort {c : FullCfg} {s : FullState}
    {wsort' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pWsort wsort' ⋆
      (FullWvecWsortRest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with wsort := wsort' } } ⋆ R) m := by
  have hreq : FullWvecWsortRest c { s with scratch := { s.scratch with wsort := wsort' } } =
      FullWvecWsortRest c s := rfl
  have heq : (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort wsort' ⋆ (FullWvecWsortRest c s ⋆ R)) =
      (array (t := i32) c.pWvec s.core.wvec ⋆
        array (t := i32) c.pWsort wsort' ⋆ FullWvecWsortRest c s ⋆ R) := by ac_rfl
  rw [fullMem_eq_wvec_wsort_rest]; dsimp only; rw [hreq, sep_assoc]; exact heq ▸ hm

private theorem sep_rw_ac {k v : Type} [BEq k] [Hashable k] [EquivBEq k] [LawfulBEq k]
    {P Q : Std.ExtHashMap k v → Prop} {m : Std.ExtHashMap k v} (h : P = Q) (hp : P m) : Q m :=
  h ▸ hp

theorem full_wvec_wsort_split4 {c : FullCfg} {s : FullState} {n : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (h2n : 2 * n + 256 ≤ 2 * c.max_vars)
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort (s.scratch.wsort.take n) ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n))
        ((s.scratch.wsort.drop n).take n) ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n)))
        ((s.scratch.wsort.drop (2 * n)).take 256) ⋆
      (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n + 256)))
        (s.scratch.wsort.drop (2 * n + 256)) ⋆ FullWvecWsortRest c s ⋆ R)) m := by
  have hws : s.scratch.wsort.length = 2 * c.max_vars := hlen.scratch_ok.wsort_len
  have hm1 := focus_wvec_wsort hm
  rw [array32_split_4 (a := c.pWsort) (xs := s.scratch.wsort) (k1 := n) (k2 := 2 * n)
    (k3 := 2 * n + 256) (by omega) (by omega) (by rw [hws]; exact h2n)] at hm1
  simp only [show 2 * n - n = n by omega, show 2 * n + 256 - 2 * n = 256 by omega] at hm1
  exact sep_rw_ac (by ac_rfl) hm1

theorem full_wvec_wsort_unsplit4 {c : FullCfg} {s : FullState} {n : Nat}
    {ws1 tmp1 cnt1 : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (h2n : 2 * n + 256 ≤ 2 * c.max_vars)
    (hws1 : ws1.length = n) (htmp1 : tmp1.length = n) (hcnt1 : cnt1.length = 256)
    (hm : (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort ws1 ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) tmp1 ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n))) cnt1 ⋆
      (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n + 256)))
        (s.scratch.wsort.drop (2 * n + 256)) ⋆ FullWvecWsortRest c s ⋆ R)) m) :
    let wsort' := ws1 ++ tmp1 ++ cnt1 ++ s.scratch.wsort.drop (2 * n + 256)
    wsort'.length = 2 * c.max_vars ∧ wsort'.take n = ws1 ∧
    (FullMem c { s with scratch := { s.scratch with wsort := wsort' } } ⋆ R) m := by
  have hws : s.scratch.wsort.length = 2 * c.max_vars := hlen.scratch_ok.wsort_len
  let wsort' := ws1 ++ tmp1 ++ cnt1 ++ s.scratch.wsort.drop (2 * n + 256)
  have hlen' : wsort'.length = 2 * c.max_vars := by
    simp [wsort', hws1, htmp1, hcnt1, List.length_drop, hws]; omega
  have htk' : wsort'.take n = ws1 := by simp [wsort', List.append_assoc, hws1]
  have hre : array (t := i32) c.pWsort wsort' =
      (array (t := i32) c.pWsort ws1 ⋆
       array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) tmp1 ⋆
       array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n))) cnt1 ⋆
       array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n + 256)))
         (s.scratch.wsort.drop (2 * n + 256))) := by
    dsimp only [wsort']; rw [array_append, array_append, array_append]
    simp only [Ty.bytes, Ty.size, i32, List.length_append, hws1, htmp1, hcnt1,
      show (32 + 7) / 8 = 4 from rfl]
    have hmul2 : 4 * (n + n) = 4 * (2 * n) := by omega
    have hmul3 : 4 * (n + n + 256) = 4 * (2 * n + 256) := by omega
    rw [hmul2, hmul3]
  refine ⟨hlen', htk', unfocus_wvec_wsort ?_⟩
  rw [hre]; exact sep_rw_ac (by ac_rfl) hm

private theorem sep_wstk_split_ac {A B1 B2 C1 C2 C3 C4 Rest R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B1 ⋆ B2) ⋆ (C1 ⋆ C2 ⋆ C3 ⋆ C4) ⋆ Rest ⋆ R) m) :
    (A ⋆ B1 ⋆ C2 ⋆ C3 ⋆ (B2 ⋆ C1 ⋆ C4 ⋆ Rest ⋆ R)) m :=
  sep_rw_ac (by ac_rfl) h

private theorem sep_wstk_unsplit_ac {A B1 B2 C1 C2 C3 C4 Rest R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B1 ⋆ C2 ⋆ C3 ⋆ (B2 ⋆ C1 ⋆ C4 ⋆ Rest ⋆ R)) m) :
    (A ⋆ (B1 ⋆ B2) ⋆ (C1 ⋆ C2 ⋆ C3 ⋆ C4) ⋆ Rest ⋆ R) m :=
  sep_rw_ac (by ac_rfl) h

theorem full_wstack_defrag_wstk_split {c : FullCfg} {s : FullState} {n : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hn_ws : n ≤ 2 * c.max_vars)
    (hn : s.core.wlen + n + 256 ≤ c.wcap) (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort (s.scratch.wsort.take n) ⋆
      array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * s.core.wlen))
        ((s.core.wstk.drop s.core.wlen).take n) ⋆
      array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n)))
        ((s.core.wstk.drop (s.core.wlen + n)).take 256) ⋆
      (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) (s.scratch.wsort.drop n) ⋆
       array (t := i32) c.pWstk (s.core.wstk.take s.core.wlen) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n + 256)))
         (s.core.wstk.drop (s.core.wlen + n + 256)) ⋆
       FullRestNoWatch c s ⋆ R)) m := by
  have hws : s.scratch.wsort.length = 2 * c.max_vars := hlen.scratch_ok.wsort_len
  have hwst : s.core.wstk.length = c.wcap := hlen.core_ok.wstk_len_arr
  have hwle : s.core.wlen ≤ c.wcap := hlen.core_ok.wlen_le
  have hm1 := hm; rw [fullMem_eq_wvec_wsort_wstk] at hm1
  have hws_arr : array (t := i32) c.pWsort s.scratch.wsort =
      (array (t := i32) c.pWsort (s.scratch.wsort.take n) ⋆
       array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) (s.scratch.wsort.drop n)) := by
    conv => lhs; rw [← List.take_append_drop n s.scratch.wsort]
    rw [array_append]
    simp only [Ty.bytes, Ty.size, i32, List.length_take, hws,
      show min n (2 * c.max_vars) = n by omega, show (32 + 7) / 8 = 4 from rfl]
  have hwstk_arr : array (t := i32) c.pWstk s.core.wstk =
      (array (t := i32) c.pWstk (s.core.wstk.take s.core.wlen) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * s.core.wlen))
         ((s.core.wstk.drop s.core.wlen).take n) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n)))
         ((s.core.wstk.drop (s.core.wlen + n)).take 256) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n + 256)))
         (s.core.wstk.drop (s.core.wlen + n + 256))) := by
    rw [array32_split_4 (a := c.pWstk) (xs := s.core.wstk) (k1 := s.core.wlen)
      (k2 := s.core.wlen + n) (k3 := s.core.wlen + n + 256)
      (by omega) (by omega) (by rw [hwst]; exact hn)]
    simp only [show s.core.wlen + n - s.core.wlen = n by omega,
      show s.core.wlen + n + 256 - (s.core.wlen + n) = 256 by omega]
  rw [hws_arr, hwstk_arr] at hm1
  exact sep_wstk_split_ac hm1

theorem full_wstack_defrag_wstk_unsplit {c : FullCfg} {s : FullState} {n : Nat}
    {ws1 tmp1 cnt1 : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hn_ws : n ≤ 2 * c.max_vars)
    (hn : s.core.wlen + n + 256 ≤ c.wcap)
    (hws1 : ws1.length = n) (htmp1 : tmp1.length = n) (hcnt1 : cnt1.length = 256)
    (hm : (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort ws1 ⋆
      array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * s.core.wlen)) tmp1 ⋆
      array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n))) cnt1 ⋆
      (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) (s.scratch.wsort.drop n) ⋆
       array (t := i32) c.pWstk (s.core.wstk.take s.core.wlen) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n + 256)))
         (s.core.wstk.drop (s.core.wlen + n + 256)) ⋆
       FullRestNoWatch c s ⋆ R)) m) :
    let wsort' := ws1 ++ s.scratch.wsort.drop n
    let wstk' := s.core.wstk.take s.core.wlen ++ tmp1 ++ cnt1 ++
      s.core.wstk.drop (s.core.wlen + n + 256)
    wsort'.length = 2 * c.max_vars ∧ wstk'.length = c.wcap ∧ wsort'.take n = ws1 ∧
    (∀ k < s.core.wlen, wstk'[k]? = s.core.wstk[k]?) ∧
    (FullMem c { s with core := { s.core with wstk := wstk' }
                        scratch := { s.scratch with wsort := wsort' } } ⋆ R) m := by
  have hws : s.scratch.wsort.length = 2 * c.max_vars := hlen.scratch_ok.wsort_len
  have hwst : s.core.wstk.length = c.wcap := hlen.core_ok.wstk_len_arr
  have hwle : s.core.wlen ≤ c.wcap := hlen.core_ok.wlen_le
  let wsort' := ws1 ++ s.scratch.wsort.drop n
  let wstk' := s.core.wstk.take s.core.wlen ++ tmp1 ++ cnt1 ++
    s.core.wstk.drop (s.core.wlen + n + 256)
  have hlen_ws : wsort'.length = 2 * c.max_vars := by
    simp [wsort', hws1, List.length_drop, hws]; omega
  have hlen_stk : wstk'.length = c.wcap := by
    simp [wstk', htmp1, hcnt1, List.length_take, List.length_drop, hwst]; omega
  have htk_ws : wsort'.take n = ws1 := by simp [wsort', hws1]
  have hpre_stk : ∀ k < s.core.wlen, wstk'[k]? = s.core.wstk[k]? := by
    intro k hk
    have hlt1 : k < (s.core.wstk.take s.core.wlen).length := by rw [List.length_take]; omega
    dsimp only [wstk']
    rw [List.append_assoc, List.append_assoc, List.getElem?_append_left hlt1,
      List.getElem?_eq_getElem hlt1, List.getElem_take, List.getElem?_eq_getElem (by omega)]
  have hre_ws : array (t := i32) c.pWsort wsort' =
      (array (t := i32) c.pWsort ws1 ⋆
       array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) (s.scratch.wsort.drop n)) := by
    dsimp only [wsort']; rw [array_append]
    simp [Ty.bytes, Ty.size, i32, hws1, show (32 + 7) / 8 = 4 from rfl]
  have hre_stk : array (t := i32) c.pWstk wstk' =
      (array (t := i32) c.pWstk (s.core.wstk.take s.core.wlen) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * s.core.wlen)) tmp1 ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n))) cnt1 ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n + 256)))
         (s.core.wstk.drop (s.core.wlen + n + 256))) := by
    dsimp only [wstk']; rw [array_append, array_append, array_append]
    have hlt1 : (s.core.wstk.take s.core.wlen).length = s.core.wlen := by
      rw [List.length_take]; omega
    simp only [Ty.bytes, Ty.size, i32, List.length_append, hlt1, htmp1, hcnt1,
      show (32 + 7) / 8 = 4 from rfl]
  refine ⟨hlen_ws, hlen_stk, htk_ws, hpre_stk, ?_⟩
  have hrest_eq : FullRestNoWatch c { s with
      core := { s.core with wstk := wstk' },
      scratch := { s.scratch with wsort := wsort' } } = FullRestNoWatch c s := rfl
  rw [fullMem_eq_wvec_wsort_wstk]; dsimp only; rw [hrest_eq, hre_ws, hre_stk]
  exact sep_wstk_unsplit_ac hm

/-! ## 2. Defrag Loop Invariants & Step Lemmas -/

@[expose] def DefragScanInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) :
    Tup Val [i64, i64, i64, i64, Ty.bool] → Mem 64 → Prop
  | (n, l, max_off, prev_off, sorted, ()), m1 =>
    l.toNat ≤ 2 * s.core.cur_vars ∧ n.toNat ≤ l.toNat ∧
    max_off.toNat ≤ c.wcap ∧ prev_off.toNat ≤ max_off.toNat ∧
    ∃ (wvec1 wsort1 : List (BitVec 32)),
      wvec1.length = 4 * c.max_vars ∧ wsort1.length = 2 * c.max_vars ∧
      (∀ j < 2 * s.core.cur_vars, wvec1[2 * j + 1]? = s.core.wvec[2 * j + 1]?) ∧
      (∀ j < 2 * s.core.cur_vars,
        0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?) ∧
      (∀ j < l.toNat, fullWatchSize s j = 0 → wvec1[2 * j]? = some 0#32) ∧
      WsCovers wsort1 n.toNat l.toNat (fullWatchSize s) ∧
      (∀ j < n.toNat, fullWatchOff s (Spec.wsVal wsort1 j) ≤ max_off.toNat) ∧
      (sorted = true → Spec.SortedRange (fullWatchOff s) wsort1 0 n.toNat ∧
        ∀ j < n.toNat, fullWatchOff s (Spec.wsVal wsort1 j) ≤ prev_off.toNat) ∧
      (FullMem c { s with core := { s.core with wvec := wvec1 },
                          scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m1

@[expose] def DefragCompactInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (n : Nat) (wsort2 : List (BitVec 32)) : Tup Val [i64, i64] → Mem 64 → Prop
  | (p, i, ()), mC =>
    1 ≤ p.toNat ∧ p.toNat ≤ s.core.wlen ∧ i.toNat ≤ n ∧
    (i.toNat < n → p.toNat ≤ fullWatchOff s (Spec.wsVal wsort2 i.toNat)) ∧
    ∃ wvecC wstkC : List (BitVec 32), wvecC.length = 4 * c.max_vars ∧
      wstkC.length = c.wcap ∧ DefragCopied s wvecC wstkC wsort2 p.toNat i.toNat n ∧
      (FullMem c { s with core := { s.core with wvec := wvecC, wstk := wstkC },
                          scratch := { s.scratch with wsort := wsort2 } } ⋆ R) mC

@[expose] def DefragSortPost (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (wvec1 : List (BitVec 32)) (n : Nat) (_ : Tup Val []) (m2 : Mem 64) : Prop :=
  ∃ wstk2 wsort2 : List (BitVec 32),
    wstk2.length = c.wcap ∧ wsort2.length = 2 * c.max_vars ∧
    (∀ i < s.core.wlen, wstk2[i]? = s.core.wstk[i]?) ∧
    WsCovers wsort2 n (2 * s.core.cur_vars) (fullWatchSize s) ∧
    Spec.SortedRange (fullWatchOff s) wsort2 0 n ∧
    (FullMem c { s with core := { s.core with wvec := wvec1, wstk := wstk2 },
                        scratch := { s.scratch with wsort := wsort2 } } ⋆ R) m2

@[expose] def DefragHeapInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (wvec1 : List (BitVec 32)) (n : Nat) : Tup Val [i64] → Mem 64 → Prop
  | (st, ()), mB =>
    st.toNat ≤ n ∧ ∃ wsB : List (BitVec 32),
      wsB.length = 2 * c.max_vars ∧
      WsCovers wsB n (2 * s.core.cur_vars) (fullWatchSize s) ∧
      FullWsortMaxHeap wvec1 wsB st.toNat n ∧
      (FullMem c { s with core := { s.core with wvec := wvec1 },
                          scratch := { s.scratch with wsort := wsB } } ⋆ R) mB

@[expose] def DefragExtractInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (wvec1 : List (BitVec 32)) (n : Nat) : Tup Val [i64] → Mem 64 → Prop
  | (e, ()), mE =>
    e.toNat < n ∧ ∃ wsE : List (BitVec 32),
      wsE.length = 2 * c.max_vars ∧
      WsCovers wsE n (2 * s.core.cur_vars) (fullWatchSize s) ∧
      FullWsortMaxHeap wvec1 wsE 0 (e.toNat + 1) ∧
      SplitLe (Spec.fullWvecOff wvec1) wsE (e.toNat + 1) n ∧
      Spec.SortedRange (Spec.fullWvecOff wvec1) wsE (e.toNat + 1) n ∧
      (FullMem c { s with core := { s.core with wvec := wvec1 },
                          scratch := { s.scratch with wsort := wsE } } ⋆ R) mE

@[expose] def DefragCopyPost (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (wsort2 : List (BitVec 32)) (i p n : Nat) (_ : Tup Val []) (mD : Mem 64) : Prop :=
  ∃ (wvecD wstkD : List (BitVec 32)),
    wvecD.length = 4 * c.max_vars ∧ wstkD.length = c.wcap ∧
    DefragCopied s wvecD wstkD wsort2 (p + fullWatchSize s (Spec.wsVal wsort2 i)) (i + 1) n ∧
    (FullMem c { s with core := { s.core with wvec := wvecD, wstk := wstkD },
                        scratch := { s.scratch with wsort := wsort2 } } ⋆ R) mD

@[expose] def DefragKInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (wvecC wstkC wsort2 : List (BitVec 32)) (i p : Nat) : Tup Val [i64] → Mem 64 → Prop
  | (k, ()), mK => k.toNat ≤ fullWatchSize s (Spec.wsVal wsort2 i) ∧
    ∃ wstkK : List (BitVec 32), wstkK.length = c.wcap ∧
      (∀ idx < p, wstkK[idx]? = wstkC[idx]?) ∧
      (∀ idx, fullWatchOff s (Spec.wsVal wsort2 i) + k.toNat ≤ idx →
        wstkK[idx]? = wstkC[idx]?) ∧
      (∀ r < k.toNat, wstkK[p + r]? = s.core.wstk[fullWatchOff s (Spec.wsVal wsort2 i) + r]?) ∧
      (∀ r, k.toNat ≤ r → r < fullWatchSize s (Spec.wsVal wsort2 i) →
        wstkK[fullWatchOff s (Spec.wsVal wsort2 i) + r]? =
          s.core.wstk[fullWatchOff s (Spec.wsVal wsort2 i) + r]?) ∧
      (FullMem c { s with core := { s.core with wvec := wvecC, wstk := wstkK },
                          scratch := { s.scratch with wsort := wsort2 } } ⋆ R) mK

theorem defrag_scan_step_cov {ws1 : List (BitVec 32)} {n l : Nat} {sz : Nat → Nat}
    {w : BitVec 32} (hw : w.toNat = l) (hcov1 : WsCovers ws1 n l sz)
    (hn_lt : n < ws1.length) (hszp : 0 < sz l) :
    WsCovers (ws1.set n w) (n + 1) (l + 1) sz := by
  have hws_at : ∀ k, Spec.wsVal (ws1.set n w) k = if k = n then l else Spec.wsVal ws1 k :=
    fun k => by
      unfold Spec.wsVal; by_cases hk : k = n
      · subst hk; rw [List.getElem?_set_self hn_lt, Option.getD_some, hw]; simp
      · rw [List.getElem?_set_ne (Ne.symm hk)]; simp [hk]
  refine ⟨fun i hi => by
      rw [hws_at]; split
      · exact ⟨Nat.lt_succ_self l, hszp⟩
      · have := hcov1.1 i (by omega); exact ⟨by omega, this.2⟩,
    fun a ha b hb hab => by
      rw [hws_at, hws_at]; split <;> split
      · omega
      · have := (hcov1.1 b (by omega)).1; omega
      · have := (hcov1.1 a (by omega)).1; omega
      · exact hcov1.2.1 a (by omega) b (by omega) hab,
    fun j hj hzj => by
      by_cases hjl : j = l
      · subst hjl; exact ⟨n, by omega, by rw [hws_at]; simp⟩
      · obtain ⟨i, hi, hij⟩ := hcov1.2.2 j (by omega) hzj
        exact ⟨i, by omega, by rw [hws_at]; simp [show i ≠ n by omega]; exact hij⟩⟩

theorem defrag_scan_step_sorted {ws1 : List (BitVec 32)} {key : Nat → Nat}
    {n l prev_off : Nat} {w : BitVec 32} (hw : w.toNat = l) (hn_lt : n < ws1.length)
    {sorted : Bool}
    (hsrt1 : sorted = true → Spec.SortedRange key ws1 0 n ∧
      ∀ j < n, key (Spec.wsVal ws1 j) ≤ prev_off)
    (hge_prev : prev_off ≤ key l) (hs_old : sorted = true) :
    Spec.SortedRange key (ws1.set n w) 0 (n + 1) ∧
      ∀ j < n + 1, key (Spec.wsVal (ws1.set n w) j) ≤ key l := by
  have hws_at : ∀ k, Spec.wsVal (ws1.set n w) k = if k = n then l else Spec.wsVal ws1 k :=
    fun k => by
      unfold Spec.wsVal; by_cases hk : k = n
      · subst hk; rw [List.getElem?_set_self hn_lt, Option.getD_some, hw]; simp
      · rw [List.getElem?_set_ne (Ne.symm hk)]; simp [hk]
  obtain ⟨hsrt_old, hprev_old⟩ := hsrt1 hs_old
  refine ⟨fun a b ha hab hb => ?_, fun j hj => ?_⟩
  · rw [hws_at, hws_at]
    by_cases han : a = n <;> by_cases hbn : b = n
    · subst han hbn; simp
    · omega
    · subst hbn; simp only [han, ↓reduceIte]
      exact Nat.le_trans (hprev_old a (by omega)) hge_prev
    · simp only [han, hbn, ↓reduceIte]; exact hsrt_old a b ha hab (by omega)
  · rw [hws_at]; by_cases hjn : j = n
    · subst hjn; simp only [↓reduceIte]; exact Nat.le_refl _
    · simp only [hjn, ↓reduceIte]; exact Nat.le_trans (hprev_old j (by omega)) hge_prev

theorem defrag_scan_zero_inv {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {n l max_off prev_off : BitVec 64} {sorted : Bool}
    {wvec1 wsort1 : List (BitVec 32)} {m : Mem 64}
    (hl_lt : l.toNat < 2 * s.core.cur_vars) (hn_le : n.toNat ≤ l.toNat)
    (hmax_le : max_off.toNat ≤ c.wcap) (hprev_le : prev_off.toNat ≤ max_off.toNat)
    (hwv1 : wvec1.length = 4 * c.max_vars) (hws1 : wsort1.length = 2 * c.max_vars)
    (hsz1 : ∀ j < 2 * s.core.cur_vars, wvec1[2 * j + 1]? = s.core.wvec[2 * j + 1]?)
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hzero1 : ∀ j < l.toNat, fullWatchSize s j = 0 → wvec1[2 * j]? = some 0#32)
    (hcov1 : WsCovers wsort1 n.toNat l.toNat (fullWatchSize s))
    (hmax_elt : ∀ j < n.toNat, fullWatchOff s (Spec.wsVal wsort1 j) ≤ max_off.toNat)
    (hsrt1 : sorted = true → Spec.SortedRange (fullWatchOff s) wsort1 0 n.toNat ∧
      ∀ j < n.toNat, fullWatchOff s (Spec.wsVal wsort1 j) ≤ prev_off.toNat)
    (hsz0 : fullWatchSize s l.toNat = 0)
    (hl2 : (l <<< (1 : Nat)).toNat = 2 * l.toNat)
    (hlp1 : (l + (1 : BitVec 64)).toNat = l.toNat + 1)
    (hset : ∀ j,
      (wvec1.set (l <<< (1 : Nat)).toNat (0 : BitVec 32))[2 * j + 1]? = wvec1[2 * j + 1]? ∧
      (j ≠ l.toNat →
        (wvec1.set (l <<< (1 : Nat)).toNat (0 : BitVec 32))[2 * j]? = wvec1[2 * j]?) ∧
      (wvec1.set (2 * l.toNat) (0 : BitVec 32))[2 * l.toNat]? = some 0#32)
    (hm : (FullMem c { s with
        core := { s.core with wvec := wvec1.set (l <<< (1 : Nat)).toNat (0 : BitVec 32) },
        scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m) :
    DefragScanInv c s R (n, l + (1 : BitVec 64), max_off, prev_off, sorted, ()) m :=
  ⟨by omega, by omega, hmax_le, hprev_le, _, wsort1, by rw [List.length_set, hwv1], hws1,
   fun j hj => (hset j).1.trans (hsz1 j hj),
   fun j hj hp => ((hset j).2.1 fun heq => by subst heq; omega).trans (hoff1 j hj hp),
   fun j hj hzj => by
     by_cases hjl : j = l.toNat
     · subst hjl; rw [hl2]; exact (hset l.toNat).2.2
     · exact ((hset j).2.1 hjl).trans (hzero1 j (by omega) hzj),
   ⟨fun i hi => ⟨by have := (hcov1.1 i hi).1; omega, (hcov1.1 i hi).2⟩, hcov1.2.1,
    fun j hj hzj => hcov1.2.2 j
      (if hjl : j = l.toNat then by subst hjl; omega else by omega) hzj⟩,
   hmax_elt, hsrt1, hm⟩

theorem defrag_scan_pos_inv {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {n l max_off prev_off : BitVec 64} {sorted : Bool}
    {wvec1 wsort1 : List (BitVec 32)} {off64 : BitVec 64} {m : Mem 64}
    (hl_lt : l.toNat < 2 * s.core.cur_vars) (hn_le : n.toNat ≤ l.toNat)
    (hmax_le : max_off.toNat ≤ c.wcap) (_hprev_le : prev_off.toNat ≤ max_off.toNat)
    (hwv1 : wvec1.length = 4 * c.max_vars) (hws1 : wsort1.length = 2 * c.max_vars)
    (hn_ws_len : n.toNat < wsort1.length)
    (hsz1 : ∀ j < 2 * s.core.cur_vars, wvec1[2 * j + 1]? = s.core.wvec[2 * j + 1]?)
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hzero1 : ∀ j < l.toNat, fullWatchSize s j = 0 → wvec1[2 * j]? = some 0#32)
    (hcov1 : WsCovers wsort1 n.toNat l.toNat (fullWatchSize s))
    (hmax_elt : ∀ j < n.toNat, fullWatchOff s (Spec.wsVal wsort1 j) ≤ max_off.toNat)
    (hsrt1 : sorted = true → Spec.SortedRange (fullWatchOff s) wsort1 0 n.toNat ∧
      ∀ j < n.toNat, fullWatchOff s (Spec.wsVal wsort1 j) ≤ prev_off.toNat)
    (hszp : 0 < fullWatchSize s l.toNat) (hoff_le_cap : fullWatchOff s l.toNat ≤ c.wcap)
    (hoff64_nat : off64.toNat = fullWatchOff s l.toNat)
    (hlp1 : (l + (1 : BitVec 64)).toNat = l.toNat + 1)
    (hnp1 : (n + (1 : BitVec 64)).toNat = n.toNat + 1)
    (htr : (l.setWidth 32).toNat = l.toNat)
    (hm : (FullMem c { s with core := { s.core with wvec := wvec1 },
                              scratch := { s.scratch with
                                wsort := wsort1.set n.toNat (l.setWidth 32) } } ⋆ R) m) :
    let new_sorted := if off64.ult prev_off then false else sorted
    let new_max := if max_off.ult off64 then off64 else max_off
    DefragScanInv c s R
      (n + (1 : BitVec 64), l + (1 : BitVec 64), new_max, off64, new_sorted, ()) m := by
  have hws_at : ∀ k, Spec.wsVal (wsort1.set n.toNat (l.setWidth 32)) k =
      if k = n.toNat then l.toNat else Spec.wsVal wsort1 k := fun k => by
    unfold Spec.wsVal; by_cases hk : k = n.toNat
    · subst hk; rw [List.getElem?_set_self hn_ws_len, Option.getD_some, htr]; simp
    · rw [List.getElem?_set_ne (Ne.symm hk)]; simp [hk]
  refine ⟨by omega, by omega, ?_, ?_, wvec1, wsort1.set n.toNat (l.setWidth 32), hwv1,
    by rw [List.length_set, hws1], hsz1, hoff1,
    fun j hj hzj => hzero1 j (if hjl : j = l.toNat then by subst hjl; omega else by omega) hzj,
    by rw [hlp1, hnp1]; exact defrag_scan_step_cov htr hcov1 hn_ws_len hszp,
    fun j hj => ?_, fun hns => ?_, hm⟩
  · split
    · rw [hoff64_nat]; exact hoff_le_cap
    · exact hmax_le
  · split
    · rw [hoff64_nat]; exact Nat.le_refl _
    · next hult =>
      by_cases hgt : off64.toNat ≤ max_off.toNat
      · exact hgt
      · exfalso; apply hult; simp only [BitVec.ult, decide_eq_true_eq]; omega
  · rw [hws_at]
    by_cases hjn : j = n.toNat
    · subst hjn; simp only [↓reduceIte]; split
      · rw [hoff64_nat]; exact Nat.le_refl _
      · next hult =>
        have hle : off64.toNat ≤ max_off.toNat := by
          by_cases hgt : off64.toNat ≤ max_off.toNat
          · exact hgt
          · exfalso; apply hult; simp only [BitVec.ult, decide_eq_true_eq]; omega
        rwa [hoff64_nat] at hle
    · simp only [hjn, ↓reduceIte]
      have h1 := hmax_elt j (by omega)
      split
      · next hult =>
        have hlt : max_off.toNat < off64.toNat := by simpa [BitVec.ult] using hult
        omega
      · exact h1
  · have hs_t : sorted = true ∧ ¬ (off64.toNat < prev_off.toNat) := by
      by_cases hult : off64.ult prev_off = true
      · simp [hult] at hns
      · simp only [hult, Bool.false_eq_true, ↓reduceIte] at hns
        exact ⟨hns, fun hlt => hult (by simpa [BitVec.ult] using hlt)⟩
    rw [hnp1, hoff64_nat]
    exact defrag_scan_step_sorted htr hn_ws_len hsrt1 (by rw [← hoff64_nat]; omega) hs_t.1

private theorem defrag_radix_keys {c : FullCfg} {s : FullState} {wvec1 wsort1 : List (BitVec 32)}
    {n : Nat} (hwv1 : wvec1.length = 4 * c.max_vars) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hcov1 : WsCovers wsort1 n (2 * s.core.cur_vars) (fullWatchSize s))
    {max_off : Nat} (hkeys_m : ∀ j < n, fullWatchOff s (Spec.wsVal wsort1 j) ≤ max_off) :
    ∀ j < n, 2 * Spec.wsVal (wsort1.take n) j + 1 < wvec1.length ∧
      Spec.fullWvecOff wvec1 (Spec.wsVal (wsort1.take n) j) ≤ max_off := by
  intro j hj
  have hi := hcov1.1 j hj
  have hwv_k : Spec.wsVal (wsort1.take n) j = Spec.wsVal wsort1 j := by
    unfold Spec.wsVal; simp [hj]
  rw [hwv_k]; refine ⟨by omega, ?_⟩
  unfold Spec.fullWvecOff; rw [hoff1 _ hi.1 hi.2]; exact hkeys_m j hj

private theorem defrag_sort_post_of_perm {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wvec1 wsort1 ws' wsortNew wstkNew : List (BitVec 32)} {n : Nat} {m' : Mem 64}
    (hwsl : wstkNew.length = c.wcap) (hwsn : wsortNew.length = 2 * c.max_vars)
    (hpre_stk : ∀ i < s.core.wlen, wstkNew[i]? = s.core.wstk[i]?)
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hcov1 : WsCovers wsort1 n (2 * s.core.cur_vars) (fullWatchSize s))
    (hn_ws : n ≤ wsort1.length) (hn_new : n ≤ wsortNew.length)
    (htk : wsortNew.take n = ws') (hws' : ws'.length = n) (hperm' : (wsort1.take n).Perm ws')
    (hsrt' : Spec.SortedRange (Spec.fullWvecOff wvec1) ws' 0 n)
    (hm' : (FullMem c { s with core := { s.core with wvec := wvec1, wstk := wstkNew },
                               scratch := { s.scratch with wsort := wsortNew } } ⋆ R) m') :
    DefragSortPost c s R wvec1 n () m' := by
  have hcov' : WsCovers wsortNew n (2 * s.core.cur_vars) (fullWatchSize s) :=
    wsCovers_of_perm_suffix hcov1 (by rw [htk]; exact hperm'.symm) hn_ws hn_new
  refine ⟨wstkNew, wsortNew, hwsl, hwsn, hpre_stk, hcov', fun i j hi hij hj => ?_, hm'⟩
  have hki := hcov'.1 i (by omega); have hkj := hcov'.1 j hj
  unfold fullWatchOff fullWatchOffCore
  rw [← hoff1 _ hki.1 hki.2, ← hoff1 _ hkj.1 hkj.2]
  have hv (k : Nat) (hk : k < n) : Spec.wsVal wsortNew k = Spec.wsVal ws' k := by
    unfold Spec.wsVal; rw [← htk, List.getElem?_take_of_lt (by omega)]
  rw [hv i (by omega), hv j hj]; exact hsrt' i j hi hij hj

theorem defrag_extract_next {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wvec1 wsE ws' : List (BitVec 32)} {e n : Nat} {e_bv : BitVec 64}
    {h0 : 0 < wsE.length} {he_len : e < wsE.length} {m' : Mem 64}
    (hn_le : n ≤ 2 * c.max_vars) (he_pos : 0 < e) (he_lt : e < n)
    (hem1 : (e_bv - (1 : BitVec 64)).toNat = e - 1)
    (hwsE : wsE.length = 2 * c.max_vars)
    (hws' : ws'.length = ((wsE.set 0 (wsE[e]'he_len)).set e (wsE[0]'h0)).length)
    (hmaxE : FullWsortMaxHeap wvec1 wsE 0 (e + 1))
    (hspE : SplitLe (Spec.fullWvecOff wvec1) wsE (e + 1) n)
    (hsrtE : Spec.SortedRange (Spec.fullWvecOff wvec1) wsE (e + 1) n)
    (hcovE : WsCovers wsE n (2 * s.core.cur_vars) (fullWatchSize s))
    (hperm' : ws'.Perm ((wsE.set 0 (wsE[e]'he_len)).set e (wsE[0]'h0)))
    (hsuf' : ∀ i, i < 0 ∨ e ≤ i →
      ws'[i]? = ((wsE.set 0 (wsE[e]'he_len)).set e (wsE[0]'h0))[i]?)
    (hmax' : FullWsortMaxHeap wvec1 ws' 0 e)
    (hm' : (FullMem c { s with
        core := { s.core with wvec := wvec1 },
        scratch := { s.scratch with wsort := ws' } } ⋆ R) m') :
    DefragExtractInv c s R wvec1 n (e_bv - (1 : BitVec 64), ()) m' := by
  have hsw_step := wsort_extract_swap_step hmaxE hspE hsrtE he_pos he_lt (by omega)
  have hsw_cov := wsCovers_swap hcovE (i := 0) (j := e) (by omega) he_lt (by omega) he_len
  let wsSwap := swapIdx wsE 0 e
  have hsw_eq : wsSwap = (wsE.set 0 (wsE[e]'he_len)).set e (wsE[0]'h0) := by
    simp [wsSwap, swapIdx, h0, he_len]
  have hlen_sw : wsSwap.length = 2 * c.max_vars := by rw [swapIdx_length, hwsE]
  have hlen_n_sw : n ≤ wsSwap.length := hlen_sw ▸ hn_le
  have hpt : (ws'.take e).Perm (wsSwap.take e) :=
    list_perm_take_of_drop_eq (hsw_eq ▸ hperm') (List.ext_getElem? fun i => by
      rw [List.getElem?_drop, List.getElem?_drop, hsw_eq]
      exact hsuf' (e + i) (Or.inr (Nat.le_add_right e i)))
  have hpt_n : (ws'.take n).Perm (wsSwap.take n) :=
    list_perm_take_of_drop_eq (hsw_eq ▸ hperm') (List.ext_getElem? fun i => by
      rw [List.getElem?_drop, List.getElem?_drop, hsw_eq]
      exact hsuf' (n + i) (Or.inr (Nat.le_trans (Nat.le_of_lt he_lt) (Nat.le_add_right n i))))
  have hcov' := wsCovers_of_perm_suffix hsw_cov hpt_n hlen_n_sw
    (by rw [hws', ← hsw_eq]; exact hlen_n_sw)
  have hperm_ps := wsort_extract_perm_post (e := e) (n := n)
    (fun i hi => by dsimp only [wsSwap] at hsw_eq; rw [hsw_eq]; exact hsuf' i (Or.inr hi))
    hsw_step.2.1 hsw_step.2.2 hpt
    (by rw [hws', ← hsw_eq, hlen_sw]; omega) (by rw [hlen_sw]; omega)
  have hep : (e_bv - (1 : BitVec 64)).toNat + 1 = e := by rw [hem1]; omega
  refine ⟨by rw [hem1]; omega, ws', by rw [hws', ← hsw_eq, hlen_sw], hcov',
    by rw [hep]; exact hmax', by rw [hep]; exact hperm_ps.1, by rw [hep]; exact hperm_ps.2, hm'⟩

theorem defrag_extract_done {s : FullState} {wvec1 wsE : List (BitVec 32)} {n : Nat}
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j →
      wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hcovE : WsCovers wsE n (2 * s.core.cur_vars) (fullWatchSize s))
    (hspE : SplitLe (Spec.fullWvecOff wvec1) wsE 1 n)
    (hsrtE : Spec.SortedRange (Spec.fullWvecOff wvec1) wsE 1 n) :
    Spec.SortedRange (fullWatchOff s) wsE 0 n := by
  intro i j hi hij hj
  have hkey_eq : ∀ k < n, Spec.fullWvecOff wvec1 (Spec.wsVal wsE k) =
      fullWatchOff s (Spec.wsVal wsE k) := fun k hk => by
    have := hcovE.1 k hk; unfold Spec.fullWvecOff fullWatchOff fullWatchOffCore
    rw [hoff1 _ this.1 this.2]
  rw [← hkey_eq i (by omega), ← hkey_eq j hj]
  rcases Nat.eq_zero_or_pos i with rfl | hip
  · rcases Nat.eq_zero_or_pos j with rfl | hjp
    · exact Nat.le_refl _
    · exact hspE 0 (by omega) j (by omega) hj
  · exact hsrtE i j (by omega) hij hj

theorem defrag_compact_keep_inv {s : FullState} {wvecC wstkC wsort2 : List (BitVec 32)}
    {p i n : Nat} (hp1 : 1 ≤ p) (hi_lt : i < n)
    (hcop : DefragCopied s wvecC wstkC wsort2 p i n)
    (hoff_eq_p : fullWatchOff s (Spec.wsVal wsort2 i) = p) :
    DefragCopied s wvecC wstkC wsort2 (p + fullWatchSize s (Spec.wsVal wsort2 i)) (i + 1) n := by
  obtain ⟨hszC, hzeroC, hdoneC, hdisjC, hremC⟩ := hcop
  refine ⟨hszC, hzeroC, fun j hj => ?_, fun a ha b hb hab => ?_, fun j hj1 => hremC j (by omega)⟩
  · dsimp only; by_cases hji : j = i
    · subst j; have hr := hremC i (by omega) hi_lt; rw [hr.1, hoff_eq_p]
      exact ⟨hp1, by omega, fun r hr' => by rw [← hoff_eq_p]; exact hr.2 r hr'⟩
    · have hd := hdoneC j (by omega); exact ⟨hd.1, by omega, hd.2.2⟩
  · dsimp only; by_cases hai : a = i
    · subst a; rw [(hremC i (by omega) hi_lt).1, hoff_eq_p]
      exact Or.inr (hdoneC b (by omega)).2.1
    · by_cases hbi : b = i
      · subst b; rw [(hremC i (by omega) hi_lt).1, hoff_eq_p]
        exact Or.inl (hdoneC a (by omega)).2.1
      · exact hdisjC a (by omega) b (by omega) hab

theorem defrag_compact_copy_inv {s : FullState} {wvecC wstkK wsort2 : List (BitVec 32)}
    {p i n : Nat} {pv : BitVec 32} {wstkC : List (BitVec 32)}
    (hi_lt : i < n) (hp1 : 1 ≤ p) (hpv : pv.toNat = p)
    (hcov2 : WsCovers wsort2 n (2 * s.core.cur_vars) (fullWatchSize s))
    (hlay : WatchStackLayout s.core) (hsrt2 : Spec.SortedRange (fullWatchOff s) wsort2 0 n)
    (hwv_lt : 2 * Spec.wsVal wsort2 i < wvecC.length)
    (hcop : DefragCopied s wvecC wstkC wsort2 p i n)
    (hpreK : ∀ idx < p, wstkK[idx]? = wstkC[idx]?)
    (hpostK : ∀ idx, fullWatchOff s (Spec.wsVal wsort2 i) +
      fullWatchSize s (Spec.wsVal wsort2 i) ≤ idx → wstkK[idx]? = wstkC[idx]?)
    (hcopK : ∀ r < fullWatchSize s (Spec.wsVal wsort2 i),
      wstkK[p + r]? = s.core.wstk[fullWatchOff s (Spec.wsVal wsort2 i) + r]?) :
    DefragCopied s (wvecC.set (2 * Spec.wsVal wsort2 i) pv) wstkK wsort2
      (p + fullWatchSize s (Spec.wsVal wsort2 i)) (i + 1) n := by
  obtain ⟨hszC, hzeroC, hdoneC, hdisjC, hremC⟩ := hcop
  have hlit_info := hcov2.1 i hi_lt
  have hset := wvec_set_even_eq (wvec := wvecC) (l := Spec.wsVal wsort2 i) (v := pv) hwv_lt
  refine ⟨fun j hj => by rw [(hset j).1]; exact hszC j hj,
    fun j hj hzj => by
      have hne : j ≠ Spec.wsVal wsort2 i := fun heq => by subst heq; have := hlit_info.2; omega
      rw [(hset j).2.1 hne]; exact hzeroC j hj hzj,
    fun j hj => ?_, fun a ha b hb hab => ?_, fun j hj1 hj2 => ?_⟩
  · dsimp only; by_cases hji : j = i
    · subst j; rw [(hset 0).2.2, Option.getD_some, hpv]
      exact ⟨hp1, Nat.le_refl _, fun r hr => hcopK r hr⟩
    · have hne := hcov2.2.1 j (by omega) i hi_lt hji
      rw [(hset _).2.1 hne]; have hd := hdoneC j (by omega)
      exact ⟨hd.1, Nat.le_trans hd.2.1 (Nat.le_add_right _ _),
        fun r hr => by rw [hpreK _ (by omega)]; exact hd.2.2 r hr⟩
  · dsimp only; by_cases hai : a = i
    · subst a; have hne := hcov2.2.1 b (by omega) i hi_lt (by omega)
      rw [(hset 0).2.2, (hset _).2.1 hne, Option.getD_some, hpv]
      exact Or.inr (hdoneC b (by omega)).2.1
    · by_cases hbi : b = i
      · subst b; have hne := hcov2.2.1 a (by omega) i hi_lt (by omega)
        rw [(hset 0).2.2, (hset _).2.1 hne, Option.getD_some, hpv]
        exact Or.inl (hdoneC a (by omega)).2.1
      · rw [(hset _).2.1 (hcov2.2.1 a (by omega) i hi_lt hai),
          (hset _).2.1 (hcov2.2.1 b (by omega) i hi_lt hbi)]
        exact hdisjC a (by omega) b (by omega) hab
  · dsimp only; rw [(hset _).2.1 (hcov2.2.1 j hj2 i hi_lt (by omega))]
    have hgap := defrag_sorted_gap hlay hcov2 hsrt2 (i := i) (j := j) (by omega) hj2
    have hr := hremC j (by omega) hj2
    exact ⟨hr.1, fun r hr' => by rw [hpostK _ (by omega)]; exact hr.2 r hr'⟩

private theorem defrag_ptr_mul4 {p : BitVec 64} {a b : Nat} (_ha : a < 2 ^ 62) (_hb : b < 2 ^ 62)
    (hab : a + b < 2 ^ 62) :
    p + BitVec.ofNat 64 a * (4 : BitVec 64) + BitVec.ofNat 64 b * (4 : BitVec 64) =
      p + BitVec.ofNat 64 (4 * (a + b)) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow,
    show (4 : BitVec 64).toNat = 4 from rfl]
  rw [Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
    Nat.mul_comm a 4, Nat.mul_comm b 4,
    Nat.mod_eq_of_lt (by omega : 4 * a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 4 * b < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * a + 4 * b < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * (a + b) < 2 ^ 64)]; omega

theorem defrag_b1_pre {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wvec1 wsort1 : List (BitVec 32)} {n : BitVec 64} {m1 : Mem 64}
    (hlen1 : FullState.LengthsOk c { s with
        core := { s.core with wvec := wvec1 },
        scratch := { s.scratch with wsort := wsort1 } })
    (hwsl : s.core.wstk.length = c.wcap)
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hcov1 : WsCovers wsort1 n.toNat (2 * s.core.cur_vars) (fullWatchSize s))
    (hwcap_lt : c.wcap < 2 ^ 32) (hmax_lt : c.max_vars < 2 ^ 30)
    (h2n_le : 2 * n.toNat + 256 ≤ 2 * c.max_vars)
    (hm1 : (FullMem c { s with core := { s.core with wvec := wvec1 },
                                scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m1)
    {max_off : BitVec 64} (hmax_le : max_off.toNat ≤ c.wcap)
    (hkeys_m : ∀ j < n.toNat, fullWatchOff s (Spec.wsVal wsort1 j) ≤ max_off.toNat)
    {Q' : Post []} {X : XPost}
    (hk : ∀ m', DefragSortPost c s R wvec1 n.toNat () m' → Q' () m') :
    Proof.Watch.Spec.fullWstackRadixSortSpec
      (c.pWvec, c.pWsort, c.pWsort + n * (4 : BitVec 64),
        c.pWsort + (n <<< (1 : Nat)) * (4 : BitVec 64), n, max_off, ())
      m1 Q' X := by
  have hws_l : wsort1.length = 2 * c.max_vars := hlen1.scratch_ok.wsort_len
  have hwv_l : wvec1.length = 4 * c.max_vars := hlen1.core_ok.wvec_len
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen1.core_ok.cur_vars_le
  have hlen_w : (wsort1.take n.toNat).length = n.toNat := by rw [List.length_take, hws_l]; omega
  have hp1_eq : c.pWsort + n * (4 : BitVec 64) = c.pWsort + BitVec.ofNat 64 (4 * n.toNat) := by
    simpa [BitVec.add_zero] using defrag_ptr_mul4 (p := c.pWsort) (a := n.toNat) (b := 0)
      (by omega) (by omega) (by omega)
  have hp2_eq : c.pWsort + (n <<< (1 : Nat)) * (4 : BitVec 64) =
      c.pWsort + BitVec.ofNat 64 (4 * (2 * n.toNat)) := by
    have hn2 : n <<< (1 : Nat) = BitVec.ofNat 64 (2 * n.toNat) := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
    rw [hn2]
    simpa [BitVec.add_zero] using defrag_ptr_mul4 (p := c.pWsort) (a := 2 * n.toNat) (b := 0)
      (by omega) (by omega) (by omega)
  refine ⟨wvec1, wsort1.take n.toNat, (wsort1.drop n.toNat).take n.toNat,
    (wsort1.drop (2 * n.toNat)).take 256,
    (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n.toNat + 256)))
      (wsort1.drop (2 * n.toNat + 256)) ⋆ FullWvecWsortRest c { s with
        core := { s.core with wvec := wvec1 },
        scratch := { s.scratch with wsort := wsort1 } } ⋆ R),
    Nat.le_of_eq hlen_w.symm, by rw [List.length_take, List.length_drop, hws_l]; omega,
    by rw [List.length_take, List.length_drop, hws_l]; omega, by omega, by omega,
    defrag_radix_keys hwv_l hcv_le hoff1 hcov1 hkeys_m, ?_, ?_⟩
  · rw [hp1_eq, hp2_eq]; exact full_wvec_wsort_split4 hlen1 h2n_le hm1
  · intro ws' tmp' cnt' m' hws' htmp' hcnt' hperm' hsrt' _ hm'
    rw [hp1_eq, hp2_eq] at hm'
    have hperm1 := hperm'
    rw [List.take_of_length_le (Nat.le_of_eq (hws'.trans hlen_w)),
      List.take_of_length_le (Nat.le_of_eq hlen_w)] at hperm1
    have hrec := full_wvec_wsort_unsplit4 hlen1 h2n_le (by rw [hws', hlen_w])
      (by rw [htmp', List.length_take, List.length_drop, hws_l]; omega)
      (by rw [hcnt', List.length_take, List.length_drop, hws_l]; omega) hm'
    exact hk m' (defrag_sort_post_of_perm hwsl hrec.1 (fun _ _ => rfl) hoff1 hcov1
      (by omega) (by rw [hrec.1]; omega) hrec.2.1 (by omega) hperm1.symm hsrt' hrec.2.2)

theorem defrag_b2_pre {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wvec1 wsort1 : List (BitVec 32)} {n : BitVec 64} {m1 : Mem 64}
    (hlen1 : FullState.LengthsOk c { s with
        core := { s.core with wvec := wvec1 },
        scratch := { s.scratch with wsort := wsort1 } })
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hcov1 : WsCovers wsort1 n.toNat (2 * s.core.cur_vars) (fullWatchSize s))
    (hwcap_lt : c.wcap < 2 ^ 32) (hmax_lt : c.max_vars < 2 ^ 30)
    (hn_ws : n.toNat ≤ 2 * c.max_vars) (hcap_le : s.core.wlen + n.toNat + 256 ≤ c.wcap)
    (hm1 : (FullMem c { s with core := { s.core with wvec := wvec1 },
                                scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m1)
    {max_off : BitVec 64} (hmax_le : max_off.toNat ≤ c.wcap)
    (hkeys_m : ∀ j < n.toNat, fullWatchOff s (Spec.wsVal wsort1 j) ≤ max_off.toNat)
    {Q' : Post []} {X : XPost}
    (hk : ∀ m', DefragSortPost c s R wvec1 n.toNat () m' → Q' () m') :
    Proof.Watch.Spec.fullWstackRadixSortSpec
      (c.pWvec, c.pWsort, c.pWstk + BitVec.ofNat 64 s.core.wlen * (4 : BitVec 64),
        c.pWstk + BitVec.ofNat 64 s.core.wlen * (4 : BitVec 64) + n * (4 : BitVec 64),
        n, max_off, ())
      m1 Q' X := by
  have hws_l : wsort1.length = 2 * c.max_vars := hlen1.scratch_ok.wsort_len
  have hwv_l : wvec1.length = 4 * c.max_vars := hlen1.core_ok.wvec_len
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen1.core_ok.cur_vars_le
  have hst_l : s.core.wstk.length = c.wcap := hlen1.core_ok.wstk_len_arr
  have hwle : s.core.wlen ≤ c.wcap := hlen1.core_ok.wlen_le
  have hq1_eq : c.pWstk + BitVec.ofNat 64 s.core.wlen * (4 : BitVec 64) =
      c.pWstk + BitVec.ofNat 64 (4 * s.core.wlen) := by
    simpa [BitVec.add_zero] using defrag_ptr_mul4 (p := c.pWstk) (a := s.core.wlen) (b := 0)
      (by omega) (by omega) (by omega)
  have hq2_eq : c.pWstk + BitVec.ofNat 64 s.core.wlen * (4 : BitVec 64) + n * (4 : BitVec 64) =
      c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n.toNat)) := by
    simpa using defrag_ptr_mul4 (p := c.pWstk) (a := s.core.wlen) (b := n.toNat)
      (by omega) (by omega) (by omega)
  have hlen_w2 : (wsort1.take n.toNat).length = n.toNat := by rw [List.length_take, hws_l]; omega
  refine ⟨wvec1, wsort1.take n.toNat, (s.core.wstk.drop s.core.wlen).take n.toNat,
    (s.core.wstk.drop (s.core.wlen + n.toNat)).take 256,
    (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n.toNat)) (wsort1.drop n.toNat) ⋆
     array (t := i32) c.pWstk (s.core.wstk.take s.core.wlen) ⋆
     array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n.toNat + 256)))
       (s.core.wstk.drop (s.core.wlen + n.toNat + 256)) ⋆
     FullRestNoWatch c { s with
       core := { s.core with wvec := wvec1 }
       scratch := { s.scratch with wsort := wsort1 } } ⋆ R),
    Nat.le_of_eq hlen_w2.symm, by rw [List.length_take, List.length_drop, hst_l]; omega,
    by rw [List.length_take, List.length_drop, hst_l]; omega, by omega, by omega,
    defrag_radix_keys hwv_l hcv_le hoff1 hcov1 hkeys_m, ?_, ?_⟩
  · rw [hq2_eq, hq1_eq]; exact full_wstack_defrag_wstk_split hlen1 hn_ws hcap_le hm1
  · intro ws' tmp' cnt' m' hws' htmp' hcnt' hperm' hsrt' _ hm'
    rw [hq2_eq, hq1_eq] at hm'
    have hperm2 := hperm'
    rw [List.take_of_length_le (Nat.le_of_eq (hws'.trans hlen_w2)),
      List.take_of_length_le (Nat.le_of_eq hlen_w2)] at hperm2
    have hrec := full_wstack_defrag_wstk_unsplit hlen1 hn_ws hcap_le (by rw [hws', hlen_w2])
      (by rw [htmp', List.length_take, List.length_drop, hst_l]; omega)
      (by rw [hcnt', List.length_take, List.length_drop, hst_l]; omega) hm'
    exact hk m' (defrag_sort_post_of_perm hrec.2.1 hrec.1 hrec.2.2.2.1 hoff1 hcov1
      (by omega) (by rw [hrec.1]; omega) hrec.2.2.1 (by omega) hperm2.symm hsrt' hrec.2.2.2.2)

theorem defrag_compact_init_inv {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wvec1 wstk2 wsort2 : List (BitVec 32)} {n : Nat} {m2 : Mem 64}
    (hwv1 : wvec1.length = 4 * c.max_vars) (hwst2 : wstk2.length = c.wcap)
    (hwlen_gt1 : 1 < s.core.wlen) (_hn_pos : 0 < n)
    (hlay : WatchStackLayout s.core)
    (hsz1 : ∀ j < 2 * s.core.cur_vars, wvec1[2 * j + 1]? = s.core.wvec[2 * j + 1]?)
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hzero1 : ∀ j < 2 * s.core.cur_vars, fullWatchSize s j = 0 → wvec1[2 * j]? = some 0#32)
    (hwstk_pre : ∀ i < s.core.wlen, wstk2[i]? = s.core.wstk[i]?)
    (hcov2 : WsCovers wsort2 n (2 * s.core.cur_vars) (fullWatchSize s))
    (hm2 : (FullMem c { s with core := { s.core with wvec := wvec1, wstk := wstk2 },
                                scratch := { s.scratch with wsort := wsort2 } } ⋆ R) m2) :
    DefragCompactInv c s R n wsort2 ((1 : BitVec 64), (0 : BitVec 64), ()) m2 := by
  have h0_64 : (0 : BitVec 64).toNat = 0 := rfl
  have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
  refine ⟨by rw [h1_64]; exact Nat.le_refl 1, by rw [h1_64]; omega,
    by rw [h0_64]; exact Nat.zero_le _, fun h0 => ?_, wvec1, wstk2, hwv1, hwst2,
    ⟨fun j hj => by unfold fullWatchSize fullWatchSizeCore; rw [hsz1 j hj],
     fun j hj hz => by rw [hzero1 j hj hz]; rfl,
     fun _ hj => by rw [h0_64] at hj; omega, fun _ ha => by rw [h0_64] at ha; omega,
     fun j _ hjn => ⟨by have := hcov2.1 j hjn
                        unfold fullWatchOff fullWatchOffCore; rw [hoff1 _ this.1 this.2],
       fun k hk => hwstk_pre _
         (by have := hcov2.1 j hjn; have := hlay.bounds _ this.1
             dsimp only [fullWatchOff, fullWatchSize] at *; omega)⟩⟩,
    hm2⟩
  rw [h0_64] at h0; have hc0 := hcov2.1 0 h0
  have := hlay.pos_off _ hc0.1 hc0.2; rw [h1_64]; exact this

theorem defrag_compact_copy_next_inv {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wsort2 wvecD wstkD : List (BitVec 32)} {i n : Nat} {p pNxt iNxt : BitVec 64}
    {mD : Mem 64}
    (hlay : WatchStackLayout s.core)
    (hcov2 : WsCovers wsort2 n (2 * s.core.cur_vars) (fullWatchSize s))
    (hsrt2 : Spec.SortedRange (fullWatchOff s) wsort2 0 n)
    (hi_lt : i < n) (hp1 : 1 ≤ p.toNat) (hp_le_off : p.toNat ≤ fullWatchOff s (Spec.wsVal wsort2 i))
    (hps_le : p.toNat + fullWatchSize s (Spec.wsVal wsort2 i) ≤ s.core.wlen)
    (hip1 : iNxt.toNat = i + 1)
    (hpnxt : pNxt.toNat = p.toNat + fullWatchSize s (Spec.wsVal wsort2 i))
    (hwvD : wvecD.length = 4 * c.max_vars) (hwsD : wstkD.length = c.wcap)
    (hcopD : DefragCopied s wvecD wstkD wsort2
      (p.toNat + fullWatchSize s (Spec.wsVal wsort2 i)) (i + 1) n)
    (hmD : (FullMem c { s with core := { s.core with wvec := wvecD, wstk := wstkD },
                                scratch := { s.scratch with wsort := wsort2 } } ⋆ R) mD) :
    DefragCompactInv c s R n wsort2 (pNxt, iNxt, ()) mD := by
  rw [← hpnxt, ← hip1] at hcopD
  refine ⟨by rw [hpnxt]; omega, by rw [hpnxt]; omega, by rw [hip1]; omega, fun hi1 => ?_,
    wvecD, wstkD, hwvD, hwsD, hcopD, hmD⟩
  rw [hpnxt, hip1]; rw [hip1] at hi1
  exact Nat.le_trans (Nat.add_le_add_left (Nat.le_refl _) _)
    (Nat.le_trans (Nat.add_le_add_right hp_le_off _)
      (defrag_sorted_gap hlay hcov2 hsrt2 (by omega) hi1))

theorem defrag_k_loop_step_inv {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wvecC wstkC wstkK wsort2 : List (BitVec 32)} {i : Nat} {p k kNxt : BitVec 64}
    {offIdx srcIdx : Nat} {m : Mem 64}
    (hk_lt : k.toNat < fullWatchSize s (Spec.wsVal wsort2 i))
    (hp_lt_off : p.toNat < fullWatchOff s (Spec.wsVal wsort2 i))
    (hwsK : wstkK.length = c.wcap)
    (_hok_eq : offIdx = fullWatchOff s (Spec.wsVal wsort2 i) + k.toNat)
    (hpk : (p + k).toNat = p.toNat + k.toNat)
    (hkp1 : kNxt.toNat = k.toNat + 1)
    (hpk_lt : (p + k).toNat < wstkK.length) (hok_lt : srcIdx < wstkK.length)
    (hsrc_eq : srcIdx = fullWatchOff s (Spec.wsVal wsort2 i) + k.toNat)
    (hpreK : ∀ idx < p.toNat, wstkK[idx]? = wstkC[idx]?)
    (hpostK : ∀ idx,
      fullWatchOff s (Spec.wsVal wsort2 i) + k.toNat ≤ idx → wstkK[idx]? = wstkC[idx]?)
    (hcopK : ∀ r < k.toNat,
      wstkK[p.toNat + r]? = s.core.wstk[fullWatchOff s (Spec.wsVal wsort2 i) + r]?)
    (hsrcK : ∀ r, k.toNat ≤ r → r < fullWatchSize s (Spec.wsVal wsort2 i) →
      wstkK[fullWatchOff s (Spec.wsVal wsort2 i) + r]? =
        s.core.wstk[fullWatchOff s (Spec.wsVal wsort2 i) + r]?)
    (hm : (FullMem c { s with
        core := { s.core with
          wvec := wvecC, wstk := wstkK.set (p + k).toNat (wstkK[srcIdx]'hok_lt) }
        scratch := { s.scratch with wsort := wsort2 } } ⋆ R) m) :
    DefragKInv c s R wvecC wstkC wsort2 i p.toNat (kNxt, ()) m := by
  refine ⟨by omega, _, by simp [hwsK],
    fun idx hidx => by rw [List.getElem?_set_ne (by omega)]; exact hpreK idx hidx,
    fun idx hidx => by rw [List.getElem?_set_ne (by omega)]; exact hpostK idx (by omega),
    fun r hr => ?_, fun r hr1 hr2 => by
      have hr1' : k.toNat ≤ r := by rw [hkp1] at hr1; exact Nat.le_of_succ_le hr1
      rw [List.getElem?_set_ne (by
        rw [hpk]; exact Nat.ne_of_lt (Nat.lt_of_lt_of_le
          (Nat.add_lt_add_right hp_lt_off k.toNat) (Nat.add_le_add_left hr1' _)))]
      exact hsrcK r hr1' hr2, hm⟩
  rw [hkp1] at hr
  by_cases hrk : r = k.toNat
  · subst hrk
    rw [← hpk, List.getElem?_set_self hpk_lt, ← List.getElem?_eq_getElem hok_lt, hsrc_eq]
    exact hsrcK k.toNat (Nat.le_refl _) hk_lt
  · rw [List.getElem?_set_ne (by omega)]; exact hcopK r (by omega)

theorem defrag_heap_step_inv {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wvec1 wsB ws' : List (BitVec 32)} {n : Nat} {st stNxt : BitVec 64} {m' : Mem 64}
    (hn_le : n ≤ 2 * s.core.cur_vars) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (_hst_pos : 0 < st.toNat) (hst_le : st.toNat ≤ n)
    (hstm1 : stNxt.toNat = st.toNat - 1) (hwsB : wsB.length = 2 * c.max_vars)
    (hcovB : WsCovers wsB n (2 * s.core.cur_vars) (fullWatchSize s))
    (hws' : ws'.length = wsB.length) (hperm' : ws'.Perm wsB)
    (hsuf' : ∀ i, n ≤ i → ws'[i]? = wsB[i]?)
    (hmax' : FullWsortMaxHeap wvec1 ws' stNxt.toNat n)
    (hm'' : (FullMem c { s with core := { s.core with wvec := wvec1 },
                                 scratch := { s.scratch with wsort := ws' } } ⋆ R) m') :
    DefragHeapInv c s R wvec1 n (stNxt, ()) m' := by
  have hcov' := wsCovers_of_perm_suffix hcovB
    (list_perm_take_of_drop_eq hperm' (List.ext_getElem? fun i => by
      rw [List.getElem?_drop, List.getElem?_drop]; exact hsuf' (n + i) (Nat.le_add_right _ _)))
    (hwsB ▸ Nat.le_trans hn_le (Nat.mul_le_mul_left 2 hcv_le))
    (by rw [hws', hwsB]; exact Nat.le_trans hn_le (Nat.mul_le_mul_left 2 hcv_le))
  exact ⟨by rw [hstm1]; exact Nat.le_trans (Nat.sub_le _ 1) hst_le,
    ws', by rw [hws', hwsB], hcov', hmax', hm''⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Watch