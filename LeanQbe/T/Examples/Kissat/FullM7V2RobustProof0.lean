/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7V2Robust
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas1
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` `M7` v2 Robustness Parametric `Func.wp` Proofs (`FullM7V2RobustProof0`)

M1-clean (`public section`, `0 @[expose]`, `0 @[local]`, `0 import all`, `0 sorry`) parametric
UNSAT-only `(Γ : Env)` `Func.wp` proofs (`XPost := False`, `0` SAT model-finding proofs) for all
`5` candidate functions of `FullM7V2Robust`:

1. `full_watch_pop_c0_wp` against `fullWatchPopC0Spec`, plus `modeWatchesInv_of_pop` and
   `binOnlyWatchesInv_of_pop`.
2. `full_add_clause_wp` against canonical `Full.fullAddClauseSpec` (atomic rollback via
   `full_watch_pop_c0` and `h->arena_len = cref`).
3. `full_sweep_copy_wp` against canonical `Full.fullSweepCopySpec` (atomic `bin` watch-push OOM
   rollback via `full_watch_pop_c0` + `PH_RED` zombie drop).
4. `full_reduce_purge_c0_wp` against `fullReducePurgeC0Spec` (`Full.fullReduceSpec (h, true, ())`,
   marking all non-reason redundant clauses `PH_GARB` and sweeping/propagating to level-0 fixpoint).
5. `full_learn_clause_wp` against canonical `Full.fullLearnClauseSpec` (preserving the pre-add
   headroom check + 3-step `defrag` / `full_reduce(h, true)` / `full_reduce_purge_c0` retry ladder).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7V2Robust

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Watch-Pop Contract, Proof (`full_watch_pop_c0`), & Purge Contract -/

section WatchPopSection

open Full.FullAssignAddTactics
open scoped Full.FullArenaTactics Full.FullAssignAddTactics

/-- Helper contract for `full_watch_pop_c0(h, lit, cnt)`: pops `cnt` slots from `lit`'s watch
slice when `lit < 2 * cur_vars` and `0 < cnt ≤ sz`, preserving `WatchStackLayout` and all
remaining watch entries verbatim. -/
def fullWatchPopC0Spec : Spec [i64, i32, i32] [] :=
  fun (h, lit, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      lit.toNat < 2 * s.core.cur_vars ∧
      0 < cnt.toNat ∧ cnt.toNat ≤ fullWatchSize s lit.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ wvec' wstk' wusable' m',
        let s' : FullState :=
          { s with core :=
            { s.core with wvec := wvec', wstk := wstk', wusable := wusable' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
          fullWatchOff s' l = fullWatchOff s l ∧
          fullWatchSize s' l = fullWatchSize s l ∧
          ∀ k < fullWatchSize s l,
            s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
        fullWatchOff s' lit.toNat = fullWatchOff s lit.toNat →
        fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat - cnt.toNat →
        (∀ k < fullWatchSize s lit.toNat - cnt.toNat,
          s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
            s.core.wstk[fullWatchOff s lit.toNat + k]?) →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Emergency purge contract: `full_reduce_purge_c0(h)` satisfies `Full.fullReduceSpec` with
`force = true`. -/
def fullReducePurgeC0Spec : Spec [i64] [i64] := fun (h, ()) m Q X =>
  Full.fullReduceSpec (h, true, ()) m Q X

theorem fullWatchPopC0Spec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : fullWatchPopC0Spec xs m Q X) : fullWatchPopC0Spec xs m Q X' :=
  h

theorem fullReducePurgeC0Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : fullReducePurgeC0Spec xs m Q X) : fullReducePurgeC0Spec xs m Q X' :=
  h

theorem fullReducePurgeC0Spec_of_full {h : BitVec 64} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (hr : Full.fullReduceSpec (h, true, ()) m Q X) :
    fullReducePurgeC0Spec (h, ()) m Q X :=
  hr

theorem fullReducePurgeC0Spec_elim {h : BitVec 64} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (hp : fullReducePurgeC0Spec (h, ()) m Q X) :
    Full.fullReduceSpec (h, true, ()) m Q X :=
  hp

private theorem wvec_set_odd_pop {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l + 1 < wvec.length) (j : Nat) :
    (wvec.set (2 * l + 1) v)[2 * j]? = wvec[2 * j]? ∧
    (j ≠ l → (wvec.set (2 * l + 1) v)[2 * j + 1]? = wvec[2 * j + 1]?) ∧
    (wvec.set (2 * l + 1) v)[2 * l + 1]? = some v :=
  ⟨List.getElem?_set_ne (by omega), fun hne => List.getElem?_set_ne (by omega),
   List.getElem?_set_self hl⟩

/-- Parametrically proves `full_watch_pop_c0` against `fullWatchPopC0Spec`. -/
theorem full_watch_pop_c0_wp (Γ : Env) :
    ∀ args m Q X, fullWatchPopC0Spec args m Q X →
      Func.wp Γ full_watch_pop_c0_body args m Q X := by
  rintro ⟨h, lit, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hlit_lt, hcnt_pos, hcnt_le, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap
  unfold dimacsBound at hmx hwcap
  have hco := hlen.core_ok
  have hcv_le := hco.cur_vars_le
  have hwvec_len := hco.wvec_len
  have hwstk_len := hco.wstk_len_arr
  have hwlen_le := hco.wlen_le
  have hcv_lt64 : 2 * s.core.cur_vars < 2 ^ 64 := by omega
  have hlit_cv :
      (lit.setWidth 64).toNat < (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by
    rw [zext_toNat _ (by decide), BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega),
      Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
    omega
  unfold Func.wp full_watch_pop_c0_body
  faa_head_steps; c0_split
  · have h2l_lt : 2 * lit.toNat < s.core.wvec.length := by omega
    have h2l1_lt : 2 * lit.toNat + 1 < s.core.wvec.length := by omega
    have h2l_idx : (lit.setWidth 64 <<< 1#64).toNat = 2 * lit.toNat := by
      rw [show (lit.setWidth 64 <<< 1#64) = lit.setWidth 64 <<< (1 : Nat) from rfl,
        BitVec.toNat_shiftLeft, zext_toNat _ (by decide), Nat.shiftLeft_eq, Nat.mul_comm]
      exact Nat.mod_eq_of_lt (by omega)
    have h2l1_idx : ((lit.setWidth 64 <<< 1#64) + 1#64).toNat = 2 * lit.toNat + 1 := by
      rw [BitVec.toNat_add, h2l_idx, show (1#64 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    have hoff_eq : (s.core.wvec[(lit.setWidth 64 <<< 1#64).toNat]'(by
        rw [h2l_idx]; exact h2l_lt)).toNat = fullWatchOff s lit.toNat := by
      unfold fullWatchOff fullWatchOffCore
      simp only [h2l_idx, List.getElem?_eq_getElem h2l_lt, Option.getD_some]
    have hsz_eq : (s.core.wvec[((lit.setWidth 64 <<< 1#64) + 1#64).toNat]'(by
        rw [h2l1_idx]; exact h2l1_lt)).toNat = fullWatchSize s lit.toNat := by
      unfold fullWatchSize fullWatchSizeCore
      simp only [h2l1_idx, List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
    let off64 := (s.core.wvec[(lit.setWidth 64 <<< 1#64).toNat]'(by
      rw [h2l_idx]; exact h2l_lt)).setWidth 64
    let sz64 := (s.core.wvec[((lit.setWidth 64 <<< 1#64) + 1#64).toNat]'(by
      rw [h2l1_idx]; exact h2l1_lt)).setWidth 64
    have hoff_toNat : off64.toNat = fullWatchOff s lit.toNat := by
      dsimp only [off64]; rw [zext_toNat _ (by decide)]; exact hoff_eq
    have hsz_toNat : sz64.toNat = fullWatchSize s lit.toNat := by
      dsimp only [sz64]; rw [zext_toNat _ (by decide)]; exact hsz_eq
    have hbd_slice : off64.toNat + sz64.toNat ≤ s.core.wlen := by
      rw [hoff_toNat, hsz_toNat]; exact hlay.bounds lit.toNat hlit_lt
    have hcnt64 : (cnt.setWidth 64).toNat = cnt.toNat := zext_toNat _ (by decide)
    -- Short-circuit `if (c == 0ULL || sz < c || off + sz > h->wlen) { return; }`.
    -- `faa_steps` already discharges `c == 0ULL` via `hcnt_pos`.
    faa_steps
    · exfalso
      have hsz_lt_w : (lit.toNat * 2 ^ 1 + 1) % 2 ^ 64 < s.core.wvec.length := by
        rw [Nat.pow_one, Nat.mul_comm lit.toNat 2,
          Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64)]
        exact h2l1_lt
      have hsz' : (s.core.wvec[(lit.toNat * 2 ^ 1 + 1) % 2 ^ 64]'hsz_lt_w).toNat =
          fullWatchSize s lit.toNat := by
        unfold fullWatchSize fullWatchSizeCore
        have hget : (some (s.core.wvec[(lit.toNat * 2 ^ 1 + 1) % 2 ^ 64]'hsz_lt_w)).getD 0#32 =
            s.core.wvec[2 * lit.toNat + 1]?.getD 0#32 := by
          rw [← List.getElem?_eq_getElem hsz_lt_w]
          simp only [Nat.pow_one, Nat.mul_comm lit.toNat 2,
            Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64)]
        exact congrArg BitVec.toNat hget
      rw [hsz'] at hc; omega
    · exfalso
      have hoff_lt_w : lit.toNat * 2 ^ 1 % 2 ^ 64 < s.core.wvec.length := by
        rw [Nat.pow_one, Nat.mul_comm lit.toNat 2,
          Nat.mod_eq_of_lt (by omega : 2 * lit.toNat < 2 ^ 64)]
        exact h2l_lt
      have hsz_lt_w : (lit.toNat * 2 ^ 1 + 1) % 2 ^ 64 < s.core.wvec.length := by
        rw [Nat.pow_one, Nat.mul_comm lit.toNat 2,
          Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64)]
        exact h2l1_lt
      have hoff' : (s.core.wvec[lit.toNat * 2 ^ 1 % 2 ^ 64]'hoff_lt_w).toNat =
          fullWatchOff s lit.toNat := by
        unfold fullWatchOff fullWatchOffCore
        have hget : (some (s.core.wvec[lit.toNat * 2 ^ 1 % 2 ^ 64]'hoff_lt_w)).getD 0#32 =
            s.core.wvec[2 * lit.toNat]?.getD 0#32 := by
          rw [← List.getElem?_eq_getElem hoff_lt_w]
          simp only [Nat.pow_one, Nat.mul_comm lit.toNat 2,
            Nat.mod_eq_of_lt (by omega : 2 * lit.toNat < 2 ^ 64)]
        exact congrArg BitVec.toNat hget
      have hsz' : (s.core.wvec[(lit.toNat * 2 ^ 1 + 1) % 2 ^ 64]'hsz_lt_w).toNat =
          fullWatchSize s lit.toNat := by
        unfold fullWatchSize fullWatchSizeCore
        have hget : (some (s.core.wvec[(lit.toNat * 2 ^ 1 + 1) % 2 ^ 64]'hsz_lt_w)).getD 0#32 =
            s.core.wvec[2 * lit.toNat + 1]?.getD 0#32 := by
          rw [← List.getElem?_eq_getElem hsz_lt_w]
          simp only [Nat.pow_one, Nat.mul_comm lit.toNat 2,
            Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64)]
        exact congrArg BitVec.toNat hget
      rw [Nat.mod_eq_of_lt (by omega : s.core.wlen < 2 ^ 64), hoff', hsz',
        Nat.mod_eq_of_lt (by rw [← hoff_toNat, ← hsz_toNat]; omega :
          fullWatchOff s lit.toNat + fullWatchSize s lit.toNat < 2 ^ 64)] at hc
      rw [← hoff_toNat, ← hsz_toNat] at hc; omega
    ·
          c0_to_group
          refine wp_loop_inv
            (fun (k, ()) mL =>
              sz64.toNat - cnt.toNat ≤ k.toNat ∧ k.toNat ≤ sz64.toNat ∧
              ∃ wstkL : List (BitVec 32), wstkL.length = c.wcap ∧
                (∀ idx, idx < off64.toNat + (sz64.toNat - cnt.toNat) ∨
                  off64.toNat + k.toNat ≤ idx → wstkL[idx]? = s.core.wstk[idx]?) ∧
                (FullMem c { s with core := { s.core with wstk := wstkL } } ⋆ R) mL)
            (fun (k, ()) _ => sz64.toNat - k.toNat)
            (fun JL hLoop => by
              c0_steps
              have hsub_eq : (sz64 - cnt.setWidth 64).toNat = sz64.toNat - cnt.toNat := by
                rw [BitVec.toNat_sub_of_le
                  (BitVec.le_def.mpr (by rw [hsz_toNat, hcnt64]; exact hcnt_le)), hcnt64]
              exact hLoop (sz64 - cnt.setWidth 64, ()) m
                ⟨by rw [hsub_eq]; exact Nat.le_refl _, by rw [hsub_eq]; omega,
                  s.core.wstk, hwstk_len, fun _ _ => rfl, hm⟩)
            (fun JL (k, ()) mL ⟨hk_lo, hk_hi, wstkL, hwlL, hagrL, hmL⟩ hLoop => ?_)
          · have hsz_lt_w2 : (lit.toNat * 2 ^ 1 + 1) % 2 ^ 64 < s.core.wvec.length := by
              rw [Nat.pow_one, Nat.mul_comm lit.toNat 2,
                Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64)]
              exact h2l1_lt
            have hsz_w2 :
                (s.core.wvec[(lit.toNat * 2 ^ 1 + 1) % 2 ^ 64]'hsz_lt_w2).toNat = sz64.toNat := by
              rw [hsz_toNat]; unfold fullWatchSize fullWatchSizeCore
              have hget : (some (s.core.wvec[(lit.toNat * 2 ^ 1 + 1) % 2 ^ 64]'hsz_lt_w2)).getD
                  0#32 = s.core.wvec[2 * lit.toNat + 1]?.getD 0#32 := by
                rw [← List.getElem?_eq_getElem hsz_lt_w2]
                simp only [Nat.pow_one, Nat.mul_comm lit.toNat 2,
                  Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64)]
              exact congrArg BitVec.toNat hget
            c0_split
            · have hk_lt : k.toNat < sz64.toNat := by
                rw [← hsz_w2]; try simp only [Nat.pow_one] at hc ⊢
                exact hc
              have hoff_k_lt : (off64 + k).toNat < wstkL.length := by
                have : off64.toNat + k.toNat < c.wcap := by omega
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
              have hk1_eq : (k + 1#64).toNat = k.toNat + 1 := by
                rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              have hoff_k_eq : (off64 + k).toNat = off64.toNat + k.toNat := by
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
              have hoff_k_lt' :
                  (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 lit <<< 1#64).toNat]'(by
                    rw [h2l_idx]; exact h2l_lt)) + k).toNat < wstkL.length := hoff_k_lt
              c0_hsteps
              let wstk' := wstkL.set (off64 + k).toNat 0xFFFFFFFF#32
              refine hLoop (k + 1#64, ()) m (by dsimp only; rw [hk1_eq]; omega)
                ⟨by rw [hk1_eq]; omega, by rw [hk1_eq]; omega, wstk', by simp [wstk', hwlL],
                  ?_, by simpa only [wstk', off64,
                    show (lit.setWidth 64 <<< (1 : Nat)) = lit.setWidth 64 <<< 1#64 from rfl,
                    show (0xFFFFFFFF#32 : BitVec 32) = 4294967295 from rfl] using hm⟩
              intro idx hidx; rw [hk1_eq] at hidx; dsimp only [wstk']
              rw [List.getElem?_set_ne (by rw [hoff_k_eq]; rcases hidx with h | h <;> omega)]
              exact hagrL idx (by rcases hidx with h | h; exact Or.inl h; exact Or.inr (by omega))
            · have hk_eq : k.toNat = sz64.toNat := by
                have hnot : ¬ k.toNat < sz64.toNat := by
                  rw [← hsz_w2]; try simp only [Nat.pow_one] at hc ⊢
                  exact hc
                omega
              rw [hk_eq] at hagrL
              let newsz32 : BitVec 32 := (sz64 - cnt.setWidth 64).setWidth 32
              have hnewsz_toNat : newsz32.toNat = fullWatchSize s lit.toNat - cnt.toNat := by
                have hsub : (sz64 - cnt.setWidth 64).toNat = sz64.toNat - cnt.toNat := by
                  rw [BitVec.toNat_sub_of_le
                    (BitVec.le_def.mpr (by rw [hsz_toNat, hcnt64]; exact hcnt_le)), hcnt64]
                dsimp only [newsz32]
                rw [BitVec.toNat_setWidth, hsub, hsz_toNat,
                  Nat.mod_eq_of_lt (by have := sz64.isLt; omega)]
              have hidx_w2l1 : ((lit.setWidth 64 <<< 1#64) + 1#64).toNat < s.core.wvec.length := by
                rw [h2l1_idx]; exact h2l1_lt
              c0_hsteps
              let wvec' := s.core.wvec.set (2 * lit.toNat + 1) newsz32
              let wusable' := s.core.wusable + cnt.setWidth 64
              let s' : FullState :=
                { s with core := { s.core with wvec := wvec', wstk := wstkL, wusable := wusable' } }
              have hwvec'_eq : s.core.wvec.set ((lit.setWidth 64 <<< 1#64) + 1#64).toNat
                  newsz32 = wvec' := by
                dsimp only [wvec']; rw [h2l1_idx]
              have hmem' : (FullMem c s' ⋆ R) m := by
                refine cast (congrArg (fun st' => (FullMem c st' ⋆ R) m) ?_) hm
                dsimp only [s', wusable']
                congr 2 <;> try (
                  dsimp only [newsz32, sz64]; rw [← hwvec'_eq]
                  simp only [show (1 : BitVec 64) = 1#64 from rfl])
              have hlen' : s'.LengthsOk c :=
                { core_ok := { hco with
                    wvec_len := by simp [s', wvec', hwvec_len]
                    wstk_len_arr := by simp [s', hwlL] }
                  scratch_ok := hlen.scratch_ok }
              have hod := fun j => wvec_set_odd_pop (wvec := s.core.wvec) (l := lit.toNat)
                (v := newsz32) h2l1_lt j
              have hoff_other : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
                  fullWatchOff s' l = fullWatchOff s l ∧
                  fullWatchSize s' l = fullWatchSize s l := fun l hl hne => by
                change fullWatchOffCore s'.core l = fullWatchOffCore s.core l ∧
                  fullWatchSizeCore s'.core l = fullWatchSizeCore s.core l
                unfold fullWatchOffCore fullWatchSizeCore; dsimp only [s', wvec']
                rw [(hod l).1, (hod l).2.1 hne]; exact ⟨rfl, rfl⟩
              have hoff_self : fullWatchOff s' lit.toNat = fullWatchOff s lit.toNat := by
                change fullWatchOffCore s'.core lit.toNat = fullWatchOffCore s.core lit.toNat
                unfold fullWatchOffCore; dsimp only [s', wvec']; rw [(hod lit.toNat).1]
              have hsz_self : fullWatchSize s' lit.toNat =
                  fullWatchSize s lit.toNat - cnt.toNat := by
                change fullWatchSizeCore s'.core lit.toNat =
                  fullWatchSizeCore s.core lit.toNat - cnt.toNat
                unfold fullWatchSizeCore; dsimp only [s', wvec']
                rw [(hod lit.toNat).2.2, Option.getD_some, hnewsz_toNat]; rfl
              have hslice_self : ∀ idx < fullWatchSize s lit.toNat - cnt.toNat,
                  s'.core.wstk[fullWatchOff s' lit.toNat + idx]? =
                    s.core.wstk[fullWatchOff s lit.toNat + idx]? := fun idx hidx => by
                rw [hoff_self]; dsimp only [s']
                exact hagrL _ (Or.inl (by rw [hoff_toNat, hsz_toNat]; omega))
              have hslice_other : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
                  ∀ idx < fullWatchSize s l,
                    s'.core.wstk[fullWatchOff s' l + idx]? =
                      s.core.wstk[fullWatchOff s l + idx]? := fun l hl hne idx hidx => by
                rw [(hoff_other l hl hne).1]; dsimp only [s']
                have hdisj := hlay.disjoint l lit.toNat hl hlit_lt hne
                  (by change 0 < fullWatchSize s l; omega)
                  (by change 0 < fullWatchSize s lit.toNat; omega)
                refine hagrL _ ?_
                rcases hdisj with hd | hd
                · exact Or.inl (by
                    rw [hoff_toNat, hsz_toNat]
                    unfold fullWatchSize at hidx
                    unfold fullWatchOff fullWatchSize
                    omega)
                · exact Or.inr (by
                    rw [hoff_toNat, hsz_toNat]
                    unfold fullWatchOff fullWatchSize
                    omega)
              have hlay' : WatchStackLayout s'.core := by
                refine ⟨?_, ?_, ?_, ?_⟩
                · intro l hl
                  by_cases hle : l = lit.toNat
                  · subst hle
                    change fullWatchOff s' lit.toNat + fullWatchSize s' lit.toNat ≤ s'.core.wlen
                    rw [hoff_self, hsz_self]
                    have := hlay.bounds lit.toNat hlit_lt; dsimp only [s']
                    dsimp only [fullWatchOff, fullWatchSize] at *; omega
                  · obtain ⟨ho, hs⟩ := hoff_other l hl hle
                    change fullWatchOff s' l + fullWatchSize s' l ≤ s'.core.wlen
                    rw [ho, hs]; exact hlay.bounds l hl
                · intro l hl hpos
                  by_cases hle : l = lit.toNat
                  · subst hle; change 1 ≤ fullWatchOff s' lit.toNat; rw [hoff_self]
                    change fullWatchSize s' lit.toNat > 0 at hpos; rw [hsz_self] at hpos
                    exact hlay.pos_off lit.toNat hlit_lt
                      (by change 0 < fullWatchSize s lit.toNat; omega)
                  · obtain ⟨ho, hs⟩ := hoff_other l hl hle
                    change 1 ≤ fullWatchOff s' l; rw [ho]
                    change fullWatchSize s' l > 0 at hpos; rw [hs] at hpos
                    exact hlay.pos_off l hl hpos
                · intro l1 l2 h1 h2 hne hp1 hp2
                  change fullWatchSize s' l1 > 0 at hp1; change fullWatchSize s' l2 > 0 at hp2
                  change fullWatchOff s' l1 + fullWatchSize s' l1 ≤ fullWatchOff s' l2 ∨
                    fullWatchOff s' l2 + fullWatchSize s' l2 ≤ fullWatchOff s' l1
                  by_cases hl1 : l1 = lit.toNat
                  · subst hl1
                    obtain ⟨ho2, hs2⟩ := hoff_other l2 h2 hne.symm
                    rw [hoff_self, hsz_self, ho2, hs2]
                    rw [hsz_self] at hp1; rw [hs2] at hp2
                    rcases hlay.disjoint lit.toNat l2 h1 h2 hne
                        (by change 0 < fullWatchSize s lit.toNat; omega)
                        (by change 0 < fullWatchSize s l2; omega) with d | d
                    · exact Or.inl (by dsimp only [fullWatchOff, fullWatchSize] at d ⊢; omega)
                    · exact Or.inr d
                  · by_cases hl2 : l2 = lit.toNat
                    · subst hl2
                      obtain ⟨ho1, hs1⟩ := hoff_other l1 h1 hne
                      rw [ho1, hs1, hoff_self, hsz_self]
                      rw [hs1] at hp1; rw [hsz_self] at hp2
                      rcases hlay.disjoint l1 lit.toNat h1 h2 hne
                          (by change 0 < fullWatchSize s l1; omega)
                          (by change 0 < fullWatchSize s lit.toNat; omega) with d | d
                      · exact Or.inl d
                      · exact Or.inr (by dsimp only [fullWatchOff, fullWatchSize] at d ⊢; omega)
                    · obtain ⟨ho1, hs1⟩ := hoff_other l1 h1 hl1
                      obtain ⟨ho2, hs2⟩ := hoff_other l2 h2 hl2
                      rw [ho1, hs1, ho2, hs2]; rw [hs1] at hp1; rw [hs2] at hp2
                      exact hlay.disjoint l1 l2 h1 h2 hne hp1 hp2
                · intro l hl idx hidx
                  change fullWatchSize s' l > idx at hidx
                  change s'.core.wstk[fullWatchOff s' l + idx]? ≠ some 0xFFFFFFFF#32
                  by_cases hle : l = lit.toNat
                  · subst hle; rw [hsz_self] at hidx
                    rw [hslice_self idx hidx]
                    exact hlay.no_sentinel lit.toNat hlit_lt idx
                      (by change idx < fullWatchSize s lit.toNat; omega)
                  · obtain ⟨_, hs⟩ := hoff_other l hl hle; rw [hs] at hidx
                    rw [hslice_other l hl hle idx hidx]; exact hlay.no_sentinel l hl idx hidx
              exact hQ wvec' wstkL wusable' _ hlen' hlay'
                (fun l hl hne => ⟨(hoff_other l hl hne).1, (hoff_other l hl hne).2,
                  hslice_other l hl hne⟩)
                hoff_self hsz_self hslice_self hmem'

/-- Restores `ModeWatchesInv F_cur k3` by combining `k0` on `lit` (`full_watch_pop_c0` rollback)
and `k2` on all other literals `l ≠ lit`. -/
theorem modeWatchesInv_of_pop {F_cur : List (List Nat)} {k0 k2 k3 : FullCoreState} {lit : Nat}
    (hw0 : ModeWatchesInv F_cur k0) (hw2 : ModeWatchesInv F_cur k2)
    (hlay3 : WatchStackLayout k3) (hcv2 : k2.cur_vars = k0.cur_vars)
    (hcv3 : k3.cur_vars = k0.cur_vars) (hdm2 : k2.dense_mode = k0.dense_mode)
    (hdm3 : k3.dense_mode = k0.dense_mode)
    (hsub30 : ∀ r ∈ fullArenaClauseRefsCore k0, r ∈ fullArenaClauseRefsCore k3)
    (hsub32 : ∀ r ∈ fullArenaClauseRefsCore k2, r ∈ fullArenaClauseRefsCore k3)
    (hlit : lit < 2 * k0.cur_vars)
    (hpop_lit : fullWatchSizeCore k3 lit = fullWatchSizeCore k0 lit ∧
      ∀ j < fullWatchSizeCore k0 lit,
        k3.wstk[fullWatchOffCore k3 lit + j]? = k0.wstk[fullWatchOffCore k0 lit + j]?)
    (hpop_oth : ∀ l < 2 * k0.cur_vars, l ≠ lit →
      fullWatchSizeCore k3 l = fullWatchSizeCore k2 l ∧
      ∀ j < fullWatchSizeCore k2 l,
        k3.wstk[fullWatchOffCore k3 l + j]? = k2.wstk[fullWatchOffCore k2 l + j]?) :
    ModeWatchesInv F_cur k3 := by
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  unfold ModeWatchesInv at hw0 hw2 ⊢; rw [hdm2] at hw2; rw [hdm3]
  by_cases hc : k0.dense_mode = 0#64 <;> simp only [hc, ↓reduceIte] at hw0 hw2 ⊢
  · refine ⟨hlay3, fun l hl => ?_⟩
    by_cases hle : l = lit
    · rw [hle, hpop_lit.1]
      exact FullAssignAddSpecs.watchSlice_relocate hrefl (by omega) hsub30 hpop_lit.2
        (hw0.slices lit hlit)
    · obtain ⟨hs, hslice⟩ := hpop_oth l (hcv3 ▸ hl) hle; rw [hs]
      exact FullAssignAddSpecs.watchSlice_relocate hrefl (by omega) hsub32 hslice
        (hw2.slices l (hcv2 ▸ hcv3 ▸ hl))
  · refine ⟨hlay3, fun l hl => ?_⟩
    by_cases hle : l = lit
    · rw [hle, hpop_lit.1]
      exact FullAssignAddSpecs.denseWatchSlice_relocate hrefl (by omega) hsub30 hpop_lit.2
        (hw0.slices lit hlit)
    · obtain ⟨hs, hslice⟩ := hpop_oth l (hcv3 ▸ hl) hle; rw [hs]
      exact FullAssignAddSpecs.denseWatchSlice_relocate hrefl (by omega) hsub32 hslice
        (hw2.slices l (hcv2 ▸ hcv3 ▸ hl))

/-- Restores `FullReduceSpecs.BinOnlyWatchesInv F_cur k3` by combining `k0` on `lit`
(`full_watch_pop_c0` rollback) and `k2` on all other literals `l ≠ lit`. -/
theorem binOnlyWatchesInv_of_pop {F_cur : List (List Nat)} {k0 k2 k3 : FullCoreState} {lit : Nat}
    (hb0 : FullReduceSpecs.BinOnlyWatchesInv F_cur k0)
    (hb2 : FullReduceSpecs.BinOnlyWatchesInv F_cur k2)
    (hlay3 : WatchStackLayout k3) (hcv2 : k2.cur_vars = k0.cur_vars)
    (hcv3 : k3.cur_vars = k0.cur_vars) (hlit : lit < 2 * k0.cur_vars)
    (hpop_lit : fullWatchSizeCore k3 lit = fullWatchSizeCore k0 lit ∧
      ∀ j < fullWatchSizeCore k0 lit,
        k3.wstk[fullWatchOffCore k3 lit + j]? = k0.wstk[fullWatchOffCore k0 lit + j]?)
    (hpop_oth : ∀ l < 2 * k0.cur_vars, l ≠ lit →
      fullWatchSizeCore k3 l = fullWatchSizeCore k2 l ∧
      ∀ j < fullWatchSizeCore k2 l,
        k3.wstk[fullWatchOffCore k3 l + j]? = k2.wstk[fullWatchOffCore k2 l + j]?) :
    FullReduceSpecs.BinOnlyWatchesInv F_cur k3 := by
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  refine ⟨hlay3, fun l hl => ?_⟩
  by_cases hle : l = lit
  · rw [hle, hpop_lit.1]
    exact (hb0.slices lit hlit).relocate hrefl (by omega) hpop_lit.2
  · obtain ⟨hs, hslice⟩ := hpop_oth l (hcv3 ▸ hl) hle; rw [hs]
    exact (hb2.slices l (hcv2 ▸ hcv3 ▸ hl)).relocate hrefl (by omega) hslice

end WatchPopSection

/-! ## 2. `full_add_clause` (`Full.fullAddClauseSpec`) -/

section AddClauseProof

open Full.FullAssignAddTactics
open scoped Full.FullArenaTactics Full.FullAssignAddTactics

private abbrev v2rAddClauseState (s : FullState) (len : Nat)
    (arena' wvec' wstk' : List (BitVec 32)) (wlen' : Nat)
    (wusable' fred' ni' nr' : BitVec 64) (wsort' : List (BitVec 32)) : FullState :=
  { s with
    core :=
      { s.core with
        arena := arena', arena_len := s.core.arena_len + 3 + len
        wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable'
        first_reducible := fred', num_irred := ni', num_redundant := nr' }
    scratch := { s.scratch with wsort := wsort' } }

private theorem addClauseRollback_preserves_witness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {arena' wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wusable' : BitVec 64}
    {wsort' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                            wusable := wusable' }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                    wusable := wusable' })
    (hhold : ∀ k < s.core.arena_len, arena'[k]? = s.core.arena[k]?)
    (hw_pres : ∀ l < 2 * s.core.cur_vars,
      fullWatchSizeCore
        { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                      wusable := wusable' } l = fullWatchSizeCore s.core l ∧
      ∀ idx < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore
          { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                        wusable := wusable' } l + idx]? =
          s.core.wstk[fullWatchOffCore s.core l + idx]?) :
    let s' : FullState :=
      { s with
        core := { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                              wusable := wusable' }
        scratch := { s.scratch with wsort := wsort' } }
    FullWitnessInv c F0 F_cur s'.core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (FullArenaVarsNodup s → FullArenaVarsNodup s') := by
  intro s'
  have hcl := hlen.core_ok
  have hcl' := hlen'.core_ok
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff s'.core.arena s'.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := fun r hr =>
    hw.arena.arenaNextOff_extend (alen' := s.core.arena_len) (Nat.le_refl _) hhold r hr
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hmeta : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaHdrCore s'.core r = fullArenaHdrCore s.core r ∧
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have h1 : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena_len := by omega
    have hlen_ar : s.core.arena.length = c.arena_cap := hcl.arena_len_arr
    have hlen_ar' : s'.core.arena.length = c.arena_cap := hcl'.arena_len_arr
    have hbd : s.core.arena_len ≤ c.arena_cap := hcl.arena_len_le
    have h0 := hhold r (by omega); have h2 := hhold (r + 2) (by omega)
    have hsz : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
      unfold fullArenaClauseSizeCore s'; rw [h2]
    refine ⟨by unfold fullArenaHdrCore s'; rw [h0], hsz,
      by unfold fullArenaClauseGarbCore fullArenaHdrCore s'; rw [h0],
      fullArenaClauseLitsCore_eq_of_hold (k := s.core) (k' := s'.core)
        (by rw [hlen_ar]; omega) (by rw [hlen_ar']; omega) hsz
        fun j hj => hhold (r + 3 + j) (by omega)⟩
  have ha' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      rw [hnxt r hr, (hmeta r hr).2.1]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr; rw [(hmeta r hr).1] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh
      exact ⟨t, by rw [(hmeta r hr).2.1]; exact ht1, ht2,
        by dsimp only [s']; rw [hhold t ht2]; exact hsent⟩
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hmeta r hr).2.2.1] at hng; rw [(hmeta r hr).2.2.2] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [(hmeta r hr).2.2.1] at hng; rw [(hmeta r hr).2.2.2]
      exact hw.arena.entails r hr hng
  have hwat' : ModeWatchesInv F_cur s'.core := by
    have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
      rw [CNF.entails_def]; exact fun _ h => h
    have hm0 := hw.watches
    have hdm' : s'.core.dense_mode = s.core.dense_mode := rfl
    unfold ModeWatchesInv at hm0 ⊢
    rw [hdm']
    by_cases hc : s.core.dense_mode = 0#64
    · rw [ite_eq_left hc] at hm0 ⊢
      refine ⟨hlay', fun l hl => ?_⟩
      obtain ⟨hsz, hslice⟩ := hw_pres l hl; rw [hsz]
      exact FullAssignAddSpecs.watchSlice_relocate (k := s.core) (k' := s'.core)
        hrefl (Nat.le_refl _) (fun r hr => hrefs ▸ hr) hslice (hm0.slices l hl)
    · rw [ite_eq_right hc] at hm0 ⊢
      refine ⟨hlay', fun l hl => ?_⟩
      obtain ⟨hsz, hslice⟩ := hw_pres l hl; rw [hsz]
      exact FullAssignAddSpecs.denseWatchSlice_relocate (k := s.core) (k' := s'.core)
        hrefl (Nat.le_refl _) (fun r hr => hrefs ▸ hr) hslice (hm0.slices l hl)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := ha'
      watches := hwat'
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        change if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then _ else _
        split
        · rename_i hbin; rw [ite_eq_left hbin] at hrs; exact hrs
        · rename_i hlg; rw [ite_eq_right hlg] at hrs
          obtain ⟨hr, hng, hall⟩ := hrs
          exact ⟨hrefs ▸ hr, (hmeta _ hr).2.2.1.trans hng,
            fun q hq => hall q ((hmeta _ hr).2.2.2 ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hmem := hw.reason_lit_mem idx hidx hne hlg
        have hrs := hw.reason_inv idx hidx hne
        rw [ite_eq_right (fun h => h hlg)] at hrs
        change (s.core.trl[idx]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s'.core _
        rw [(hmeta _ hrs.1).2.2.2]; exact hmem }
  have hnd' : FullArenaVarsNodup s → FullArenaVarsNodup s' := fun hnd r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    change fullArenaClauseGarbCore s'.core r = false at hng
    rw [(hmeta r hr).2.2.1] at hng
    unfold fullArenaClauseLits; rw [(hmeta r hr).2.2.2]; exact hnd r hr hng
  exact ⟨hw', hrefs, hnd'⟩

/-- `FullM7V2Robust.full_add_clause` satisfies canonical `Full.fullAddClauseSpec` cleanly across
all atomic failure rollbacks (binary pop rollback + large `arena_len` / pop rollback). -/
theorem full_add_clause_wp (Γ : Env)
    (hAlloc : ∀ args m Q X, fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hPop : ∀ args m Q X, fullWatchPopC0Spec args m Q X →
      Γ "full_watch_pop_c0" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullAddClauseSpec args m Q X →
      Func.wp Γ full_add_clause_body args m Q X := by
  rintro ⟨h, len, glue, red, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, _hlen_bd, hcl_bd, hm, hQ⟩
  have hmv := c.hmaxv; have har := c.harena; have hwcap := c.hwcap
  unfold dimacsBound at hmv har hwcap; have hco := hlen.core_ok
  have hcv_lt : s.core.cur_vars < 2 ^ 29 := by have := hco.cur_vars_le; omega
  faa_head_steps
  refine wp_head_jnz_iff (b := decide (len.toNat = 2))
    (by simpa [Arg.val_var] using bv32_beq_nat_eq (x := len) (n := 2) (by decide)) ?_
  rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun h2 => ?_, fun hne2 => ?_⟩
  · -- Binary case (`len == 2`)
    simp only [h2, show ¬ (2 < 2) by omega, ↓reduceIte] at hQ hcl_bd
    obtain ⟨hlits_lt, _hnd2, hent2⟩ := hcl_bd (by omega)
    have htm_gt0 : 0 < s.core.tmp.length := by rw [hco.tmp_len_arr]; omega
    have htm_gt1 : 1 < s.core.tmp.length := by rw [hco.tmp_len_arr]; omega
    let l0 := s.core.tmp[0]'htm_gt0; let l1 := s.core.tmp[1]'htm_gt1
    have htmp_take2 : (s.core.tmp.take 2).map BitVec.toNat = [l0.toNat, l1.toNat] := by
      refine List.ext_getElem (by simp [hco.tmp_len_arr]; omega) fun k hk _ => ?_
      match k, hk with | 0, _ => simp [l0] | 1, _ => simp [l1]
    rw [htmp_take2] at hlits_lt hent2
    have hl0_lt : l0.toNat < 2 * s.core.cur_vars := hlits_lt _ (by simp)
    have hl1_lt : l1.toNat < 2 * s.core.cur_vars := hlits_lt _ (by simp)
    have hent2_swap := entails_swap2 hent2
    let b0 := (l1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let b1 := (l0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    have hb0_ne : b0 ≠ 0xFFFFFFFF#32 := bv32_tag_bin_ne_sent (by omega)
    have hb1_ne : b1 ≠ 0xFFFFFFFF#32 := bv32_tag_bin_ne_sent (by omega)
    faa_steps; c0_call hPush
    refine ⟨c, s, R, rfl, hlen, hw.watches.layout, (fun _ => hb0_ne),
      (fun hc => absurd hc (by decide)), hm, ?_⟩
    intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 s1 hlen1 hlay1 hoth1 hok1t hok1f hm1
    have htm1_gt0 : 0 < s1.core.tmp.length := by rw [hlen1.core_ok.tmp_len_arr]; omega
    have htm1_gt1 : 1 < s1.core.tmp.length := by rw [hlen1.core_ok.tmp_len_arr]; omega
    have hwat1 : ModeWatchesInv F_cur s1.core :=
      FullAssignAddSpecs.fullWatchPush_preserves_modeWatchesInv
      hw.watches hlay1 rfl rfl (fun _ hr => hr)
      (fun _ => ⟨bv32_tag_bin_flag l1, hb0_ne,
        by rw [bv32_tag_bin_mask (by omega)]; exact hl1_lt,
        by rw [bv32_tag_bin_mask (by omega)]; exact hent2⟩)
      (fun hc => absurd hc (by decide)) hoth1 hok1t (fun h => (hok1f h).1)
    have hw1 : FullWitnessInv c F0 F_cur s1.core :=
      FullAssignAddSpecs.watchUpdate_preserves_witness hw hwat1
    faa_steps
    · subst hc; c0_call hPush
      refine ⟨c, s1, R, rfl, hlen1, hlay1, (fun _ => hb1_ne),
        (fun hc => absurd hc (by decide)), hm1, ?_⟩
      intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 s2 hlen2 hlay2 hoth2 hok2t hok2f hm2
      have hwat2 : ModeWatchesInv F_cur s2.core :=
        FullAssignAddSpecs.fullWatchPush_preserves_modeWatchesInv hwat1 hlay2 rfl rfl
          (fun _ hr => hr)
          (fun _ => ⟨bv32_tag_bin_flag l0, hb1_ne,
            by rw [bv32_tag_bin_mask (by omega)]; exact hl0_lt,
            by rw [bv32_tag_bin_mask (by omega)]; exact hent2_swap⟩)
          (fun hc => absurd hc (by decide)) hoth2 hok2t (fun h => (hok2f h).1)
      have hw2 : FullWitnessInv c F0 F_cur s2.core :=
        FullAssignAddSpecs.watchUpdate_preserves_witness hw1 hwat2
      faa_steps
      · -- Both binary pushes succeeded
        have hwat_fin : ModeWatchesInv F_cur
            { s2.core with num_binary := s.core.num_binary + 1#64 } :=
          hwat2.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
        have hw_fin : FullWitnessInv c F0 F_cur
            { s2.core with num_binary := s.core.num_binary + 1#64 } :=
          FullAssignAddSpecs.watchUpdate_preserves_witness hw (oom' := s.core.oom) hwat_fin
        exact hQ 0xFFFFFFFE#64 wvec2 wstk2 wlen2 wu2 (s.core.num_binary + 1#64) wsort2 _
          (Or.inr rfl) { core_ok := { hlen2.core_ok with vals_len := hlen2.core_ok.vals_len },
                         scratch_ok := hlen2.scratch_ok } hw_fin ‹_›
      · -- `push2` failed: `full_watch_pop_c0(h, tmp[0], 1u)` rolls back `push1`!
        obtain ⟨_, _, hsz1, hpre1, _, _⟩ := hok1t rfl
        have ht1_1 : (s1.core.tmp[1]'htm1_gt1) = l1 := rfl
        have hsz2_l0 : fullWatchSize s2 l0.toNat = fullWatchSize s l0.toNat + 1 ∧
            ∀ k < fullWatchSize s l0.toNat,
              s2.core.wstk[fullWatchOff s2 l0.toNat + k]? =
                s.core.wstk[fullWatchOff s l0.toNat + k]? := by
          by_cases heql : l0.toNat = l1.toNat
          · have hs2' := (hok2f hc).1 (by dsimp only [s1]; exact hl1_lt)
            change fullWatchSize s2 (s1.core.tmp[1]'htm1_gt1).toNat =
              fullWatchSize s1 (s1.core.tmp[1]'htm1_gt1).toNat ∧
              ∀ k < fullWatchSize s1 (s1.core.tmp[1]'htm1_gt1).toNat,
                s2.core.wstk[fullWatchOff s2 (s1.core.tmp[1]'htm1_gt1).toNat + k]? =
                  s1.core.wstk[fullWatchOff s1 (s1.core.tmp[1]'htm1_gt1).toNat + k]? at hs2'
            rw [ht1_1, ← heql] at hs2'
            exact ⟨hs2'.1.trans hsz1, fun k hk =>
              (hs2'.2 k (by
                change k < fullWatchSize s1 s.core.tmp[0].toNat
                rw [hsz1]; exact Nat.lt_succ_of_lt hk)).trans (hpre1 k hk)⟩
          · have hne' : l0.toNat ≠ (s1.core.tmp[1]'htm1_gt1).toNat := by
              rw [ht1_1]; exact heql
            obtain ⟨hs2, hk2⟩ := hoth2 l0.toNat (by dsimp only [s1]; exact hl0_lt) hne'
            change fullWatchSize s2 l0.toNat = fullWatchSize s1 l0.toNat at hs2
            change ∀ k < fullWatchSize s1 l0.toNat,
              s2.core.wstk[fullWatchOff s2 l0.toNat + k]? =
                s1.core.wstk[fullWatchOff s1 l0.toNat + k]? at hk2
            exact ⟨hs2.trans hsz1, fun k hk =>
              (hk2 k (by
                change k < fullWatchSize s1 s.core.tmp[0].toNat
                rw [hsz1]; exact Nat.lt_succ_of_lt hk)).trans (hpre1 k hk)⟩
        have htm2_gt0 : 0 < s2.core.tmp.length := by rw [hlen2.core_ok.tmp_len_arr]; omega
        have hs2_t0 : s2.core.tmp[0]'htm2_gt0 = l0 := rfl
        c0_call hPop
        refine ⟨c, s2, R, rfl, hlen2, hlay2, by rw [hs2_t0]; exact hl0_lt, by decide,
          by change 1 ≤ fullWatchSize s2 (s2.core.tmp[0]'htm2_gt0).toNat
             rw [hs2_t0, hsz2_l0.1]; exact Nat.le_add_left 1 _,
          hm2, ?_⟩
        intro wvec3 wstk3 wu3 m3 s3 hlen3 hlay3 hoth3 hoff3 hsz3 hslice3 hm3
        rw [hs2_t0] at hsz3 hslice3 hoth3
        have hoth3' : ∀ l < 2 * s.core.cur_vars, l ≠ l0.toNat →
            fullWatchSizeCore s3.core l = fullWatchSizeCore s2.core l ∧
            ∀ j < fullWatchSizeCore s2.core l,
              s3.core.wstk[fullWatchOffCore s3.core l + j]? =
                s2.core.wstk[fullWatchOffCore s2.core l + j]? := fun l hl hne => by
          obtain ⟨_, hs3, hk3⟩ := hoth3 l (by dsimp only [s2, s1]; exact hl) hne
          exact ⟨hs3, hk3⟩
        have hsz3_sub : fullWatchSize s3 l0.toNat = fullWatchSize s l0.toNat := by
          change fullWatchSize s3 l0.toNat = fullWatchSize s2 l0.toNat - 1 at hsz3
          rw [hsz3, hsz2_l0.1, Nat.add_sub_cancel]
        have hwat3 : ModeWatchesInv F_cur s3.core :=
          modeWatchesInv_of_pop hw.watches hwat2 hlay3 rfl rfl rfl rfl
            (fun _ hr => hr) (fun _ hr => hr) hl0_lt
            ⟨hsz3_sub, fun k hk =>
              (hslice3 k (by
                change fullWatchSize s2 l0.toNat - 1 > k
                rw [hsz2_l0.1, Nat.add_sub_cancel]; exact hk)).trans (hsz2_l0.2 k hk)⟩
            hoth3'
        have hw3 : FullWitnessInv c F0 F_cur s3.core :=
          FullAssignAddSpecs.watchUpdate_preserves_witness hw hwat3
        faa_steps
        exact hQ 0xFFFFFFFF#64 wvec3 wstk3 wlen2 wu3 s.core.num_binary wsort2 m3
          (Or.inl rfl) hlen3 hw3 hm3
    · exact hQ 0xFFFFFFFF#64 wvec1 wstk1 wlen1 wu1 s.core.num_binary wsort1 m1 (Or.inl rfl)
        hlen1 hw1 hm1
  · -- Non-binary case
    faa_head_steps
    refine wp_head_jnz_iff (b := decide (len.toNat < 3))
      (by simp only [Arg.val_var]; simpa [bv_ofNat_toNat_eq len] using
        bv32_ult_eq len.isLt (b := 3) (by decide)) ?_
    rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hlt3 => ?_, fun hge3 => ?_⟩
    · simp only [show len.toNat < 2 by omega, ↓reduceIte] at hQ; faa_steps; exact hQ
    · have hge3' : 3 ≤ len.toNat := by omega
      simp only [show ¬ (len.toNat < 2) by omega, hne2, ↓reduceIte] at hQ
      have hs_alen_lt32 : s.core.arena_len < 0xFFFFFFFF := by have := hco.arena_len_le; omega
      have hs_alen_lt64 : s.core.arena_len < 2 ^ 64 := by omega
      have hcref_ne : BitVec.ofNat 64 s.core.arena_len ≠ 0xFFFFFFFF#64 := fun he => by
        have h := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs_alen_lt64] at h
        change s.core.arena_len = 0xFFFFFFFF at h; omega
      obtain ⟨hlits_lt, hnd_tmp, hent_cl⟩ := hcl_bd (by omega)
      faa_steps; c0_call hAlloc; refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
      split
      · faa_steps
        · exact hQ 0xFFFFFFFF#64 s.core.arena s.core.arena_len s.core.wvec s.core.wstk
            s.core.wlen s.core.wusable s.core.first_reducible s.core.num_irred
            s.core.num_redundant s.scratch.wsort m (Or.inl rfl) hlen hw (fun _ h => h) id
            (fun hc => absurd hc.symm hcref_ne) hm
        · exact absurd rfl (by assumption)
      · intro arena1 m1 alen1 s1_st hlen1 hhold1 hnoshrk1 hnogarb1 _hred1 hsz1 hm1
        faa_steps
        refine wp_loop_group (ts := [i32]) (fun r (iv, ()) mc => ∃ i arena',
          i ≤ len.toNat ∧ r = len.toNat - i ∧ iv = BitVec.ofNat 32 i ∧
          arena'.length = c.arena_cap ∧
          (∀ k < s.core.arena_len + 3, arena'[k]? = arena1[k]?) ∧
          (∀ k < i, arena'[s.core.arena_len + 3 + k]? = s.core.tmp[k]?) ∧
          (FullMem c { s1_st with core := { s1_st.core with arena := arena' } } ⋆ R) mc) ?_ ?_
        · rintro L r ⟨iv, ⟨⟩⟩ mc ih ⟨i, arena', hile, rfl, rfl, harl, hpre, hcp, hmc⟩
          faa_head_steps
          refine wp_head_jnz_iff (b := decide (i < len.toNat)) (by
            simp only [Arg.val_var]
            simpa [bv_ofNat_toNat_eq len] using bv32_ult_eq (a := i) (by omega) len.isLt) ?_
          rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hilt => ?_, fun hige => ?_⟩
          · have htm_bd_i : i <
                ({ s1_st with core := { s1_st.core with arena := arena' } }).core.tmp.length := by
              simp [s1_st, hco.tmp_len_arr]; omega
            have har_bd : s.core.arena_len + 3 + i < arena'.length := by
              have := hlen1.core_ok.arena_len_le; simp [s1_st, alen1] at this; omega
            have hidx_eq : ((BitVec.ofNat 32 i).setWidth 64) * 4 = BitVec.ofNat 64 (4 * i) := by
              rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega)]; bv_omega
            have hidx2 : c.pArena + ((BitVec.ofNat 64 s.core.arena_len + (3 : BitVec 64) +
                BitVec.ofNat 64 i) * 4) =
                c.pArena + BitVec.ofNat 64 (4 * (s.core.arena_len + 3 + i)) := by bv_omega
            faa_lets; try rw [hidx_eq]
            refine wp_load_of (FullArenaTactics.load_full_tmp (i := i) htm_bd_i hmc) ?_
            faa_lets; rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), hidx2]
            let lit_i := s.core.tmp[i]'(by rw [hco.tmp_len_arr]; omega)
            obtain ⟨ok_ar, hm_ar⟩ :=
              FullArenaTactics.store_full_arena (i := s.core.arena_len + 3 + i) lit_i
                (by simpa [s1_st] using har_bd) hmc
            refine ⟨ok_ar, ?_⟩; faa_lets
            rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
              show BitVec.ofNat 32 i + BitVec.ofNat 32 1 = BitVec.ofNat 32 (i + 1) by bv_omega]
            exact ih (len.toNat - (i + 1)) (BitVec.ofNat 32 (i + 1), ()) _ (by omega)
              ⟨i + 1, arena'.set (s.core.arena_len + 3 + i) lit_i, by omega, rfl, rfl,
                by simp [harl],
                (fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hpre k hk),
                (fun k hk => by
                  by_cases hki : k = i
                  · subst hki; rw [List.getElem?_set_self har_bd,
                      List.getElem?_eq_getElem (by rw [hco.tmp_len_arr]; omega)]
                  · rw [List.getElem?_set_ne (by omega)]; exact hcp k (by omega)), hm_ar⟩
          · have hieq : i = len.toNat := by omega
            subst hieq
            let s_cp : FullState := { s1_st with core := { s1_st.core with arena := arena' } }
            have hhold_cp : ∀ k < s.core.arena_len, arena'[k]? = s.core.arena[k]? := fun k hk =>
              (hpre k (by omega)).trans (hhold1 k hk)
            have hnoshrk_cp : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
              rw [hpre s.core.arena_len (by omega)]; exact hnoshrk1
            have hnogarb_cp : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32 := by
              rw [hpre s.core.arena_len (by omega)]; exact hnogarb1
            have hsz_cp : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len.toNat := by
              rw [hpre (s.core.arena_len + 2) (by omega)]; exact hsz1
            have hrefs_cp :
                fullArenaClauseRefsCore s_cp.core =
                  fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
              fullArenaClauseRefsCore_append hw.arena hge3' rfl hhold_cp hnoshrk_cp hsz_cp
            have hwat_cp : ModeWatchesInv F_cur s_cp.core :=
              hw.watches.with_wstk rfl rfl rfl rfl rfl
                (fun r hr => hrefs_cp ▸ List.mem_append_left _ hr)
            have hlen_cp : s_cp.LengthsOk c :=
              { core_ok := { hlen1.core_ok with arena_len_arr := by simp [s_cp, harl] }
                scratch_ok := hlen1.scratch_ok }
            have hlits_cp : fullArenaClauseLits s_cp s.core.arena_len =
                (s.core.tmp.take len.toNat).map BitVec.toNat := by
              have hle_len : s.core.arena_len + 3 + len.toNat ≤ arena'.length := by
                have := hlen1.core_ok.arena_len_le; simp [s1_st, alen1] at this; omega
              apply List.ext_getElem
              · simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_cp,
                  hsz_cp, harl, hco.tmp_len_arr]
                omega
              · intro k hk1 _
                have hk_lt : k < len.toNat := by
                  simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_cp,
                    hsz_cp] at hk1
                  omega
                have hcpk := hcp k hk_lt
                rw [List.getElem?_eq_getElem (by omega),
                  List.getElem?_eq_getElem (by rw [hco.tmp_len_arr]; omega)] at hcpk
                simp [fullArenaClauseLits, fullArenaClauseLitsCore, fullArenaClauseSizeCore, s_cp,
                  hsz_cp, Option.some.inj hcpk]
            have hcref32_ne : BitVec.ofNat 32 s.core.arena_len ≠ 0xFFFFFFFF#32 := fun he => by
              have ht := congrArg BitVec.toNat he
              rw [bv32_ofNat_toNat (by omega)] at ht
              change s.core.arena_len = 0xFFFFFFFF at ht; omega
            have hcref32_lt : (BitVec.ofNat 32 s.core.arena_len).toNat < 0x80000000 := by
              rw [bv32_ofNat_toNat (by omega)]; omega
            have htm_cp0 : 0 < s_cp.core.tmp.length := by
              simp [s_cp, s1_st, hco.tmp_len_arr]; omega
            have htm_cp1 : 1 < s_cp.core.tmp.length := by
              simp [s_cp, s1_st, hco.tmp_len_arr]; omega
            faa_steps; rw [bv64_trunc32_ofNat (by omega)]; c0_call hPush
            refine ⟨c, s_cp, R, rfl, hlen_cp, hwat_cp.layout, (fun hc => absurd hc (by decide)),
              (fun _ => ⟨bv32_mask_ne_sent _, hcref32_ne⟩), hmc, ?_⟩
            intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 s1 hlen1' hlay1 hoth1 hok1t hok1f hm1'
            have htm_s1_0 : 0 < s1.core.tmp.length := by
              simp [s1, s_cp, s1_st, hlen1'.core_ok.tmp_len_arr]; omega
            have htm_s1_1 : 1 < s1.core.tmp.length := by
              simp [s1, s_cp, s1_st, hlen1'.core_ok.tmp_len_arr]; omega
            have hrefs1 :
                fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s_cp.core := rfl
            have hwat1 : ModeWatchesInv F_cur s1.core :=
              FullAssignAddSpecs.fullWatchPush_preserves_modeWatchesInv
                hwat_cp hlay1 rfl rfl (fun r hr => hrefs1 ▸ hr)
                (fun hc => absurd hc (by decide)) (fun _ => ⟨bv32_mask_flag0 _,
                  fun hdm' => absurd hdm hdm', hcref32_lt,
                  hrefs1 ▸ hrefs_cp ▸ List.mem_append_right _
                    (by simp [bv32_ofNat_toNat (by omega : s.core.arena_len < 2 ^ 32)])⟩)
                hoth1 hok1t (fun h => (hok1f h).1)
            faa_steps
            · -- `push1` succeeded -> try `push2`
              rw [bv64_trunc32_ofNat (by omega)]; c0_call hPush
              refine ⟨c, s1, R, rfl, hlen1', hlay1, (fun hc => absurd hc (by decide)),
                (fun _ => ⟨bv32_mask_ne_sent _, hcref32_ne⟩), hm1', ?_⟩
              intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 s2 hlen2 hlay2 hoth2 hok2t hok2f hm2
              have hrefs2 : fullArenaClauseRefsCore s2.core = fullArenaClauseRefsCore s1.core := rfl
              have hwat2 : ModeWatchesInv F_cur s2.core :=
                FullAssignAddSpecs.fullWatchPush_preserves_modeWatchesInv
                  hwat1 hlay2 rfl rfl (fun r hr => hrefs2 ▸ hr)
                  (fun hc => absurd hc (by decide)) (fun _ => ⟨bv32_mask_flag0 _,
                    fun hdm' => absurd hdm hdm', hcref32_lt,
                    hrefs2 ▸ hrefs1 ▸ hrefs_cp ▸ List.mem_append_right _
                      (by simp [bv32_ofNat_toNat (by omega : s.core.arena_len < 2 ^ 32)])⟩)
                  hoth2 hok2t (fun h => (hok2f h).1)
              have hfin : ∀ fred' ni' nr' mf,
                  (FullMem c (v2rAddClauseState s len.toNat arena' wvec2 wstk2 wlen2 wu2
                    fred' ni' nr' wsort2) ⋆ R) mf → Q (BitVec.ofNat 64 s.core.arena_len, ()) mf :=
                fun fred' ni' nr' mf hm_f => by
                  let s_fin := v2rAddClauseState s len.toNat arena' wvec2 wstk2 wlen2 wu2
                    fred' ni' nr' wsort2
                  have hlen_f : s_fin.LengthsOk c :=
                    { core_ok := { hlen2.core_ok with arena_len_arr := by simp [s_fin, harl] }
                      scratch_ok := hlen2.scratch_ok }
                  have hrefs_f0 :
                      fullArenaClauseRefsCore s_fin.core =
                        fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
                    fullArenaClauseRefsCore_append hw.arena hge3' rfl hhold_cp hnoshrk_cp hsz_cp
                  have hwat_f : ModeWatchesInv F_cur s_fin.core :=
                    hwat2.with_wstk rfl rfl rfl rfl rfl
                      (fun r hr => by
                        have h1 : fullArenaClauseRefsCore s2.core =
                            fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
                          hrefs2.trans (hrefs1.trans hrefs_cp)
                        rwa [hrefs_f0, ← h1])
                  have hlits_fin : fullArenaClauseLitsCore s_fin.core s.core.arena_len =
                      (s.core.tmp.take len.toNat).map BitVec.toNat := hlits_cp
                  obtain ⟨hw_f, hrefs_f, hhold_f⟩ :=
                    FullAssignAddSpecs.addEntailedClause_preserves_witness
                      hlen hw hlen_f hge3' hlits_lt hent_cl hhold_cp hnoshrk_cp hsz_cp hlits_fin
                      hwat_f
                  have hgarb_f : fullArenaClauseGarb s_fin s.core.arena_len = false := by
                    change (fullArenaHdrCore s_fin.core s.core.arena_len &&&
                      0x00080000#32 != 0#32) = false
                    unfold fullArenaHdrCore; simp [s_fin, hnogarb_cp]
                  have hnd_f : FullArenaVarsNodup s → FullArenaVarsNodup s_fin :=
                    fun hnd r hr hng => by
                      change r ∈ fullArenaClauseRefsCore s_fin.core at hr
                      rw [hrefs_f, List.mem_append, List.mem_singleton] at hr
                      rcases hr with hr | rfl
                      · change fullArenaClauseGarbCore s_fin.core r = false at hng
                        rw [(hhold_f r hr).1] at hng
                        unfold fullArenaClauseLits; rw [(hhold_f r hr).2]
                        exact hnd r hr hng
                      · unfold fullArenaClauseLits
                        rw [show fullArenaClauseLitsCore s_fin.core s.core.arena_len =
                            (s.core.tmp.take len.toNat).map BitVec.toNat from hlits_fin,
                          List.map_map]
                        exact hnd_tmp
                  exact hQ (BitVec.ofNat 64 s.core.arena_len) arena' alen1 wvec2 wstk2 wlen2 wu2
                    fred' ni' nr' wsort2 mf (Or.inr rfl) hlen_f hw_f
                    (fun r hr => by
                      change r ∈ fullArenaClauseRefsCore s_fin.core
                      rw [hrefs_f]; exact List.mem_append_left _ hr)
                    hnd_f
                    (fun _ => ⟨rfl,
                      by change s.core.arena_len ∈ fullArenaClauseRefsCore s_fin.core
                         rw [hrefs_f]; exact List.mem_append_right _ (by simp),
                      hgarb_f, hlits_fin⟩)
                    hm_f
              faa_steps
              · exact hfin (BitVec.ofNat 64 s.core.arena_len) s.core.num_irred
                  (s.core.num_redundant + 1#64) _ (by assumption)
              · exact hfin s.core.first_reducible s.core.num_irred
                  (s.core.num_redundant + 1#64) _ (by assumption)
              · exact hfin s.core.first_reducible (s.core.num_irred + 1#64)
                  s.core.num_redundant _ (by assumption)
              · -- `push2` failed: `full_watch_pop_c0(h, tmp[0], 2u); h->arena_len = cref;`
                have hl0_lt : (s.core.tmp[0]'htm_cp0).toNat < 2 * s.core.cur_vars := by
                  have hlt := hlits_lt (s.core.tmp[0]'htm_cp0).toNat
                    (List.mem_map.mpr ⟨s.core.tmp[0]'htm_cp0,
                      List.mem_iff_getElem.mpr ⟨0, by simp [hco.tmp_len_arr]; omega, by simp⟩, rfl⟩)
                  simpa using hlt
                have hl1_lt : (s.core.tmp[1]'htm_cp1).toNat < 2 * s.core.cur_vars := by
                  have hlt := hlits_lt (s.core.tmp[1]'htm_cp1).toNat
                    (List.mem_map.mpr ⟨s.core.tmp[1]'htm_cp1,
                      List.mem_iff_getElem.mpr ⟨1, by simp [hco.tmp_len_arr]; omega, by simp⟩, rfl⟩)
                  simpa using hlt
                obtain ⟨_, _, hsz1, hpre1, _, _⟩ := hok1t (by assumption)
                have hsz1_s : fullWatchSize s1 (s.core.tmp[0]'htm_cp0).toNat =
                    fullWatchSize s (s.core.tmp[0]'htm_cp0).toNat + 2 := hsz1
                have hpre1_s : ∀ k < fullWatchSize s (s.core.tmp[0]'htm_cp0).toNat,
                    s1.core.wstk[fullWatchOff s1 (s.core.tmp[0]'htm_cp0).toNat + k]? =
                      s.core.wstk[fullWatchOff s (s.core.tmp[0]'htm_cp0).toNat + k]? := hpre1
                have hsz2_l0 : fullWatchSize s2 (s.core.tmp[0]'htm_cp0).toNat =
                    fullWatchSize s (s.core.tmp[0]'htm_cp0).toNat + 2 ∧
                    ∀ k < fullWatchSize s (s.core.tmp[0]'htm_cp0).toNat,
                      s2.core.wstk[fullWatchOff s2 (s.core.tmp[0]'htm_cp0).toNat + k]? =
                        s.core.wstk[fullWatchOff s (s.core.tmp[0]'htm_cp0).toNat + k]? := by
                  by_cases heql : (s.core.tmp[0]'htm_cp0).toNat = (s.core.tmp[1]'htm_cp1).toNat
                  · obtain ⟨hs2, hk2⟩ :=
                      (hok2f hc).1 (by dsimp only [s1, s_cp, s1_st]; exact hl1_lt)
                    have ht1_1 : (s1.core.tmp[1]'htm_s1_1) = s.core.tmp[1]'htm_cp1 := rfl
                    change fullWatchSize s2 (s1.core.tmp[1]'htm_s1_1).toNat =
                      fullWatchSize s1 (s1.core.tmp[1]'htm_s1_1).toNat at hs2
                    change ∀ k < fullWatchSize s1 (s1.core.tmp[1]'htm_s1_1).toNat,
                      s2.core.wstk[fullWatchOff s2 (s1.core.tmp[1]'htm_s1_1).toNat + k]? =
                        s1.core.wstk[fullWatchOff s1 (s1.core.tmp[1]'htm_s1_1).toNat + k]? at hk2
                    rw [ht1_1, ← heql] at hs2 hk2
                    exact ⟨hs2.trans hsz1_s, fun k hk =>
                      (hk2 k (by rw [hsz1_s]; omega)).trans (hpre1_s k hk)⟩
                  · obtain ⟨hs2, hk2⟩ := hoth2 (s.core.tmp[0]'htm_cp0).toNat
                      (by dsimp only [s1, s_cp, s1_st]; exact hl0_lt) heql
                    change fullWatchSize s2 (s.core.tmp[0]'htm_cp0).toNat =
                      fullWatchSize s1 (s.core.tmp[0]'htm_cp0).toNat at hs2
                    change ∀ k < fullWatchSize s1 (s.core.tmp[0]'htm_cp0).toNat,
                      s2.core.wstk[fullWatchOff s2 (s.core.tmp[0]'htm_cp0).toNat + k]? =
                        s1.core.wstk[fullWatchOff s1 (s.core.tmp[0]'htm_cp0).toNat + k]? at hk2
                    exact ⟨hs2.trans hsz1_s, fun k hk =>
                      (hk2 k (by rw [hsz1_s]; omega)).trans (hpre1_s k hk)⟩
                have hsz2_oth : ∀ l < 2 * s.core.cur_vars,
                    l ≠ (s.core.tmp[0]'htm_cp0).toNat →
                    fullWatchSize s2 l = fullWatchSize s l ∧
                    ∀ k < fullWatchSize s l,
                      s2.core.wstk[fullWatchOff s2 l + k]? =
                        s.core.wstk[fullWatchOff s l + k]? := fun l hl hne => by
                  obtain ⟨hs1o, hk1o⟩ := hoth1 l (by dsimp only [s_cp, s1_st]; exact hl) hne
                  change fullWatchSize s1 l = fullWatchSize s l at hs1o
                  change ∀ k < fullWatchSize s l,
                    s1.core.wstk[fullWatchOff s1 l + k]? =
                      s.core.wstk[fullWatchOff s l + k]? at hk1o
                  by_cases heql : l = (s.core.tmp[1]'htm_cp1).toNat
                  · subst heql
                    obtain ⟨hs2o, hk2o⟩ := (hok2f hc).1 (by dsimp only [s1, s_cp, s1_st]; exact hl)
                    have ht1_1 : (s1.core.tmp[1]'htm_s1_1) = s.core.tmp[1]'htm_cp1 := rfl
                    change fullWatchSize s2 (s1.core.tmp[1]'htm_s1_1).toNat =
                      fullWatchSize s1 (s1.core.tmp[1]'htm_s1_1).toNat at hs2o
                    change ∀ k < fullWatchSize s1 (s1.core.tmp[1]'htm_s1_1).toNat,
                      s2.core.wstk[fullWatchOff s2 (s1.core.tmp[1]'htm_s1_1).toNat + k]? =
                        s1.core.wstk[fullWatchOff s1 (s1.core.tmp[1]'htm_s1_1).toNat + k]? at hk2o
                    rw [ht1_1] at hs2o hk2o
                    exact ⟨hs2o.trans hs1o,
                      fun k hk => (hk2o k (by rw [hs1o]; exact hk)).trans (hk1o k hk)⟩
                  · obtain ⟨hs2o, hk2o⟩ := hoth2 l (by dsimp only [s1, s_cp, s1_st]; exact hl) heql
                    change fullWatchSize s2 l = fullWatchSize s1 l at hs2o
                    change ∀ k < fullWatchSize s1 l,
                      s2.core.wstk[fullWatchOff s2 l + k]? =
                        s1.core.wstk[fullWatchOff s1 l + k]? at hk2o
                    exact ⟨hs2o.trans hs1o,
                      fun k hk => (hk2o k (by rw [hs1o]; exact hk)).trans (hk1o k hk)⟩
                have htm2_gt0 : 0 < s2.core.tmp.length := by rw [hlen2.core_ok.tmp_len_arr]; omega
                c0_call hPop
                refine ⟨c, s2, R, rfl, hlen2, hlay2,
                  by dsimp only [s2, s1, s_cp, s1_st]; exact hl0_lt,
                  by decide, by rw [hsz2_l0.1]; omega, hm2, ?_⟩
                intro wvec3 wstk3 wu3 m3 s3 hlen3 hlay3 hoth3 hoff3 hsz3 hslice3 hm3
                have hsz3_2 : fullWatchSize s3 (s.core.tmp[0]'htm_cp0).toNat =
                    fullWatchSize s2 (s.core.tmp[0]'htm_cp0).toNat - 2 := hsz3
                have hslice3_2 : ∀ idx < fullWatchSize s2 (s.core.tmp[0]'htm_cp0).toNat - 2,
                    s3.core.wstk[fullWatchOff s3 (s.core.tmp[0]'htm_cp0).toNat + idx]? =
                      s2.core.wstk[fullWatchOff s2 (s.core.tmp[0]'htm_cp0).toNat + idx]? := hslice3
                faa_steps
                let s_r2 : FullState :=
                  { s with
                    core := { s.core with arena := arena', wvec := wvec3, wstk := wstk3,
                                          wlen := wlen2, wusable := wu3 }
                    scratch := { s.scratch with wsort := wsort2 } }
                have hlen_r2 : s_r2.LengthsOk c :=
                  { core_ok := { hlen3.core_ok with
                      arena_len_le := by
                        change s.core.arena_len ≤ c.arena_cap; exact hco.arena_len_le }
                    scratch_ok := hlen3.scratch_ok }
                have hlay_r2 : WatchStackLayout s_r2.core :=
                  hlay3.with_wstk rfl rfl rfl rfl
                have hpres_r2 : ∀ l < 2 * s.core.cur_vars,
                    fullWatchSizeCore s_r2.core l = fullWatchSizeCore s.core l ∧
                    ∀ idx < fullWatchSizeCore s.core l,
                      wstk3[fullWatchOffCore s_r2.core l + idx]? =
                        s.core.wstk[fullWatchOffCore s.core l + idx]? := fun l hl => by
                  by_cases hll0 : l = (s.core.tmp[0]'htm_cp0).toNat
                  · subst hll0
                    refine ⟨by
                        change fullWatchSize s3 (s.core.tmp[0]'htm_cp0).toNat =
                          fullWatchSize s (s.core.tmp[0]'htm_cp0).toNat
                        rw [hsz3_2, hsz2_l0.1, Nat.add_sub_cancel],
                      fun idx hidx =>
                        (hslice3_2 idx (by rw [hsz2_l0.1, Nat.add_sub_cancel]; exact hidx)).trans
                          (hsz2_l0.2 idx hidx)⟩
                  · obtain ⟨_, hs32, hk32⟩ :=
                      hoth3 l (by dsimp only [s2, s1, s_cp, s1_st]; exact hl) hll0
                    obtain ⟨hs20, hk20⟩ := hsz2_oth l hl hll0
                    change fullWatchSize s2 l = fullWatchSize s l at hs20
                    change ∀ idx < fullWatchSize s l,
                      s2.core.wstk[fullWatchOff s2 l + idx]? =
                        s.core.wstk[fullWatchOff s l + idx]? at hk20
                    exact ⟨hs32.trans hs20,
                      fun idx hidx => (hk32 idx (by rw [hs20]; exact hidx)).trans (hk20 idx hidx)⟩
                obtain ⟨hw_r2, hrefs_r2, hnd_r2⟩ := addClauseRollback_preserves_witness
                  hlen hw hlen_r2 hlay_r2 hhold_cp hpres_r2
                exact hQ 0xFFFFFFFF#64 arena' s.core.arena_len wvec3 wstk3 wlen2 wu3
                  s.core.first_reducible s.core.num_irred s.core.num_redundant wsort2 m
                  (Or.inl rfl) hlen_r2 hw_r2
                  (fun r hr => hrefs_r2 ▸ hr) hnd_r2
                  (fun hc' => absurd hc'.symm hcref_ne)
                  (by simpa only [s_r2, s3, s2, s1, s_cp, s1_st] using hm)
            · -- `push1` failed: `h->arena_len = cref;`
              faa_steps
              let s_r1 : FullState :=
                { s with
                  core := { s.core with arena := arena', wvec := wvec1, wstk := wstk1,
                                        wlen := wlen1, wusable := wu1 }
                  scratch := { s.scratch with wsort := wsort1 } }
              have hlen_r1 : s_r1.LengthsOk c :=
                { core_ok := { hlen1'.core_ok with
                    arena_len_le := by
                      change s.core.arena_len ≤ c.arena_cap; exact hco.arena_len_le }
                  scratch_ok := hlen1'.scratch_ok }
              have hlay_r1 : WatchStackLayout s_r1.core :=
                hlay1.with_wstk rfl rfl rfl rfl
              have hpres_r1 : ∀ l < 2 * s.core.cur_vars,
                  fullWatchSizeCore s_r1.core l = fullWatchSizeCore s.core l ∧
                  ∀ idx < fullWatchSizeCore s.core l,
                    wstk1[fullWatchOffCore s_r1.core l + idx]? =
                      s.core.wstk[fullWatchOffCore s.core l + idx]? := fun l hl => by
                by_cases hll0 : l = (s.core.tmp[0]'htm_cp0).toNat
                · subst hll0; exact (hok1f hc).1 (by dsimp only [s_cp, s1_st]; omega)
                · exact hoth1 l (by dsimp only [s_cp, s1_st]; omega) hll0
              obtain ⟨hw_r1, hrefs_r1, hnd_r1⟩ := addClauseRollback_preserves_witness
                hlen hw hlen_r1 hlay_r1 hhold_cp hpres_r1
              exact hQ 0xFFFFFFFF#64 arena' s.core.arena_len wvec1 wstk1 wlen1 wu1
                s.core.first_reducible s.core.num_irred s.core.num_redundant wsort1 m
                (Or.inl rfl) hlen_r1 hw_r1
                (fun r hr => hrefs_r1 ▸ hr) hnd_r1
                (fun hc' => absurd hc'.symm hcref_ne)
                (by simpa only [s_r1, s1, s_cp, s1_st] using hm)
        · intro J hJ; faa_steps
          exact hJ len.toNat (0#32, ()) m1 ⟨0, arena1, Nat.zero_le _, Nat.sub_zero _, rfl,
            hlen1.core_ok.arena_len_arr, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _),
            hm1⟩

end AddClauseProof

/-! ## 3. `full_sweep_copy` (`Full.fullSweepCopySpec`) -/

section SweepCopyProof

open Full.FullReduceTactics Full.FullReduceHelpers
open scoped Full.FullArenaTactics Full.FullReduceTactics

private theorem v2r_m7scRedBinOnlySlice_get {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : FullReduceSpecs.BinOnlyWatchSliceOk F_cur k lit p rem) :
    ∀ i < rem, let w := k.wstk[p + i]?.getD 0#32
      (w &&& 0x80000000#32) ≠ 0#32 ∧ (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat]) := by
  induction h with
  | empty => intro i hi; omega
  | bin hw hmsb _ hlt hent _ ih =>
    intro i hi; cases i with
    | zero => simpa [hw] using ⟨hmsb, hlt, hent⟩
    | succ j => simpa [Nat.add_assoc, Nat.add_comm 1 j] using ih j (by omega)

private theorem v2r_m7scRedBinOnlySlice_of_all {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) {lit p rem : Nat} (hbd : p + rem ≤ k.wstk.length)
    (hall : ∀ i < rem, let w := k.wstk[p + i]?.getD 0#32
      (w &&& 0x80000000#32) ≠ 0#32 ∧ (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat])) :
    FullReduceSpecs.BinOnlyWatchSliceOk F_cur k lit p rem := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx; have hcv := hlen.cur_vars_le
  induction rem generalizing p with
  | zero => exact .empty
  | succ r ih =>
    have hp_lt : p < k.wstk.length := by omega
    have h0 := hall 0 (Nat.zero_lt_succ r)
    rw [Nat.add_zero, List.getElem?_eq_getElem hp_lt, Option.getD_some] at h0
    have hne : k.wstk[p]'hp_lt ≠ 0xFFFFFFFF#32 := by
      intro heq; have h2 := h0.2.1; rw [heq] at h2
      have hm : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := by decide
      rw [hm] at h2; omega
    refine .bin (List.getElem?_eq_getElem hp_lt) h0.1 hne h0.2.1 h0.2.2
      (ih (by omega) fun j hj => ?_)
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using hall (j + 1) (by omega)

private theorem v2r_m7scRedBinOnly_to_full {F_cur : List (List Nat)} {k : FullCoreState}
    (h : FullReduceSpecs.BinOnlyWatchesInv F_cur k) : FullBinOnlyWatchesInv F_cur k :=
  ⟨h.layout, fun l hl => v2r_m7scRedBinOnlySlice_get (h.slices l hl)⟩

private theorem v2r_m7scFullBinOnly_to_red {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (h : FullBinOnlyWatchesInv F_cur k) :
    FullReduceSpecs.BinOnlyWatchesInv F_cur k :=
  ⟨h.1, fun l hl => v2r_m7scRedBinOnlySlice_of_all hlen
    (by have := h.1.bounds l hl; have := hlen.wlen_le; have := hlen.wstk_len_arr; omega)
    (h.2 l hl)⟩

private theorem v2r_m7sc_witness_with_ar {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {dst : Nat} {ar' : List (BitVec 32)}
    (har_len : s.core.arena.length = c.arena_cap) (hdst_le : dst ≤ c.arena_cap)
    (hcl0 : s.core.cur_level = 0)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst })
    (har' : ar'.length = c.arena_cap) (hpre : PrefixAgrees dst s.core.arena ar') :
    FullWitnessInv c F0 F_cur { s.core with arena := ar', arena_len := dst } := by
  let k0 : FullCoreState := { s.core with arena_len := dst }
  let k1 : FullCoreState := { s.core with arena := ar', arena_len := dst }
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k0,
      fullArenaNextOff k1.arena k0.arena_len r = fullArenaNextOff k0.arena k0.arena_len r :=
    fun r hr => hw_dst.arena.arenaNextOff_extend (Nat.le_refl _) (fun i hi => hpre i hi) r hr
  have hrefs : fullArenaClauseRefsCore k1 = fullArenaClauseRefsCore k0 :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hmeta : ∀ r ∈ fullArenaClauseRefsCore k0,
      fullArenaHdrCore k1 r = fullArenaHdrCore k0 r ∧
      fullArenaClauseSizeCore k1 r = fullArenaClauseSizeCore k0 r ∧
      fullArenaClauseGarbCore k1 r = fullArenaClauseGarbCore k0 r ∧
      fullArenaClauseLitsCore k1 r = fullArenaClauseLitsCore k0 r := fun r hr => by
    have hwf := hw_dst.arena.refs_wf r hr
    have h1 : r + 3 + fullArenaClauseSizeCore k0 r ≤ fullArenaNextOff k0.arena dst r := hwf.2.2.1
    have h3 : fullArenaNextOff k0.arena dst r ≤ dst := hwf.2.2.2.1
    have hk0_len : k0.arena.length = c.arena_cap := har_len
    have hk1_len : k1.arena.length = c.arena_cap := har'
    have h0 := hpre r (by omega); have h2 := hpre (r + 2) (by omega)
    have hsz : fullArenaClauseSizeCore k1 r = fullArenaClauseSizeCore k0 r := by
      unfold fullArenaClauseSizeCore k1 k0; rw [h2]
    refine ⟨by unfold fullArenaHdrCore k1 k0; rw [h0], hsz,
      by unfold fullArenaClauseGarbCore fullArenaHdrCore k1 k0; rw [h0],
      fullArenaClauseLitsCore_eq_of_hold (by omega) (by omega) hsz
        fun j hj => hpre (r + 3 + j) (by omega)⟩
  have harena1 : FullArenaClausesInv c F_cur k1 := by
    refine ⟨hw_dst.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have h := hw_dst.arena.refs_wf r hr
      dsimp only [k1, k0] at hnxt h ⊢; rw [hnxt r hr, (hmeta r hr).2.1]; exact h
    · intro r hr hsh; rw [hrefs] at hr; rw [(hmeta r hr).1] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw_dst.arena.shrk_term r hr hsh
      dsimp only [k0] at ht2
      exact ⟨t, by rw [(hmeta r hr).2.1]; exact ht1, ht2,
        by dsimp only [k1]; rw [hpre t ht2]; exact hsent⟩
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hmeta r hr).2.2.1] at hng; rw [(hmeta r hr).2.2.2] at hl
      exact hw_dst.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [(hmeta r hr).2.2.1] at hng; rw [(hmeta r hr).2.2.2]
      exact hw_dst.arena.entails r hr hng
  exact { hw_dst with
    arena := harena1
    watches := hw_dst.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => absurd (hw_dst.level0_rsn_none idx hidx
      (by have := hw_dst.lvl_le idx hidx; change _ ≤ s.core.cur_level at this; omega)) hne
    reason_lit_mem := fun idx hidx hne => absurd (hw_dst.level0_rsn_none idx hidx
      (by have := hw_dst.lvl_le idx hidx; change _ ≤ s.core.cur_level at this; omega)) hne }

private theorem v2r_m7sc_witness_with_binWatches {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} {arL wvec' wstk' : List (BitVec 32)}
    {dst wlen' : Nat} {wu' nb' oom' : BitVec 64}
    (hw : FullWitnessInv c F0 F_cur { k with arena := arL, arena_len := dst })
    (hbin : FullReduceSpecs.BinOnlyWatchesInv F_cur
      { k with arena := arL, wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
               num_binary := nb', oom := oom' }) :
    FullWitnessInv c F0 F_cur
      { k with arena := arL, arena_len := dst, wvec := wvec', wstk := wstk', wlen := wlen',
               wusable := wu', num_binary := nb', oom := oom' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := (hbin.with_core
      (k' := { k with arena := arL, arena_len := dst, wvec := wvec', wstk := wstk',
                      wlen := wlen', wusable := wu', num_binary := nb', oom := oom' })
      rfl rfl rfl rfl).toModeWatchesInv }

private theorem v2r_m7sc_new1_prep {F_cur : List (List Nat)} {arL : List (BitVec 32)}
    {dst : BitVec 64} {cur_vars : Nat}
    (hd3_eq : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3)
    (hd3_lt : (dst + (3 : BitVec 64)).toNat < arL.length)
    (hlt0 : (arL[dst.toNat + 3 + 0]?.getD 0#32).toNat < 2 * cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((arL.drop (dst.toNat + 3)).take 1).map BitVec.toNat))) :
    let ulit := arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt
    ulit = arL[dst.toNat + 3]'(by omega) ∧ ulit.toNat < 2 * cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [ulit.toNat]) := by
  intro ulit
  have hulit_eq : ulit = arL[dst.toNat + 3]'(by omega) := by dsimp only [ulit]; simp only [hd3_eq]
  refine ⟨hulit_eq, ?_, ?_⟩
  · rw [Nat.add_zero, List.getElem?_eq_getElem (by omega : dst.toNat + 3 < arL.length),
      Option.getD_some, ← hulit_eq] at hlt0; exact hlt0
  · rw [show (1 : Nat) = 0 + 1 from rfl,
      drop_take_succ (by omega : dst.toNat + 3 + 0 < arL.length)] at hent
    simpa [hulit_eq] using hent

private theorem v2r_m7sc_new2_prep {F_cur : List (List Nat)} {arL : List (BitVec 32)}
    {dst : BitVec 64} {cur_vars : Nat} (hcv_lt : cur_vars < 2 * 2 ^ 28)
    (hd3_eq : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3)
    (hd4_eq : (dst + (4 : BitVec 64)).toNat = dst.toNat + 4)
    (hd3_lt : (dst + (3 : BitVec 64)).toNat < arL.length)
    (hd4_lt : (dst + (4 : BitVec 64)).toNat < arL.length)
    (hlt0 : (arL[dst.toNat + 3 + 0]?.getD 0#32).toNat < 2 * cur_vars)
    (hlt1 : (arL[dst.toNat + 3 + 1]?.getD 0#32).toNat < 2 * cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((arL.drop (dst.toNat + 3)).take 2).map BitVec.toNat))) :
    let l0 := arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt
    let l1 := arL[(dst + (4 : BitVec 64)).toNat]'hd4_lt
    l0.toNat < 2 * cur_vars ∧ l1.toNat < 2 * cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat, l1.toNat]) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l1.toNat, l0.toNat]) ∧
    l0.toNat < 0x7FFFFFFF ∧ l1.toNat < 0x7FFFFFFF := by
  intro l0 l1
  have hl0_eq : l0 = arL[dst.toNat + 3]'(by omega) := by dsimp only [l0]; simp only [hd3_eq]
  have hl1_eq : l1 = arL[dst.toNat + 4]'(by omega) := by dsimp only [l1]; simp only [hd4_eq]
  have hl0_lt : l0.toNat < 2 * cur_vars := by
    rw [Nat.add_zero, List.getElem?_eq_getElem (by omega : dst.toNat + 3 < arL.length),
      Option.getD_some, ← hl0_eq] at hlt0; exact hlt0
  have hl1_lt : l1.toNat < 2 * cur_vars := by
    rw [show dst.toNat + 3 + 1 = dst.toNat + 4 by omega,
      List.getElem?_eq_getElem (by omega : dst.toNat + 4 < arL.length),
      Option.getD_some, ← hl1_eq] at hlt1; exact hlt1
  have hent_01 : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat, l1.toNat]) := by
    have htk : (arL.drop (dst.toNat + 3)).take 2 = [l0, l1] := by
      apply List.ext_getElem (by simp; omega)
      intro j hj1 _; have hj : j < 2 := by simp at hj1; omega
      simp only [List.getElem_take, List.getElem_drop]
      match j, hj with
      | 0, _ => simp [hl0_eq]
      | 1, _ => simp [hl1_eq, show dst.toNat + 3 + 1 = dst.toNat + 4 by omega]
    rw [htk] at hent; simpa using hent
  have hent_10 : (cnfOfClauses F_cur).EntailsClause (cnfClause [l1.toNat, l0.toNat]) :=
    entails_of_mem_or_false hent_01 fun q hq =>
      Or.inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
                 rcases hq with rfl | rfl <;> simp)
  exact ⟨hl0_lt, hl1_lt, hent_01, hent_10, by omega, by omega⟩

private theorem v2r_m7sc_keep_inv {c : FullCfg} {s : FullState} {src dst : BitVec 64}
    {new_sz i : BitVec 32} {arL : List (BitVec 32)} {lit : BitVec 32}
    (harL : arL.length = c.arena_cap)
    (hdst_idx : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat = dst.toNat + 3 + new_sz.toNat)
    (hdst_lt : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat < arL.length)
    (hnsz1_eq : (new_sz + (1 : BitVec 32)).toNat = new_sz.toNat + 1)
    (hlit_cv : lit.toNat < 2 * s.core.cur_vars)
    (houtL : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + new_sz.toNat) s.core.arena arL)
    (hltL : ∀ j < new_sz.toNat, (arL[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hsubL : List.Sublist (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat))
    (hdropL : ∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat,
      l ∈ ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (horig_succ : ((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat =
      ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat ++ [lit.toNat]) :
    let ar' := arL.set (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat lit
    ar'.length = c.arena_cap ∧
    OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + (new_sz + (1 : BitVec 32)).toNat)
      s.core.arena ar' ∧
    (∀ j < (new_sz + (1 : BitVec 32)).toNat,
      (ar'[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    List.Sublist (((ar'.drop (dst.toNat + 3)).take (new_sz + (1 : BitVec 32)).toNat).map
      BitVec.toNat) (((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat) ∧
    (∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat,
      l ∈ ((ar'.drop (dst.toNat + 3)).take (new_sz + (1 : BitVec 32)).toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8)) := by
  intro ar'
  have hkept_succ :
      ((ar'.drop (dst.toNat + 3)).take (new_sz.toNat + 1)).map BitVec.toNat =
      ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ++ [lit.toNat] := by
    dsimp only [ar']
    rw [hdst_idx,
      drop_take_set_append (by omega : dst.toNat + 3 + new_sz.toNat < arL.length),
      List.map_append, List.map_singleton]
  refine ⟨by simp [ar', harL], ?_, ?_, ?_, ?_⟩
  · intro idx hidx; rw [hnsz1_eq] at hidx; dsimp only [ar']
    rw [List.getElem?_set_ne (by omega)]; exact houtL idx (by omega)
  · intro j hj; rw [hnsz1_eq] at hj; dsimp only [ar']
    by_cases hje : j = new_sz.toNat
    · subst hje; rw [← hdst_idx, List.getElem?_set_self hdst_lt, Option.getD_some]; exact hlit_cv
    · rw [List.getElem?_set_ne (by omega)]; exact hltL j (by omega)
  · rw [hnsz1_eq, hkept_succ, horig_succ]; exact hsubL.append (List.Sublist.refl _)
  · intro l hl; rw [horig_succ, List.mem_append, List.mem_singleton] at hl
    rw [hnsz1_eq, hkept_succ, List.mem_append, List.mem_singleton]
    rcases hl with hl | rfl
    · rcases hdropL l hl with hin | hd
      · exact Or.inl (Or.inl hin)
      · exact Or.inr hd
    · exact Or.inl (Or.inr rfl)

private def V2rM7ScNoZredPrefix (s : FullState) (src : BitVec 64) (n : Nat) : Prop :=
  (s.core.arena[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 →
  ∀ j < n,
    let v := (s.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat / 2
    v < s.core.cur_vars → (s.core.flags[v]?.getD 0#32 &&& 1#32) ≠ 0#32

private def V2rM7ScLoopInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (src dst : BitVec 64) (old_sz : BitVec 32) (p : Tup Val [i32, i32]) (mL : Mem 64) : Prop :=
  let (new_sz, i, ()) := p
  new_sz.toNat ≤ i.toNat ∧ i.toNat ≤ old_sz.toNat ∧
  ∃ arL : List (BitVec 32), arL.length = c.arena_cap ∧
    OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + new_sz.toNat) s.core.arena arL ∧
    (∀ j < new_sz.toNat, (arL[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    List.Sublist (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat) ∧
    (∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat,
      l ∈ ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8)) ∧
    V2rM7ScNoZredPrefix s src i.toNat ∧
    (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL

private def V2rM7ScJoinInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (src dst : BitVec 64) (i : BitVec 32) (p : Tup Val [i32]) (m' : Mem 64) : Prop :=
  let (new_sz', ()) := p
  new_sz'.toNat ≤ i.toNat + 1 ∧
  ∃ ar' : List (BitVec 32), ar'.length = c.arena_cap ∧
    OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + new_sz'.toNat) s.core.arena ar' ∧
    (∀ j < new_sz'.toNat, (ar'[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    List.Sublist (((ar'.drop (dst.toNat + 3)).take new_sz'.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat) ∧
    (∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat,
      l ∈ ((ar'.drop (dst.toNat + 3)).take new_sz'.toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8)) ∧
    V2rM7ScNoZredPrefix s src (i.toNat + 1) ∧
    (FullMem c { s with core := { s.core with arena := ar' } } ⋆ R) m'

private def V2rM7ScOomInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (arL : List (BitVec 32)) (_ : Tup Val []) (mOom : Mem 64) : Prop :=
  ∃ wvecO wstkO wlenO wuO wsO,
    let sO : FullState :=
      { core := { s.core with arena := arL, wvec := wvecO, wstk := wstkO, wlen := wlenO,
                              wusable := wuO }
        scratch := { s.scratch with wsort := wsO } }
    sO.LengthsOk c ∧ FullReduceSpecs.BinOnlyWatchesInv F_cur sO.core ∧ (FullMem c sO ⋆ R) mOom

private theorem v2r_m7sc_ret_sat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {src dst : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {arL : List (BitVec 32)} {mL : Mem 64}
    (hlen : s.LengthsOk c) (hdst_le : dst.toNat ≤ c.arena_cap) (_hsz_lt : old_sz.toNat < 2 * 2 ^ 28)
    (har_t : at_root = true) (hcl0 : s.core.cur_level = 0)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat })
    (hbin0 : FullReduceSpecs.BinOnlyWatchesInv F_cur s.core)
    (hQ : FullReduceSpecs.fullSweepCopyPost c F0 F_cur s R src dst old_sz at_root Q)
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL)
    (hmL : (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL) :
    Q (0xFFFFFFFF#64, ()) mL :=
  hQ 0xFFFFFFFF#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
    s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk s.core.wlen
    s.core.wusable s.core.num_binary s.core.oom s.scratch.phases s.scratch.wsort mL
    ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩ hout
    ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
     fun _ => ⟨v2r_m7sc_witness_with_ar (s := s) hlen.core_ok.arena_len_arr hdst_le hcl0 hw_dst
         harL (fun idx (hidx : idx < dst.toNat) => hout.getElem?_lt (by omega)),
       hbin0.with_core rfl rfl rfl rfl, Nat.le_refl _, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
       (fun h => by cases h), (fun h => by cases h), (fun _ => rfl), (fun h => by cases h),
       (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩⟩ hmL

private theorem v2r_m7sc_ret_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {src dst : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {arL : List (BitVec 32)} {mL : Mem 64}
    (hlen : s.LengthsOk c) (hdst_le : dst.toNat ≤ c.arena_cap) (_hsz_lt : old_sz.toNat < 2 * 2 ^ 28)
    (har_t : at_root = true) (hcl0 : s.core.cur_level = 0)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat })
    (hbin0 : FullReduceSpecs.BinOnlyWatchesInv F_cur s.core)
    (hQ : FullReduceSpecs.fullSweepCopyPost c F0 F_cur s R src dst old_sz at_root Q)
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL)
    (hunsat : F0.Unsat)
    (hmL : (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL) :
    Q (0xFFFFFFFE#64, ()) mL :=
  hQ 0xFFFFFFFE#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
    s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk s.core.wlen
    s.core.wusable s.core.num_binary s.core.oom s.scratch.phases s.scratch.wsort mL
    ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩ hout
    ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
     fun _ => ⟨v2r_m7sc_witness_with_ar (s := s) hlen.core_ok.arena_len_arr hdst_le hcl0 hw_dst
         harL (fun idx (hidx : idx < dst.toNat) => hout.getElem?_lt (by omega)),
       hbin0.with_core rfl rfl rfl rfl, Nat.le_refl _, Or.inl rfl, (fun _ => hunsat),
       (fun h => by cases h), (fun _ => rfl), (fun h => by cases h),
       (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩⟩ hmL

/-- `FullM7V2Robust.full_sweep_copy` satisfies canonical `Full.fullSweepCopySpec`, including
atomic `bin` watch-push OOM rollback via `full_watch_pop_c0` and `PH_RED` zombie drop. -/
theorem full_sweep_copy_wp (Γ : Env)
    (hassign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hpush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hpop : ∀ a m Q X, fullWatchPopC0Spec a m Q X →
      Γ "full_watch_pop_c0" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullSweepCopySpec a m Q X → Func.wp Γ full_sweep_copy_body a m Q X := by
  rintro ⟨h, src, dst, old_sz, at_root, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hdst_src, hsz3, hsrc_fit, hat_eq, hlits_lt, hroot_pre, hm, hQ⟩
  have hcap_lt : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hal_le := hlen.core_ok.arena_len_le
  have har_len := hlen.core_ok.arena_len_arr
  have hcv_le := hlen.core_ok.cur_vars_le
  have hv_len := hlen.core_ok.vals_len
  have hfl_len := hlen.core_ok.flags_len
  have hl_len := hlen.core_ok.lvl_len
  have hfit_cap : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap := by omega
  have hdst_fit : dst.toNat + 3 + old_sz.toNat ≤ c.arena_cap := by omega
  have hsrc_lt0 : src.toNat < s.core.arena.length := by omega
  let Qsp : FullReduceSpecs.fullSweepCopyPost c F0 F_cur s R src dst old_sz at_root Q :=
    fun r arena' vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb'
      oom' ph' wsort' m' hl' ho' ⟨hf_out, ht_out⟩ hm' =>
      hQ r arena' vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb'
        oom' ph' wsort' m' hl' ho' hf_out
        (fun ht => let ⟨hw', hbo', rest⟩ := ht_out ht; ⟨hw', v2r_m7scRedBinOnly_to_full hbo', rest⟩)
        hm'
  unfold Func.wp full_sweep_copy_body
  c0_hsteps_nogrp
  c0_hsplit
  · have har_t : at_root = true := by simpa using hc
    have hcl0 : s.core.cur_level = 0 := of_decide_eq_true (hat_eq.symm.trans har_t)
    obtain ⟨hw_dst, hfb0, hent0⟩ := hroot_pre har_t
    have hbin0 : FullReduceSpecs.BinOnlyWatchesInv F_cur s.core :=
      v2r_m7scFullBinOnly_to_red hlen.core_ok hfb0
    clear hfb0 hroot_pre hat_eq
    have hQsat : ∀ {arL mL}, arL.length = c.arena_cap →
        OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL →
        (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL →
        Q (0xFFFFFFFF#64, ()) mL := fun harL hout hmL =>
      v2r_m7sc_ret_sat hlen (by omega) (by omega) har_t hcl0 hw_dst hbin0 Qsp harL hout hmL
    c0_hsteps_nogrp
    refine wp_loop_inv (V2rM7ScLoopInv c s R src dst old_sz)
      (fun (_, i, ()) _ => old_sz.toNat - i.toNat) (fun J hLoop => ?_) ?_
    · c0_hsteps
      exact hLoop (0#32, 0#32, ()) m ⟨Nat.le_refl _, Nat.zero_le _, s.core.arena, har_len,
        fun _ _ => rfl, fun _ hj => by simp at hj, by simp, fun _ hl => by simp at hl,
        (fun _ _ hj => by cases hj), hm⟩
    · rintro J ⟨new_sz, i, ⟨⟩⟩ mL ⟨hni, hi_le, arL, harL, houtL, hltL, hsubL, hdropL, hnzL, hmL⟩
        hLoop
      c0_hsplit
      · have hi_lt : i.toNat < old_sz.toNat := by c0_bound
        have hi1_eq : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := bv32_add1 (by omega)
        have hnsz1_eq : (new_sz + (1 : BitVec 32)).toNat = new_sz.toNat + 1 :=
          bv32_add1 (by omega)
        have hsrc_idx : (src + (3 : BitVec 64) + i.setWidth 64).toNat = src.toNat + 3 + i.toNat :=
          bv64_add3_zext_toNat (by omega)
        have hdst_idx : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat =
            dst.toNat + 3 + new_sz.toNat := bv64_add3_zext_toNat (by omega)
        have hsrc_lt : (src + (3 : BitVec 64) + i.setWidth 64).toNat < arL.length := by omega
        have hdst_lt : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat < arL.length := by omega
        let lit := arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt
        have hlit_eq : lit = arL[src.toNat + 3 + i.toNat]'(by omega) := by
          dsimp only [lit]; simp only [hsrc_idx]
        have hlit_orig : lit = s.core.arena[src.toNat + 3 + i.toNat]'(by omega) := by
          have h1 := houtL.getElem?_ge (i := src.toNat + 3 + i.toNat) (by omega)
          rw [List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < arL.length),
            List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < s.core.arena.length)]
            at h1
          rw [hlit_eq]; exact Option.some.inj h1
        have hlit_cv : lit.toNat < 2 * s.core.cur_vars := by
          have := hlits_lt i.toNat hi_lt
          rw [List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < s.core.arena.length),
            Option.getD_some, ← hlit_orig] at this; exact this
        have horig_succ : ((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat
            = ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat ++
                [lit.toNat] := by
          rw [drop_take_succ (by omega : src.toNat + 3 + i.toNat < s.core.arena.length),
            List.map_append, List.map_singleton, hlit_orig]
        have hlit_vlen : (arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt).toNat <
            s.core.vals.length := by change lit.toNat < _; omega
        have hidx_mod : (src.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64 =
            src.toNat + 3 + i.toNat := by
          rw [show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
        have ha_lit : arL[(src.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64]'(by
            rw [hidx_mod]; omega) = lit := by rw [hlit_eq]; simp only [hidx_mod]
        have hnz_step :
            ¬ (lit.toNat / 2 < s.core.cur_vars ∧
                (s.core.arena[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
                (s.core.flags[lit.toNat / 2]?.getD 0#32 &&& 1#32) = 0#32) →
            V2rM7ScNoZredPrefix s src (i.toNat + 1) := by
          intro hnot hred j hj v hv_lt hfl0
          by_cases hji : j = i.toNat
          · rcases hji with rfl
            have har_j : s.core.arena[src.toNat + 3 + i.toNat]?.getD 0#32 = lit := by
              rw [List.getElem?_eq_getElem
                    (by omega : src.toNat + 3 + i.toNat < s.core.arena.length),
                Option.getD_some, ← hlit_orig]
            dsimp only [v] at hv_lt hfl0
            rw [har_j] at hv_lt hfl0
            exact hnot ⟨hv_lt, hred, hfl0⟩
          · exact hnzL hred j (by omega) hv_lt hfl0
        c0_hsteps_nogrp
        refine wp_join_group (fun (_ : Tup Val []) m' =>
            V2rM7ScNoZredPrefix s src (i.toNat + 1) ∧ m' = mL)
          (by
            rintro _ ⟨⟩ m' ⟨hnz_i1, hm'⟩
            subst m'
            c0_hsteps_nogrp
            refine wp_join_group (V2rM7ScJoinInv c s R src dst i) ?_ ?_
            · rintro _ ⟨new_sz', ⟨⟩⟩ m' ⟨hni', ar', har', hout', hlt', hsub', hdrop', hnz', hm'⟩
              c0_hsteps
              exact hLoop (new_sz', i + (1 : BitVec 32), ()) m' (by dsimp only; rw [hi1_eq]; omega)
                ⟨by rw [hi1_eq]; exact hni', by rw [hi1_eq]; omega, ar', har', hout', hlt',
                 by rw [hi1_eq]; exact hsub', by rw [hi1_eq]; exact hdrop',
                 by rw [hi1_eq]; exact hnz', hm'⟩
            · intro Ji hJi
              clear hLoop J hassign hpush hpop hent0 hlits_lt
              c0_hsteps_nogrp
              refine wp_join_group (fun (_ : Tup Val []) m'' => m'' = mL) ?_ ?_
              · rintro _ ⟨⟩ m'' hm''
                have hm''_mem :
                    (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) m'' :=
                  hm''.symm ▸ hmL
                clear hm''
                c0_hsteps
                obtain ⟨har', hout', hlt', hsub', hdrop'⟩ := v2r_m7sc_keep_inv harL
                  hdst_idx hdst_lt hnsz1_eq hlit_cv houtL hltL hsubL hdropL horig_succ
                exact hJi (new_sz + (1 : BitVec 32), ()) _
                  ⟨by rw [hnsz1_eq]; omega, _, har', hout', hlt', hsub', hdrop', hnz_i1,
                   by assumption⟩
              · intro Je hJe
                c0_hsplit
                · c0_hsplit
                  · have hlvl_z : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = 0 := by
                      have h1 : s.core.lvl[lit.toNat / 2]'(by omega) = (0 : BitVec 32) := by
                        simpa only [ha_lit] using hc
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, h1]; rfl
                    c0_hsplit
                    · have hval_ne : s.core.vals[lit.toNat]'(by omega) ≠ 0#8 := fun h0 => by
                        have h1 : (s.core.vals[lit.toNat]'(by omega)).signExtend 32 ≠ 0#32 := by
                          simpa only [ha_lit] using hc
                        rw [h0] at h1; exact h1 rfl
                      c0_hsplit
                      · c0_hsteps
                        exact hQsat harL (fun idx hidx => houtL idx (by omega)) hmL
                      · have hval_ff : s.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
                          have hdom := hw_dst.vals_domain lit.toNat hlit_cv
                          have hv_get : s.core.vals[lit.toNat]?.getD 0#8 =
                              s.core.vals[lit.toNat]'(by omega) := by
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                          have hng : (0#32).slt
                              ((s.core.vals[lit.toNat]'(by omega)).signExtend 32) = false := by
                            simpa only [ha_lit] using hc
                          rw [hv_get] at hdom ⊢
                          rcases hdom with h0 | h1 | hff
                          · exact absurd h0 hval_ne
                          · exact absurd ((bv8_gt0_of_dom (Or.inr (Or.inl h1))).1.mpr h1)
                              (by simp [hng])
                          · exact hff
                        c0_hsteps
                        refine hJi (new_sz, ()) mL
                          ⟨by omega, arL, harL, houtL, hltL, ?_, ?_, hnz_i1, hmL⟩
                        · rw [horig_succ]; exact hsubL.trans (List.sublist_append_left _ _)
                        · intro l hl; rw [horig_succ, List.mem_append, List.mem_singleton] at hl
                          rcases hl with hl | rfl
                          · exact hdropL l hl
                          · exact Or.inr ⟨hlit_cv, hlvl_z, hval_ff⟩
                    · c0_hsteps; exact hJe () mL rfl
                  · c0_hsteps; exact hJe () mL rfl
                · c0_hsteps; exact hJe () mL rfl)
          (fun Jz hJz => ?_)
        · have hlit_v2_lt :
              (arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt).toNat / 2 <
              s.core.cur_vars := by
            change lit.toNat / 2 < _; omega
          c0_hsplit
          · c0_hsplit
            · have hv_fl_lt :
                  (((arL[(src + (3 : BitVec 64) +
                    i.setWidth 64).toNat]'hsrc_lt) >>> 1#32).setWidth 64).toNat <
                    s.core.flags.length := by
                rw [zext_toNat _ (by decide), bv32_shr1_toNat]; change lit.toNat / 2 < _; omega
              c0_hsplit
              · c0_hsteps
                exact hQsat harL (fun idx hidx => houtL idx (by omega)) hmL
              · c0_hsteps
                refine hJz () mL ⟨hnz_step fun ⟨_, _, hfl0⟩ => ?_, rfl⟩
                have hfl_ne : s.core.flags[lit.toNat / 2]'(by omega) &&& 1#32 ≠ 0#32 :=
                  fun h0 => hc (by simp only [ha_lit]; exact h0)
                rw [List.getElem?_eq_getElem (by omega : lit.toNat / 2 < s.core.flags.length),
                  Option.getD_some] at hfl0
                exact hfl_ne hfl0
            · c0_hsteps
              refine hJz () mL ⟨hnz_step fun ⟨_, hred, _⟩ => ?_, rfl⟩
              rw [List.getElem?_eq_getElem hsrc_lt0, Option.getD_some] at hred
              exact absurd hc hred
          · c0_hsteps
            have hcv_le_v : s.core.cur_vars ≤ lit.toNat / 2 := by
              rw [show lit.toNat / 2 =
                  (((arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt) >>>
                    1#32).setWidth 64).toNat by
                rw [zext_toNat _ (by decide), bv32_shr1_toNat]]
              c0_bound
            exact hJz () mL ⟨hnz_step fun ⟨hv_lt, _, _⟩ => absurd hv_lt (by omega), rfl⟩
      · have hi_eq : i.toNat = old_sz.toNat := by c0_bound
        have hnz_fin : V2rM7ScNoZredPrefix s src old_sz.toNat := hi_eq ▸ hnzL
        have hpre : PrefixAgrees dst.toNat s.core.arena arL :=
          fun idx hidx => houtL.getElem?_lt (by omega)
        have hwL : FullWitnessInv c F0 F_cur { s.core with arena := arL, arena_len := dst.toNat } :=
          v2r_m7sc_witness_with_ar har_len (by omega) hcl0 hw_dst harL hpre
        have hsub_fin : List.Sublist
            (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)
            (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat) :=
          hi_eq ▸ hsubL
        have hent_kept : (cnfOfClauses F_cur).EntailsClause
            (cnfClause (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)) :=
          level0_entails_of_filter hw_dst hent0 (hi_eq ▸ hdropL)
        have hout_fin : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat)
            s.core.arena arL := fun idx hidx => houtL idx (by omega)
        have hlenL : ({ s with core := { s.core with arena := arL } } : FullState).LengthsOk c :=
          ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩
        have hbinL : FullReduceSpecs.BinOnlyWatchesInv F_cur { s.core with arena := arL } :=
          hbin0.with_core rfl rfl rfl rfl
        c0_hsplit
        · have hnsz0 : new_sz.toNat = 0 := by c0_bound
          rw [hnsz0] at hent_kept; simp only [List.take_zero, List.map_nil] at hent_kept
          c0_hsteps
          exact v2r_m7sc_ret_unsat hlen (by omega) (by omega) har_t hcl0 hw_dst hbin0 Qsp harL
            hout_fin (level0_unsat_of_entails_nil hwL hent_kept) hmL
        · c0_hsplit
          · have hnsz1 : new_sz.toNat = 1 := by c0_bound
            have hd3_eq : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3 := bv64_add3 (by omega)
            have hd3_lt : (dst + (3 : BitVec 64)).toNat < arL.length := by omega
            let ulit := arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt
            obtain ⟨hulit_eq, hulit_lt, hent_u⟩ :=
              v2r_m7sc_new1_prep hd3_eq hd3_lt (hltL 0 (by omega)) (hnsz1 ▸ hent_kept)
            have hulit_lt' : ulit.toNat < 2 * s.core.cur_vars := hulit_lt
            have hulit_vlen : (arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt).toNat <
                s.core.vals.length := by omega
            clear hLoop J hsub_fin hent_kept hent0 hlits_lt hpush hpop hltL hsubL hdropL houtL hpre
              hnzL hnz_fin
            c0_hsplit
            · have hff : s.core.vals[ulit.toNat]?.getD 0#8 = 0xFF#8 := by
                have hdom := hwL.vals_domain ulit.toNat hulit_lt'
                have hget :
                    s.core.vals[ulit.toNat]?.getD 0#8 = s.core.vals[ulit.toNat]'(by omega) := by
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                rw [hget] at hdom ⊢
                exact (bv8_gt0_of_dom hdom).2.mp hc
              c0_hsteps
              exact v2r_m7sc_ret_unsat hlen (by omega) (by omega) har_t hcl0 hw_dst hbin0 Qsp harL
                hout_fin
                (level0_unsat_of_unit_false hwL hcl0 hulit_lt' hent_u hff) hmL
            · c0_hsplit
              · have hun : s.core.vals[ulit.toNat]?.getD 0#8 = 0#8 := by
                  have hdm : (dst.toNat + (3 : BitVec 64).toNat) % 2 ^ 64 = dst.toNat + 3 := by
                    rw [show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
                  have hua : arL[(dst.toNat + (3 : BitVec 64).toNat) % 2 ^ 64]'(by
                      rw [hdm]; omega) = ulit := by
                    dsimp only [ulit]; rw [hulit_eq]; simp only [hdm]
                  have hsext0 : (s.core.vals[ulit.toNat]'(by omega)).signExtend 32 = 0#32 := by
                    simpa only [hua] using hc
                  have hdom := hwL.vals_domain ulit.toNat hulit_lt'
                  have hg : s.core.vals[ulit.toNat]?.getD 0#8 =
                      s.core.vals[ulit.toNat]'(by omega) := by
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  rw [hg] at hdom ⊢
                  exact (bv8_sext32_eq0_of_dom hdom).mp hsext0
                have hte_lt : s.core.trail_end < s.core.cur_vars :=
                  hwL.trail_end_lt_of_unassigned hulit_lt' hun
                have hnot_skip : ¬ (s.core.cur_vars ≤ ulit.toNat / 2 ∨
                    c.max_vars ≤ s.core.trail_end ∨ s.core.vals[ulit.toNat]?.getD 0#8 ≠ 0#8) := by
                  simp only [hun, ne_eq, not_true_eq_false, or_false]; omega
                c0_hsteps; c0_call hassign
                refine ⟨c, { s with core := { s.core with arena := arL } }, R, rfl, hlenL, hmL, ?_⟩
                split
                · rename_i hskip; exact absurd hskip hnot_skip
                · dsimp only
                  intro flags' unass' phases' m' hfl' hph' hm'
                  have hw' := level0Assign_preserves_witness
                    (k := { s.core with arena := arL, arena_len := dst.toNat })
                    { hlenL.core_ok with arena_len_le := by change dst.toNat ≤ c.arena_cap; omega }
                    hwL hcl0 hulit_lt' hun hent_u flags' unass' (s.core.unflushed + 1#64)
                  c0_hsteps
                  exact Qsp 1#64 arL
                    ((s.core.vals.set ulit.toNat 1#8).set (ulit.toNat ^^^ 1) 0xFF#8)
                    flags' (s.core.lvl.set (ulit.toNat / 2) 0#32)
                    (s.core.rsns.set (ulit.toNat / 2) 0xFFFFFFFF#32)
                    (s.core.trl.set s.core.trail_end ulit)
                    (s.core.trail_pos.set (ulit.toNat / 2) (BitVec.ofNat 32 s.core.trail_end))
                    (s.core.trail_end + 1) unass' (s.core.unflushed + 1#64) s.core.wvec s.core.wstk
                    s.core.wlen s.core.wusable s.core.num_binary s.core.oom phases' s.scratch.wsort
                    m'
                    ⟨{ hlenL.core_ok with
                       vals_len := by simp [hlenL.core_ok.vals_len], flags_len := hfl'
                       lvl_len := by simp [hlenL.core_ok.lvl_len]
                       rsns_len := by simp [hlenL.core_ok.rsns_len]
                       trl_len := by simp [hlenL.core_ok.trl_len]
                       trail_pos_len := by simp [hlenL.core_ok.trail_pos_len]
                       trail_end_le := hte_lt
                       propagated_le := Nat.le_succ_of_le hlenL.core_ok.propagated_le },
                     { hlenL.scratch_ok with phases_len := hph' }⟩
                    hout_fin ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
                     fun _ => ⟨hw', hbinL.with_core rfl rfl rfl rfl, by dsimp only; omega,
                       Or.inr (Or.inr (Or.inl rfl)), (fun h => by cases h), (fun h => by cases h),
                       (fun _ => rfl), (fun _ => by dsimp only; omega),
                       (fun ⟨h3, _⟩ => by exfalso; revert h3; decide)⟩⟩ hm'
              · c0_hsteps; exact hQsat harL hout_fin hmL
          · c0_hsplit
            · have hnsz2 : new_sz.toNat = 2 := by c0_bound
              have hd3_eq : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3 := bv64_add3 (by omega)
              have hd4_eq : (dst + (4 : BitVec 64)).toNat = dst.toNat + 4 := bv64_add4 (by omega)
              have hd3_lt : (dst + (3 : BitVec 64)).toNat < arL.length := by omega
              have hd4_lt : (dst + (4 : BitVec 64)).toNat < arL.length := by omega
              let l0 := arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt
              let l1 := arL[(dst + (4 : BitVec 64)).toNat]'hd4_lt
              obtain ⟨hl0_lt, hl1_lt, hent_01, hent_10, hl0_b, hl1_b⟩ :=
                v2r_m7sc_new2_prep (by omega) hd3_eq hd4_eq hd3_lt hd4_lt
                  (hltL 0 (by omega)) (hltL 1 (by omega)) (hnsz2 ▸ hent_kept)
              have hb0 := bv32_bin_word_props hl1_b
              have hb1 := bv32_bin_word_props hl0_b
              have hsz_lt_cap : old_sz.toNat < 2 * 2 ^ 28 := by omega
              clear hLoop J hsub_fin hent_kept hw_dst hent0 hlits_lt
                hassign hltL hsubL hdropL houtL hpre hbin0 hnzL hnz_fin
                hcap_lt hmax_lt hal_le har_len hcv_le hv_len hfl_len hl_len hfit_cap hdst_fit
                hcl0 hlen hdst_src hsz3 hsrc_fit hnsz2 hl0_b hl1_b
              have hRetOom : ∀ wvecO wstkO wlenO wuO wsO mO,
                  let sO : FullState :=
                    { core := { s.core with arena := arL, wvec := wvecO, wstk := wstkO,
                                            wlen := wlenO, wusable := wuO, oom := 1#64 }
                      scratch := { s.scratch with wsort := wsO } }
                  sO.LengthsOk c → FullReduceSpecs.BinOnlyWatchesInv F_cur sO.core →
                  (FullMem c sO ⋆ R) mO → Q (0xFFFFFFFD#64, ()) mO :=
                fun wvecO wstkO wlenO wuO wsO mO hlenO hbinO hmO =>
                let hwO := v2r_m7sc_witness_with_binWatches hwL hbinO
                Qsp 0xFFFFFFFD#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns
                  s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
                  wvecO wstkO wlenO wuO s.core.num_binary 1#64 s.scratch.phases wsO mO
                  ⟨{ hlenO.core_ok with }, hlenO.scratch_ok⟩ hout_fin
                  ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
                   fun _ => ⟨hwO, hbinO, Nat.le_refl _, Or.inr (Or.inl rfl),
                     (fun h => by cases h), (fun _ => rfl), (fun h => absurd rfl h),
                     (fun h => by cases h),
                     (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩⟩ hmO
              let s_arL : FullState := { s with core := { s.core with arena := arL } }
              c0_hsteps; c0_call hpush
              refine ⟨c, s_arL, R, rfl, hlenL,
                hbinL.layout, fun _ => hb0.2.1, fun h => by exfalso; revert h; decide, hmL,
                fun ok1 wvec1 wstk1 wlen1 wu1 ws1 m1 hlen1 hlay1 hoth1 hok1t hok1f hm1 => ?_⟩
              have hbin1 : FullReduceSpecs.BinOnlyWatchesInv F_cur
                  { s.core with arena := arL, wvec := wvec1, wstk := wstk1, wlen := wlen1,
                                wusable := wu1 } :=
                fullWatchPush_preserves_binOnly hbinL hlay1 rfl
                  ⟨hb0.1, hb0.2.1, by rw [hb0.2.2]; exact hl1_lt, by rw [hb0.2.2]; exact hent_01⟩
                  hoth1
                  (fun h => by obtain ⟨a, _, b, c, d, _⟩ := hok1t h; exact ⟨a, b, c, d⟩)
                  (hok1f · |>.1)
              let k1 : FullCoreState :=
                { s.core with arena := arL, wvec := wvec1, wstk := wstk1,
                              wlen := wlen1, wusable := wu1 }
              let s1 : FullState :=
                { s_arL with core := k1, scratch := { s.scratch with wsort := ws1 } }
              c0_hsplit
              · c0_hsteps; c0_call hpush
                refine ⟨c, s1, R, rfl, hlen1,
                  hlay1, fun _ => hb1.2.1, fun h => by exfalso; revert h; decide, hm1,
                  fun ok2 wvec2 wstk2 wlen2 wu2 ws2 m2 hlen2 hlay2 hoth2 hok2t hok2f hm2 => ?_⟩
                have hbin2 : FullReduceSpecs.BinOnlyWatchesInv F_cur
                    { s.core with arena := arL, wvec := wvec2, wstk := wstk2, wlen := wlen2,
                                  wusable := wu2 } :=
                  fullWatchPush_preserves_binOnly hbin1 hlay2 rfl
                    ⟨hb1.1, hb1.2.1, by rw [hb1.2.2]; exact hl0_lt,
                      by rw [hb1.2.2]; exact hent_10⟩
                    hoth2
                    (fun h => by obtain ⟨a, _, b, c, d, _⟩ := hok2t h; exact ⟨a, b, c, d⟩)
                    (hok2f · |>.1)
                c0_hsplit
                · have hbin2' : FullReduceSpecs.BinOnlyWatchesInv F_cur
                      { s.core with arena := arL, wvec := wvec2, wstk := wstk2, wlen := wlen2,
                                    wusable := wu2, num_binary := s.core.num_binary + 1#64 } :=
                    hbin2.with_core rfl rfl rfl rfl
                  have hw2 := v2r_m7sc_witness_with_binWatches hwL hbin2'
                  c0_hsteps
                  exact Qsp 0xFFFFFFFF#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns
                    s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned
                    s.core.unflushed wvec2 wstk2 wlen2 wu2 (s.core.num_binary + 1#64) s.core.oom
                    s.scratch.phases ws2 _ ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩ hout_fin
                    ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
                     fun _ => ⟨hw2, hbin2', Nat.le_refl _,
                       Or.inr (Or.inr (Or.inr (Or.inl rfl))),
                       (fun h => by cases h), (fun h => by cases h), (fun _ => rfl),
                       (fun h => by cases h),
                       (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩⟩
                    (fullMem_cast (by assumption) rfl)
                · -- `push2` failed: call `full_watch_pop_c0(h, l0, 1u);` before `h->oom = 1ULL`!
                  obtain ⟨_, _, hsz1, hpre1, _, _⟩ := hok1t (by assumption)
                  let k2 : FullCoreState :=
                    { s.core with arena := arL, wvec := wvec2, wstk := wstk2,
                                  wlen := wlen2, wusable := wu2 }
                  let s2 : FullState :=
                    { s_arL with core := k2, scratch := { s.scratch with wsort := ws2 } }
                  have hsz1_s : fullWatchSize s1 l0.toNat = fullWatchSize s_arL l0.toNat + 1 := by
                    dsimp only [s1, k1, s_arL]; exact hsz1
                  have hpre1_s : ∀ j < fullWatchSize s_arL l0.toNat,
                      wstk1[fullWatchOff s1 l0.toNat + j]? =
                        s.core.wstk[fullWatchOff s_arL l0.toNat + j]? := by
                    dsimp only [s1, k1, s_arL]; exact hpre1
                  have hsz2_l0 :
                      fullWatchSize s2 l0.toNat = fullWatchSize s_arL l0.toNat + 1 ∧
                      ∀ j < fullWatchSize s_arL l0.toNat,
                        wstk2[fullWatchOff s2 l0.toNat + j]? =
                        s.core.wstk[fullWatchOff s_arL l0.toNat + j]? := by
                    by_cases heql : l0.toNat = l1.toNat
                    · have hs2' := (hok2f hc).1 (by dsimp only [s1, k1, s_arL]; exact hl1_lt)
                      change fullWatchSizeCore k2 l1.toNat = fullWatchSizeCore k1 l1.toNat ∧
                        ∀ j < fullWatchSizeCore k1 l1.toNat,
                          wstk2[fullWatchOffCore k2 l1.toNat + j]? =
                            wstk1[fullWatchOffCore k1 l1.toNat + j]? at hs2'
                      rw [← heql] at hs2'
                      exact ⟨hs2'.1.trans hsz1_s, fun j hj =>
                        (hs2'.2 j (by
                          change j < fullWatchSize s1 l0.toNat
                          rw [hsz1_s]; exact Nat.lt_succ_of_lt hj)).trans (hpre1_s j hj)⟩
                    · obtain ⟨hs2, hk2⟩ := hoth2 l0.toNat
                        (by dsimp only [s1, k1, s_arL]; exact hl0_lt) heql
                      exact ⟨hs2.trans hsz1_s, fun j hj =>
                        (hk2 j (by
                          change j < fullWatchSize s1 l0.toNat
                          rw [hsz1_s]; exact Nat.lt_succ_of_lt hj)).trans (hpre1_s j hj)⟩
                  c0_hsteps; c0_call hpop
                  refine ⟨c, s2, R, rfl, hlen2,
                    hlay2, hl0_lt, by decide,
                    by change (1 : Nat) ≤ fullWatchSize s2 l0.toNat; rw [hsz2_l0.1]; omega,
                    hm2, ?_⟩
                  intro wvec3 wstk3 wu3 m3 s3 hlen3 hlay3 hoth3 hoff3 hsz3 hslice3 hm3
                  have hbin3 : FullReduceSpecs.BinOnlyWatchesInv F_cur
                      { s.core with arena := arL, wvec := wvec3, wstk := wstk3,
                                    wlen := wlen2, wusable := wu3 } :=
                    binOnlyWatchesInv_of_pop hbinL hbin2 hlay3 rfl rfl hl0_lt
                      ⟨by change fullWatchSize s3 l0.toNat = fullWatchSize s_arL l0.toNat
                          rw [show fullWatchSize s3 l0.toNat =
                              fullWatchSize s2 l0.toNat - (1#32).toNat from hsz3,
                            hsz2_l0.1, show (1#32 : BitVec 32).toNat = 1 from rfl,
                            Nat.add_sub_cancel],
                       fun j hj => by
                         have hj' : j < fullWatchSize s_arL l0.toNat := hj
                         have hk : j < fullWatchSize s2 l0.toNat - (1#32).toNat := by
                           rw [hsz2_l0.1, show (1#32 : BitVec 32).toNat = 1 from rfl,
                             Nat.add_sub_cancel]
                           exact hj'
                         exact (hslice3 j hk).trans (hsz2_l0.2 j hj')⟩
                      (by
                        intro l hl hne
                        obtain ⟨_, hs3, hk3⟩ := hoth3 l (by dsimp only [s2, k2]; exact hl) hne
                        exact ⟨hs3, hk3⟩)
                  c0_hsteps
                  exact hRetOom wvec3 wstk3 wlen2 wu3 ws2 _
                    ⟨{ hlen3.core_ok with vals_len := hlen3.core_ok.vals_len }, hlen3.scratch_ok⟩
                    (hbin3.with_core rfl rfl rfl rfl) (fullMem_cast (by assumption) rfl)
              · c0_hsteps
                exact hRetOom wvec1 wstk1 wlen1 wu1 ws1 _
                  ⟨{ hlen1.core_ok with vals_len := hlen1.core_ok.vals_len }, hlen1.scratch_ok⟩
                  (hbin1.with_core rfl rfl rfl rfl) (fullMem_cast (by assumption) rfl)
            · have hge3 : 3 ≤ new_sz.toNat := by
                have h0 : new_sz.toNat ≠ 0 := by c0_bound
                have h1 : new_sz.toNat ≠ 1 := by c0_bound
                have h2 : new_sz.toNat ≠ 2 := by c0_bound
                omega
              have hnsz64 : (new_sz.setWidth 64).toNat = new_sz.toNat := zext_toNat _ (by decide)
              c0_hsteps
              exact Qsp (new_sz.setWidth 64) arL s.core.vals s.core.flags s.core.lvl s.core.rsns
                s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
                s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.core.num_binary s.core.oom
                s.scratch.phases s.scratch.wsort mL hlenL hout_fin
                ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
                 fun _ => ⟨hwL, hbinL, Nat.le_refl _,
                   Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))),
                   fun h => by have := congrArg BitVec.toNat h; rw [hnsz64] at this; simp at this
                               omega,
                   fun h => by have := congrArg BitVec.toNat h; rw [hnsz64] at this; simp at this
                               omega,
                   fun _ => rfl,
                   fun h => by have := congrArg BitVec.toNat h; rw [hnsz64] at this; simp at this
                               omega,
                   fun _ => ⟨by simpa [hnsz64] using hltL, by simpa [hnsz64] using hsub_fin,
                     by simpa [hnsz64] using hent_kept⟩⟩⟩ hmL
  · have har_f : at_root = false := by simpa using hc
    clear hassign hpush hpop hroot_pre hat_eq hlits_lt hv_len hfl_len hl_len hcv_le hmax_lt
    c0_hsteps
    refine wp_loop_inv
      (fun (i, ()) mL =>
        i.toNat ≤ old_sz.toNat ∧
        ∃ arL : List (BitVec 32), arL.length = c.arena_cap ∧
          OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + i.toNat) s.core.arena arL ∧
          (∀ j < i.toNat, arL[dst.toNat + 3 + j]? = s.core.arena[src.toNat + 3 + j]?) ∧
          (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL)
      (fun (i, ()) _ => old_sz.toNat - i.toNat)
      (fun J hLoop => ?_) ?_
    · c0_hsteps
      exact hLoop (0#32, ()) m ⟨Nat.zero_le _, s.core.arena, har_len,
        fun _ _ => rfl, fun _ hj => by simp at hj, hm⟩
    · rintro J ⟨i, ⟨⟩⟩ mL ⟨hi_le, arL, harL, houtL, hcpL, hmL⟩ hLoop
      c0_hsplit
      · have hi_lt : i.toNat < old_sz.toNat := by c0_bound
        have hi1_eq : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := bv32_add1 (by omega)
        have hsrc_idx : (src + (3 : BitVec 64) + i.setWidth 64).toNat = src.toNat + 3 + i.toNat :=
          bv64_add3_zext_toNat (by omega)
        have hdst_idx : (dst + (3 : BitVec 64) + i.setWidth 64).toNat = dst.toNat + 3 + i.toNat :=
          bv64_add3_zext_toNat (by omega)
        have hsrc_lt : (src + (3 : BitVec 64) + i.setWidth 64).toNat < arL.length := by omega
        have hdst_lt : (dst + (3 : BitVec 64) + i.setWidth 64).toNat < arL.length := by omega
        have hread_orig : arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt =
            s.core.arena[src.toNat + 3 + i.toNat]'(by omega) := by
          have h1 := houtL.getElem?_ge (i := src.toNat + 3 + i.toNat) (by omega)
          rw [List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < arL.length),
            List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < s.core.arena.length)]
            at h1
          simp only [hsrc_idx]; exact Option.some.inj h1
        c0_hsteps
        let ar' := arL.set (dst + (3 : BitVec 64) + i.setWidth 64).toNat
          (arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt)
        refine hLoop (i + (1 : BitVec 32), ()) m (by dsimp only; rw [hi1_eq]; omega)
          ⟨by rw [hi1_eq]; omega, ar', by simp [ar', harL], ?_, ?_, hm⟩
        · intro idx hidx
          rw [hi1_eq] at hidx; dsimp only [ar']
          rw [List.getElem?_set_ne (by omega)]
          exact houtL idx (by omega)
        · intro j hj; rw [hi1_eq] at hj
          by_cases hje : j = i.toNat
          · subst hje; dsimp only [ar']
            rw [← hdst_idx, List.getElem?_set_self hdst_lt, hread_orig,
              List.getElem?_eq_getElem (by omega)]
          · dsimp only [ar']; rw [List.getElem?_set_ne (by omega)]; exact hcpL j (by omega)
      · have hi_eq : i.toNat = old_sz.toNat := by c0_bound
        c0_hsteps
        exact Qsp (old_sz.setWidth 64) arL s.core.vals s.core.flags s.core.lvl s.core.rsns
          s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
          s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.core.num_binary s.core.oom
          s.scratch.phases s.scratch.wsort mL
          ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩
          (hi_eq ▸ houtL)
          ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
             rfl, rfl, rfl, hi_eq ▸ hcpL⟩,
           fun ht => Bool.noConfusion (har_f.symm.trans ht)⟩ hmL

end SweepCopyProof

/-! ## 4. `full_reduce_purge_c0` (`fullReducePurgeC0Spec`) -/

section ReducePurgeProof

open Full.FullReduceTactics
open scoped Full.FullArenaTactics Full.FullReduceTactics

private def PurgeStateOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) : Prop :=
  FullSparseInv c F0 s' ∧
  FullWitnessInv c F0 F_cur s'.core ∧
  s'.core.cur_level ≤ s.core.cur_level ∧
  s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
  s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.tmp = s.core.tmp ∧
  s'.core.tmp_len = s.core.tmp_len ∧
  s'.core.frame_trail = s.core.frame_trail ∧
  s'.core.frame_dec = s.core.frame_dec ∧
  s'.core.inconsistent = s.core.inconsistent ∧
  s'.core.d_cur = s.core.d_cur ∧
  s'.core.d_val = s.core.d_val ∧
  s'.scratch.extend_len = s.scratch.extend_len ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  (0 < s'.core.cur_level →
    s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
    s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
    s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end)

private theorem purgeStateOk_refl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core) :
    PurgeStateOk c F0 F_cur s s :=
  ⟨hsp, hw, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem purgeStateOk_trans {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s1 s2 : FullState} (h1 : PurgeStateOk c F0 F_cur s s1)
    (h2 : PurgeStateOk c F0 F_cur s1 s2) : PurgeStateOk c F0 F_cur s s2 :=
  ⟨h2.1, h2.2.1, Nat.le_trans h2.2.2.1 h1.2.2.1, Nat.le_trans h2.2.2.2.1 h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun hpos => by
      have hpos1 : 0 < s1.core.cur_level := Nat.lt_of_lt_of_le hpos h2.2.2.1
      have ha := h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hpos
      have hb := h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hpos1
      exact ⟨ha.1.trans hb.1, ha.2.1.trans hb.2.1, ha.2.2.1.trans hb.2.2.1,
        ha.2.2.2.1.trans hb.2.2.2.1, ha.2.2.2.2.1.trans hb.2.2.2.2.1,
        ha.2.2.2.2.2.trans hb.2.2.2.2.2⟩⟩

private theorem purgeStateOk_with_unflushed {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s1 : FullState} (h1 : PurgeStateOk c F0 F_cur s s1)
    (u' : BitVec 64) :
    PurgeStateOk c F0 F_cur s { s1 with core := { s1.core with unflushed := u' } } := by
  have hsp1 := h1.1
  have hw' := FullDenseWatchHelpers.fullWitnessInv_with_unflushed h1.2.1 u'
  have hlen' : ({ s1 with core := { s1.core with unflushed := u' } } : FullState).LengthsOk c :=
    ⟨{ hsp1.1.lengths.core_ok with vals_len := hsp1.1.lengths.core_ok.vals_len },
      hsp1.1.lengths.scratch_ok⟩
  have hsp' : FullSparseInv c F0 { s1 with core := { s1.core with unflushed := u' } } :=
    ⟨⟨hlen', ⟨F_cur, hw'⟩⟩, hsp1.2.1, hsp1.2.2.1, hsp1.2.2.2.1, hsp1.2.2.2.2⟩
  exact purgeStateOk_trans h1 ⟨hsp', hw', Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem purgeStateOk_mark_reasons {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s2 : FullState} {ar' : List (BitVec 32)}
    (h2 : PurgeStateOk c F0 F_cur s s2)
    (hlen' : ({ s2 with core := { s2.core with arena := ar' } } : FullState).LengthsOk c)
    (hrefs : fullArenaClauseRefs { s2 with core := { s2.core with arena := ar' } } =
      fullArenaClauseRefs s2)
    (hper : ∀ r ∈ fullArenaClauseRefs s2,
      fullArenaClauseSize { s2 with core := { s2.core with arena := ar' } } r =
        fullArenaClauseSize s2 r ∧
      fullArenaClauseGarb { s2 with core := { s2.core with arena := ar' } } r =
        fullArenaClauseGarb s2 r ∧
      fullArenaClauseLits { s2 with core := { s2.core with arena := ar' } } r =
        fullArenaClauseLits s2 r)
    (hw' : FullWitnessInv c F0 F_cur { s2.core with arena := ar' }) :
    PurgeStateOk c F0 F_cur s { s2 with core := { s2.core with arena := ar' } } := by
  let s3 : FullState := { s2 with core := { s2.core with arena := ar' } }
  have hnd : FullArenaVarsNodup s3 := fun r hr hng => by
    rw [hrefs] at hr; rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
    exact h2.1.2.2.1 r hr hng
  have hll : FullLastLearnedWf s3 := fun i hi => by
    change s2.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (s2.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s3
    rw [hrefs]; exact h2.1.2.2.2.1.1 i hi
  exact purgeStateOk_trans h2 ⟨⟨⟨hlen', ⟨F_cur, hw'⟩⟩, h2.1.2.1, hnd,
    ⟨hll, h2.1.2.2.2.1.2⟩, h2.1.2.2.2.2⟩, hw', Nat.le_refl _, Nat.le_refl _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem purgeStateOk_backtrack0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s0 : FullState} (h0 : PurgeStateOk c F0 F_cur s s0)
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' : BitVec 64} {sc' : FullScratch} :
    let sB : FullState := { s0 with
      core := { s0.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
      scratch := sc' }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    sc'.last_learned = s0.scratch.last_learned →
    sc'.extend_len = s0.scratch.extend_len →
    sc'.work_stk2 = s0.scratch.work_stk2 →
    PurgeStateOk c F0 F_cur s sB := by
  intro sB hlen' hw' hll' hext' hws2'
  have hllB : FullLastLearnedWf sB := fun i hi => by
    change sc'.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sc'.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s0
    rw [hll']; exact h0.1.2.2.2.1.1 i hi
  exact purgeStateOk_trans h0 ⟨⟨⟨hlen', ⟨F_cur, hw'⟩⟩, h0.1.2.1, h0.1.2.2.1,
    ⟨hllB, hext' ▸ h0.1.2.2.2.1.2⟩, h0.1.2.2.2.2⟩, hw', Nat.zero_le _, Nat.le_refl _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hext', hws2', fun hpos => by cases hpos⟩

private theorem purgeStateOk_propagate0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sA : FullState} (hA : PurgeStateOk c F0 F_cur s sA) (hcl0 : sA.core.cur_level = 0)
    {valsB : List (BitVec 8)}
    {flagsB lvlB rsnsB trlB tpB wvecB arenaB wstkB : List (BitVec 32)}
    {teB propB wlenB : Nat} {unassB unflB wuB fuelB ctypeB crefB c0B c1B oomB : BitVec 64}
    {scB : FullScratch} :
    let sB : FullState :=
      { sA with
        core := { sA.core with
          vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
          trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
          unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB, wlen := wlenB,
          wusable := wuB, fuel := fuelB, confl_type := ctypeB, confl_ref := crefB,
          confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
        scratch := scB }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    FullArenaVarsNodup sB → (∀ ref ∈ fullArenaClauseRefs sA, ref ∈ fullArenaClauseRefs sB) →
    scB.last_learned = sA.scratch.last_learned →
    scB.extend_len = sA.scratch.extend_len →
    scB.work_stk2 = sA.scratch.work_stk2 →
    fuelB.toNat ≤ sA.core.fuel.toNat →
    PurgeStateOk c F0 F_cur s sB := by
  intro sB hlenB hwB hndB hrefsB hllB hextB hws2B hfuelB
  have hll' : FullLastLearnedWf sB := fun i hi => by
    change scB.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (scB.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs sB
    rw [hllB]; exact (hA.1.2.2.2.1.1 i hi).imp id (hrefsB _)
  exact purgeStateOk_trans hA ⟨⟨⟨hlenB, ⟨F_cur, hwB⟩⟩, hA.1.2.1, hndB,
    ⟨hll', hextB ▸ hA.1.2.2.2.1.2⟩, hA.1.2.2.2.2⟩, hwB, Nat.le_refl _, hfuelB,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hextB, hws2B,
    fun hpos => by change 0 < sA.core.cur_level at hpos; omega⟩

private theorem purgeStateOk_arena_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hst : PurgeStateOk c F0 F_cur s st)
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
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core →
    FullArenaVarsNodup sA → FullLastLearnedWf sA →
    sc'.extend_len = st.scratch.extend_len →
    sc'.work_stk2 = st.scratch.work_stk2 →
    (0 < st.core.cur_level →
      vals' = st.core.vals ∧ lvl' = st.core.lvl ∧ trl' = st.core.trl ∧
      tp' = st.core.trail_pos ∧ te' = st.core.trail_end) →
    PurgeStateOk c F0 F_cur s sA := by
  intro sA hlenA hwA hndA hllA hextA hws2A hposA
  exact purgeStateOk_trans hst ⟨⟨⟨hlenA, ⟨F_cur, hwA⟩⟩, hst.1.2.1, hndA,
    ⟨hllA, hextA ▸ hst.1.2.2.2.1.2⟩, hst.1.2.2.2.2⟩, hwA, Nat.le_refl _, Nat.le_refl _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hextA, hws2A,
    fun hpos => by
      obtain ⟨hv, hl, ht, htp, hte⟩ := hposA hpos
      exact ⟨rfl, hv, hl, ht, htp, hte⟩⟩

private theorem purgeStateOk_mark_garb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {cr : Nat} {agN : BitVec 64}
    (hokL : PurgeStateOk c F0 F_cur s sL) (hrmL : FullDenseWatchSpecs.FullReasonsMarked sL)
    (hcr_mem : cr ∈ fullArenaClauseRefs sL)
    (hcr_norsn : (fullArenaHdr sL cr &&& 0x00200000#32) = 0#32)
    (hcr_ar : cr < sL.core.arena.length) :
    let sM : FullState :=
      { sL with core := { sL.core with
        arena := sL.core.arena.set cr (sL.core.arena[cr]'hcr_ar ||| 0x00080000#32)
        arena_garbage := agN } }
    PurgeStateOk c F0 F_cur s sM ∧ FullDenseWatchSpecs.FullReasonsMarked sM ∧
    fullArenaClauseRefs sM = fullArenaClauseRefs sL := by
  intro sM
  have hhdr_eq : sL.core.arena[cr]'hcr_ar = fullArenaHdr sL cr := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some]
  have hnonact := FullDenseWatchHelpers.markGarb_nonact_of_reasonsMarked hokL.2.1 hrmL hcr_norsn
  have hmg := FullDenseWatchHelpers.markGarb_preserves_fullWitnessInv
    hokL.1.1.lengths hokL.2.1 hcr_mem agN hnonact
  rw [← hhdr_eq] at hmg
  obtain ⟨hlenM, hrefsM, hwM, hrsnM, hndM⟩ := hmg
  have hndM' : FullArenaVarsNodup sM := hndM fun r hr hng => hokL.1.2.2.1 r hr hng
  have hllM : FullLastLearnedWf sM := fun j hj => by
    change sL.scratch.last_learned[j]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sL.scratch.last_learned[j]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs sM
    rw [hrefsM]; exact hokL.1.2.2.2.1.1 j hj
  have hrmM : FullDenseWatchSpecs.FullReasonsMarked sM := fun idx hidx hlp hlg => by
    have hne0 : sL.core.rsns[(sL.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      intro heq; rw [heq] at hlg; revert hlg; decide
    have hrs := hokL.2.1.reason_inv idx hidx hne0
    have hbf : ¬ (sL.core.rsns[(sL.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
    rw [ite_eq_right hbf] at hrs
    rw [hrsnM _ hrs.1]; exact hrmL idx hidx hlp hlg
  have hokM : PurgeStateOk c F0 F_cur s sM :=
    purgeStateOk_trans hokL ⟨⟨⟨hlenM, ⟨F_cur, hwM⟩⟩, hokL.1.2.1, hndM',
      ⟨hllM, hokL.1.2.2.2.1.2⟩, hokL.1.2.2.2.2⟩, hwM,
      Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  exact ⟨hokM, hrmM, hrefsM⟩

private theorem purge_bv32_norsn_of_mask {x : BitVec 32} (hx : (x &&& 0x00280000#32) = 0#32) :
    (x &&& 0x00200000#32) = 0#32 := by
  have h21 : (x &&& 0x00280000#32)[21] = false := by rw [hx]; decide
  have hb : (0x00280000#32 : BitVec 32)[21] = true := by decide
  simp only [BitVec.getElem_and, hb, Bool.and_true] at h21
  ext i hi
  by_cases hi21 : i = 21
  · subst hi21; simp [h21]
  · have hz : (0x00200000#32 : BitVec 32)[i] = false := by revert i hi hi21; decide
    simp [BitVec.getElem_and, hz]

/-- `FullM7V2Robust.full_reduce_purge_c0` satisfies `fullReducePurgeC0Spec`
(`Full.fullReduceSpec (h, true, ())`). -/
theorem full_reduce_purge_c0_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullReducePurgeC0Spec a m Q X →
      Func.wp Γ full_reduce_purge_c0_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, ⟨hlen, hw, hlm, hnd, hext, hdm⟩, hm, hQ⟩
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hsp0 : FullSparseInv c F0 s := ⟨⟨hlen, ⟨F_cur, hw⟩⟩, hlm, hnd, hext, hdm⟩
  have hok0 : PurgeStateOk c F0 F_cur s s := purgeStateOk_refl hsp0 hw
  have hret : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      PurgeStateOk c F0 F_cur s st → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64) →
      (FullMem c st ⋆ R) ml → Q (r, ()) ml := fun r st ml hok hr hu hoom hml =>
    hQ r st ml ⟨hok.1.1.lengths, hok.2.1, hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1, hok.1.2.2.2.2⟩
      hr hok.2.2.1 hok.2.2.2.1 hok.2.2.2.2.1 hok.2.2.2.2.2.1
      hok.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hu hoom
      (fun _ => hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2) hml
  unfold Func.wp full_reduce_purge_c0_body
  fr_to_group
  refine wp_join_group
    (fun _ m1 => ∃ s1 : FullState, PurgeStateOk c F0 F_cur s s1 ∧
      (s.core.oom = 0#64 → s1.core.oom = 0#64) ∧ (FullMem c s1 ⋆ R) m1)
    ?_ ?_
  · rintro _ _ m1 ⟨s1, hok1, hoom1, hm1⟩
    clear hsp0 hm
    fr_to_group; c0_call hMarkRsn
    refine ⟨c, F0, F_cur, s1, R, rfl, hok1.1.1.lengths, hok1.2.1, hm1,
      fun ar2 m3 hlen3 hrefs3 hper3 hrm3 hw3 hm3 => ?_⟩
    obtain ⟨s3, hok3, hoom3, hrm3', hm3'⟩ :
        ∃ s3 : FullState, PurgeStateOk c F0 F_cur s s3 ∧
          (s.core.oom = 0#64 → s3.core.oom = 0#64) ∧ FullDenseWatchSpecs.FullReasonsMarked s3 ∧
          (FullMem c s3 ⋆ R) m3 :=
      ⟨{ s1 with core := { s1.core with arena := ar2 } },
        purgeStateOk_mark_reasons hok1 hlen3 hrefs3 hper3 hw3, hoom1,
        fun idx hidx hp hg => hrm3 rfl idx hidx hp hg, hm3⟩
    clear hm3 s1 hok1 hoom1 hm1 ar2 hlen3 hrefs3 hper3 hrm3 hw3
    fr_to_group
    -- Join after loop 1 (`while (p < arena_len) { ... if (n <= p) break; p = n; }`)
    refine wp_join_group
      (fun _ m4 =>
        ∃ s4 : FullState, PurgeStateOk c F0 F_cur s s4 ∧
          (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧ FullDenseWatchSpecs.FullReasonsMarked s4 ∧
          (FullMem c s4 ⋆ R) m4)
      ?_ ?_
    · rintro _ _ m4 ⟨s4, hok4, hoom4, hrm4, hm4⟩
      clear s3 hok3 hoom3 hrm3' hm3' m3
      fr_to_group
      -- `while (true)` sweep loop
      refine wp_join_group
        (fun _ mK => ∃ sK : FullState, PurgeStateOk c F0 F_cur s sK ∧
          (s.core.oom = 0#64 → sK.core.oom = 0#64) ∧ (FullMem c sK ⋆ R) mK)
        (fun _ _ mK ⟨sK, hokK, hoomK, hmK⟩ => by
          fr_steps
          exact hret 1#64 sK mK hokK (Or.inr (Or.inl rfl)) (fun h => by cases h)
            (fun _ => hoomK) hmK)
        (fun Jbrk hJbrk => by
          fr_to_group
          refine wp_loop_group
            (fun rem () ml => ∃ st : FullState, rem = c.max_vars - st.core.trail_end ∧
              PurgeStateOk c F0 F_cur s st ∧
              (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
              (0 < st.core.cur_level → FullDenseWatchSpecs.FullReasonsMarked st) ∧
              (FullMem c st ⋆ R) ml) ?_ ?_
          · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hok_st, hoom_st, hrm_st, hm_st⟩
            dsimp only [Blocks.get]
            refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
            c0_call hSweep
            refine ⟨c, F0, F_cur, st, R, rfl, hok_st.1.1.lengths, hok_st.2.1,
              hok_st.1.2.2.1, hok_st.1.2.2.2.2,
              fun hpos => fun idx hidx hp hg => hrm_st hpos idx hidx hp hg, hm_st,
              fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena'
                alen' wlen' wu' fred' ni' nr' nb' oom' sc' mA
                hlenA hdomA hextA hws2A hllA hwA hndA hoomA hposA hsr1 hsr2 hsr3 hmA => ?_⟩
            obtain ⟨sA, hokA, hclA_eq, hteA, hoomA', hmA'⟩ :
                ∃ sA : FullState, PurgeStateOk c F0 F_cur s sA ∧
                  sA.core.cur_level = st.core.cur_level ∧ sA.core.trail_end = te' ∧
                  (sr = 0#64 ∨ sr = 1#64 → sA.core.oom = 0#64) ∧ (FullMem c sA ⋆ R) mA :=
              ⟨_, purgeStateOk_arena_sweep hok_st hlenA hwA hndA hllA hextA hws2A
                (fun hpos => by
                  obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposA hpos
                  exact ⟨hv, hl, ht, htp, hte⟩),
                rfl, rfl, hoomA, hmA⟩
            clear hmA vals' flags' lvl' rsns' trl' tp' unass' unfl' wvec' wstk' arena' alen'
              wlen' wu' fred' ni' nr' nb' oom' sc' hlenA hwA hndA hllA hextA hws2A hoomA
              hposA hsr3
            fr_steps
            · exact hret 20#64 sA mA hokA (Or.inr (Or.inr rfl)) (fun _ => (hsr2 hc).2)
                (fun h => by cases h) hmA'
            · exact hret 0#64 sA mA hokA (Or.inl rfl) (fun h => by cases h)
                (fun h => by cases h) hmA'
            · exact hJbrk () mA ⟨sA, hokA, fun _ => hoomA' (Or.inl hc), hmA'⟩
            · have hsr_eq1 : sr = 1#64 := by
                rcases hdomA with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
              obtain ⟨hcl0, hst_te_lt⟩ := hsr1 hsr_eq1
              have hoomA0 : sA.core.oom = 0#64 := hoomA' (Or.inr hsr_eq1)
              have hclA0 : sA.core.cur_level = 0 := by omega
              c0_call hProp
              refine ⟨c, F0, F_cur, sA, R, rfl, hokA.1.1.lengths, hokA.2.1, hokA.1.2.2.2.2, hmA',
                fun pr valsB flagsB lvlB rsnsB trlB tpB teB propB unassB unflB wvecB arenaB
                  wstkB wlenB wuB fuelB ctypeB crefB c0B c1B oomB ticksB wsortB phasesB mB
                  hlenB hwB hteB hpermB hfuelB hdomB hpr0 hpr1 hpr2 hidleB hmB => ?_⟩
              have hndB : FullArenaVarsNodup
                  { sA with
                    core := { sA.core with
                      vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
                      trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
                      unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB,
                      wlen := wlenB, wusable := wuB, fuel := fuelB, confl_type := ctypeB,
                      confl_ref := crefB, confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
                    scratch := { sA.scratch with
                      search_ticks := ticksB, wsort := wsortB, phases := phasesB } } := by
                intro ref href hng
                have href0 : ref ∈ fullArenaClauseRefsCore sA.core := hpermB.2.1 ▸ href
                obtain ⟨_, hgb, hp⟩ := hpermB.2.2 ref href0
                exact (hp.map (· / 2)).nodup_iff.mpr (hokA.1.2.2.1 ref href0 (hgb.symm.trans hng))
              obtain ⟨sB, hokB, hteB_eq, hclB0, hoomB', hconflB', hmB'⟩ :
                  ∃ sB : FullState, PurgeStateOk c F0 F_cur s sB ∧
                    sB.core.trail_end = teB ∧ sB.core.cur_level = 0 ∧
                    (pr = 0#64 → sB.core.oom = 0#64) ∧ (pr = 1#64 → F0.Unsat) ∧
                    (FullMem c sB ⋆ R) mB := by
                refine ⟨_, purgeStateOk_propagate0 hokA hclA0 hlenB hwB hndB
                  (fun ref href => by
                    change ref ∈ fullArenaClauseRefsCore _; rw [hpermB.2.1]; exact href)
                  rfl rfl rfl hfuelB, rfl, hclA0, fun h0 => (hpr0 h0).2.1 hoomA0, ?_, hmB⟩
                intro h1
                refine FullDenseWatchHelpers.fullConflictInv_level0_unsat hwB hclA0 ?_
                rcases (hpr1 h1).2.2 with ⟨ht, h0, h1', hf0, hf1, hent⟩ | hlg
                · exact Or.inl ⟨ht, h0, h1', hent, hf0, hf1⟩
                · exact Or.inr hlg
              have hteA_le_B : te' ≤ teB := by rw [← hteA]; exact hteB.1
              clear hmB hteB valsB flagsB lvlB rsnsB trlB tpB propB unassB unflB wvecB arenaB
                wstkB wlenB wuB fuelB ctypeB crefB c0B c1B oomB ticksB wsortB phasesB
                hlenB hwB hndB hpermB hfuelB hdomB hpr0 hpr1 hpr2 hidleB
              fr_steps
              · exact hret 20#64 sB mB hokB (Or.inr (Or.inr rfl))
                  (fun _ => hconflB' hc) (fun h => by cases h) hmB'
              · exact hret 0#64 sB mB hokB (Or.inl rfl) (fun h => by cases h)
                  (fun h => by cases h) hmB'
              · have hte_bd : sB.core.trail_end ≤ c.max_vars :=
                  Nat.le_trans hokB.1.1.lengths.core_ok.trail_end_le
                    hokB.1.1.lengths.core_ok.cur_vars_le
                exact ih (c.max_vars - sB.core.trail_end) () _ (by omega)
                  ⟨{ sB with core := { sB.core with unflushed := 0#64 } }, rfl,
                    purgeStateOk_with_unflushed hokB 0#64, fun _ => hoomB' hc,
                    fun hpos => by change 0 < sB.core.cur_level at hpos; omega, hm⟩
          · intro L hL; fr_steps
            exact hL (c.max_vars - s4.core.trail_end) () m4
              ⟨s4, rfl, hok4, hoom4, fun _ => hrm4, hm4⟩)
    · intro J4 hJ4
      fr_to_group
      refine wp_loop_inv
        (fun (p, ()) mL =>
          p.toNat ≤ s3.core.arena_len ∧
          (p.toNat = s3.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s3) ∧
          ∃ sL : FullState,
            sL.core.arena_len = s3.core.arena_len ∧
            PurgeStateOk c F0 F_cur s sL ∧ (s.core.oom = 0#64 → sL.core.oom = 0#64) ∧
            FullDenseWatchSpecs.FullReasonsMarked sL ∧
            fullArenaClauseRefs sL = fullArenaClauseRefs s3 ∧ (FullMem c sL ⋆ R) mL)
        (fun (p, ()) _ => s3.core.arena_len - p.toNat)
        (fun JL hLoopL => by
          fr_to_group
          refine hLoopL (0#64, ()) m3 ⟨Nat.zero_le _, ?_, s3, rfl,
            hok3, hoom3, hrm3', rfl, hm3'⟩
          by_cases hz : s3.core.arena_len = 0
          · exact Or.inl hz.symm
          · exact Or.inr (FullDenseWatchHelpers.fullArenaClauseRefs_zero_mem hok3.2.1.arena
              (Nat.pos_of_ne_zero hz)))
        (fun JL (p, ()) mL ⟨hp_le, hp_mem, sL, halenL, hokL, hoomL, hrmL, hrefsL, hmL⟩ hLoopL => ?_)
      have hlenL := hokL.1.1.lengths
      have halL := hlenL.core_ok.arena_len_le
      have haarL := hlenL.core_ok.arena_len_arr
      fr_to_group
      · have hp_lt : p.toNat < sL.core.arena_len := by c0_bound
        have hp_in : p.toNat ∈ fullArenaClauseRefs sL := by
          rw [hrefsL]; exact hp_mem.resolve_left (by omega)
        have hp_wf := hokL.2.1.arena.refs_wf p.toNat hp_in
        have hp_lt32 : p.toNat < 2 ^ 32 := by omega
        have hp_trunc : (p.setWidth 32).toNat = p.toNat := by
          rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hp_lt32
        have hnb := fullArenaNextOff_bounds (ar := sL.core.arena) (alen := sL.core.arena_len)
          (cref := p.toNat) hp_wf.1
        have hnxt_mem := FullDenseWatchHelpers.fullArenaClauseRefs_next_mem hokL.2.1.arena hp_in
        let n32 :=
          BitVec.ofNat 32 (fullArenaNextOff sL.core.arena sL.core.arena_len (p.setWidth 32).toNat)
        have hn_eq : (n32.setWidth 64).toNat =
            fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat := by
          dsimp only [n32]; rw [hp_trunc, BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        fr_to_group; c0_call hArenaNext
        refine ⟨c, sL, R, rfl, hlenL, hmL, ?_⟩
        fr_to_group
        refine wp_join_group
          (fun _ mM =>
            ∃ sM : FullState,
              sM.core.arena_len = s3.core.arena_len ∧
              PurgeStateOk c F0 F_cur s sM ∧ (s.core.oom = 0#64 → sM.core.oom = 0#64) ∧
              FullDenseWatchSpecs.FullReasonsMarked sM ∧
              fullArenaClauseRefs sM = fullArenaClauseRefs s3 ∧ (FullMem c sM ⋆ R) mM)
          (fun _ _ mM ⟨sM, halenM, hokM, hoomM, hrmM, hrefsM, hmM⟩ => by
            fr_to_group
            · exfalso
              have hle_np : (n32.setWidth 64).toNat ≤ p.toNat := by c0_bound
              omega
            · fr_steps
              exact hLoopL (n32.setWidth 64, ()) mM (by dsimp only; rw [hn_eq]; omega)
                ⟨by rw [hn_eq]; omega,
                  by rw [hn_eq]
                     rcases hnxt_mem with hend | hmem
                     · exact Or.inl (hend.trans halenL)
                     · exact Or.inr (hrefsL ▸ hmem),
                  sM, halenM, hokM, hoomM, hrmM, hrefsM, hmM⟩)
          (fun JM hJM => ?_)
        fr_to_group
        · have hp3_le : p.toNat + 3 ≤ sL.core.arena_len := hp_wf.1
          have hmask :
              (sL.core.arena[p.toNat]'(by omega) &&& (0x00080000#32 ||| 0x00200000#32)) = 0#32 := by
            simpa [bv_c0] using hc
          have hmask2 : (sL.core.arena[p.toNat]'(by omega) &&& 0x00280000#32) = 0#32 := by
            simpa [show (0x00080000#32 ||| 0x00200000#32) = 0x00280000#32 by decide] using hmask
          have hp_ar : p.toNat < sL.core.arena.length := by omega
          have hp2_ar : p.toNat + 2 < sL.core.arena.length := by omega
          have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := by
            rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          have hp2_ar64 : (p + 2#64).toNat < sL.core.arena.length := by rw [hp2_eq]; exact hp2_ar
          have hhdr_eq : sL.core.arena[p.toNat]'(by omega) = fullArenaHdr sL p.toNat := by
            unfold fullArenaHdr fullArenaHdrCore
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hnorsn : (fullArenaHdr sL p.toNat &&& 0x00200000#32) = 0#32 := by
            rw [← hhdr_eq]; exact purge_bv32_norsn_of_mask hmask2
          fr_steps
          let agN := sL.core.arena_garbage + 3#64 +
            ((sL.core.arena.set p.toNat
              (sL.core.arena[p.toNat]'hp_ar ||| 0x00080000#32))[p.toNat + 2]'(by
                simp [hp2_ar])).setWidth 64
          obtain ⟨hokM, hrmM, hrefsM⟩ :=
            purgeStateOk_mark_garb (agN := agN) hokL hrmL hp_in hnorsn hp_ar
          let sM : FullState :=
            { sL with core := { sL.core with
              arena := sL.core.arena.set p.toNat (sL.core.arena[p.toNat]'hp_ar ||| 0x00080000#32)
              arena_garbage := agN } }
          exact hJM () m ⟨sM, halenL, hokM, hoomL, hrmM, hrefsM.trans hrefsL, by
            refine cast (congrArg (fun st' => (FullMem c st' ⋆ R) m) ?_) hm
            dsimp only [sM, agN]
            have h5 : (524288 : BitVec 32) = 0x00080000#32 := rfl
            have h3 : (3 : BitVec 64) = 3#64 := rfl
            have h2 : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := hp2_eq
            simp only [h5, h3]
            congr 2; congr 1
            simp only [h2]⟩
        all_goals exact hJM () mL ⟨sL, halenL, hokL, hoomL, hrmL, hrefsL, hmL⟩
      · exact hJ4 (p, ()) mL ⟨sL, hokL, hoomL, hrmL, hmL⟩
  · intro J1 hJ1
    fr_to_group
    · refine wp_join_group
        (fun _ mB => ∃ sB : FullState, PurgeStateOk c F0 F_cur s sB ∧ sB.core.cur_level = 0 ∧
          (s.core.oom = 0#64 → sB.core.oom = 0#64) ∧ (FullMem c sB ⋆ R) mB)
        (fun _ _ mB ⟨sB, hokB, hclB, hoomB0, hmB⟩ => by
          clear hc hsp0 hm
          fr_to_group; c0_call hProp
          refine ⟨c, F0, F_cur, sB, R, rfl, hokB.1.1.lengths, hokB.2.1, hokB.1.2.2.2.2, hmB,
            fun pr valsP flagsP lvlP rsnsP trlP tpP teP propP unassP unflP wvecP arenaP wstkP
              wlenP wuP fuelP ctypeP crefP c0P c1P oomP ticksP wsortP phasesP mP
              hlenP hwP hteP hpermP hfuelP hdomP hpr0 hpr1 hpr2 hidleP hmP => ?_⟩
          have hndP : FullArenaVarsNodup
              { sB with
                core := { sB.core with
                  vals := valsP, flags := flagsP, lvl := lvlP, rsns := rsnsP, trl := trlP,
                  trail_pos := tpP, trail_end := teP, propagated := propP, unassigned := unassP,
                  unflushed := unflP, wvec := wvecP, arena := arenaP, wstk := wstkP,
                  wlen := wlenP, wusable := wuP, fuel := fuelP, confl_type := ctypeP,
                  confl_ref := crefP, confl_lit0 := c0P, confl_lit1 := c1P, oom := oomP }
                scratch := { sB.scratch with
                  search_ticks := ticksP, wsort := wsortP, phases := phasesP } } := by
            intro ref href hng
            have href0 : ref ∈ fullArenaClauseRefsCore sB.core := hpermP.2.1 ▸ href
            obtain ⟨_, hgb, hp⟩ := hpermP.2.2 ref href0
            exact (hp.map (· / 2)).nodup_iff.mpr (hokB.1.2.2.1 ref href0 (hgb.symm.trans hng))
          obtain ⟨sP, hokP, hoomP', hconflP', hmP'⟩ :
              ∃ sP : FullState, PurgeStateOk c F0 F_cur s sP ∧
                (pr = 0#64 → s.core.oom = 0#64 → sP.core.oom = 0#64) ∧
                (pr = 1#64 → F0.Unsat) ∧ (FullMem c sP ⋆ R) mP := by
            refine ⟨_, purgeStateOk_propagate0 hokB hclB hlenP hwP hndP
              (fun ref href => by
                change ref ∈ fullArenaClauseRefsCore _; rw [hpermP.2.1]; exact href)
              rfl rfl rfl hfuelP, fun h0 hso => (hpr0 h0).2.1 (hoomB0 hso), ?_, hmP⟩
            intro h1
            refine FullDenseWatchHelpers.fullConflictInv_level0_unsat hwP hclB ?_
            rcases (hpr1 h1).2.2 with ⟨ht, h0, h1', hf0, hf1, hent⟩ | hlg
            · exact Or.inl ⟨ht, h0, h1', hent, hf0, hf1⟩
            · exact Or.inr hlg
          clear hmP hteP valsP flagsP lvlP rsnsP trlP tpP teP propP unassP unflP wvecP arenaP wstkP
            wlenP wuP fuelP ctypeP crefP c0P c1P oomP ticksP wsortP phasesP hlenP hwP hndP hpermP
            hfuelP hdomP hpr0 hpr1 hpr2 hidleP
          fr_steps
          · exact hret 20#64 sP mP hokP (Or.inr (Or.inr rfl)) (fun _ => hconflP' hc)
              (fun h => by cases h) hmP'
          · exact hret 0#64 sP mP hokP (Or.inl rfl) (fun h => by cases h)
              (fun h => by cases h) hmP'
          · exact hJ1 () _ ⟨{ sP with core := { sP.core with unflushed := 0#64 } },
              purgeStateOk_with_unflushed hokP 0#64, hoomP' hc, hm⟩)
        (fun JB hJB => by
          fr_to_group
          · c0_call hBacktrack
            have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
            have hcl_bd : s.core.cur_level < 2 ^ 64 := by
              have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
              have := hlen.core_ok.cur_vars_le; omega
            refine ⟨c, s, R, rfl, hlen, hcl_bd,
              fun _ => by
                have := hlen.core_ok.trail_end_le
                have := hlen.core_ok.cur_vars_le
                have := hw.cur_level_le
                omega,
              hw.trail_lits_lt, hm,
              fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
                hlen' _ _ hcl' hps _ _ _ hwt _ hm' => ?_⟩
            have hmin : cl' = 0 := hcl'.trans (Nat.min_zero _)
            subst hmin
            fr_steps
            exact hJB () m' ⟨_, purgeStateOk_backtrack0 hok0 hlen' (hwt F0 F_cur hw (Nat.zero_le _))
              hps.1.1 hps.1.2 hps.2.2.1, rfl, id, hm'⟩
          · have hcl0 : s.core.cur_level = 0 := by
              have hle := hlen.core_ok.trail_end_le
              have hcv := hlen.core_ok.cur_vars_le
              have hcl := hw.cur_level_le
              c0_bound
            exact hJB () _ ⟨s, hok0, hcl0, id, hm⟩)
    · exact hJ1 () _ ⟨s, hok0, id, hm⟩

end ReducePurgeProof

/-! ## 5. `full_learn_clause` (`Full.fullLearnClauseSpec`) -/

section LearnClauseProof

open Full.FullLearnAnaTactics Full.FullLearnAnaHelpers
open scoped Full.FullArenaTactics Full.FullLearnAnaTactics

private theorem v2r_la_bv64_add1_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem v2r_la_bv32_lshr_1 (x : BitVec 32) :
    (x >>> 1#32).toNat = x.toNat / 2 := bv32_lshr_1 x

private theorem v2r_la_bv64_sub1_toNat {x : BitVec 64} (h : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hx := x.isLt; bv_omega

private theorem v2r_la_getElem_congr_idx {α : Type} {xs : List α} {i j : Nat}
    (h : i = j) {hi : i < xs.length} {hj : j < xs.length} :
    xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem v2r_nat_lt31_bv32_msb0 {n : Nat} (hn : n < 2 ^ 31 - 1) :
    let v := (BitVec.ofNat 64 n).setWidth 32
    v.toNat = n ∧ v ≠ 0xFFFFFFFF#32 ∧ (v &&& 0x80000000#32) = 0#32 := by
  have hn_mod : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by omega)
  have hto : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), hn_mod]
  refine ⟨hto, ?_, ?_⟩
  · intro heq; have h1 := congrArg BitVec.toNat heq; rw [hto] at h1
    have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
  · apply BitVec.eq_of_getElem_eq; intro i hi
    rw [BitVec.getElem_and, BitVec.getElem_zero]
    by_cases h31 : i = 31
    · subst h31; rw [BitVec.getElem_eq_testBit_toNat, hto, Nat.testBit,
        Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega : n < 2 ^ 31)]; simp
    · rw [show (0x80000000#32 : BitVec 32)[i]'hi = false from by revert i hi h31; decide]
      simp

private theorem v2r_tmp_take1_eq {tmp : List (BitVec 32)} {u : BitVec 32} (h1 : 1 ≤ tmp.length)
    (h0 : tmp[0]? = some u) : (tmp.take 1).map BitVec.toNat = [u.toNat] := by
  cases tmp with
  | nil => simp at h1
  | cons a _ =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0; simp

private theorem v2r_tmp_take2_eq {tmp : List (BitVec 32)} {u v : BitVec 32} (h2 : 2 ≤ tmp.length)
    (h0 : tmp[0]? = some u) (h1 : tmp[1]? = some v) :
    (tmp.take 2).map BitVec.toNat = [u.toNat, v.toNat] := by
  rcases tmp with _ | ⟨a, _ | ⟨b, _⟩⟩
  · simp at h2
  · simp at h2
  · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
    subst h0 h1; simp

private theorem v2r_canon_to_laOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k) :
    FullLearnAnaSpecs.FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem v2r_laOtfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullLearnAnaSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem v2r_canon_to_laOtfsInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s) :
    FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, v2r_canon_to_laOtfs h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem v2r_laOtfsInv_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s) :
    FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, v2r_laOtfs_to_canon h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem v2r_laSparse_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullLearnAnaSpecs.FullSparseInvW c F0 F_cur s) :
    FullSparseInvW c F0 F_cur s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem v2r_bv32_or_used31_garb (h : BitVec 32) :
    ((h ||| 0xF8000000#32) &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  rw [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_and]
  have h0 : ((0xF8000000#32 : BitVec 32)[i]'hi && (0x00080000#32 : BitVec 32)[i]'hi) = false := by
    revert i hi; decide
  cases h1 : (0x00080000#32 : BitVec 32)[i]'hi <;> cases h2 : (0xF8000000#32 : BitVec 32)[i]'hi <;>
    simp_all

private theorem v2r_bv32_or_used31_shrk (h : BitVec 32) :
    ((h ||| 0xF8000000#32) &&& 0x00800000#32) = (h &&& 0x00800000#32) := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  rw [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_and]
  have h0 : ((0xF8000000#32 : BitVec 32)[i]'hi && (0x00800000#32 : BitVec 32)[i]'hi) = false := by
    revert i hi; decide
  cases h1 : (0x00800000#32 : BitVec 32)[i]'hi <;> cases h2 : (0xF8000000#32 : BitVec 32)[i]'hi <;>
    simp_all

private theorem v2r_orUsed31_preserves_fullSparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hs : FullSparseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) :
    let ar' := s.core.arena.set cref (fullArenaHdr s cref ||| 0xF8000000#32)
    let s' : FullState := { s with core := { s.core with arena := ar' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro ar' s'
  have hlen := hs.1.core_ok
  have hw := hs.2.1
  have ha := hw.arena
  have hcref_wf := ha.refs_wf cref href
  have har_len : cref < s.core.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hget_cref : s.core.arena[cref]? = some (fullArenaHdrCore s.core cref) := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem har_len, Option.getD_some]
  have ha_cref : s'.core.arena[cref]? = some (fullArenaHdrCore s.core cref ||| 0xF8000000#32) :=
    List.getElem?_set_self har_len
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff s.core.arena s.core.arena_len cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len cref ≤ r) := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (ha.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by omega, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : s'.core.arena[cref + 2]? = s.core.arena[cref + 2]? :=
        List.getElem?_set_ne (by omega)
      have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some]
      rw [v2r_bv32_or_used31_shrk,
        show fullArenaHdrCore s.core cref = s.core.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
        · have := (ha.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i hi1 _
        rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (ha.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [s', ar']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_ne (by omega)]
    · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
      · have := (ha.refs_wf r hr).2.1; rw [List.getElem?_set_ne (by omega)]
      · rw [List.getElem?_set_ne (by omega)]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore
    by_cases hrc : r = cref
    · subst r; rw [ha_cref, hget_cref, Option.getD_some, Option.getD_some, v2r_bv32_or_used31_garb]
    · dsimp only [s', ar']; rw [List.getElem?_set_ne (Ne.symm hrc)]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hszr := hsz_eq r hr
    unfold fullArenaClauseLitsCore
    rw [hszr]; congr 1
    apply List.ext_getElem
    · have hwf := ha.refs_wf r hr
      simp only [List.length_take, List.length_drop, s', ar', List.length_set]
    · intro j hj1 hj2
      simp only [List.getElem_take, List.getElem_drop]
      dsimp only [s', ar']
      have hne_idx : cref ≠ r + 3 + j := by
        by_cases hrc : r = cref
        · subst r; omega
        · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
          · simp only [List.length_take, List.length_drop, s', ar', List.length_set] at hj1
            omega
          · omega
      exact List.getElem_set_ne hne_idx _
  have ha' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨ha.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := ha.refs_wf r hr
      dsimp only [s'] at hnxt ⊢; rw [hnxt r hr, hsz_eq r hr]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh ⊢
          simpa only [ha_cref, hget_cref, Option.getD_some, v2r_bv32_or_used31_shrk] using hsh
        · unfold fullArenaHdrCore at hsh ⊢
          simpa only [s', ar', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
        have hr3 := (ha.refs_wf r hr).1
        have : r < s.core.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      have hsh_ar : (s.core.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_r, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, ht0_hi, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (ha.refs_wf r hr).1 hsh_ar ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (ha.refs_wf cref hr).2.1; omega
        · rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
          · omega
          · have := (ha.refs_wf r hr).2.1; omega
      refine ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo,
        by dsimp only [s']; exact Nat.lt_of_le_of_lt ht0_hi ht2, ?_⟩
      dsimp only [s', ar']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr] at hl
      exact ha.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr]
      exact ha.entails r hr hng
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := ha'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        change if (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 then _ else _
        split
        · rename_i hbin; rw [ite_eq_left hbin] at hrs; exact hrs
        · rename_i hlg; rw [ite_eq_right hlg] at hrs
          obtain ⟨hrr, hng, hall⟩ := hrs
          exact ⟨hrefs.symm ▸ hrr, (hgarb_eq _ hrr).trans hng,
            fun q hq => hall q ((hlits_eq _ hrr) ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hmem := hw.reason_lit_mem idx hidx hne hlg
        have hrs := hw.reason_inv idx hidx hne
        rw [ite_eq_right (fun h => h hlg)] at hrs
        change (s.core.trl[idx]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s'.core _
        rw [hlits_eq _ hrs.1]; exact hmem }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen with arena_len_arr := by simp [s', ar', hlen.arena_len_arr] }, hs.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    change fullArenaClauseGarbCore s'.core r = false at hng; rw [hgarb_eq r hr] at hng
    change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
    rw [hlits_eq r hr]; exact hs.2.2.2.1 r hr hng
  have hext' : FullExtScratchOk c s' :=
    Full.FullExtScratchOk.of_pres hs.2.2.2.2.1 ⟨rfl, rfl⟩
      (fun _ hr => by change _ ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr)
  exact ⟨⟨hlen', hw', hs.2.2.1, hnd', hext', hs.2.2.2.2.2⟩, hrefs,
    fun r hr => ⟨hgarb_eq r hr, hlits_eq r hr⟩⟩

private theorem bv32_lshr1_nat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

private def V2rAddClPre (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (nlvl : BitVec 64) (tmp_sw : List (BitVec 32))
    (vals_bt : List (BitVec 8)) (lvl_bt trl_bt : List (BitVec 32)) (te_bt : Nat)
    (sg : FullState) : Prop :=
  FullSparseInvW c F0 F_cur sg ∧ sg.core.cur_level = nlvl.toNat ∧
  sg.core.cur_vars = s.core.cur_vars ∧ sg.core.fuel.toNat ≤ s.core.fuel.toNat ∧
  sg.core.tmp = tmp_sw ∧ sg.core.tmp_len = s.core.tmp_len ∧
  sg.core.vals = vals_bt ∧ sg.core.lvl = lvl_bt ∧ sg.core.trl = trl_bt ∧
  sg.core.trail_end = te_bt ∧ sg.scratch.work_stk2 = s.scratch.work_stk2

private def V2rNrSpec (F_cur : List (List Nat)) (s : FullState)
    (uip wm : BitVec 32) (tmp_sw : List (BitVec 32))
    (sac : FullState) (r_ac : BitVec 64) : Prop :=
  r_ac = 0xFFFFFFFF#64 ∨
  (r_ac ≠ 0xFFFFFFFF#64 ∧
    if r_ac = 0xFFFFFFFE#64 then
      (cnfOfClauses F_cur).EntailsClause (cnfClause [uip.toNat, wm.toNat])
    else
      r_ac.toNat < 2 ^ 31 - 1 ∧
      r_ac.toNat ∈ fullArenaClauseRefs sac ∧
      fullArenaClauseGarb sac r_ac.toNat = false ∧
      (∀ q ∈ fullArenaClauseLits sac r_ac.toNat,
        q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat) ∧
      uip.toNat ∈ fullArenaClauseLits sac r_ac.toNat)

private theorem v2r_learn_clause_post_ac_wp {Γ X} {Q : Post [i64]} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s_ac : FullState} {R : Mem 64 → Prop} {m_ac : Mem 64}
    {uip_lit wm : BitVec 32} {new_ref64 : BitVec 64} {max_lvl : Nat}
    {tmp_sw : List (BitVec 32)}
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X)
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hac_sparse : FullSparseInvW c F0 F_cur s_ac)
    (hcur_lt : s_ac.core.cur_level < s.core.cur_level)
    (hmax_pos : 0 < max_lvl) (hmax_le : max_lvl ≤ s_ac.core.cur_level)
    (hmax_lt28 : max_lvl < 2 * 2 ^ 28)
    (hcv_eq : s_ac.core.cur_vars = s.core.cur_vars)
    (hfuel : s_ac.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hws2 : s_ac.scratch.work_stk2 = s.scratch.work_stk2)
    (htmp_eq : s_ac.core.tmp = tmp_sw) (htlen_eq : s_ac.core.tmp_len = s.core.tmp_len)
    (hsw_1 : tmp_sw[1]? = some wm)
    (htl_2 : 2 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (huip_lt : uip_lit.toNat < 2 * s.core.cur_vars)
    (hwm_lt : wm.toNat < 2 * s.core.cur_vars)
    (htmp_lt : ∀ k < s.core.tmp_len, (tmp_sw[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (hwm_on_bt : ∃ idx < s_ac.core.trail_end,
      (s_ac.core.trl[idx]?.getD 0#32).toNat = wm.toNat ^^^ 1 ∧
      (s_ac.core.lvl[wm.toNat / 2]?.getD 0#32).toNat ≤ max_lvl)
    (hlow : ∀ q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
      q = uip_lit.toNat ∨ ∃ idx < s_ac.core.trail_end,
        (s_ac.core.trl[idx]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s_ac.core.lvl[q / 2]?.getD 0#32).toNat ≤ max_lvl)
    (hr_spec : V2rNrSpec F_cur s uip_lit wm tmp_sw s_ac new_ref64)
    (hm_ac : (FullMem c s_ac ⋆ R) m_ac) :
    wp Γ Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
          args := (Arg.var new_ref64, Arg.imm 4294967295, ()) } fun p36 =>
        Expr.jnz (Arg.var p36.1) (Expr.ret (Arg.imm 0, ()))
          (Expr.let_
            { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var uip_lit, ()) } fun p37 =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var c.pVals, Arg.var p37.1, ()) } fun p38 =>
              Expr.load i8 (Arg.var p38.1) fun ld =>
                Expr.let_
                  { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p39 =>
                  Expr.let_
                    { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var ld, ()) } fun p40 =>
                    Expr.let_
                      { sig := [i8], code := OpCode.sext 8 32,
                        args := (Arg.var p39.1, ()) } fun p41 =>
                      Expr.let_
                        { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                          args := (Arg.var p40.1, Arg.var p41.1, ()) } fun p42 =>
                        Expr.jnz (Arg.var p42.1) (Expr.ret (Arg.imm 0, ()))
                          (Expr.group (sig := [[]])
                            (fun _Ju =>
                              Blocks.cons
                                (fun _ =>
                                  Expr.group (sig := [[i32]])
                                    (fun _Js =>
                                      Blocks.cons
                                        (fun p43 =>
                                          Expr.let_
                                            { sig := [i64], code := OpCode.trunc 64 32,
                                              args := (Arg.var (BitVec.ofNat 64 max_lvl), ()) }
                                            fun p44 =>
                                            Expr.call (as := [i64, i32, i32, i32]) (bs := [])
                                              (rs := [i64]) "full_assign_lvl"
                                              (Arg.var c.hdr, Arg.var uip_lit, Arg.var p43.1,
                                                Arg.var p44.1, ())
                                              fun (_ : Tup Val []) =>
                                              Expr.call (as := [i64, i64]) (bs := []) (rs := [i64])
                                                "full_eager_subsume"
                                                (Arg.var c.hdr, Arg.var new_ref64, ())
                                                fun (_ : Tup Val []) =>
                                                  Expr.ret (rs := [i64]) (Arg.imm 1, ()))
                                        Blocks.nil)
                                    fun Js =>
                                    Expr.let_
                                      { sig := [i64, i64],
                                        code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                                        args := (Arg.var new_ref64, Arg.imm 4294967294, ()) }
                                      fun p =>
                                      Expr.jnz (Arg.var p.1)
                                        (Expr.let_
                                          { sig := [i32], code := OpCode.sext 32 64,
                                            args := (Arg.imm 1, ()) } fun p =>
                                          Expr.let_
                                            { sig := [i64, i64], code := OpCode.mul i64,
                                              args := (Arg.var p.1, Arg.imm 4, ()) } fun p =>
                                            Expr.let_
                                              { sig := [i64, i64], code := OpCode.add i64,
                                                args := (Arg.var c.pTmp, Arg.var p.1, ()) } fun p =>
                                              Expr.load i32 (Arg.var p.1) fun ld =>
                                                Expr.let_
                                                  { sig := [i32, i32], code := OpCode.and i32,
                                                    args := (Arg.var ld, Arg.imm 2147483647, ()) }
                                                  fun p =>
                                                  Expr.let_
                                                    { sig := [i32, i32], code := OpCode.or i32,
                                                      args :=
                                                        (Arg.var p.1, Arg.imm 2147483648, ()) }
                                                    fun p =>
                                                    Expr.jump Js.1 (Arg.var p.1, ()))
                                        (Expr.let_
                                          { sig := [i64], code := OpCode.trunc 64 32,
                                            args := (Arg.var new_ref64, ()) } fun p =>
                                          Expr.jump Js.1 (Arg.var p.1, ())))
                                Blocks.nil)
                            fun Ju =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                                args := (Arg.var new_ref64, Arg.imm 4294967294, ()) } fun p =>
                              Expr.jnz (Arg.var p.1)
                                (Expr.let_
                                  { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var c.hdr, Arg.imm 48, ()) } fun p =>
                                  Expr.load i64 (Arg.var p.1) fun ld =>
                                    Expr.let_
                                      { sig := [i64, i64],
                                        code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                                        args := (Arg.var new_ref64, Arg.var ld, ()) } fun p =>
                                      Expr.jnz (Arg.var p.1)
                                        (Expr.let_
                                          { sig := [i64, i64], code := OpCode.add i64,
                                            args := (Arg.var c.hdr, Arg.imm 112, ()) } fun p =>
                                          Expr.load i64 (Arg.var p.1) fun ld_ar =>
                                            Expr.let_
                                              { sig := [i64, i64], code := OpCode.mul i64,
                                                args := (Arg.var new_ref64, Arg.imm 4, ()) }
                                              fun p =>
                                              Expr.let_
                                                { sig := [i64, i64], code := OpCode.add i64,
                                                  args := (Arg.var ld_ar, Arg.var p.1, ()) }
                                                fun p_el =>
                                                Expr.load i32 (Arg.var p_el.1) fun ld_h =>
                                                  Expr.let_
                                                    { sig := [i32, i32], code := OpCode.shl i32,
                                                      args := (Arg.imm 31, Arg.imm 27, ()) }
                                                    fun p_sh =>
                                                    Expr.let_
                                                      { sig := [i32, i32], code := OpCode.or i32,
                                                        args := (Arg.var ld_h, Arg.var p_sh.1, ()) }
                                                      fun p_nh =>
                                                      Expr.store (Arg.var p_nh.1)
                                                        (Arg.var p_el.1)
                                                        (Expr.jump Ju.1 ()))
                                        (Expr.jump Ju.1 ()))
                                (Expr.jump Ju.1 ()))))
      m_ac := by
  have hac_len := hac_sparse.1
  have hcl := hac_len.core_ok
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have huip_vlen : uip_lit.toNat < s_ac.core.vals.length := by
    rw [hcl.vals_len]; have := hcl.cur_vars_le; omega
  c0_split
  · c0_steps
    exact hQ 0#64 s_ac m_ac hac_len (Or.inl rfl) hcv_eq hfuel hws2
      (fun h => by cases h) (fun _ => hac_sparse) (fun h => by cases h) hm_ac
  · have hne_ff : new_ref64 ≠ 0xFFFFFFFF#64 := by assumption
    have hnr_ok := (hr_spec.resolve_left hne_ff).2
    c0_split
    · c0_steps
      exact hQ 0#64 s_ac m_ac hac_len (Or.inl rfl) hcv_eq hfuel hws2
        (fun h => by cases h) (fun _ => hac_sparse) (fun h => by cases h) hm_ac
    · have huip_z : s_ac.core.vals[uip_lit.toNat]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem huip_vlen, Option.getD_some]
        exact (i8_sext32_eq0 _).mp hc
      refine wp_join_group (ts := []) (fun () m_u =>
          ∃ ar_u : List (BitVec 32),
            let s_u : FullState := { s_ac with core := { s_ac.core with arena := ar_u } }
            FullSparseInvW c F0 F_cur s_u ∧ fullArenaClauseRefs s_u = fullArenaClauseRefs s_ac ∧
            (∀ r ∈ fullArenaClauseRefs s_ac,
              fullArenaClauseGarb s_u r = fullArenaClauseGarb s_ac r ∧
              fullArenaClauseLits s_u r = fullArenaClauseLits s_ac r) ∧
            (FullMem c s_u ⋆ R) m_u) ?_ ?_
      · rintro _ ⟨⟩ m_u ⟨ar_u, hu_sparse, hrefs_u, hprops_u, hm_u⟩
        let s_u : FullState := { s_ac with core := { s_ac.core with arena := ar_u } }
        have hu_len := hu_sparse.1
        refine wp_join_group (ts := [i32]) (fun (rsn_bv, ()) m_r =>
            m_r = m_u ∧ rsn_bv ≠ 0xFFFFFFFF#32 ∧
            (if (rsn_bv &&& 0x80000000#32) ≠ 0#32 then
              let ot := (rsn_bv &&& 0x7FFFFFFF#32).toNat
              ot < 2 * s_u.core.cur_vars ∧
              (cnfOfClauses F_cur).EntailsClause (cnfClause [uip_lit.toNat, ot]) ∧
              ∃ m < s_u.core.trail_end, (s_u.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
                (s_u.core.lvl[ot / 2]?.getD 0#32).toNat ≤ max_lvl
            else
              rsn_bv.toNat ∈ fullArenaClauseRefsCore s_u.core ∧
              fullArenaClauseGarbCore s_u.core rsn_bv.toNat = false ∧
              (∀ q ∈ fullArenaClauseLitsCore s_u.core rsn_bv.toNat,
                q = uip_lit.toNat ∨ ∃ m < s_u.core.trail_end,
                  (s_u.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
                  (s_u.core.lvl[q / 2]?.getD 0#32).toNat ≤ max_lvl) ∧
              uip_lit.toNat ∈ fullArenaClauseLitsCore s_u.core rsn_bv.toNat)) ?_ ?_
        · rintro _ ⟨rsn_bv, ⟨⟩⟩ m_r ⟨rfl, hrsn_ne, hrsn_prop⟩
          have hte_lt : s_u.core.trail_end < c.max_vars := by
            have h1 := hu_sparse.2.1.trail_end_lt_of_unassigned (hcv_eq ▸ huip_lt) huip_z
            have := hcl.cur_vars_le; dsimp only [s_u] at h1 ⊢; omega
          have hml_tr : ((BitVec.ofNat 64 max_lvl).setWidth 32).toNat = max_lvl := by
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : max_lvl < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
          have hml_nz : (BitVec.ofNat 64 max_lvl).setWidth 32 ≠ 0#32 := fun heq => by
            have h0 := congrArg BitVec.toNat heq
            rw [hml_tr, show (0#32 : BitVec 32).toNat = 0 from rfl] at h0; omega
          c0_to_group; c0_call hAsgn
          refine ⟨c, s_u, R, rfl, hu_len, hm_u, ?_⟩
          rw [ite_eq_right (fun h => by
            dsimp only [s_u] at h hte_lt
            rw [huip_z] at h
            have := hcv_eq ▸ huip_lt
            rcases h with h | h | h
            · omega
            · omega
            · exact h rfl)]
          intro v rsn_let unfl_let flags' unass' phases' m_as hfll hph s_as0 hm_as
          have hrsn_let : rsn_let = rsn_bv := ite_eq_right hml_nz
          have hunfl_let : unfl_let = s_u.core.unflushed := ite_eq_right hml_nz
          c0_clean; c0_to_group
          let s_as : FullState :=
            { s_u with
              core :=
                { s_u.core with
                  vals := (s_u.core.vals.set uip_lit.toNat 1#8).set (uip_lit.toNat ^^^ 1) 0xFF#8
                  flags := flags'
                  lvl := s_u.core.lvl.set (uip_lit.toNat / 2)
                    ((BitVec.ofNat 64 max_lvl).setWidth 32)
                  rsns := s_u.core.rsns.set (uip_lit.toNat / 2) rsn_bv
                  trl := s_u.core.trl.set s_u.core.trail_end uip_lit
                  trail_pos := s_u.core.trail_pos.set (uip_lit.toNat / 2)
                    (BitVec.ofNat 32 s_u.core.trail_end)
                  trail_end := s_u.core.trail_end + 1
                  unassigned := unass', unflushed := s_u.core.unflushed }
              scratch := { s_u.scratch with phases := phases' } }
          have hml_bv : (BitVec.ofNat 64 max_lvl).setWidth 32 = BitVec.ofNat 32 max_lvl :=
            BitVec.eq_of_toNat_eq (by rw [hml_tr, bv32_ofNat_toNat (by omega)])
          have hsc_as : s_as.scratch.LengthsOk c := { hu_len.scratch_ok with phases_len := hph }
          have ⟨has_len, has_w⟩ := chronoAssign_preserves_fullWitness hu_sparse.2.1 hu_len hsc_as
            (rsn := rsn_bv) (unassigned' := unass') (unflushed' := s_u.core.unflushed)
            hfll (hcv_eq ▸ huip_lt) huip_z hmax_le (fun _ => hrsn_ne)
            (fun h0 => absurd h0 (by omega))
            (fun _ _ => by
              split
              · rename_i hbin; rw [ite_eq_left hbin] at hrsn_prop; exact hrsn_prop
              · rename_i hnbin; rw [ite_eq_right hnbin] at hrsn_prop
                exact ⟨hrsn_prop.1, hrsn_prop.2.1, hrsn_prop.2.2.1⟩)
            (fun _ _ hzero => by
              rw [ite_eq_right (fun h => absurd hzero h)] at hrsn_prop; exact hrsn_prop.2.2.2)
          have hm_as' : (FullMem c s_as ⋆ R) m_as := by
            simpa only [s_as, s_as0, v, hrsn_let, hunfl_let] using hm_as
          have hmne0 : max_lvl ≠ 0 := by omega
          have has_sparse : FullSparseInvW c F0 F_cur s_as :=
            ⟨by simpa [s_as, hml_bv, hmne0] using has_len,
             by simpa [s_as, hml_bv, hmne0] using has_w,
             hu_sparse.2.2.1, hu_sparse.2.2.2.1, hu_sparse.2.2.2.2.1, hu_sparse.2.2.2.2.2⟩
          have htmp_as_lt : ∀ k < s_as.core.tmp_len,
              (s_as.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars := fun k hk => by
            simpa only [s_as, s_u, htmp_eq, htlen_eq] using
              htmp_lt k (by simpa [s_as, s_u, htlen_eq] using hk)
          c0_call hEsub
          refine ⟨c, F0, F_cur, s_as, R, rfl, has_sparse, htmp_as_lt, ?_, hm_as', ?_⟩
          · intro _
            by_cases hfe : new_ref64 = 0xFFFFFFFE#64
            · subst hfe; exfalso; have : (0xFFFFFFFE#64 : BitVec 64).toNat = 2 ^ 32 - 2 := rfl
              omega
            · simp only [hfe, ↓reduceIte] at hnr_ok
              change new_ref64.toNat ∈ fullArenaClauseRefs s_u
              rw [hrefs_u]; exact hnr_ok.2.1
          · intro ar' ag' sc' m_fin _ hfin_sparse hws2' hm_fin
            c0_steps
            exact hQ 1#64 _ m_fin hfin_sparse.1 (Or.inr (Or.inl rfl)) hcv_eq hfuel
              (hws2'.trans (by simp [s_as, s_u, hws2])) (fun h => by cases h)
              (fun h => by cases h) (fun _ => ⟨hfin_sparse, hcur_lt⟩) hm_fin
        · intro Jrsn hJrsn; c0_split
          · have hfe : new_ref64 = 0xFFFFFFFE#64 := by assumption
            simp only [hfe, ↓reduceIte] at hnr_ok
            have := hcl.cur_vars_le
            have hwm_lt31 : wm.toNat < 2 ^ 31 - 1 := by omega
            have hmask := bin_rsn_mask_props (l := wm) hwm_lt31
            have h1_lt : 1 < s_u.core.tmp.length := by rw [hu_len.core_ok.tmp_len_arr]; omega
            have htmp1_eq : s_u.core.tmp[1]'h1_lt = wm := Option.some.inj
              (by rw [← List.getElem?_eq_getElem h1_lt, show s_u.core.tmp = tmp_sw from htmp_eq,
                hsw_1])
            c0_steps
            refine wp_load_of (load_full_tmp1 (c := c) (s := s_u) (R := R) h1_lt hm_u) ?_
            c0_steps
            rw [htmp1_eq]
            refine hJrsn ((wm &&& 0x7FFFFFFF#32) ||| 0x80000000#32, ()) m_u ⟨rfl, hmask.1, ?_⟩
            rw [ite_eq_left hmask.2.1, hmask.2.2]
            exact ⟨hcv_eq ▸ hwm_lt, hnr_ok, hwm_on_bt⟩
          · have hne_fe : new_ref64 ≠ 0xFFFFFFFE#64 := by assumption
            simp only [hne_fe, ↓reduceIte] at hnr_ok
            obtain ⟨hlt31, href, hng, hlits_sub, huip_in⟩ := hnr_ok
            have hnr_bv := v2r_nat_lt31_bv32_msb0 hlt31
            rw [BitVec.eq_of_toNat_eq (bv64_ofNat_toNat new_ref64.isLt)] at hnr_bv
            c0_steps
            refine hJrsn (new_ref64.setWidth 32, ()) m_u ⟨rfl, hnr_bv.2.1, ?_⟩
            rw [ite_eq_right (fun h => absurd hnr_bv.2.2 h), hnr_bv.1]
            obtain ⟨hgu, hlu⟩ := hprops_u new_ref64.toNat href
            exact ⟨by change _ ∈ fullArenaClauseRefs s_u; rw [hrefs_u]; exact href,
              hgu.trans hng,
              fun q hq => hlow q (hlits_sub q (by
                change q ∈ fullArenaClauseLits s_ac _; rw [← hlu]; exact hq)),
              by change uip_lit.toNat ∈ fullArenaClauseLits s_u _; rw [hlu]; exact huip_in⟩
      · intro Ju hJu; c0_split
        · have hne_fe : new_ref64 ≠ 0xFFFFFFFE#64 := by assumption
          simp only [hne_fe, ↓reduceIte] at hnr_ok
          obtain ⟨_, href, _, _, _⟩ := hnr_ok
          c0_split
          · have hnr_ar : new_ref64.toNat < s_ac.core.arena.length := by
              have hwf := hac_sparse.2.1.arena.refs_wf new_ref64.toNat href
              have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
            have hhdr_eq : s_ac.core.arena[new_ref64.toNat]'hnr_ar =
                fullArenaHdr s_ac new_ref64.toNat := by
              unfold fullArenaHdr fullArenaHdrCore
              rw [List.getElem?_eq_getElem hnr_ar, Option.getD_some]
            have hmask31 : ((31 : BitVec 32) <<< (27 : BitVec 32)) = 0xF8000000#32 := by decide
            have hmask31n : ((31 : BitVec 32) <<< (27 : Nat)) = 0xF8000000#32 := by decide
            c0_steps
            refine wp_load_of (FullArenaTactics.load_full_arena_ptr hm_ac) ?_
            c0_steps
            obtain ⟨hu_sp, hrefs_u, hprops_u⟩ :=
              v2r_orUsed31_preserves_fullSparseW hac_sparse href
            exact hJu () m ⟨_, hu_sp, hrefs_u, hprops_u,
              by simpa only [hhdr_eq, hmask31, hmask31n] using hm⟩
          · c0_steps; exact hJu () m_ac ⟨s_ac.core.arena, hac_sparse, rfl,
              fun _ _ => ⟨rfl, rfl⟩, hm_ac⟩
        · c0_steps; exact hJu () m_ac ⟨s_ac.core.arena, hac_sparse, rfl,
            fun _ _ => ⟨rfl, rfl⟩, hm_ac⟩

/-- `FullM7V2Robust.full_learn_clause` satisfies canonical `Full.fullLearnClauseSpec` with the
pre-add headroom check and 3-step `defrag` / `full_reduce(h, true)` / `full_reduce_purge_c0`
OOM-retry ladder. -/
theorem full_learn_clause_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X →
      Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hRedPurge : ∀ a m Q X, fullReducePurgeC0Spec a m Q X →
      Γ "full_reduce_purge_c0" [i64] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    ∀ args m Q X, fullLearnClauseSpec args m Q X →
      Func.wp Γ full_learn_clause_body args m Q X := by
  rintro ⟨h, glue, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hs_c, hcur_pos, htl1, htl_cv, htmp_nd,
    htmp_vals, htmp_lvls, hent, hm, hQ⟩
  have hs := v2r_canon_to_laOtfsInv hs_c
  have hcl := hs.1.core_ok
  have hw := hs.2.1
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have hcur_le := hw.cur_level_le
  have hte_le := hcl.trail_end_le
  have hcv_le := hcl.cur_vars_le
  have htmp_len_arr := hcl.tmp_len_arr
  have huip_in : 0 < s.core.tmp.length := by omega
  let uip := s.core.tmp[0]'huip_in
  have huip_0 : s.core.tmp[0]? = some uip := List.getElem?_eq_getElem huip_in
  have huip_lt : uip.toNat < 2 * s.core.cur_vars := by
    have := (htmp_vals 0 htl1).1; rwa [huip_0, Option.getD_some] at this
  unfold Func.wp full_learn_clause_body
  c0_clean; c0_split
  · -- Unit learned clause (`tmp_len == 1`)
    have htl_is1 : s.core.tmp_len = 1 := by bv_omega
    have hent_unit : (cnfOfClauses F_cur).EntailsClause (cnfClause [uip.toNat]) := by
      rwa [htl_is1, v2r_tmp_take1_eq huip_in huip_0] at hent
    c0_to_group; c0_call hBt
    refine ⟨c, s, R, rfl, hs.1, by omega, fun _ => by omega, hw.trail_lits_lt, hm, ?_⟩
    intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt s_bt
      hbt_len hbt_te _ hbt_cl hbt_pres _ _ _ _ hbt_otfs hm_bt
    have hcl_0 : cl' = 0 := by
      rw [hbt_cl, show (0 : BitVec 64).toNat = 0 from rfl, Nat.min_zero]
    have hbt_w : FullWitnessInv c F0 F_cur s_bt.core := hbt_otfs F0 F_cur hs_c.2.1 (by omega)
    have hbt_sparse := fullBacktrack_preserves_fullSparseW hs hbt_len hbt_w rfl rfl rfl rfl rfl
      hbt_pres.1
    have huip_vlen : uip.toNat < vals'.length := by
      have hvl := hbt_len.core_ok.vals_len; dsimp only [s_bt] at hvl; omega
    c0_clean; c0_split
    · c0_clean; c0_steps
      exact hQ 0#64 s_bt m_bt hbt_len (Or.inl rfl) rfl (Nat.le_refl _) hbt_pres.2.2.1
        (fun h => by cases h) (fun _ => hbt_sparse) (fun h => by cases h) hm_bt
    · have huip_z : vals'[uip.toNat]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem huip_vlen, Option.getD_some]
        exact (i8_sext32_eq0 _).mp hc
      have hbt_te_lt : te' < c.max_vars := by
        have := hbt_w.trail_end_lt_of_unassigned huip_lt huip_z; dsimp only [s_bt] at this; omega
      c0_to_group; c0_call hAsgn
      refine ⟨c, s_bt, R, rfl, hbt_len, hm_bt, ?_⟩
      rw [ite_eq_right (fun h => by
        dsimp only [s_bt] at h
        rw [show s.core.tmp[0] = uip from rfl] at h
        simp only [huip_z, ne_eq, not_true_eq_false, or_false] at h; omega)]
      intro v rsn_let unfl_let flags' unass'' phases' m_f hfll hph s_f0 hm_f
      have hrsn_let : rsn_let = 0xFFFFFFFF#32 := ite_eq_left rfl
      have hunfl_let : unfl_let = s_bt.core.unflushed + 1#64 := ite_eq_left rfl
      c0_clean; c0_steps
      let s_fin : FullState :=
        { s_bt with
          core :=
            { s_bt.core with
              vals := (vals'.set uip.toNat 1#8).set (uip.toNat ^^^ 1) 0xFF#8
              flags := flags', lvl := lvl'.set (uip.toNat / 2) 0#32
              rsns := rsns'.set (uip.toNat / 2) 0xFFFFFFFF#32
              trl := trl'.set te' uip
              trail_pos := tp'.set (uip.toNat / 2) (BitVec.ofNat 32 te')
              trail_end := te' + 1, unassigned := unass''
              unflushed := s_bt.core.unflushed + 1#64 }
          scratch := { sc' with phases := phases' } }
      have hsc_f : s_fin.scratch.LengthsOk c := { hbt_len.scratch_ok with phases_len := hph }
      have ⟨hfin_len, hfin_w⟩ := chronoAssign_preserves_fullWitness hbt_w hbt_len hsc_f
        (rsn := 0xFFFFFFFF#32) (unassigned' := unass'') (unflushed' := s_bt.core.unflushed + 1#64)
        hfll huip_lt huip_z (Nat.zero_le _) (fun h => by omega) (fun _ => hent_unit)
        (fun h _ => by omega) (fun h _ _ => by omega)
      have hfin_sparse : FullSparseInvW c F0 F_cur s_fin :=
        ⟨hfin_len, hfin_w,
          by dsimp only [s_fin, s_bt]; exact hbt_sparse.2.2.1,
          by dsimp only [s_fin, s_bt]; exact hbt_sparse.2.2.2.1,
          by dsimp only [s_fin, s_bt]; exact hbt_sparse.2.2.2.2.1,
          by dsimp only [s_fin, s_bt]; exact hbt_sparse.2.2.2.2.2⟩
      have hm_f' : (FullMem c s_fin ⋆ R) m_f := by
        simpa only [s_fin, s_f0, s_bt, v, hrsn_let, hunfl_let,
          show (0 : BitVec 32) = 0#32 from rfl, show s.core.tmp[0] = uip from rfl] using hm_f
      exact hQ 1#64 s_fin m_f hfin_len (Or.inr (Or.inl rfl)) rfl (Nat.le_refl _)
        (by dsimp only [s_fin, s_bt]; exact hbt_pres.2.2.1) (fun h => by cases h)
        (fun h => by cases h)
        (fun _ => ⟨hfin_sparse, by dsimp only [s_fin, s_bt]; omega⟩) hm_f'
  · -- Non-unit learned clause (`2 ≤ tmp_len`)
    have htl_ge2 : 2 ≤ s.core.tmp_len := by
      have hne : s.core.tmp_len ≠ 1 := by
        intro h1; have heq : BitVec.ofNat 64 s.core.tmp_len = 1#64 := by rw [h1]
        contradiction
      omega
    have hmi_eq : (BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat = s.core.tmp_len - 1 := by
      rw [v2r_la_bv64_sub1_toNat (x := BitVec.ofNat 64 s.core.tmp_len)
        (by rw [bv64_ofNat_toNat (by omega)]; omega), bv64_ofNat_toNat (by omega)]
    have hmi_tmp : (BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat < s.core.tmp.length := by
      rw [hmi_eq]; omega
    c0_clean; c0_steps
    let wm := s.core.tmp[s.core.tmp_len - 1]'(by omega)
    have hwm_eq : s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat]'hmi_tmp = wm :=
      v2r_la_getElem_congr_idx hmi_eq
    have hmi_post := htmp_lvls (s.core.tmp_len - 1) (by omega) (by omega)
    have hwm_get : s.core.tmp[s.core.tmp_len - 1]?.getD 0#32 = wm := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hwm_vals := htmp_vals (s.core.tmp_len - 1) (by omega)
    rw [hwm_get] at hmi_post hwm_vals
    have hwm_lt : wm.toNat < 2 * s.core.cur_vars := hwm_vals.1
    have hwm_v_lt : wm.toNat / 2 < s.core.lvl.length := by rw [hcl.lvl_len]; omega
    have hmi_lvl : ((s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat]'hmi_tmp >>>
        1#32).setWidth 64).toNat < s.core.lvl.length := by
      rw [bv32_setWidth64_toNat, v2r_la_bv32_lshr_1, hwm_eq]; exact hwm_v_lt
    refine wp_load_of (FullArenaTactics.c0_load_full_lvl (c := c) (s := s) (R := R) hmi_lvl hm) ?_
    let max_lvl := (s.core.lvl[wm.toNat / 2]?.getD 0#32).toNat
    have hml_pos : 0 < max_lvl := hmi_post.1
    have hml_lt : max_lvl < s.core.cur_level := hmi_post.2.1
    have hml_get : (s.core.lvl[((s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len -
        1#64).toNat]'hmi_tmp >>> 1#32).setWidth 64).toNat]'hmi_lvl).toNat = max_lvl := by
      have hidx : ((s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat]'hmi_tmp >>>
          1#32).setWidth 64).toNat = wm.toNat / 2 := by
        rw [bv32_setWidth64_toNat, v2r_la_bv32_lshr_1, hwm_eq]
      dsimp only [max_lvl]; rw [List.getElem?_eq_getElem hwm_v_lt, Option.getD_some]
      exact congrArg BitVec.toNat (v2r_la_getElem_congr_idx hidx)
    c0_to_group
    refine wp_join_group (ts := [i64]) (fun (ml_v, ()) m_ml =>
        m_ml = m ∧ ml_v = BitVec.ofNat 64 max_lvl) ?_ ?_
    · rintro _ ⟨ml_v, ⟨⟩⟩ m_ml ⟨rfl, rfl⟩
      have h1_tmp : 1 < s.core.tmp.length := by omega
      c0_clean; c0_let_simp
      refine wp_load_of (load_full_tmp1 (c := c) (s := s) (R := R) h1_tmp hm) ?_
      c0_clean; c0_let_simp
      refine wp_load_of (FullArenaTactics.c0_load_full_tmp (c := c) (s := s) (R := R) hmi_tmp hm) ?_
      let w1 := s.core.tmp[1]'h1_tmp
      have hwm_bv_eq : s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat]'hmi_tmp = wm :=
        hwm_eq
      refine wp_store_sep (store_full_tmp1 (c := c) (s := s) (R := R)
          (s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat]'hmi_tmp) h1_tmp hm)
        fun m1 hm1 => ?_
      c0_clean; c0_let_simp
      let s_t1 : FullState := { s with core := { s.core with tmp := s.core.tmp.set 1 wm } }
      have hmi_t1 : (BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat < s_t1.core.tmp.length := by
        dsimp only [s_t1]; rw [List.length_set]; exact hmi_tmp
      have hm1' : (FullMem c s_t1 ⋆ R) m1 := by simpa only [s_t1, hwm_bv_eq] using hm1
      refine wp_store_sep
        (FullArenaTactics.c0_store_full_tmp (c := c) (s := s_t1) (R := R) w1 hmi_t1 hm1')
        fun m_sw hm_sw => ?_
      let tmp_sw := (s.core.tmp.set 1 wm).set (s.core.tmp_len - 1) w1
      let s_sw : FullState := { s with core := { s.core with tmp := tmp_sw } }
      have htmpsw_eq : (s.core.tmp.set 1 wm).set
          (BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat w1 = tmp_sw := by
        rw [hmi_eq]
      have hm_sw' : (FullMem c s_sw ⋆ R) m_sw := by
        simpa only [s_sw, s_t1, show (1 : BitVec 64) = 1#64 from rfl, htmpsw_eq] using hm_sw
      have hsw_len : s_sw.LengthsOk c :=
        ⟨{ hcl with tmp_len_arr := by simp [s_sw, tmp_sw, htmp_len_arr] }, hs.1.scratch_ok⟩
      have hsw_inv : FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s_sw :=
        ⟨hsw_len, FullOtfsWitnessInv.with_tmp hw tmp_sw, hs.2.2.1,
          hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩
      have hsw_inv_c : FullOtfsInvW c F0 F_cur s_sw := v2r_laOtfsInv_to_canon hsw_inv
      obtain ⟨hsw_iff, hsw_mem, hsw_nd, hsw_0, hsw_1⟩ :=
        swap_tmp_props_full (tl := s.core.tmp_len) (max_idx := s.core.tmp_len - 1)
          htl_ge2 (by omega) (by omega) (by omega) huip_0 htmp_nd
      have hent_sw : (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((tmp_sw.take s.core.tmp_len).map BitVec.toNat)) :=
        entails_of_mem_or_false hent fun l hl => Or.inl ((hsw_iff l).mpr hl)
      have hsw_lits_lt : ∀ l ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
          l < 2 * s.core.cur_vars := fun l hl => by
        rcases hsw_mem l hl with rfl | ⟨j, hj1, hj2, hjeq⟩
        · exact huip_lt
        · rw [← hjeq]; exact (htmp_vals j hj2).1
      have htmp_sw_lt : ∀ k < s.core.tmp_len, (tmp_sw[k]?.getD 0#32).toNat < 2 * c.max_vars := by
        intro k hk
        have hlen_sw : k < tmp_sw.length := by simp [tmp_sw, htmp_len_arr]; omega
        have hmem : (tmp_sw[k]?.getD 0#32).toNat ∈
            (tmp_sw.take s.core.tmp_len).map BitVec.toNat := by
          rw [List.mem_map]
          refine ⟨tmp_sw[k]'hlen_sw, List.mem_iff_getElem.mpr ⟨k, by
            rw [List.length_take]; omega, by rw [List.getElem_take]⟩, ?_⟩
          rw [List.getElem?_eq_getElem hlen_sw, Option.getD_some]
        have := hsw_lits_lt _ hmem; omega
      c0_to_group; c0_call hDnl
      have hml_bv64 : (BitVec.ofNat 64 max_lvl).toNat = max_lvl := bv64_ofNat_toNat (by omega)
      refine ⟨c, s_sw, R, rfl, hsw_len, by dsimp [s_sw]; omega, hm_sw',
        fun nlvl hnlvl_zero hnlvl_pos => ?_⟩
      obtain ⟨hnlvl_ge, hnlvl_lt⟩ :=
        hnlvl_pos hcur_pos (by dsimp [s_sw]; rw [hml_bv64]; exact hml_lt)
      dsimp only [s_sw] at hnlvl_ge hnlvl_lt
      rw [hml_bv64] at hnlvl_ge
      c0_to_group; c0_call hBt
      refine ⟨c, s_sw, R, rfl, hsw_len, by dsimp [s_sw]; omega,
        fun _ => by have := hcl.cur_vars_le; omega, hsw_inv.2.1.trail_lits_lt, hm_sw', ?_⟩
      intro vals_bt lvl_bt rsns_bt trl_bt tp_bt te_bt prop_bt cl_bt unass_bt sc_bt m_bt s_bt
        hbt_len hbt_te_le hbt_prop_le hbt_cl hbt_pres hbt_ss hbt_a1 hbt_keep hbt_a2 hbt_otfs hm_bt
      have hcl_bt : cl_bt = nlvl.toNat := by dsimp [s_sw] at hbt_cl; omega
      have hbt_w : FullWitnessInv c F0 F_cur s_bt.core := hbt_otfs F0 F_cur hsw_inv_c.2.1 hnlvl_lt
      have hbt_sparse := fullBacktrack_preserves_fullSparseW hsw_inv hbt_len hbt_w rfl rfl rfl rfl
        rfl hbt_pres.1
      have ⟨hkeep_v, hkeep_l⟩ := hbt_keep ⟨F0, F_cur, Or.inr hsw_inv_c.2.1⟩
      have hlow_on_bt : ∀ j, 1 ≤ j → j < s.core.tmp_len →
          ∃ idx < te_bt, (trl_bt[idx]?.getD 0#32).toNat = (s.core.tmp[j]?.getD 0#32).toNat ^^^ 1 ∧
            (lvl_bt[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
        intro j hj1 hj2
        have hjv := htmp_vals j hj2; have hjl := htmp_lvls j hj1 hj2
        have hle_ml : (s.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            max_lvl := by simpa only [max_lvl, hwm_get] using hjl.2.2
        have hle_nl : (s_sw.core.lvl[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            nlvl.toNat := by dsimp only [s_sw]; omega
        have hv_bt : vals_bt[(s.core.tmp[j]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
          rw [hkeep_v _ hjv.1, ite_eq_left hle_nl]; exact hjv.2
        have hl_bt : (lvl_bt[(s.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
          obtain ⟨i0, hi0, hi0_eq⟩ := (hsw_inv.2.1.vals_false_iff _ hjv.1).mp hjv.2
          have hdiv : (s_sw.core.trl[i0]?.getD 0#32).toNat / 2 =
              (s.core.tmp[j]?.getD 0#32).toNat / 2 := by rw [hi0_eq, fullInv_var_xor1]
          have hl_eq := hkeep_l i0 hi0
          rw [hdiv] at hl_eq; rw [hl_eq, ite_eq_left hle_nl]; exact hle_ml
        obtain ⟨idx, hidx, heq⟩ := (hbt_w.vals_false_iff _ hjv.1).mp hv_bt
        exact ⟨idx, hidx, heq, hl_bt⟩
      have hwm_on_bt : ∃ idx < te_bt,
          (trl_bt[idx]?.getD 0#32).toNat = wm.toNat ^^^ 1 ∧
          (lvl_bt[wm.toNat / 2]?.getD 0#32).toNat ≤ max_lvl := by
        simpa only [hwm_get] using hlow_on_bt (s.core.tmp_len - 1) (by omega) (by omega)
      clear hDnl hBt htmp_vals htmp_lvls hent hm_sw hm_sw' hm1 hm1' hbt_ss hbt_keep hbt_otfs
        hbt_te_le hbt_prop_le hnlvl_zero hnlvl_pos hkeep_v hkeep_l hbt_a1 hbt_a2
      let AddClPre : FullState → Prop := fun sg =>
        FullSparseInvW c F0 F_cur sg ∧ sg.core.cur_level = nlvl.toNat ∧
        sg.core.cur_vars = s.core.cur_vars ∧ sg.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        sg.core.tmp = tmp_sw ∧ sg.core.tmp_len = s.core.tmp_len ∧
        sg.core.vals = vals_bt ∧ sg.core.lvl = lvl_bt ∧ sg.core.trl = trl_bt ∧
        sg.core.trail_end = te_bt ∧ sg.scratch.work_stk2 = s.scratch.work_stk2
      let NrSpec : FullState → BitVec 64 → Prop := fun sac r_ac =>
        r_ac = 0xFFFFFFFF#64 ∨
        (r_ac ≠ 0xFFFFFFFF#64 ∧
          if r_ac = 0xFFFFFFFE#64 then
            (cnfOfClauses F_cur).EntailsClause (cnfClause [uip.toNat, wm.toNat])
          else
            r_ac.toNat < 2 ^ 31 - 1 ∧
            r_ac.toNat ∈ fullArenaClauseRefs sac ∧
            fullArenaClauseGarb sac r_ac.toNat = false ∧
            (∀ q ∈ fullArenaClauseLits sac r_ac.toNat,
              q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat) ∧
            uip.toNat ∈ fullArenaClauseLits sac r_ac.toNat)
      -- Pre-add GC headroom check (`arena_len + tmp_len + 8 > arena_cap || wcap - wlen < 32`)
      c0_to_group
      refine wp_join_group (ts := []) (fun () m_gc =>
          ∃ s_gc : FullState, AddClPre s_gc ∧ (FullMem c s_gc ⋆ R) m_gc) ?_ ?_
      · rintro _ ⟨⟩ m_gc ⟨s_gc, hgc_pre, hm_gc⟩
        clear hbt_sparse hbt_w hbt_len hm_bt hbt_pres hmi_t1 hsw_len hsw_inv hsw_inv_c hsw_iff
          hml_bv64 hbt_cl hcl_bt s_t1 s_sw s_bt sc_bt m_bt
        have htl_tr32 : ((BitVec.ofNat 64 s.core.tmp_len).setWidth 32).toNat = s.core.tmp_len := by
          rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : s.core.tmp_len < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
        -- Local helper packaging any `full_add_clause(h, (u32)h->tmp_len, (u32)glue, true)` call
        have hAddCall : ∀ (sg : FullState) (mg : Mem 64)
            (k : Tup Val [i64] → Expr Val Cont [i64]),
            AddClPre sg → (FullMem c sg ⋆ R) mg →
            (∀ new_ref64 s_ac m_ac,
              AddClPre s_ac → NrSpec s_ac new_ref64 → (FullMem c s_ac ⋆ R) m_ac →
              wp Γ Q X (k (new_ref64, ())) m_ac) →
            wp Γ Q X
              (Expr.call (as := [i64, i32, i32, .bool]) (bs := [i64]) (rs := [i64])
                "full_add_clause"
                (Arg.var c.hdr, Arg.var ((BitVec.ofNat 64 sg.core.tmp_len).setWidth 32),
                  Arg.var (glue.setWidth 32), Arg.imm true, ()) k) mg := by
          intro sg mg k hsg_pre hm_g hk
          obtain ⟨hsp, hcl_s, hcv_s, hfu_s, htmp_s, htl_s, hvals_s, hlvl_s, htrl_s, hte_s,
            hws2_s⟩ := hsg_pre
          have hlen_s := hsp.1
          refine wp_call_of_spec _ _ ?_
          dsimp only [Arg.val_var, vals]
          refine hAddCl _ _ _ _ ⟨c, F0, F_cur, sg, R, rfl, hlen_s, hsp.2.1, hsp.2.2.2.2.2,
            by rw [htl_s, htl_tr32]; omega,
            fun _ => by rw [htmp_s, htl_s, htl_tr32, hcv_s]; exact ⟨hsw_lits_lt, hsw_nd, hent_sw⟩,
            hm_g, ?_⟩
          rw [htl_s, htl_tr32]
          simp only [show ¬ s.core.tmp_len < 2 by omega, ↓reduceIte]
          by_cases htl2 : s.core.tmp_len = 2
          · simp only [htl2, ↓reduceIte]
            intro r_ac wvec_a wstk_a wlen_a wu_a nb_a wsort_a m_ac hr_ac hac_len hac_w hm_ac
            let s_ac : FullState :=
              { sg with
                core := { sg.core with
                  wvec := wvec_a, wstk := wstk_a, wlen := wlen_a, wusable := wu_a,
                  num_binary := nb_a }
                scratch := { sg.scratch with wsort := wsort_a } }
            have hac_sp : FullSparseInvW c F0 F_cur s_ac :=
              ⟨hac_len, hac_w, hsp.2.2.1, hsp.2.2.2.1,
                Full.FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r),
                hsp.2.2.2.2.2⟩
            have hnr : NrSpec s_ac r_ac := by
              rcases hr_ac with rfl | rfl
              · exact Or.inl rfl
              · right; refine ⟨by decide, ?_⟩; simp only [↓reduceIte]
                have hlen2_sw : 2 ≤ tmp_sw.length := by
                  simp only [tmp_sw, List.length_set, htmp_len_arr]; omega
                rw [htl2, v2r_tmp_take2_eq hlen2_sw hsw_0 hsw_1] at hent_sw
                exact hent_sw
            exact hk r_ac s_ac m_ac ⟨hac_sp, hcl_s, hcv_s, hfu_s, htmp_s, htl_s, hvals_s, hlvl_s,
              htrl_s, hte_s, hws2_s⟩ hnr hm_ac
          · simp only [htl2, ↓reduceIte]
            intro r_ac arena_a alen_a wvec_a wstk_a wlen_a wu_a fred_a ni_a nr_a wsort_a m_ac
              hr_ac hac_len hac_w hrefs_sub hnd_imp hok_a hm_ac
            let s_ac : FullState :=
              { sg with
                core := { sg.core with
                  arena := arena_a, arena_len := alen_a, wvec := wvec_a, wstk := wstk_a,
                  wlen := wlen_a, wusable := wu_a, first_reducible := fred_a, num_irred := ni_a,
                  num_redundant := nr_a }
                scratch := { sg.scratch with wsort := wsort_a } }
            have hac_sp : FullSparseInvW c F0 F_cur s_ac :=
              ⟨hac_len, hac_w, hsp.2.2.1, hnd_imp hsp.2.2.2.1,
                Full.FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ hrefs_sub,
                hsp.2.2.2.2.2⟩
            have hnr : NrSpec s_ac r_ac := by
              rcases hr_ac with rfl | rfl
              · exact Or.inl rfl
              · obtain ⟨_, href_a, hng_a, hlits_a⟩ := hok_a rfl
                have hal_lt31 : sg.core.arena_len < 2 ^ 31 - 1 := by
                  have := hlen_s.core_ok.arena_len_le; omega
                have hnr_toNat : (BitVec.ofNat 64 sg.core.arena_len).toNat = sg.core.arena_len :=
                  bv64_ofNat_toNat (by omega)
                have hne_ff : BitVec.ofNat 64 sg.core.arena_len ≠ 0xFFFFFFFF#64 := fun heq => by
                  have := congrArg BitVec.toNat heq; rw [hnr_toNat] at this
                  have : (0xFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 32 - 1 := rfl; omega
                have hne_fe : BitVec.ofNat 64 sg.core.arena_len ≠ 0xFFFFFFFE#64 := fun heq => by
                  have := congrArg BitVec.toNat heq; rw [hnr_toNat] at this
                  have : (0xFFFFFFFE#64 : BitVec 64).toNat = 2 ^ 32 - 2 := rfl; omega
                right; refine ⟨hne_ff, ?_⟩; simp only [hne_fe, ↓reduceIte, hnr_toNat]
                have hlits_eq : fullArenaClauseLits s_ac sg.core.arena_len =
                    (tmp_sw.take s.core.tmp_len).map BitVec.toNat := by
                  change fullArenaClauseLits s_ac sg.core.arena_len =
                    (sg.core.tmp.take s.core.tmp_len).map BitVec.toNat at hlits_a
                  rwa [htmp_s] at hlits_a
                refine ⟨hal_lt31, href_a, hng_a, fun q hq => by rwa [hlits_eq] at hq, ?_⟩
                rw [hlits_eq, List.mem_map]
                have h0_sw : 0 < tmp_sw.length := by simp [tmp_sw, htmp_len_arr]; omega
                have hu_sw : tmp_sw[0]'h0_sw = uip := by
                  have := List.getElem?_eq_getElem h0_sw; rw [hsw_0] at this
                  exact (Option.some.inj this).symm
                exact ⟨uip, List.mem_iff_getElem.mpr ⟨0, by rw [List.length_take]; omega,
                  by rw [List.getElem_take]; exact hu_sw⟩, rfl⟩
            exact hk r_ac s_ac m_ac ⟨hac_sp, hcl_s, hcv_s, hfu_s, htmp_s, htl_s, hvals_s, hlvl_s,
              htrl_s, hte_s, hws2_s⟩ hnr hm_ac
        let AddClPre := V2rAddClPre c F0 F_cur s nlvl tmp_sw vals_bt lvl_bt trl_bt te_bt
        let NrSpec := V2rNrSpec F_cur s uip wm tmp_sw
        -- First `full_add_clause` call before retry loop:
        c0_to_group
        refine hAddCall s_gc m_gc _ hgc_pre hm_gc fun new_ref0 s_ac0 m_ac0 h0_pre h0_nr hm_ac0 => ?_
        have hlow_bt : ∀ q ∈ (tmp_sw.take s.core.tmp_len).map BitVec.toNat,
            q = uip.toNat ∨ ∃ idx < te_bt,
              (trl_bt[idx]?.getD 0#32).toNat = q ^^^ 1 ∧
              (lvl_bt[q / 2]?.getD 0#32).toNat ≤ max_lvl := fun q hq => by
          rcases hsw_mem q hq with rfl | ⟨j, hj1, hj2, hjeq⟩
          · exact Or.inl rfl
          · right; rw [← hjeq]; exact hlow_on_bt j hj1 hj2
        clear hAddCl hsw_mem hlow_on_bt s_gc hgc_pre hm_gc
        c0_to_group
        refine wp_loop_inv
          (fun (new_ref64, step, ()) mL =>
            step.toNat ≤ 3 ∧
            ∃ s_lp : FullState, AddClPre s_lp ∧ NrSpec s_lp new_ref64 ∧ (FullMem c s_lp ⋆ R) mL)
          (fun (_, step, ()) _ => 3 - step.toNat)
          (fun JL hLoop =>
            hLoop (new_ref0, 0#64, ()) m_ac0 ⟨Nat.zero_le _, s_ac0, h0_pre, h0_nr, hm_ac0⟩)
          (fun JL (new_ref64, step, ()) mL ⟨hstep_le, s_lp, hlp_pre, hlp_nr, hmL⟩ hLoop => ?_)
        refine wp_join_group (ts := [])
          (fun () m_ex => ∃ s_ex, AddClPre s_ex ∧ NrSpec s_ex new_ref64 ∧ (FullMem c s_ex ⋆ R) m_ex)
          ?_ ?_
        · rintro _ ⟨⟩ m_ex ⟨s_ex, hex_pre, hex_nr, hm_ex⟩
          simp only [Blocks.get]
          exact v2r_learn_clause_post_ac_wp (c := c) (F0 := F0) (F_cur := F_cur) (s := s)
            (s_ac := s_ex) (R := R) (uip_lit := uip) (wm := wm) (new_ref64 := new_ref64)
            (max_lvl := max_lvl) (tmp_sw := tmp_sw) hAsgn hEsub hQ
            hex_pre.1 (by rw [hex_pre.2.1]; exact hnlvl_lt) hml_pos
            (by rw [hex_pre.2.1]; omega) (by omega) hex_pre.2.2.1 hex_pre.2.2.2.1
            hex_pre.2.2.2.2.2.2.2.2.2.2 hex_pre.2.2.2.2.1 hex_pre.2.2.2.2.2.1 hsw_1 htl_ge2
            htl_cv huip_lt hwm_lt htmp_sw_lt
            (by rw [hex_pre.2.2.2.2.2.2.2.2.1, hex_pre.2.2.2.2.2.2.2.1,
                  hex_pre.2.2.2.2.2.2.2.2.2.1]; exact hwm_on_bt)
            (by rw [hex_pre.2.2.2.2.2.2.2.2.1, hex_pre.2.2.2.2.2.2.2.1,
                  hex_pre.2.2.2.2.2.2.2.2.2.1]; exact hlow_bt)
            hex_nr hm_ex
        · intro J_post hJ_post
          clear hAsgn hEsub hsw_1 hwm_on_bt hlow_bt
          c0_split
          · c0_split
            · have hstep_lt : step.toNat < 3 := by c0_bound
              have hstep1 : (step + 1#64).toNat = step.toNat + 1 := by c0_bound
              c0_to_group
              refine wp_join_group (ts := [])
                (fun () m_pre => ∃ s_pre : FullState, AddClPre s_pre ∧ (FullMem c s_pre ⋆ R) m_pre)
                ?_ ?_
              · rintro _ ⟨⟩ m_pre ⟨s_pre, hpre_ok, hm_pre⟩
                c0_steps
                refine hAddCall s_pre m_pre _ hpre_ok hm_pre
                  fun nr' sac' mac' hsac' hnr' hmac' => ?_
                c0_steps
                exact hLoop (nr', step + 1#64, ()) mac' (by dsimp only; rw [hstep1]; omega)
                  ⟨by omega, sac', hsac', hnr', hmac'⟩
              · intro J1 hJ1
                c0_split
                · c0_to_group
                  refine wp_join_group (ts := [])
                    (fun () m_d => ∃ s_d : FullState, AddClPre s_d ∧ (FullMem c s_d ⋆ R) m_d)
                    ?_ ?_
                  · rintro _ ⟨⟩ m_d ⟨s_d, hd_pre, hm_d⟩
                    c0_steps; exact hJ1 () m_d ⟨s_d, hd_pre, hm_d⟩
                  · intro Jd hJd
                    have ⟨hlp_sp, hlp_cl, hlp_cv, hlp_fu, hlp_tmp, hlp_tl, hlp_vals, hlp_lvl,
                      hlp_trl, hlp_te, hlp_ws2⟩ := hlp_pre
                    c0_split
                    · have hlp_lay : WatchStackLayout s_lp.core := by
                        have hm_w := hlp_sp.2.1.watches
                        unfold ModeWatchesInv at hm_w
                        rw [ite_eq_left hlp_sp.2.2.2.2.2] at hm_w
                        exact hm_w.layout
                      c0_call hDefrag
                      refine ⟨c, s_lp, R, rfl, hlp_sp.1, hlp_lay, hmL, ?_⟩
                      intro wvec_d wstk_d wlen_d wsort_d m_d _ hd_len hd_lay _ hd_pres hm_d
                      let s_d : FullState :=
                        { s_lp with
                          core := { s_lp.core with
                            wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
                          scratch := { s_lp.scratch with wsort := wsort_d } }
                      have hd_sp :=
                        fullWstackDefrag_preserves_fullSparseW hlp_sp hd_len hd_lay hd_pres
                      c0_steps
                      exact hJd () m_d ⟨s_d, ⟨hd_sp, hlp_cl, hlp_cv, hlp_fu, hlp_tmp, hlp_tl,
                        hlp_vals, hlp_lvl, hlp_trl, hlp_te, hlp_ws2⟩, hm_d⟩
                    · have hwuz : s_lp.core.wusable = 0#64 := by
                        apply BitVec.eq_of_toNat_eq; bv_omega
                      c0_steps
                      exact hJd () mL ⟨s_lp, hlp_pre, by simpa only [hwuz] using hmL⟩
                · c0_to_group
                  refine wp_join_group (ts := [i64])
                    (fun (gr, ()) m_r => ∃ s_r : FullState,
                      FullSparseInvW c F0 F_cur s_r ∧ (gr = 0#64 ∨ gr = 1#64 ∨ gr = 20#64) ∧
                      s_r.core.cur_level ≤ s_lp.core.cur_level ∧
                      s_r.core.fuel.toNat ≤ s_lp.core.fuel.toNat ∧
                      s_r.core.cur_vars = s_lp.core.cur_vars ∧
                      s_r.core.tmp = s_lp.core.tmp ∧ s_r.core.tmp_len = s_lp.core.tmp_len ∧
                      s_r.scratch.work_stk2 = s_lp.scratch.work_stk2 ∧
                      (gr = 20#64 → F0.Unsat) ∧
                      (gr = 1#64 → 0 < s_r.core.cur_level →
                        s_r.core.cur_level = s_lp.core.cur_level ∧ s_r.core.vals = s_lp.core.vals ∧
                        s_r.core.lvl = s_lp.core.lvl ∧ s_r.core.trl = s_lp.core.trl ∧
                        s_r.core.trail_pos = s_lp.core.trail_pos ∧
                        s_r.core.trail_end = s_lp.core.trail_end) ∧
                      (FullMem c s_r ⋆ R) m_r)
                    ?_ ?_
                  · rintro _ ⟨gr, ⟨⟩⟩ m_r ⟨s_r, hr_sp, hr_dom, hr_cl, hr_fu, hr_cv, hr_tmp, hr_tl,
                      hr_ws2, hr_20, hr_pos, hm_r⟩
                    have ⟨hlp_sp, hlp_cl, hlp_cv, hlp_fu, hlp_tmp, hlp_tl, hlp_vals, hlp_lvl,
                      hlp_trl, hlp_te, hlp_ws2⟩ := hlp_pre
                    have hr_cv' : s_r.core.cur_vars = s.core.cur_vars := hr_cv.trans hlp_cv
                    have hr_fu' : s_r.core.fuel.toNat ≤ s.core.fuel.toNat :=
                      Nat.le_trans hr_fu hlp_fu
                    have hr_ws2' : s_r.scratch.work_stk2 = s.scratch.work_stk2 :=
                      hr_ws2.trans hlp_ws2
                    clear hlp_pre hlp_sp hlp_cv hlp_fu hlp_ws2
                    c0_hsplit
                    · c0_hsteps
                      exact hQ 20#64 s_r m_r hr_sp.1 (Or.inr (Or.inr rfl)) hr_cv' hr_fu' hr_ws2'
                        (fun _ => ⟨hr_20 (by simpa [bv_c0] using hc), hr_sp, by omega⟩)
                        (fun h => by cases h) (fun h => by cases h) hm_r
                    · c0_hsplit
                      · c0_hsteps
                        exact hQ 0#64 s_r m_r hr_sp.1 (Or.inl rfl) hr_cv' hr_fu' hr_ws2'
                          (fun h => by cases h) (fun _ => hr_sp) (fun h => by cases h) hm_r
                      · have hgr1 : gr = 1#64 := by
                          rcases hr_dom with rfl | rfl | rfl
                          · exfalso; simp [bv_c0] at hc
                          · rfl
                          · exfalso; simp [bv_c0] at hc
                        c0_hsplit
                        · c0_hsteps
                          exact hQ 1#64 s_r m_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv' hr_fu' hr_ws2'
                            (fun h => by cases h) (fun h => by cases h)
                            (fun _ => ⟨hr_sp, by omega⟩) hm_r
                        · have hcl_eq : s_r.core.cur_level = nlvl.toNat := by
                            have hbv : BitVec.ofNat 64 s_r.core.cur_level = nlvl := by
                              simpa [bv_c0] using hc
                            have hsr_lt64 : s_r.core.cur_level < 2 ^ 64 := by
                              have := hr_sp.1.core_ok.cur_vars_le
                              have := hr_sp.2.1.cur_level_le
                              have := hr_sp.1.core_ok.trail_end_le; omega
                            have := congrArg BitVec.toNat hbv
                            rw [bv64_ofNat_toNat hsr_lt64] at this; exact this
                          have huip_r_lt : (BitVec.setWidth 64 (s.core.tmp[0]'huip_in)).toNat <
                              s_r.core.vals.length := by
                            rw [bv32_setWidth64_toNat, hr_sp.1.core_ok.vals_len]
                            change uip.toNat < 2 * c.max_vars; omega
                          c0_hsplit
                          · c0_hsteps
                            exact hQ 1#64 s_r m_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv' hr_fu'
                              hr_ws2' (fun h => by cases h) (fun h => by cases h)
                              (fun _ => ⟨hr_sp, by omega⟩) hm_r
                          · obtain ⟨_, hr_vals, hr_lvl, hr_trl, _, hr_te⟩ :=
                              hr_pos hgr1 (by omega)
                            c0_hsteps
                            exact hJ1 () m_r ⟨s_r, ⟨hr_sp, hcl_eq, hr_cv', hr_fu',
                              hr_tmp.trans hlp_tmp, hr_tl.trans hlp_tl, hr_vals.trans hlp_vals,
                              hr_lvl.trans hlp_lvl, hr_trl.trans hlp_trl, hr_te.trans hlp_te,
                              hr_ws2'⟩, hm_r⟩
                  · intro Jr hJr
                    c0_split
                    · c0_call hRed
                      refine ⟨c, F0, F_cur, s_lp, R, rfl, hlp_pre.1, hmL, ?_⟩
                      intro rr s_r m_r hr_sp hr_dom hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
                        hr_20 _ hr_pos hm_r
                      c0_steps
                      exact hJr (rr, ()) m_r
                        ⟨s_r, hr_sp, hr_dom, hr_cl, hr_fu, hr_cv, hr_tmp, hr_tl,
                          hr_ws2, hr_20, hr_pos, hm_r⟩
                    · c0_call hRedPurge
                      refine ⟨c, F0, F_cur, s_lp, R, rfl, hlp_pre.1, hmL, ?_⟩
                      intro rr s_r m_r hr_sp hr_dom hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
                        hr_20 _ hr_pos hm_r
                      c0_steps
                      exact hJr (rr, ()) m_r
                        ⟨s_r, hr_sp, hr_dom, hr_cl, hr_fu, hr_cv, hr_tmp, hr_tl,
                          hr_ws2, hr_20, hr_pos, hm_r⟩
            · c0_hsteps; exact hJ_post () mL ⟨s_lp, hlp_pre, hlp_nr, hmL⟩
          · c0_hsteps; exact hJ_post () mL ⟨s_lp, hlp_pre, hlp_nr, hmL⟩
      · -- Pre-add GC headroom `if` body
        clear hAddCl hAsgn hEsub hent_sw hsw_lits_lt hlow_on_bt hwm_on_bt htmp_sw_lt
          hRedPurge
        intro Jgc hJgc
        c0_to_group
        refine wp_join_group (ts := []) (fun () m_in => m_in = m_bt) ?_ ?_
        · rintro _ ⟨⟩ m_in rfl
          c0_to_group
          refine wp_join_group (ts := []) (fun () m_d => ∃ wvec_d wstk_d wlen_d wsort_d,
              let s_d : FullState :=
                { s_bt with
                  core := { s_bt.core with
                    wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
                  scratch := { sc_bt with wsort := wsort_d } }
              FullSparseInvW c F0 F_cur s_d ∧ (FullMem c s_d ⋆ R) m_d) ?_ ?_
          · rintro _ ⟨⟩ m_d ⟨wvec_d, wstk_d, wlen_d, wsort_d, hd_sp, hm_d⟩
            let s_d : FullState :=
              { s_bt with
                core := { s_bt.core with
                  wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
                scratch := { sc_bt with wsort := wsort_d } }
            have hd_cl : s_d.core.cur_level = nlvl.toNat := hcl_bt
            c0_to_group
            refine wp_join_group (ts := []) (fun () m_3 =>
                ∃ s_3 : FullState, AddClPre s_3 ∧ (FullMem c s_3 ⋆ R) m_3) ?_ ?_
            · rintro _ ⟨⟩ m_3 ⟨s_3, h3_pre, hm_3⟩
              c0_steps; exact hJgc () m_3 ⟨s_3, h3_pre, hm_3⟩
            · intro J3 hJ3; c0_split
              · c0_to_group; c0_call hRed
                refine ⟨c, F0, F_cur, s_d, R, rfl, hd_sp, hm_d, ?_⟩
                intro rr s_r m_r hr_sp hr_dom hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
                  hr_20 _ hr_pos hm_r
                dsimp only [s_d, s_bt, s_sw] at hr_cl hr_fu hr_cv hr_tmp hr_tl hr_ws2
                dsimp only [s_d] at hr_pos
                have hr_ws2' : s_r.scratch.work_stk2 = s.scratch.work_stk2 :=
                  hr_ws2.trans hbt_pres.2.2.1
                c0_hsplit
                · c0_hsteps
                  exact hQ 20#64 s_r m_r hr_sp.1 (Or.inr (Or.inr rfl)) hr_cv hr_fu hr_ws2'
                    (fun _ => ⟨hr_20 (by simpa [bv_c0] using hc), hr_sp, by omega⟩)
                    (fun h => by cases h) (fun h => by cases h) hm_r
                · c0_hsplit
                  · c0_hsteps
                    exact hQ 0#64 s_r m_r hr_sp.1 (Or.inl rfl) hr_cv hr_fu hr_ws2'
                      (fun h => by cases h) (fun _ => hr_sp) (fun h => by cases h) hm_r
                  · have hrr1 : rr = 1#64 := by
                      rcases hr_dom with rfl | rfl | rfl
                      · exfalso; simp [bv_c0] at hc
                      · rfl
                      · exfalso; simp [bv_c0] at hc
                    c0_hsplit
                    · c0_hsteps
                      exact hQ 1#64 s_r m_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv hr_fu hr_ws2'
                        (fun h => by cases h) (fun h => by cases h)
                        (fun _ => ⟨hr_sp, by omega⟩) hm_r
                    · have hcl_eq : s_r.core.cur_level = nlvl.toNat := by
                        have hbv : BitVec.ofNat 64 s_r.core.cur_level = nlvl := by
                          simpa [bv_c0] using hc
                        have hsr_lt64 : s_r.core.cur_level < 2 ^ 64 := by
                          have := hr_sp.1.core_ok.cur_vars_le
                          have := hr_sp.2.1.cur_level_le
                          have := hr_sp.1.core_ok.trail_end_le; omega
                        have := congrArg BitVec.toNat hbv
                        rw [bv64_ofNat_toNat hsr_lt64] at this; exact this
                      have huip_r_lt : (BitVec.setWidth 64 (s.core.tmp[0]'huip_in)).toNat <
                          s_r.core.vals.length := by
                        rw [bv32_setWidth64_toNat, hr_sp.1.core_ok.vals_len]
                        change uip.toNat < 2 * c.max_vars; omega
                      c0_hsplit
                      · c0_hsteps
                        exact hQ 1#64 s_r m_r hr_sp.1 (Or.inr (Or.inl rfl)) hr_cv hr_fu hr_ws2'
                          (fun h => by cases h) (fun h => by cases h)
                          (fun _ => ⟨hr_sp, by omega⟩) hm_r
                      · obtain ⟨_, hr_vals, hr_lvl, hr_trl, _, hr_te⟩ :=
                          hr_pos hrr1 (by omega)
                        c0_hsteps
                        exact hJ3 () m_r ⟨s_r, ⟨hr_sp, hcl_eq, hr_cv, hr_fu, hr_tmp, hr_tl,
                          hr_vals, hr_lvl, hr_trl, hr_te, hr_ws2'⟩, hm_r⟩
              · c0_steps
                exact hJ3 () m_d ⟨s_d, ⟨hd_sp, hd_cl, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl,
                  rfl, hbt_pres.2.2.1⟩, hm_d⟩
          · intro Jdef hJdef; c0_split
            · have hbt_lay : WatchStackLayout s_bt.core := by
                have hm_w := hbt_sparse.2.1.watches
                unfold ModeWatchesInv at hm_w
                rw [ite_eq_left hbt_sparse.2.2.2.2.2] at hm_w
                exact hm_w.layout
              c0_call hDefrag
              refine ⟨c, s_bt, R, rfl, hbt_len, hbt_lay, hm_bt, ?_⟩
              intro wvec_d wstk_d wlen_d wsort_d m_d _ hd_len hd_lay _ hd_pres hm_d
              let s_d : FullState :=
                { s_bt with
                  core := { s_bt.core with
                    wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := 0#64 }
                  scratch := { sc_bt with wsort := wsort_d } }
              have hd_sp := fullWstackDefrag_preserves_fullSparseW hbt_sparse hd_len hd_lay hd_pres
              c0_steps
              exact hJdef () m_d ⟨wvec_d, wstk_d, wlen_d, wsort_d, hd_sp, hm_d⟩
            · have hwuz : s.core.wusable = 0#64 := by
                dsimp only [s_bt, s_sw] at *; apply BitVec.eq_of_toNat_eq; bv_omega
              c0_steps
              refine hJdef () m_in ⟨s_bt.core.wvec, s_bt.core.wstk, s_bt.core.wlen, sc_bt.wsort, ?_,
                ?_⟩
              · simpa only [s_bt, s_sw, hwuz] using v2r_laSparse_to_canon hbt_sparse
              · simpa only [s_bt, s_sw, hwuz] using hm_bt
        · intro J_in hJ_in; c0_split
          · c0_steps; exact hJ_in () m_bt rfl
          · c0_split
            · c0_steps; exact hJ_in () m_bt rfl
            · c0_steps
              exact hJgc () m_bt ⟨s_bt, ⟨v2r_laSparse_to_canon hbt_sparse, hcl_bt, rfl,
                Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, hbt_pres.2.2.1⟩, hm_bt⟩
    · intro Jml hJml; c0_split
      c0_steps
      have hml_set : BitVec.setWidth 64
          (s.core.lvl[((s.core.tmp[(BitVec.ofNat 64 s.core.tmp_len - 1#64).toNat]'hmi_tmp >>>
            1#32).setWidth 64).toNat]'hmi_lvl) = BitVec.ofNat 64 max_lvl := by
        apply BitVec.eq_of_toNat_eq
        rw [bv32_setWidth64_toNat, hml_get, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hml_set]
      exact hJml (BitVec.ofNat 64 max_lvl, ()) m ⟨rfl, rfl⟩

end LearnClauseProof

end LeanQbe.T.Examples.Kissat.FullM7V2Robust
