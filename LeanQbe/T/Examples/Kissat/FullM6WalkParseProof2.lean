module

public import LeanQbe.T.Examples.Kissat.FullM6WalkParseProof1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 Wave 2 (`RC-26b` + `RC-27`) `Func.wp` Proofs — Part 2 (`FullM6WalkParseProof2`)

Proves UNSAT-only parametric `Func.wp` contracts (`XPost := False`, `0` SAT proofs) for the
ProbSAT CSR collection and construction helpers:
1. `m6WalkCollectSpec` and `full_walk_collect_m6_wp`.
2. `m6WalkBuildCsrSpec` and `full_walk_build_csr_m6_wp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6WalkParse

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Specs & Shared CSR / `FullWalkEntriesOk` Helpers -/

/-- Contract for `full_walk_collect_m6(h, max_cl, occ_cap) -> ncl`. -/
def m6WalkCollectSpec : Spec [i64, i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, max_cl, occ_cap, ()) s =>
      h = c.hdr ∧ (∃ F0, FullCoreInv c F0 s) ∧ 5 * max_cl.toNat + occ_cap.toNat ≤ c.scratch_cap)
    (fun _ (_, max_cl, _, ()) (r, ()) s s' =>
      FullExtScratchPres s s' ∧ r.toNat ≤ max_cl.toNat ∧ FullWalkEntriesOk s' r.toNat)

/-- Contract for `full_walk_build_csr_m6(h, ncl, max_cl, occ_cap) -> ulen`. -/
def m6WalkBuildCsrSpec : Spec [i64, i64, i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ncl, max_cl, occ_cap, ()) s =>
      h = c.hdr ∧ (∃ F0, FullCoreInv c F0 s) ∧ ncl.toNat ≤ max_cl.toNat ∧
      5 * max_cl.toNat + occ_cap.toNat ≤ c.scratch_cap ∧ FullWalkEntriesOk s ncl.toNat)
    (fun _ (_, ncl, _, _, ()) (r, ()) s s' =>
      FullExtScratchPres s s' ∧ r.toNat ≤ ncl.toNat ∧ FullWalkEntriesOk s' ncl.toNat)

theorem m6_walkEntriesOk_of_scr_eq {s1 s2 : FullState} {n : Nat}
    (hok : FullWalkEntriesOk s1 n) (hcore : s2.core = s1.core)
    (hscr : ∀ i < 2 * n, s2.scratch.scratch_buf[i]? = s1.scratch.scratch_buf[i]?) :
    FullWalkEntriesOk s2 n := by
  intro idx hidx
  have h0 := hok idx hidx
  unfold FullWalkEntryOk at h0 ⊢
  dsimp only [fullArenaClauseRefs, fullArenaClauseRefsCore,
    fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore] at h0 ⊢
  rw [hcore, hscr (2 * idx) (by omega), hscr (2 * idx + 1) (by omega)]
  exact h0

theorem m6_walkEntriesOk_set_hi {s : FullState} {n idx : Nat} {val : BitVec 32}
    (hok : FullWalkEntriesOk s n) (hhi : 2 * n ≤ idx) :
    FullWalkEntriesOk
      { s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set idx val } }
      n :=
  m6_walkEntriesOk_of_scr_eq hok rfl fun i hi => List.getElem?_set_ne (by omega)

theorem m6_walkEntriesOk_with_scratch {s : FullState} {n : Nat} {sc' : FullScratch}
    (hok : FullWalkEntriesOk s n) (hscr : sc'.scratch_buf = s.scratch.scratch_buf) :
    FullWalkEntriesOk { core := s.core, scratch := sc' } n :=
  m6_walkEntriesOk_of_scr_eq hok rfl fun i _ => by rw [hscr]

theorem m6_walkEntriesOk_set_hi_upd {s s' : FullState} {n idx : Nat} {val : BitVec 32}
    (hok : FullWalkEntriesOk s n) (hcore : s'.core = s.core)
    (hscr : s'.scratch.scratch_buf = s.scratch.scratch_buf.set idx val)
    (hhi : 2 * n ≤ idx) : FullWalkEntriesOk s' n :=
  m6_walkEntriesOk_of_scr_eq hok hcore fun i hi => by
    rw [hscr, List.getElem?_set_ne (by omega)]

theorem m6_walkEntriesOk_push_bin {s : FullState} {n : Nat}
    (hok : FullWalkEntriesOk s n) (hl : s.core.cur_vars < 2 * dimacsBound)
    {l ot : Nat} (hl_lt : l < 2 * s.core.cur_vars) (hot_lt : ot < 2 * s.core.cur_vars)
    (hlen_bd : 2 * n + 1 < s.scratch.scratch_buf.length) :
    let l32 := BitVec.ofNat 32 l ||| 0x80000000#32
    let ot32 := BitVec.ofNat 32 ot
    let buf' := (s.scratch.scratch_buf.set (2 * n) l32).set (2 * n + 1) ot32
    FullWalkEntriesOk { s with scratch := { s.scratch with scratch_buf := buf' } } (n + 1) := by
  intro l32 ot32 buf' idx hidx
  have hdim : 2 * dimacsBound < 2 ^ 30 := by unfold dimacsBound; decide
  have hl32_eq : l32 &&& 0x7FFFFFFF#32 = BitVec.ofNat 32 l := by
    dsimp only [l32]
    rw [BitVec.and_or_distrib_right,
      show (0x80000000#32 &&& 0x7FFFFFFF#32 : BitVec 32) = 0#32 by decide, BitVec.or_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hflag : (l32 &&& 0x80000000#32) ≠ 0#32 := by
    dsimp only [l32]
    intro heq
    have hbit := congrArg (fun x : BitVec 32 => x.toNat.testBit 31) heq
    simp only [BitVec.toNat_and, BitVec.toNat_or, Nat.testBit_and, Nat.testBit_or,
      show (0x80000000#32 : BitVec 32).toNat = 2 ^ 31 from rfl, Nat.testBit_two_pow_self,
      Bool.or_true, Bool.and_true, BitVec.toNat_zero, Nat.zero_testBit] at hbit
    cases hbit
  unfold FullWalkEntryOk; dsimp only
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hidx) with hlt | rfl
  · have := hok idx hlt; unfold FullWalkEntryOk at this
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact this
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
      List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some, Option.getD_some]
    have hl_to : (BitVec.ofNat 32 l).toNat = l := bv32_ofNat_toNat (by omega)
    have hot_to : ot32.toNat = ot := bv32_ofNat_toNat (by omega)
    split
    · rw [hl32_eq, hl_to, hot_to]; exact ⟨hl_lt, hot_lt⟩
    · exact absurd hflag (by assumption)

theorem m6_walkEntriesOk_push_large {s : FullState} {n : Nat}
    (hok : FullWalkEntriesOk s n) {p : Nat} (hp_ref : p ∈ fullArenaClauseRefs s)
    (hp_ng : fullArenaClauseGarb s p = false) (hp_bd : p < 2 ^ 31)
    (hlen_bd : 2 * n + 1 < s.scratch.scratch_buf.length) :
    let p32 := BitVec.ofNat 32 p
    let buf' := (s.scratch.scratch_buf.set (2 * n) p32).set (2 * n + 1) 0#32
    FullWalkEntriesOk { s with scratch := { s.scratch with scratch_buf := buf' } } (n + 1) := by
  intro p32 buf' idx hidx
  have hflag : (p32 &&& 0x80000000#32) = 0#32 := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    rw [BitVec.getElem_and, BitVec.getElem_zero, BitVec.getElem_eq_testBit_toNat,
      BitVec.getElem_eq_testBit_toNat]
    by_cases hi31 : i = 31
    · subst hi31
      rw [show p32.toNat = p from bv32_ofNat_toNat (by omega),
        Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hp_bd]; rfl
    · have h0 : (0x80000000#32 : BitVec 32).toNat.testBit i = false := by
        rw [show (0x80000000#32 : BitVec 32).toNat = 2 ^ 31 from rfl, Nat.testBit_two_pow]
        have hne : 31 ≠ i := Ne.symm hi31; simp [hne]
      rw [h0, Bool.and_false]
  unfold FullWalkEntryOk; dsimp only
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hidx) with hlt | rfl
  · have := hok idx hlt; unfold FullWalkEntryOk at this
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact this
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
      List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
    have hp_to : p32.toNat = p := bv32_ofNat_toNat (by omega)
    simp only [hflag, ne_eq, not_true_eq_false, ↓reduceIte, hp_to]
    exact ⟨hp_ref, hp_ng⟩

private theorem m6_arenaScanRefs_next {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, r ∈ fullArenaScanRefs ar alen pos fuel →
      (∀ q ∈ fullArenaScanRefs ar alen pos fuel,
        q + 3 ≤ alen ∧ fullArenaNextOff ar alen q ≤ alen ∧
        (fullArenaNextOff ar alen q = alen ∨ fullArenaNextOff ar alen q + 3 ≤ alen)) →
      alen - pos ≤ fuel →
      fullArenaNextOff ar alen r = alen ∨
      fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, h, _, _ => by simp [fullArenaScanRefs] at h
  | fuel + 1, pos, r, hr, hchain, hfl => by
    unfold fullArenaScanRefs at hr hchain ⊢
    split at hr
    · rename_i hle
      simp only [hle, ↓reduceIte]
      have hq := hchain pos (by simp [hle])
      have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases List.mem_cons.mp hr with rfl | hrest
      · rcases hq.2.2 with heq | hmore
        · exact Or.inl heq
        · right; apply List.mem_cons_of_mem
          cases fuel with
          | zero => omega
          | succ f' => unfold fullArenaScanRefs; simp [hmore]
      · rcases m6_arenaScanRefs_next hrest
          (fun q hqm => hchain q (by simp [hle, hqm])) (by omega) with heq | hm
        · exact Or.inl heq
        · exact Or.inr (List.mem_cons_of_mem _ hm)
    · simp at hr

private theorem m6_arenaClauseRefs_next {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
    fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k :=
  m6_arenaScanRefs_next hr (fun q hq => by
    have hwf := ha.refs_wf q hq; exact ⟨hwf.1, hwf.2.2.2.1, hwf.2.2.2.2⟩) (by omega)

private theorem m6_zero_mem_arenaClauseRefsCore {k : FullCoreState} (h3 : 3 ≤ k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  unfold fullArenaClauseRefsCore
  obtain ⟨f, hf⟩ : ∃ f, k.arena_len = f + 1 := ⟨k.arena_len - 1, by omega⟩
  rw [hf]; unfold fullArenaScanRefs
  have hle : 0 + 3 ≤ f + 1 := by omega
  simp [hle]

private theorem m6_watchSlice_step {F_cur : List (List Nat)} {k : FullCoreState} {l p rem : Nat}
    (hdm : k.dense_mode = 0#64 → WatchSliceOk F_cur k l p rem)
    (hdns : k.dense_mode ≠ 0#64 → DenseWatchSliceOk F_cur k l p rem)
    (hpos : 0 < rem) :
    ∃ w0, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 →
        (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧ 1 ≤ rem ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k l (p + 1) (rem - 1)
         else DenseWatchSliceOk F_cur k l (p + 1) (rem - 1))) ∧
      ((w0 &&& 0x80000000#32) = 0#32 →
        2 ≤ rem ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k l (p + 2) (rem - 2)
         else DenseWatchSliceOk F_cur k l (p + 2) (rem - 2))) := by
  by_cases hc : k.dense_mode = 0#64
  · cases hs : hdm hc with
    | empty => omega
    | bin hp hf _ hlt _ hrest =>
      refine ⟨_, hp, fun _ => ⟨hlt, by omega, by simpa [hc] using hrest⟩,
        fun h0 => absurd h0 hf⟩
    | large hp _ hf _ _ hrest =>
      refine ⟨_, hp, fun hne => absurd hf hne,
        fun _ => ⟨by omega, by simpa [hc] using hrest⟩⟩
  · cases hs : hdns hc with
    | empty => omega
    | bin hp hf _ hlt _ hrest =>
      refine ⟨_, hp, fun _ => ⟨hlt, by omega, by simpa [hc] using hrest⟩,
        fun h0 => absurd h0 hf⟩
    | occ hp _ hf _ _ _ hrest =>
      refine ⟨_, hp, fun hne => absurd hf hne,
        fun _ => ⟨by omega, by simpa [hc] using hrest⟩⟩

theorem m6_len_set_sb {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (hs : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with
      scratch_buf := s.scratch.scratch_buf.set i v } }).LengthsOk c :=
  hs.with_scratch { hs.scratch_ok with
    scratch_buf_len := by rw [List.length_set]; exact hs.scratch_ok.scratch_buf_len }

theorem m6_len_set_w2 {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (hs : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with
      work_stk2 := s.scratch.work_stk2.set i v } }).LengthsOk c :=
  hs.with_scratch { hs.scratch_ok with
    work_stk2_len := by rw [List.length_set]; exact hs.scratch_ok.work_stk2_len }

theorem m6_len_set_w1 {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (hs : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with
      work_stk1 := s.scratch.work_stk1.set i v } }).LengthsOk c :=
  hs.with_scratch { hs.scratch_ok with
    work_stk1_len := by rw [List.length_set]; exact hs.scratch_ok.work_stk1_len }

theorem m6_len_set_tm {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (hs : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with
      tarjan_mark := s.scratch.tarjan_mark.set i v } }).LengthsOk c :=
  hs.with_scratch { hs.scratch_ok with
    tarjan_mark_len := by rw [List.length_set]; exact hs.scratch_ok.tarjan_mark_len }

theorem m6_len_set_tr {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (hs : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with
      tarjan_reach := s.scratch.tarjan_reach.set i v } }).LengthsOk c :=
  hs.with_scratch { hs.scratch_ok with
    tarjan_reach_len := by rw [List.length_set]; exact hs.scratch_ok.tarjan_reach_len }

theorem m6_len_set_wv {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 8}
    (hs : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with
      walk_vals := s.scratch.walk_vals.set i v } }).LengthsOk c :=
  hs.with_scratch { hs.scratch_ok with
    walk_vals_len := by rw [List.length_set]; exact hs.scratch_ok.walk_vals_len }

theorem m6_len_set_wb {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 8}
    (hs : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with
      walk_best := s.scratch.walk_best.set i v } }).LengthsOk c :=
  hs.with_scratch { hs.scratch_ok with
    walk_best_len := by rw [List.length_set]; exact hs.scratch_ok.walk_best_len }

theorem m6_len_set_ph {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 8}
    (hs : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with
      phases := s.scratch.phases.set i v } }).LengthsOk c :=
  hs.with_scratch { hs.scratch_ok with
    phases_len := by rw [List.length_set]; exact hs.scratch_ok.phases_len }

theorem m6_len_set_pt {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 8}
    (hs : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with
      phases_target := s.scratch.phases_target.set i v } }).LengthsOk c :=
  hs.with_scratch { hs.scratch_ok with
    phases_target_len := by rw [List.length_set]; exact hs.scratch_ok.phases_target_len }

theorem m6_len_set_pb {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 8}
    (hs : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with
      phases_best := s.scratch.phases_best.set i v } }).LengthsOk c :=
  hs.with_scratch { hs.scratch_ok with
    phases_best_len := by rw [List.length_set]; exact hs.scratch_ok.phases_best_len }

theorem m6_walkEntriesOk_set_w2 {s : FullState} {n i : Nat} {v : BitVec 32}
    (hok : FullWalkEntriesOk s n) :
    FullWalkEntriesOk
      { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set i v } } n :=
  hok

theorem m6_extPres_set_sb {s0 s : FullState} {i : Nat} {v : BitVec 32}
    (hp : FullExtScratchPres s0 s) :
    FullExtScratchPres s0
      { s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set i v } } :=
  hp

theorem m6_extPres_set_w2 {s0 s : FullState} {i : Nat} {v : BitVec 32}
    (hp : FullExtScratchPres s0 s) :
    FullExtScratchPres s0
      { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set i v } } :=
  hp

theorem m6_core_set_sb {s0 s : FullState} {i : Nat} {v : BitVec 32}
    (hc : PreservesCoreSlice FullState.core s0 s) :
    PreservesCoreSlice FullState.core s0
      { s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set i v } } :=
  hc

theorem m6_core_set_w2 {s0 s : FullState} {i : Nat} {v : BitVec 32}
    (hc : PreservesCoreSlice FullState.core s0 s) :
    PreservesCoreSlice FullState.core s0
      { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set i v } } :=
  hc

/-! ## 2. `full_walk_collect_m6` (`m6WalkCollectSpec`) -/

section WalkCollectProof

open scoped FullArenaTactics

private theorem m6_add1_64 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem m6_add2_64 {x : BitVec 64} (h : x.toNat + 2 < 2 ^ 64) :
    (x + 2#64).toNat = x.toNat + 2 := by
  rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt h]

private theorem m6_add1_32 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem m6_sub_64 {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub]; omega

private theorem m6_shl1_64 {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega

private theorem m6_shl1_add1_64 {x : BitVec 64} (h : 2 * x.toNat + 1 < 2 ^ 64) :
    ((x <<< (1 : Nat)) + 1).toNat = 2 * x.toNat + 1 := by
  rw [BitVec.toNat_add, m6_shl1_64 (by omega), show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt h]

private theorem m6_arena_lit_lt {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    {p j : Nat} (ha : FullArenaClausesInv c F_cur k) (harl : k.arena.length = c.arena_cap)
    (hp_mem : p ∈ fullArenaClauseRefsCore k) (hng : fullArenaClauseGarbCore k p = false)
    (hle : p + 3 + fullArenaClauseSizeCore k p ≤ c.arena_cap)
    (hj : j < fullArenaClauseSizeCore k p) :
    (k.arena[p + 3 + j]'(by rw [harl]; omega)).toNat < 2 * k.cur_vars := by
  have hmem : (k.arena[p + 3 + j]'(by rw [harl]; omega)).toNat ∈ fullArenaClauseLitsCore k p := by
    unfold fullArenaClauseLitsCore
    refine List.mem_map.mpr ⟨_, ?_, rfl⟩
    have hlt : j < ((k.arena.drop (p + 3)).take (fullArenaClauseSizeCore k p)).length := by
      rw [List.length_take, List.length_drop, harl]; exact Nat.lt_min.mpr ⟨hj, by omega⟩
    simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt
  exact ha.lits_lt p hp_mem hng _ hmem

private theorem m6_watchSlice_init {F_cur : List (List Nat)} {k : FullCoreState} {l : Nat}
    (hw : ModeWatchesInv F_cur k) (hl : l < 2 * k.cur_vars) :
    fullWatchOffCore k l + fullWatchSizeCore k l ≤ k.wlen ∧
    (if k.dense_mode = 0#64 then
      WatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)
    else DenseWatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)) := by
  by_cases hdm : k.dense_mode = 0#64
  · have hws : WatchesInv F_cur k := by unfold ModeWatchesInv at hw; rwa [ite_eq_left hdm] at hw
    exact ⟨hws.layout.bounds l hl, by rw [ite_eq_left hdm]; exact hws.slices l hl⟩
  · have hwd : DenseWatchesInv F_cur k := by
      unfold ModeWatchesInv at hw; rwa [ite_eq_right hdm] at hw
    exact ⟨hwd.layout.bounds l hl, by rw [ite_eq_right hdm]; exact hwd.slices l hl⟩

private theorem m6_add3_k_64 {p : BitVec 64} {k : BitVec 32} (h : p.toNat + 3 + k.toNat < 2 ^ 64) :
    (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, show (3#64 : BitVec 64).toNat = 3 from rfl,
    zext_toNat _ (by decide), Nat.mod_eq_of_lt (by omega : p.toNat + 3 < 2 ^ 64),
    Nat.mod_eq_of_lt h]

private theorem m6_walkEntriesOk_push_bin_2 {s : FullState} {n l ot i0 i1 : Nat}
    {v0 v1 : BitVec 32} (hok : FullWalkEntriesOk s n)
    (hi0 : i0 = 2 * n) (hi1 : i1 = 2 * n + 1)
    (hv0 : v0 = BitVec.ofNat 32 l ||| 0x80000000#32) (hv1 : v1 = BitVec.ofNat 32 ot)
    (hcv : s.core.cur_vars < 2 * dimacsBound) (hl : l < 2 * s.core.cur_vars)
    (hot : ot < 2 * s.core.cur_vars) (hbd : 2 * n + 1 < s.scratch.scratch_buf.length) :
    let s1 := { s with scratch := { s.scratch with
      scratch_buf := s.scratch.scratch_buf.set i0 v0 } }
    FullWalkEntriesOk
      { s1 with scratch := { s1.scratch with
        scratch_buf := s1.scratch.scratch_buf.set i1 v1 } } (n + 1) := by
  intro s1
  have hpb := m6_walkEntriesOk_push_bin hok hcv hl hot hbd
  refine m6_walkEntriesOk_of_scr_eq hpb rfl fun i _ => ?_
  dsimp only [s1]; rw [hi0, hi1, hv0, hv1]

private theorem m6_walkEntriesOk_push_large_2 {s : FullState} {n ref i0 i1 : Nat}
    {v0 : BitVec 32} (hok : FullWalkEntriesOk s n)
    (hi0 : i0 = 2 * n) (hi1 : i1 = 2 * n + 1) (hv0 : v0 = BitVec.ofNat 32 ref)
    (href : ref ∈ fullArenaClauseRefsCore s.core)
    (hng : fullArenaClauseGarb s ref = false) (hlo : ref < 2 ^ 31)
    (hbd : 2 * n + 1 < s.scratch.scratch_buf.length) :
    let s1 := { s with scratch := { s.scratch with
      scratch_buf := s.scratch.scratch_buf.set i0 v0 } }
    FullWalkEntriesOk
      { s1 with scratch := { s1.scratch with
        scratch_buf := s1.scratch.scratch_buf.set i1 0#32 } } (n + 1) := by
  intro s1
  have hpl := m6_walkEntriesOk_push_large hok href hng hlo hbd
  refine m6_walkEntriesOk_of_scr_eq hpl rfl fun i _ => ?_
  dsimp only [s1]; rw [hi0, hi1, hv0]

/-- `full_walk_collect_m6` satisfies `m6WalkCollectSpec`. -/
theorem full_walk_collect_m6_wp (Γ : Env)
    (hArenaNext : ∀ a m Q X,
      fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, m6WalkCollectSpec a m Q X → Func.wp Γ full_walk_collect_m6_body a m Q X := by
  rintro ⟨h, max_cl, occ_cap, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, ⟨F0, hinv⟩, hcap⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  obtain ⟨F_cur, hw_inv⟩ := hinv.witness
  obtain ha := hw_inv.arena; obtain hw := hw_inv.watches
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain haca : c.arena_cap < 2 * dimacsBound := c.harena
  obtain hwc : c.wcap < 2 * dimacsBound := c.hwcap
  obtain hsca : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmax haca hwc hsca
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain harl := hlen.core_ok.arena_len_arr
  obtain hale := hlen.core_ok.arena_len_le
  obtain hwvl := hlen.core_ok.wvec_len
  obtain hwsl := hlen.core_ok.wstk_len_arr
  obtain hwll := hlen.core_ok.wlen_le
  obtain hvl := hlen.core_ok.vals_len
  have hnl_eq : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega), Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  c0_hsteps_nogrp
  -- Loop 1: zero `work_stk2[0 ..< 2*cv)`
  refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
    (fun s1 (l, ()) => l.toNat ≤ 2 * s.core.cur_vars ∧ FullExtScratchPres s s1)
    (fun (l, ()) => 2 * s.core.cur_vars - l.toNat)
    (fun J1 hJ1 => by
      c0_hsteps; exact hJ1 s (0#64, ()) m hm rfl hlen ⟨Nat.zero_le _, ⟨rfl, rfl⟩⟩)
    (fun J1 s1 (l, ()) m1 hcore1 hs1 ⟨hlle, hpres1⟩ hm1 hJ1 => ?_)
  dsimp only [fullSafetySlice] at hs1 hm1
  have hceq1 : s1.core = s.core := hcore1
  obtain hws2l1 := hs1.scratch_ok.work_stk2_len
  c0_hsteps_nogrp
  · have hllt : l.toNat < 2 * s.core.cur_vars := by
      have h1 : l.toNat < 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by assumption
      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at h1
      exact h1
    have hl_ws2 : l.toNat < s1.scratch.work_stk2.length := by rw [hws2l1]; omega
    have hl1 : (l + 1#64).toNat = l.toNat + 1 := m6_add1_64 (by omega)
    c0_hsteps
    exact hJ1 _ (l + 1#64, ()) m hm (by dsimp only; omega) rfl
      (m6_len_set_w2 hs1) ⟨by omega, hpres1⟩
  · -- Loop 2: binary clause collection
    clear J1 hJ1
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
      (fun s2 (l, n, tot, ()) =>
        l.toNat ≤ 2 * s.core.cur_vars ∧ n.toNat ≤ max_cl.toNat ∧
        tot.toNat ≤ occ_cap.toNat ∧ FullWalkEntriesOk s2 n.toNat ∧ FullExtScratchPres s s2)
      (fun (l, _, _, ()) => 2 * s.core.cur_vars - l.toNat)
      (fun J2 hJ2 => by
        c0_hsteps; exact hJ2 s1 (0#64, 0#64, 0#64, ()) m1 hm1 rfl hs1
          ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _),
            hpres1⟩)
      (fun J2 s2 (l, n, tot, ()) m2 hcore2 hs2 ⟨hlle2, hnle2, htot2, hok2, hpres2⟩ hm2 hJ2 => ?_)
    rw [Blocks.get_here]
    dsimp only [fullSafetySlice] at hs2 hm2
    have hceq2 : s2.core = s.core := Eq.trans hcore2 hceq1
    -- Join after Loop 2 -> enter Loop 3 (arena scan)
    refine wp_join_group (ts := [])
      (fun () m3 => ∃ s3 : FullState,
        PreservesCoreSlice FullState.core s s3 ∧ s3.LengthsOk c ∧
        n.toNat ≤ max_cl.toNat ∧ tot.toNat ≤ occ_cap.toNat ∧
        FullWalkEntriesOk s3 n.toNat ∧ FullExtScratchPres s s3 ∧ (FullMem c s3 ⋆ R) m3)
      (fun _ () m3 ⟨s3, hcore3, hs3, hn3, htot3, hok3, hpres3, hm3⟩ => ?_)
      (fun Jb hJb => ?_)
    · -- Loop 3: arena scan
      clear J2 hJ2 hw hwvl hwsl hwll hnl_eq hwc hinv hw_inv hcore2 hs2 hm2 hlle2 hnle2 htot2 hok2
        hpres2 hceq2 hcore1 hs1 hm1 hlle hpres1 hceq1 hws2l1
      refine wp_loop_safety_slice (fullSafetySlice c) s3 R (fun _ => True) trivial
        (fun s4 (n4, tot4, p, ()) =>
          p.toNat ≤ s.core.arena_len ∧
          (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefsCore s.core) ∧
          n4.toNat ≤ max_cl.toNat ∧ tot4.toNat ≤ occ_cap.toNat ∧
          FullWalkEntriesOk s4 n4.toNat ∧ FullExtScratchPres s s4)
        (fun (_, _, p, ()) => s.core.arena_len - p.toNat)
        (fun J3 hJ3 => by
          c0_hsteps
          refine hJ3 s3 (n, tot, 0#64, ()) m3 hm3 rfl hs3
            ⟨Nat.zero_le _, ?_, hn3, htot3, hok3, hpres3⟩
          rcases ha.len_ok with hz | h3
          · exact Or.inl hz.symm
          · exact Or.inr (m6_zero_mem_arenaClauseRefsCore h3))
        (fun J3 s4 (n4, tot4, p, ()) m4 hcore4 hs4 _
            ⟨hple, hpref, hn4, htot4, hok4, hpres4⟩ hm4 hJ3 => ?_)
      dsimp only [fullSafetySlice] at hs4 hm4
      have hceq4 : s4.core = s.core := Eq.trans hcore4 hcore3
      have hret_end : Q (n4, ()) m4 :=
        hQ (n4, ()) s4 m4 hceq4 hs4 ⟨hpres4, hn4, hok4⟩ hm4
      c0_hsteps_nogrp
      · have hplt : p.toNat < s.core.arena_len := by
          have : p.toNat < s4.core.arena_len % 2 ^ 64 := by assumption
          rw [hceq4, Nat.mod_eq_of_lt (by omega)] at this; exact this
        have hn4lt : n4.toNat < max_cl.toNat := by assumption
        have hp_mem : p.toNat ∈ fullArenaClauseRefsCore s.core :=
          hpref.resolve_left (by omega)
        have hwf := ha.refs_wf p.toNat hp_mem
        have hwf1 := hwf.1; have hwf3 := hwf.2.2.1; have hwf4 := hwf.2.2.2.1
        have hp_ar : p.toNat < s4.core.arena.length := by rw [hceq4, harl]; omega
        have hp2_ar : (p + 2#64).toNat < s4.core.arena.length := by
          rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
            Nat.mod_eq_of_lt (by omega), hceq4, harl]; omega
        c0_hsteps_nogrp
        -- Join before `full_arena_next(h, (u32)p)`
        refine wp_join_group (ts := [i64, i64])
          (fun (n5, tot5, ()) m5 => ∃ s5 : FullState,
            PreservesCoreSlice FullState.core s s5 ∧ s5.LengthsOk c ∧
            n5.toNat ≤ max_cl.toNat ∧ tot5.toNat ≤ occ_cap.toNat ∧
            FullWalkEntriesOk s5 n5.toNat ∧ FullExtScratchPres s s5 ∧ (FullMem c s5 ⋆ R) m5)
          (fun _ ⟨n5, tot5, ⟨⟩⟩ m5 ⟨s5, hcore5, hs5, hn5, htot5, hok5, hpres5, hm5⟩ => ?_)
          (fun Jn hJn => ?_)
        · c0_hsteps_nogrp
          c0_call hArenaNext
          refine ⟨c, s5, R, rfl, hs5, hm5, ?_⟩
          dsimp only
          have hp32_eq : (p.setWidth 32).toNat = p.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          have hr_eq : (BitVec.ofNat 32 (fullArenaNextOff s5.core.arena s5.core.arena_len
              (p.setWidth 32).toNat)).toNat =
              fullArenaNextOff s.core.arena s.core.arena_len p.toNat := by
            rw [hcore5, hp32_eq, bv32_ofNat_toNat (by omega)]
          have hnxt_gt : p.toNat < fullArenaNextOff s.core.arena s.core.arena_len p.toNat := by
            omega
          have hnxt_dom := m6_arenaClauseRefs_next ha hp_mem
          exact hJ3 s5 (n5, tot5,
            (BitVec.ofNat 32 (fullArenaNextOff s5.core.arena s5.core.arena_len
              (p.setWidth 32).toNat)).setWidth 64, ()) m5 hm5
            (by dsimp only; rw [zext_toNat _ (by decide), hr_eq]; omega)
            (Eq.trans hcore5 hceq4.symm) hs5
            ⟨by rw [zext_toNat _ (by decide), hr_eq]; exact hwf4,
              by rw [zext_toNat _ (by decide), hr_eq]; exact hnxt_dom,
              hn5, htot5, hok5, hpres5⟩
        · c0_hsteps_nogrp
          · -- Candidate large clause: `!garb && !red && sz >= 3`
            have hp2_idx : (p + 2#64).toNat = p.toNat + 2 := by
              rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
                Nat.mod_eq_of_lt (by omega)]
            have hsz_eq : (s4.core.arena[(p + 2#64).toNat]'hp2_ar).toNat =
                fullArenaClauseSizeCore s.core p.toNat := by
              have h1 : s4.core.arena[(p + 2#64).toNat]'hp2_ar =
                  s.core.arena[p.toNat + 2]'(by rw [harl]; omega) := by
                simp only [hceq4, hp2_idx]
              rw [h1]; unfold fullArenaClauseSizeCore
              rw [List.getElem?_eq_getElem (by rw [harl]; omega), Option.getD_some]
            have hng : fullArenaClauseGarb s4 p.toNat = false := by
              unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
              rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
              have h0 : (s4.core.arena[p.toNat]'hp_ar &&& 0x00080000#32) = 0#32 := by assumption
              rw [h0]; rfl
            have hng_s : fullArenaClauseGarbCore s.core p.toNat = false := by
              change fullArenaClauseGarbCore s4.core p.toNat = false at hng
              rwa [hceq4] at hng
            have hle_al : p.toNat + 3 + fullArenaClauseSizeCore s.core p.toNat ≤
                s.core.arena_len := Nat.le_trans hwf3 hwf4
            have hp_lit : ∀ j (hj : j < fullArenaClauseSizeCore s.core p.toNat),
                (s.core.arena[p.toNat + 3 + j]'(by rw [harl]; omega)).toNat <
                  2 * s.core.cur_vars :=
              fun j hj => m6_arena_lit_lt ha harl hp_mem hng_s (by omega) hj
            clear ha hng_s hQ hJ3 hArenaNext
            -- Loop 3a: read-only scan `k < sz` counting `unass` and `root_sat`
            refine wp_loop_break_group
              (fun (_rsat, unass, _k, ()) m_a =>
                m_a = m4 ∧ unass.toNat ≤ fullArenaClauseSizeCore s.core p.toNat)
              (fun rem (unass, k, ()) m_a =>
                m_a = m4 ∧ k.toNat ≤ fullArenaClauseSizeCore s.core p.toNat ∧
                unass.toNat ≤ k.toNat ∧ rem = fullArenaClauseSizeCore s.core p.toNat - k.toNat)
              ?_ ?_ ?_
            · rintro _ ⟨rsat, unass, _k, ⟨⟩⟩ m_a ⟨rfl, hun_le⟩
              refine wp_join_group (ts := [i64, i64, i32])
                (fun (n5, tot5, _k5, ()) m5 => ∃ s5 : FullState,
                  PreservesCoreSlice FullState.core s s5 ∧ s5.LengthsOk c ∧
                  n5.toNat ≤ max_cl.toNat ∧ tot5.toNat ≤ occ_cap.toNat ∧
                  FullWalkEntriesOk s5 n5.toNat ∧ FullExtScratchPres s s5 ∧ (FullMem c s5 ⋆ R) m5)
                (fun _ ⟨n5, tot5, _k5, ⟨⟩⟩ m5 ⟨s5, hcore5, hs5, hn5, htot5, hok5, hpres5, hm5⟩ => by
                  c0_hsteps; exact hJn (n5, tot5, ()) m5
                    ⟨s5, hcore5, hs5, hn5, htot5, hok5, hpres5, hm5⟩)
                (fun Jc3 hJc3 => ?_)
              c0_hsteps_nogrp
              · exact hJc3 (n4, tot4, _k, ()) m_a ⟨s4, hceq4, hs4, hn4, htot4, hok4, hpres4, hm4⟩
              · -- `!rsat && unass >= 2 && unass <= occ_cap - tot4`: commit clause!
                have hsbl4 := hs4.scratch_ok.scratch_buf_len
                have h2n : (n4 <<< (1 : Nat)).toNat = 2 * n4.toNat := m6_shl1_64 (by omega)
                have h2n_lt : 2 * n4.toNat + 1 < s4.scratch.scratch_buf.length := by
                  rw [hsbl4]; omega
                have h2n_lt0 : (n4 <<< (1 : Nat)).toNat < s4.scratch.scratch_buf.length := by
                  rw [h2n]; omega
                have h2n1_eq : ((n4 <<< (1 : Nat)) + 1).toNat = 2 * n4.toNat + 1 :=
                  m6_shl1_add1_64 (by omega)
                have h2n1_lt : ((n4 <<< (1 : Nat)) + 1).toNat <
                    s4.scratch.scratch_buf.length := by rw [h2n1_eq]; exact h2n_lt
                have htot_sub : (occ_cap - tot4).toNat = occ_cap.toNat - tot4.toNat :=
                  m6_sub_64 htot4
                have hun_le_rem : unass.toNat ≤ occ_cap.toNat - tot4.toNat := by
                  have h1 : unass.toNat ≤ (occ_cap - tot4).toNat := by
                    rw [BitVec.toNat_sub]; exact by assumption
                  omega
                have htot_new : (tot4 + unass).toNat = tot4.toNat + unass.toNat := by
                  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                have hn4_new : (n4 + 1#64).toNat = n4.toNat + 1 := m6_add1_64 (by omega)
                c0_hsteps_nogrp
                -- Inner loop 3b: increment `work_stk2[lit]` for `vals[lit] == 0`
                let s4_1 : FullState := { s4 with scratch := { s4.scratch with
                  scratch_buf := s4.scratch.scratch_buf.set (n4 <<< (1 : Nat)).toNat
                    (p.setWidth 32) } }
                let s4w : FullState := { s4_1 with scratch := { s4_1.scratch with
                  scratch_buf := s4_1.scratch.scratch_buf.set
                    ((n4 <<< (1 : Nat)) + 1).toNat 0#32 } }
                have hs4w_len : s4w.LengthsOk c := m6_len_set_sb (m6_len_set_sb hs4)
                have hs4w_ok : FullWalkEntriesOk s4w (n4.toNat + 1) :=
                  m6_walkEntriesOk_push_large_2 hok4 h2n h2n1_eq rfl
                    (by change p.toNat ∈ fullArenaClauseRefsCore s4.core; rw [hceq4]; exact hp_mem)
                    hng (by omega) h2n_lt
                have hs4w_pres : FullExtScratchPres s s4w :=
                  m6_extPres_set_sb (m6_extPres_set_sb hpres4)
                clear hwf1 hwf3 hwf4 hng hret_end h2n h2n_lt
                  h2n_lt0 h2n1_eq h2n1_lt htot_sub hJn
                refine wp_loop_safety_slice_pure (fullSafetySlice c) s4w R
                  (fun s5 (k, ()) =>
                    k.toNat ≤ fullArenaClauseSizeCore s.core p.toNat ∧
                    s5.scratch.scratch_buf = s4w.scratch.scratch_buf ∧ FullExtScratchPres s s5)
                  (fun (k, ()) => fullArenaClauseSizeCore s.core p.toNat - k.toNat)
                  (fun Jk hJk => by
                    c0_hsteps
                    exact hJk s4w (0#32, ()) _ hm rfl hs4w_len ⟨Nat.zero_le _, rfl, hs4w_pres⟩)
                  (fun Jk s5 (k, ()) m5 hcore5 hs5 ⟨hkle, hsb5, hpres5⟩ hm5 hJk => ?_)
                dsimp only [fullSafetySlice] at hs5 hm5
                have hceq5 : s5.core = s.core := Eq.trans hcore5 hceq4
                obtain hws2l5 := hs5.scratch_ok.work_stk2_len
                c0_hsteps_nogrp
                · have hklt : k.toNat < fullArenaClauseSizeCore s.core p.toNat := by
                    have : k.toNat < (s4.core.arena[(p + 2#64).toNat]'hp2_ar).toNat := by assumption
                    omega
                  have hk_idx : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat :=
                    m6_add3_k_64 (by omega)
                  have hk_ar : (p + 3#64 + k.setWidth 64).toNat < s5.core.arena.length := by
                    rw [hk_idx, hceq5, harl]; omega
                  let lit5 := s5.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hk_ar
                  have hlit_lt : lit5.toNat < 2 * s.core.cur_vars := by
                    have := hp_lit k.toNat hklt
                    simpa only [lit5, hceq5, hk_idx] using this
                  have hvl5 : s5.core.vals.length = 2 * c.max_vars := by rw [hceq5, hvl]
                  have hlit_z : (lit5.setWidth 64).toNat = lit5.toNat := zext_toNat _ (by decide)
                  have hlit_v : (lit5.setWidth 64).toNat < s5.core.vals.length := by omega
                  have hlit_w2 : (lit5.setWidth 64).toNat < s5.scratch.work_stk2.length := by
                    rw [hws2l5]; omega
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := m6_add1_32 (by omega)
                  c0_hsteps
                  · exact hJk _ (k + 1#32, ()) _ hm (by dsimp only; omega)
                      (m6_core_set_w2 rfl) (m6_len_set_w2 hs5)
                      ⟨by omega, hsb5, m6_extPres_set_w2 hpres5⟩
                  · exact hJk s5 (k + 1#32, ()) m5 hm5 (by dsimp only; omega) rfl hs5
                      ⟨by omega, hsb5, hpres5⟩
                · c0_hsteps
                  have hok5 : FullWalkEntriesOk s5 (n4 + 1#64).toNat := by
                    rw [hn4_new]
                    exact m6_walkEntriesOk_of_scr_eq hs4w_ok hcore5 (fun i _ => by rw [hsb5])
                  exact hJc3 (n4 + 1#64, tot4 + unass, k, ()) m5
                    ⟨s5, hceq5, hs5, by omega, by omega, hok5, hpres5, hm5⟩
              · exact hJc3 (n4, tot4, _k, ()) m_a ⟨s4, hceq4, hs4, hn4, htot4, hok4, hpres4, hm4⟩
              · exact hJc3 (n4, tot4, _k, ()) m_a ⟨s4, hceq4, hs4, hn4, htot4, hok4, hpres4, hm4⟩
            · rintro B _ rem ⟨unass, k, ⟨⟩⟩ m_a hB ih ⟨rfl, hkle, hun_le, rfl⟩
              c0_hsteps_nogrp
              · have hklt : k.toNat < fullArenaClauseSizeCore s.core p.toNat := by
                  have : k.toNat < (s4.core.arena[(p + 2#64).toNat]'hp2_ar).toNat := by assumption
                  omega
                have hk_idx : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat :=
                  m6_add3_k_64 (by omega)
                have hk_ar : (p + 3#64 + k.setWidth 64).toNat < s4.core.arena.length := by
                  rw [hk_idx, hceq4, harl]; omega
                let lit4 := s4.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hk_ar
                have hlit_lt : lit4.toNat < 2 * s.core.cur_vars := by
                  have := hp_lit k.toNat hklt
                  simpa only [lit4, hceq4, hk_idx] using this
                have hvl4 : s4.core.vals.length = 2 * c.max_vars := by rw [hceq4, hvl]
                have hlit_v : (lit4.setWidth 64).toNat < s4.core.vals.length := by
                  rw [zext_toNat _ (by decide)]; omega
                have hk1 : (k + 1#32).toNat = k.toNat + 1 := m6_add1_32 (by omega)
                have hun1 : (unass + 1#64).toNat = unass.toNat + 1 := m6_add1_64 (by omega)
                c0_hsteps
                · exact hB (true, unass, k, ()) m_a ⟨rfl, by omega⟩
                · exact ih (fullArenaClauseSizeCore s.core p.toNat - (k + 1#32).toNat)
                    (unass + 1#64, k + 1#32, ()) m_a (by rw [hk1]; omega)
                    ⟨rfl, by rw [hk1]; omega, by rw [hun1, hk1]; omega, rfl⟩
                · exact ih (fullArenaClauseSizeCore s.core p.toNat - (k + 1#32).toNat)
                    (unass, k + 1#32, ()) m_a (by rw [hk1]; omega)
                    ⟨rfl, by rw [hk1]; omega, by rw [hk1]; omega, rfl⟩
              · exact hB (false, unass, k, ()) m_a ⟨rfl, by omega⟩
            · intro _ _ _ hL; c0_hsteps
              exact hL (fullArenaClauseSizeCore s.core p.toNat) (0#64, 0#32, ()) m4
                ⟨rfl, Nat.zero_le _, Nat.zero_le _, (Nat.sub_zero _).symm⟩
          · exact hJn (n4, tot4, ()) m4 ⟨s4, hceq4, hs4, hn4, htot4, hok4, hpres4, hm4⟩
          · exact hJn (n4, tot4, ()) m4 ⟨s4, hceq4, hs4, hn4, htot4, hok4, hpres4, hm4⟩
          · exact hJn (n4, tot4, ()) m4 ⟨s4, hceq4, hs4, hn4, htot4, hok4, hpres4, hm4⟩
      · exact hret_end
      · exact hret_end
    · -- Loop 2 body (`l < nlits && n < max_cl && tot + 2 <= occ_cap`)
      have hexit2 : Jb () m2 :=
        hJb () m2 ⟨s2, hceq2, hs2, hnle2, htot2, hok2, hpres2, hm2⟩
      c0_hsteps_nogrp
      · have hllt2 : l.toNat < 2 * s.core.cur_vars := by
          have h1 : l.toNat < 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by assumption
          rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at h1
          exact h1
        have hl_v : l.toNat < s2.core.vals.length := by rw [hceq2, hvl]; omega
        have hl1 : (l + 1#64).toNat = l.toNat + 1 := m6_add1_64 (by omega)
        -- Join after `if (vals[l] == 0)` -> `l = l + 1; jump J2`
        refine wp_join_group (ts := [i64, i64])
          (fun (n_a, tot_a, ()) m_a => ∃ s_a : FullState,
            PreservesCoreSlice (fullSafetySlice c).coreProj s2 s_a ∧ s_a.LengthsOk c ∧
            n_a.toNat ≤ max_cl.toNat ∧ tot_a.toNat ≤ occ_cap.toNat ∧
            FullWalkEntriesOk s_a n_a.toNat ∧ FullExtScratchPres s s_a ∧ (FullMem c s_a ⋆ R) m_a)
          (fun _ ⟨n_a, tot_a, ⟨⟩⟩ m_a ⟨s_a, hcore_a, hs_a, hn_a, htot_a, hok_a, hpres_a, hm_a⟩ => by
            c0_hsteps
            exact hJ2 s_a (l + 1#64, n_a, tot_a, ()) m_a hm_a (by dsimp only; omega) hcore_a hs_a
              ⟨by omega, hn_a, htot_a, hok_a, hpres_a⟩)
          (fun Jl hJl => ?_)
        c0_hsteps_nogrp
        · -- `vals[l] == 0`: scan watch list of `l`
          have h2l_w : (l <<< (1 : Nat)).toNat = 2 * l.toNat := m6_shl1_64 (by omega)
          have h2l_wv : 2 * l.toNat < s2.core.wvec.length := by rw [hceq2, hwvl]; omega
          have h2l1_wv : 2 * l.toNat + 1 < s2.core.wvec.length := by rw [hceq2, hwvl]; omega
          have h2l_wv' : (l <<< (1 : Nat)).toNat < s2.core.wvec.length := by
            rw [h2l_w]; exact h2l_wv
          have h2l1_eq : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1 := by
            rw [BitVec.toNat_add, h2l_w, show (1#64 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          have h2l1_wv' : ((l <<< (1 : Nat)) + 1#64).toNat < s2.core.wvec.length := by
            rw [h2l1_eq]; exact h2l1_wv
          have hwo_eq : (s2.core.wvec[(l <<< (1 : Nat)).toNat]'h2l_wv').toNat =
              fullWatchOffCore s.core l.toNat := by
            have h1 : s2.core.wvec[(l <<< (1 : Nat)).toNat]'h2l_wv' =
                s.core.wvec[2 * l.toNat]'(by rw [hwvl]; omega) := by simp only [hceq2, h2l_w]
            rw [h1]; unfold fullWatchOffCore
            rw [List.getElem?_eq_getElem (by rw [hwvl]; omega), Option.getD_some]
          have hws_eq : (s2.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'h2l1_wv').toNat =
              fullWatchSizeCore s.core l.toNat := by
            have h1 : s2.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'h2l1_wv' =
                s.core.wvec[2 * l.toNat + 1]'(by rw [hwvl]; omega) := by simp only [hceq2, h2l1_eq]
            rw [h1]; unfold fullWatchSizeCore
            rw [List.getElem?_eq_getElem (by rw [hwvl]; omega), Option.getD_some]
          obtain ⟨hslice_bd, hslice0⟩ := m6_watchSlice_init hw hllt2
          clear hArenaNext hinv hw_inv ha hw hQ hJ2 hJb hexit2 haca harl hale hcore1 hs1 hm1
            hlle hpres1 hceq1 hws2l1 hnl_eq
          let off0 := (s2.core.wvec[(l <<< (1 : Nat)).toNat]'h2l_wv').setWidth 64
          let sz0 := (s2.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'h2l1_wv').setWidth 64
          let end0 := off0 + sz0
          have hend0_eq : end0.toNat =
              fullWatchOffCore s.core l.toNat + fullWatchSizeCore s.core l.toNat := by
            dsimp only [end0, off0, sz0]
            rw [BitVec.toNat_add, zext_toNat _ (by decide), zext_toNat _ (by decide),
              hwo_eq, hws_eq, Nat.mod_eq_of_lt (by omega)]
          c0_hsteps_nogrp
          refine wp_loop_safety_slice_pure (fullSafetySlice c) s2 R
            (fun sw (nw, totw, offw, ()) =>
              offw.toNat ≤ end0.toNat ∧ nw.toNat ≤ max_cl.toNat ∧
              totw.toNat ≤ occ_cap.toNat ∧ FullWalkEntriesOk sw nw.toNat ∧
              FullExtScratchPres s sw ∧
              (if s.core.dense_mode = 0#64 then
                WatchSliceOk F_cur s.core l.toNat offw.toNat (end0.toNat - offw.toNat)
              else
                DenseWatchSliceOk F_cur s.core l.toNat offw.toNat (end0.toNat - offw.toNat)))
            (fun (_, _, offw, ()) => end0.toNat - offw.toNat)
            (fun Jw hJw => by
              c0_hsteps
              refine hJw s2 (n, tot, off0, ()) m2 hm2 rfl hs2
                ⟨by rw [hend0_eq]; dsimp only [off0]; rw [zext_toNat _ (by decide), hwo_eq]; omega,
                  hnle2, htot2, hok2, hpres2, ?_⟩
              have hsub : end0.toNat - off0.toNat = fullWatchSizeCore s.core l.toNat := by
                rw [hend0_eq]; dsimp only [off0]; rw [zext_toNat _ (by decide), hwo_eq]; omega
              have hoff0_eq : off0.toNat = fullWatchOffCore s.core l.toNat := by
                dsimp only [off0]; rw [zext_toNat _ (by decide), hwo_eq]
              rw [hsub, hoff0_eq]; exact hslice0)
            (fun Jw sw (nw, totw, offw, ()) mw hcorew hsw
                ⟨hoff_le, hnw_le, htotw_le, hokw, hpresw, hslw⟩ hmw hJw => ?_)
          dsimp only [fullSafetySlice] at hsw hmw
          have hceqw : sw.core = s.core := Eq.trans hcorew hceq2
          have hdone_w : Jl (nw, totw, ()) mw :=
            hJl (nw, totw, ()) mw ⟨sw, hcorew, hsw, hnw_le, htotw_le, hokw, hpresw, hmw⟩
          c0_hsteps_nogrp
          · have hoff_lt : offw.toNat < end0.toNat := by
              have h1 : offw.toNat <
                  ((s2.core.wvec[2 * l.toNat % 2 ^ 64]'(by
                      rw [Nat.mod_eq_of_lt (by omega), hceq2, hwvl]; omega)).toNat +
                    (s2.core.wvec[(2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                      rw [show (1 : BitVec 64).toNat = 1 from rfl,
                        Nat.mod_eq_of_lt (by omega), hceq2, hwvl]; omega)).toNat) %
                    2 ^ 64 := by assumption
              rw [hend0_eq]
              have ha1 : (s2.core.wvec[2 * l.toNat % 2 ^ 64]'(by
                  rw [Nat.mod_eq_of_lt (by omega), hceq2, hwvl]; omega)).toNat =
                  fullWatchOffCore s.core l.toNat := by
                rw [← hwo_eq]; congr 1
              have ha2 : (s2.core.wvec[(2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                  rw [show (1 : BitVec 64).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt (by omega), hceq2, hwvl]; omega)).toNat =
                  fullWatchSizeCore s.core l.toNat := by
                rw [← hws_eq]; congr 1
                simp only [h2l1_eq, show (1 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega : 2 * l.toNat + 1 < 2 ^ 64)]
              rw [ha1, ha2, Nat.mod_eq_of_lt (by omega)] at h1; exact h1
            have hnw_lt : nw.toNat < max_cl.toNat := by assumption
            have htot_p2 : (totw + 2#64).toNat = totw.toNat + 2 := m6_add2_64 (by omega)
            have htot_lt : totw.toNat + 2 ≤ occ_cap.toNat := by
              have h1 : (totw.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 ≤ occ_cap.toNat := by
                assumption
              rw [show (2 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)] at h1
              exact h1
            have hrem_pos : 0 < end0.toNat - offw.toNat := by omega
            obtain ⟨w0, hw0_at, hbin_st, hlg_st⟩ := m6_watchSlice_step
              (fun hc => by rw [ite_eq_left hc] at hslw; exact hslw)
              (fun hc => by rw [ite_eq_right hc] at hslw; exact hslw) hrem_pos
            have hoff_ws : offw.toNat < sw.core.wstk.length := by rw [hceqw, hwsl]; omega
            have hw0_eq : sw.core.wstk[offw.toNat]'hoff_ws = w0 := by
              have h1 : sw.core.wstk[offw.toNat]'hoff_ws =
                  s.core.wstk[offw.toNat]'(by rw [hwsl]; omega) := by simp only [hceqw]
              rw [List.getElem?_eq_getElem (by rw [hwsl]; omega)] at hw0_at
              rw [h1]; exact Option.some.inj hw0_at
            clear h2l_w h2l_wv h2l1_wv h2l1_eq hwo_eq hws_eq hslice_bd hslice0
              hw0_at hslw hdone_w hrem_pos
            c0_hsteps_nogrp
            -- Join after `if (w0 & PW_BIN_FLAG) ... else ...` -> `jump Jw (nw', totw', offw')`
            refine wp_join_group (ts := [i64, i64, i64])
              (fun (nw', totw', offw', ()) m' => ∃ sw' : FullState,
                PreservesCoreSlice (fullSafetySlice c).coreProj sw sw' ∧ sw'.LengthsOk c ∧
                offw.toNat < offw'.toNat ∧ offw'.toNat ≤ end0.toNat ∧
                nw'.toNat ≤ max_cl.toNat ∧ totw'.toNat ≤ occ_cap.toNat ∧
                FullWalkEntriesOk sw' nw'.toNat ∧ FullExtScratchPres s sw' ∧
                (if s.core.dense_mode = 0#64 then
                  WatchSliceOk F_cur s.core l.toNat offw'.toNat (end0.toNat - offw'.toNat)
                else DenseWatchSliceOk F_cur s.core l.toNat offw'.toNat
                  (end0.toNat - offw'.toNat)) ∧
                (FullMem c sw' ⋆ R) m')
              (fun _ ⟨nw', totw', offw', ⟨⟩⟩ m'
                  ⟨sw', hcore', hs', hoff_gt, hoff_le', hnw', htotw', hok', hpres', hsl', hm'⟩ => by
                c0_hsteps
                exact hJw sw' (nw', totw', offw', ()) m' hm' (by dsimp only; omega)
                  hcore' hs' ⟨hoff_le', hnw', htotw', hok', hpres', hsl'⟩)
              (fun Jstep hJstep => ?_)
            c0_hsteps_nogrp
            · -- Binary watch
              have hflag : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                rw [← hw0_eq]
                change (sw.core.wstk[offw.toNat]'hoff_ws &&& 2147483648) ≠ 0; assumption
              obtain ⟨hot_lt, _, hsl_next⟩ := hbin_st hflag
              have hot_v : ((sw.core.wstk[offw.toNat]'hoff_ws &&& 0x7FFFFFFF#32).setWidth 64).toNat
                  < sw.core.vals.length := by
                rw [hw0_eq, zext_toNat _ (by decide), hceqw, hvl]; omega
              have hoff1 : (offw + 1#64).toNat = offw.toNat + 1 := m6_add1_64 (by omega)
              have hsl1 : if s.core.dense_mode = 0#64 then
                    WatchSliceOk F_cur s.core l.toNat (offw + 1#64).toNat
                      (end0.toNat - (offw + 1#64).toNat)
                  else DenseWatchSliceOk F_cur s.core l.toNat (offw + 1#64).toNat
                      (end0.toNat - (offw + 1#64).toNat) := by
                rw [hoff1,
                  show end0.toNat - (offw.toNat + 1) = end0.toNat - offw.toNat - 1 by omega]
                exact hsl_next
              clear hbin_st hlg_st hflag hsl_next
              refine wp_join_group (ts := [i64, i64])
                (fun (nw', totw', ()) m' => ∃ sw' : FullState,
                  PreservesCoreSlice (fullSafetySlice c).coreProj sw sw' ∧ sw'.LengthsOk c ∧
                  nw'.toNat ≤ max_cl.toNat ∧ totw'.toNat ≤ occ_cap.toNat ∧
                  FullWalkEntriesOk sw' nw'.toNat ∧ FullExtScratchPres s sw' ∧
                  (FullMem c sw' ⋆ R) m')
                (fun _ ⟨nw', totw', ⟨⟩⟩ m'
                    ⟨sw', hcore', hs', hnw', htotw', hok', hpres', hm'⟩ => by
                  c0_hsteps
                  exact hJstep (nw', totw', offw + 1#64, ()) m'
                    ⟨sw', hcore', hs', by omega, by omega, hnw', htotw', hok', hpres', hsl1, hm'⟩)
                (fun Jb2 hJb2 => ?_)
              c0_hsteps_nogrp
              · -- `l < ot && vals[ot] == 0`: push binary entry!
                clear hsl1 hoff_lt hoff_le hend0_eq hcore2 hs2 hm2 hlle2 hnle2 htot2 hok2 hpres2
                  hceq2 hl1 hJstep hJw
                have hsblw := hsw.scratch_ok.scratch_buf_len
                have hws2lw := hsw.scratch_ok.work_stk2_len
                have h2n : (nw <<< (1 : Nat)).toNat = 2 * nw.toNat := m6_shl1_64 (by omega)
                have h2n_lt : 2 * nw.toNat + 1 < sw.scratch.scratch_buf.length := by
                  rw [hsblw]; omega
                have h2n_lt0 : (nw <<< (1 : Nat)).toNat < sw.scratch.scratch_buf.length := by
                  rw [h2n]; omega
                have h2n1_eq : ((nw <<< (1 : Nat)) + 1).toNat = 2 * nw.toNat + 1 :=
                  m6_shl1_add1_64 (by omega)
                have h2n1_lt : ((nw <<< (1 : Nat)) + 1).toNat <
                    sw.scratch.scratch_buf.length := by rw [h2n1_eq]; exact h2n_lt
                have hl_w2 : l.toNat < sw.scratch.work_stk2.length := by rw [hws2lw]; omega
                have hot_w2 : ((sw.core.wstk[offw.toNat]'hoff_ws &&&
                    0x7FFFFFFF#32).setWidth 64).toNat < sw.scratch.work_stk2.length := by
                  rw [hw0_eq, zext_toNat _ (by decide), hws2lw]; omega
                have hnw1 : (nw + 1#64).toNat = nw.toNat + 1 := m6_add1_64 (by omega)
                c0_hsteps
                refine hJb2 (nw + 1#64, totw + 2#64, ()) _
                  ⟨_, ?_, ?_, by omega, by omega, ?_, ?_, hm⟩
                · exact m6_core_set_w2 (m6_core_set_w2 (m6_core_set_sb (m6_core_set_sb rfl)))
                · exact m6_len_set_w2 (m6_len_set_w2 (m6_len_set_sb (m6_len_set_sb hsw)))
                · have hl32 : l.setWidth 32 ||| 0x80000000#32 =
                      BitVec.ofNat 32 l.toNat ||| 0x80000000#32 := rfl
                  have hot32 : sw.core.wstk[offw.toNat]'hoff_ws &&& 0x7FFFFFFF#32 =
                      BitVec.ofNat 32 (w0 &&& 0x7FFFFFFF#32).toNat := by
                    rw [hw0_eq]; apply BitVec.eq_of_toNat_eq
                    rw [bv32_ofNat_toNat (BitVec.isLt _)]
                  rw [hnw1]
                  exact m6_walkEntriesOk_set_w2 (m6_walkEntriesOk_set_w2
                    (m6_walkEntriesOk_push_bin_2 hokw h2n h2n1_eq hl32 hot32
                      (by rw [hceqw]; exact Nat.lt_of_le_of_lt hcv_le c.hmaxv)
                      (by rw [hceqw]; exact hllt2) (by rw [hceqw]; exact hot_lt) h2n_lt))
                · exact m6_extPres_set_w2 (m6_extPres_set_w2
                    (m6_extPres_set_sb (m6_extPres_set_sb hpresw)))
              · exact hJb2 (nw, totw, ()) mw ⟨sw, rfl, hsw, hnw_le, htotw_le, hokw, hpresw, hmw⟩
              · exact hJb2 (nw, totw, ()) mw ⟨sw, rfl, hsw, hnw_le, htotw_le, hokw, hpresw, hmw⟩
            · -- Large watch: skip 2 words
              have hflag0 : (w0 &&& 0x80000000#32) = 0#32 := by
                rw [← hw0_eq]
                change (sw.core.wstk[offw.toNat]'hoff_ws &&& 2147483648) = 0; assumption
              obtain ⟨hrem2, hsl_next⟩ := hlg_st hflag0
              have hoff2 : (offw + 2#64).toNat = offw.toNat + 2 := m6_add2_64 (by omega)
              c0_hsteps
              exact hJstep (nw, totw, offw + 2#64, ()) mw
                ⟨sw, rfl, hsw, by omega, by omega, hnw_le, htotw_le, hokw, hpresw, by
                  rw [hoff2, show end0.toNat - (offw.toNat + 2) = end0.toNat - offw.toNat - 2 by
                    omega]
                  exact hsl_next, hmw⟩
          · exact hdone_w
          · exact hdone_w
          · exact hdone_w
        · exact hJl (n, tot, ()) m2 ⟨s2, rfl, hs2, hnle2, htot2, hok2, hpres2, hm2⟩
      · exact hexit2
      · exact hexit2
      · exact hexit2

end WalkCollectProof

/-! ## 3. `full_walk_build_csr_m6` (`m6WalkBuildCsrSpec`) -/

section WalkBuildCsrProof

open scoped FullArenaTactics

private theorem m6_occ_idx {max_cl occ_cap : BitVec 64} {pos : BitVec 32} {cap : Nat}
    (hcap : 5 * max_cl.toNat + occ_cap.toNat ≤ cap) (hsca : cap < 2 ^ 28)
    (hpos : pos.toNat < occ_cap.toNat) :
    (max_cl * 5 + pos.setWidth 64).toNat = 5 * max_cl.toNat + pos.toNat ∧
    (max_cl * 5 + pos.setWidth 64).toNat < cap ∧
    2 * max_cl.toNat ≤ (max_cl * 5 + pos.setWidth 64).toNat := by
  have heq : (max_cl * 5 + pos.setWidth 64).toNat = 5 * max_cl.toNat + pos.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, show (5 : BitVec 64).toNat = 5 from rfl,
      zext_toNat _ (by decide), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  exact ⟨heq, by omega, by omega⟩

/-- `full_walk_build_csr_m6` satisfies `m6WalkBuildCsrSpec`. -/
theorem full_walk_build_csr_m6_wp (Γ : Env) :
    ∀ a m Q X, m6WalkBuildCsrSpec a m Q X → Func.wp Γ full_walk_build_csr_m6_body a m Q X := by
  rintro ⟨h, ncl, max_cl, occ_cap, ⟨⟩⟩ m Q X
    ⟨c, s, R, ⟨rfl, ⟨F0, hinv⟩, hncl, hcap, hok0⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  obtain ⟨F_cur, hw_inv⟩ := hinv.witness
  obtain ha := hw_inv.arena
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain haca : c.arena_cap < 2 * dimacsBound := c.harena
  obtain hsca : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmax haca hsca
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain harl := hlen.core_ok.arena_len_arr
  obtain hale := hlen.core_ok.arena_len_le
  obtain hvl := hlen.core_ok.vals_len
  have hnl_eq : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega), Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hsh_mc : (max_cl <<< (1 : Nat)).toNat = 2 * max_cl.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have hsh_mc4 : (max_cl <<< (2 : Nat)).toNat = 4 * max_cl.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  c0_hsteps_nogrp
  -- Loop 1: prefix sums (`occ_off`, `occ_len`, `occ_cur`)
  refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
    (fun s1 (acc, l, ()) =>
      l.toNat ≤ 2 * s.core.cur_vars ∧ acc.toNat ≤ occ_cap.toNat ∧
      s1.scratch.scratch_buf = s.scratch.scratch_buf ∧ FullExtScratchPres s s1)
    (fun (_, l, ()) => 2 * s.core.cur_vars - l.toNat)
    (fun J1 hJ1 => by
      c0_hsteps; exact hJ1 s (0#64, 0#64, ()) m hm rfl hlen ⟨by simp, by simp, rfl, ⟨rfl, rfl⟩⟩)
    (fun J1 s1 (acc, l, ()) m1 hcore1 hs1 ⟨hlle, hacc, hsb1, hpres1⟩ hm1 hJ1 => ?_)
  dsimp only [fullSafetySlice] at hs1 hm1
  have hceq1 : s1.core = s.core := hcore1
  obtain hws1l := hs1.scratch_ok.work_stk1_len
  obtain hws2l := hs1.scratch_ok.work_stk2_len
  obtain html := hs1.scratch_ok.tarjan_mark_len
  c0_hsteps_nogrp
  · have hllt : l.toNat < 2 * s.core.cur_vars := by
      have h1 : l.toNat < 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by assumption
      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at h1
      exact h1
    have hl_w1 : l.toNat < s1.scratch.work_stk1.length := by rw [hws1l]; omega
    have hl_w2 : l.toNat < s1.scratch.work_stk2.length := by rw [hws2l]; omega
    have hl_tm : l.toNat < s1.scratch.tarjan_mark.length := by rw [html]; omega
    have hl1 : (l + 1#64).toNat = l.toNat + 1 := m6_add1_64 (by omega)
    have hrem : (occ_cap - acc).toNat = occ_cap.toNat - acc.toNat := m6_sub_64 hacc
    c0_hsteps
    · exact hJ1 _ (acc + (occ_cap - acc), l + 1#64, ()) _ hm (by dsimp only; omega) rfl
        (hs1.with_scratch { hs1.scratch_ok with
          work_stk1_len := by rw [List.length_set]; exact hws1l
          work_stk2_len := by rw [List.length_set]; exact hws2l
          tarjan_mark_len := by rw [List.length_set]; exact html })
        ⟨by omega, by rw [BitVec.toNat_add, hrem, Nat.mod_eq_of_lt (by omega)]; omega,
          hsb1, hpres1⟩
    · have hdeg_le : (s1.scratch.work_stk2[l.toNat]'hl_w2).toNat ≤ occ_cap.toNat - acc.toNat := by
        have : ¬(occ_cap - acc).toNat < (s1.scratch.work_stk2[l.toNat]'hl_w2).toNat := by assumption
        omega
      exact hJ1 _ (acc + (s1.scratch.work_stk2[l.toNat]'hl_w2).setWidth 64, l + 1#64, ()) _ hm
        (by dsimp only; omega) rfl
        (hs1.with_scratch { hs1.scratch_ok with
          work_stk1_len := by rw [List.length_set]; exact hws1l
          tarjan_mark_len := by rw [List.length_set]; exact html })
        ⟨by omega, by
          rw [BitVec.toNat_add, zext_toNat _ (by decide), Nat.mod_eq_of_lt (by omega)]
          omega, hsb1, hpres1⟩
  · -- Loop 2: populate CSR `occ_flat`, `sat_cnt`, `unsat_pos`, `unsat_list`
    clear J1 hJ1
    have hok1 : FullWalkEntriesOk s1 ncl.toNat :=
      m6_walkEntriesOk_of_scr_eq hok0 hceq1 fun i _ => by rw [hsb1]
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
      (fun s2 (ulen, ci, ()) =>
        ci.toNat ≤ ncl.toNat ∧ ulen.toNat ≤ ncl.toNat ∧
        FullWalkEntriesOk s2 ncl.toNat ∧ FullExtScratchPres s s2)
      (fun (_, ci, ()) => ncl.toNat - ci.toNat)
      (fun J2 hJ2 => by
        c0_hsteps; exact hJ2 s1 (0#64, 0#64, ()) m1 hm1 rfl hs1 ⟨by simp, by simp, hok1, hpres1⟩)
      (fun J2 s2 (ulen, ci, ()) m2 hcore2 hs2 ⟨hcile, hul_le, hok2, hpres2⟩ hm2 hJ2 => ?_)
    dsimp only [fullSafetySlice] at hs2 hm2
    have hceq2 : s2.core = s.core := Eq.trans hcore2 hceq1
    obtain hsbl2 := hs2.scratch_ok.scratch_buf_len
    obtain hwvl2 := hs2.scratch_ok.walk_vals_len
    obtain html2 := hs2.scratch_ok.tarjan_mark_len
    c0_hsteps_nogrp
    · have hcilt : ci.toNat < ncl.toNat := by assumption
      have h2ci : (ci <<< (1 : Nat)).toNat = 2 * ci.toNat := by
        rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
      have h2ci_lt : 2 * ci.toNat < s2.scratch.scratch_buf.length := by rw [hsbl2]; omega
      have h2ci1_lt : 2 * ci.toNat + 1 < s2.scratch.scratch_buf.length := by rw [hsbl2]; omega
      have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by bv_omega
      have hent := hok2 ci.toNat hcilt
      unfold FullWalkEntryOk at hent
      -- Join after computing `sc` and populating `occ_flat` -> write `sat_cnt`/`upos`/`ulist`
      refine wp_join_group (ts := [i32])
        (fun (_sc, ()) m3 => ∃ s3 : FullState,
          PreservesCoreSlice FullState.core s s3 ∧ s3.LengthsOk c ∧
          FullWalkEntriesOk s3 ncl.toNat ∧ FullExtScratchPres s s3 ∧ (FullMem c s3 ⋆ R) m3)
        (fun _ ⟨sc, ⟨⟩⟩ m3 ⟨s3, hcore3, hs3, hok3, hpres3, hm3⟩ => ?_)
        (fun Jsc hJsc => ?_)
      · obtain hsbl3 := hs3.scratch_ok.scratch_buf_len
        have hsat_idx : ((max_cl <<< (1 : Nat)) + ci).toNat = 2 * max_cl.toNat + ci.toNat := by
          rw [BitVec.toNat_add, hsh_mc, Nat.mod_eq_of_lt (by omega)]
        have hsat_lt : ((max_cl <<< (1 : Nat)) + ci).toNat < s3.scratch.scratch_buf.length := by
          rw [hsat_idx, hsbl3]; omega
        have hup_idx : (max_cl * 3 + ci).toNat = 3 * max_cl.toNat + ci.toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_mul, show (3 : BitVec 64).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by omega : max_cl.toNat * 3 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : max_cl.toNat * 3 + ci.toNat < 2 ^ 64)]; omega
        have hup_lt : (max_cl * 3 + ci).toNat < s3.scratch.scratch_buf.length := by
          rw [hup_idx, hsbl3]; omega
        have hul_idx : ((max_cl <<< (2 : Nat)) + ulen).toNat = 4 * max_cl.toNat + ulen.toNat := by
          rw [BitVec.toNat_add, hsh_mc4, Nat.mod_eq_of_lt (by omega)]
        c0_hsteps
        · have hul_lt : ulen.toNat < ncl.toNat := by assumption
          have hul_sb : ((max_cl <<< (2 : Nat)) + ulen).toNat < s3.scratch.scratch_buf.length := by
            rw [hul_idx, hsbl3]; omega
          have hul1 : (ulen + 1#64).toNat = ulen.toNat + 1 := m6_add1_64 (by omega)
          c0_hsteps
          exact hJ2 _ (ulen + 1#64, ci + 1#64, ()) _ hm (by dsimp only; omega)
            (Eq.trans hcore3 hceq2.symm)
            (hs3.with_scratch { hs3.scratch_ok with
              scratch_buf_len := by
                rw [List.length_set, List.length_set, List.length_set]; exact hsbl3 })
            ⟨by omega, by omega,
              m6_walkEntriesOk_set_hi (m6_walkEntriesOk_set_hi
                (m6_walkEntriesOk_set_hi hok3 (by rw [hsat_idx]; omega))
                (by rw [hup_idx]; omega)) (by rw [hul_idx]; omega),
              hpres3⟩
        · exact hJ2 _ (ulen, ci + 1#64, ()) _ hm (by dsimp only; omega)
            (Eq.trans hcore3 hceq2.symm)
            (hs3.with_scratch { hs3.scratch_ok with
              scratch_buf_len := by rw [List.length_set, List.length_set]; exact hsbl3 })
            ⟨by omega, hul_le,
              m6_walkEntriesOk_set_hi
                (m6_walkEntriesOk_set_hi hok3 (by rw [hsat_idx]; omega))
                (by rw [hup_idx]; omega),
              hpres3⟩
        · exact hJ2 _ (ulen, ci + 1#64, ()) _ hm (by dsimp only; omega)
            (Eq.trans hcore3 hceq2.symm)
            (hs3.with_scratch { hs3.scratch_ok with
              scratch_buf_len := by rw [List.length_set, List.length_set]; exact hsbl3 })
            ⟨by omega, hul_le,
              m6_walkEntriesOk_set_hi
                (m6_walkEntriesOk_set_hi hok3 (by rw [hsat_idx]; omega))
                (by rw [hup_idx]; omega),
              hpres3⟩
      · -- Compute `sc` and populate `occ_flat` for clause `ci`
        have h2ci_lt' : (ci <<< (1 : Nat)).toNat < s2.scratch.scratch_buf.length := by
          rw [h2ci]; exact h2ci_lt
        let w0 := s2.scratch.scratch_buf[(ci <<< (1 : Nat)).toNat]'h2ci_lt'
        have hw0_at : s2.scratch.scratch_buf[2 * ci.toNat]?.getD 0#32 = w0 := by
          have hw0_eq : s2.scratch.scratch_buf[2 * ci.toNat]'h2ci_lt = w0 := by
            simp only [w0, h2ci]
          rw [List.getElem?_eq_getElem h2ci_lt, Option.getD_some, hw0_eq]
        have h2ci_mod : 2 * ci.toNat % 2 ^ 64 = 2 * ci.toNat := Nat.mod_eq_of_lt (by omega)
        have h2ci1_eq : ((ci <<< (1 : Nat)) + 1#64).toNat = 2 * ci.toNat + 1 := by
          rw [BitVec.toNat_add, h2ci, show (1#64 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have h2ci1_lt' : ((ci <<< (1 : Nat)) + 1#64).toNat < s2.scratch.scratch_buf.length := by
          rw [h2ci1_eq]; exact h2ci1_lt
        c0_hsteps_nogrp
        · -- Binary clause entry
          have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
            have hw_eq : s2.scratch.scratch_buf[2 * ci.toNat % 2 ^ 64]'(by
                rw [h2ci_mod]; exact h2ci_lt) = w0 := by simp only [w0, h2ci, h2ci_mod]
            rw [← hw_eq]; exact hc
          rw [hw0_at, ite_eq_left hbin] at hent
          obtain ⟨ha_lt, hb_lt⟩ := hent
          rw [hceq2] at ha_lt hb_lt
          have ha_v : (w0 &&& 0x7FFFFFFF#32).toNat < s2.core.vals.length := by
            rw [hceq2, hvl]; omega
          have ha_wv : (w0 &&& 0x7FFFFFFF#32).toNat < s2.scratch.walk_vals.length := by
            rw [hwvl2]; omega
          have ha_tm : (w0 &&& 0x7FFFFFFF#32).toNat < s2.scratch.tarjan_mark.length := by
            rw [html2]; omega
          have hb_eq : (s2.scratch.scratch_buf[((ci <<< (1 : Nat)) + 1#64).toNat]'h2ci1_lt').toNat <
              2 * s.core.cur_vars := by
            have hb' : (s2.scratch.scratch_buf[2 * ci.toNat + 1]'h2ci1_lt).toNat <
                2 * s.core.cur_vars := by
              rw [List.getElem?_eq_getElem h2ci1_lt, Option.getD_some] at hb_lt; exact hb_lt
            simpa only [h2ci1_eq] using hb'
          -- Join after literal `a`
          refine wp_join_group (ts := [i32])
            (fun (_sc1, ()) m_a => ∃ s_a : FullState,
              PreservesCoreSlice FullState.core s s_a ∧ s_a.LengthsOk c ∧
              FullWalkEntriesOk s_a ncl.toNat ∧ FullExtScratchPres s s_a ∧ (FullMem c s_a ⋆ R) m_a)
            (fun _ ⟨sc1, ⟨⟩⟩ m_a ⟨s_a, hcore_a, hs_a, hok_a, hpres_a, hm_a⟩ => ?_)
            (fun Ja hJa => ?_)
          · obtain hsbl_a := hs_a.scratch_ok.scratch_buf_len
            obtain hwvl_a := hs_a.scratch_ok.walk_vals_len
            obtain html_a := hs_a.scratch_ok.tarjan_mark_len
            let b_lit := s2.scratch.scratch_buf[((ci <<< (1 : Nat)) + 1#64).toNat]'h2ci1_lt'
            have hb_z : (b_lit.setWidth 64).toNat = b_lit.toNat := zext_toNat _ (by decide)
            have hb_v : (b_lit.setWidth 64).toNat < s_a.core.vals.length := by
              rw [hb_z, hcore_a, hvl]; exact Nat.lt_of_lt_of_le hb_eq (by omega)
            have hb_wv : (b_lit.setWidth 64).toNat < s_a.scratch.walk_vals.length := by
              rw [hb_z, hwvl_a]; exact Nat.lt_of_lt_of_le hb_eq (by omega)
            have hb_tm : (b_lit.setWidth 64).toNat < s_a.scratch.tarjan_mark.length := by
              rw [hb_z, html_a]; exact Nat.lt_of_lt_of_le hb_eq (by omega)
            clear hinv hw_inv ha hQ hJ2 haca harl hale hsh_mc hsh_mc4 hnl_eq hok0 hok1 hok2
            refine wp_join_group (ts := [i32])
              (fun (_sc2, ()) m_w => ∃ s_w : FullState,
                PreservesCoreSlice FullState.core s s_w ∧ s_w.LengthsOk c ∧
                FullWalkEntriesOk s_w ncl.toNat ∧ FullExtScratchPres s s_w ∧
                (FullMem c s_w ⋆ R) m_w)
              (fun _ ⟨sc2, ⟨⟩⟩ m_w ⟨s_w, hcore_w, hs_w, hok_w, hpres_w, hm_w⟩ => by
                c0_hsteps; exact hJsc (sc2, ()) m_w
                  ⟨s_w, hcore_w, hs_w, hok_w, hpres_w, hm_w⟩)
              (fun Jb hJb => ?_)
            c0_hsteps_nogrp
            · refine wp_join_group (ts := [i32]) (fun (_sc2, ()) m_w => m_w = m_a)
                (fun _ ⟨sc2, ⟨⟩⟩ m_w hm_w => ?_) (fun Jw hJw => ?_)
              · subst hm_w
                c0_hsteps_nogrp
                refine wp_join_group (ts := [])
                  (fun () m_o => ∃ s_o : FullState,
                    PreservesCoreSlice FullState.core s s_o ∧ s_o.LengthsOk c ∧
                    FullWalkEntriesOk s_o ncl.toNat ∧ FullExtScratchPres s s_o ∧
                    (FullMem c s_o ⋆ R) m_o)
                  (fun _ () m_o ⟨s_o, hcore_o, hs_o, hok_o, hpres_o, hm_o⟩ => by
                    c0_hsteps; exact hJb (sc2, ()) m_o
                      ⟨s_o, hcore_o, hs_o, hok_o, hpres_o, hm_o⟩)
                  (fun Jo hJo => ?_)
                c0_hsteps_nogrp
                · have hpos_b : (s_a.scratch.tarjan_mark[
                      (b_lit.setWidth 64).toNat]'hb_tm).toNat < occ_cap.toNat := by
                    have h1 : (s_a.scratch.tarjan_mark[b_lit.toNat]'(by
                        rw [← hb_z]; exact hb_tm)).toNat < occ_cap.toNat := by
                      simpa only [b_lit, h2ci1_eq, BitVec.toNat_add,
                        show (1 : BitVec 64).toNat = 1 from rfl, h2ci,
                        Nat.mod_eq_of_lt (by omega : 2 * ci.toNat + 1 < 2 ^ 64)] using hc
                    simpa only [hb_z] using h1
                  have hocc := m6_occ_idx hcap (by omega) hpos_b
                  have hocc_lt : (max_cl * 5 + (s_a.scratch.tarjan_mark[
                      (b_lit.setWidth 64).toNat]'hb_tm).setWidth 64).toNat <
                      s_a.scratch.scratch_buf.length := by rw [hsbl_a]; exact hocc.2.1
                  c0_hsteps
                  refine hJo () _ ⟨_, ?_, ?_, ?_, ?_, hm⟩
                  · exact hcore_a
                  · exact hs_a.with_scratch { hs_a.scratch_ok with
                      scratch_buf_len := by rw [List.length_set]; exact hsbl_a
                      tarjan_mark_len := by rw [List.length_set]; exact html_a }
                  · exact m6_walkEntriesOk_set_hi_upd hok_a rfl rfl
                      (Nat.le_trans (by omega) hocc.2.2)
                  · exact hpres_a
                · exact hJo () m_w ⟨s_a, hcore_a, hs_a, hok_a, hpres_a, hm_a⟩
              · c0_hsteps
                · exact hJw (sc1 + 1#32, ()) m_a rfl
                · exact hJw (sc1, ()) m_a rfl
            · exact hJb (sc1, ()) m_a ⟨s_a, hcore_a, hs_a, hok_a, hpres_a, hm_a⟩
          · have ha_z : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat =
                (w0 &&& 0x7FFFFFFF#32).toNat := zext_toNat _ (by decide)
            have ha_v' : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < s2.core.vals.length := by
              rw [ha_z]; exact ha_v
            have ha_wv' : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                s2.scratch.walk_vals.length := by rw [ha_z]; exact ha_wv
            have ha_tm' : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                s2.scratch.tarjan_mark.length := by rw [ha_z]; exact ha_tm
            clear hinv hw_inv ha hQ hJ2 haca harl hale hsh_mc hsh_mc4 hnl_eq hok0 hok1
            c0_hsteps_nogrp
            · refine wp_join_group (ts := [i32]) (fun (_sc1, ()) m_w => m_w = m2)
                (fun _ ⟨sc1, ⟨⟩⟩ m_w hm_w => ?_) (fun Jw hJw => ?_)
              · subst hm_w
                c0_hsteps_nogrp
                refine wp_join_group (ts := [])
                  (fun () m_o => ∃ s_o : FullState,
                    PreservesCoreSlice FullState.core s s_o ∧ s_o.LengthsOk c ∧
                    FullWalkEntriesOk s_o ncl.toNat ∧ FullExtScratchPres s s_o ∧
                    (FullMem c s_o ⋆ R) m_o)
                  (fun _ () m_o ⟨s_o, hcore_o, hs_o, hok_o, hpres_o, hm_o⟩ => by
                    c0_hsteps; exact hJa (sc1, ()) m_o
                      ⟨s_o, hcore_o, hs_o, hok_o, hpres_o, hm_o⟩)
                  (fun Jo hJo => ?_)
                c0_hsteps_nogrp
                · have hpos_a : (s2.scratch.tarjan_mark[
                      ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat]'ha_tm').toNat <
                      occ_cap.toNat := by
                    have h1 : (s2.scratch.tarjan_mark[(w0 &&& 2147483647).toNat]'ha_tm).toNat <
                        occ_cap.toNat := by simpa only [w0, h2ci, h2ci_mod] using hc
                    change (s2.scratch.tarjan_mark[(w0 &&& 0x7FFFFFFF#32).toNat]'ha_tm).toNat <
                      occ_cap.toNat at h1
                    simpa only [ha_z] using h1
                  have hocc := m6_occ_idx hcap (by omega) hpos_a
                  have hocc_lt : (max_cl * 5 + (s2.scratch.tarjan_mark[
                      ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat]'ha_tm').setWidth 64).toNat <
                      s2.scratch.scratch_buf.length := by rw [hsbl2]; exact hocc.2.1
                  c0_hsteps
                  refine hJo () _ ⟨_, ?_, ?_, ?_, ?_, hm⟩
                  · exact hceq2
                  · exact hs2.with_scratch { hs2.scratch_ok with
                      scratch_buf_len := by rw [List.length_set]; exact hsbl2
                      tarjan_mark_len := by rw [List.length_set]; exact html2 }
                  · exact m6_walkEntriesOk_set_hi_upd hok2 rfl rfl
                      (Nat.le_trans (by omega) hocc.2.2)
                  · exact hpres2
                · exact hJo () m_w ⟨s2, hceq2, hs2, hok2, hpres2, hm2⟩
              · c0_hsteps
                · exact hJw (1#32, ()) m2 rfl
                · exact hJw (0#32, ()) m2 rfl
            · exact hJa (0#32, ()) m2 ⟨s2, hceq2, hs2, hok2, hpres2, hm2⟩
        · -- Large clause entry
          have hlg : (w0 &&& 0x80000000#32) = 0#32 := by
            have hw_eq : s2.scratch.scratch_buf[2 * ci.toNat % 2 ^ 64]'(by
                rw [h2ci_mod]; exact h2ci_lt) = w0 := by simp only [w0, h2ci, h2ci_mod]
            rw [← hw_eq]; exact hc
          rw [hw0_at, ite_eq_right (by simp [hlg])] at hent
          obtain ⟨hw0_ref, hw0_ng⟩ := hent
          have hw0_ref' : w0.toNat ∈ fullArenaClauseRefsCore s.core := by
            change w0.toNat ∈ fullArenaClauseRefsCore s2.core at hw0_ref
            rw [hceq2] at hw0_ref; exact hw0_ref
          have hw0_ng' : fullArenaClauseGarbCore s.core w0.toNat = false := by
            change fullArenaClauseGarbCore s2.core w0.toNat = false at hw0_ng
            rwa [hceq2] at hw0_ng
          have hwf := ha.refs_wf w0.toNat hw0_ref'
          have hwf1 := hwf.1; have hwf3 := hwf.2.2.1; have hwf4 := hwf.2.2.2.1
          have hw02_idx : (w0.setWidth 64 + 2#64).toNat = w0.toNat + 2 := by
            rw [BitVec.toNat_add, zext_toNat _ (by decide),
              show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
          have hw02_ar : (w0.setWidth 64 + 2#64).toNat < s2.core.arena.length := by
            rw [hw02_idx, hceq2, harl]; omega
          have hsz_eq : (s2.core.arena[(w0.setWidth 64 + 2#64).toNat]'hw02_ar).toNat =
              fullArenaClauseSizeCore s.core w0.toNat := by
            have h1 : s2.core.arena[(w0.setWidth 64 + 2#64).toNat]'hw02_ar =
                s.core.arena[w0.toNat + 2]'(by rw [harl]; omega) := by
              simp only [hceq2, hw02_idx]
            rw [h1]; unfold fullArenaClauseSizeCore
            rw [List.getElem?_eq_getElem (by rw [harl]; omega), Option.getD_some]
          c0_hsteps_nogrp
          refine wp_loop_safety_slice_pure (fullSafetySlice c) s2 R
            (fun sk (_sck, k, ()) =>
              k.toNat ≤ fullArenaClauseSizeCore s.core w0.toNat ∧
              FullWalkEntriesOk sk ncl.toNat ∧ FullExtScratchPres s sk)
            (fun (_, k, ()) => fullArenaClauseSizeCore s.core w0.toNat - k.toNat)
            (fun Jk hJk => by
              c0_hsteps; exact hJk s2 (0#32, 0#32, ()) m2 hm2 rfl hs2 ⟨by simp, hok2, hpres2⟩)
            (fun Jk sk (sck, k, ()) mk hcorek hsk ⟨hkle, hokk, hpresk⟩ hmk hJk => ?_)
          dsimp only [fullSafetySlice] at hsk hmk
          have hceqk : sk.core = s.core := Eq.trans hcorek hceq2
          obtain hsblk := hsk.scratch_ok.scratch_buf_len
          obtain hwvlk := hsk.scratch_ok.walk_vals_len
          obtain htmlk := hsk.scratch_ok.tarjan_mark_len
          c0_hsteps_nogrp
          · have hklt : k.toNat < fullArenaClauseSizeCore s.core w0.toNat := by
              have : k.toNat < (s2.core.arena[(w0.setWidth 64 + 2#64).toNat]'hw02_ar).toNat := by
                assumption
              omega
            have hk_idx : (w0.setWidth 64 + 3#64 + k.setWidth 64).toNat =
                w0.toNat + 3 + k.toNat := by
              rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat _ (by decide),
                zext_toNat _ (by decide), show (3#64 : BitVec 64).toNat = 3 from rfl,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            have hk_ar : (w0.setWidth 64 + 3#64 + k.setWidth 64).toNat < sk.core.arena.length := by
              rw [hk_idx, hceqk, harl]; omega
            let lit := sk.core.arena[(w0.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hk_ar
            have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
              have hmem : (s.core.arena[w0.toNat + 3 + k.toNat]'(by rw [harl]; omega)).toNat ∈
                  fullArenaClauseLitsCore s.core w0.toNat := by
                unfold fullArenaClauseLitsCore
                refine List.mem_map.mpr ⟨_, ?_, rfl⟩
                have hlt : k.toNat < ((s.core.arena.drop (w0.toNat + 3)).take
                    (fullArenaClauseSizeCore s.core w0.toNat)).length := by
                  rw [List.length_take, List.length_drop, harl]; omega
                simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt
              have := ha.lits_lt w0.toNat hw0_ref' hw0_ng' _ hmem
              simpa only [lit, hceqk, hk_idx] using this
            have hlit_z : (lit.setWidth 64).toNat = lit.toNat := zext_toNat _ (by decide)
            have hlit_v : (lit.setWidth 64).toNat < sk.core.vals.length := by
              rw [hlit_z, hceqk, hvl]; omega
            have hlit_wv : (lit.setWidth 64).toNat < sk.scratch.walk_vals.length := by
              rw [hlit_z, hwvlk]; omega
            have hlit_tm : (lit.setWidth 64).toNat < sk.scratch.tarjan_mark.length := by
              rw [hlit_z, htmlk]; omega
            have hk1 : (k + 1#32).toNat = k.toNat + 1 := m6_add1_32 (by omega)
            clear hinv hw_inv ha hQ hJ2 hsh_mc hsh_mc4 hnl_eq hok0 hok1 hok2
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32])
              (fun (_sck', ()) m_k => ∃ s_k : FullState,
                PreservesCoreSlice (fullSafetySlice c).coreProj sk s_k ∧ s_k.LengthsOk c ∧
                FullWalkEntriesOk s_k ncl.toNat ∧ FullExtScratchPres s s_k ∧
                (FullMem c s_k ⋆ R) m_k)
              (fun _ ⟨sck', ⟨⟩⟩ m_k ⟨s_k, hcore_k, hs_k, hok_k, hpres_k, hm_k⟩ => by
                c0_hsteps
                exact hJk s_k (sck', k + 1#32, ()) m_k hm_k (by dsimp only; omega)
                  hcore_k hs_k ⟨by omega, hok_k, hpres_k⟩)
              (fun Jlit hJlit => ?_)
            c0_hsteps_nogrp
            · refine wp_join_group (ts := [i32]) (fun (_sck', ()) m_w => m_w = mk)
                (fun _ ⟨sck', ⟨⟩⟩ m_w hm_w => ?_) (fun Jw hJw => ?_)
              · subst hm_w
                c0_hsteps_nogrp
                refine wp_join_group (ts := [])
                  (fun () m_o => ∃ s_o : FullState,
                    PreservesCoreSlice (fullSafetySlice c).coreProj sk s_o ∧ s_o.LengthsOk c ∧
                    FullWalkEntriesOk s_o ncl.toNat ∧ FullExtScratchPres s s_o ∧
                    (FullMem c s_o ⋆ R) m_o)
                  (fun _ () m_o ⟨s_o, hcore_o, hs_o, hok_o, hpres_o, hm_o⟩ => by
                    c0_hsteps
                    exact hJlit (sck', ()) m_o ⟨s_o, hcore_o, hs_o, hok_o, hpres_o, hm_o⟩)
                  (fun Jo hJo => ?_)
                c0_hsteps_nogrp
                · have hpos_l : (sk.scratch.tarjan_mark[
                      (lit.setWidth 64).toNat]'hlit_tm).toNat < occ_cap.toNat := by
                    have h1 : (sk.scratch.tarjan_mark[lit.toNat]'(by
                        rw [← hlit_z]; exact hlit_tm)).toNat < occ_cap.toNat := by
                      simp only [lit, hk_idx]
                      have hmod : (s2.scratch.scratch_buf[2 * ci.toNat]'h2ci_lt).toNat + 3 +
                          k.toNat < 2 ^ 64 := by
                        have : s2.scratch.scratch_buf[2 * ci.toNat]'h2ci_lt = w0 := by
                          simp only [w0, h2ci]
                        rw [this]; omega
                      simpa only [w0, h2ci, h2ci_mod, show (3 : BitVec 64).toNat = 3 from rfl,
                        Nat.mod_eq_of_lt hmod] using hc
                    simpa only [hlit_z] using h1
                  have hocc := m6_occ_idx hcap (by omega) hpos_l
                  have hocc_lt : (max_cl * 5 + (sk.scratch.tarjan_mark[
                      (lit.setWidth 64).toNat]'hlit_tm).setWidth 64).toNat <
                      sk.scratch.scratch_buf.length := by rw [hsblk]; exact hocc.2.1
                  c0_hsteps
                  refine hJo () _ ⟨_, ?_, ?_, ?_, ?_, hm⟩
                  · exact rfl
                  · exact hsk.with_scratch { hsk.scratch_ok with
                      scratch_buf_len := by rw [List.length_set]; exact hsblk
                      tarjan_mark_len := by rw [List.length_set]; exact htmlk }
                  · exact m6_walkEntriesOk_set_hi_upd hokk rfl rfl
                      (Nat.le_trans (by omega) hocc.2.2)
                  · exact hpresk
                · exact hJo () m_w ⟨sk, rfl, hsk, hokk, hpresk, hmk⟩
              · c0_hsteps
                · exact hJw (sck + 1#32, ()) mk rfl
                · exact hJw (sck, ()) mk rfl
            · exact hJlit (sck, ()) mk ⟨sk, rfl, hsk, hokk, hpresk, hmk⟩
          · exact hJsc (sck, ()) mk ⟨sk, hceqk, hsk, hokk, hpresk, hmk⟩
    · exact hQ (ulen, ()) s2 m2 hceq2 hs2 ⟨hpres2, hul_le, hok2⟩ hm2

end WalkBuildCsrProof

end LeanQbe.T.Examples.Kissat.FullM6WalkParse
