/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Mem
public import LeanQbe.T.Examples.Kissat.Proof.Ref.Subsume
public import LeanQbe.T.Examples.Kissat.Ref.Sweep

/-!
# Shared Congruence Proof Invariants & Pure Semantic Lemmas

Pure and invariant helpers shared across `Proof.Congruence.Wp*` shards:
1. `FullDenseInvW`, `FullWitnessInv`, `FullLitMarksClear`, `FullArenaVarsNodup`, and
   `FullExtScratchOk` preservation lemmas across core and scratch updates.
2. Signed/unsigned `i8` domain, literal negation, valuation-entailment, and arena helpers.
3. Union-find root (`congRoot`) and `FullCongReprInv` lemmas.
4. Unified `CongGateAt` / `CongGateSeqOk` / `CongHtInv` / `CongCtrlLayout` / `xorEvalList`
   transport and semantic gate lemmas.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

public section

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

/-! ## 1. `FullMem` Focusing Wrappers & `FullDenseInvW` Frame Lemmas -/

theorem focus_full_repr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pRepr s.core.repr ⋆ (ArrayField.repr.rest c s ⋆ R)) m :=
  ArrayField.repr.focus hm

theorem unfocus_full_repr {c : FullCfg} {s : FullState} {repr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pRepr repr' ⋆ (ArrayField.repr.rest c s ⋆ R)) m) :
    (FullMem c { s with core := { s.core with repr := repr' } } ⋆ R) m :=
  ArrayField.repr.unfocus hm

theorem focus_full_tmp {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pTmp s.core.tmp ⋆ (ArrayField.tmp.rest c s ⋆ R)) m :=
  ArrayField.tmp.focus hm

theorem unfocus_full_tmp {c : FullCfg} {s : FullState} {tmp' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pTmp tmp' ⋆ (ArrayField.tmp.rest c s ⋆ R)) m) :
    (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m :=
  ArrayField.tmp.unfocus hm

theorem focus_full_ws1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      (ArrayField.work_stk1.rest c s ⋆ R)) m :=
  ArrayField.work_stk1.focus hm

theorem unfocus_full_ws1 {c : FullCfg} {s : FullState} {ws1' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pWorkStk1 ws1' ⋆ (ArrayField.work_stk1.rest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m :=
  ArrayField.work_stk1.unfocus hm

theorem focus_full_scratch_buf {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
      (ArrayField.scratch_buf.rest c s ⋆ R)) m :=
  ArrayField.scratch_buf.focus hm

theorem unfocus_full_scratch_buf {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pScratchBuf scr' ⋆
      (ArrayField.scratch_buf.rest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m :=
  ArrayField.scratch_buf.unfocus hm

theorem fullLitMarksClear_of_eq {c : FullCfg} {s s' : FullState}
    (h : FullLitMarksClear c s) (h1 : s'.core.mrk = s.core.mrk)
    (h2 : s'.core.lit_mark = s.core.lit_mark) : FullLitMarksClear c s' :=
  ⟨fun v hv => by rw [h1]; exact h.1 v hv, fun l hl => by rw [h2]; exact h.2 l hl⟩

theorem fullArenaVarsNodup_of_eq {s s' : FullState} (h : FullArenaVarsNodup s)
    (h1 : s'.core.arena = s.core.arena) (h2 : s'.core.arena_len = s.core.arena_len) :
    FullArenaVarsNodup s' := by
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore fullArenaClauseGarb
    fullArenaClauseGarbCore fullArenaHdrCore fullArenaClauseLits fullArenaClauseLitsCore
    fullArenaClauseSizeCore at h ⊢
  rw [h1, h2]; exact h

theorem fullExtScratchOk_of_eq {c : FullCfg} {s s' : FullState} (h : FullExtScratchOk c s)
    (h1 : s'.core.arena = s.core.arena) (h2 : s'.core.arena_len = s.core.arena_len)
    (h3 : s'.scratch.last_learned = s.scratch.last_learned)
    (h4 : s'.scratch.extend_len = s.scratch.extend_len) : FullExtScratchOk c s' := by
  refine ⟨fun i hi => ?_, by rw [h4]; exact h.2⟩
  have hll := h.1 i hi; dsimp only [fullArenaClauseRefs, fullArenaClauseRefsCore] at hll ⊢
  rw [h1, h2, h3]; exact hll

theorem fullWitnessInv_with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (repr' : List (BitVec 32)) :
    FullWitnessInv c F0 F_cur { k with repr := repr' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullWitnessInv_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (tmp' : List (BitVec 32)) :
    FullWitnessInv c F0 F_cur { k with tmp := tmp' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullWitnessInv_with_tmp_lm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (tmp' : List (BitVec 32)) (lm' : List (BitVec 8)) :
    FullWitnessInv c F0 F_cur { k with tmp := tmp', lit_mark := lm' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullWitnessInv_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (oom' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with oom := oom' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullWitnessInv_with_inconsistent {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (inc' : BitVec 64)
    (hu : inc' ≠ 0#64 → (cnfOfClauses F_cur).Unsat) :
    FullWitnessInv c F0 F_cur { k with inconsistent := inc' } :=
  { hw with
    inconsistent_sound := hu
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullDenseInvW_with_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s) {scr' : List (BitVec 32)}
    (hl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := scr' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with scratch_buf_len := hl }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_ws1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s) {ws1' : List (BitVec 32)}
    (hl : ws1'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with work_stk1_len := hl }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_ws2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s) {ws2' : List (BitVec 32)}
    (hl : ws2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk2 := ws2' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with work_stk2_len := hl }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_rr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s) {rr' : List (BitVec 32)}
    (hl : rr'.length = c.red_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with red_refs_len := hl }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_rsz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s) (rsz' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with res_sz := rsz' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_antsz_ressz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s) (asz' rsz' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with ant_sz := asz', res_sz := rsz' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s) {repr' : List (BitVec 32)}
    (hr : repr'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with repr := repr' } } :=
  ⟨⟨{ hd.1.core_ok with repr_len := hr }, hd.1.scratch_ok⟩,
   fullWitnessInv_with_repr hd.2.1 repr', hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_cong_cnt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s) (cc' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with cong_cnt := cc' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fullAddUnitSpec_fullDenseInvW {c : FullCfg}
    {s s' : FullState} (hmk : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s)
    (hext : FullExtScratchOk c s) (hdm : s.core.dense_mode ≠ 0#64)
    (hcl' : s'.core.cur_level = 0)
    (hmrk' : s'.core.mrk = s.core.mrk) (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (har' : s'.core.arena = s.core.arena) (hal' : s'.core.arena_len = s.core.arena_len)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len)
    (hdm' : s'.core.dense_mode = s.core.dense_mode) :
    FullLitMarksClear c s' ∧ FullArenaVarsNodup s' ∧ FullExtScratchOk c s' ∧
    s'.core.cur_level = 0 ∧ s'.core.dense_mode ≠ 0#64 :=
  ⟨fullLitMarksClear_of_eq hmk hmrk' hlm', fullArenaVarsNodup_of_eq hnd har' hal',
   fullExtScratchOk_of_eq hext har' hal' hll' hext', hcl', hdm' ▸ hdm⟩

theorem unsat_of_inconsistent_w {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hinc : k.inconsistent ≠ 0#64) :
    F0.Unsat :=
  hw.ext_sound.2 (hw.inconsistent_sound hinc)

theorem fullWatchBounds_of_dense {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s) :
    ∀ l < 2 * s.core.cur_vars,
      fullWatchOffCore s.core l + fullWatchSizeCore s.core l ≤ c.wcap := by
  intro l hl
  have hw_le := hd.1.core_ok.wlen_le
  have hwt := hd.2.1.watches
  unfold ModeWatchesInv at hwt
  split at hwt
  · exact Nat.le_trans (hwt.layout.bounds l hl) hw_le
  · exact Nat.le_trans (hwt.layout.bounds l hl) hw_le

/-! ## 2. Signed `i8`, Literal Parity, Arena, and Entailment Helpers -/

theorem bv8_ne0_of_signExtend32 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hne : v.signExtend 32 ≠ 0#32) : v ≠ 0#8 := by
  intro rfl; exact hne (by decide)

theorem bv8_eq0_of_signExtend32 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (heq : v.signExtend 32 = 0#32) : v = 0#8 := by
  rcases hdom with rfl | rfl | rfl
  · rfl
  · exact absurd heq (by decide)
  · exact absurd heq (by decide)

theorem bv8_eq1_of_signExtend32_sgt0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hsgt : (0#32 : BitVec 32).slt (v.signExtend 32) = true) :
    v = 1#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd hsgt (by decide)
  · rfl
  · exact absurd hsgt (by decide)

theorem bv8_not_slt0_of_signExtend32_nslt0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hnslt : (v.signExtend 32).slt 0#32 = false) :
    ¬ v.slt 0#8 = true := by
  rcases hdom with rfl | rfl | rfl
  · decide
  · decide
  · exact absurd hnslt (by decide)

theorem bv8_ne0_not_signExtend32_sgt0_eqff {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hne0 : v ≠ 0#8)
    (hnsgt : ¬ (0#32 : BitVec 32).slt (v.signExtend 32) = true) : v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd rfl hne0
  · exact absurd (by decide) hnsgt
  · rfl

theorem bv8_not_slt0_of_signExtend32_eq0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (heq : v.signExtend 32 = 0#32) :
    ¬ v.slt 0#8 = true := by
  rw [bv8_eq0_of_signExtend32 hdom heq]; decide

theorem bv8_eq1_of_signExtend32_ne0_nslt0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hne : v.signExtend 32 ≠ 0#32)
    (hnslt : ¬ v.slt 0#8 = true) : v = 1#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd (by decide) hne
  · rfl
  · exact absurd (by decide) hnslt

theorem bv8_sgt0_iff_eq1 {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) :
    (0#8 : BitVec 8).slt v = true ↔ v = 1#8 := by
  rcases hdom with rfl | rfl | rfl <;> decide

theorem bv8_eq1_of_sgt0 {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hsgt : (0#8 : BitVec 8).slt v = true) : v = 1#8 :=
  (bv8_sgt0_iff_eq1 hdom).mp hsgt

theorem bv8_eqff_of_slt0 {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hslt : v.slt 0#8 = true) : v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl
  · cases hslt
  · cases hslt
  · rfl

theorem bv8_ne0_not_sgt0_eqff {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hne0 : v ≠ 0#8) (hnsgt : ¬ (0#8 : BitVec 8).slt v = true) : v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd rfl hne0
  · exact absurd (by decide) hnsgt
  · rfl

theorem m6_testBit_false_of_lt {a b : Nat} (h : a < 2 ^ b) : a.testBit b = false := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]; rfl

theorem m6_bv32_and_not1_toNat (x : BitVec 32) :
    (x &&& ~~~1#32).toNat = 2 * (x.toNat / 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [BitVec.toNat_and, Nat.testBit_and]
  cases i with
  | zero => simp
  | succ k =>
    by_cases hk : k + 1 < 32
    · have hall : ∀ j < 32, 0 < j → (~~~1#32 : BitVec 32).toNat.testBit j = true := by decide
      rw [hall (k + 1) hk (by omega), Bool.and_true, Nat.testBit_succ, Nat.testBit_succ]
      congr 1; omega
    · have hx : x.toNat < 2 ^ (k + 1) :=
        Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega))
      have h2 : 2 * (x.toNat / 2) < 2 ^ (k + 1) := by omega
      rw [m6_testBit_false_of_lt hx, m6_testBit_false_of_lt h2, Bool.false_and]

theorem bv32_even_or_bit_toNat (y b : BitVec 32) :
    ((y &&& ~~~1#32) ||| (b &&& 1#32)).toNat = 2 * (y.toNat / 2) + b.toNat % 2 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [BitVec.toNat_or, Nat.testBit_or, m6_bv32_and_not1_toNat, BitVec.toNat_and, Nat.testBit_and]
  cases i with
  | zero =>
    have h1 : (1#32 : BitVec 32).toNat.testBit 0 = true := by decide
    rw [h1, Bool.and_true, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one b.toNat with hb | hb <;> simp [hb] <;> omega
  | succ k =>
    have h0 : (1#32 : BitVec 32).toNat.testBit (k + 1) = false := by
      rw [show (1#32 : BitVec 32).toNat = 1 from rfl]
      exact m6_testBit_false_of_lt (Nat.lt_of_lt_of_le (by omega)
        (Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ k + 1)))
    rw [h0, Bool.and_false, Bool.or_false, Nat.testBit_succ, Nat.testBit_succ]
    congr 1; omega

theorem litSign_of_mod2 (n : Nat) : litSign n = decide (n % 2 = 1) := by
  unfold litSign; rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem litNeg_div2 (n : Nat) : litNeg n / 2 = n / 2 := litVar_litNeg n

theorem bv32_xor1_eq_litNeg (x : BitVec 32) : (x ^^^ 1#32).toNat = litNeg x.toNat := by
  simp [litNeg, BitVec.toNat_xor]

theorem bv32_xor1_litNeg (x : BitVec 32) : (x ^^^ 1).toNat = litNeg x.toNat := by
  simp [litNeg, BitVec.toNat_xor]

theorem bv32_xor1_lt_even {x n : Nat} (hx : x < 2 * n) : x ^^^ 1 < 2 * n :=
  litNeg_lt_two_mul hx

theorem bv32_xor1_symm {a b : BitVec 32} (h : a ≠ b ^^^ 1#32) : b ≠ a ^^^ 1#32 := by
  intro heq; apply h; rw [heq, BitVec.xor_assoc]; simp

theorem bv32_lt_and_ne_xor1_div_lt {ra rb : BitVec 32} (hlt : ra.toNat < rb.toNat)
    (hne : ra ≠ rb ^^^ 1#32) :
    ra.toNat / 2 < rb.toNat / 2 ∧ (ra ^^^ 1#32).toNat < (rb ^^^ 1#32).toNat := by
  have hdiv_ne : ra.toNat / 2 ≠ rb.toNat / 2 := by
    intro hd
    rcases (litVar_eq_iff ra.toNat rb.toNat).mp hd with h1 | h2
    · omega
    · apply hne; apply BitVec.eq_of_toNat_eq; simpa [litNeg, BitVec.toNat_xor] using h2
  have hdiv_lt : ra.toNat / 2 < rb.toNat / 2 := by omega
  refine ⟨hdiv_lt, ?_⟩
  have h1 : (ra ^^^ 1#32).toNat = litNeg ra.toNat := by simp [litNeg, BitVec.toNat_xor]
  have h2 : (rb ^^^ 1#32).toNat = litNeg rb.toNat := by simp [litNeg, BitVec.toNat_xor]
  rw [h1, h2, litNeg_eq, litNeg_eq]
  split <;> split <;> omega

theorem vals1_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {k : FullCoreState}
    (hw : FullWitnessInv c F0 F_cur k) (_hcl0 : k.cur_level = 0) {l : Nat}
    (hl : l < 2 * k.cur_vars) (hval : k.vals[l]?.getD 0#8 = 1#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l]) := by
  obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp hval
  have hlvl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hs := hw.level0_sound i hi hlvl0; rwa [heq] at hs

theorem valsff_entails_neg {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (_hcl0 : k.cur_level = 0) {l : Nat}
    (hl : l < 2 * k.cur_vars) (hval : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg l]) := by
  obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp hval
  have hlvl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hs := hw.level0_sound i hi hlvl0; rwa [heq] at hs

theorem entails_eval_true {f : CNF Nat} {l : Nat} (h : f.EntailsClause (cnfClause [l]))
    {α : Nat → Bool} (hα : f.Sat α) : evalLitVal α l = true := by
  have hs := CNF.entails_clause_def.mp h α hα
  rw [← clauseEvalVal_iff, clauseEvalVal] at hs
  simpa using hs

theorem entails_neg_eval_false {f : CNF Nat} {l : Nat}
    (h : f.EntailsClause (cnfClause [litNeg l])) {α : Nat → Bool} (hα : f.Sat α) :
    evalLitVal α l = false := by
  have ht := entails_eval_true h hα
  rw [evalLitVal_litNeg] at ht
  cases hb : evalLitVal α l <;> simp [hb] at ht ⊢

theorem entails_of_eval_mem {f : CNF Nat} {xs : List Nat}
    (h : ∀ α : Nat → Bool, f.Sat α → ∃ l ∈ xs, evalLitVal α l = true) :
    f.EntailsClause (cnfClause xs) := by
  rw [CNF.entails_clause_def]
  intro α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]; exact h α hα

theorem entails_perm_clause {f : CNF Nat} {xs ys : List Nat}
    (hsub : ∀ x ∈ xs, x ∈ ys) (h : f.EntailsClause (cnfClause xs)) :
    f.EntailsClause (cnfClause ys) :=
  CNF.entails_clause_def.mpr fun α hα =>
    sat_clause_of_subset hsub (CNF.entails_clause_def.mp h α hα)

theorem unsat_of_litEquiv_neg {f : CNF Nat} {a : Nat}
    (h : LitEquiv f a (litNeg a)) : f.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have he := litEquiv_eval hα h; rw [evalLitVal_litNeg] at he
  cases hb : evalLitVal α a <;> simp [hb] at he

theorem unassigned_clause_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (_hcl0 : s.core.cur_level = 0)
    {cr : Nat} (hcr : cr ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cr = false)
    {unass : List Nat}
    (hcov : ∀ l ∈ fullArenaClauseLits s cr,
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨ l ∈ unass) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause unass) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hsat := (clauseEvalVal_iff α _).mpr
    ((CNF.entails_clause_def.mp (hw.arena.entails cr hcr hng)) α hα)
  rw [clauseEvalVal, List.any_eq_true] at hsat
  obtain ⟨l, hl_mem, hl_t⟩ := hsat
  rcases hcov l hl_mem with hff | hin
  · exfalso
    have hl_lt := hw.arena.lits_lt cr hcr hng l hl_mem
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl_lt).mp hff
    have hlvl0 : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hw.lvl_le i hi; omega
    have hunit := hw.level0_sound i hi hlvl0; rw [heq] at hunit
    have hs := (CNF.entails_clause_def.mp hunit) α hα
    rw [← clauseEvalVal_iff, clauseEvalVal] at hs
    simp only [List.any_cons, List.any_nil, Bool.or_false,
      show l ^^^ 1 = litNeg l from rfl, evalLitVal_litNeg, hl_t] at hs
    cases hs
  · exact ⟨l, hin, hl_t⟩

theorem slice_pop_step {F_cur : List (List Nat)} {k : FullCoreState} {a p rem : Nat}
    (hslice : if k.dense_mode = 0#64 then WatchSliceOk F_cur k a p rem
      else DenseWatchSliceOk F_cur k a p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [a, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 1) (rem - 1)
         else DenseWatchSliceOk F_cur k a (p + 1) (rem - 1)) ∨
       (w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
        ∃ cr : BitVec 32, k.wstk[p + 1]? = some cr ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 2) (rem - 2)
         else DenseWatchSliceOk F_cur k a (p + 2) (rem - 2))) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hslice ⊢
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ hent hrest => exact ⟨_, hp, Or.inl ⟨hf, hent, hrest⟩⟩
    | large hp hp1 hf _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ hent hrest => exact ⟨_, hp, Or.inl ⟨hf, hent, hrest⟩⟩
    | occ hp hp1 hf _ _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩

theorem bin_subsumes_unass {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (_hcl0 : s.core.cur_level = 0)
    {a b : Nat} {unass : List Nat} (hb_lt : b < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a, b]))
    (ha_in : a ∈ unass) (hb_cov : s.core.vals[b]?.getD 0#8 = 0xFF#8 ∨ b ∈ unass) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause unass) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hs := (clauseEvalVal_iff α _).mpr ((CNF.entails_clause_def.mp hent) α hα)
  rw [clauseEvalVal] at hs
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hs
  rcases hs with ha_t | hb_t
  · exact ⟨a, ha_in, ha_t⟩
  · rcases hb_cov with hff | hb_in
    · exfalso
      obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff b hb_lt).mp hff
      have hlvl0 : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        have := hw.lvl_le i hi; omega
      have hunit := hw.level0_sound i hi hlvl0; rw [heq] at hunit
      have hsu := (CNF.entails_clause_def.mp hunit) α hα
      rw [← clauseEvalVal_iff, clauseEvalVal] at hsu
      simp only [List.any_cons, List.any_nil, Bool.or_false,
        show b ^^^ 1 = litNeg b from rfl, evalLitVal_litNeg, hb_t] at hsu
      cases hsu
    · exact ⟨b, hb_in, hb_t⟩

theorem garb_false_of_and_480000 {hdr : BitVec 32}
    (h : (hdr &&& 0x00480000#32) = 0#32) :
    ((hdr &&& 0x00080000#32) != 0#32) = false := by
  have hmask : (0x00480000#32 : BitVec 32) &&& 0x00080000#32 = 0x00080000#32 := by decide
  have hb : (hdr &&& 0x00080000#32) = 0#32 := by
    calc hdr &&& 0x00080000#32 = hdr &&& (0x00480000#32 &&& 0x00080000#32) := by rw [hmask]
      _ = (hdr &&& 0x00480000#32) &&& 0x00080000#32 := by rw [BitVec.and_assoc]
      _ = 0#32 := by rw [h]; decide
  simp [hb]

theorem arena_clause3_lits {k : FullCoreState} {cr : Nat}
    (hsz : fullArenaClauseSizeCore k cr = 3) (hbd : cr + 6 ≤ k.arena.length) :
    fullArenaClauseLitsCore k cr =
      [(k.arena[cr + 3]'(by omega)).toNat, (k.arena[cr + 4]'(by omega)).toNat,
       (k.arena[cr + 5]'(by omega)).toNat] := by
  unfold fullArenaClauseLitsCore; rw [hsz]
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro i hi1 _
    simp only [List.length_map, List.length_take, List.length_drop] at hi1
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    rcases i with _ | _ | _ | i' <;> first | rfl | omega

private theorem not_mem_erase_of_nodup {α : Type _} [BEq α] [LawfulBEq α] {a : α} :
    ∀ {xs : List α}, xs.Nodup → a ∉ xs.erase a
  | [], _ => by simp
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    by_cases hxa : x = a
    · subst hxa; simpa using hnd.1
    · have hne : (x == a) = false := beq_false_of_ne hxa
      simp only [List.erase_cons, hne, Bool.false_eq_true, ↓reduceIte, List.mem_cons, not_or]
      exact ⟨Ne.symm hxa, not_mem_erase_of_nodup hnd.2⟩

theorem nodup_lt_length_le : ∀ {n : Nat} {xs : List Nat},
    xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n := by
  intro n; induction n with
  | zero =>
    intro xs _ hlt; cases xs with
    | nil => exact Nat.le_refl 0
    | cons x _ => exfalso; have := hlt x List.mem_cons_self; omega
  | succ n ih =>
    intro xs hnd hlt
    by_cases hmem : n ∈ xs
    · have hnd' : (xs.erase n).Nodup := hnd.erase n
      have hlt' : ∀ x ∈ xs.erase n, x < n := fun x hx => by
        have hxm : x ∈ xs := List.mem_of_mem_erase hx
        have hne : x ≠ n := fun h => not_mem_erase_of_nodup hnd (h ▸ hx)
        have := hlt x hxm; omega
      have hle := ih hnd' hlt'
      have hlen : (xs.erase n).length = xs.length - 1 := List.length_erase_of_mem hmem
      have hpos : 0 < xs.length := List.length_pos_of_mem hmem; omega
    · have hlt' : ∀ x ∈ xs, x < n := fun x hx => by
        have hne : x ≠ n := fun h => hmem (h ▸ hx)
        have := hlt x hx; omega
      exact Nat.le_trans (ih hnd hlt') (Nat.le_succ n)

theorem nodup_of_map_nodup {α β : Type _} {f : α → β} {xs : List α}
    (h : (xs.map f).Nodup) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun ha => h.1 (List.mem_map_of_mem ha), ih h.2⟩

theorem fullArenaClauseSize_le_cur_vars {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hnodup : FullArenaVarsNodup s) {r : Nat}
    (hr : r ∈ fullArenaClauseRefs s) (hg : fullArenaClauseGarb s r = false) :
    fullArenaClauseSize s r ≤ s.core.cur_vars := by
  have hwf := hw.arena.refs_wf r hr
  have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hlen_lits : (fullArenaClauseLits s r).length = fullArenaClauseSizeCore s.core r := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.length_map, List.length_take, List.length_drop]; omega
  have hnd := hnodup r hr hg
  have hle := nodup_lt_length_le (n := s.core.cur_vars) hnd fun v hv => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
    have hl_lt : l < 2 * s.core.cur_vars := hw.arena.lits_lt r hr hg l hl; omega
  rw [List.length_map, hlen_lits] at hle; exact hle

theorem fullArenaScanRefs_next_mem {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, alen - pos ≤ fuel →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen r + 3 ≤ alen →
      fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, h, _ => by simp [fullArenaScanRefs] at h
  | fuel + 1, pos, r, hfl, hmem, hn3 => by
    unfold fullArenaScanRefs at hmem ⊢; split at hmem
    · rename_i hle; simp only [hle, ↓reduceIte, List.mem_cons] at hmem ⊢
      have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases hmem with rfl | hrest
      · right; cases fuel with
        | zero => omega
        | succ f' => unfold fullArenaScanRefs; simp [hn3]
      · right; exact fullArenaScanRefs_next_mem (by omega) hrest hn3
    · simp at hmem

theorem fullArenaClauseRefs_zero_mem {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  have h3 : 3 ≤ k.arena_len := hw.arena.len_ok.elim (fun h => by omega) id
  unfold fullArenaClauseRefsCore
  cases hal : k.arena_len with
  | zero => omega
  | succ f => unfold fullArenaScanRefs; simp [show 3 ≤ f + 1 by omega]

theorem fullArenaClauseRefs_next_or_end {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {r : Nat}
    (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k := by
  rcases (hw.arena.refs_wf r hr).2.2.2.2 with heq | h3
  · exact Or.inl heq
  · exact Or.inr (fullArenaScanRefs_next_mem (by omega) hr h3)

/-! ## 3. Union-Find Root (`congRoot`) Lemmas -/

/-- Iterated union-find root following `repr[x]` up to `fuel` steps. -/
@[expose] def congRoot (repr : List (BitVec 32)) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
    let p := (repr[x]?.getD 0#32).toNat
    if p = x then x else congRoot repr fuel p

theorem congRoot_fuel_ge {repr : List (BitVec 32)} {nlits : Nat}
    (hwf : FullCongReprWf nlits repr) :
    ∀ {x f1 f2 : Nat}, x < nlits → x < f1 → x < f2 →
      congRoot repr f1 x = congRoot repr f2 x := by
  intro x; induction x using Nat.strongRecOn with
  | ind x ih =>
    intro f1 f2 hx hf1 hf2
    cases f1 with
    | zero => omega
    | succ f1' =>
      cases f2 with
      | zero => omega
      | succ f2' =>
        simp only [congRoot]; split
        · rfl
        · rename_i hne
          have hle := hwf.2 x hx; have hlt : (repr[x]?.getD 0#32).toNat < x := by omega
          exact ih _ hlt (by omega) (by omega) (by omega)

theorem congRoot_le {repr : List (BitVec 32)} {nlits : Nat}
    (hwf : FullCongReprWf nlits repr) :
    ∀ {fuel x : Nat}, x < nlits → congRoot repr fuel x ≤ x := by
  intro fuel; induction fuel with
  | zero => intro x _; exact Nat.le_refl _
  | succ f ih =>
    intro x hx; simp only [congRoot]; split
    · exact Nat.le_refl _
    · have hle := hwf.2 x hx; exact Nat.le_trans (ih (by omega)) hle

theorem congRoot_litEquiv {F_cur : List (List Nat)} {nlits : Nat}
    {repr : List (BitVec 32)} (hinv : FullCongReprInv F_cur nlits repr) :
    ∀ {fuel x : Nat}, x < nlits →
      LitEquiv (cnfOfClauses F_cur) x (congRoot repr fuel x) := by
  intro fuel; induction fuel with
  | zero => intro x _; exact LitEquiv.refl _ _
  | succ f ih =>
    intro x hx; simp only [congRoot]; split
    · exact LitEquiv.refl _ _
    · have hle := hinv.1.2 x hx; exact (hinv.2 x hx).trans (ih (by omega))

theorem congRoot_eq_of_fixed {repr : List (BitVec 32)} {fuel x : Nat}
    (hfix : (repr[x]?.getD 0#32).toNat = x) : congRoot repr fuel x = x := by
  cases fuel with
  | zero => rfl
  | succ f => simp [congRoot, hfix]

/-! ## 4. Unified `CongGateAt`, `CongGateSeqOk`, `CongHtInv` & XOR/Control Helpers -/

theorem xorEvalList_nil (α : Nat → Bool) : xorEvalList α [] = false := rfl

theorem xorEvalList_cons (α : Nat → Bool) (x : Nat) (xs : List Nat) :
    xorEvalList α (x :: xs) = (evalLitVal α x != xorEvalList α xs) := rfl

theorem xorEvalList_append (α : Nat → Bool) (xs ys : List Nat) :
    xorEvalList α (xs ++ ys) = (xorEvalList α xs != xorEvalList α ys) := by
  induction xs with
  | nil => rw [List.nil_append, xorEvalList_nil, Bool.false_bne]
  | cons a as ih =>
    rw [List.cons_append, xorEvalList_cons, xorEvalList_cons, ih]
    cases evalLitVal α a <;> cases xorEvalList α as <;> cases xorEvalList α ys <;> rfl

theorem xorEvalList_pair (α : Nat → Bool) (a b : Nat) :
    xorEvalList α [a, b] = (evalLitVal α a != evalLitVal α b) := by
  rw [xorEvalList_cons, xorEvalList_cons, xorEvalList_nil]
  cases evalLitVal α a <;> cases evalLitVal α b <;> rfl

theorem xorEvalList_triple (α : Nat → Bool) (a b c : Nat) :
    xorEvalList α [a, b, c] = (evalLitVal α a != (evalLitVal α b != evalLitVal α c)) := by
  rw [xorEvalList_cons, xorEvalList_cons, xorEvalList_cons, xorEvalList_nil]
  cases evalLitVal α a <;> cases evalLitVal α b <;> cases evalLitVal α c <;> rfl

theorem xorEvalList_perm (α : Nat → Bool) {xs ys : List Nat} (hp : List.Perm xs ys) :
    xorEvalList α xs = xorEvalList α ys := by
  induction hp with
  | nil => rfl
  | cons x _ ih => rw [xorEvalList_cons, xorEvalList_cons, ih]
  | swap a b l =>
    rw [xorEvalList_cons, xorEvalList_cons, xorEvalList_cons, xorEvalList_cons]
    cases evalLitVal α a <;> cases evalLitVal α b <;> cases xorEvalList α l <;> rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem xorEvalList_of_litEquiv {f : CNF Nat} {α : Nat → Bool} (hα : f.Sat α) :
    ∀ {xs ys : List Nat}, xs.length = ys.length →
      (∀ i < xs.length, LitEquiv f (xs[i]?.getD 0) (ys[i]?.getD 0)) →
      xorEvalList α xs = xorEvalList α ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, heq => by
    have h0 := heq 0 (by simp)
    simp only [List.getElem?_cons_zero, Option.getD_some] at h0
    have ih := xorEvalList_of_litEquiv (xs := xs) (ys := ys) hα (by simpa using hlen)
      (fun i hi => by simpa using heq (i + 1) (by simpa using Nat.succ_lt_succ hi))
    rw [xorEvalList_cons, xorEvalList_cons, litEquiv_eval hα h0, ih]

theorem xorEvalList_litNeg_head (α : Nat → Bool) (x : Nat) (xs : List Nat) :
    xorEvalList α (litNeg x :: xs) = !(xorEvalList α (x :: xs)) := by
  rw [xorEvalList_cons, xorEvalList_cons, evalLitVal_litNeg]
  cases evalLitVal α x <;> cases xorEvalList α xs <;> rfl

theorem xorEvalList_dedup_adj (α : Nat → Bool) (x : Nat) (xs : List Nat) :
    xorEvalList α (x :: x :: xs) = xorEvalList α xs := by
  rw [xorEvalList_cons, xorEvalList_cons]
  cases evalLitVal α x <;> cases xorEvalList α xs <;> rfl

theorem xorGateDef_of_eval_eq {f : CNF Nat} {g a b : Nat}
    (h : ∀ α : Nat → Bool, f.Sat α →
      evalLitVal α g = (evalLitVal α a != evalLitVal α b)) :
    XorGateDef f g a b := by
  refine ⟨entails_of_eval_mem fun α hα => ?_, entails_of_eval_mem fun α hα => ?_,
    entails_of_eval_mem fun α hα => ?_, entails_of_eval_mem fun α hα => ?_⟩
  · have hv := h α hα
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b
    · exact ⟨litNeg a, by simp, by simp [evalLitVal_litNeg, ha]⟩
    · exact ⟨g, by simp, by simp [hv, ha, hb]⟩
    · exact ⟨g, by simp, by simp [hv, ha, hb]⟩
    · exact ⟨b, by simp, hb⟩
  · have hv := h α hα
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b
    · exact ⟨litNeg b, by simp, by simp [evalLitVal_litNeg, hb]⟩
    · exact ⟨g, by simp, by simp [hv, ha, hb]⟩
    · exact ⟨g, by simp, by simp [hv, ha, hb]⟩
    · exact ⟨a, by simp, ha⟩
  · have hv := h α hα
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b
    · exact ⟨litNeg g, by simp, by simp [evalLitVal_litNeg, hv, ha, hb]⟩
    · exact ⟨b, by simp, hb⟩
    · exact ⟨a, by simp, ha⟩
    · exact ⟨a, by simp, ha⟩
  · have hv := h α hα
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b
    · exact ⟨litNeg a, by simp, by simp [evalLitVal_litNeg, ha]⟩
    · exact ⟨litNeg a, by simp, by simp [evalLitVal_litNeg, ha]⟩
    · exact ⟨litNeg b, by simp, by simp [evalLitVal_litNeg, hb]⟩
    · exact ⟨litNeg g, by simp, by simp [evalLitVal_litNeg, hv, ha, hb]⟩

theorem iteGateDef_of_eval_eq {f : CNF Nat} {g c t e : Nat}
    (h : ∀ α : Nat → Bool, f.Sat α →
      evalLitVal α g = if evalLitVal α c then evalLitVal α t else evalLitVal α e) :
    IteGateDef f g c t e := by
  refine ⟨entails_of_eval_mem fun α hα => ?_, entails_of_eval_mem fun α hα => ?_,
    entails_of_eval_mem fun α hα => ?_, entails_of_eval_mem fun α hα => ?_⟩
  · have hv := h α hα
    cases hc : evalLitVal α c <;> cases ht : evalLitVal α t
    · exact ⟨litNeg c, by simp, by simp [evalLitVal_litNeg, hc]⟩
    · exact ⟨litNeg c, by simp, by simp [evalLitVal_litNeg, hc]⟩
    · exact ⟨litNeg t, by simp, by simp [evalLitVal_litNeg, ht]⟩
    · exact ⟨g, by simp, by simp [hv, hc, ht]⟩
  · have hv := h α hα
    cases hc : evalLitVal α c <;> cases he : evalLitVal α e
    · exact ⟨litNeg e, by simp, by simp [evalLitVal_litNeg, he]⟩
    · exact ⟨g, by simp, by simp [hv, hc, he]⟩
    · exact ⟨c, by simp, hc⟩
    · exact ⟨c, by simp, hc⟩
  · have hv := h α hα
    cases hc : evalLitVal α c <;> cases ht : evalLitVal α t
    · exact ⟨litNeg c, by simp, by simp [evalLitVal_litNeg, hc]⟩
    · exact ⟨litNeg c, by simp, by simp [evalLitVal_litNeg, hc]⟩
    · exact ⟨litNeg g, by simp, by simp [evalLitVal_litNeg, hv, hc, ht]⟩
    · exact ⟨t, by simp, ht⟩
  · have hv := h α hα
    cases hc : evalLitVal α c <;> cases he : evalLitVal α e
    · exact ⟨litNeg g, by simp, by simp [evalLitVal_litNeg, hv, hc, he]⟩
    · exact ⟨e, by simp, he⟩
    · exact ⟨c, by simp, hc⟩
    · exact ⟨c, by simp, hc⟩

theorem congGateArity_of_ne3 {mword : BitVec 32} (h : (mword >>> 28) ≠ 3#32) :
    congGateArity mword = (mword &&& 0xFF#32).toNat := by
  simp [congGateArity, h]

theorem congGateArity_of_eq3 {mword : BitVec 32} (h : (mword >>> 28) = 3#32) :
    congGateArity mword = (mword &&& 0x0FFFFFFF#32).toNat := by
  simp [congGateArity, h]

theorem congGateAt_mono {maxA maxB : Nat} (hle : maxA ≤ maxB)
    {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)} {g_len g : Nat}
    (h : CongGateAt maxA F_cur cv scr g_len g) : CongGateAt maxB F_cur cv scr g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, ha, hrhs, hsem⟩ := h
  exact ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, Nat.le_trans ha hle, hrhs, hsem⟩

theorem congGateAt_frame {maxA : Nat} {F_cur : List (List Nat)} {cv g_len g : Nat}
    {scr scr' : List (BitVec 32)}
    (hpref : ∀ idx < g_len, scr'[idx]? = scr[idx]?)
    (h : CongGateAt maxA F_cur cv scr g_len g) : CongGateAt maxA F_cur cv scr' g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, ha, hrhs, hsem⟩ := h
  have hdt : (scr'.drop (g + 2)).take (congGateArity mword) =
      (scr.drop (g + 2)).take (congGateArity mword) := by
    have hle1 : g + 2 + congGateArity mword ≤ scr.length := by
      have h1l : g + 1 < scr.length := (List.getElem?_eq_some_iff.mp h1).1
      rcases Nat.eq_zero_or_pos (congGateArity mword) with hz | hp
      · omega
      · obtain ⟨_, hr, _⟩ := hrhs (congGateArity mword - 1) (by omega)
        have hrl := (List.getElem?_eq_some_iff.mp hr).1; omega
    have hle2 : g + 2 + congGateArity mword ≤ scr'.length := by
      have h1' := (hpref (g + 1) (by omega)).trans h1
      have h1l : g + 1 < scr'.length := (List.getElem?_eq_some_iff.mp h1').1
      rcases Nat.eq_zero_or_pos (congGateArity mword) with hz | hp
      · omega
      · obtain ⟨_, hr, _⟩ := hrhs (congGateArity mword - 1) (by omega)
        have hr' := (hpref (g + 2 + (congGateArity mword - 1)) (by omega)).trans hr
        have hrl := (List.getElem?_eq_some_iff.mp hr').1; omega
    refine List.ext_getElem
      (by simp only [List.length_take, List.length_drop]; omega) fun k hk1 _ => ?_
    simp only [List.getElem_take, List.getElem_drop]
    have hk_lt : k < congGateArity mword := by
      simp only [List.length_take, List.length_drop] at hk1; omega
    have heq := hpref (g + 2 + k) (by omega)
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
    exact Option.some.inj heq
  refine ⟨lhs, mword, (hpref g (by omega)).trans h0, (hpref (g + 1) (by omega)).trans h1,
    hlhs, hbd, hcv, ha, fun k hk => ?_, ?_⟩
  · obtain ⟨r, hr, hlt⟩ := hrhs k hk
    exact ⟨r, (hpref (g + 2 + k) (by omega)).trans hr, hlt⟩
  · rcases hsem with ⟨ht, hand⟩ | ⟨ht, h2, h4, hxor⟩ | ⟨ht, h3, hite⟩
    · exact Or.inl ⟨ht, by rwa [hdt]⟩
    · exact Or.inr (Or.inl ⟨ht, h2, h4, by rwa [hdt]⟩)
    · refine Or.inr (Or.inr ⟨ht, h3, ?_⟩)
      rw [hpref (g + 2) (by omega), hpref (g + 3) (by omega), hpref (g + 4) (by omega)]
      exact hite

theorem congGateAt_ext_len {maxA : Nat} {F_cur : List (List Nat)} {cv g_len g_len' g : Nat}
    {scr : List (BitVec 32)} (hle : g_len ≤ g_len')
    (h : CongGateAt maxA F_cur cv scr g_len g) : CongGateAt maxA F_cur cv scr g_len' g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, ha, hrhs, hsem⟩ := h
  exact ⟨lhs, mword, h0, h1, hlhs, Nat.le_trans hbd hle, hcv, ha, hrhs, hsem⟩

theorem congGateSeqOk_mono {maxA maxB : Nat} (hle : maxA ≤ maxB)
    {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)} {g_len g : Nat}
    (h : CongGateSeqOk maxA F_cur cv scr g_len g) :
    CongGateSeqOk maxB F_cur cv scr g_len g := by
  induction h with
  | done => exact .done
  | step hg _ ih => exact .step (congGateAt_mono hle hg) ih

theorem congGateSeqOk_append_gate {maxA : Nat} {F_cur : List (List Nat)}
    {cv g_len g_len' g : Nat} {scr scr' : List (BitVec 32)}
    (hpref : ∀ idx < g_len, scr'[idx]? = scr[idx]?)
    (hseq : CongGateSeqOk maxA F_cur cv scr g_len g)
    (htail : CongGateSeqOk maxA F_cur cv scr' g_len' g_len)
    (hle : g_len ≤ g_len') :
    CongGateSeqOk maxA F_cur cv scr' g_len' g := by
  induction hseq with
  | done => exact htail
  | @step g0 hg _ ih =>
    have hg' := congGateAt_ext_len hle (congGateAt_frame hpref hg)
    obtain ⟨_, mword, _, h1, _, hbd, _, _, _, _⟩ := hg
    have hm_eq : scr'[g0 + 1]?.getD 0#32 = scr[g0 + 1]?.getD 0#32 := by
      rw [hpref (g0 + 1) (by omega)]
    exact .step hg' (by rw [hm_eq]; exact ih)

theorem congGateSeqOk_inv_lt {maxA : Nat} {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr : List (BitVec 32)} {g_len g : Nat}
    (hs : CongGateSeqOk maxA F_cur cur_vars scr g_len g) (hlt : g < g_len) :
    CongGateAt maxA F_cur cur_vars scr g_len g ∧
      CongGateSeqOk maxA F_cur cur_vars scr g_len
        (g + 2 + congGateArity (scr[g + 1]?.getD 0#32)) := by
  cases hs with
  | done => omega
  | step hg hrest => exact ⟨hg, hrest⟩

theorem congHtInv_mono {maxA maxB : Nat} (hle : maxA ≤ maxB)
    {F_cur : List (List Nat)} {cv : Nat} {scr0 scr : List (BitVec 32)}
    {g_len ht_off ht_sz : Nat}
    (h : CongHtInv maxA F_cur cv scr0 scr g_len ht_off ht_sz) :
    CongHtInv maxB F_cur cv scr0 scr g_len ht_off ht_sz := fun k hk =>
  (h k hk).elim Or.inl fun hg => Or.inr (congGateAt_mono hle hg)

theorem congHtInv_clear {maxA : Nat} {F_cur : List (List Nat)} {cv g_len ht_off ht_sz : Nat}
    {scr0 scr : List (BitVec 32)}
    (hall : ∀ k < ht_sz, scr[ht_off + k]? = some 0xFFFFFFFF#32) :
    CongHtInv maxA F_cur cv scr0 scr g_len ht_off ht_sz := fun k hk => by
  left; rw [hall k hk, Option.getD_some]

theorem congHtInv_set_gate {maxA : Nat} {F_cur : List (List Nat)} {cv g_len ht_off ht_sz : Nat}
    {scr0 scr : List (BitVec 32)} {slot : Nat} {g : BitVec 32}
    (hinv : CongHtInv maxA F_cur cv scr0 scr g_len ht_off ht_sz)
    (hslot : slot < ht_sz) (harr : ht_off + slot < scr.length)
    (hg : CongGateAt maxA F_cur cv scr0 g_len g.toNat) :
    CongHtInv maxA F_cur cv scr0 (scr.set (ht_off + slot) g) g_len ht_off ht_sz := by
  intro k hk
  by_cases hks : k = slot
  · subst hks; right; rw [List.getElem?_set_self harr, Option.getD_some]; exact hg
  · rw [List.getElem?_set_ne (by omega)]; exact hinv k hk

theorem cong_pow2_sub1_and_eq_mod {n p : Nat} (_hp : 1 ≤ p) (hp20 : p ≤ 20) (x : BitVec 32)
    (hn : n = 2 ^ p) : (x &&& (BitVec.ofNat 32 n - 1#32)).toNat = x.toNat % n := by
  have hlt : 2 ^ p ≤ 1048576 := Nat.pow_le_pow_right (by omega) hp20
  have hsub : (BitVec.ofNat 32 n - 1#32).toNat = 2 ^ p - 1 := by
    have hof : (BitVec.ofNat 32 n).toNat = 2 ^ p := by
      rw [hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hof]; exact Nat.one_le_two_pow)), hof]
    rfl
  rw [BitVec.toNat_and, hsub, hn, Nat.and_two_pow_sub_one_eq_mod]

theorem cong_and_sub1_u32_eq_mod {occ_bkt : Nat}
    (hp : ∃ p : Nat, 1 ≤ p ∧ p ≤ 20 ∧ occ_bkt = 2 ^ p) (x : BitVec 32) :
    (x &&& (BitVec.ofNat 32 occ_bkt - 1#32)).toNat = x.toNat % occ_bkt := by
  obtain ⟨p, h1, h2, rfl⟩ := hp; exact cong_pow2_sub1_and_eq_mod h1 h2 x rfl

theorem congCtrlLayout_set_q {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (h : CongCtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    {scr' : List (BitVec 32)} (_hlen' : scr'.length = scr.length)
    (hk05 : ∀ i < 8, i ≠ 4 → i ≠ 5 → scr'[ctrl_off + i]? = scr[ctrl_off + i]?)
    (hqh' : (scr'[ctrl_off + 4]?.getD 0#32).toNat < occ_bkt)
    (hql' : (scr'[ctrl_off + 5]?.getD 0#32).toNat ≤ occ_bkt)
    (hqok' : ∀ k < (scr'[ctrl_off + 5]?.getD 0#32).toNat,
      (scr'[q_off + ((scr'[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]?.getD 0#32).toNat <
        occ_bkt) :
    CongCtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  rcases h with
    ⟨h1, h2, h3, h4, s0, s1, s2, s3, s6, s7, h5, h6, hpow, h7, h8, h9, h10, h11, h12, _, _, _⟩
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_, ?_, ?_,
    h5, h6, hpow, h7, h8, h9, h10, h11, h12, hqh', hql', hqok'⟩
  · have h0 := hk05 0 (by decide) (by decide) (by decide)
    rw [Nat.add_zero] at h0; exact (congrArg (Option.getD · 0#32) h0).trans s0
  · exact (congrArg (Option.getD · 0#32) (hk05 1 (by decide) (by decide) (by decide))).trans s1
  · exact (congrArg (Option.getD · 0#32) (hk05 2 (by decide) (by decide) (by decide))).trans s2
  · exact (congrArg (Option.getD · 0#32) (hk05 3 (by decide) (by decide) (by decide))).trans s3
  · exact (congrArg (Option.getD · 0#32) (hk05 6 (by decide) (by decide) (by decide))).trans s6
  · exact (congrArg (Option.getD · 0#32) (hk05 7 (by decide) (by decide) (by decide))).trans s7

theorem congCtrlLayout_same_tail {c : FullCfg} {scr scr' : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (h : CongCtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hlen' : scr'.length = scr.length)
    (hql' : (scr'[ctrl_off + 5]?.getD 0#32).toNat ≤ occ_bkt)
    (hk : ∀ i < 8, i ≠ 5 → scr'[ctrl_off + i]? = scr[ctrl_off + i]?)
    (hqok' : ∀ k < (scr'[ctrl_off + 5]?.getD 0#32).toNat,
      (scr'[q_off + ((scr'[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt]?.getD 0#32).toNat <
        occ_bkt) :
    CongCtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  refine congCtrlLayout_set_q h hlen' (fun i hi _ h5 => hk i hi h5) ?_ hql' hqok'
  rw [hk 4 (by decide) (by decide)]; exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem congCtrlLayout_pop_q {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (h : CongCtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz)
    (hlen : scr.length = c.scratch_cap)
    (hpos : 0 < (scr[ctrl_off + 5]?.getD 0#32).toNat) :
    let qh := scr[ctrl_off + 4]?.getD 0#32
    let ql := scr[ctrl_off + 5]?.getD 0#32
    let b := scr[q_off + qh.toNat]?.getD 0#32
    let nqh := (qh + 1#32) &&& (BitVec.ofNat 32 occ_bkt - 1#32)
    let scr' := ((scr.set (ctrl_off + 4) nqh).set (ctrl_off + 5) (ql - 1#32)).set
      (inq_off + b.toNat) 0#32
    b.toNat < occ_bkt ∧ nqh.toNat < occ_bkt ∧
    CongCtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz := by
  intro qh ql b nqh scr'
  rcases h with
    ⟨h1, h2, h3, h4, s0, s1, s2, s3, s6, s7, h5, h6, hpow, h7, h8, h9, h10, h11, h12,
     hqh_lt, hql_le, hqok⟩
  have hb_lt : b.toNat < occ_bkt := by
    have := hqok 0 hpos; rwa [Nat.add_zero, Nat.mod_eq_of_lt hqh_lt] at this
  have hnqh_lt : nqh.toNat < occ_bkt := by
    dsimp only [nqh]; rw [cong_and_sub1_u32_eq_mod hpow]; exact Nat.mod_lt _ h5
  have hql_sub : (ql - 1#32).toNat = ql.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show (1#32 : BitVec 32).toNat ≤ ql.toNat from
      Nat.succ_le_of_lt hpos))]; rfl
  have hnqh_mod : nqh.toNat = (qh.toNat + 1) % occ_bkt := by
    dsimp only [nqh]; rw [cong_and_sub1_u32_eq_mod hpow]
    have hqh1 : (qh + 1#32).toNat = qh.toNat + 1 :=
      bv32_add1_lt_of (Nat.lt_trans (Nat.succ_lt_succ hqh_lt)
        (Nat.lt_of_le_of_lt (Nat.succ_le_succ h6) (by decide : congOccBktMax + 1 < 2 ^ 32)))
    rw [hqh1]
  have hscr'_ctrl : ∀ i, i < 8 → i ≠ 4 → i ≠ 5 → scr'[ctrl_off + i]? = scr[ctrl_off + i]? := by
    intro i _ h4' h5'; dsimp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hscr'_4 : scr'[ctrl_off + 4]?.getD 0#32 = nqh := by
    dsimp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp [hlen]; omega), Option.getD_some]
  have hscr'_5 : scr'[ctrl_off + 5]?.getD 0#32 = ql - 1#32 := by
    dsimp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hlen]; omega),
      Option.getD_some]
  refine ⟨hb_lt, hnqh_lt, ?_⟩
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_, ?_, ?_,
    h5, h6, hpow, h7, h8, h9, h10, h11, h12,
    by rw [hscr'_4]; exact hnqh_lt,
    by rw [hscr'_5, hql_sub]; exact Nat.le_trans (Nat.sub_le _ _) hql_le, ?_⟩
  · have h0 := hscr'_ctrl 0 (by decide) (by decide) (by decide)
    rw [Nat.add_zero] at h0; exact (congrArg (Option.getD · 0#32) h0).trans s0
  · exact (congrArg (Option.getD · 0#32)
      (hscr'_ctrl 1 (by decide) (by decide) (by decide))).trans s1
  · exact (congrArg (Option.getD · 0#32)
      (hscr'_ctrl 2 (by decide) (by decide) (by decide))).trans s2
  · exact (congrArg (Option.getD · 0#32)
      (hscr'_ctrl 3 (by decide) (by decide) (by decide))).trans s3
  · exact (congrArg (Option.getD · 0#32)
      (hscr'_ctrl 6 (by decide) (by decide) (by decide))).trans s6
  · exact (congrArg (Option.getD · 0#32)
      (hscr'_ctrl 7 (by decide) (by decide) (by decide))).trans s7
  · intro k hk; rw [hscr'_5, hql_sub] at hk; rw [hscr'_4, hnqh_mod]
    have hidx : ((qh.toNat + 1) % occ_bkt + k) % occ_bkt = (qh.toNat + (k + 1)) % occ_bkt := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc, Nat.add_comm 1 k]
    rw [hidx]
    have hslot_lt : q_off + (qh.toNat + (k + 1)) % occ_bkt < inq_off + b.toNat := by
      have := Nat.mod_lt (qh.toNat + (k + 1)) h5; omega
    dsimp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
    exact hqok (k + 1) (by change k < (scr[ctrl_off + 5]?.getD 0#32).toNat - 1 at hk; omega)

theorem congCtrlLayout_unique {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off o1 b1 i1 q1 h1 s1 o2 b2 i2 q2 h2 s2 : Nat}
    (hl1 : CongCtrlLayout c scr g_len ctrl_off o1 b1 i1 q1 h1 s1)
    (hl2 : CongCtrlLayout c scr g_len ctrl_off o2 b2 i2 q2 h2 s2) :
    o1 = o2 ∧ b1 = b2 ∧ i1 = i2 ∧ q1 = q2 ∧ h1 = h2 ∧ s1 = s2 := by
  have heqc : ∀ {a b : Nat}, a < 2 ^ 32 → b < 2 ^ 32 →
      BitVec.ofNat 32 a = BitVec.ofNat 32 b → a = b := fun ha hb hv => by
    have h := congrArg BitVec.toNat hv
    rwa [bv32_ofNat_toNat_lt ha, bv32_ofNat_toNat_lt hb] at h
  rcases hl1 with ⟨_, _, _, _, e1_0, e1_1, e1_2, e1_3, e1_6, e1_7,
    _, ho1_le, _, _, _, _, _, _, hh1_hi, _, _, _⟩
  rcases hl2 with ⟨_, _, _, _, e2_0, e2_1, e2_2, e2_3, e2_6, e2_7,
    _, ho2_le, _, _, _, _, _, _, hh2_hi, _, _, _⟩
  have hsc := c.hscr; unfold dimacsBound at hsc; unfold congOccBktMax at ho1_le ho2_le
  exact ⟨heqc (by omega) (by omega) (e1_0.symm.trans e2_0),
    heqc (by omega) (by omega) (e1_1.symm.trans e2_1),
    heqc (by omega) (by omega) (e1_2.symm.trans e2_2),
    heqc (by omega) (by omega) (e1_3.symm.trans e2_3),
    heqc (by omega) (by omega) (e1_6.symm.trans e2_6),
    heqc (by omega) (by omega) (e1_7.symm.trans e2_7)⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
