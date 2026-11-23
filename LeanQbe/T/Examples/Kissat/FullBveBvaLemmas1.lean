module

public import LeanQbe.T.Examples.Kissat.Full
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullArena

/-!
# Kissat `D-Full` UNSAT-Only BVE/BCE Proofs — Part 1 (`Stage 4`, BVE/BCE Shard)

Provides:
1. Scoped `FullBveBvaTactics` bitwise/BitVec/pointer-slice helpers and stepping macros.
2. Canonical `D-Full` invariants and `FullSpec3` `Spec` contracts in `FullBveBvaSpecs`
   (covering the `6` `full_bve_*` functions with unconstrained `garb` bounds).
3. `FullBveItemOk`, `FullDenseInvW` transport, and watch/resolution lemmas.
4. Parametric `(Γ : Env)` `Func.wp` proofs for `full_bve_collect`, `full_bve_mark_and`, and
   `full_bve_gates`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Scoped tactics & bitwise/slice helpers (`FullBveBvaTactics`) -/

namespace FullBveBvaTactics

open FullArenaTactics
open scoped FullArenaTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64
attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

@[scoped bv_c0] theorem bv_c0_fullState_core (k : FullCoreState) (sc : FullScratch) :
    ({ core := k, scratch := sc } : FullState).core = k := rfl

@[scoped bv_c0] theorem bv_c0_lshr1_32 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

@[scoped bv_c0] theorem bv_c0_shl1_nat_mod {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt hx]

@[scoped bv_c0] theorem bv_c0_shl1_toNat {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat = 2 * x.toNat := by
  have h1 : BitVec.signExtend 64 (1 : BitVec 32) = (1 : BitVec 64) := rfl
  rw [h1]; exact bv_c0_shl1_nat_mod hx

@[scoped bv_c0] theorem bv_c0_shl1_add1_toNat {x : BitVec 64} (hx : 2 * x.toNat + 1 < 2 ^ 64) :
    (x <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat = 2 * x.toNat + 1 := by
  have hsh := bv_c0_shl1_toNat (x := x) (by omega)
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, hsh, h1, Nat.mod_eq_of_lt hx]

theorem nat_xor1_lt_two_mul {l n : Nat} (hl : l < 2 * n) : l ^^^ 1 < 2 * n := by
  have hdiv : (l ^^^ 1) / 2 = l / 2 := fullInv_var_xor1 l
  omega

theorem bv32_xor_1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := rfl

theorem bv32_xor_1_lt {x : BitVec 32} {n : Nat} (hx : x.toNat < 2 * n) :
    (x ^^^ 1#32).toNat < 2 * n := by
  rw [bv32_xor_1_toNat]; exact nat_xor1_lt_two_mul hx

theorem bv32_and_litMask_toNat (w : BitVec 32) :
    (w &&& 0x7FFFFFFF#32).toNat = w.toNat % 2 ^ 31 := by
  simpa [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl] using
    Nat.and_two_pow_sub_one_eq_mod w.toNat 31

theorem bv32_and_msb_eq_zero_of_lt {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    x &&& 0x80000000#32 = 0#32 := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero]
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi31 | rfl
  · simp [show (0x80000000#32)[i] = false from by
      rw [BitVec.getElem_eq_testBit_toNat, show (0x80000000#32).toNat = 2 ^ 31 by rfl,
        Nat.testBit_two_pow_of_ne (by omega)]]
  · have hb : x[31] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt hx]; rfl
    simp [hb]

theorem bv32_and_0x480000_eq_zero (x : BitVec 32)
    (h : (x &&& (0x00080000#32 ||| 0x00400000#32)) = 0#32) :
    (x &&& 0x00080000#32) = 0#32 ∧ (x &&& 0x00400000#32) = 0#32 := by
  have hmask : (0x00080000#32 ||| 0x00400000#32) = 0x00480000#32 := by decide
  rw [hmask] at h
  have h19 : (0x00080000#32 : BitVec 32) = 0x00480000#32 &&& 0x00080000#32 := by decide
  have h22 : (0x00400000#32 : BitVec 32) = 0x00480000#32 &&& 0x00400000#32 := by decide
  exact ⟨by rw [h19, ← BitVec.and_assoc, h, BitVec.zero_and],
         by rw [h22, ← BitVec.and_assoc, h, BitVec.zero_and]⟩

private theorem m4_off (a : BitVec 64) (off : Nat) (i : BitVec 64) :
    (a + BitVec.ofNat 64 (4 * off)) + i * 4 = a + BitVec.ofNat 64 (4 * (off + i.toNat)) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat, ptr_add_ofNat,
    ← Nat.mul_add]

@[scoped c0_load] theorem load_full_scratch_buf0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pScratchBuf = some s.scratch.scratch_buf[0] := by
  simpa using load_full_scratch_buf (i := 0) hi hm

@[scoped c0_store] theorem store_full_scratch_buf0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pScratchBuf ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set 0 v } } ⋆ R)
        (storeMem m i32 c.pScratchBuf v) := by
  simpa using store_full_scratch_buf (i := 0) v hi hm

@[scoped c0_load] theorem c0_load_full_scratch_buf_off {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {off : Nat} {i : BitVec 64}
    (hi : off + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * off)) + i * 4) =
      some s.scratch.scratch_buf[off + i.toNat] := by
  rw [m4_off]; exact load_full_scratch_buf hi hm

@[scoped c0_store] theorem c0_store_full_scratch_buf_off {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {off : Nat} {i : BitVec 64} (v : BitVec 32)
    (hi : off + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * off)) + i * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (off + i.toNat) v } } ⋆ R)
        (storeMem m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * off)) + i * 4) v) := by
  rw [m4_off]; exact store_full_scratch_buf v hi hm

@[scoped c0_load] theorem load_full_scratch_buf_u64_off0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {off : Nat}
    (hi : off < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 (4 * off)) =
      some s.scratch.scratch_buf[off] := by
  simpa using load_full_scratch_buf (i := off) hi hm

@[scoped c0_store] theorem store_full_scratch_buf_u64_off0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {off : Nat} (v : BitVec 32)
    (hi : off < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 (4 * off)) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set off v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 (4 * off)) v) := by
  simpa using store_full_scratch_buf (i := off) v hi hm

@[scoped c0_load] theorem load_full_scratch_buf_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {d : Nat}
    (hd : d % 4 = 0) (hd64 : d < 2 ^ 64)
    (hi : d / 4 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 d) = some s.scratch.scratch_buf[d / 4] := by
  have heq : BitVec.ofNat 64 d = BitVec.ofNat 64 (4 * (d / 4)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd64,
      Nat.mod_eq_of_lt (by omega)]; omega
  rw [heq]; exact load_full_scratch_buf hi hm

@[scoped c0_store] theorem store_full_scratch_buf_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {d : Nat} (v : BitVec 32)
    (hd : d % 4 = 0) (hd64 : d < 2 ^ 64)
    (hi : d / 4 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 d) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (d / 4) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 d) v) := by
  have heq : BitVec.ofNat 64 d = BitVec.ofNat 64 (4 * (d / 4)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd64,
      Nat.mod_eq_of_lt (by omega)]; omega
  rw [heq]; exact store_full_scratch_buf v hi hm

/-- Strip `Expr.mdata` after unfolding `Func.wp`, then run `c0_steps`. -/
scoped syntax "bve_steps" : tactic
scoped macro_rules
  | `(tactic| bve_steps) => `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _); c0_steps))

/-- Strip `Expr.mdata` after unfolding `Func.wp`, then run strict `c0_steps!`. -/
scoped syntax "bve_steps!" : tactic
scoped macro_rules
  | `(tactic| bve_steps!) => `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _); c0_steps!))

end FullBveBvaTactics

open FullBveBvaTactics
open scoped FullArenaTactics FullBveBvaTactics

/-! ## 2. Canonical Stage-4 shared invariants & local `Spec` contracts (`FullBveBvaSpecs`) -/

namespace FullBveBvaSpecs

@[expose] def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

@[expose] def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

@[expose] def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

@[expose] def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

@[expose] def FullDenseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

@[expose]
def FullDenseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧
  s.core.dense_mode ≠ 0#64

theorem FullDenseInvW.toDense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) : FullDenseInv c F0 s :=
  ⟨⟨h.1, F_cur, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem FullDenseInv.exists_witness {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) : ∃ F_cur, FullDenseInvW c F0 F_cur s :=
  let ⟨F_cur, hw⟩ := h.1.witness
  ⟨F_cur, h.1.lengths, hw, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

@[expose] def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

/-- Clause/binary watch entry collected for literal `lit` during BVE/BCE. -/
private def FullBveItemOk (k : FullCoreState) (F_cur : List (List Nat)) (lit : Nat)
    (w : BitVec 32) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    w ≠ 0xFFFFFFFF#32 ∧ (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat])
  else
    w.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k w.toNat = false

/-- Canonical `FullSpec3` collected occurrence entry for literal `lit`. -/
@[expose] def FullBveEntryOkW (F_cur : List (List Nat)) (s : FullState) (lit : Nat)
    (w : BitVec 32) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    let ot := (w &&& 0x7FFFFFFF#32).toNat
    ot < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, ot])
  else
    w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false

private theorem FullBveItemOk.to_entryW {F_cur : List (List Nat)} {s : FullState} {lit : Nat}
    {w : BitVec 32} (h : FullBveItemOk s.core F_cur lit w) :
    FullBveEntryOkW F_cur s lit w := by
  unfold FullBveItemOk at h; unfold FullBveEntryOkW
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at h ⊢; exact h.2
  · simp [hb] at h ⊢; exact h

/-- Weak structural validity preserved across clause garbage marking and binary deletion. -/
@[expose] def FullBveWeakItemOk (k : FullCoreState) (w : BitVec 32) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars
  else
    w.toNat ∈ fullArenaClauseRefsCore k

/-- Weak structural validity for `full_bve_try_bce` (`garb` unconstrained). -/
@[expose] def FullBveBceWeakOk (c : FullCfg) (s : FullState) (w : BitVec 32) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    (w &&& 0x7FFFFFFF#32).toNat < 2 * c.max_vars
  else
    w.toNat ∈ fullArenaClauseRefs s ∧
    w.toNat + 3 + fullArenaClauseSize s w.toNat ≤ s.core.arena_len ∧
    ∀ l ∈ fullArenaClauseLits s w.toNat, l < 2 * c.max_vars

private theorem FullBveItemOk.to_weak {k : FullCoreState} {F_cur : List (List Nat)} {lit : Nat}
    {w : BitVec 32} (h : FullBveItemOk k F_cur lit w) : FullBveWeakItemOk k w := by
  unfold FullBveItemOk at h; unfold FullBveWeakItemOk
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at h ⊢; exact h.2.1
  · simp [hb] at h ⊢; exact h.1

theorem FullBveEntryOkW.to_weak {F_cur : List (List Nat)} {s : FullState} {lit : Nat}
    {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w) : FullBveWeakItemOk s.core w := by
  unfold FullBveEntryOkW at h; unfold FullBveWeakItemOk
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at h ⊢; exact h.1
  · simp [hb] at h ⊢; exact h.1

/-- Structural slice masking only `core.tmp` (for `full_bve_try_bce`). -/
private def fullCoreTmpMask (s : FullState) : FullCoreState :=
  { s.core with tmp := [] }

private def fullTryBceSlice (c : FullCfg) : SafetySlice FullState FullCoreState where
  mem := FullMem c
  coreProj := fullCoreTmpMask
  safe := FullState.LengthsOk c

/-- 1a. `full_bve_collect` core-level internal spec. -/
private def fullBveCollectCoreSpec : Spec [i64, i32, i64, i32] [i32] :=
  fun (h, lit, out, cap, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop) (off : Nat),
      h = c.hdr ∧ FullCoreInv c F0 s ∧ lit.toNat < 2 * s.core.cur_vars ∧
      out = c.pScratchBuf + BitVec.ofNat 64 (4 * off) ∧
      off + cap.toNat ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        s'.LengthsOk c →
        (r = 0xFFFFFFFF#32 ∨ r.toNat ≤ cap.toNat) →
        (∀ k < c.scratch_cap, k < off ∨ off + cap.toNat ≤ k →
          scr'[k]? = s.scratch.scratch_buf[k]?) →
        (∀ F_cur, FullWitnessInv c F0 F_cur s.core → r ≠ 0xFFFFFFFF#32 →
          ∀ k < r.toNat, FullBveItemOk s.core F_cur lit.toNat (scr'[off + k]?.getD 0#32)) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- 1. `full_bve_collect(h, lit, out_ptr, cap) : u32` (`FullSpec3`). -/
@[expose] def fullBveCollectSpec : Spec [i64, i32, i64, i32] [i32] :=
  fun (h, lit, out_ptr, cap, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (out_off : Nat)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ lit.toNat < 2 * s.core.cur_vars ∧
      out_ptr = c.pScratchBuf + BitVec.ofNat 64 (4 * out_off) ∧
      out_off + cap.toNat ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ r scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < out_off ∨ out_off + cap.toNat ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (r = 0xFFFFFFFF#32 ∨ (r.toNat ≤ cap.toNat ∧
          ∀ i < r.toNat, FullBveEntryOkW F_cur s' lit.toNat (scr'[out_off + i]?.getD 0#32))) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- 2a. `full_bve_mark_and` `SafetySlice` internal helper spec. -/
private def fullBveMarkAndSliceSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _v_lit, cr, n_off, nn, ()) s =>
      h = c.hdr ∧ FullLitMarksClear c s ∧
      cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr.toNat = false ∧
      (∀ l ∈ fullArenaClauseLits s cr.toNat, l < 2 * c.max_vars) ∧
      cr.toNat + 3 + fullArenaClauseSize s cr.toNat ≤ s.core.arena_len ∧
      132 ≤ c.scratch_cap ∧ n_off.toNat + nn.toNat ≤ c.scratch_cap ∧
      ∀ j < nn.toNat,
        let w := s.scratch.scratch_buf[n_off.toNat + j]?.getD 0#32
        (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * c.max_vars)
    (fun c _ _ s s' =>
      ∃ scr', s'.scratch = { s.scratch with scratch_buf := scr' } ∧
      ∀ k < c.scratch_cap, k ≠ 130 → k ≠ 131 →
        scr'[k]? = s.scratch.scratch_buf[k]?)

/-- 2. `full_bve_mark_and(h, v_lit, cr, n_off, nn) : bool` (`FullSpec3`). -/
@[expose] def fullBveMarkAndSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, v_lit, cr, n_off, nn, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 132 ≤ c.scratch_cap ∧
      cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr.toNat = false ∧
      n_off.toNat + nn.toNat ≤ c.scratch_cap ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (v_lit.toNat ^^^ 1)
        (s.scratch.scratch_buf[n_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with
            core := { s.core with lit_mark := lm' }
            scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' →
        (∀ i < c.scratch_cap, i ≠ 130 → i ≠ 131 → scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- 3. `full_bve_gates(h, v, np, nn) : void` (`FullSpec3`). -/
@[expose] def fullBveGatesSpec : Spec [i64, i32, i32, i32] [] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 132 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 64 ∧ nn.toNat ≤ 64 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[64 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ lm' scr' m',
      let s' : FullState :=
        { s with
          core := { s.core with lit_mark := lm' }
          scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' →
      (∀ i < c.scratch_cap, (i < 128 ∨ 132 ≤ i) → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- 4. `full_bve_resolve_pair(h, v, pc, nc) : bool` (`FullSpec3`). -/
@[expose] def fullBveResolvePairSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, v, pc, nc, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ v.toNat < s.core.cur_vars ∧
      FullBveEntryOkW F_cur s (2 * v.toNat) pc ∧
      FullBveEntryOkW F_cur s (2 * v.toNat + 1) nc ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' tmp' tl' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm', tmp := tmp', tmp_len := tl' } }
        FullDenseInvW c F0 F_cur s' → tl' ≤ s.core.cur_vars →
        (ok = true →
          (∀ k < tl', (tmp'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          ((tmp'.take tl').map fun x => x.toNat / 2).Nodup ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat))) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- 5. `full_bve_weaken(h, blk_lit, off, cnt) : bool` (`FullSpec3` with weak item validity). -/
@[expose] def fullBveWeakenSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, blk_lit, off, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ blk_lit.toNat < 2 * s.core.cur_vars ∧
      off.toNat + cnt.toNat ≤ c.scratch_cap ∧
      (∀ i < cnt.toNat,
        FullBveWeakItemOk s.core (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel = s.core.fuel → s'.scratch.scratch_buf = s.scratch.scratch_buf →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- 6a. `full_bve_try_bce` `SafetySlice` internal helper spec (weak `garb`). -/
private def fullBveTryBceSliceSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  SafetySlice.spec fullTryBceSlice
    (fun c (h, _blk_lit, cr, opp_off, opp_n, ()) s =>
      h = c.hdr ∧ FullLitMarksClear c s ∧ opp_off.toNat + opp_n.toNat ≤ c.scratch_cap ∧
      FullBveBceWeakOk c s cr ∧
      ((cr &&& 0x80000000#32) = 0#32 → ((fullArenaClauseLits s cr.toNat).map (· / 2)).Nodup) ∧
      ∀ j < opp_n.toNat, FullBveBceWeakOk c s (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32))
    (fun _ _ _ s s' =>
      s'.core.lit_mark = s.core.lit_mark ∧
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len = s.scratch.extend_len ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf)

/-- 6. `full_bve_try_bce(h, blk_lit, cr, opp_off, opp_n) : bool`
(`FullSpec3` with weak item validity). -/
@[expose] def fullBveTryBceSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, blk_lit, cr, opp_off, opp_n, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ blk_lit.toNat < 2 * s.core.cur_vars ∧
      FullBveBceWeakOk c s cr ∧
      ((cr &&& 0x80000000#32) = 0#32 → ((fullArenaClauseLits s cr.toNat).map (· / 2)).Nodup) ∧
      opp_off.toNat + opp_n.toNat ≤ c.scratch_cap ∧
      (∀ j < opp_n.toNat,
        FullBveBceWeakOk c s (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (blk : Bool) lm' tmp' m',
        let s' : FullState := { s with core := { s.core with lit_mark := lm', tmp := tmp' } }
        FullDenseInvW c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q (blk, ()) m'

/-- Callee contracts used by `full_bve_weaken` (`FullSpec{2,3}`, weak item validity). -/
@[expose] def fullExtendPush2Spec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _ot, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf)

@[expose] def fullExtendPushClSpec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _cr, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf)

@[expose] def fullDeleteBinarySpec : Spec [i64, i32, i32] [] :=
  fun (h, _a, _b, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
      ∀ wvec' wstk' wu' nb' m',
        let s' : FullState :=
          { s with core := { s.core with
            wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
        (FullMem c s' ⋆ R) m' → Q () m'

end FullBveBvaSpecs

open FullBveBvaSpecs

/-! ## 3. Shared invariant transport, watch-slice collection, & BVE resolution lemmas -/

namespace FullBveBvaHelpers

theorem fullDenseInv_with_scratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullDenseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hext : FullExtScratchOk c s') : FullDenseInv c F0 s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨h.1.with_scratch hlen' hcore, ?_, ?_, hext, ?_, ?_⟩
  · unfold FullLitMarksClear at *; rw [heq]; exact h.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact h.2.2.1
  · rw [heq]; exact h.2.2.2.2.1
  · rw [heq]; exact h.2.2.2.2.2

theorem fullArenaClauses_lits_lt_max_vars {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (ha : FullArenaClausesInv c F_cur s.core)
    {r : Nat} (hr : r ∈ fullArenaClauseRefs s) (hg : fullArenaClauseGarb s r = false) :
    ∀ l ∈ fullArenaClauseLits s r, l < 2 * c.max_vars := fun l hl =>
  Nat.lt_of_lt_of_le (ha.lits_lt r hr hg l hl) (Nat.mul_le_mul_left 2 hlen.core_ok.cur_vars_le)

theorem fullLitMark_eq_of_all_zero {lm0 lm1 : List (BitVec 8)} {n : Nat}
    (hl0 : lm0.length = n) (hl1 : lm1.length = n)
    (hz0 : ∀ l < n, lm0[l]?.getD 0#8 = 0#8) (hz1 : ∀ l < n, lm1[l]? = some 0#8) :
    lm1 = lm0 := by
  apply List.ext_getElem (by omega)
  intro i hi1 hi0
  have h1 := hz1 i (by omega)
  rw [List.getElem?_eq_getElem hi1, Option.some.injEq] at h1
  have h0 := hz0 i (by omega)
  rw [List.getElem?_eq_getElem hi0, Option.getD_some] at h0
  rw [h1, h0]

end FullBveBvaHelpers

open FullBveBvaHelpers

private theorem modeWatchSlice_step {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p end_ : Nat} (hlt : p < end_)
    (hslice : if k.dense_mode = 0#64 then WatchSliceOk F_cur k lit p (end_ - p)
              else DenseWatchSliceOk F_cur k lit p (end_ - p)) :
    if (k.wstk[p]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 then
      let w0 := k.wstk[p]?.getD 0#32
      w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      (if k.dense_mode = 0#64 then WatchSliceOk F_cur k lit (p + 1) (end_ - (p + 1))
       else DenseWatchSliceOk F_cur k lit (p + 1) (end_ - (p + 1)))
    else
      ∃ w0 cref, k.wstk[p]? = some w0 ∧ k.wstk[p + 1]? = some cref ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ p + 1 < end_ ∧
      cref.toNat < 0x80000000 ∧ cref.toNat ∈ fullArenaClauseRefsCore k ∧
      (if k.dense_mode = 0#64 then WatchSliceOk F_cur k lit (p + 2) (end_ - (p + 2))
       else DenseWatchSliceOk F_cur k lit (p + 2) (end_ - (p + 2))) := by
  generalize hrem : end_ - p = rem at hslice
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hslice ⊢
  · cases hslice with
    | empty => omega
    | @bin _ rem' w0 hp hflag hne hot hent htail =>
      have hrem' : rem' = end_ - (p + 1) := by omega
      have hget : k.wstk[p]?.getD 0#32 = w0 := by rw [hp, Option.getD_some]
      simp only [hget, hflag, ne_eq, not_false_eq_true, ↓reduceIte]
      exact ⟨hne, hot, hent, by rwa [← hrem']⟩
    | @large _ rem' w0 cref hp hp1 hflag hcr_lt hcr_mem htail =>
      have hrem' : rem' = end_ - (p + 2) := by omega
      have hget : k.wstk[p]?.getD 0#32 = w0 := by rw [hp, Option.getD_some]
      simp only [hget, hflag, ne_eq, not_true_eq_false, ↓reduceIte]
      exact ⟨w0, cref, hp, hp1, hflag, by omega, hcr_lt, hcr_mem, by rwa [← hrem']⟩
  · cases hslice with
    | empty => omega
    | @bin _ rem' w0 hp hflag hne hot hent htail =>
      have hrem' : rem' = end_ - (p + 1) := by omega
      have hget : k.wstk[p]?.getD 0#32 = w0 := by rw [hp, Option.getD_some]
      simp only [hget, hflag, ne_eq, not_false_eq_true, ↓reduceIte]
      exact ⟨hne, hot, hent, by rwa [← hrem']⟩
    | @occ _ rem' w0 cref hp hp1 hflag _ hcr_lt hcr_mem htail =>
      have hrem' : rem' = end_ - (p + 2) := by omega
      have hget : k.wstk[p]?.getD 0#32 = w0 := by rw [hp, Option.getD_some]
      simp only [hget, hflag, ne_eq, not_true_eq_false, ↓reduceIte]
      exact ⟨w0, cref, hp, hp1, hflag, by omega, hcr_lt, hcr_mem, by rwa [← hrem']⟩

/-! ## 4. `Func.wp` Proofs: `full_bve_collect`, `full_bve_mark_and`, `full_bve_gates` -/

private theorem bve_collect_items_push {k : FullCoreState} {F_cur : List (List Nat)}
    {lit off cnt : Nat} {scr : List (BitVec 32)} {v : BitVec 32}
    (hlen : off + cnt < scr.length)
    (hold : ∀ j < cnt, FullBveItemOk k F_cur lit (scr[off + j]?.getD 0#32))
    (hnew : FullBveItemOk k F_cur lit v) :
    ∀ j < cnt + 1, FullBveItemOk k F_cur lit ((scr.set (off + cnt) v)[off + j]?.getD 0#32) := by
  intro j hj
  by_cases hjc : j = cnt
  · subst hjc; rw [List.getElem?_set_self hlen, Option.getD_some]; exact hnew
  · rw [List.getElem?_set_ne (by omega)]
    exact hold j (by omega)

private theorem full_bve_collect_core_wp (Γ : Env) :
    ∀ args m Q X, fullBveCollectCoreSpec args m Q X →
      Func.wp Γ full_bve_collect_body args m Q X := by
  rintro ⟨h, lit, out, cap, ⟨⟩⟩ m Q X
    ⟨c, F0, s, R, off, rfl, hinv, hlit, rfl, hcap, hm, hQ⟩
  have hmv := c.hmaxv; have hwc := c.hwcap; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmv hwc harc hsc
  have hcl := hinv.lengths.core_ok; have hsl := hinv.lengths.scratch_ok
  have hcv := hcl.cur_vars_le; have hwv := hcl.wvec_len; have hws := hcl.wstk_len_arr
  have harl := hcl.arena_len_arr; have harle := hcl.arena_len_le
  have hvll := hcl.vals_len; have hwl := hcl.wlen_le; have hscrl := hsl.scratch_buf_len
  obtain ⟨F_cur0, hw0⟩ := hinv.witness
  have hwbd := hw0.watches.bounds lit.toNat hlit
  unfold Func.wp full_bve_collect_body
  bve_steps!
  let hsh_eq : (BitVec.setWidth 64 lit <<< 1).toNat = 2 * lit.toNat := by c0_bound
  let hsh1_eq : (BitVec.setWidth 64 lit <<< 1 + 1).toNat = 2 * lit.toNat + 1 := by bv_omega
  let woff := s.core.wvec[2 * lit.toNat]'(by omega)
  let wsz := s.core.wvec[2 * lit.toNat + 1]'(by omega)
  have hwoff_eq : s.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'(by omega) = woff := by
    simp only [woff, hsh_eq]
  have hwsz_eq : s.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1).toNat]'(by omega) = wsz := by
    simp only [wsz, hsh1_eq]
  have hwoff_nat : woff.toNat = fullWatchOffCore s.core lit.toNat := by
    unfold fullWatchOffCore woff
    rw [List.getElem?_eq_getElem (by omega : 2 * lit.toNat < s.core.wvec.length), Option.getD_some]
  have hwsz_nat : wsz.toNat = fullWatchSizeCore s.core lit.toNat := by
    unfold fullWatchSizeCore wsz
    rw [List.getElem?_eq_getElem (by omega : 2 * lit.toNat + 1 < s.core.wvec.length),
      Option.getD_some]
  let end_bv : BitVec 64 := woff.setWidth 64 + wsz.setWidth 64
  have hw_sum_lt : woff.toNat + wsz.toNat < 2 ^ 64 := by omega
  have hw1 : (woff.setWidth 64).toNat = woff.toNat := by bv_omega
  have hw2 : (wsz.setWidth 64).toNat = wsz.toNat := by bv_omega
  have hend_bv_nat : (woff.setWidth 64 + wsz.setWidth 64).toNat = woff.toNat + wsz.toNat := by
    bv_omega
  have hend_nat : end_bv.toNat = fullWatchOffCore s.core lit.toNat +
      fullWatchSizeCore s.core lit.toNat := by
    change (woff.setWidth 64 + wsz.setWidth 64).toNat = _
    rw [hend_bv_nat, hwoff_nat, hwsz_nat]
  simp only [hwoff_eq, hwsz_eq]
  refine wp_loop_inv (ts := [i64, i32])
    (fun (p, cnt, _) ml =>
      ∃ scr',
        woff.toNat ≤ p.toNat ∧ p.toNat ≤ end_bv.toNat ∧ cnt.toNat ≤ cap.toNat ∧
        scr'.length = c.scratch_cap ∧
        (∀ k < c.scratch_cap, k < off ∨ off + cap.toNat ≤ k →
          scr'[k]? = s.scratch.scratch_buf[k]?) ∧
        (∀ F_cur, FullWitnessInv c F0 F_cur s.core →
          (if s.core.dense_mode = 0#64 then
            WatchSliceOk F_cur s.core lit.toNat p.toNat (end_bv.toNat - p.toNat)
           else
            DenseWatchSliceOk F_cur s.core lit.toNat p.toNat (end_bv.toNat - p.toNat)) ∧
          ∀ k < cnt.toNat,
            FullBveItemOk s.core F_cur lit.toNat (scr'[off + k]?.getD 0#32)) ∧
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) ml)
    (fun (p, _, _) _ => end_bv.toNat - p.toNat)
    ?_ ?_
  · intro J_lp hJ_lp
    bve_steps!
    refine hJ_lp (woff.setWidth 64, 0#32, PUnit.unit) m ⟨s.scratch.scratch_buf, ?_, ?_, ?_, hscrl,
      fun _ _ _ => rfl, ?_, hm⟩
    · simp [hw1]
    · rw [hw1]; change _ ≤ (woff.setWidth 64 + wsz.setWidth 64).toNat
      rw [hend_bv_nat]; omega
    · simp
    · intro F_cur hw; refine ⟨?_, fun _ hk => by simp at hk⟩
      have hslc := hw.watches
      by_cases hdm : s.core.dense_mode = 0#64 <;>
        simp only [ModeWatchesInv, hdm, ↓reduceIte] at hslc ⊢
      · simpa [hw1, hend_nat, hwoff_nat] using hslc.slices lit.toNat hlit
      · simpa [hw1, hend_nat, hwoff_nat] using hslc.slices lit.toNat hlit
  · rintro J_lp ⟨p, cnt, ⟨⟩⟩ ml ⟨scr', hp_ge, hp_le, hcnt_le, hlen', hout, hitems, hm_lp⟩ ih
    bve_steps
    · have hp_lt : p.toNat < end_bv.toNat := by
        change p.toNat < (woff.setWidth 64 + wsz.setWidth 64).toNat; bv_omega
      have hp_wstk : p.toNat < s.core.wstk.length := by omega
      have hw0_get : s.core.wstk[p.toNat]? = some (s.core.wstk[p.toNat]'hp_wstk) :=
        List.getElem?_eq_getElem hp_wstk
      have hbin_at : (s.core.wstk[p.toNat]'hp_wstk &&& 0x80000000#32) ≠ 0#32 := hc
      have hbin : (s.core.wstk[p.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
        rw [hw0_get, Option.getD_some]; exact hbin_at
      have hstep0 := modeWatchSlice_step hp_lt (hitems F_cur0 hw0).1
      rw [ite_eq_left hbin, hw0_get, Option.getD_some] at hstep0
      have hot_cv : (s.core.wstk[p.toNat]'hp_wstk &&& 0x7FFFFFFF#32).toNat <
          2 * s.core.cur_vars := hstep0.2.1
      have hot_lt : (s.core.wstk[p.toNat]'hp_wstk &&& 0x7FFFFFFF#32).toNat <
          s.core.vals.length := by omega
      bve_steps!
      · -- vals[ot] > 0 -> continue (p + 1, cnt)
        have hlt_mu : end_bv.toNat - (p + 1).toNat < end_bv.toNat - p.toNat := by bv_omega
        have hp1_nat : (p + 1).toNat = p.toNat + 1 := by bv_omega
        refine ih (p + 1, cnt, PUnit.unit) ml hlt_mu ⟨scr', by bv_omega, by bv_omega, hcnt_le,
          hlen', hout, fun F_cur hw => ?_, hm_lp⟩
        have hstF := modeWatchSlice_step hp_lt (hitems F_cur hw).1
        rw [ite_eq_left hbin] at hstF
        refine ⟨?_, (hitems F_cur hw).2⟩
        rw [hp1_nat]; exact hstF.2.2.2
      · -- cnt >= cap -> return 0xFFFFFFFF
        exact hQ 0xFFFFFFFF#32 scr' ml ⟨hcl, { hsl with scratch_buf_len := hlen' }⟩
          (Or.inl rfl) hout (fun _ _ hne => absurd rfl hne) hm_lp
      · -- store out[cnt] = w0 and continue (p + 1, cnt + 1)
        have hlt_cnt : cnt.toNat < cap.toNat := by bv_omega
        have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by bv_omega
        have hp1_nat : (p + 1).toNat = p.toNat + 1 := by bv_omega
        have hlt_mu : end_bv.toNat - (p + 1).toNat < end_bv.toNat - p.toNat := by bv_omega
        refine ih (p + 1, cnt + 1#32, PUnit.unit) m hlt_mu
          ⟨scr'.set (off + cnt.toNat) (s.core.wstk[p.toNat]'hp_wstk),
            by bv_omega, by bv_omega, by omega, by simp [hlen'],
            fun k hk1 hk2 => by
              rw [List.getElem?_set_ne (by omega)]; exact hout k hk1 hk2,
            fun F_cur hw => ?_, hm⟩
        have hstF := modeWatchSlice_step hp_lt (hitems F_cur hw).1
        rw [ite_eq_left hbin] at hstF
        have hnew_item : FullBveItemOk s.core F_cur lit.toNat
            (s.core.wstk[p.toNat]'hp_wstk) := by
          unfold FullBveItemOk
          rw [ite_eq_left hbin_at]
          rw [hw0_get, Option.getD_some] at hstF
          exact ⟨hstF.1, hstF.2.1, hstF.2.2.1⟩
        refine ⟨?_, ?_⟩
        · rw [hp1_nat]; exact hstF.2.2.2
        · rw [hcnt1]; exact bve_collect_items_push (by omega) (hitems F_cur hw).2 hnew_item
    · -- occ/large entry with p + 1 >= end (impossible by WatchSliceOk)
      have hp_lt : p.toNat < end_bv.toNat := by
        change p.toNat < (woff.setWidth 64 + wsz.setWidth 64).toNat; bv_omega
      have hp_wstk : p.toNat < s.core.wstk.length := by omega
      have hw0_get : s.core.wstk[p.toNat]? = some (s.core.wstk[p.toNat]'hp_wstk) :=
        List.getElem?_eq_getElem hp_wstk
      have hnb : ¬ (s.core.wstk[p.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
        have hflag0 : (s.core.wstk[p.toNat]'hp_wstk &&& 0x80000000#32) = 0#32 := by assumption
        rw [hw0_get, Option.getD_some]; exact fun h => h hflag0
      have hstep0 := modeWatchSlice_step hp_lt (hitems F_cur0 hw0).1
      rw [ite_eq_right hnb] at hstep0
      obtain ⟨_, _, _, _, _, hp1_lt, _⟩ := hstep0
      exfalso; bv_omega
    · -- occ/large entry: wstk[p+1] = cref
      have hp_lt : p.toNat < end_bv.toNat := by
        change p.toNat < (woff.setWidth 64 + wsz.setWidth 64).toNat; bv_omega
      have hp_wstk : p.toNat < s.core.wstk.length := by omega
      have hw0_get : s.core.wstk[p.toNat]? = some (s.core.wstk[p.toNat]'hp_wstk) :=
        List.getElem?_eq_getElem hp_wstk
      have hnb : ¬ (s.core.wstk[p.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
        have hflag0 : (s.core.wstk[p.toNat]'hp_wstk &&& 0x80000000#32) = 0#32 := by assumption
        rw [hw0_get, Option.getD_some]; exact fun h => h hflag0
      have hstep0 := modeWatchSlice_step hp_lt (hitems F_cur0 hw0).1
      rw [ite_eq_right hnb] at hstep0
      obtain ⟨w0, cref, hp_eq, hp1_eq, hflag, hp1_lt, _, hcr_mem, _⟩ := hstep0
      have hp1_nat : (p + 1).toNat = p.toNat + 1 := by bv_omega
      have hp1_wstk : (p + 1).toNat < s.core.wstk.length := by bv_omega
      have hcr_eq : s.core.wstk[(p + 1).toNat]'hp1_wstk = cref := by
        have h1 : s.core.wstk[(p + 1).toNat]? = some cref := by rw [hp1_nat]; exact hp1_eq
        exact Option.some.inj ((List.getElem?_eq_getElem hp1_wstk).symm.trans h1)
      have hcr_wf := (hw0.arena.refs_wf cref.toNat hcr_mem).1
      have hcr_ar : cref.toNat < s.core.arena.length := by omega
      have hcr_ld : (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'hp1_wstk)).toNat <
          s.core.arena.length := by rw [bv_c0_zext32_64, hcr_eq]; exact hcr_ar
      bve_steps!
      · -- (ar[cr] & (PH_GARB | PH_RED)) != 0 -> continue (p + 2, cnt)
        have hlt_mu : end_bv.toNat - (p + 1 + 1).toNat < end_bv.toNat - p.toNat := by bv_omega
        have hp2_nat : (p + 1 + 1).toNat = p.toNat + 2 := by bv_omega
        refine ih (p + 1 + 1, cnt, PUnit.unit) ml hlt_mu ⟨scr', by bv_omega, by bv_omega, hcnt_le,
          hlen', hout, fun F_cur hw => ?_, hm_lp⟩
        have hstF := modeWatchSlice_step hp_lt (hitems F_cur hw).1
        rw [ite_eq_right hnb] at hstF
        obtain ⟨_, _, _, _, _, _, _, _, htail⟩ := hstF
        refine ⟨?_, (hitems F_cur hw).2⟩
        rw [hp2_nat]; exact htail
      · -- cnt >= cap -> return 0xFFFFFFFF
        exact hQ 0xFFFFFFFF#32 scr' ml ⟨hcl, { hsl with scratch_buf_len := hlen' }⟩
          (Or.inl rfl) hout (fun _ _ hne => absurd rfl hne) hm_lp
      · -- store out[cnt] = cref and continue (p + 2, cnt + 1)
        have hlt_cnt : cnt.toNat < cap.toNat := by bv_omega
        have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by bv_omega
        have hp2_nat : (p + 1 + 1).toNat = p.toNat + 2 := by bv_omega
        have hlt_mu : end_bv.toNat - (p + 1 + 1).toNat < end_bv.toNat - p.toNat := by bv_omega
        have hgarb_f : fullArenaClauseGarbCore s.core cref.toNat = false := by
          have hcr_idx_eq :
              s.core.wstk[(p.toNat + (1#64).toNat) % 2 ^ 64]'(by bv_omega) = cref := by
            have heq_i : (p.toNat + (1#64).toNat) % 2 ^ 64 = (p + 1).toNat := by bv_omega
            simp only [heq_i]; exact hcr_eq
          have hand0_raw :
              s.core.arena[(s.core.wstk[(p.toNat + (1#64).toNat) % 2 ^ 64]'(by bv_omega)).toNat]'(
                by simp only [hcr_idx_eq]; exact hcr_ar) &&& (0x00080000#32 ||| 0x00400000#32) =
                0#32 := by
            assumption
          have hand0 : s.core.arena[cref.toNat]'hcr_ar &&&
              (0x00080000#32 ||| 0x00400000#32) = 0#32 := by
            simpa only [hcr_idx_eq] using hand0_raw
          have hg := (bv32_and_0x480000_eq_zero _ hand0).1
          unfold fullArenaClauseGarbCore fullArenaHdrCore
          rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some, hg]; rfl
        refine ih (p + 1 + 1, cnt + 1#32, PUnit.unit) m hlt_mu
          ⟨scr'.set (off + cnt.toNat) (s.core.wstk[(p + 1).toNat]'hp1_wstk),
            by bv_omega, by bv_omega, by omega, by simp [hlen'],
            fun k hk1 hk2 => by
              rw [List.getElem?_set_ne (by omega)]; exact hout k hk1 hk2,
            fun F_cur hw => ?_, hm⟩
        have hstF := modeWatchSlice_step hp_lt (hitems F_cur hw).1
        rw [ite_eq_right hnb] at hstF
        obtain ⟨_, cref', _, hp1_eq', _, _, _, hcr_mem', htail⟩ := hstF
        have hcreq : cref' = cref := Option.some.inj (hp1_eq'.symm.trans hp1_eq)
        have hnew_item : FullBveItemOk s.core F_cur lit.toNat
            (s.core.wstk[(p + 1).toNat]'hp1_wstk) := by
          rw [hcr_eq]; unfold FullBveItemOk
          have hnot : ¬ (cref &&& 0x80000000#32) ≠ 0#32 := by
            have hlt31 : cref.toNat < 2 ^ 31 :=
              Classical.byContradiction fun hn => by
                have hmod : (cref &&& 0x7FFFFFFF#32).toNat = cref.toNat % 2 ^ 31 :=
                  bv32_and_litMask_toNat cref
                omega
            simp [bv32_and_msb_eq_zero_of_lt hlt31]
          rw [ite_eq_right hnot]
          exact ⟨hcreq ▸ hcr_mem', hgarb_f⟩
        refine ⟨?_, ?_⟩
        · rw [hp2_nat]; exact htail
        · rw [hcnt1]; exact bve_collect_items_push (by omega) (hitems F_cur hw).2 hnew_item
    · have heq_end : p.toNat = end_bv.toNat := by
        change p.toNat = (woff.setWidth 64 + wsz.setWidth 64).toNat; bv_omega
      exact hQ cnt scr' ml ⟨hcl, { hsl with scratch_buf_len := hlen' }⟩ (Or.inr hcnt_le)
        hout (fun F_cur hw _ => (hitems F_cur hw).2) hm_lp

theorem full_bve_collect_wp (Γ : Env) :
    ∀ args m Q X, fullBveCollectSpec args m Q X → Func.wp Γ full_bve_collect_body args m Q X := by
  rintro ⟨h, lit, out, cap, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, off, R, rfl, hdw, hlit, rfl, hcap, hm, hQ⟩
  refine full_bve_collect_core_wp Γ _ m Q X
    ⟨c, F0, s, R, off, rfl, ⟨hdw.1, F_cur, hdw.2.1⟩, hlit, rfl, hcap, hm, ?_⟩
  intro r scr' m' s' hlen' hbd hout hitems hm'
  refine hQ r scr' m' hlen'.scratch_ok.scratch_buf_len hout ?_ hm'
  rcases hbd with rfl | hle
  · exact Or.inl rfl
  · refine Or.inr ⟨hle, fun k hk => ?_⟩
    have hsc := c.hscr; unfold dimacsBound at hsc
    exact (hitems F_cur hdw.2.1 (by intro heq; simp [heq] at hle; omega) k hk).to_entryW

private theorem litMark_set_agree_outside {lm0 : List (BitVec 8)} {ar : List (BitVec 32)}
    {cr i n : Nat} {v : BitVec 8}
    (hagree : ∀ l < n, (∀ j < i, (ar[cr + 3 + j]?.getD 0#32).toNat ^^^ 1 ≠ l) →
      lm0[l]? = some 0#8)
    (hi : cr + 3 + i < ar.length) :
    let idx := ((ar[cr + 3 + i]'hi ^^^ 1#32)).toNat
    ∀ l < n, (∀ j < i + 1, (ar[cr + 3 + j]?.getD 0#32).toNat ^^^ 1 ≠ l) →
      (lm0.set idx v)[l]? = some 0#8 := by
  intro idx l hl hnone
  have hne : idx ≠ l := by
    have h0 := hnone i (Nat.lt_succ_self i)
    rw [List.getElem?_eq_getElem hi, Option.getD_some] at h0
    exact h0
  rw [List.getElem?_set_ne hne]
  exact hagree l hl fun j hj => hnone j (Nat.lt_succ_of_lt hj)

private theorem litMark_clear_step {lm : List (BitVec 8)} {ar : List (BitVec 32)}
    {cr sz i n : Nat} (hi_lt : cr + 3 + i < ar.length)
    (hidx_lt : ((ar[cr + 3 + i]'hi_lt ^^^ 1#32)).toNat < n)
    (hml : lm.length = n)
    (hcov : ∀ l < n,
      ((∃ j < i, (ar[cr + 3 + j]?.getD 0#32).toNat ^^^ 1 = l) ∨
       (∀ j < sz, (ar[cr + 3 + j]?.getD 0#32).toNat ^^^ 1 ≠ l)) → lm[l]? = some 0#8) :
    let idx := ((ar[cr + 3 + i]'hi_lt ^^^ 1#32)).toNat
    ∀ l < n,
      ((∃ j < i + 1, (ar[cr + 3 + j]?.getD 0#32).toNat ^^^ 1 = l) ∨
       (∀ j < sz, (ar[cr + 3 + j]?.getD 0#32).toNat ^^^ 1 ≠ l)) →
      (lm.set idx 0#8)[l]? = some 0#8 := by
  intro idx l hl hc
  by_cases heq : l = idx
  · subst heq; rw [List.getElem?_set_self (by omega)]
  · rw [List.getElem?_set_ne (Ne.symm heq)]
    refine hcov l hl ?_
    rcases hc with ⟨j, hj, hjl⟩ | hnone
    · left
      have hji : j ≠ i := by
        rintro rfl; apply heq; rw [← hjl, List.getElem?_eq_getElem hi_lt, Option.getD_some]; rfl
      exact ⟨j, by omega, hjl⟩
    · exact Or.inr hnone

private theorem full_bve_mark_and_slice_wp (Γ : Env) :
    ∀ args m Q X, fullBveMarkAndSliceSpec args m Q X →
      Func.wp Γ full_bve_mark_and_body args m Q X := by
  rintro ⟨h, v_lit, cr, n_off, nn, ⟨⟩⟩ m Q X
    ⟨c, s, R, ⟨rfl, hlm_clr, href, _hgarb, hlits_lt, hcr_bd, h132, hn_bd, hn_bin⟩,
     hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at *
  have hmv := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmv harc hsc
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv := hcl.cur_vars_le; have harl := hcl.arena_len_arr; have harle := hcl.arena_len_le
  have hlml := hcl.lit_mark_len; have hscrl := hsl.scratch_buf_len
  have hcr2_nat : (cr.setWidth 64 + 2).toNat = cr.toNat + 2 := by bv_omega
  have hcr2_lt : (cr.setWidth 64 + 2).toNat < s.core.arena.length := by bv_omega
  let sz := s.core.arena[cr.toNat + 2]'(by omega)
  have hsz_eq : s.core.arena[(cr.setWidth 64 + 2).toNat]'hcr2_lt = sz := by
    simp only [sz, hcr2_nat]
  have hsz_nat : sz.toNat = fullArenaClauseSize s cr.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore sz
    rw [List.getElem?_eq_getElem (by omega : cr.toNat + 2 < s.core.arena.length), Option.getD_some]
  have hcr_sz_bd : cr.toNat + 3 + sz.toNat ≤ s.core.arena_len := by rw [hsz_nat]; exact hcr_bd
  have hlit_lt_at : ∀ j < sz.toNat,
      (s.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat < 2 * c.max_vars := fun j hj => by
    rw [List.getElem?_eq_getElem (by omega : cr.toNat + 3 + j < s.core.arena.length),
      Option.getD_some]
    apply hlits_lt
    unfold fullArenaClauseLits
    rw [mem_fullArenaClauseLitsCore_iff (by unfold fullArenaClauseSize at hcr_bd; omega)]
    exact ⟨j, by simpa [fullArenaClauseSize, ← hsz_nat] using hj, rfl⟩
  unfold Func.wp full_bve_mark_and_body
  bve_steps!
  simp only [hsz_eq]
  refine wp_loop_inv
    (fun (need, i, _) m1 =>
      i.toNat ≤ sz.toNat ∧ need.toNat ≤ i.toNat ∧
      ∃ lm1, lm1.length = 2 * c.max_vars ∧
      (∀ l < 2 * c.max_vars,
        (∀ j < i.toNat, (s.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat ^^^ 1 ≠ l) →
        lm1[l]? = some 0#8) ∧
      (FullMem c { s with core := { s.core with lit_mark := lm1 } } ⋆ R) m1)
    (fun (_, i, _) _ => sz.toNat - i.toNat)
    (fun J1 hJ1 => by
      bve_steps!
      exact hJ1 _ _ ⟨Nat.zero_le _, Nat.le_refl _, s.core.lit_mark, hlml, fun l hl _ => by
        have := hlm_clr.2 l hl
        rw [List.getElem?_eq_getElem (by omega : l < s.core.lit_mark.length), Option.getD_some]
          at this
        rw [List.getElem?_eq_getElem (by omega : l < s.core.lit_mark.length), this], hm⟩)
    (fun J1 ⟨need, i, ⟨⟩⟩ m1 ⟨hi_le, hneed_le, lm1, hlm1_len, hlm1_ag, hm1⟩ ih1 => by
      bve_steps
      · have hi_lt : i.toNat < sz.toNat := by bv_omega
        have har_idx : (cr.setWidth 64 + 3 + i.setWidth 64).toNat <
            s.core.arena.length := by bv_omega
        have har_nat : (cr.setWidth 64 + 3 + i.setWidth 64).toNat = cr.toNat + 3 + i.toNat := by
          bv_omega
        have hl_ar : (s.core.arena[(cr.setWidth 64 + 3 + i.setWidth 64).toNat]'har_idx).toNat <
            2 * c.max_vars := by
          have := hlit_lt_at i.toNat hi_lt
          rw [List.getElem?_eq_getElem (by omega : cr.toNat + 3 + i.toNat < s.core.arena.length),
            Option.getD_some] at this
          have hidx_eq : s.core.arena[(cr.setWidth 64 + 3 + i.setWidth 64).toNat]'har_idx =
              s.core.arena[cr.toNat + 3 + i.toNat]'(by omega) := by
            simp only [har_nat]
          rw [hidx_eq]; exact this
        have hidx_lt : (BitVec.setWidth 64 (s.core.arena[(cr.setWidth 64 + 3 +
            i.setWidth 64).toNat]'har_idx ^^^ 1#32)).toNat <
            ({ s with core := { s.core with lit_mark := lm1 } } : FullState
              ).core.lit_mark.length := by
          change (BitVec.setWidth 64 _).toNat < lm1.length
          rw [bv_c0_zext32_64, hlm1_len]; exact bv32_xor_1_lt hl_ar
        bve_steps!
        have hi_ar2 : cr.toNat + 3 + i.toNat < s.core.arena.length := by omega
        have hneed1 : (need + 1#32).toNat ≤ (i + 1#32).toNat := by bv_omega
        refine ih1 (need + 1#32, i + 1#32, PUnit.unit) _ (by bv_omega)
          ⟨by bv_omega, hneed1,
            lm1.set (s.core.arena[(cr.setWidth 64 + 3 + i.setWidth 64).toNat]'har_idx ^^^
              1#32).toNat 1#8,
            by simp [hlm1_len], fun l hl hnone => ?_, ?_⟩
        · have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
          have hidx_eq :
              (s.core.arena[(cr.setWidth 64 + 3 + i.setWidth 64).toNat]'har_idx ^^^ 1#32).toNat =
              (s.core.arena[cr.toNat + 3 + i.toNat]'hi_ar2 ^^^ 1#32).toNat := by
            simp only [har_nat]
          rw [hidx_eq]
          exact litMark_set_agree_outside (v := 1#8) hlm1_ag hi_ar2 l hl
            (fun j hj => hnone j (by omega))
        · rw [← bv_c0_zext32_64]; assumption
      · have hi_lt : i.toNat < sz.toNat := by bv_omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        exact ih1 (need, i + 1#32, PUnit.unit) m1 (by bv_omega)
          ⟨by bv_omega, by bv_omega, lm1, hlm1_len, fun l hl hnone =>
            hlm1_ag l hl (fun j hj => hnone j (by omega)), hm1⟩
      · have hi_eq : i.toNat = sz.toNat := by bv_omega
        have hlm1_zero : ∀ l < 2 * c.max_vars,
            (∀ j < sz.toNat, (s.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat ^^^ 1 ≠ l) →
            lm1[l]? = some 0#8 := fun l hl hnone =>
          hlm1_ag l hl (fun j hj => hnone j (by omega))
        bve_steps!
        refine wp_loop_inv (ts := [i32, i64, i32])
          (fun (_matched, _nmask, j, _) m2 => j.toNat ≤ nn.toNat ∧ m2 = m1)
          (fun (_, _, j, _) _ => nn.toNat - j.toNat)
          (fun J2 hJ2 => by
            bve_steps!
            exact hJ2 _ _ ⟨Nat.zero_le _, rfl⟩)
          (fun J2 ⟨matched, nmask, j, ⟨⟩⟩ m2 ⟨hj_le, rfl⟩ ih2 => by
            bve_steps
            · have hj_lt : j.toNat < nn.toNat := by bv_omega
              have hscr_idx : (n_off + j).toNat < s.scratch.scratch_buf.length := by bv_omega
              have hno_nat : (n_off + j).toNat = n_off.toNat + j.toNat := by bv_omega
              have hscr_idx64 : (BitVec.setWidth 64 (n_off + j)).toNat <
                  s.scratch.scratch_buf.length := by rw [bv_c0_zext32_64]; exact hscr_idx
              have hbin : (s.scratch.scratch_buf[(n_off + j).toNat]'hscr_idx &&&
                  0x80000000#32) ≠ 0#32 := hc
              have hw_lt : (s.scratch.scratch_buf[(n_off + j).toNat]'hscr_idx &&&
                    0x7FFFFFFF#32).toNat < 2 * c.max_vars := by
                have := hn_bin j.toNat hj_lt
                rw [← hno_nat, List.getElem?_eq_getElem hscr_idx, Option.getD_some] at this
                exact this hbin
              have hlm1_idx : (BitVec.setWidth 64
                  (s.scratch.scratch_buf[(BitVec.setWidth 64 (n_off + j)).toNat]'hscr_idx64 &&&
                    0x7FFFFFFF#32)).toNat <
                  ({ s with core := { s.core with lit_mark := lm1 } } : FullState
                    ).core.lit_mark.length := by
                change (BitVec.setWidth 64 _).toNat < lm1.length
                simp only [bv_c0_zext32_64] at *; rw [hlm1_len]; exact hw_lt
              bve_steps! <;> exact ih2 _ _ (by bv_omega) ⟨by bv_omega, rfl⟩
            · exact ih2 _ _ (by bv_omega) ⟨by bv_omega, rfl⟩
            · bve_steps!
              refine wp_loop_inv (ts := [i32])
                (fun (i3, _) m3 =>
                  i3.toNat ≤ sz.toNat ∧
                  ∃ lm', lm'.length = 2 * c.max_vars ∧
                  (∀ l < 2 * c.max_vars,
                    ((∃ j < i3.toNat,
                        (s.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat ^^^ 1 = l) ∨
                     (∀ j < sz.toNat,
                        (s.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat ^^^ 1 ≠ l)) →
                    lm'[l]? = some 0#8) ∧
                  (FullMem c { s with core := { s.core with lit_mark := lm' } } ⋆ R) m3)
                (fun (i3, _) _ => sz.toNat - i3.toNat)
                ?_ ?_
              · intro J3 hJ3; bve_steps!
                exact hJ3 (0#32, PUnit.unit) m2 ⟨Nat.zero_le _, lm1, hlm1_len, fun l hl hc => by
                  rcases hc with ⟨j, hj, _⟩ | hnone
                  · bv_omega
                  · exact hlm1_zero l hl hnone, hm1⟩
              · rintro J3 ⟨i3, ⟨⟩⟩ m3 ⟨hi3_le, lm', hlm'_len, hlm'_cov, hm3⟩ ih3
                bve_steps
                · have hi3_lt : i3.toNat < sz.toNat := by bv_omega
                  have har_idx : (cr.setWidth 64 + 3 + i3.setWidth 64).toNat <
                      s.core.arena.length := by bv_omega
                  have har_nat : (cr.setWidth 64 + 3 + i3.setWidth 64).toNat =
                      cr.toNat + 3 + i3.toNat := by bv_omega
                  have hl_ar : (s.core.arena[(cr.setWidth 64 + 3 +
                      i3.setWidth 64).toNat]'har_idx).toNat < 2 * c.max_vars := by
                    have := hlit_lt_at i3.toNat hi3_lt
                    rw [List.getElem?_eq_getElem
                      (by omega : cr.toNat + 3 + i3.toNat < s.core.arena.length),
                      Option.getD_some] at this
                    have hidx_eq : s.core.arena[(cr.setWidth 64 + 3 +
                        i3.setWidth 64).toNat]'har_idx =
                        s.core.arena[cr.toNat + 3 + i3.toNat]'(by omega) := by
                      simp only [har_nat]
                    rw [hidx_eq]; exact this
                  have hidx_lt : (s.core.arena[(cr.setWidth 64 + 3 +
                      i3.setWidth 64).toNat]'har_idx ^^^ 1#32).toNat < lm'.length := by
                    rw [hlm'_len]; exact bv32_xor_1_lt hl_ar
                  have hidx3_st : (BitVec.setWidth 64 (s.core.arena[(cr.setWidth 64 + 3 +
                      i3.setWidth 64).toNat]'har_idx ^^^ 1#32)).toNat <
                      ({ s with core := { s.core with lit_mark := lm' } } :
                        FullState).core.lit_mark.length := by
                    change (BitVec.setWidth 64 _).toNat < lm'.length
                    rw [bv_c0_zext32_64]; exact hidx_lt
                  bve_steps!
                  have hi_ar2 : cr.toNat + 3 + i3.toNat < s.core.arena.length := by omega
                  have hidx_eq :
                      (s.core.arena[(cr.setWidth 64 + 3 + i3.setWidth 64).toNat]'har_idx ^^^
                        1#32).toNat =
                      (s.core.arena[cr.toNat + 3 + i3.toNat]'hi_ar2 ^^^ 1#32).toNat := by
                    simp only [har_nat]
                  have hcov' := litMark_clear_step hi_ar2
                    (by rw [← hidx_eq, ← hlm'_len]; exact hidx_lt) hlm'_len hlm'_cov
                  refine ih3 (i3 + 1#32, PUnit.unit) _ (by bv_omega) ⟨by bv_omega,
                    lm'.set (s.core.arena[(cr.setWidth 64 + 3 +
                      i3.setWidth 64).toNat]'har_idx ^^^ 1#32).toNat 0#8,
                    by simp [hlm'_len], fun l hl hc => ?_, ?_⟩
                  · rw [show (i3 + 1#32).toNat = i3.toNat + 1 from by bv_omega] at hc
                    rw [hidx_eq]
                    exact hcov' l hl hc
                  · rw [← bv_c0_zext32_64]; assumption
                · have hi3_eq : i3.toNat = sz.toNat := by bv_omega
                  have heq_lm : lm' = s.core.lit_mark := by
                    refine fullLitMark_eq_of_all_zero hlml hlm'_len hlm_clr.2 fun l hl => ?_
                    apply hlm'_cov l hl
                    by_cases hex : ∃ j < sz.toNat,
                        (s.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat ^^^ 1 = l
                    · exact Or.inl (hi3_eq ▸ hex)
                    · exact Or.inr fun j hj heq => hex ⟨j, hj, heq⟩
                  subst heq_lm
                  have h130_lt : 520 / 4 < s.scratch.scratch_buf.length := by omega
                  have h131_lt : 524 / 4 < s.scratch.scratch_buf.length := by omega
                  bve_steps!
                  let scr' := (s.scratch.scratch_buf.set (520 / 4) (nmask.setWidth 32)).set
                    (524 / 4) ((nmask >>> 32).setWidth 32)
                  let s' : FullState :=
                    { s with scratch := { s.scratch with scratch_buf := scr' } }
                  refine hQ (true, PUnit.unit) s' _ (PreservesCoreSlice.refl _ _)
                    ⟨hcl, { hsl with scratch_buf_len := by dsimp only [s', scr']; simp [hscrl] }⟩
                    ⟨scr', rfl, fun k _ hk1 hk2 => by
                      simp only [scr']
                      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]⟩
                    (by assumption)
                · have hi3_eq : i3.toNat = sz.toNat := by bv_omega
                  have heq_lm : lm' = s.core.lit_mark := by
                    refine fullLitMark_eq_of_all_zero hlml hlm'_len hlm_clr.2 fun l hl => ?_
                    apply hlm'_cov l hl
                    by_cases hex : ∃ j < sz.toNat,
                        (s.core.arena[cr.toNat + 3 + j]?.getD 0#32).toNat ^^^ 1 = l
                    · exact Or.inl (hi3_eq ▸ hex)
                    · exact Or.inr fun j hj heq => hex ⟨j, hj, heq⟩
                  subst heq_lm
                  exact hQ (false, PUnit.unit) s _ (PreservesCoreSlice.refl _ _) hlen
                    ⟨s.scratch.scratch_buf, rfl, fun _ _ _ _ => rfl⟩ (by assumption)))

theorem FullDenseInvW.with_litMark_scr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} {scr' : List (BitVec 32)}
    (hll : lm'.length = 2 * c.max_vars) (hsl : scr'.length = c.scratch_cap)
    (hlmc : FullLitMarksClear c { s with core := { s.core with lit_mark := lm' } }) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with lit_mark := lm' }
        scratch := { s.scratch with scratch_buf := scr' } } := by
  refine ⟨⟨{ h.1.core_ok with lit_mark_len := hll },
           { h.1.scratch_ok with scratch_buf_len := hsl }⟩,
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    hlmc, h.2.2.2.1, ⟨fun i hi => h.2.2.2.2.1.1 i hi, h.2.2.2.2.1.2⟩,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem full_bve_mark_and_wp (Γ : Env) :
    ∀ args m Q X, fullBveMarkAndSpec args m Q X →
      Func.wp Γ full_bve_mark_and_body args m Q X := by
  rintro ⟨h, v_lit, cr, n_off, nn, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdw, h132, href, hgarb, hn_bd, hn_ok, hm, hQ⟩
  refine full_bve_mark_and_slice_wp Γ _ m Q X ⟨c, s, R, ?_, hdw.1, hm, ?_⟩
  · refine ⟨rfl, hdw.2.2.1, href, hgarb, ?_,
      (by have := hdw.2.1.arena.refs_wf cr.toNat href; unfold fullArenaClauseSize; omega),
      h132, hn_bd, fun j hj hb => ?_⟩
    · intro l hl
      exact Nat.lt_of_lt_of_le (hdw.2.1.arena.lits_lt _ href hgarb l hl)
        (Nat.mul_le_mul_left 2 hdw.1.core_ok.cur_vars_le)
    · have hwf := hn_ok j hj
      unfold FullBveEntryOkW at hwf; rw [ite_eq_left hb] at hwf
      exact Nat.lt_of_lt_of_le hwf.1 (Nat.mul_le_mul_left 2 hdw.1.core_ok.cur_vars_le)
  · rintro ⟨ok, ⟨⟩⟩ s' m' hcore hlen ⟨scr', hsc_eq, hout⟩ hm'
    have hcore_eq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
    have hcore_up : { s.core with lit_mark := s.core.lit_mark } = s.core := by
      cases s.core; rfl
    have hs' : s' =
        { s with
          core := { s.core with lit_mark := s.core.lit_mark }
          scratch := { s.scratch with scratch_buf := scr' } } := by
      cases s'; dsimp only at hcore_eq hsc_eq; rw [hcore_eq, hsc_eq, hcore_up]
    rw [hs'] at hlen hm'
    refine hQ ok s.core.lit_mark scr' m' ?_ hout hm'
    exact FullDenseInvW.with_litMark_scr hdw hdw.1.core_ok.lit_mark_len
      hlen.scratch_ok.scratch_buf_len hdw.2.2.1

theorem full_bve_gates_wp (Γ : Env)
    (hMark : ∀ xs m Q X, fullBveMarkAndSpec xs m Q X →
      Γ "full_bve_mark_and" [i64, i32, i32, i32, i32] [.bool] xs m Q X) :
    ∀ args m Q X, fullBveGatesSpec args m Q X → Func.wp Γ full_bve_gates_body args m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdw, h132, hv_lt, hnp, hnn, hpos, hneg, hm, hQ⟩
  have hmv := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmv hsc
  have hlen := hdw.1; have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv := hcl.cur_vars_le; have hlml := hcl.lit_mark_len; have hscrl := hsl.scratch_buf_len
  have h128_lt : 512 / 4 < s.scratch.scratch_buf.length := by omega
  have h129_lt : 516 / 4 < s.scratch.scratch_buf.length := by omega
  have h130_lt : 520 / 4 < s.scratch.scratch_buf.length := by omega
  have h131_lt : 524 / 4 < s.scratch.scratch_buf.length := by omega
  unfold Func.wp full_bve_gates_body
  bve_steps!
  refine wp_loop_inv (ts := [i32])
    (fun (i, _) mi =>
      i.toNat ≤ np.toNat ∧
      ∃ (lm' : List (BitVec 8)) (scr' : List (BitVec 32)),
        let si : FullState :=
          { s with
            core := { s.core with lit_mark := lm' }
            scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur si ∧
        (∀ k < c.scratch_cap, k < 128 ∨ 132 ≤ k → scr'[k]? = s.scratch.scratch_buf[k]?) ∧
        (FullMem c si ⋆ R) mi)
    (fun (i, _) _ => np.toNat - i.toNat)
    ?_ ?_
  · intro J hJ; bve_steps!
    let scr0 := (((s.scratch.scratch_buf.set (512 / 4) 0).set (516 / 4) 0).set
      (520 / 4) 0).set (524 / 4) 0
    have hlen0_scr : scr0.length = c.scratch_cap := by simp [scr0, hscrl]
    have hout0 : ∀ k < c.scratch_cap, k < 128 ∨ 132 ≤ k →
        scr0[k]? = s.scratch.scratch_buf[k]? := fun k _ hk => by
      simp only [scr0]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    have hdw0 : FullDenseInvW c F0 F_cur
        { s with
          core := { s.core with lit_mark := s.core.lit_mark }
          scratch := { s.scratch with scratch_buf := scr0 } } :=
      FullDenseInvW.with_litMark_scr hdw hlml hlen0_scr hdw.2.2.1
    have hcore_up : { s.core with lit_mark := s.core.lit_mark } = s.core := by cases s.core; rfl
    refine hJ (0#32, PUnit.unit) m ⟨Nat.zero_le _, s.core.lit_mark, scr0, hdw0, hout0, ?_⟩
    rw [hcore_up]; exact hm
  · clear m hm h128_lt h129_lt h130_lt h131_lt hlml
    rintro J ⟨i, ⟨⟩⟩ ml ⟨hi_le, lm', scr', hdw', hout', hm'⟩ ih
    let si : FullState :=
      { s with
        core := { s.core with lit_mark := lm' }
        scratch := { s.scratch with scratch_buf := scr' } }
    have hscrl' : scr'.length = c.scratch_cap := hdw'.1.scratch_ok.scratch_buf_len
    have h128' : 512 / 4 < scr'.length := by omega
    have h129' : 516 / 4 < scr'.length := by omega
    have h130' : 520 / 4 < scr'.length := by omega
    have h131' : 524 / 4 < scr'.length := by omega
    bve_steps!
    { refine wp_loop_inv (ts := [i32])
        (fun (j, _) mj => j.toNat ≤ nn.toNat ∧ mj = ml)
        (fun (j, _) _ => nn.toNat - j.toNat)
        ?_ ?_
      { intro J2 hJ2; bve_steps!; exact hJ2 _ _ ⟨Nat.zero_le _, rfl⟩ }
      { rintro J2 ⟨j, ⟨⟩⟩ mj ⟨hj_le, rfl⟩ ih2
        bve_steps!
        { obtain ⟨scr_f, hm_f, hlen_f, hout_f⟩ :
              ∃ scr_f,
                (FullMem c
                  { s with
                    core := { s.core with lit_mark := lm' }
                    scratch := { s.scratch with scratch_buf := scr_f } } ⋆ R) m ∧
                scr_f.length = c.scratch_cap ∧
                (∀ k < c.scratch_cap, k < 128 ∨ 132 ≤ k → scr_f[k]? = scr'[k]?) :=
            ⟨_, by assumption, by simp [hscrl'], fun k hk1 hk2 => by
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]⟩
          exact hQ lm' scr_f m
            (FullDenseInvW.with_litMark_scr hdw' hdw'.1.core_ok.lit_mark_len hlen_f hdw'.2.2.1)
            (fun k hk1 hk2 => (hout_f k hk1 hk2).trans (hout' k hk1 hk2)) hm_f }
        { exact ih2 _ _ (by bv_omega) ⟨by bv_omega, rfl⟩ }
        { exact ih2 _ _ (by bv_omega) ⟨by bv_omega, rfl⟩ }
        { exact ih _ _ (by bv_omega) ⟨by bv_omega, lm', scr', hdw', hout', hm'⟩ } } }
    { have hi_lt : i.toNat < np.toNat := by bv_omega
      have hi_scr : i.toNat < scr'.length := by rw [hscrl']; bv_omega
      have hwp_eq : scr'[i.toNat]? = s.scratch.scratch_buf[i.toNat]? :=
        hout' i.toNat (by omega) (Or.inl (by omega))
      have hwp_get : scr'[i.toNat]'hi_scr = s.scratch.scratch_buf[i.toNat]?.getD 0#32 :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem hi_scr, hwp_eq,
            List.getElem?_eq_getElem (by omega : i.toNat < s.scratch.scratch_buf.length)]; rfl)
      have hpos_i := hpos i.toNat hi_lt
      have hnot_bin : ¬ (s.scratch.scratch_buf[i.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 :=
        fun hne => hne (by rw [← hwp_get]; exact hc)
      unfold FullBveEntryOkW at hpos_i; rw [ite_eq_right hnot_bin] at hpos_i
      refine wp_call_of_spec _ _ (hMark _ ml _ X ⟨c, F0, F_cur, si, R, rfl, hdw', h132,
        ?_, ?_, ?_, ?_, hm', ?_⟩)
      { c0_let_simp; simp only [bv_c0_zext32_64]
        unfold fullArenaClauseRefs fullArenaClauseRefsCore
        change (scr'[i.toNat]'hi_scr).toNat ∈ _; rw [hwp_get]; exact hpos_i.1 }
      { c0_let_simp; simp only [bv_c0_zext32_64]
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
        change fullArenaClauseGarbCore si.core (scr'[i.toNat]'hi_scr).toNat = false
        rw [hwp_get]; exact hpos_i.2 }
      { c0_let_simp; bv_omega }
      { intro j hj; revert j hj; c0_let_simp; intro j hj
        have hwn := hneg j hj
        have hwn_eq : scr'[64 + j]? = s.scratch.scratch_buf[64 + j]? :=
          hout' (64 + j) (by omega) (Or.inl (by omega))
        try rw [show (64#32 : BitVec 32).toNat = 64 from rfl]
        have hpl_xor : (v <<< 1).toNat ^^^ 1 = 2 * v.toNat + 1 := by
          have hv2 : (v <<< 1).toNat = 2 * v.toNat := by bv_omega
          have hle := litNeg_eq (2 * v.toNat)
          simp only [litNeg, show (2 * v.toNat) % 2 = 0 by omega, ↓reduceIte] at hle
          rw [hv2, hle]
        change FullBveEntryOkW F_cur si ((v <<< 1).toNat ^^^ 1) (scr'[64 + j]?.getD 0#32)
        rw [hpl_xor, hwn_eq]; exact hwn }
      { intro ok lm'' scr'' m'' s'' hdw'' hout'' hm''
        have hscrl'' : scr''.length = c.scratch_cap := hdw''.1.scratch_ok.scratch_buf_len
        have h128'' : 512 / 4 < scr''.length := by omega
        have h129'' : 516 / 4 < scr''.length := by omega
        have hs''_eq : s'' =
            { s with
              core := { s.core with lit_mark := lm'' }
              scratch := { s.scratch with scratch_buf := scr'' } } := by
          simp only [s'', si]
        rw [hs''_eq] at hdw'' hm''
        clear hs''_eq s'' hdw' hm' hwp_eq hwp_get hpos_i hnot_bin hi_scr hi_lt
        bve_steps!
        { obtain ⟨scr_f, hm_f, hlen_f, hout_f⟩ :
              ∃ scr_f,
                (FullMem c
                  { s with
                    core := { s.core with lit_mark := lm'' }
                    scratch := { s.scratch with scratch_buf := scr_f } } ⋆ R) m ∧
                scr_f.length = c.scratch_cap ∧
                (∀ k < c.scratch_cap, k < 128 ∨ 132 ≤ k → scr_f[k]? = scr''[k]?) :=
            ⟨_, hm, by simp [hscrl''], fun k hk1 hk2 => by
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]⟩
          exact hQ lm'' scr_f m
            (FullDenseInvW.with_litMark_scr hdw'' hdw''.1.core_ok.lit_mark_len hlen_f
              hdw''.2.2.1)
            (fun k hk1 hk2 =>
              (hout_f k hk1 hk2).trans
                ((hout'' k hk1 (by omega) (by omega)).trans (hout' k hk1 hk2)))
            hm_f }
        { exact ih _ _ (by bv_omega) ⟨by bv_omega, lm'', scr'', hdw'', fun k hk1 hk2 =>
            (hout'' k hk1 (by omega) (by omega)).trans (hout' k hk1 hk2), hm''⟩ } } }
    { refine wp_loop_inv (ts := [i32])
        (fun (j, _) mj =>
          j.toNat ≤ nn.toNat ∧
          ∃ (lm'' : List (BitVec 8)) (scr'' : List (BitVec 32)),
            let sj : FullState :=
              { s with
                core := { s.core with lit_mark := lm'' }
                scratch := { s.scratch with scratch_buf := scr'' } }
            FullDenseInvW c F0 F_cur sj ∧
            (∀ k < c.scratch_cap, k < 128 ∨ 132 ≤ k → scr''[k]? = s.scratch.scratch_buf[k]?) ∧
            (FullMem c sj ⋆ R) mj)
        (fun (j, _) _ => nn.toNat - j.toNat)
        ?_ ?_
      { intro J2 hJ2; bve_steps!
        exact hJ2 (0#32, PUnit.unit) ml ⟨Nat.zero_le _, lm', scr', hdw', hout', hm'⟩ }
      { clear h128' h129' h130' h131' hscrl' si lm' scr' hdw' hout' hm' ih
        rintro J2 ⟨j, ⟨⟩⟩ mj ⟨hj_le, lmj, scrj, hdwj, houtj, hm_j⟩ ih2
        let sj : FullState :=
          { s with
            core := { s.core with lit_mark := lmj }
            scratch := { s.scratch with scratch_buf := scrj } }
        have hscrlj : scrj.length = c.scratch_cap := hdwj.1.scratch_ok.scratch_buf_len
        bve_steps!
        { have hj_lt : j.toNat < nn.toNat := by bv_omega
          have hj_scr : (64#32 + j).toNat < scrj.length := by rw [hscrlj]; bv_omega
          have hj_nat : (64#32 + j).toNat = 64 + j.toNat := by bv_omega
          have hwn_eq : scrj[(64#32 + j).toNat]? = s.scratch.scratch_buf[64 + j.toNat]? := by
            rw [hj_nat]; exact houtj (64 + j.toNat) (by omega) (Or.inl (by omega))
          have hwn_get : scrj[(64#32 + j).toNat]'hj_scr =
              s.scratch.scratch_buf[64 + j.toNat]?.getD 0#32 := Option.some.inj (by
            rw [← List.getElem?_eq_getElem hj_scr, hwn_eq,
              List.getElem?_eq_getElem (by omega : 64 + j.toNat < s.scratch.scratch_buf.length)]
            rfl)
          have hneg_j := hneg j.toNat hj_lt
          have hnot_bin : ¬ (s.scratch.scratch_buf[64 + j.toNat]?.getD 0#32 &&&
              0x80000000#32) ≠ 0#32 := by
            have hhc : scrj[(64#32 + j).toNat]'hj_scr &&& 0x80000000#32 = 0#32 := by
              have hmod : (BitVec.toNat (64 : BitVec 32) + j.toNat) % 2 ^ 32 =
                  (64#32 + j).toNat := by bv_omega
              simp only [hmod] at hc; exact hc
            rw [hwn_get] at hhc; exact fun hne => hne hhc
          unfold FullBveEntryOkW at hneg_j; rw [ite_eq_right hnot_bin] at hneg_j
          refine wp_call_of_spec _ _ (hMark _ mj _ X ⟨c, F0, F_cur, sj, R, rfl, hdwj, h132,
            ?_, ?_, ?_, ?_, hm_j, ?_⟩)
          { c0_let_simp
            simp only [bv_c0_zext32_64, show (64 : BitVec 32) + j = 64#32 + j from rfl]
            unfold fullArenaClauseRefs fullArenaClauseRefsCore
            change (scrj[(64#32 + j).toNat]'hj_scr).toNat ∈ _; rw [hwn_get]; exact hneg_j.1 }
          { c0_let_simp
            simp only [bv_c0_zext32_64, show (64 : BitVec 32) + j = 64#32 + j from rfl]
            unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
            change fullArenaClauseGarbCore sj.core
              (scrj[(64#32 + j).toNat]'hj_scr).toNat = false
            rw [hwn_get]; exact hneg_j.2 }
          { c0_let_simp; bv_omega }
          { intro i' hi'; revert i' hi'; c0_let_simp; intro i' hi'
            have hwp' := hpos i' hi'
            have hwp_eq' : scrj[i']? = s.scratch.scratch_buf[i']? :=
              houtj i' (by omega) (Or.inl (by omega))
            try rw [show (0#32 : BitVec 32).toNat = 0 from rfl]
            simp only [Nat.zero_add]
            have hnl_xor : ((v <<< 1) ^^^ 1#32).toNat ^^^ 1 = 2 * v.toNat := by
              have hv2 : (v <<< 1).toNat = 2 * v.toNat := by bv_omega
              have hnl : ((v <<< 1) ^^^ 1#32).toNat = 2 * v.toNat + 1 := by
                have hle := litNeg_eq (2 * v.toNat)
                simp only [litNeg, show (2 * v.toNat) % 2 = 0 by omega, ↓reduceIte] at hle
                change (v <<< 1).toNat ^^^ 1 = _; rw [hv2, hle]
              have hle := litNeg_eq (2 * v.toNat + 1)
              simp only [litNeg, show (2 * v.toNat + 1) % 2 ≠ 0 by omega, ↓reduceIte] at hle
              rw [hnl, hle]; omega
            change FullBveEntryOkW F_cur sj (((v <<< 1) ^^^ 1#32).toNat ^^^ 1)
              (scrj[i']?.getD 0#32)
            rw [hnl_xor, hwp_eq']; exact hwp' }
          { intro ok lm'' scr'' m'' s'' hdw'' hout'' hm''
            have hscrl'' : scr''.length = c.scratch_cap := hdw''.1.scratch_ok.scratch_buf_len
            have h128'' : 512 / 4 < scr''.length := by omega
            have h129'' : 516 / 4 < scr''.length := by omega
            have h130'' : 520 / 4 < scr''.length := by omega
            have h131'' : 524 / 4 < scr''.length := by omega
            have hs''_eq : s'' =
                { s with
                  core := { s.core with lit_mark := lm'' }
                  scratch := { s.scratch with scratch_buf := scr'' } } := by
              simp only [s'', sj]
            rw [hs''_eq] at hdw'' hm''
            clear hs''_eq s'' hdwj hm_j hpos hneg hwn_eq hwn_get hneg_j
            clear hnot_bin hj_lt hj_scr hj_nat
            bve_steps!
            { obtain ⟨scr_f, hm_f, hlen_f, hout_f⟩ :
                  ∃ scr_f,
                    (FullMem c
                      { s with
                        core := { s.core with lit_mark := lm'' }
                        scratch := { s.scratch with scratch_buf := scr_f } } ⋆ R) m ∧
                    scr_f.length = c.scratch_cap ∧
                    (∀ k < c.scratch_cap, k < 128 ∨ 132 ≤ k → scr_f[k]? = scr''[k]?) :=
                ⟨_, hm, by simp [hscrl''], fun k hk1 hk2 => by
                  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                    List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                    List.getElem?_set_ne (by omega)]⟩
              exact hQ lm'' scr_f m
                (FullDenseInvW.with_litMark_scr hdw'' hdw''.1.core_ok.lit_mark_len hlen_f
                  hdw''.2.2.1)
                (fun k hk1 hk2 =>
                  (hout_f k hk1 hk2).trans
                    ((hout'' k hk1 (by omega) (by omega)).trans (houtj k hk1 hk2)))
                hm_f }
            { exact ih2 _ _ (by bv_omega) ⟨by bv_omega, lm'', scr'', hdw'', fun k hk1 hk2 =>
                (hout'' k hk1 (by omega) (by omega)).trans (houtj k hk1 hk2), hm''⟩ } } }
        { exact ih2 _ _ (by bv_omega) ⟨by bv_omega, lmj, scrj, hdwj, houtj, hm_j⟩ }
        { exact hQ lmj scrj mj hdwj houtj hm_j } } }

end LeanQbe.T.Examples.Kissat.Full
