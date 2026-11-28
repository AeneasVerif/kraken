/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.ControlComb
public import Kraken.Mem
public import Kraken.Separation

/-!
# Shared Framing, BitVec, CNF & `FullDenseInvW` Helpers (`Proof.Eliminate.Helpers`)

Self-contained shared lemmas (`0` legacy `Full*` imports, `0` `@[expose]` on theorems/sections,
`<= 100` cols) supporting all `16` `Proof.Eliminate.Wp*` proofs.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Eliminate

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. Scoped Pointer-Offset Rules & Tactic Macros (`EliminateTactics`) -/

namespace EliminateTactics

open FullArenaTactics
open scoped FullArenaTactics

private theorem m4_off (a : BitVec 64) (off : Nat) (i : BitVec 64) :
    (a + BitVec.ofNat 64 (4 * off)) + i * 4 = a + BitVec.ofNat 64 (4 * (off + i.toNat)) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat, ptr_add_ofNat,
    ← Nat.mul_add]

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

scoped macro "elim_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

scoped macro "elim_steps" : tactic =>
  `(tactic| ((try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _); c0_hsteps))

scoped macro "elim_steps_nogrp" : tactic =>
  `(tactic| ((try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _); c0_hsteps_nogrp))

scoped macro "elim_steps!" : tactic =>
  `(tactic| ((try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _); c0_hsteps!))

end EliminateTactics

/-! ## 2. Basic List, `BitVec`, & `TmkZero` Helpers -/

theorem elim_getElem_congr {α : Type} {xs : List α} {i j : Nat} (h : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem elim_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem elim_bv32_ofNat_toNat {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem elim_bv64_setWidth32_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (BitVec.setWidth 32 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

theorem elim_nat_xor1_lt_two_mul {l n : Nat} (hl : l < 2 * n) : l ^^^ 1 < 2 * n := by
  have hdiv : (l ^^^ 1) / 2 = l / 2 := fullInv_var_xor1 l
  omega

theorem elim_xor1_mod2 (a : Nat) : (a ^^^ 1) % 2 = 1 - a % 2 := by
  have htb : (a ^^^ 1).testBit 0 = !(a.testBit 0) := by
    rw [Nat.testBit_xor]; cases a.testBit 0 <;> decide
  have h1 : ∀ n : Nat, n.testBit 0 = decide (n % 2 = 1) := fun n => Nat.testBit_zero n
  rw [h1, h1] at htb
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one (a ^^^ 1) with hb | hb <;> simp_all

theorem elim_bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := rfl

theorem elim_bv32_and_litMask_toNat (w : BitVec 32) :
    (w &&& 0x7FFFFFFF#32).toNat = w.toNat % 2 ^ 31 := by
  simpa [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl] using
    Nat.and_two_pow_sub_one_eq_mod w.toNat 31

theorem elim_bv32_and_msb_zero_of_lt {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
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

theorem elim_bv32_ne_sent_of_lt {x : BitVec 32} (hlt : x.toNat < 2 ^ 31) :
    x ≠ 0xFFFFFFFF#32 := fun h => by
  have := congrArg BitVec.toNat h; simp at this; omega

theorem elim_bv32_bit19_or_garb_ne0 (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro h; have := congrArg (·[19]) h; simp at this

theorem elim_bv32_bit23_or_garb (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
  have h23 : (0x00800000#32)[i] = true → (0x00080000#32)[i] = false := by
    revert i hi; decide
  cases h : (0x00800000#32)[i]
  · simp
  · simp [h23 h]

theorem elim_bv32_bit23_or_sub (x : BitVec 32) :
    ((x ||| 0x01000000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
  have h23 : (0x00800000#32)[i] = true → (0x01000000#32)[i] = false := by
    revert i hi; decide
  cases h : (0x00800000#32)[i]
  · simp
  · simp [h23 h]

theorem elim_bv32_bit19_or_sub (x : BitVec 32) :
    ((x ||| 0x01000000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
  have h19 : (0x00080000#32)[i] = true → (0x01000000#32)[i] = false := by
    revert i hi; decide
  cases h : (0x00080000#32)[i]
  · simp
  · simp [h19 h]

theorem elim_pl_nl_eq (v : BitVec 32) (hv : v.toNat < 2 * 2 ^ 28) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
    ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have h1 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have h2 : ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := by
    rw [BitVec.toNat_or, h1, BitVec.toNat_ofNat]
    have h1m : 1 % 2 ^ 32 = 1 := rfl
    rw [h1m]
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero =>
      rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero, Nat.mul_mod_right]
      simp [show (2 * v.toNat + 1) % 2 = 1 by omega]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      simp [Nat.mul_add_div (by omega : 0 < 2)]
  exact ⟨h1, h2⟩

theorem elim_bv8_dom_pos_slt {v : BitVec 8} (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : (BitVec.ofNat 32 0).slt (v.signExtend 32) = true) : v = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

theorem elim_bv8_dom_neg_slt {v : BitVec 8} (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : (v.signExtend 32).slt (BitVec.ofNat 32 0) = true) : v = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

theorem elim_bv8_dom_neg_of_not_pos_ne0 {v : BitVec 8}
    (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h1 : (BitVec.ofNat 32 0).slt (v.signExtend 32) = false)
    (h2 : v.signExtend 32 ≠ 0#32) : v = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl
  · exact absurd rfl h2
  · simp at h1
  · rfl

theorem elim_bv8_dom_zero_of_not_pos_neg {v : BitVec 8}
    (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h1 : (BitVec.ofNat 32 0).slt (v.signExtend 32) = false)
    (h2 : (v.signExtend 32).slt (BitVec.ofNat 32 0) = false) : v = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

theorem tmkZero_congr {s s' : FullState} (h : TmkZero s)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (htmk : s'.scratch.tarjan_mark = s.scratch.tarjan_mark) : TmkZero s' := fun v hv => by
  rw [htmk]; exact h v (hcv ▸ hv)

theorem tmkZero_of_init {s : FullState} {tmki : List (BitVec 32)}
    (hinit : ∀ k < s.core.cur_vars, tmki[k]?.getD 0#32 = 0#32) :
    TmkZero { s with scratch := { s.scratch with tarjan_mark := tmki } } :=
  fun v hv => hinit v hv

/-! ## 3. CNF Entailment, `vals` & Refutation Helpers -/

theorem elim_vals_pos_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {l : Nat} (hl : l < 2 * k.cur_vars) (h1 : k.vals[l]?.getD 0#8 = 1#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l]) := by
  obtain ⟨idx, hidx, htrl⟩ := (hw.vals_true_iff l hl).mp h1
  have hv0 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le idx hidx; omega
  have hs := hw.level0_sound idx hidx hv0
  rwa [htrl] at hs

theorem elim_vals_neg_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {l : Nat} (hl : l < 2 * k.cur_vars) (hff : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  obtain ⟨idx, hidx, htrl⟩ := (hw.vals_false_iff l hl).mp hff
  have hv0 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le idx hidx; omega
  have hs := hw.level0_sound idx hidx hv0
  rwa [htrl] at hs

theorem elim_unsat_of_lit_and_neg {F : CNF Nat} {a : Nat}
    (h1 : F.EntailsClause (cnfClause [a]))
    (h2 : F.EntailsClause (cnfClause [a ^^^ 1])) : F.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have s1 := (CNF.entails_clause_def.mp h1) α hα
  have s2 := (CNF.entails_clause_def.mp h2) α hα
  rw [clause_sat_cnfClause_iff] at s1 s2
  obtain ⟨l1, hl1, hs1⟩ := s1; obtain ⟨l2, hl2, hs2⟩ := s2
  rw [List.mem_singleton] at hl1 hl2; rw [hl1] at hs1; rw [hl2] at hs2
  simp only [litVar, litSign] at hs1 hs2
  rw [fullInv_var_xor1 a, elim_xor1_mod2 a] at hs2
  cases h : α (a / 2) <;> simp [h] at hs1 hs2 <;> omega

theorem elim_clause_all_false_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {cl : List Nat} (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause cl))
    (hlt : ∀ l ∈ cl, l < 2 * k.cur_vars)
    (hfalse : ∀ l ∈ cl, k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have hs := (CNF.entails_clause_def.mp hent) α hα
  rw [clause_sat_cnfClause_iff] at hs
  obtain ⟨l, hl, hsl⟩ := hs
  have hneg := elim_vals_neg_entails hw hl0 (hlt l hl) (hfalse l hl)
  have hsn := (CNF.entails_clause_def.mp hneg) α hα
  rw [clause_sat_cnfClause_iff] at hsn
  obtain ⟨l', hl', hsl'⟩ := hsn
  rw [List.mem_singleton] at hl'; rw [hl'] at hsl'
  simp only [litVar, litSign] at hsl hsl'
  rw [fullInv_var_xor1 l, elim_xor1_mod2 l] at hsl'
  cases h : α (l / 2) <;> simp [h] at hsl hsl' <;> omega

theorem elim_clause_one_unass_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {cl : List Nat} {u : Nat} (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause cl))
    (hlt : ∀ l ∈ cl, l < 2 * k.cur_vars)
    (hoth : ∀ l ∈ cl, l ≠ u → k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [u]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have hs := (CNF.entails_clause_def.mp hent) α hα
  rw [clause_sat_cnfClause_iff] at hs ⊢
  obtain ⟨l, hl, hsl⟩ := hs
  by_cases hlu : l = u
  · subst hlu; exact ⟨l, List.mem_singleton_self _, hsl⟩
  · exfalso
    have hneg := elim_vals_neg_entails hw hl0 (hlt l hl) (hoth l hl hlu)
    have hsn := (CNF.entails_clause_def.mp hneg) α hα
    rw [clause_sat_cnfClause_iff] at hsn
    obtain ⟨l', hl', hsl'⟩ := hsn
    rw [List.mem_singleton] at hl'; rw [hl'] at hsl'
    simp only [litVar, litSign] at hsl hsl'
    rw [fullInv_var_xor1 l, elim_xor1_mod2 l] at hsl'
    cases h : α (l / 2) <;> simp [h] at hsl hsl' <;> omega

/-! ## 4. `FullDenseInvW` / `FullDenseInv` / `WatchStackLayout` Updaters -/

theorem denseWatchesInv_of_w {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) : DenseWatchesInv F_cur s.core := by
  have hm := h.2.1.watches
  unfold ModeWatchesInv at hm
  simp only [h.2.2.2.2.2.2, ↓reduceIte] at hm
  exact hm

theorem watchLayout_of_denseInv {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) : WatchStackLayout s.core :=
  let ⟨_, hdw⟩ := h.exists_witness
  (denseWatchesInv_of_w hdw).layout

theorem fullDenseInvW_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (v : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with oom := v } } := by
  let hw := h.2.1
  exact ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_inconsistent {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (v : BitVec 64)
    (hinc : v ≠ 0#64 → (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := v } } := by
  let hw := h.2.1
  exact ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
    { hw with inconsistent_sound := hinc
              arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_scratch_buf {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {scr' : List (BitVec 32)}
    (hlen : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := scr' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with scratch_buf_len := hlen }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_bve_cnt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (v : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with bve_cnt := v } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with scratch_buf_len := h.1.scratch_ok.scratch_buf_len }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_res_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (v : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with res_sz := v } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with scratch_buf_len := h.1.scratch_ok.scratch_buf_len }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_wsort {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {ws' : List (BitVec 32)}
    (hlen : ws'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with wsort := ws' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with wsort_len := hlen }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_flags_unassigned {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {fl' : List (BitVec 32)}
    (hfl : fl'.length = c.max_vars) (un' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with flags := fl', unassigned := un' } } := by
  let hw := h.2.1
  exact ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_lit_mark {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {lm' : List (BitVec 8)}
    (hlm_len : lm'.length = 2 * c.max_vars)
    (hlm_clr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with lit_mark := lm' } } :=
  ⟨⟨{ h.1.core_ok with lit_mark_len := hlm_len }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   ⟨h.2.2.1.1, hlm_clr⟩, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_of_safetySlice {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullDenseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullDenseInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨hlen', heq ▸ h.2.1, ?_, ?_, ?_, heq ▸ h.2.2.2.2.2.1, heq ▸ h.2.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact h.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact h.2.2.2.1
  · exact FullExtScratchOk.of_pres h.2.2.2.2.1 hpres fun r hr => by
      unfold fullArenaClauseRefs; rwa [heq]

theorem fullDenseInvW_of_markGarb_zero {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' := by
  intro s'
  have hlen' : s'.LengthsOk c :=
    ⟨{ h.1.core_ok with arena_len_arr := by simp [s', h.1.core_ok.arena_len_arr] },
     h.1.scratch_ok⟩
  have hmg := h.2.1.arena.markGarb h.1.core_ok href ag'
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hmg.1
  have hl0 : s.core.cur_level = 0 := h.2.2.2.2.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { h.2.1 with
      arena := hmg.2
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
      reason_inv := fun idx hi hne =>
        absurd (h.2.1.level0_rsn_none idx hi (by have := h.2.1.lvl_le idx hi; omega)) hne
      reason_lit_mem := fun idx hi hne _ =>
        absurd (h.2.1.level0_rsn_none idx hi (by have := h.2.1.lvl_le idx hi; omega)) hne }
  exact ⟨hlen', hw', h.2.2.1, FullArenaVarsNodup.of_markGarb ⟨h.1, F_cur, h.2.1⟩ h.2.2.2.1 href ag',
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rwa [hrefs]),
    hl0, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_of_deleteBinary {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fl' wvec' wstk' : List (BitVec 32)} {wu' nb' : BitVec 64}
    (hlen' : ({ s with core := { s.core with flags := fl', wvec := wvec', wstk := wstk',
                                             wusable := wu', num_binary := nb' } } :
      FullState).LengthsOk c)
    (hwat : ModeWatchesInv F_cur
      { s.core with flags := fl', wvec := wvec', wstk := wstk',
                    wusable := wu', num_binary := nb' }) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with flags := fl', wvec := wvec', wstk := wstk',
                                     wusable := wu', num_binary := nb' } } := by
  let hw := h.2.1
  refine ⟨hlen', { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat },
    h.2.2.1, ?_, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
      fullArenaClauseRefsCore fullArenaClauseGarbCore fullArenaClauseLitsCore fullArenaHdrCore
      fullArenaClauseSizeCore
    exact h.2.2.2.1
  · unfold FullExtScratchOk FullLastLearnedWf fullArenaClauseRefs fullArenaClauseRefsCore
    exact h.2.2.2.2.1

theorem fullDenseInvW_of_addUnit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' unfl' inc' : BitVec 64} {sc' : FullScratch}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            propagated := prop', cur_level := cl', unassigned := unass',
                            unflushed := unfl', inconsistent := inc' }
      scratch := sc' } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    propagated := prop', cur_level := cl', unassigned := unass',
                    unflushed := unfl', inconsistent := inc' })
    (hpres : FullExtScratchPres s
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', cur_level := cl', unassigned := unass',
                              unflushed := unfl', inconsistent := inc' }
        scratch := sc' })
    (hcl0 : cl' = 0) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', cur_level := cl', unassigned := unass',
                              unflushed := unfl', inconsistent := inc' }
        scratch := sc' } := by
  refine ⟨hlen', hw', h.2.2.1, ?_, ?_, hcl0, h.2.2.2.2.2.2⟩
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
      fullArenaClauseRefsCore fullArenaClauseGarbCore fullArenaClauseLitsCore fullArenaHdrCore
      fullArenaClauseSizeCore
    exact h.2.2.2.1
  · exact FullExtScratchOk.of_pres h.2.2.2.2.1 hpres fun r hr => by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; exact hr

theorem fullDenseInvW_of_addBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' : Nat} {unass' unfl' : BitVec 64} {wvec' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' nb' oom' inc' : BitVec 64} {phases' : List (BitVec 8)}
    {wsort' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                            oom := oom', inconsistent := inc' }
      scratch := { s.scratch with phases := phases', wsort := wsort' } } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    unassigned := unass', unflushed := unfl', wvec := wvec',
                    wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                    oom := oom', inconsistent := inc' }) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                              oom := oom', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', wsort := wsort' } } := by
  refine ⟨hlen', hw', h.2.2.1, ?_, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
      fullArenaClauseRefsCore fullArenaClauseGarbCore fullArenaClauseLitsCore fullArenaHdrCore
      fullArenaClauseSizeCore
    exact h.2.2.2.1
  · exact FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ fun r hr => by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; exact hr

theorem fullDenseInvW_addEntailedClause {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {len : Nat}
    {arena' fl' wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wusable' ni' : BitVec 64}
    (hlen' : ({ s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            flags := fl', wvec := wvec', wstk := wstk', wlen := wlen',
                            wusable := wusable', num_irred := ni' } } :
      FullState).LengthsOk c)
    (hge3 : 3 ≤ len)
    (hlits_lt : ∀ l ∈ fullArenaClauseLitsCore
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len } s.core.arena_len,
      l < 2 * s.core.cur_vars)
    (hnodup : ((fullArenaClauseLitsCore
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len }
        s.core.arena_len).map (· / 2)).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause (fullArenaClauseLitsCore
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len } s.core.arena_len)))
    (hhold_arena : ∀ k < s.core.arena_len, arena'[k]? = s.core.arena[k]?)
    (hnew_noshrk : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnew_sz : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len)
    (hwat : ModeWatchesInv F_cur
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                    flags := fl', wvec := wvec', wstk := wstk', wlen := wlen',
                    wusable := wusable', num_irred := ni' }) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                              flags := fl', wvec := wvec', wstk := wstk', wlen := wlen',
                              wusable := wusable', num_irred := ni' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            flags := fl', wvec := wvec', wstk := wstk', wlen := wlen',
                            wusable := wusable', num_irred := ni' } }
  let hw := h.2.1
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + len)
    (by omega) hhold_arena
  have hrefs :
      fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hge3 rfl hhold_arena hnew_noshrk hnew_sz
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hhold_arena r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseSizeCore s'; simp [hhold_arena (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have h1l := h.1.core_ok.arena_len_arr; have h1e := h.1.core_ok.arena_len_le
    have h2l : arena'.length = c.arena_cap := hlen'.core_ok.arena_len_arr
    have h2e : s.core.arena_len + 3 + len ≤ c.arena_cap := hlen'.core_ok.arena_len_le
    have hbd_ar : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena_len := by omega
    exact fullArenaClauseLitsCore_eq_of_hold (by omega) (by dsimp only [s']; omega)
      (hold_sz r hr) fun j hj => hhold_arena (r + 3 + j) (by omega)
  have hnew_lits_eq : fullArenaClauseLitsCore s'.core s.core.arena_len =
      fullArenaClauseLitsCore
        { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len }
        s.core.arena_len := rfl
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr
        rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : fullArenaNextOff s'.core.arena s'.core.arena_len s.core.arena_len =
            s.core.arena_len + 3 + len := by unfold fullArenaNextOff s'; simp [hnew_sz, hnew_noshrk]
        rw [hnxt_new, show fullArenaClauseSizeCore s'.core s.core.arena_len = len from hnew_sz]
        refine ⟨by dsimp [s']; omega, hge3, by omega, by dsimp [s']; omega, Or.inl (by dsimp [s'])⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hw.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh
          rwa [hhold_arena r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [s']; omega,
          by dsimp only [s']; rw [hhold_arena t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [s'] at hsh; exact absurd hnew_noshrk hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.lits_lt r hr hng
      · rw [hnew_lits_eq]; exact hlits_lt
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.entails r hr hng
      · rw [hnew_lits_eq]; exact hent
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hng
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · change fullArenaClauseGarbCore s'.core r = false at hng
      rw [hold_garb r hr] at hng
      unfold fullArenaClauseLits; rw [hold_lits r hr]; exact h.2.2.2.1 r hr hng
    · change ((fullArenaClauseLitsCore s'.core s.core.arena_len).map (· / 2)).Nodup
      rw [hnew_lits_eq]; exact hnodup
  have hl0 : s.core.cur_level = 0 := h.2.2.2.2.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena', watches := hwat
      reason_inv := fun idx hi hne =>
        absurd (hw.level0_rsn_none idx hi (by have := hw.lvl_le idx hi; omega)) hne
      reason_lit_mem := fun idx hi hne _ =>
        absurd (hw.level0_rsn_none idx hi (by have := hw.lvl_le idx hi; omega)) hne }
  exact ⟨hlen', hw', h.2.2.1, hnd',
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact List.mem_append_left _ hr),
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_addGarbageClause {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {len : Nat}
    {arena' fl' wvec' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wusable' ag' oom' : BitVec 64}
    (hlen' : ({ s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            flags := fl', wvec := wvec', wstk := wstk', wlen := wlen',
                            wusable := wusable', arena_garbage := ag', oom := oom' } } :
      FullState).LengthsOk c)
    (hge3 : 3 ≤ len)
    (hhold_arena : ∀ k < s.core.arena_len, arena'[k]? = s.core.arena[k]?)
    (hnew_noshrk : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnew_garb : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32)
    (hnew_sz : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len)
    (hwat : ModeWatchesInv F_cur
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                    flags := fl', wvec := wvec', wstk := wstk', wlen := wlen',
                    wusable := wusable', arena_garbage := ag', oom := oom' }) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                              flags := fl', wvec := wvec', wstk := wstk', wlen := wlen',
                              wusable := wusable', arena_garbage := ag', oom := oom' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            flags := fl', wvec := wvec', wstk := wstk', wlen := wlen',
                            wusable := wusable', arena_garbage := ag', oom := oom' } }
  let hw := h.2.1
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + len)
    (by omega) hhold_arena
  have hrefs :
      fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hge3 rfl hhold_arena hnew_noshrk hnew_sz
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hhold_arena r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseSizeCore s'; simp [hhold_arena (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have h1l := h.1.core_ok.arena_len_arr; have h1e := h.1.core_ok.arena_len_le
    have h2l : arena'.length = c.arena_cap := hlen'.core_ok.arena_len_arr
    have h2e : s.core.arena_len + 3 + len ≤ c.arena_cap := hlen'.core_ok.arena_len_le
    have hbd_ar : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena_len := by omega
    exact fullArenaClauseLitsCore_eq_of_hold (by omega) (by dsimp only [s']; omega)
      (hold_sz r hr) fun j hj => hhold_arena (r + 3 + j) (by omega)
  have hnew_garb_s' : fullArenaClauseGarbCore s'.core s.core.arena_len = true := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hnew_garb]
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr
        rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : fullArenaNextOff s'.core.arena s'.core.arena_len s.core.arena_len =
            s.core.arena_len + 3 + len := by unfold fullArenaNextOff s'; simp [hnew_sz, hnew_noshrk]
        rw [hnxt_new, show fullArenaClauseSizeCore s'.core s.core.arena_len = len from hnew_sz]
        refine ⟨by dsimp [s']; omega, hge3, by omega, by dsimp [s']; omega, Or.inl (by dsimp [s'])⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hw.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh
          rwa [hhold_arena r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [s']; omega,
          by dsimp only [s']; rw [hhold_arena t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [s'] at hsh; exact absurd hnew_noshrk hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.lits_lt r hr hng
      · rw [hnew_garb_s'] at hng; cases hng
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.entails r hr hng
      · rw [hnew_garb_s'] at hng; cases hng
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hng
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · change fullArenaClauseGarbCore s'.core r = false at hng
      rw [hold_garb r hr] at hng
      unfold fullArenaClauseLits; rw [hold_lits r hr]; exact h.2.2.2.1 r hr hng
    · change fullArenaClauseGarbCore s'.core s.core.arena_len = false at hng
      rw [hnew_garb_s'] at hng; cases hng
  have hl0 : s.core.cur_level = 0 := h.2.2.2.2.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena', watches := hwat
      reason_inv := fun idx hi hne =>
        absurd (hw.level0_rsn_none idx hi (by have := hw.lvl_le idx hi; omega)) hne
      reason_lit_mem := fun idx hi hne _ =>
        absurd (hw.level0_rsn_none idx hi (by have := hw.lvl_le idx hi; omega)) hne }
  exact ⟨hlen', hw', h.2.2.1, hnd',
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact List.mem_append_left _ hr),
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInv_with_oom {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) (v : BitVec 64) :
    FullDenseInv c F0 { s with core := { s.core with oom := v } } :=
  let ⟨_, hdw⟩ := h.exists_witness
  (fullDenseInvW_with_oom hdw v).toDense

theorem fullDenseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hel : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInv c F0 { s with scratch := sc' } := by
  obtain ⟨F_cur, hdw⟩ := h.exists_witness
  have hdw' : FullDenseInvW c F0 F_cur { s with scratch := sc' } :=
    ⟨⟨hdw.1.core_ok, hok⟩, hdw.2.1, hdw.2.2.1, hdw.2.2.2.1,
      FullExtScratchOk.of_pres hdw.2.2.2.2.1 ⟨hll, hel⟩ (fun _ hr => hr),
      hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩
  exact hdw'.toDense

theorem fullDenseInv_with_ws1_ss {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {ws1' : List (BitVec 32)} {ss' : List (BitVec 64)}
    (hws1 : ws1'.length = 2 * c.max_vars) (hss : ss'.length = c.max_vars) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } :=
  fullDenseInv_with_scratch_keep h
    { h.lengths.scratch_ok with work_stk1_len := hws1, sim_sig_len := hss } rfl rfl

theorem fullDenseInv_with_min_clr_ws2 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {mclr' ws2' : List (BitVec 32)}
    (hmc : mclr'.length = c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    FullDenseInv c F0
      { s with
        core := { s.core with min_clr := mclr' }
        scratch := { s.scratch with work_stk2 := ws2' } } := by
  obtain ⟨F_cur, hdw⟩ := h.exists_witness
  let hw := hdw.2.1
  have hdw' : FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with min_clr := mclr' }
        scratch := { s.scratch with work_stk2 := ws2' } } :=
    ⟨⟨{ hdw.1.core_ok with min_clr_len_arr := hmc },
      { hdw.1.scratch_ok with work_stk2_len := hws2 }⟩,
     { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
               watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
     hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2.1, hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩
  exact hdw'.toDense

theorem fullDenseInv_with_min_clr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {mclr' : List (BitVec 32)} (hmc : mclr'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with min_clr := mclr' } } := by
  obtain ⟨F_cur, hdw⟩ := h.exists_witness
  let hw := hdw.2.1
  have hdw' : FullDenseInvW c F0 F_cur { s with core := { s.core with min_clr := mclr' } } :=
    ⟨⟨{ hdw.1.core_ok with min_clr_len_arr := hmc }, hdw.1.scratch_ok⟩,
     { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
               watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
     hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2.1, hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩
  exact hdw'.toDense

theorem fullDenseInv_with_flags {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl' } } := by
  obtain ⟨F_cur, hdw⟩ := h.exists_witness
  exact (fullDenseInvW_set_flags hdw hfl).toDense

theorem fullDenseInv_with_flags_fuel {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars)
    (fu' : BitVec 64) :
    FullDenseInv c F0 { s with core := { s.core with flags := fl', fuel := fu' } } := by
  obtain ⟨F_cur, hdw⟩ := h.exists_witness
  let hw := hdw.2.1
  have h2 : FullDenseInvW c F0 F_cur
      { s with core := { s.core with flags := fl', fuel := fu' } } :=
    ⟨⟨{ hdw.1.core_ok with flags_len := hfl }, hdw.1.scratch_ok⟩,
     { hw with
       arena := { hw.arena with len_ok := hw.arena.len_ok }
       watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
     hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2.1, hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩
  exact h2.toDense

theorem fullDenseInv_with_inconsistent {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) (v : BitVec 64)
    (hinc : ∀ F_cur, FullWitnessInv c F0 F_cur s.core → v ≠ 0#64 → (cnfOfClauses F_cur).Unsat) :
    FullDenseInv c F0 { s with core := { s.core with inconsistent := v } } := by
  obtain ⟨F_cur, hdw⟩ := h.exists_witness
  exact (fullDenseInvW_with_inconsistent hdw v (hinc F_cur hdw.2.1)).toDense

/-! ## 5. `FullBveEntryOkW` & `FullResBufOkW` Framing Helpers -/

theorem bveEntry_to_weak {F_cur : List (List Nat)} {s : FullState} {lit : Nat}
    {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w) : FullBveWeakItemOk s.core w := by
  unfold FullBveEntryOkW at h; unfold FullBveWeakItemOk
  split at h <;> simp_all

theorem bveEntry_to_extNeed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {lit : Nat} {w : BitVec 32}
    (h : FullBveEntryOkW F_cur s lit w) :
    (w &&& 0x80000000#32) ≠ 0#32 ∨ w.toNat + 2 < c.arena_cap := by
  unfold FullBveEntryOkW at h
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · exact Or.inl hb
  · right; rw [ite_eq_right hb] at h
    have hwf := hdw.2.1.arena.refs_wf w.toNat h.1
    have hal := hdw.1.core_ok.arena_len_le; omega

theorem bveEntry_congr_core {F_cur : List (List Nat)} {s s' : FullState}
    {lit : Nat} {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w)
    (hcv : s'.core.cur_vars = s.core.cur_vars) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) :
    FullBveEntryOkW F_cur s' lit w := by
  unfold FullBveEntryOkW at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact ⟨by rw [hcv]; exact h.1, h.2⟩
  · rw [ite_eq_right hb] at h ⊢
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    have hgb : fullArenaClauseGarb s' w.toNat = fullArenaClauseGarb s w.toNat := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
    rw [hrefs, hgb]; exact h

theorem bveEntry_with_state {F_cur : List (List Nat)} {s s' : FullState} {lit : Nat}
    {w : BitVec 32} (hvars : s.core.cur_vars ≤ s'.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (h : FullBveEntryOkW F_cur s lit w) : FullBveEntryOkW F_cur s' lit w := by
  unfold FullBveEntryOkW at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at h ⊢; exact ⟨by omega, h.2⟩
  · simp only [hb, ↓reduceIte] at h ⊢
    unfold fullArenaClauseRefs fullArenaClauseRefsCore fullArenaClauseGarb
      fullArenaClauseGarbCore fullArenaHdrCore at h ⊢
    rw [har, hal]; exact h

theorem resBuf_with_state {F_cur : List (List Nat)} {s s' : FullState}
    {r_off r_end : Nat} (hvars : s'.core.cur_vars = s.core.cur_vars)
    (hbuf : ∀ idx, r_off ≤ idx → idx < r_end →
      s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (h : FullResBufOkW F_cur s r_end r_off) : FullResBufOkW F_cur s' r_end r_off := by
  induction h with
  | nil => exact .nil
  | @cons p sz hbd hsz hlts hnd hent _ ih =>
    have hpeq : s'.scratch.scratch_buf[p]?.getD 0#32 = s.scratch.scratch_buf[p]?.getD 0#32 := by
      rw [hbuf p (Nat.le_refl _) (by omega)]
    have hleq : ∀ k < sz,
        (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat =
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat := fun k hk => by
      rw [hbuf (p + 1 + k) (by omega) (by omega)]
    refine .cons (sz := sz) hbd (by simpa [hpeq] using hsz)
      (fun k hk => by rw [hleq k hk, hvars]; exact hlts k hk) ?_ ?_
      (ih fun idx hi1 hi2 => hbuf idx (by omega) hi2)
    · have hm : ((List.range sz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) =
          ((List.range sz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) :=
        List.map_congr_left fun k hk => by rw [hleq k (List.mem_range.mp hk)]
      rw [hm]; exact hnd
    · have hm : ((List.range sz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) =
          ((List.range sz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) :=
        List.map_congr_left fun k hk => by exact hleq k (List.mem_range.mp hk)
      rw [hm]; exact hent

theorem resBuf_append_block {F_cur : List (List Nat)} {s s' : FullState}
    {r0 r1 sz : Nat} (hvars : s'.core.cur_vars = s.core.cur_vars)
    (hbuf : ∀ idx < r1, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (hsz : (s'.scratch.scratch_buf[r1]?.getD 0#32).toNat = sz)
    (hlts : ∀ k < sz,
      (s'.scratch.scratch_buf[r1 + 1 + k]?.getD 0#32).toNat < 2 * s'.core.cur_vars)
    (hnodup : ((List.range sz).map fun k =>
      (s'.scratch.scratch_buf[r1 + 1 + k]?.getD 0#32).toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range sz).map fun k =>
      (s'.scratch.scratch_buf[r1 + 1 + k]?.getD 0#32).toNat)))
    (h : FullResBufOkW F_cur s r1 r0) : FullResBufOkW F_cur s' (r1 + 1 + sz) r0 := by
  induction h with
  | nil => exact .cons (Nat.le_refl _) hsz hlts hnodup hent .nil
  | @cons p sz0 hbd hpsz hplts hpnd hpent _ ih =>
    have hpeq : s'.scratch.scratch_buf[p]?.getD 0#32 = s.scratch.scratch_buf[p]?.getD 0#32 := by
      rw [hbuf p (by omega)]
    have hleq : ∀ k < sz0,
        (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat =
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat := fun k hk => by
      rw [hbuf (p + 1 + k) (by omega)]
    refine .cons (sz := sz0) (by omega) (by simpa [hpeq] using hpsz)
      (fun k hk => by rw [hleq k hk, hvars]; exact hplts k hk) ?_ ?_ ih
    · have hm : ((List.range sz0).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) =
          ((List.range sz0).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) :=
        List.map_congr_left fun k hk => by rw [hleq k (List.mem_range.mp hk)]
      rw [hm]; exact hpnd
    · have hm : ((List.range sz0).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) =
          ((List.range sz0).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) :=
        List.map_congr_left fun k hk => by exact hleq k (List.mem_range.mp hk)
      rw [hm]; exact hpent

end

end LeanQbe.T.Examples.Kissat.Proof.Eliminate
