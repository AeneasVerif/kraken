/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import Std.Sat.CNF.Relabel

/-!
# Parse-Local Tumble Renaming Invariants & Pure Soundness (`Proof.Parse.Tumble`)

1. Parse-local tumble renaming invariants (`TumbleMapInv`, `TumbleInv`, `tumblePi`, `tumbleLit`,
   `TumbleCovers`, `CnfVarsLt`, `TumbleValsRel`, `TumbleUnusedZero`).
2. Pure soundness lifts (`extUnsatSound_of_tumble`, `cnf_unsat_of_relabel_tumble`,
   `fullWitnessInv_relabel_back`, `fullSparseInvW_with_fd_ext`, `fullSparseInvW_with_act`,
   `fullSparseInvW_with_gu`, `tumbleValsRel_assign_unit`) via `Std.Sat.CNF.unsat_relabel_iff`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Parse

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Parse-Local Tumble Map Invariants & Relabeling Definitions -/

/-- Parse-local tumble table invariant (`imap = core.frame_dec`, `next = scratch.extend_len`).
Tracks exact mapped count via `List.countP` so any unmapped `ev < mv` gives `next < mv`. -/
@[expose] def TumbleMapInv (mv next : Nat) (fd : List (BitVec 32)) : Prop :=
  next ≤ mv ∧
  (List.range mv).countP (fun e => decide (fd[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)) = next ∧
  (∀ e < mv, fd[e]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
    (fd[e]?.getD 0xFFFFFFFF#32).toNat < next) ∧
  (∀ e₁ < mv, ∀ e₂ < mv,
    fd[e₁]?.getD 0xFFFFFFFF#32 = fd[e₂]?.getD 0xFFFFFFFF#32 →
    fd[e₁]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 → e₁ = e₂)

/-- Conditional tumble invariant (`tum = decide (mv < extend_cap)`). -/
@[expose] def TumbleInv (tum : Bool) (mv next : Nat) (fd : List (BitVec 32)) : Prop :=
  tum = true → TumbleMapInv mv next fd

/-- Variable renaming `π : Nat → Nat` induced by `frame_dec` when `tum = true`. -/
@[expose] def tumblePi (tum : Bool) (fd : List (BitVec 32)) (e : Nat) : Nat :=
  if tum then (fd[e]?.getD 0xFFFFFFFF#32).toNat else e

/-- Literal renaming corresponding to `tumblePi`. -/
@[expose] def tumbleLit (tum : Bool) (fd : List (BitVec 32)) (l : Nat) : Nat :=
  2 * tumblePi tum fd (l / 2) + l % 2

/-- Every variable occurring in `F` is mapped in `fd` when `tum = true`. -/
@[expose] def TumbleCovers (tum : Bool) (fd : List (BitVec 32)) (F : CNF Nat) : Prop :=
  tum = true → ∀ v, CNF.VarMem v F → fd[v]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32

/-- Every variable occurring in `F` is strictly below `mv`. -/
@[expose] def CnfVarsLt (mv : Nat) (F : CNF Nat) : Prop :=
  ∀ v, CNF.VarMem v F → v < mv

/-- External-vs-internal `values[]` correspondence during parse-time `UnitUnsatTrace`. -/
@[expose] def TumbleValsRel (tum : Bool) (mv : Nat) (fd : List (BitVec 32))
    (vext vint : List (BitVec 8)) : Prop :=
  ∀ l < 2 * mv,
    vext[l]?.getD 0#8 =
      if tum = true ∧ fd[l / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 then 0#8
      else vint[tumbleLit tum fd l]?.getD 0#8

/-- Internal variables `[next .. mv)` remain unassigned (`0#8`) while no propagation has run. -/
@[expose] def TumbleUnusedZero (tum : Bool) (mv next : Nat) (vint : List (BitVec 8)) : Prop :=
  tum = true → ∀ l, 2 * next ≤ l → l < 2 * mv → vint[l]?.getD 0#8 = 0#8

/-! ## 2. Pure Tumble Map, Relabeling & UNSAT Soundness Lemmas -/

private theorem countP_range_zero {mv : Nat} {p : Nat → Bool}
    (hp : ∀ e < mv, p e = false) : (List.range mv).countP p = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  rw [List.mem_range] at he
  simp [hp e he]

private theorem countP_lt_length_of_false {α : Type} {xs : List α} {p : α → Bool} {a : α}
    (ha : a ∈ xs) (hf : p a = false) : xs.countP p < xs.length := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
    simp only [List.countP_cons, List.length_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [hf]; simp; exact Nat.lt_succ_of_le (List.countP_le_length)
    · have := ih ha'
      cases p x <;> simp <;> omega

private theorem countP_range_set_flip {mv ev : Nat} {p q : Nat → Bool}
    (hev : ev < mv) (hpe : p ev = false) (hqe : q ev = true)
    (hother : ∀ e < mv, e ≠ ev → q e = p e) :
    (List.range mv).countP q = (List.range mv).countP p + 1 := by
  have hgo : ∀ n, n ≤ mv →
      (List.range n).countP q =
        (List.range n).countP p + (if ev < n then 1 else 0) := by
    intro n hn
    induction n with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.countP_append, List.countP_append, ih (by omega)]
      simp only [List.countP_cons, List.countP_nil]
      by_cases hk : k = ev
      · subst hk; rw [hpe, hqe]; simp
      · have hne : k ≠ ev := hk
        rw [hother k (by omega) hne]
        by_cases hlt : ev < k
        · have hlt2 : ev < k + 1 := by omega
          simp [hlt, hlt2]; omega
        · have hlt2 : ¬ ev < k + 1 := by omega
          simp [hlt, hlt2]
  have := hgo mv (Nat.le_refl _)
  simpa [hev] using this

theorem tumbleMapInv_init {mv : Nat} {fd : List (BitVec 32)}
    (hfd : ∀ e < mv, fd[e]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    TumbleMapInv mv 0 fd := by
  refine ⟨Nat.zero_le _, ?_, fun e he => Or.inl (hfd e he),
    fun e₁ he₁ _ _ _ hne => absurd (hfd e₁ he₁) hne⟩
  exact countP_range_zero fun e he => by simp [hfd e he]

theorem tumbleMapInv_next_lt {mv next ev : Nat} {fd : List (BitVec 32)}
    (hm : TumbleMapInv mv next fd) (hev : ev < mv)
    (hun : fd[ev]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    next < mv := by
  have hlt := countP_lt_length_of_false
    (p := fun e => decide (fd[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32))
    (List.mem_range.mpr hev) (by simp [hun])
  rw [hm.2.1, List.length_range] at hlt
  exact hlt

theorem tumbleMapInv_set {mv next ev : Nat} {fd : List (BitVec 32)}
    (hm : TumbleMapInv mv next fd) (hev : ev < mv) (hfdl : mv ≤ fd.length)
    (hmv32 : mv < 2 ^ 32 - 1)
    (hun : fd[ev]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    TumbleMapInv mv (next + 1) (fd.set ev (BitVec.ofNat 32 next)) := by
  have hnxt_lt : next < mv := tumbleMapInv_next_lt hm hev hun
  have hnxt32 : next < 2 ^ 32 - 1 := by omega
  have hne_ff : BitVec.ofNat 32 next ≠ 0xFFFFFFFF#32 := by
    intro h
    have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at h1
    change next % 2 ^ 32 = 2 ^ 32 - 1 at h1
    omega
  have hto : (BitVec.ofNat 32 next).toNat = next := Nat.mod_eq_of_lt (by omega)
  let fd' := fd.set ev (BitVec.ofNat 32 next)
  have hget : ∀ e < mv, fd'[e]?.getD 0xFFFFFFFF#32 =
      if e = ev then BitVec.ofNat 32 next else fd[e]?.getD 0xFFFFFFFF#32 := fun e _ => by
    by_cases h : e = ev
    · subst h; dsimp only [fd']; rw [List.getElem?_set_self (by omega)]; simp
    · dsimp only [fd']; rw [List.getElem?_set_ne (Ne.symm h)]; simp [h]
  refine ⟨by omega, ?_, ?_, ?_⟩
  · have hcnt := countP_range_set_flip (mv := mv) (ev := ev)
      (p := fun e => decide (fd[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32))
      (q := fun e => decide (fd'[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32))
      hev (by simp [hun]) (by rw [hget ev hev]; simp [hne_ff])
      (fun e he hne => by rw [hget e he]; simp [hne])
    rw [hcnt, hm.2.1]
  · intro e he
    rw [hget e he]
    split
    · exact Or.inr (by rw [hto]; omega)
    · rcases hm.2.2.1 e he with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (by omega)
  · intro e₁ he₁ e₂ he₂ heq hne
    rw [hget e₁ he₁, hget e₂ he₂] at heq
    rw [hget e₁ he₁] at hne
    by_cases h1 : e₁ = ev <;> by_cases h2 : e₂ = ev
    · omega
    · simp only [h1, h2, ↓reduceIte] at heq
      rcases hm.2.2.1 e₂ he₂ with hff | hlt
      · rw [hff] at heq; exact absurd heq hne_ff
      · have := congrArg BitVec.toNat heq; rw [hto] at this; omega
    · simp only [h1, h2, ↓reduceIte] at heq
      rcases hm.2.2.1 e₁ he₁ with hff | hlt
      · rw [hff] at heq; exact absurd heq.symm hne_ff
      · have := congrArg BitVec.toNat heq; rw [hto] at this; omega
    · simp only [h1, h2, ↓reduceIte] at heq hne
      exact hm.2.2.2 e₁ he₁ e₂ he₂ heq hne

theorem tumblePi_false (fd : List (BitVec 32)) : tumblePi false fd = id := by
  funext e; rfl

theorem tumbleLit_false (fd : List (BitVec 32)) (l : Nat) : tumbleLit false fd l = l := by
  unfold tumbleLit tumblePi; simp; omega

theorem tumbleLit_div2 (tum : Bool) (fd : List (BitVec 32)) (l : Nat) :
    tumbleLit tum fd l / 2 = tumblePi tum fd (l / 2) := by
  unfold tumbleLit; omega

theorem tumbleLit_mod2 (tum : Bool) (fd : List (BitVec 32)) (l : Nat) :
    tumbleLit tum fd l % 2 = l % 2 := by
  unfold tumbleLit; omega

private theorem tum_nat_xor1_eq (l : Nat) :
    l ^^^ 1 = if l % 2 = 0 then l + 1 else l - 1 := by
  have h : l ^^^ 1 = 2 * (l / 2) + (1 - l % 2) := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_xor]
    cases i with
    | zero =>
      simp only [Nat.testBit_zero, show (1 : Nat) % 2 = 1 from rfl, decide_true, Bool.xor_true]
      by_cases he : l % 2 = 0
      · simp [he]
      · have hl1 : l % 2 = 1 := by omega
        simp [hl1]
    | succ k =>
      have h1 : Nat.testBit 1 (k + 1) = false := by simp [Nat.testBit_succ]
      rw [h1, Bool.xor_false, Nat.testBit_succ, Nat.testBit_succ,
        show (2 * (l / 2) + (1 - l % 2)) / 2 = l / 2 by omega]
  by_cases he : l % 2 = 0 <;> simp [he] <;> omega

theorem tum_nat_xor1_div2 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := by
  rw [tum_nat_xor1_eq]; by_cases h : l % 2 = 0 <;> simp [h] <;> omega

theorem tumbleLit_xor1 (tum : Bool) (fd : List (BitVec 32)) (l : Nat) :
    tumbleLit tum fd (l ^^^ 1) = tumbleLit tum fd l ^^^ 1 := by
  unfold tumbleLit
  rw [tum_nat_xor1_div2, tum_nat_xor1_eq l, tum_nat_xor1_eq (2 * tumblePi tum fd (l / 2) + l % 2)]
  by_cases h : l % 2 = 0
  · have h2 : (l + 1) % 2 = 1 := by omega
    simp [h, h2]
  · have h2 : (l - 1) % 2 = 0 := by omega
    have h3 : l % 2 = 1 := by omega
    simp [h2, h3]

theorem tumblePi_lt {tum : Bool} {mv next e : Nat} {fd : List (BitVec 32)}
    (hm : TumbleInv tum mv next fd) (he : e < mv)
    (hmap : tum = true → fd[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    tumblePi tum fd e < mv := by
  cases tum with
  | false => simpa [tumblePi] using he
  | true =>
    have hm' := hm rfl
    unfold tumblePi; simp only [↓reduceIte]
    rcases hm'.2.2.1 e he with hff | hlt
    · exact absurd hff (hmap rfl)
    · exact Nat.lt_of_lt_of_le hlt hm'.1

theorem tumbleLit_lt {tum : Bool} {mv next l : Nat} {fd : List (BitVec 32)}
    (hm : TumbleInv tum mv next fd) (hl : l < 2 * mv)
    (hmap : tum = true → fd[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    tumbleLit tum fd l < 2 * mv := by
  have hp := tumblePi_lt hm (by omega : l / 2 < mv) hmap
  unfold tumbleLit; omega

theorem tumblePi_set_eq {tum : Bool} {ev e : Nat} {v : BitVec 32} {fd : List (BitVec 32)}
    (hun : fd[ev]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hmap : tum = true → fd[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    tumblePi tum (fd.set ev v) e = tumblePi tum fd e := by
  cases tum with
  | false => rfl
  | true =>
    have hne : ev ≠ e := fun heq => by subst heq; exact hmap rfl hun
    unfold tumblePi; simp only [↓reduceIte, List.getElem?_set_ne hne]

theorem tumbleLit_set_eq {tum : Bool} {ev l : Nat} {v : BitVec 32} {fd : List (BitVec 32)}
    (hun : fd[ev]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hmap : tum = true → fd[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    tumbleLit tum (fd.set ev v) l = tumbleLit tum fd l := by
  unfold tumbleLit
  rw [tumblePi_set_eq hun hmap]

theorem tumbleCovers_empty (tum : Bool) (fd : List (BitVec 32)) :
    TumbleCovers tum fd (shiftDownCnf CNF.empty) := by
  intro _ v hv
  simp only [CNF.VarMem, shiftDownCnf, CNF.empty, Array.map_empty] at hv
  obtain ⟨c, hc, _⟩ := hv
  exact absurd hc (by simp)

theorem cnfVarsLt_empty (mv : Nat) : CnfVarsLt mv (shiftDownCnf CNF.empty) := by
  intro v hv
  simp only [CNF.VarMem, shiftDownCnf, CNF.empty, Array.map_empty] at hv
  obtain ⟨c, hc, _⟩ := hv
  exact absurd hc (by simp)

theorem tumbleCovers_set {tum : Bool} {ev : Nat} {v : BitVec 32} {fd : List (BitVec 32)}
    {F : CNF Nat} (hc : TumbleCovers tum fd F)
    (hun : fd[ev]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    TumbleCovers tum (fd.set ev v) F := by
  intro ht u hu
  have hmap := hc ht u hu
  have hne : ev ≠ u := fun heq => by subst heq; exact hmap hun
  rw [List.getElem?_set_ne hne]; exact hmap

theorem cnf_relabel_tumble_set {tum : Bool} {ev : Nat} {v : BitVec 32}
    {fd : List (BitVec 32)} {F : CNF Nat}
    (hc : TumbleCovers tum fd F)
    (hun : fd[ev]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    CNF.relabel (tumblePi tum (fd.set ev v)) F = CNF.relabel (tumblePi tum fd) F :=
  CNF.relabel_congr fun u hu => tumblePi_set_eq hun (fun ht => hc ht u hu)

theorem cnf_relabel_tumble_false {fd : List (BitVec 32)} {F : CNF Nat} :
    CNF.relabel (tumblePi false fd) F = F := by
  rw [tumblePi_false, CNF.relabel_id]

theorem tumblePi_inj {tum : Bool} {mv next : Nat} {fd : List (BitVec 32)} {F : CNF Nat}
    (hm : TumbleInv tum mv next fd) (hc : TumbleCovers tum fd F) (hvb : CnfVarsLt mv F) :
    ∀ {v1 v2}, CNF.VarMem v1 F → CNF.VarMem v2 F →
      tumblePi tum fd v1 = tumblePi tum fd v2 → v1 = v2 := by
  intro v1 v2 h1 h2 heq
  cases tum with
  | false => simpa [tumblePi] using heq
  | true =>
    have hm' := hm rfl
    unfold tumblePi at heq; simp only [↓reduceIte] at heq
    have hbv : fd[v1]?.getD 0xFFFFFFFF#32 = fd[v2]?.getD 0xFFFFFFFF#32 :=
      BitVec.eq_of_toNat_eq heq
    exact hm'.2.2.2 v1 (hvb v1 h1) v2 (hvb v2 h2) hbv (hc rfl v1 h1)

/-- Core UNSAT soundness transfer across tumble renaming via `Std.Sat.CNF.unsat_relabel_iff`. -/
theorem cnf_unsat_of_relabel_tumble {tum : Bool} {mv next : Nat} {fd : List (BitVec 32)}
    {F : CNF Nat} (hm : TumbleInv tum mv next fd) (hc : TumbleCovers tum fd F)
    (hvb : CnfVarsLt mv F) (hu : (CNF.relabel (tumblePi tum fd) F).Unsat) :
    F.Unsat :=
  (CNF.unsat_relabel_iff (tumblePi_inj hm hc hvb)).mp hu

/-- Bridge relabeled `ExtUnsatSound` back to original `F0` without changing `FullWitnessInv`. -/
theorem extUnsatSound_of_tumble {tum : Bool} {F0 : CNF Nat} {F : List (List Nat)}
    {mv next : Nat} {fd : List (BitVec 32)}
    (hm : TumbleInv tum mv next fd) (hc : TumbleCovers tum fd F0) (hvb : CnfVarsLt mv F0)
    (hext : ExtUnsatSound (CNF.relabel (tumblePi tum fd) F0) mv F) :
    ExtUnsatSound F0 mv F :=
  ⟨hext.1, fun hu => cnf_unsat_of_relabel_tumble hm hc hvb (hext.2 hu)⟩

/-- Lift `FullWitnessInv` from relabeled `F0` back to original `F0` at parse exit. -/
theorem fullWitnessInv_relabel_back {c : FullCfg} {tum : Bool} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} {next : Nat}
    (hcv : k.cur_vars = c.mv)
    (hm : TumbleInv tum c.mv next k.frame_dec) (hc : TumbleCovers tum k.frame_dec F0)
    (hvb : CnfVarsLt c.mv F0)
    (hw : FullWitnessInv c (CNF.relabel (tumblePi tum k.frame_dec) F0) F_cur k) :
    FullWitnessInv c F0 F_cur k :=
  { hw with ext_sound := hcv ▸ extUnsatSound_of_tumble hm hc hvb (hcv ▸ hw.ext_sound) }

/-- Updating `frame_dec` and `extend_len` (at `cur_level = 0`, `extend_len ≤ extend_cap`)
preserves `FullSparseInvW` for any `F0`. -/
theorem fullSparseInvW_with_fd_ext {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (hcl0 : s.core.cur_level = 0)
    {fd' : List (BitVec 32)} {ext' : List (BitVec 32)} {elen' : Nat}
    (hfdl : fd'.length = c.max_vars + 1) (hextl : ext'.length = c.extend_cap)
    (helen : elen' ≤ c.extend_cap) :
    FullSparseInvW c F0 F_cur
      { core := { s.core with frame_dec := fd' }
        scratch := { s.scratch with extend_stk := ext', extend_len := elen' } } := by
  let s' : FullState :=
    { core := { s.core with frame_dec := fd' }
      scratch := { s.scratch with extend_stk := ext', extend_len := elen' } }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hsp.1.core_ok with frame_dec_len := hfdl },
     { hsp.1.scratch_ok with extend_stk_len := hextl }⟩
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hsp.2.1 with
      arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
      watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      frame_dec_lt := fun L hL1 hLle => by change L ≤ s.core.cur_level at hLle; omega }
  exact ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1, ⟨hsp.2.2.2.2.1.1, helen⟩, hsp.2.2.2.2.2⟩

/-- Updating `flags`, `unassigned`, and `FullExtScratchPres`-preserving scratch preserves
`FullSparseInvW`. -/
theorem fullSparseInvW_with_act {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {flags' : List (BitVec 32)} {unass' : BitVec 64} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with flags := flags', unassigned := unass' }
                scratch := sc' } : FullState).LengthsOk c)
    (hpres : FullExtScratchPres s
      { core := { s.core with flags := flags', unassigned := unass' }, scratch := sc' }) :
    FullSparseInvW c F0 F_cur
      { core := { s.core with flags := flags', unassigned := unass' }, scratch := sc' } := by
  let s' : FullState :=
    { core := { s.core with flags := flags', unassigned := unass' }, scratch := sc' }
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hsp.2.1 with
      arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
      watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1,
    hsp.2.2.2.2.1.of_pres hpres (fun _ hr => hr), hsp.2.2.2.2.2⟩

/-- Updating `glue_used` only preserves `FullSparseInvW`. -/
theorem fullSparseInvW_with_gu {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {gu' : List (BitVec 32)} (hgu : gu'.length = 64) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with glue_used := gu' } } := by
  refine ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with glue_used_len := hgu }⟩,
    { hsp.2.1 with
      arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
      watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

/-- Relabeling a Kissat DIMACS clause agrees with `cnfClause` on `tumbleLit`-mapped literals. -/
theorem cnfClause_relabel_eq {tum : Bool} {fd : List (BitVec 32)} {lits : List Nat} :
    CNF.Clause.relabel (tumblePi tum fd)
      (shiftDownClause (CNF.Clause.ofLiterals (lits.map kissatLitToDimacsLiteral))) =
      cnfClause (lits.map (tumbleLit tum fd)) := by
  apply CNF.Clause.ext
  rw [CNF.Clause.literals_relabel]
  unfold shiftDownClause cnfClause
  simp only [CNF.Clause.literals_ofLiterals, List.map_map]
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_def, kissatLitToDimacsLiteral, litToLiteral, litVar, litSign]
  rw [tumbleLit_div2, tumbleLit_mod2, Nat.add_sub_cancel]

/-- Adding a clause preserves `TumbleCovers` when every variable in `lits` is mapped. -/
theorem tumbleCovers_add_clause {tum : Bool} {fd : List (BitVec 32)}
    {accCnf : CNF Nat} {lits : List Nat}
    (hc : TumbleCovers tum fd (shiftDownCnf accCnf))
    (hcov : tum = true → ∀ l ∈ lits, fd[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    TumbleCovers tum fd
      (shiftDownCnf (accCnf.add (CNF.Clause.ofLiterals (lits.map kissatLitToDimacsLiteral)))) := by
  intro ht v hv
  rw [shiftDownCnf_add, CNF.VarMem_add] at hv
  rcases hv with hv1 | hv2
  · rw [CNF.Clause.VarMem_iff_exists_mem_literals] at hv1
    obtain ⟨pol, hmem⟩ := hv1
    unfold shiftDownClause at hmem
    simp only [CNF.Clause.literals_ofLiterals, List.map_map, List.mem_map] at hmem
    obtain ⟨l, hl, hpair⟩ := hmem
    simp only [Function.comp_def, kissatLitToDimacsLiteral, Nat.add_sub_cancel,
      Prod.mk.injEq] at hpair
    rw [← hpair.1]
    exact hcov ht l hl
  · exact hc ht v hv2

/-- Adding a clause with literals `< 2 * mv` preserves `CnfVarsLt mv`. -/
theorem cnfVarsLt_add_clause {mv : Nat} {accCnf : CNF Nat} {lits : List Nat}
    (hvb : CnfVarsLt mv (shiftDownCnf accCnf))
    (hlt : ∀ l ∈ lits, l < 2 * mv) :
    CnfVarsLt mv
      (shiftDownCnf (accCnf.add (CNF.Clause.ofLiterals (lits.map kissatLitToDimacsLiteral)))) := by
  intro v hv
  rw [shiftDownCnf_add, CNF.VarMem_add] at hv
  rcases hv with hv1 | hv2
  · rw [CNF.Clause.VarMem_iff_exists_mem_literals] at hv1
    obtain ⟨pol, hmem⟩ := hv1
    unfold shiftDownClause at hmem
    simp only [CNF.Clause.literals_ofLiterals, List.map_map, List.mem_map] at hmem
    obtain ⟨l, hl, hpair⟩ := hmem
    simp only [Function.comp_def, kissatLitToDimacsLiteral, Nat.add_sub_cancel,
      Prod.mk.injEq] at hpair
    have hpair1 : l / 2 = v := hpair.1
    have := hlt l hl; omega
  · exact hvb v hv2

/-! ## 3. `TumbleValsRel` & `TumbleUnusedZero` Helpers for `UnitUnsatTrace` -/

theorem tumbleValsRel_init {tum : Bool} {mv mx : Nat} {fd : List (BitVec 32)} :
    TumbleValsRel tum mv fd (List.replicate (2 * mv) 0#8) (List.replicate (2 * mx) 0#8) := by
  intro l hl
  have h1 : (List.replicate (2 * mv) 0#8)[l]?.getD 0#8 = 0#8 := by simp [hl]
  rw [h1]
  split
  · rfl
  · by_cases hlt : tumbleLit tum fd l < 2 * mx
    · simp [hlt]
    · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem tumbleUnusedZero_init {tum : Bool} {mv mx : Nat} (hmv : mv ≤ mx) :
    TumbleUnusedZero tum mv 0 (List.replicate (2 * mx) 0#8) := by
  intro _ l _ hl; simp [show l < 2 * mx by omega]

theorem tumbleValsRel_set_unmapped {tum : Bool} {mv next ev : Nat}
    {fd : List (BitVec 32)} {vext vint : List (BitVec 8)}
    (hrel : TumbleValsRel tum mv fd vext vint)
    (hunz : TumbleUnusedZero tum mv next vint)
    (hev : ev < mv) (hfdl : mv ≤ fd.length) (hnxt : next < mv) (hmv32 : mv < 2 ^ 32)
    (hun : fd[ev]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    TumbleValsRel tum mv (fd.set ev (BitVec.ofNat 32 next)) vext vint := by
  intro l hl
  have h0 := hrel l hl
  cases tum with
  | false => simpa [tumbleLit_false] using h0
  | true =>
    have hto : (BitVec.ofNat 32 next).toNat = next := Nat.mod_eq_of_lt (by omega)
    have hne_ff : BitVec.ofNat 32 next ≠ 0xFFFFFFFF#32 := by
      intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      change next % 2 ^ 32 = 2 ^ 32 - 1 at this; omega
    by_cases hlev : l / 2 = ev
    · rw [hlev] at h0
      simp only [hun, true_and, ↓reduceIte] at h0
      rw [h0, hlev, List.getElem?_set_self (by omega)]
      simp only [Option.getD_some, hne_ff, and_false, ↓reduceIte]
      unfold tumbleLit tumblePi
      rw [hlev, List.getElem?_set_self (by omega)]
      simp only [Option.getD_some, ↓reduceIte, hto]
      exact (hunz rfl (2 * next + l % 2) (by omega) (by omega)).symm
    · have hne : ev ≠ l / 2 := Ne.symm hlev
      rw [List.getElem?_set_ne hne]
      have hlit_eq : tumbleLit true (fd.set ev (BitVec.ofNat 32 next)) l =
          tumbleLit true fd l := by
        unfold tumbleLit tumblePi; simp only [↓reduceIte, List.getElem?_set_ne hne]
      rw [hlit_eq]; exact h0

theorem tumbleValsRel_assign_unit {tum : Bool} {mv next l : Nat}
    {fd : List (BitVec 32)} {vext vint : List (BitVec 8)}
    (hm : TumbleInv tum mv next fd)
    (hrel : TumbleValsRel tum mv fd vext vint)
    (hvl : 2 * mv ≤ vext.length) (hvil : 2 * mv ≤ vint.length)
    (hl : l < 2 * mv) (hmap : tum = true → fd[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    let tl := tumbleLit tum fd l
    TumbleValsRel tum mv fd
      ((vext.set l 1#8).set (l ^^^ 1) 0xFF#8)
      ((vint.set tl 1#8).set (tl ^^^ 1) 0xFF#8) := by
  intro tl k hk
  have htl_lt : tl < 2 * mv := tumbleLit_lt hm hl hmap
  have hln_lt : l ^^^ 1 < 2 * mv := litNeg_lt_two_mul hl
  have htln_lt : tl ^^^ 1 < 2 * mv := litNeg_lt_two_mul htl_lt
  have hdiv_ln : (l ^^^ 1) / 2 = l / 2 := tum_nat_xor1_div2 l
  by_cases hkn : k = l ^^^ 1
  · subst hkn
    rw [List.getElem?_set_self (by simp; omega)]
    simp only [Option.getD_some]
    have hnotun : ¬ (tum = true ∧ fd[(l ^^^ 1) / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := by
      rintro ⟨ht, hff⟩; rw [hdiv_ln] at hff; exact hmap ht hff
    simp only [hnotun, ↓reduceIte, tumbleLit_xor1]
    rw [List.getElem?_set_self (by simp; omega)]; rfl
  · rw [List.getElem?_set_ne (Ne.symm hkn)]
    by_cases hkl : k = l
    · rw [hkl, List.getElem?_set_self (by omega)]
      simp only [Option.getD_some]
      have hnotun : ¬ (tum = true ∧ fd[l / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := by
        rintro ⟨ht, hff⟩; exact hmap ht hff
      simp only [hnotun, ↓reduceIte]
      have hne_tl : tl ^^^ 1 ≠ tl := litNeg_ne_self tl
      rw [List.getElem?_set_ne hne_tl, List.getElem?_set_self (by omega)]; rfl
    · rw [List.getElem?_set_ne (Ne.symm hkl)]
      have h0 := hrel k hk
      split at h0
      · rename_i hun_k
        simp only [hun_k]; exact h0
      · rename_i hnotun_k
        simp only [hnotun_k, ↓reduceIte]
        have htk_ne_tl : tl ≠ tumbleLit tum fd k := by
          intro heq
          have hpi : tumblePi tum fd (k / 2) = tumblePi tum fd (l / 2) := by
            have := congrArg (· / 2) heq.symm
            rw [tumbleLit_div2, tumbleLit_div2] at this; exact this
          have hmd : k % 2 = l % 2 := by
            have := congrArg (· % 2) heq.symm
            rw [tumbleLit_mod2, tumbleLit_mod2] at this; exact this
          have hkv : k / 2 = l / 2 := by
            cases tum with
            | false => simpa [tumblePi] using hpi
            | true =>
              have hm' := hm rfl
              unfold tumblePi at hpi; simp only [↓reduceIte] at hpi
              exact hm'.2.2.2 (k / 2) (by omega) (l / 2) (by omega)
                (BitVec.eq_of_toNat_eq hpi) (fun hff => hnotun_k ⟨rfl, hff⟩)
          omega
        have htk_ne_tln : tl ^^^ 1 ≠ tumbleLit tum fd k := by
          intro heq
          rw [← tumbleLit_xor1] at heq
          have hpi : tumblePi tum fd (k / 2) = tumblePi tum fd ((l ^^^ 1) / 2) := by
            have := congrArg (· / 2) heq.symm
            rw [tumbleLit_div2, tumbleLit_div2] at this; exact this
          have hmd : k % 2 = (l ^^^ 1) % 2 := by
            have := congrArg (· % 2) heq.symm
            rw [tumbleLit_mod2, tumbleLit_mod2] at this; exact this
          have hkv : k / 2 = (l ^^^ 1) / 2 := by
            cases tum with
            | false => simpa [tumblePi] using hpi
            | true =>
              have hm' := hm rfl
              unfold tumblePi at hpi; simp only [↓reduceIte] at hpi
              exact hm'.2.2.2 (k / 2) (by omega) ((l ^^^ 1) / 2) (by omega)
                (BitVec.eq_of_toNat_eq hpi) (fun hff => hnotun_k ⟨rfl, hff⟩)
          omega
        rw [List.getElem?_set_ne htk_ne_tln, List.getElem?_set_ne htk_ne_tl]
        exact h0

theorem tumbleUnusedZero_assign {tum : Bool} {mv next tl : Nat} {vint : List (BitVec 8)}
    (hunz : TumbleUnusedZero tum mv next vint) (htl : tum = true → tl < 2 * next) :
    TumbleUnusedZero tum mv next ((vint.set tl 1#8).set (tl ^^^ 1) 0xFF#8) := by
  intro ht j hj1 hj2
  have htl' := htl ht
  have htln' : tl ^^^ 1 < 2 * next := litNeg_lt_two_mul htl'
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  exact hunz ht j hj1 hj2

theorem tumbleUnusedZero_mono {tum : Bool} {mv n1 n2 : Nat} {vint : List (BitVec 8)}
    (hunz : TumbleUnusedZero tum mv n1 vint) (hle : n1 ≤ n2) :
    TumbleUnusedZero tum mv n2 vint :=
  fun ht j hj1 hj2 => hunz ht j (by omega) hj2

end LeanQbe.T.Examples.Kissat.Proof.Parse
