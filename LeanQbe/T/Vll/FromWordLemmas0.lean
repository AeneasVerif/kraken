module

public import LeanQbe.T.Vll.FromWord
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.TargetLemmas
import LeanQbe.T.BedrockWord.Ops

/-!
# Core Simulation & Framing Lemmas for `Vll.FromWord` (`Vll.FromWordLemmas0`)

Arch-free foundational proof layer for `LeanQbe.T.Vll.FromWord`:
* §1. `WordRegBind.Wf` disjointness & `locOf` injectivity + `EnvRel` / `WordRegsRel` framing.
* §2. `bodyWp` combinators, stack-slot & prologue/epilogue `instrWp`, and `hwStackMem` helpers.
* §3. `BitVec` & `ValHolds64` bitvector identities for all lowered scalar/bool ops & casts.
* §4. Operand loading (`loadArgToGpr`, `loadArgInto`, `argToSrc`), `emitToLoc`, and
      cycle-breaking parallel register transfer (`parMove`, `emitNextRegs`).
* §5. Lowered ALU, comparison, branchless select, and `lowerOp_bodyWp` correctness.

Zero `@[expose]`, zero `Arm64`/`Amd64`/`Kraken.X64`/`Kraken.AArch64` imports, zero `*Lemmas*`
public imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.BedrockWord

/-! ## §1. `WordRegBind.Wf` Disjointness, `locOf` Injectivity, and `EnvRel` Framing -/

private theorem nodup_getElem?_inj {α : Type} :
    ∀ {xs : List α}, xs.Nodup → ∀ {i j : Nat} {a : α},
      xs[i]? = some a → xs[j]? = some a → i = j
  | [], _, _, _, _, hi, _ => by simp at hi
  | x :: xs, hnd, 0, 0, _, _, _ => rfl
  | x :: xs, hnd, 0, j + 1, a, hi, hj => by
    rw [List.nodup_cons] at hnd
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    simp only [List.getElem?_cons_succ] at hj
    subst hi
    exact absurd (List.mem_of_getElem? hj) hnd.1
  | x :: xs, hnd, i + 1, 0, a, hi, hj => by
    rw [List.nodup_cons] at hnd
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    simp only [List.getElem?_cons_succ] at hi
    subst hj
    exact absurd (List.mem_of_getElem? hi) hnd.1
  | x :: xs, hnd, i + 1, j + 1, a, hi, hj => by
    rw [List.nodup_cons] at hnd
    exact congrArg Nat.succ (nodup_getElem?_inj hnd.2 hi hj)

theorem WordRegBind.checkStruct_wf {A : Arch} (b : WordRegBind A)
    (hs : b.checkStruct = true)
    (hc : ∀ (o : CmpOp) (cc : A.Cond) (w : Width) (x y : BitVec w.bits) (f : A.Flags),
      b.condOfCmp? o = some cc → A.evalCond (A.cmpFlags w x y f) cc = o.evalBits x y) :
    b.Wf := by
  dsimp only [WordRegBind.checkStruct] at hs
  rw [Bool.and_eq_true] at hs
  have hall := List.all_eq_true.mp hs.2
  refine ⟨listNodup_nodup hs.1, ?_, ?_, ?_, ?_, hc⟩
  · intro r hr
    have h := hall r hr
    simp only [Bool.and_eq_true, bne_iff_ne] at h
    exact h.1.1.1
  · intro r hr hm
    have h := hall r hr
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    have hc' : A.abi.scratch.contains r = true := List.contains_iff_mem.mpr hm
    rw [hc'] at h; cases h.1.1.2
  · intro r hr hm
    have h := hall r hr
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    have hc' : A.abi.raRegs.contains r = true := List.contains_iff_mem.mpr hm
    rw [hc'] at h; cases h.1.2
  · intro r hr
    have hrAll : r ∈ b.allRegs := List.mem_append_left _ (List.mem_append_left _ hr)
    have h := hall r hrAll
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    have hcon : b.wordRegs.contains r = true := List.contains_iff_mem.mpr hr
    rcases h.2 with ((hnot | ha) | hc')
    · rw [hcon] at hnot; cases hnot
    · exact Or.inl (List.contains_iff_mem.mp ha)
    · exact Or.inr (List.contains_iff_mem.mp hc')

private theorem allRegs_idx_eq {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {i j : Nat} {r : A.Reg} (hi : b.allRegs[i]? = some r) (hj : b.allRegs[j]? = some r) :
    i = j :=
  nodup_getElem?_inj hwf.allRegs_nodup hi hj

private theorem regAt_eq_allRegs? {A : Arch} (b : WordRegBind A) {i : Nat} (hi : i < 6) :
    b.allRegs[i]? = some (b.regAt i) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl

private theorem workRegs_idx_eq_allRegs? {A : Arch} (b : WordRegBind A) :
    b.allRegs[6]? = some b.altRet ∧ b.allRegs[7]? = some b.w0 ∧
    b.allRegs[8]? = some b.w1 ∧ b.allRegs[9]? = some b.w2 :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem tmps_eq_allRegs? {A : Arch} (b : WordRegBind A) {i : Nat} {r : A.Reg}
    (hi : b.tmps[i]? = some r) : b.allRegs[10 + i]? = some r := by
  have h10 : (b.wordRegs ++ b.workRegs).length = 10 := by
    simp [WordRegBind.wordRegs, WordRegBind.workRegs]
  dsimp only [WordRegBind.allRegs]
  rw [List.getElem?_append_right (by omega), h10, show 10 + i - 10 = i by omega]
  exact hi

theorem wordRegBind_work_ne {A : Arch} {b : WordRegBind A} (hwf : b.Wf) :
    b.altRet ≠ b.w0 ∧ b.altRet ≠ b.w1 ∧ b.altRet ≠ b.w2 ∧
    b.w0 ≠ b.w1 ∧ b.w0 ≠ b.w2 ∧ b.w1 ≠ b.w2 := by
  have ⟨h6, h7, h8, h9⟩ := workRegs_idx_eq_allRegs? b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he
  · exact absurd (allRegs_idx_eq hwf h6 (he ▸ h7)) (by decide)
  · exact absurd (allRegs_idx_eq hwf h6 (he ▸ h8)) (by decide)
  · exact absurd (allRegs_idx_eq hwf h6 (he ▸ h9)) (by decide)
  · exact absurd (allRegs_idx_eq hwf h7 (he ▸ h8)) (by decide)
  · exact absurd (allRegs_idx_eq hwf h7 (he ▸ h9)) (by decide)
  · exact absurd (allRegs_idx_eq hwf h8 (he ▸ h9)) (by decide)

theorem wordRegs_nodup {A : Arch} {b : WordRegBind A} (hwf : b.Wf) : b.wordRegs.Nodup := by
  have h1 := hwf.allRegs_nodup
  simp only [WordRegBind.allRegs, List.nodup_append] at h1
  exact h1.1.1

theorem locOf_gpr_idx {A : Arch} (b : WordRegBind A) (sb lvl : Nat) {r : A.Reg}
    (h : locOf b sb lvl = .gpr r) :
    ∃ k, b.allRegs[k]? = some r ∧
      ((lvl < 6 ∧ k = lvl) ∨ (6 ≤ lvl ∧ k = 10 + (lvl - 6) ∧ lvl - 6 < b.tmps.length)) := by
  dsimp only [locOf] at h
  split at h
  · rename_i hl6; cases h; exact ⟨lvl, regAt_eq_allRegs? b hl6, Or.inl ⟨hl6, rfl⟩⟩
  · rename_i hge
    have h6 : 6 ≤ lvl := Nat.le_of_not_lt hge
    cases hget : b.tmps[lvl - 6]? with
    | none => simp [hget] at h
    | some r' =>
      simp only [hget, WordLoc.gpr.injEq] at h; subst h
      have hlt : lvl - 6 < b.tmps.length := (List.getElem?_eq_some_iff.mp hget).1
      exact ⟨10 + (lvl - 6), tmps_eq_allRegs? b hget, Or.inr ⟨h6, rfl, hlt⟩⟩

theorem locOf_gpr_inj {A : Arch} {b : WordRegBind A} (hwf : b.Wf) (sb l₁ l₂ : Nat)
    {r : A.Reg} (h1 : locOf b sb l₁ = .gpr r) (h2 : locOf b sb l₂ = .gpr r) : l₁ = l₂ := by
  obtain ⟨k1, hk1, hc1⟩ := locOf_gpr_idx b sb l₁ h1
  obtain ⟨k2, hk2, hc2⟩ := locOf_gpr_idx b sb l₂ h2
  have hk := allRegs_idx_eq hwf hk1 hk2
  rcases hc1 with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rcases hc2 with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> omega

theorem locOf_inj {A : Arch} {b : WordRegBind A} (hwf : b.Wf) (sb l₁ l₂ : Nat)
    (h : locOf b sb l₁ = locOf b sb l₂) : l₁ = l₂ := by
  cases h1 : locOf b sb l₁ with
  | gpr r => exact locOf_gpr_inj hwf sb l₁ l₂ h1 (h ▸ h1)
  | slot k =>
    have h2 : locOf b sb l₂ = .slot k := h ▸ h1
    dsimp only [locOf] at h1 h2
    split at h1; · cases h1
    split at h2; · cases h2
    cases hg1 : b.tmps[l₁ - 6]? <;> simp [hg1] at h1
    cases hg2 : b.tmps[l₂ - 6]? <;> simp [hg2] at h2
    have hnone1 : b.tmps.length ≤ l₁ - 6 := (List.getElem?_eq_none_iff.mp hg1)
    have hnone2 : b.tmps.length ≤ l₂ - 6 := (List.getElem?_eq_none_iff.mp hg2)
    omega

theorem locOf_gpr_ne_work {A : Arch} {b : WordRegBind A} (hwf : b.Wf) (sb lvl : Nat) {r : A.Reg}
    (h : locOf b sb lvl = .gpr r) :
    r ≠ b.altRet ∧ r ≠ b.w0 ∧ r ≠ b.w1 ∧ r ≠ b.w2 := by
  obtain ⟨k, hk, hc⟩ := locOf_gpr_idx b sb lvl h
  have ⟨h6, h7, h8, h9⟩ := workRegs_idx_eq_allRegs? b
  have hk_not : k ≠ 6 ∧ k ≠ 7 ∧ k ≠ 8 ∧ k ≠ 9 := by
    rcases hc with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> omega
  refine ⟨fun e => hk_not.1 (allRegs_idx_eq hwf hk (e ▸ h6)),
          fun e => hk_not.2.1 (allRegs_idx_eq hwf hk (e ▸ h7)),
          fun e => hk_not.2.2.1 (allRegs_idx_eq hwf hk (e ▸ h8)),
          fun e => hk_not.2.2.2 (allRegs_idx_eq hwf hk (e ▸ h9))⟩

theorem locOf_gpr_mem_allRegs {A : Arch} (b : WordRegBind A) (sb lvl : Nat) {r : A.Reg}
    (h : locOf b sb lvl = .gpr r) : r ∈ b.allRegs := by
  obtain ⟨k, hk, _⟩ := locOf_gpr_idx b sb lvl h
  exact List.mem_of_getElem? hk

theorem locOf_gpr_ne_sp {A : Arch} {b : WordRegBind A} (hwf : b.Wf) (sb lvl : Nat) {r : A.Reg}
    (h : locOf b sb lvl = .gpr r) : r ≠ A.abi.sp :=
  hwf.no_sp r (locOf_gpr_mem_allRegs b sb lvl h)

theorem locOf_gpr_not_ra {A : Arch} {b : WordRegBind A} (hwf : b.Wf) (sb lvl : Nat) {r : A.Reg}
    (h : locOf b sb lvl = .gpr r) : r ∉ A.abi.raRegs :=
  hwf.no_ra r (locOf_gpr_mem_allRegs b sb lvl h)

theorem work_not_sp {A : Arch} {b : WordRegBind A} (hwf : b.Wf) :
    b.altRet ≠ A.abi.sp ∧ b.w0 ≠ A.abi.sp ∧ b.w1 ≠ A.abi.sp ∧ b.w2 ≠ A.abi.sp := by
  have hm : ∀ r ∈ b.workRegs, r ∈ b.allRegs := fun r hr =>
    List.mem_append_left _ (List.mem_append_right _ hr)
  refine ⟨hwf.no_sp _ (hm _ (by simp [WordRegBind.workRegs])),
    hwf.no_sp _ (hm _ (by simp [WordRegBind.workRegs])),
    hwf.no_sp _ (hm _ (by simp [WordRegBind.workRegs])),
    hwf.no_sp _ (hm _ (by simp [WordRegBind.workRegs]))⟩

theorem wordRegs_not_sp_ra {A : Arch} {b : WordRegBind A} (hwf : b.Wf) :
    (∀ r ∈ b.wordRegs, r ≠ A.abi.sp ∧ r ∉ A.abi.raRegs) ∧
    (∀ r ∈ b.wordRegs, r ≠ b.altRet ∧ r ≠ b.w0 ∧ r ≠ b.w1 ∧ r ≠ b.w2) := by
  refine ⟨fun r hr => ⟨hwf.no_sp r (List.mem_append_left _ (List.mem_append_left _ hr)),
      hwf.no_ra r (List.mem_append_left _ (List.mem_append_left _ hr))⟩,
    fun r hr => ?_⟩
  have h1 : ∀ lvl < 6, b.regAt lvl = r → r ≠ b.altRet ∧ r ≠ b.w0 ∧ r ≠ b.w1 ∧ r ≠ b.w2 :=
    fun lvl hl he => locOf_gpr_ne_work hwf 0 lvl (by simp [locOf, hl, he])
  simp only [WordRegBind.wordRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1 0 (by decide) rfl
  · exact h1 1 (by decide) rfl
  · exact h1 2 (by decide) rfl
  · exact h1 3 (by decide) rfl
  · exact h1 4 (by decide) rfl
  · exact h1 5 (by decide) rfl

theorem work_not_ra {A : Arch} {b : WordRegBind A} (hwf : b.Wf) :
    b.altRet ∉ A.abi.raRegs ∧ b.w0 ∉ A.abi.raRegs ∧
    b.w1 ∉ A.abi.raRegs ∧ b.w2 ∉ A.abi.raRegs := by
  have hm : ∀ r ∈ b.workRegs, r ∈ b.allRegs := fun r hr =>
    List.mem_append_left _ (List.mem_append_right _ hr)
  refine ⟨hwf.no_ra _ (hm _ (by simp [WordRegBind.workRegs])),
    hwf.no_ra _ (hm _ (by simp [WordRegBind.workRegs])),
    hwf.no_ra _ (hm _ (by simp [WordRegBind.workRegs])),
    hwf.no_ra _ (hm _ (by simp [WordRegBind.workRegs]))⟩

theorem wordRegs_nodup_6 {A : Arch} {b : WordRegBind A} (hwf : b.Wf) :
    b.sp ≠ b.rp ∧ b.sp ≠ b.rv ∧ b.sp ≠ b.r1 ∧ b.sp ≠ b.r2 ∧ b.sp ≠ b.r3 ∧
    b.rp ≠ b.rv ∧ b.rp ≠ b.r1 ∧ b.rp ≠ b.r2 ∧ b.rp ≠ b.r3 ∧
    b.rv ≠ b.r1 ∧ b.rv ≠ b.r2 ∧ b.rv ≠ b.r3 ∧
    b.r1 ≠ b.r2 ∧ b.r1 ≠ b.r3 ∧ b.r2 ≠ b.r3 := by
  have hnd := wordRegs_nodup hwf
  simp only [WordRegBind.wordRegs, List.nodup_cons, List.nodup_nil, List.mem_cons,
    List.not_mem_nil, or_false, not_or, not_false_eq_true, and_true] at hnd
  rcases hnd with ⟨⟨h01, h02, h03, h04, h05⟩, ⟨h12, h13, h14, h15⟩,
    ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45⟩
  exact ⟨h01, h02, h03, h04, h05, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩

theorem locOf_slot_lt {A : Arch} (b : WordRegBind A) (sb lvl d k : Nat)
    (hl : lvl < d) (hs : locOf b sb lvl = .slot k) :
    sb ≤ k ∧ k < sb + tempSpillCount b d := by
  dsimp only [locOf] at hs
  split at hs; · cases hs
  cases hg : b.tmps[lvl - 6]? <;> simp [hg] at hs
  have hlen : b.tmps.length ≤ lvl - 6 := List.getElem?_eq_none_iff.mp hg
  subst hs; simp only [tempSpillCount]; omega

theorem locOf_slot_ge_sb {A : Arch} (b : WordRegBind A) (sb lvl k : Nat)
    (hs : locOf b sb lvl = .slot k) : sb ≤ k := by
  dsimp only [locOf] at hs
  split at hs; · cases hs
  cases hg : b.tmps[lvl - 6]? <;> simp [hg] at hs
  omega

theorem wordRegsRel_setFlags {A : Arch} (b : WordRegBind A) (r : Regs) (s : MachSt A)
    (f : A.Flags) : WordRegsRel b r (s.setFlags f) ↔ WordRegsRel b r s := Iff.rfl

theorem wordRegsRel_setMem {A : Arch} (b : WordRegBind A) (r : Regs) (s : MachSt A)
    (m : Mem 64) : WordRegsRel b r (s.setMem m) ↔ WordRegsRel b r s := Iff.rfl

theorem wordRegsRel_setGpr_ne {A : Arch} (b : WordRegBind A) (r : Regs) (s : MachSt A)
    {q : A.Reg} (hq : ∀ w ∈ b.wordRegs, w ≠ q) (v : BitVec 64) :
    WordRegsRel b r (s.setGpr q v) ↔ WordRegsRel b r s := by
  simp only [WordRegsRel]
  rw [MachSt.gpr_setGpr_ne s v (hq b.sp (by simp [WordRegBind.wordRegs])),
    MachSt.gpr_setGpr_ne s v (hq b.rp (by simp [WordRegBind.wordRegs])),
    MachSt.gpr_setGpr_ne s v (hq b.rv (by simp [WordRegBind.wordRegs])),
    MachSt.gpr_setGpr_ne s v (hq b.r1 (by simp [WordRegBind.wordRegs])),
    MachSt.gpr_setGpr_ne s v (hq b.r2 (by simp [WordRegBind.wordRegs])),
    MachSt.gpr_setGpr_ne s v (hq b.r3 (by simp [WordRegBind.wordRegs]))]

theorem wordRegsRel_setGpr_work {A : Arch} {b : WordRegBind A} (hwf : b.Wf) (r : Regs)
    (s : MachSt A) {q : A.Reg} (hq : q ∈ b.workRegs ∨ q = A.abi.sp ∨ q ∈ A.abi.raRegs)
    (v : BitVec 64) :
    WordRegsRel b r (s.setGpr q v) ↔ WordRegsRel b r s := by
  refine wordRegsRel_setGpr_ne b r s (fun w hw he => ?_) v
  rcases hq with hwk | rfl | hra
  · have ⟨h0, h1, h2, h3⟩ := (wordRegs_not_sp_ra hwf).2 w hw
    simp only [WordRegBind.workRegs, List.mem_cons, List.not_mem_nil, or_false] at hwk
    rcases hwk with rfl | rfl | rfl | rfl <;>
      first | exact absurd he h0 | exact absurd he h1 | exact absurd he h2 | exact absurd he h3
  · exact (wordRegs_not_sp_ra hwf).1 w hw |>.1 he
  · exact (wordRegs_not_sp_ra hwf).1 w hw |>.2 (he ▸ hra)

theorem wordRegsRel_setGprW_work {A : Arch} {b : WordRegBind A} (hwf : b.Wf) (r : Regs)
    (s : MachSt A) (w : Width) {q : A.Reg}
    (hq : q ∈ b.workRegs ∨ q = A.abi.sp ∨ q ∈ A.abi.raRegs) (v : BitVec w.bits) :
    WordRegsRel b r (s.setGprW w q v) ↔ WordRegsRel b r s :=
  wordRegsRel_setGpr_work hwf r s hq _

theorem wordRegs_ne_locOf_ge6 {A : Arch} {b : WordRegBind A} (hwf : b.Wf) {sb lvl : Nat}
    (hge : 6 ≤ lvl) {rd : A.Reg} (hl : locOf b sb lvl = .gpr rd) {w : A.Reg}
    (hw : w ∈ b.wordRegs) : w ≠ rd := by
  intro he; subst he
  have hmem : ∃ l < 6, locOf b sb l = .gpr w := by
    simp only [WordRegBind.wordRegs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨3, by decide, rfl⟩
    · exact ⟨4, by decide, rfl⟩
    · exact ⟨5, by decide, rfl⟩
  obtain ⟨l, hl6, hlg⟩ := hmem
  have := locOf_gpr_inj hwf sb l lvl hlg hl; omega

theorem wordRegsRel_setGpr_ge6 {A : Arch} {b : WordRegBind A} (hwf : b.Wf) (r : Regs)
    (s : MachSt A) {sb lvl : Nat} (hge : 6 ≤ lvl) {rd : A.Reg} (hl : locOf b sb lvl = .gpr rd)
    (v : BitVec 64) :
    WordRegsRel b r (s.setGpr rd v) ↔ WordRegsRel b r s :=
  wordRegsRel_setGpr_ne b r s (fun _ hw => wordRegs_ne_locOf_ge6 hwf hge hl hw) v

theorem wordRegsRel_setGprW_ge6 {A : Arch} {b : WordRegBind A} (hwf : b.Wf) (r : Regs)
    (s : MachSt A) (w : Width) {sb lvl : Nat} (hge : 6 ≤ lvl) {rd : A.Reg}
    (hl : locOf b sb lvl = .gpr rd) (v : BitVec w.bits) :
    WordRegsRel b r (s.setGprW w rd v) ↔ WordRegsRel b r s :=
  wordRegsRel_setGpr_ge6 hwf r s hge hl _

theorem envRel_setFlags {A : Arch} (b : WordRegBind A) (sb d : Nat) (bvs : List ((t : Ty) × Val t))
    (s : MachSt A) (f : A.Flags) :
    EnvRel b sb d bvs (s.setFlags f) ↔ EnvRel b sb d bvs s := Iff.rfl

theorem envRel_map_loc {A : Arch} {b : WordRegBind A} {sb d : Nat}
    {bvs : List ((t : Ty) × Val t)} {s s' : MachSt A}
    (hstep : ∀ i < d, ∀ item, listGet? bvs i = some item →
      LocHolds s (locOf b sb (d - 1 - i)) item.1 item.2 →
      LocHolds s' (locOf b sb (d - 1 - i)) item.1 item.2)
    (he : EnvRel b sb d bvs s) : EnvRel b sb d bvs s' := by
  refine ⟨he.1, fun i hi => ?_⟩
  have hi' := he.2 i hi
  cases hg : listGet? bvs i with
  | none => simp [hg] at hi'
  | some item => simp only [hg] at hi' ⊢; exact hstep i hi item hg hi'

theorem envRel_setGpr_other {A : Arch} {b : WordRegBind A} {sb d : Nat}
    {bvs : List ((t : Ty) × Val t)} {s : MachSt A} {q : A.Reg} (v : BitVec 64)
    (hsp : A.abi.sp ≠ q) (hloc : ∀ lvl r, lvl < d → locOf b sb lvl = .gpr r → r ≠ q) :
    EnvRel b sb d bvs (s.setGpr q v) ↔ EnvRel b sb d bvs s := by
  have hgpr : ∀ s1 s2 : MachSt A,
      (∀ i < d, ∀ r, locOf b sb (d - 1 - i) = .gpr r → s2.gpr r = s1.gpr r) →
      s2.gpr A.abi.sp = s1.gpr A.abi.sp → s2.mem = s1.mem →
      EnvRel b sb d bvs s1 → EnvRel b sb d bvs s2 :=
    fun s1 s2 hr hsp' hm he => envRel_map_loc (fun i hi item _ h => by
      cases hl : locOf b sb (d - 1 - i) with
      | gpr r => simpa [LocHolds, hl, hr i hi r hl] using h
      | slot k => simpa [LocHolds, hl, hsp', hm] using h) he
  refine ⟨hgpr _ _ (fun i hi r hl => (MachSt.gpr_setGpr_ne s v (hloc _ r (by omega) hl)).symm)
      (MachSt.gpr_setGpr_ne s v hsp).symm rfl,
    hgpr _ _ (fun i hi r hl => MachSt.gpr_setGpr_ne s v (hloc _ r (by omega) hl))
      (MachSt.gpr_setGpr_ne s v hsp) rfl⟩

theorem envRel_setGpr_work {A : Arch} {b : WordRegBind A} (hwf : b.Wf) (sb d : Nat)
    (bvs : List ((t : Ty) × Val t)) (s : MachSt A) {q : A.Reg} (hq : q ∈ b.workRegs)
    (v : BitVec 64) :
    EnvRel b sb d bvs (s.setGpr q v) ↔ EnvRel b sb d bvs s := by
  refine envRel_setGpr_other v ?_ (fun lvl r _ hl he => ?_)
  · have ⟨h0, h1, h2, h3⟩ := work_not_sp hwf
    simp only [WordRegBind.workRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
      first | exact h0.symm | exact h1.symm | exact h2.symm | exact h3.symm
  · subst he
    have ⟨_, _, _, _⟩ := locOf_gpr_ne_work hwf sb lvl hl
    simp only [WordRegBind.workRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> contradiction

theorem envRel_setGprW_work {A : Arch} {b : WordRegBind A} (hwf : b.Wf) (sb d : Nat)
    (bvs : List ((t : Ty) × Val t)) (s : MachSt A) (w : Width) {q : A.Reg}
    (hq : q ∈ b.workRegs) (v : BitVec w.bits) :
    EnvRel b sb d bvs (s.setGprW w q v) ↔ EnvRel b sb d bvs s :=
  envRel_setGpr_work hwf sb d bvs s hq _

theorem envRel_setGpr_new {A : Arch} {b : WordRegBind A} (hwf : b.Wf) {sb d : Nat}
    {bvs : List ((t : Ty) × Val t)} {s : MachSt A} {rd : A.Reg} (hrd : locOf b sb d = .gpr rd)
    (v : BitVec 64) (he : EnvRel b sb d bvs s) :
    EnvRel b sb d bvs (s.setGpr rd v) :=
  (envRel_setGpr_other v (locOf_gpr_ne_sp hwf sb d hrd).symm fun lvl r hl hr e => by
    subst e; have := locOf_gpr_inj hwf sb lvl d hr hrd; omega).mpr he

theorem envRel_pushRegsV {A : Arch} {b : WordRegBind A} (sb : Nat) {r : Regs} {s : MachSt A}
    (hr : WordRegsRel b r s) : EnvRel b sb 6 (pushRegsV r.toRegsV) s := by
  rcases hr with ⟨hsp, hrp, hrv, hr1, hr2, hr3⟩
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ =>
    simp [pushRegsV, RegsV.toTup, Regs.toRegsV, pushTup, listGet?, locOf, WordRegBind.regAt,
      LocHolds, ValHolds64, hr3]
  | 1, _ =>
    simp [pushRegsV, RegsV.toTup, Regs.toRegsV, pushTup, listGet?, locOf, WordRegBind.regAt,
      LocHolds, ValHolds64, hr2]
  | 2, _ =>
    simp [pushRegsV, RegsV.toTup, Regs.toRegsV, pushTup, listGet?, locOf, WordRegBind.regAt,
      LocHolds, ValHolds64, hr1]
  | 3, _ =>
    simp [pushRegsV, RegsV.toTup, Regs.toRegsV, pushTup, listGet?, locOf, WordRegBind.regAt,
      LocHolds, ValHolds64, hrv]
  | 4, _ =>
    simp [pushRegsV, RegsV.toTup, Regs.toRegsV, pushTup, listGet?, locOf, WordRegBind.regAt,
      LocHolds, ValHolds64, hrp]
  | 5, _ =>
    simp [pushRegsV, RegsV.toTup, Regs.toRegsV, pushTup, listGet?, locOf, WordRegBind.regAt,
      LocHolds, ValHolds64, hsp]

theorem envRel_push1 {A : Arch} {b : WordRegBind A} {sb d : Nat}
    {bvs : List ((t : Ty) × Val t)} {s : MachSt A} {t : Ty} {v : Val t}
    (he : EnvRel b sb d bvs s) (hnew : LocHolds s (locOf b sb d) t v) :
    EnvRel b sb (d + 1) (⟨t, v⟩ :: bvs) s := by
  refine ⟨by simp [he.1], fun i hi => ?_⟩
  cases i with
  | zero => simpa [listGet?] using hnew
  | succ j =>
    have hj' := he.2 j (by omega)
    dsimp only [listGet?]
    rw [show d + 1 - 1 - (j + 1) = d - 1 - j by omega]
    exact hj'

theorem envRel_setSlot_ge {A : Arch} {b : WordRegBind A} {sb d ks : Nat}
    {bvs : List ((t : Ty) × Val t)} {s : MachSt A} {slots : List (BitVec 64)} {R : Mem 64 → Prop}
    (hk : ks < slots.length) (hks : ∀ lvl < d, locOf b sb lvl ≠ .slot ks)
    (hslots : ∀ lvl < d, ∀ j, locOf b sb lvl = .slot j → j < slots.length)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ R) s.mem)
    (v : BitVec 64) (he : EnvRel b sb d bvs s) :
    EnvRel b sb d bvs (s.setMem (storeMem s.mem i64
      (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ks)) v)) := by
  have hst := store_array64 v hk hm
  refine envRel_map_loc (fun i hi item _ h => ?_) he
  cases hl : locOf b sb (d - 1 - i) with
  | gpr r => simpa [LocHolds, hl] using h
  | slot j =>
    simp only [LocHolds, hl] at h ⊢
    obtain ⟨g, hld, hval⟩ := h
    have hj_ne : j ≠ ks := fun e => hks (d - 1 - i) (by omega) (by rw [hl, e])
    have hjlt : j < slots.length := hslots (d - 1 - i) (by omega) j hl
    have hload0 := loadVal_array64 hjlt hm
    rw [hload0] at hld; cases hld
    have hload1 := loadVal_array64 (i := j) (by simpa [List.length_set] using hjlt) hst.2
    rw [List.getElem_set_ne hj_ne.symm] at hload1
    exact ⟨_, by simpa using hload1, hval⟩

theorem envRel_setMem_of_array {A : Arch} {b : WordRegBind A} {sb d : Nat}
    {bvs : List ((t : Ty) × Val t)} {s : MachSt A} {slots : List (BitVec 64)}
    {m' : Mem 64} {R' : Mem 64 → Prop}
    (hslots : ∀ lvl < d, ∀ j, locOf b sb lvl = .slot j → j < slots.length)
    (hm1 : (array64 (s.gpr A.abi.sp) slots ⋆ R') s.mem)
    (hm2 : (array64 (s.gpr A.abi.sp) slots ⋆ R') m')
    (he : EnvRel b sb d bvs s) :
    EnvRel b sb d bvs (s.setMem m') := by
  refine envRel_map_loc (fun i hi item _ h => ?_) he
  cases hl : locOf b sb (d - 1 - i) with
  | gpr r => simpa [LocHolds, hl] using h
  | slot j =>
    simp only [LocHolds, hl] at h ⊢
    obtain ⟨g, hld, hval⟩ := h
    have hjlt := hslots (d - 1 - i) (by omega) j hl
    have h1 := loadVal_array64 hjlt hm1
    have h2 := loadVal_array64 hjlt hm2
    rw [h1] at hld; cases hld
    exact ⟨_, by simpa using h2, hval⟩

theorem envRel_slots_bound {A : Arch} (b : WordRegBind A) {sb d dMax nSlots : Nat}
    (hd : d ≤ dMax) (hn : sb + tempSpillCount b dMax ≤ nSlots) :
    ∀ lvl < d, ∀ j, locOf b sb lvl = .slot j → j < nSlots := by
  intro lvl hl j hj
  have ⟨_, hlt⟩ := locOf_slot_lt b sb lvl dMax j (Nat.lt_of_lt_of_le hl hd) hj
  omega

private theorem listGet?_some_lt {α : Type} : ∀ {xs : List α} {i : Nat} {a : α},
    listGet? xs i = some a → i < xs.length
  | [], _, _, h => by cases h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: xs, i + 1, _, h => Nat.succ_lt_succ (listGet?_some_lt h)

theorem envRel_get {A : Arch} {b : WordRegBind A} {sb d : Nat}
    {bvs : List ((t : Ty) × Val t)} {s : MachSt A} (he : EnvRel b sb d bvs s)
    {t : Ty} {idx : Nat} {v : Val t} (hden : denoteArg bvs (.var idx) = some (.var v)) :
    idx < d ∧ LocHolds s (locOf b sb (d - 1 - idx)) t v := by
  dsimp only [denoteArg, lookupV] at hden
  cases hg : listGet? bvs idx with
  | none => rw [hg] at hden; cases hden
  | some item =>
    have hlt : idx < bvs.length := listGet?_some_lt hg
    have hid : idx < d := by rw [← he.1]; exact hlt
    have hloc := he.2 idx hid
    rw [hg] at hloc; rcases item with ⟨t', v'⟩
    rw [hg] at hden; dsimp only at hden
    cases hc : castTy t' t v' with
    | none => rw [hc] at hden; cases hden
    | some v'' =>
      rw [hc] at hden; have hdv : v'' = v := by cases hden; rfl
      subst hdv
      cases t' with
      | bool => cases t with | bool => cases hc; exact ⟨hid, hloc⟩ | _ => cases hc
      | bits m =>
        cases t with
        | bits n =>
          dsimp only [castTy] at hc; split at hc
          · rename_i heq; subst heq; cases hc; exact ⟨hid, hloc⟩
          · cases hc
        | _ => cases hc
      | float _ | pair _ _ =>
        dsimp only [LocHolds, ValHolds64] at hloc
        cases hloc' : locOf b sb (d - 1 - idx) <;> simp [hloc'] at hloc

/-! ## §2. `bodyWp` Combinators, Stack-Slot `instrWp`, and Memory Helpers -/

theorem bodyWp_mono {A : Arch} {symAddr : Sym → BitVec 64} {K K' : MachSt A → Prop}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} (hK : ∀ s, K s → K' s) :
    ∀ {is : List (Instr A)} {s : MachSt A},
      bodyWp A symAddr is K Ψ H s → bodyWp A symAddr is K' Ψ H s
  | [], _, h => hK _ h
  | _ :: _, _, ⟨hex, hf, hj, hh⟩ => ⟨hex, fun _ hr => bodyWp_mono hK (hf _ hr), hj, hh⟩

theorem bodyWp_append {A : Arch} {symAddr : Sym → BitVec 64} {K : MachSt A → Prop}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} :
    ∀ (is₁ is₂ : List (Instr A)) (s : MachSt A),
      bodyWp A symAddr is₁ (bodyWp A symAddr is₂ K Ψ H) Ψ H s →
      bodyWp A symAddr (is₁ ++ is₂) K Ψ H s
  | [], _, _, h => h
  | _ :: _, is₂, _, ⟨hex, hf, hj, hh⟩ =>
    ⟨hex, fun _ hr => bodyWp_append _ is₂ _ (hf _ hr), hj, hh⟩

theorem instrWp_slotSt {A : Arch} {symAddr : Sym → BitVec 64} {i : Nat} {rs : A.Reg}
    {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A}
    (hst : storeOk s.mem i64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)))
    (hk : K (s.setMem (storeMem s.mem i64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)) (s.gpr rs)))) :
    instrWp A symAddr (.slotSt i rs) K Ψ H s :=
  instrWp_det (fun _ => by simp [instrRel, hst]) hk

theorem instrWp_slotLd {A : Arch} {symAddr : Sym → BitVec 64} {rd : A.Reg} {i : Nat}
    {v : BitVec 64} {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)}
    {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (hld : loadVal s.mem i64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)) = some v)
    (hk : K (s.setGpr rd v)) :
    instrWp A symAddr (.slotLd rd i) K Ψ H s :=
  instrWp_det (fun _ => by simp [instrRel, hld]) hk

theorem instrWp_prologue {A : Arch} (hwf : A.Wf) {symAddr : Sym → BitVec 64} {ns : Nat}
    {ra : BitVec 64} {G : Mem 64 → Prop} {K : MachSt A → Prop}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (hra : (vllFramePreds A).raReg s ra)
    (hbound : A.abi.frameSize ns ≤ 2 ^ 64)
    (hm : s.mem =⋆ (vllFramePreds A).RetAddr (s.gpr A.abi.sp) ra ⋆
      region (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns)) (A.abi.frameSize ns) ⋆ G)
    (hk : ∀ (slots : List (BitVec 64)), slots.length = ns →
      let sp' := s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns)
      ∀ m', (m' =⋆ array64 sp' slots ⋆
        (vllFramePreds A).Saved (s.gpr A.abi.sp) ra ns ⋆ G) →
        K (((s.setGpr A.abi.sp sp').setMem m').setFlags (A.prologueFlags ns s.flags))) :
    instrWp A symAddr (.prologue ns) K Ψ H s := by
  let sp' := s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns)
  have hslots_fit : 8 * ns ≤ 2 ^ 64 := Nat.le_trans (hwf.slots_le_frameSize ns) hbound
  cases hkind : A.abi.raKind with
  | stack =>
    have hsplit := region_frame_split (a := sp') (hwf.slots_le_frameSize ns) hbound
    simp only [vllFramePreds, hkind] at hm
    rw [hsplit] at hm
    have hm' : (region sp' (8 * ns) ⋆ (region (sp' + BitVec.ofNat 64 (8 * ns))
        (A.abi.frameSize ns - 8 * ns) ⋆ cell64 (s.gpr A.abi.sp) ra ⋆ G)) s.mem :=
      sep_cast hm (by ac_rfl)
    obtain ⟨slots, hs⟩ := sep_ex_l.mp (sep_mono (fun _ => region_array64 hslots_fit) hm')
    obtain ⟨hlen, harr⟩ := sep_pure_l.mp hs
    refine instrWp_det (fun _ => by simp only [instrRel, hkind]; rfl)
      (hk slots hlen s.mem ?_)
    simp only [vllFramePreds, hkind]
    exact sep_cast harr (by dsimp only [sp']; ac_rfl)
  | linkReg lr =>
    have hlr_le : 8 * ns + 8 ≤ A.abi.frameSize ns := hwf.linkReg_frameSize lr hkind ns
    have hlr_eq : s.gpr lr = ra := by simpa only [vllFramePreds, hkind] using hra
    have hsplit := region_frame_split_ra (a := sp') hlr_le hbound
    simp only [vllFramePreds, hkind] at hm
    rw [region_zero, emp_sep, hsplit] at hm
    have hm_focus : (region (sp' + BitVec.ofNat 64 (8 * ns)) 8 ⋆
        (region (sp' + BitVec.ofNat 64 (8 * ns) + 8#64) (A.abi.frameSize ns - 8 * ns - 8) ⋆
          (region sp' (8 * ns) ⋆ G))) s.mem :=
      sep_cast hm (by ac_rfl)
    obtain ⟨v0, hv0⟩ := region_sep_cell64 hm_focus
    obtain ⟨hst, hmem_st⟩ := store_cell64 (s.gpr lr) hv0
    rw [hlr_eq] at hmem_st
    have hm_reorg : (region sp' (8 * ns) ⋆
        ((cell64 (sp' + BitVec.ofNat 64 (8 * ns)) ra ⋆
          region (sp' + BitVec.ofNat 64 (8 * ns) + 8#64) (A.abi.frameSize ns - 8 * ns - 8)) ⋆ G))
        (storeMem s.mem i64 (sp' + BitVec.ofNat 64 (8 * ns)) ra) :=
      sep_cast hmem_st (by ac_rfl)
    obtain ⟨slots, hs⟩ := sep_ex_l.mp (sep_mono (fun _ => region_array64 hslots_fit) hm_reorg)
    obtain ⟨hlen, harr⟩ := sep_pure_l.mp hs
    have hm_arr : (storeMem s.mem i64 (sp' + BitVec.ofNat 64 (8 * ns)) (s.gpr lr) =⋆
        array64 sp' slots ⋆ (vllFramePreds A).Saved (s.gpr A.abi.sp) ra ns ⋆ G) := by
      rw [hlr_eq]; simp only [vllFramePreds, hkind]
      exact sep_cast harr (by dsimp only [sp']; ac_rfl)
    refine instrWp_det ?_ (hk slots hlen _ hm_arr)
    intro o; simp only [instrRel, hkind]
    exact ⟨fun h => h.2, fun h => ⟨hst, h⟩⟩

theorem instrWp_epilogue {A : Arch} (hwf : A.Wf) {symAddr : Sym → BitVec 64} {ns : Nat}
    {ra : BitVec 64} {slots : List (BitVec 64)} {G : Mem 64 → Prop} {K : MachSt A → Prop}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {s : MachSt A}
    (hlen : slots.length = ns) (hbound : A.abi.frameSize ns + A.abi.raBytes ≤ 2 ^ 64)
    (hm : s.mem =⋆ array64 (s.gpr A.abi.sp) slots ⋆
      (vllFramePreds A).Saved (s.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns)) ra ns ⋆ G)
    (hk : ∀ s',
      s'.gpr A.abi.sp = s.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns) →
      (vllFramePreds A).raReg s' ra →
      (∀ q, q ≠ A.abi.sp → q ∉ A.abi.raRegs → s'.gpr q = s.gpr q) →
      s'.mem = s.mem →
      (s'.mem =⋆ (vllFramePreds A).RetAddr (s'.gpr A.abi.sp) ra ⋆
        region (s'.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns))
          (A.abi.frameSize ns) ⋆ G) →
      K s') :
    instrWp A symAddr (.epilogue ns) K Ψ H s := by
  let sp' := s.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns)
  let f' := A.epilogueFlags ns s.flags
  have hcancel : sp' - BitVec.ofNat 64 (A.abi.frameSize ns) = s.gpr A.abi.sp :=
    BitVec.add_sub_cancel (s.gpr A.abi.sp) (BitVec.ofNat 64 (A.abi.frameSize ns))
  have hfsz : A.abi.frameSize ns ≤ 2 ^ 64 := by
    cases hkind : A.abi.raKind <;>
      simp only [Abi.raBytes, hkind, RaKind.raBytes] at hbound <;> omega
  have hslots_fit : 8 * ns ≤ 2 ^ 64 := Nat.le_trans (hwf.slots_le_frameSize ns) hfsz
  have hm_reg :
      (array64 (s.gpr A.abi.sp) slots ⋆ ((vllFramePreds A).Saved sp' ra ns ⋆ G)) s.mem := by
    rw [sep_assoc] at hm; exact hm
  have hm_slots :
      (region (s.gpr A.abi.sp) (8 * ns) ⋆ ((vllFramePreds A).Saved sp' ra ns ⋆ G)) s.mem :=
    sep_mono (fun _ => hlen ▸ array64_region (hlen ▸ hslots_fit)) hm_reg
  cases hkind : A.abi.raKind with
  | stack =>
    have hm_post : ((s.setGpr A.abi.sp sp').setFlags f').mem =⋆
        (vllFramePreds A).RetAddr ((s.setGpr A.abi.sp sp').setFlags f' |>.gpr A.abi.sp) ra ⋆
        region (((s.setGpr A.abi.sp sp').setFlags f' |>.gpr A.abi.sp) -
          BitVec.ofNat 64 (A.abi.frameSize ns)) (A.abi.frameSize ns) ⋆ G := by
      simp only [MachSt.mem_setFlags, MachSt.mem_setGpr, MachSt.gpr_setFlags,
        MachSt.gpr_setGpr_same, hcancel, vllFramePreds, hkind]
      have hsplit := region_frame_split (a := s.gpr A.abi.sp) (hwf.slots_le_frameSize ns) hfsz
      simp only [vllFramePreds, hkind, hcancel] at hm_slots
      rw [hsplit]; exact sep_cast hm_slots (by ac_rfl)
    refine instrWp_det (fun _ => by simp [instrRel, hkind, sp', f'])
      (hk ((s.setGpr A.abi.sp sp').setFlags f') (by simp [sp'])
        (by simp [vllFramePreds, hkind]) (fun q hq _ => by simp [MachSt.gpr_setGpr_ne _ _ hq])
        rfl hm_post)
  | linkReg lr =>
    have hlr_le : 8 * ns + 8 ≤ A.abi.frameSize ns := hwf.linkReg_frameSize lr hkind ns
    have hsp_ne_lr : A.abi.sp ≠ lr := by
      have hdisj := hwf.sp_disj.2.2.2.2.2
      simp only [Abi.raRegs, hkind, RaKind.raRegs, List.mem_singleton] at hdisj; exact hdisj
    simp only [vllFramePreds, hkind, hcancel] at hm_slots
    have hm_c : (cell64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns)) ra ⋆
        (region (s.gpr A.abi.sp) (8 * ns) ⋆
          (region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns) + 8#64)
            (A.abi.frameSize ns - 8 * ns - 8) ⋆ G))) s.mem :=
      sep_cast hm_slots (by ac_rfl)
    have hld : loadVal s.mem i64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns)) = some ra :=
      loadVal_cell64 hm_c
    have hm_reg2 : (region (s.gpr A.abi.sp) (8 * ns) ⋆
        (region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns)) 8 ⋆
          region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * ns) + 8#64)
            (A.abi.frameSize ns - 8 * ns - 8)) ⋆ G) s.mem :=
      sep_cast (sep_mono (fun _ => cell64_region) hm_c) (by ac_rfl)
    have hmerge := region_frame_split_ra (a := s.gpr A.abi.sp) hlr_le hfsz
    rw [← hmerge] at hm_reg2
    let s' := ((s.setGpr lr ra).setGpr A.abi.sp sp').setFlags f'
    have hm_post : s'.mem =⋆ (vllFramePreds A).RetAddr (s'.gpr A.abi.sp) ra ⋆
        region (s'.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns))
          (A.abi.frameSize ns) ⋆ G := by
      simp only [s', MachSt.mem_setFlags, MachSt.mem_setGpr, MachSt.gpr_setFlags,
        MachSt.gpr_setGpr_same, hcancel, vllFramePreds, hkind, region_zero, emp_sep]
      exact hm_reg2
    refine instrWp_det (fun _ => by simp [s', sp', f', instrRel, hkind, hld])
      (hk s' (by simp [s', sp']) ?_ ?_ rfl hm_post)
    · simp only [s', vllFramePreds, hkind, MachSt.gpr_setFlags,
        MachSt.gpr_setGpr_ne _ _ hsp_ne_lr.symm, MachSt.gpr_setGpr_same]
    · intro q hqsp hqra
      have hqlr : q ≠ lr := fun he => hqra (by simp [he, Abi.raRegs, hkind, RaKind.raRegs])
      simp only [s', MachSt.gpr_setFlags, MachSt.gpr_setGpr_ne _ _ hqsp,
        MachSt.gpr_setGpr_ne _ _ hqlr]

theorem hwStackMem_split {A : Arch} {sp0 ra : BitVec 64} {n1 n2 : Nat}
    (hle : n1 ≤ n2) (hbd : n2 + A.abi.raBytes ≤ 2 ^ 64) :
    hwStackMem A sp0 ra n2 =
      ((vllFramePreds A).RetAddr sp0 ra ⋆
        region (sp0 - BitVec.ofNat 64 n2) (n2 - n1) ⋆
        region (sp0 - BitVec.ofNat 64 n1) n1) := by
  have hn2 : n2 ≤ 2 ^ 64 := by omega
  have he : n2 = (n2 - n1) + n1 := by omega
  have hsp : sp0 - BitVec.ofNat 64 n2 + BitVec.ofNat 64 (n2 - n1) = sp0 - BitVec.ofNat 64 n1 := by
    apply BitVec.eq_of_toNat_eq; have hs := sp0.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  dsimp only [hwStackMem]
  conv => lhs; rhs; arg 2; rw [he]
  rw [region_split (by omega), hsp]
  ac_rfl

theorem region_sub_split {a : BitVec 64} {lo hi : Nat} (hle : lo ≤ hi) (hbd : hi ≤ 2 ^ 64) :
    region (a - BitVec.ofNat 64 hi) hi =
      (region (a - BitVec.ofNat 64 hi) (hi - lo) ⋆ region (a - BitVec.ofNat 64 lo) lo) := by
  have hsp : a - BitVec.ofNat 64 hi + BitVec.ofNat 64 (hi - lo) = a - BitVec.ofNat 64 lo := by
    apply BitVec.eq_of_toNat_eq; have ha := a.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have he : hi = (hi - lo) + lo := by omega
  conv => lhs; arg 2; rw [he]
  rw [region_split (by omega), hsp]

theorem loadVal_bits8_of_bool {m : Mem 64} {a : BitVec 64} {b : Bool}
    (h : loadVal m .bool a = some b) :
    loadVal m (.bits 8) a = some (BitVec.ofNat 8 b.toNat) := by
  simp only [loadVal, Ty.bytes, Ty.size] at h ⊢
  cases hi : m.loadInt a 1 with
  | none => rw [hi] at h; cases h
  | some i =>
    rw [hi] at h; dsimp only [Option.bind_some] at h ⊢
    split at h
    · rename_i hcond; cases h
      simp only [Option.some.injEq, ofBits]
      rcases (by simpa [beq_iff_eq] using hcond : i = 0 ∨ i = 1) with rfl | rfl <;> decide
    · cases h

theorem storeOk_bool_iff_bits8 (m : Mem 64) (a : BitVec 64) :
    storeOk m .bool a ↔ storeOk m (.bits 8) a := Iff.rfl

theorem storeMem_bits8_eq_bool (m : Mem 64) (a : BitVec 64) (b : Bool) :
    storeMem m (.bits 8) a (BitVec.ofNat 8 b.toNat) = storeMem m .bool a b := by
  dsimp only [storeMem]; cases b <;> rfl

/-! ## §3. Bitvector & `ValHolds64` Semantic Lemmas -/

theorem width_ofBits?_eq {n : Nat} {w : Width} (h : Width.ofBits? n = some w) : n = w.bits := by
  dsimp only [Width.ofBits?] at h
  split at h <;> cases h <;> rfl

theorem tyToWidth?_spec {t : Ty} {w : Width} (h : tyToWidth? t = some w) :
    (t = .bool ∧ w = .w8) ∨ (t = .bits w.bits) := by
  cases t with
  | bool => cases h; exact Or.inl ⟨rfl, rfl⟩
  | bits n => dsimp only [tyToWidth?] at h; rw [width_ofBits?_eq h]; exact Or.inr rfl
  | float _ | pair _ _ => cases h

theorem valHolds64_imm {t : Ty} {c : Val t} {g : BitVec 64} (h : immToBitVec64 t c = some g) :
    ValHolds64 t c g := by
  cases t with
  | bool => dsimp only [immToBitVec64] at h; cases h; cases c <;> simp [ValHolds64] <;> decide
  | bits n =>
    dsimp only [immToBitVec64] at h; split at h
    · rename_i hle; cases h
      refine ⟨hle, BitVec.eq_of_toNat_eq ?_⟩
      simp only [BitVec.toNat_setWidth]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le c.isLt (Nat.pow_le_pow_right (by decide) hle)),
        Nat.mod_eq_of_lt c.isLt]
    · cases h
  | float _ | pair _ _ => cases h

theorem valHolds64_bits_writeSub {A : Arch} (hwf : A.Wf) (w : Width) (old : BitVec 64)
    (v : BitVec w.bits) : ValHolds64 (.bits w.bits) v (A.writeSub w old v) :=
  ⟨w.bits_le_64, hwf.writeSub_setWidth w old v⟩

theorem valHolds64_bool_nonzero {b : Bool} {g : BitVec 64} (h : ValHolds64 .bool b g) :
    (g.setWidth 8 != 0#8) = b := by
  dsimp only [ValHolds64] at h; rw [h]; cases b <;> decide

theorem maskOfBits64_setWidth (w : Width) :
    (maskOfBits64 w.bits).setWidth w.bits = BitVec.allOnes w.bits := by
  cases w <;> decide

theorem normBoolCmp_eq (o : CmpOp) (a b : Bool) :
    (normBoolCmp o).evalBits (BitVec.ofNat 8 a.toNat) (BitVec.ofNat 8 b.toNat) =
      o.evalBool a b := by
  cases o <;> cases a <;> cases b <;> decide

theorem maskOfBits64_getLsbD (m i : Nat) (hm : m ≤ 64) (hi : i < 64) :
    (maskOfBits64 m).getLsbD i = decide (i < m) := by
  rcases Nat.eq_or_lt_of_le hm with rfl | hmlt
  · have h : maskOfBits64 64 = BitVec.allOnes 64 := by decide
    rw [h, BitVec.getLsbD_allOnes]
  · have hne : (m == 64) = false := beq_false_of_ne (by omega)
    dsimp only [maskOfBits64]; rw [ite_eq_right (by simp [hne])]
    have hlt : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hmlt
    have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
    have hsh : (1#64 <<< m).toNat = 2 ^ m := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      simp [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64), Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt]
    have hval : (1#64 <<< m - 1#64).toNat = 2 ^ m - 1 := by
      rw [BitVec.toNat_sub_of_le (by
        change (1#64 : BitVec 64).toNat ≤ (1#64 <<< m).toNat
        rw [hsh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64)]; exact hpos)]
      rw [hsh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64)]
    rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat, hval,
      Nat.testBit_two_pow_sub_one]

private theorem bitvec_one_getLsbD_succ (w k : Nat) (hk : k + 1 < w) :
    (BitVec.ofNat w 1).getLsbD (k + 1) = false := by
  rw [BitVec.getLsbD_eq_getElem hk, BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega)), Nat.testBit, Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero k))]
  decide

private theorem bv_ofBool_eq (n : Nat) (hn : n ≤ 64) (b : Bool) (g : BitVec 64)
    (hb : ValHolds64 .bool b g) :
    (g &&& 1#64).setWidth n = BitVec.ofNat n b.toNat := by
  have h8 : g.setWidth 8 = BitVec.ofNat 8 b.toNat := hb
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_and, hi,
    decide_true, Bool.true_and]
  cases i with
  | zero =>
    have h0 : g.getLsbD 0 = (g.setWidth 8).getLsbD 0 := by simp
    rw [h0, h8]; cases b
    · simp
    · change (1#8 : BitVec 8).getLsbD 0 = (BitVec.ofNat n 1).getLsbD 0
      rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      decide
  | succ k =>
    have h1 : (1#64 : BitVec 64).getLsbD (k + 1) = false :=
      bitvec_one_getLsbD_succ 64 k (by omega)
    rw [h1, Bool.and_false]
    cases b
    · simp
    · exact (bitvec_one_getLsbD_succ n k hi).symm

theorem bv64_zext_mask_clean {m n : Nat} (hm : m ≤ 64) (_hmn : m ≤ n) (hn : n ≤ 64)
    (g : BitVec 64) :
    (g &&& maskOfBits64 m).setWidth n = (g.setWidth m).setWidth n := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_and]
  rw [maskOfBits64_getLsbD m i hm (Nat.lt_of_lt_of_le hi hn)]
  by_cases him : i < m <;> simp [hi, him]

theorem bv64_sext_shl_ashr {m n : Nat} (hm0 : 0 < m) (hm : m < 64) (_hmn : m ≤ n) (hn : n ≤ 64)
    (g : BitVec 64) :
    let sh := BitVec.ofNat 64 (64 - m)
    ((g <<< (sh.toNat % 64)).sshiftRight (sh.toNat % 64)).setWidth n =
      (g.setWidth m).signExtend n := by
  intro sh
  have hsh : sh.toNat % 64 = 64 - m := by dsimp only [sh]; rw [BitVec.toNat_ofNat]; omega
  rw [hsh]
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  have hnot64 : ¬ (64 ≤ i) := by omega
  by_cases him : i < m
  · have hlt64 : 64 - m + i < 64 := by omega
    have hge2 : ¬ (64 - m + i < 64 - m) := by omega
    simp [him, hnot64, hlt64, hge2, show 64 - m + i - (64 - m) = i by omega]
  · have hge64 : ¬ (64 - m + i < 64) := by omega
    simp [him, hnot64, hge64, BitVec.msb_eq_getLsbD_last,
      show 64 - 1 < 64 by decide, show ¬ (64 - 1 < 64 - m) by omega,
      show 64 - 1 - (64 - m) = m - 1 by omega, show m - 1 < m by omega,
      show m - 1 < 64 by omega, BitVec.getLsbD_eq_getElem]

theorem bv64_select_mask_any (b : Bool) (c tVal fVal : BitVec 64)
    (hc : ValHolds64 .bool b c) :
    let mask : BitVec 64 := 0#64 - (c &&& 1#64)
    ((tVal &&& mask) ||| (fVal &&& (mask ^^^ 0xFFFFFFFFFFFFFFFF#64))) =
      if b then tVal else fVal := by
  have hc0 : (c &&& 1#64) = if b then 1#64 else 0#64 := by
    have h8 : c.setWidth 8 = BitVec.ofNat 8 b.toNat := hc
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and]
    cases i with
    | zero =>
      have h0 : c.getLsbD 0 = (c.setWidth 8).getLsbD 0 := by simp
      rw [h0, h8]; cases b <;> decide
    | succ k =>
      have h1 : (1#64 : BitVec 64).getLsbD (k + 1) = false :=
        bitvec_one_getLsbD_succ 64 k (by omega)
      rw [h1, Bool.and_false]
      cases b <;> simp [h1]
  dsimp only; rw [hc0]
  cases b
  · rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
    have hm0 : (0#64 - 0#64 : BitVec 64) = 0#64 := by decide
    have hxor : (0#64 ^^^ 0xFFFFFFFFFFFFFFFF#64 : BitVec 64) = BitVec.allOnes 64 := by decide
    rw [hm0, hxor, BitVec.and_zero, BitVec.and_allOnes, BitVec.zero_or]
  · rw [ite_eq_left rfl, ite_eq_left rfl]
    have hall : (0#64 - 1#64 : BitVec 64) = BitVec.allOnes 64 := by decide
    have hxor : (BitVec.allOnes 64 ^^^ 0xFFFFFFFFFFFFFFFF#64 : BitVec 64) = 0#64 := by decide
    rw [hall, hxor, BitVec.and_allOnes, BitVec.and_zero, BitVec.or_zero]

/-! ## §4. Operand Loading, `emitToLoc`, and Parallel Move (`parMove`, `emitNextRegs`) -/

private theorem denoteArg_var_eq {bvs : List ((u : Ty) × Val u)} {t : Ty} {idx : Nat}
    {a' : Arg Val t} (h : denoteArg bvs (.var idx) = some a') :
    ∃ v : Val t, a' = .var v := by
  dsimp only [denoteArg] at h
  cases hl : lookupV bvs t idx <;> simp [hl] at h
  cases h; exact ⟨_, rfl⟩

def SrcValMatch {A : Arch} (gpr : A.Reg → BitVec 64) (sr : Src A) : (t : Ty) → Val t → Prop
  | .bool, bv => sr.evalW .w8 gpr = BitVec.ofNat 8 bv.toNat
  | .bits n, bv => ∀ w : Width, (hw : n = w.bits) → sr.evalW w gpr = bv.cast hw
  | _, _ => False

private theorem src_match_valHolds {A : Arch} {t : Ty} {v : Val t} {g : BitVec 64}
    {sr : Src A} {gpr : A.Reg → BitVec 64} (hev : sr.eval gpr = g) (hv : ValHolds64 t v g) :
    SrcValMatch gpr sr t v := by
  cases t with
  | bool => simpa [SrcValMatch, Src.evalW, hev, ValHolds64] using hv
  | bits n => intro w hw; subst hw; simpa [SrcValMatch, Src.evalW, hev, ValHolds64] using hv.2
  | float _ | pair _ _ => cases hv

theorem loadArgToGpr_bodyWp {A : Arch} {b : WordRegBind A} (hwf : b.Wf) {symAddr : Sym → BitVec 64}
    {sb d : Nat} {tmp : A.Reg} {t : Ty} {a : Arg K t} {bvs : List ((u : Ty) × Val u)}
    {a' : Arg Val t} {s : MachSt A} {slots : List (BitVec 64)} {G : Mem 64 → Prop}
    {Kpost : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {is : List (Instr A)} {rg : A.Reg}
    (htmp : tmp ∈ b.workRegs)
    (he : EnvRel b sb d bvs s)
    (hden : denoteArg bvs a = some a')
    (_hm : s.mem =⋆ array64 (s.gpr A.abi.sp) slots ⋆ G)
    (hlo : loadArgToGpr b sb d tmp a = .ok (is, rg))
    (hk : ∀ s',
      (∀ q, q ≠ tmp → s'.gpr q = s.gpr q) →
      ValHolds64 t a'.val (s'.gpr rg) →
      s'.mem = s.mem →
      EnvRel b sb d bvs s' →
      Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  cases a with
  | imm c =>
    cases hden; dsimp only [loadArgToGpr] at hlo
    cases him : immToBitVec64 t c with
    | none => simp [him] at hlo
    | some v =>
      simp only [him, Except.ok.injEq, Prod.mk.injEq] at hlo
      obtain ⟨rfl, rfl⟩ := hlo
      refine instrWp_movi (hk _ (fun q hq => MachSt.gpr_setGpr_ne s v hq) ?_ rfl
        ((envRel_setGpr_work hwf sb d bvs s htmp v).mpr he))
      simpa only [MachSt.gpr_setGpr_same, Arg.val] using valHolds64_imm him
  | var idx =>
    obtain ⟨v, rfl⟩ := denoteArg_var_eq hden
    dsimp only [loadArgToGpr] at hlo; split at hlo
    · obtain ⟨_, hloc⟩ := envRel_get he hden
      cases hl : locOf b sb (d - 1 - idx) with
      | gpr r =>
        simp only [hl, Except.ok.injEq, Prod.mk.injEq] at hlo
        obtain ⟨rfl, rfl⟩ := hlo; dsimp only [LocHolds] at hloc; rw [hl] at hloc
        exact hk s (fun _ _ => rfl) hloc rfl he
      | slot k =>
        simp only [hl, Except.ok.injEq, Prod.mk.injEq] at hlo
        obtain ⟨rfl, rfl⟩ := hlo; dsimp only [LocHolds] at hloc; rw [hl] at hloc
        obtain ⟨g, hld, hval⟩ := hloc
        refine instrWp_slotLd hld (hk _ (fun q hq => MachSt.gpr_setGpr_ne s g hq) ?_ rfl
          ((envRel_setGpr_work hwf sb d bvs s htmp g).mpr he))
        simpa only [MachSt.gpr_setGpr_same, Arg.val] using hval
    · cases hlo

theorem loadArgInto_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d : Nat} {dst : A.Reg} {t : Ty} {a : Arg K t}
    {bvs : List ((u : Ty) × Val u)} {a' : Arg Val t} {s : MachSt A} {slots : List (BitVec 64)}
    {G : Mem 64 → Prop} {Kpost : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)}
    {H : Xcap.Halt (MachSt A)} {is : List (Instr A)}
    (hdst : dst ∈ b.workRegs)
    (he : EnvRel b sb d bvs s)
    (hden : denoteArg bvs a = some a')
    (_hm : s.mem =⋆ array64 (s.gpr A.abi.sp) slots ⋆ G)
    (hlo : loadArgInto b sb d dst a = .ok is)
    (hk : ∀ s',
      (∀ q, q ≠ dst → s'.gpr q = s.gpr q) →
      ValHolds64 t a'.val (s'.gpr dst) →
      s'.mem = s.mem →
      EnvRel b sb d bvs s' →
      Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  cases a with
  | imm c =>
    cases hden; dsimp only [loadArgInto] at hlo
    cases him : immToBitVec64 t c with
    | none => simp [him] at hlo
    | some v =>
      simp only [him, Except.ok.injEq] at hlo; subst hlo
      refine instrWp_movi (hk _ (fun q hq => MachSt.gpr_setGpr_ne s v hq) ?_ rfl
        ((envRel_setGpr_work hwf sb d bvs s hdst v).mpr he))
      simpa only [MachSt.gpr_setGpr_same, Arg.val] using valHolds64_imm him
  | var idx =>
    obtain ⟨v, rfl⟩ := denoteArg_var_eq hden
    dsimp only [loadArgInto] at hlo; split at hlo
    · obtain ⟨_, hloc⟩ := envRel_get he hden
      cases hl : locOf b sb (d - 1 - idx) with
      | gpr r =>
        dsimp only [LocHolds] at hloc; rw [hl] at hloc
        simp only [hl] at hlo
        by_cases hrd : r = dst
        · subst hrd; simp only [beq_self_eq_true, ↓reduceIte, Except.ok.injEq] at hlo; subst hlo
          exact hk s (fun _ _ => rfl) hloc rfl he
        · have hne : (r == dst) = false := beq_false_of_ne hrd
          simp only [hne, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hlo; subst hlo
          refine instrWp_mov (hk _ (fun q hq => MachSt.gpr_setGprW_ne s .w64 _ hq) ?_ rfl
            ((envRel_setGprW_work hwf sb d bvs s .w64 hdst _).mpr he))
          simpa only [MachSt.gpr_setGprW_same, hawf.writeSub_w64, BitVec.setWidth_eq, Arg.val]
            using hloc
      | slot k =>
        simp only [hl, Except.ok.injEq] at hlo; subst hlo
        dsimp only [LocHolds] at hloc; rw [hl] at hloc
        obtain ⟨g, hld, hval⟩ := hloc
        refine instrWp_slotLd hld (hk _ (fun q hq => MachSt.gpr_setGpr_ne s g hq) ?_ rfl
          ((envRel_setGpr_work hwf sb d bvs s hdst g).mpr he))
        simpa only [MachSt.gpr_setGpr_same, Arg.val] using hval
    · cases hlo

theorem argToSrc_bodyWp {A : Arch} {b : WordRegBind A} (hwf : b.Wf) {symAddr : Sym → BitVec 64}
    {sb d : Nat} {tmp : A.Reg} {t : Ty} {a : Arg K t} {bvs : List ((u : Ty) × Val u)}
    {a' : Arg Val t} {s : MachSt A} {Kpost : MachSt A → Prop}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {is : List (Instr A)} {src : Src A}
    (htmp : tmp ∈ b.workRegs)
    (he : EnvRel b sb d bvs s)
    (hden : denoteArg bvs a = some a')
    (hlo : argToSrc b sb d tmp a = .ok (is, src))
    (hk : ∀ s',
      (∀ q, q ≠ tmp → s'.gpr q = s.gpr q) →
      SrcValMatch s'.gpr src t a'.val →
      s'.mem = s.mem →
      EnvRel b sb d bvs s' →
      Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  cases a with
  | imm c =>
    cases hden; dsimp only [argToSrc] at hlo
    cases him : immToBitVec64 t c with
    | none => simp [him] at hlo
    | some v =>
      simp only [him, Except.ok.injEq, Prod.mk.injEq] at hlo
      obtain ⟨rfl, rfl⟩ := hlo
      exact hk s (fun _ _ => rfl)
        (src_match_valHolds (gpr := s.gpr) (sr := .imm v) rfl (valHolds64_imm him)) rfl he
  | var idx =>
    obtain ⟨v, rfl⟩ := denoteArg_var_eq hden
    dsimp only [argToSrc] at hlo; split at hlo
    · obtain ⟨_, hloc⟩ := envRel_get he hden
      cases hl : locOf b sb (d - 1 - idx) with
      | gpr r =>
        simp only [hl, Except.ok.injEq, Prod.mk.injEq] at hlo
        obtain ⟨rfl, rfl⟩ := hlo; dsimp only [LocHolds] at hloc; rw [hl] at hloc
        exact hk s (fun _ _ => rfl)
          (src_match_valHolds (gpr := s.gpr) (sr := .reg r) rfl hloc) rfl he
      | slot k =>
        simp only [hl, Except.ok.injEq, Prod.mk.injEq] at hlo
        obtain ⟨rfl, rfl⟩ := hlo; dsimp only [LocHolds] at hloc; rw [hl] at hloc
        obtain ⟨g, hld, hval⟩ := hloc
        refine instrWp_slotLd hld (hk _ (fun q hq => MachSt.gpr_setGpr_ne s g hq)
          (src_match_valHolds (gpr := (s.setGpr tmp g).gpr) (sr := .reg tmp)
            (MachSt.gpr_setGpr_same s tmp g) hval) rfl
          ((envRel_setGpr_work hwf sb d bvs s htmp g).mpr he))
    · cases hlo

theorem emitToLoc_bodyWp {A : Arch} {b : WordRegBind A} (hwf : b.Wf) {symAddr : Sym → BitVec 64}
    {sb d dMax : Nat} {t : Ty} {v : Val t} {bvs : List ((u : Ty) × Val u)}
    {rw : Regs} {slots : List (BitVec 64)} {G : Mem 64 → Prop} {s : MachSt A}
    {build : A.Reg → List (Instr A)}
    {Kpost : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    (hd : d < dMax) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (hbuild_gpr : ∀ rd, locOf b sb d = .gpr rd →
      bodyWp A symAddr (build rd) (fun s' =>
        ValHolds64 t v (s'.gpr rd) ∧
        s'.gpr A.abi.sp = s.gpr A.abi.sp ∧
        EnvRel b sb d bvs s' ∧
        WordRegsRel b rw s' ∧
        ∃ slots' : List (BitVec 64), slots'.length = slots.length ∧
          (∀ j < sb, slots'[j]? = slots[j]?) ∧
          (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem) Ψ H s)
    (hbuild_slot : ∀ k, locOf b sb d = .slot k →
      bodyWp A symAddr (build b.w0) (fun s' =>
        ValHolds64 t v (s'.gpr b.w0) ∧
        s'.gpr A.abi.sp = s.gpr A.abi.sp ∧
        EnvRel b sb d bvs s' ∧
        WordRegsRel b rw s' ∧
        ∃ slots' : List (BitVec 64), slots'.length = slots.length ∧
          (∀ j < sb, slots'[j]? = slots[j]?) ∧
          (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem) Ψ H s)
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length →
      (∀ j < sb, slots'[j]? = slots[j]?) →
      EnvRel b sb (d + 1) (⟨t, v⟩ :: bvs) s' →
      WordRegsRel b rw s' →
      s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem →
      Kpost s') :
    bodyWp A symAddr (emitToLoc b.w0 (locOf b sb d) build) Kpost Ψ H s := by
  dsimp only [emitToLoc]
  cases hloc : locOf b sb d with
  | gpr rd =>
    refine bodyWp_mono ?_ (hbuild_gpr rd hloc)
    rintro s' ⟨hv, hsp, he', hr', slots', hlen', hsb', hm'⟩
    exact hk s' slots' hlen' hsb' (envRel_push1 he' (by simpa [LocHolds, hloc] using hv))
      hr' hsp hm'
  | slot k =>
    refine bodyWp_append _ _ _ (bodyWp_mono ?_ (hbuild_slot k hloc))
    rintro s' ⟨hv, hsp, he', hr', slots', hlen', hsb', hm'⟩
    have hlt : k < slots'.length := by
      have ⟨_, hlt0⟩ := locOf_slot_lt b sb d dMax k hd hloc; omega
    have hks : ∀ lvl < d, locOf b sb lvl ≠ .slot k := fun lvl hl heq => by
      have := locOf_inj hwf sb lvl d (heq.trans hloc.symm); omega
    have hsl : ∀ lvl < d, ∀ j, locOf b sb lvl = .slot j → j < slots'.length :=
      envRel_slots_bound b (Nat.le_of_lt hd) (by omega)
    have hst := store_array64 (s'.gpr b.w0) hlt hm'
    refine instrWp_slotSt hst.1 ?_
    refine hk _ (slots'.set k (s'.gpr b.w0)) (by simpa [List.length_set] using hlen') ?_ ?_
      ((wordRegsRel_setMem _ _ _ _).mpr hr') hsp ?_
    · intro j hj
      have hge : sb ≤ k := locOf_slot_ge_sb b sb d k hloc
      rw [List.getElem?_set_ne (by omega)]; exact hsb' j hj
    · refine envRel_push1 (envRel_setSlot_ge hlt hks hsl hm' (s'.gpr b.w0) he') ?_
      simp only [LocHolds, hloc]
      have hld := loadVal_array64 (i := k) (by simpa [List.length_set] using hlt) hst.2
      rw [List.getElem_set_self (by simp; exact hlt)] at hld
      exact ⟨s'.gpr b.w0, by simpa using hld, hv⟩
    · simpa [MachSt.mem_setMem] using hst.2

/-! ### Cycle-Breaking Parallel Move (`parMove`, `emitNextRegs`) -/

private theorem length_filter_lt_of_mem {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (hx : x ∈ xs) (hpx : p x = false) : (xs.filter p).length < xs.length := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.filter]; cases hy : p y <;> simp only [List.length_cons]
    · exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · rcases List.mem_cons.mp hx with rfl | hmem
      · rw [hpx] at hy; cases hy
      · exact Nat.succ_lt_succ (ih hmem)

private theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hmem : x ∈ ys := hsub x List.mem_cons_self
    have ih := nodup_length_le_of_subset hnd.2 (xs := xs) (ys := ys.erase x) fun y hy =>
      List.mem_erase_of_ne (fun e => hnd.1 (by subst e; exact hy)) |>.mpr
        (hsub y (List.mem_cons_of_mem _ hy))
    have := List.length_erase_of_mem hmem
    have hpos : 0 < ys.length := List.length_pos_of_mem hmem
    simp only [List.length_cons]; omega

private def moveRegsRead {A : Arch} (moves : List (A.Reg × ParSrc A)) : List A.Reg :=
  moves.filterMap fun p => match p.2 with | .reg r => some r | _ => none

private theorem mem_moveRegsRead {A : Arch} [DecidableEq A.Reg] {r : A.Reg}
    {moves : List (A.Reg × ParSrc A)} :
    isReadIn r moves = true ↔ r ∈ moveRegsRead moves := by
  induction moves with
  | nil => simp [isReadIn, moveRegsRead]
  | cons p ps ih =>
    have h1 : isReadIn r (p :: ps) =
        ((match p.2 with | .reg s => s == r | _ => false) || isReadIn r ps) := rfl
    have h2 : moveRegsRead (p :: ps) =
        (match p.2 with | .reg s => s :: moveRegsRead ps | _ => moveRegsRead ps) := by
      cases hs : p.2 <;> simp [moveRegsRead, hs]
    rw [h1, h2, Bool.or_eq_true]
    cases hs : p.2 with
    | reg s =>
      simp only [List.mem_cons, beq_iff_eq]
      rw [ih]; exact ⟨Or.imp_left Eq.symm, Or.imp_left Eq.symm⟩
    | slot _ | imm _ => simp [ih]

private theorem length_moveRegsRead_le {A : Arch} (moves : List (A.Reg × ParSrc A)) :
    (moveRegsRead moves).length ≤ moves.length := by
  induction moves with
  | nil => simp [moveRegsRead]
  | cons p ps ih =>
    have h2 : moveRegsRead (p :: ps) =
        (match p.2 with | .reg s => s :: moveRegsRead ps | _ => moveRegsRead ps) := by
      cases hs : p.2 <;> simp [moveRegsRead, hs]
    rw [h2]; cases p.2 <;> simp <;> omega

private theorem parMove_all_read_in_dests {A : Arch} [DecidableEq A.Reg]
    {m : A.Reg × ParSrc A} {ms : List (A.Reg × ParSrc A)}
    (hnd : ((m :: ms).map Prod.fst).Nodup)
    (hfind : (m :: ms).find? (fun p => !isReadIn p.1 (m :: ms)) = none) :
    (∃ r, m.2 = .reg r) ∧ ∀ p ∈ m :: ms, ∀ r, p.2 = .reg r → r ∈ (m :: ms).map Prod.fst := by
  let dests := (m :: ms).map Prod.fst
  have hall : ∀ p ∈ m :: ms, isReadIn p.1 (m :: ms) = true := fun p hp => by
    have hno := List.find?_eq_none.mp hfind p hp
    cases hr : isReadIn p.1 (m :: ms) <;> simp [hr] at hno ⊢
  have hsub : ∀ d ∈ dests, d ∈ moveRegsRead (m :: ms) := fun d hd => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
    exact mem_moveRegsRead.mp (hall p hp)
  let inD := (moveRegsRead (m :: ms)).filter dests.contains
  have hsubD : ∀ d ∈ dests, d ∈ inD := fun d hd =>
    List.mem_filter.mpr ⟨hsub d hd, List.contains_iff_mem.mpr hd⟩
  have hle1 : dests.length ≤ inD.length := nodup_length_le_of_subset hnd hsubD
  have hle2 : inD.length ≤ (moveRegsRead (m :: ms)).length := List.length_filter_le _ _
  have hle3 : (moveRegsRead (m :: ms)).length ≤ (m :: ms).length := length_moveRegsRead_le _
  have hdl : dests.length = (m :: ms).length := List.length_map _
  have hm_eq : (moveRegsRead (m :: ms)).length = (m :: ms).length := by omega
  have hin_eq : inD.length = (moveRegsRead (m :: ms)).length := by omega
  constructor
  · cases hm2 : m.2 with
    | reg r => exact ⟨r, rfl⟩
    | slot _ | imm _ =>
      exfalso
      have hlt : (moveRegsRead (m :: ms)).length < (m :: ms).length := by
        simp only [moveRegsRead, List.filterMap_cons, hm2, List.length_cons]
        exact Nat.lt_succ_of_le (length_moveRegsRead_le ms)
      omega
  · intro p hp r hr
    have hmr : r ∈ moveRegsRead (m :: ms) :=
      mem_moveRegsRead.mp (List.any_eq_true.mpr ⟨p, hp, by simp [hr]⟩)
    by_cases hmem : r ∈ dests
    · exact hmem
    · exfalso
      have hf : dests.contains r = false :=
        Bool.eq_false_iff.mpr (fun hc => hmem (List.contains_iff_mem.mp hc))
      have hlt := length_filter_lt_of_mem hmr hf
      dsimp only [inD] at hin_eq; omega

private theorem dropSelfMoves_mem {A : Arch} [DecidableEq A.Reg]
    {moves : List (A.Reg × ParSrc A)} {p : A.Reg × ParSrc A} :
    p ∈ dropSelfMoves moves → p ∈ moves := fun h => (List.mem_filter.mp h).1

private theorem dropSelfMoves_noself {A : Arch} [DecidableEq A.Reg]
    {moves : List (A.Reg × ParSrc A)} {p : A.Reg × ParSrc A}
    (hp : p ∈ dropSelfMoves moves) : ∀ r, p.2 = .reg r → p.1 ≠ r := fun r hr => by
  have hf := (List.mem_filter.mp hp).2; rw [hr] at hf; exact bne_iff_ne.mp hf

private theorem nodup_filter_fst {α β : Type} (p : α × β → Bool) {xs : List (α × β)}
    (hnd : (xs.map Prod.fst).Nodup) : ((xs.filter p).map Prod.fst).Nodup :=
  hnd.sublist (List.Sublist.map _ (List.filter_sublist))

private theorem nodup_map_subst {A : Arch} [DecidableEq A.Reg] (d tmp : A.Reg)
    {ms : List (A.Reg × ParSrc A)} (hnd : (ms.map Prod.fst).Nodup) :
    ((ms.map (fun p => (p.1, p.2.substReg d tmp))).map Prod.fst).Nodup := by
  simpa [List.map_map, Function.comp_def] using hnd

def evalParSrc {A : Arch} (slots : List (BitVec 64))
    (s : MachSt A) : ParSrc A → Option (BitVec 64)
  | .reg r => some (s.gpr r)
  | .slot k => slots[k]?
  | .imm v => some v

private theorem evalParSrc_subst_ne {A : Arch} [DecidableEq A.Reg]
    (slots : List (BitVec 64)) (s s' : MachSt A) (d tmp : A.Reg)
    (htmp : s'.gpr tmp = s.gpr d) (hrest : ∀ q, q ≠ d → q ≠ tmp → s'.gpr q = s.gpr q)
    (src : ParSrc A) (hs_ntmp : src ≠ .reg tmp) :
    evalParSrc slots s' (src.substReg d tmp) = evalParSrc slots s src := by
  cases src with
  | slot _ | imm _ => rfl
  | reg r =>
    dsimp only [ParSrc.substReg]
    by_cases hrd : r = d
    · subst hrd; simp [evalParSrc, htmp]
    · simp [hrd, evalParSrc, hrest r hrd (fun h => hs_ntmp (by rw [h]))]

private theorem emitParOne_bodyWp {A : Arch} (hwf : A.Wf) {symAddr : Sym → BitVec 64}
    {hwSp : BitVec 64} {slots : List (BitVec 64)} {G : Mem 64 → Prop}
    {s : MachSt A} {d : A.Reg} {sv : ParSrc A} {v : BitVec 64}
    {Kpost : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    (hsp : s.gpr A.abi.sp = hwSp)
    (hm : (array64 hwSp slots ⋆ G) s.mem)
    (hev : evalParSrc slots s sv = some v)
    (hk : ∀ s', s'.gpr d = v → (∀ q, q ≠ d → s'.gpr q = s.gpr q) → s'.mem = s.mem → Kpost s') :
    bodyWp A symAddr (emitParOne d sv) Kpost Ψ H s := by
  cases sv with
  | reg r =>
    simp only [evalParSrc, Option.some.injEq] at hev; dsimp only [emitParOne]
    by_cases hrd : r = d
    · subst hrd; simp only [↓reduceIte]; exact hk s hev (fun _ _ => rfl) rfl
    · simp only [hrd, ↓reduceIte]
      refine instrWp_mov (hk _ ?_ (fun q hq => MachSt.gpr_setGprW_ne s .w64 _ hq) rfl)
      simpa only [MachSt.gpr_setGprW_same, hwf.writeSub_w64, BitVec.setWidth_eq] using hev
  | slot k =>
    dsimp only [evalParSrc] at hev
    have hklt : k < slots.length := (List.getElem?_eq_some_iff.mp hev).1
    have hkval : slots[k] = v := (List.getElem?_eq_some_iff.mp hev).2
    have hld := loadVal_array64 hklt hm; rw [← hsp, hkval] at hld
    dsimp only [emitParOne]
    exact instrWp_slotLd hld
      (hk _ (MachSt.gpr_setGpr_same _ _ _) (fun q hq => MachSt.gpr_setGpr_ne _ _ hq) rfl)
  | imm c =>
    simp only [evalParSrc, Option.some.injEq] at hev; dsimp only [emitParOne]
    exact instrWp_movi (hk _ (by simpa only [MachSt.gpr_setGpr_same] using hev)
      (fun q hq => MachSt.gpr_setGpr_ne _ _ hq) rfl)

theorem parMoveAux_bodyWp {A : Arch} (hwf : A.Wf) {symAddr : Sym → BitVec 64}
    {dests : List A.Reg} {tmp : A.Reg} {hwSp : BitVec 64} {slots : List (BitVec 64)}
    {G : Mem 64 → Prop} {finalVal : A.Reg → BitVec 64} {Ψ : Xcap.CodeSpec (MachSt A)}
    {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (htmp : ∀ d ∈ dests, d ≠ tmp) (hd_sp : ∀ d ∈ dests, d ≠ A.abi.sp) (htmp_sp : tmp ≠ A.abi.sp) :
    ∀ (fuel : Nat) (moves : List (A.Reg × ParSrc A)) (s : MachSt A),
      moves.length ≤ fuel →
      (moves.map Prod.fst).Nodup →
      (∀ p ∈ moves, p.1 ∈ dests) →
      (∀ p ∈ moves, ∀ r, p.2 = .reg r → p.1 ≠ r) →
      s.gpr A.abi.sp = hwSp →
      (array64 hwSp slots ⋆ G) s.mem →
      (∀ d ∈ dests, (∀ p ∈ moves, p.1 ≠ d) → s.gpr d = finalVal d) →
      (∀ p ∈ moves, evalParSrc slots s p.2 = some (finalVal p.1)) →
      (∀ s',
        (∀ d ∈ dests, s'.gpr d = finalVal d) →
        (∀ q, q ∉ dests → q ≠ tmp → s'.gpr q = s.gpr q) →
        s'.mem = s.mem →
        Kpost s') →
      bodyWp A symAddr (parMoveAux tmp fuel moves) Kpost Ψ H s
  | fuel, [], s, _, _, _, _, _, _, hdone, _, hk => by
    cases fuel <;> exact hk s (fun d hd => hdone d hd (fun _ hm => by cases hm))
      (fun _ _ _ => rfl) rfl
  | 0, _ :: _, _, hle, _, _, _, _, _, _, _, _ => by simp at hle
  | fuel + 1, m :: ms, s, hle, hnd, hsub, hns, hsp, hm, hdone, hev, hk => by
    dsimp only [parMoveAux]
    cases hfind : (m :: ms).find? (fun p => !isReadIn p.1 (m :: ms)) with
    | some p =>
      rcases p with ⟨d, sv⟩
      have hpmem : (d, sv) ∈ m :: ms := List.mem_of_find?_eq_some hfind
      have hpread : isReadIn d (m :: ms) = false := by simpa using List.find?_some hfind
      have hddest : d ∈ dests := hsub (d, sv) hpmem
      have hev_d := hev (d, sv) hpmem
      let ms' := dropSelfMoves ((m :: ms).filter (fun p => p.1 != d))
      have hlen_lt : ms'.length < (m :: ms).length :=
        Nat.lt_of_le_of_lt (List.length_filter_le _ _) (length_filter_lt_of_mem hpmem (by simp))
      refine bodyWp_append _ _ _ (emitParOne_bodyWp hwf hsp hm hev_d ?_)
      intro s1 hs1d hs1_ne hs1m
      refine parMoveAux_bodyWp hwf htmp hd_sp htmp_sp (finalVal := finalVal) fuel ms' s1
        (by omega) (nodup_filter_fst _ (nodup_filter_fst _ hnd))
        (fun q hq => hsub q (List.mem_filter.mp (dropSelfMoves_mem hq)).1)
        (fun q hq => dropSelfMoves_noself hq)
        (by rw [hs1_ne A.abi.sp (hd_sp d hddest).symm, hsp]) (hs1m ▸ hm) ?_ ?_ ?_
      · intro d' hd' hnotin
        by_cases hdd' : d' = d
        · subst hdd'; exact hs1d
        · rw [hs1_ne d' hdd']
          refine hdone d' hd' fun p hp heq => ?_
          have hp_flt : p ∈ (m :: ms).filter (fun p => p.1 != d) :=
            List.mem_filter.mpr ⟨hp, bne_iff_ne.mpr (heq ▸ hdd')⟩
          by_cases hself : (match p.2 with | .reg r => p.1 != r | _ => true)
          · exact hnotin p (List.mem_filter.mpr ⟨hp_flt, hself⟩) heq
          · cases hs2 : p.2 with
            | slot _ | imm _ => simp [hs2] at hself
            | reg r =>
              simp only [hs2, bne_iff_ne, Decidable.not_not] at hself
              exact hns p hp r hs2 hself
      · intro p hp
        have hp_orig := (List.mem_filter.mp (dropSelfMoves_mem hp)).1
        have hev_p := hev p hp_orig
        cases hs2 : p.2 with
        | imm _ | slot _ => simpa [evalParSrc, hs2] using hev_p
        | reg r =>
          have hrd : r ≠ d := fun he => by
            subst he; dsimp only [isReadIn] at hpread
            rw [List.any_eq_true.mpr ⟨p, hp_orig, by simp [hs2]⟩] at hpread; cases hpread
          simpa [evalParSrc, hs2, hs1_ne r hrd] using hev_p
      · intro s' hs'd hs'q hs'm
        exact hk s' hs'd (fun q hq1 hq2 =>
          (hs'q q hq1 hq2).trans (hs1_ne q (fun e => hq1 (e ▸ hddest)))) (hs'm.trans hs1m)
    | none =>
      obtain ⟨⟨r, hr⟩, hall_dests⟩ := parMove_all_read_in_dests hnd hfind
      rcases m with ⟨d, sv⟩; dsimp only at hr; subst hr
      have hntmp : ∀ p ∈ (d, .reg r) :: ms, p.2 ≠ .reg tmp := fun p hp heq => by
        have hmem := hall_dests p hp tmp heq
        obtain ⟨q, hqm, hqt⟩ := List.mem_map.mp hmem
        exact htmp q.1 (hsub q hqm) hqt
      have hddest : d ∈ dests := hsub (d, .reg r) List.mem_cons_self
      have hdnr : d ≠ r := hns (d, .reg r) List.mem_cons_self r rfl
      have hd_tmp : d ≠ tmp := htmp d hddest
      have hev_d : s.gpr r = finalVal d := by
        simpa [evalParSrc] using hev (d, .reg r) List.mem_cons_self
      simp only [hdnr, ↓reduceIte]
      refine bodyWp_append _ _ _ ?_
      show bodyWp A symAddr [.mov .w64 tmp d, .mov .w64 d r] _ Ψ H s
      refine instrWp_mov (instrWp_mov ?_)
      let s1 := s.setGprW .w64 tmp (s.gpr d)
      let s2 := s1.setGprW .w64 d (s1.gpr r)
      have hs1d : s1.gpr tmp = s.gpr d := by
        simp only [s1, MachSt.gpr_setGprW_same, hwf.writeSub_w64]
      have hs1r : s1.gpr r = s.gpr r :=
        MachSt.gpr_setGprW_ne s .w64 _ (fun h => hntmp (d, .reg r) List.mem_cons_self (h ▸ rfl))
      have hs2d : s2.gpr d = finalVal d := by
        simp only [s2, MachSt.gpr_setGprW_same, hwf.writeSub_w64, hs1r, hev_d]
      have hs2tmp : s2.gpr tmp = s.gpr d := by
        rw [MachSt.gpr_setGprW_ne s1 .w64 _ hd_tmp.symm, hs1d]
      have hs2_rest : ∀ q, q ≠ d → q ≠ tmp → s2.gpr q = s.gpr q := fun q hqd hqt => by
        rw [MachSt.gpr_setGprW_ne s1 .w64 _ hqd, MachSt.gpr_setGprW_ne s .w64 _ hqt]
      let ms' := dropSelfMoves (ms.map fun p => (p.1, p.2.substReg d tmp))
      have hnd_ms : (ms.map Prod.fst).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
      have hlen_le : ms'.length ≤ ms.length := Nat.le_trans (List.length_filter_le _ _) (by simp)
      refine parMoveAux_bodyWp hwf htmp hd_sp htmp_sp (finalVal := finalVal) fuel ms' s2
        (by simp at hle; omega) (nodup_filter_fst _ (nodup_map_subst d tmp hnd_ms))
        (fun q hq => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dropSelfMoves_mem hq)
          exact hsub p (List.mem_cons_of_mem _ hp))
        (fun q hq => dropSelfMoves_noself hq)
        (by rw [hs2_rest A.abi.sp (hd_sp d hddest).symm htmp_sp.symm, hsp]) hm ?_ ?_ ?_
      · intro d' hd' hnotin
        by_cases hdd' : d' = d
        · subst hdd'; exact hs2d
        · rw [hs2_rest d' hdd' (htmp d' hd')]
          refine hdone d' hd' fun p hp heq => ?_
          rcases List.mem_cons.mp hp with rfl | hpms
          · exact hdd' heq.symm
          · let p' : A.Reg × ParSrc A := (p.1, p.2.substReg d tmp)
            by_cases hself : (match p'.2 with | .reg u => p'.1 != u | _ => true)
            · exact hnotin p' (List.mem_filter.mpr ⟨List.mem_map_of_mem hpms, hself⟩) heq
            · cases hp2 : p'.2 with
              | slot _ | imm _ => simp [hp2] at hself
              | reg u =>
                simp only [hp2, bne_iff_ne, Decidable.not_not] at hself
                cases hp20 : p.2 with
                | slot _ | imm _ => simp [p', ParSrc.substReg, hp20] at hp2
                | reg v =>
                  simp only [p', ParSrc.substReg, hp20] at hp2
                  split at hp2 <;> cases hp2
                  · exact absurd hself (htmp p.1 (hsub p (List.mem_cons_of_mem _ hpms)))
                  · exact hns p hp u hp20 hself
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dropSelfMoves_mem hq)
        rw [← hev p (List.mem_cons_of_mem _ hp)]
        exact evalParSrc_subst_ne slots s s2 d tmp hs2tmp hs2_rest p.2
          (hntmp p (List.mem_cons_of_mem _ hp))
      · intro s' hs'd hs'q hs'm
        exact hk s' hs'd (fun q hq1 hq2 =>
          (hs'q q hq1 hq2).trans (hs2_rest q (fun e => hq1 (e ▸ hddest)) hq2)) hs'm

private theorem argToParSrc_sound {A : Arch} {b : WordRegBind A} {sb d : Nat}
    {a : Arg K i64} {bvs : List ((t : Ty) × Val t)} {a' : Arg Val i64}
    {s : MachSt A} {slots : List (BitVec 64)} {G : Mem 64 → Prop} {ps : ParSrc A}
    (he : EnvRel b sb d bvs s) (hden : denoteArg bvs a = some a')
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ G) s.mem)
    (hslots : ∀ lvl < d, ∀ j, locOf b sb lvl = .slot j → j < slots.length)
    (hlo : argToParSrc b sb d a = .ok ps) :
    evalParSrc slots s ps = some a'.val := by
  cases a with
  | imm c => cases hden; cases hlo; rfl
  | var idx =>
    obtain ⟨v, rfl⟩ := denoteArg_var_eq hden
    dsimp only [argToParSrc] at hlo; split at hlo
    · obtain ⟨_, hloc⟩ := envRel_get he hden
      cases hl : locOf b sb (d - 1 - idx) with
      | gpr r =>
        simp only [hl, Except.ok.injEq] at hlo; subst hlo
        dsimp only [LocHolds] at hloc; rw [hl] at hloc
        simpa [evalParSrc, ValHolds64, Arg.val] using hloc.2
      | slot k =>
        simp only [hl, Except.ok.injEq] at hlo; subst hlo
        dsimp only [LocHolds] at hloc; rw [hl] at hloc
        obtain ⟨g, hld, hval⟩ := hloc
        have hklt : k < slots.length := hslots _ (by omega) k hl
        have hld' := loadVal_array64 hklt hm; rw [hld'] at hld; cases hld
        dsimp only [evalParSrc]; rw [List.getElem?_eq_getElem hklt]
        exact congrArg some (by simpa [ValHolds64, Arg.val] using hval.2)
    · cases hlo

theorem emitNextRegs_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d : Nat} {nxt : RegsExpr K}
    {bvs : List ((t : Ty) × Val t)} {nxt' : RegsExpr Val} {s : MachSt A}
    {slots : List (BitVec 64)} {G : Mem 64 → Prop}
    {is : List (Instr A)} {Kpost : MachSt A → Prop}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    (he : EnvRel b sb d bvs s)
    (hden : denoteRegsExpr bvs nxt = some nxt')
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ G) s.mem)
    (hslots : ∀ lvl < d, ∀ j, locOf b sb lvl = .slot j → j < slots.length)
    (hlo : emitNextRegs b sb d nxt = .ok is)
    (hk : ∀ s',
      WordRegsRel b nxt'.eval s' →
      (∀ q, q ∉ b.wordRegs → q ≠ b.w1 → s'.gpr q = s.gpr q) →
      s'.mem = s.mem →
      Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  dsimp only [denoteRegsExpr] at hden
  cases hspD : denoteArg bvs nxt.sp <;> rw [hspD] at hden; · cases hden
  cases hrpD : denoteArg bvs nxt.rp <;> rw [hrpD] at hden; · cases hden
  cases hrvD : denoteArg bvs nxt.rv <;> rw [hrvD] at hden; · cases hden
  cases hr1D : denoteArg bvs nxt.r1 <;> rw [hr1D] at hden; · cases hden
  cases hr2D : denoteArg bvs nxt.r2 <;> rw [hr2D] at hden; · cases hden
  cases hr3D : denoteArg bvs nxt.r3 <;> rw [hr3D] at hden; · cases hden
  cases hden; rename_i spA rpA rvA r1A r2A r3A
  dsimp only [emitNextRegs, Except.bind] at hlo
  cases hspP : argToParSrc b sb d nxt.sp <;> rw [hspP] at hlo; · cases hlo
  cases hrpP : argToParSrc b sb d nxt.rp <;> rw [hrpP] at hlo; · cases hlo
  cases hrvP : argToParSrc b sb d nxt.rv <;> rw [hrvP] at hlo; · cases hlo
  cases hr1P : argToParSrc b sb d nxt.r1 <;> rw [hr1P] at hlo; · cases hlo
  cases hr2P : argToParSrc b sb d nxt.r2 <;> rw [hr2P] at hlo; · cases hlo
  cases hr3P : argToParSrc b sb d nxt.r3 <;> rw [hr3P] at hlo; · cases hlo
  cases hlo
  rename_i spS rpS rvS r1S r2S r3S
  have hspE := argToParSrc_sound he hspD hm hslots hspP
  have hrpE := argToParSrc_sound he hrpD hm hslots hrpP
  have hrvE := argToParSrc_sound he hrvD hm hslots hrvP
  have hr1E := argToParSrc_sound he hr1D hm hslots hr1P
  have hr2E := argToParSrc_sound he hr2D hm hslots hr2P
  have hr3E := argToParSrc_sound he hr3D hm hslots hr3P
  let allPairs : List (A.Reg × ParSrc A) :=
    [(b.sp, spS), (b.rp, rpS), (b.rv, rvS), (b.r1, r1S), (b.r2, r2S), (b.r3, r3S)]
  let pairs := dropSelfMoves allPairs
  let finalVal : A.Reg → BitVec 64 := fun q =>
    if q = b.sp then spA.val else if q = b.rp then rpA.val else if q = b.rv then rvA.val
    else if q = b.r1 then r1A.val else if q = b.r2 then r2A.val else if q = b.r3 then r3A.val
    else s.gpr q
  have ⟨h01, h02, h03, h04, h05, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ :=
    wordRegs_nodup_6 hwf
  have hw_not := wordRegs_not_sp_ra hwf
  have hw_wk := work_not_sp hwf
  have hev_all : ∀ p ∈ allPairs, evalParSrc slots s p.2 = some (finalVal p.1) := by
    intro p hp
    simp only [allPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [finalVal, hspE, hrpE, hrvE, hr1E, hr2E, hr3E, h01.symm, h02.symm, h03.symm, h04.symm,
        h05.symm, h12.symm, h13.symm, h14.symm, h15.symm, h23.symm, h24.symm, h25.symm, h34.symm,
        h35.symm, h45.symm]
  have hdone : ∀ d ∈ b.wordRegs, (∀ p ∈ pairs, p.1 ≠ d) → s.gpr d = finalVal d := by
    intro d hd hnotin
    have hchk : ∀ sv : ParSrc A, (d, sv) ∈ allPairs →
        evalParSrc slots s sv = some (finalVal d) → s.gpr d = finalVal d := by
      intro sv hmem hev0
      by_cases hself : (match sv with | .reg r => d != r | _ => true)
      · exact absurd rfl (hnotin (d, sv) (List.mem_filter.mpr ⟨hmem, hself⟩))
      · cases sv with
        | slot _ | imm _ => simp at hself
        | reg r =>
          simp only [bne_iff_ne, Decidable.not_not] at hself
          subst hself; simpa [evalParSrc] using hev0
    simp only [WordRegBind.wordRegs, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hchk spS (by simp [allPairs]) (hev_all (b.sp, spS) (by simp [allPairs]))
    · exact hchk rpS (by simp [allPairs]) (hev_all (b.rp, rpS) (by simp [allPairs]))
    · exact hchk rvS (by simp [allPairs]) (hev_all (b.rv, rvS) (by simp [allPairs]))
    · exact hchk r1S (by simp [allPairs]) (hev_all (b.r1, r1S) (by simp [allPairs]))
    · exact hchk r2S (by simp [allPairs]) (hev_all (b.r2, r2S) (by simp [allPairs]))
    · exact hchk r3S (by simp [allPairs]) (hev_all (b.r3, r3S) (by simp [allPairs]))
  refine parMoveAux_bodyWp hawf (fun d hd => (hw_not.2 d hd).2.2.1)
    (fun d hd => (hw_not.1 d hd).1) hw_wk.2.2.1 pairs.length pairs s (Nat.le_refl _)
    (nodup_filter_fst _ (by dsimp only [allPairs]; exact wordRegs_nodup hwf))
    (fun p hp => by
      have h0 := dropSelfMoves_mem hp
      simp only [allPairs, List.mem_cons, List.not_mem_nil, or_false] at h0
      rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [WordRegBind.wordRegs])
    (fun _ hp => dropSelfMoves_noself hp) rfl hm hdone
    (fun p hp => hev_all p (dropSelfMoves_mem hp)) ?_
  intro s' hs'd hs'q hs'm
  refine hk s' ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ hs'q hs'm
  · simpa [RegsExpr.eval, finalVal] using hs'd b.sp (by simp [WordRegBind.wordRegs])
  · simpa [RegsExpr.eval, finalVal, h01.symm] using hs'd b.rp (by simp [WordRegBind.wordRegs])
  · simpa [RegsExpr.eval, finalVal, h02.symm, h12.symm] using
      hs'd b.rv (by simp [WordRegBind.wordRegs])
  · simpa [RegsExpr.eval, finalVal, h03.symm, h13.symm, h23.symm] using
      hs'd b.r1 (by simp [WordRegBind.wordRegs])
  · simpa [RegsExpr.eval, finalVal, h04.symm, h14.symm, h24.symm, h34.symm] using
      hs'd b.r2 (by simp [WordRegBind.wordRegs])
  · simpa [RegsExpr.eval, finalVal, h05.symm, h15.symm, h25.symm, h35.symm, h45.symm] using
      hs'd b.r3 (by simp [WordRegBind.wordRegs])

/-! ## §5. Operation Lowering Simulation (`lowerOp_bodyWp`) -/

theorem w_mem_workRegs {A : Arch} (b : WordRegBind A) :
    b.w0 ∈ b.workRegs ∧ b.w1 ∈ b.workRegs ∧ b.w2 ∈ b.workRegs := by simp [WordRegBind.workRegs]

theorem denoteArgs_one {t : Ty} {bvs : List ((u : Ty) × Val u)}
    {a : Arg K t} {args' : Tup (Arg Val) [t]} (h : denoteArgs bvs (a, ()) = some args') :
    denoteArg bvs a = some args'.1 := by
  dsimp only [denoteArgs] at h
  cases hd : denoteArg bvs a <;> rw [hd] at h
  · cases h
  · cases h; rfl

theorem denoteArgs_two {t₁ t₂ : Ty} {bvs : List ((u : Ty) × Val u)}
    {a : Arg K t₁} {c : Arg K t₂} {args' : Tup (Arg Val) [t₁, t₂]}
    (h : denoteArgs bvs (a, c, ()) = some args') :
    denoteArg bvs a = some args'.1 ∧ denoteArg bvs c = some args'.2.1 := by
  dsimp only [denoteArgs] at h
  cases ha : denoteArg bvs a <;> rw [ha] at h; · cases h
  cases hc : denoteArg bvs c <;> rw [hc] at h; · cases h
  cases h; exact ⟨rfl, rfl⟩

theorem denoteArgs_three {t₁ t₂ t₃ : Ty} {bvs : List ((u : Ty) × Val u)}
    {a : Arg K t₁} {c : Arg K t₂} {e : Arg K t₃} {args' : Tup (Arg Val) [t₁, t₂, t₃]}
    (h : denoteArgs bvs (a, c, e, ()) = some args') :
    denoteArg bvs a = some args'.1 ∧ denoteArg bvs c = some args'.2.1 ∧
    denoteArg bvs e = some args'.2.2.1 := by
  dsimp only [denoteArgs] at h
  cases ha : denoteArg bvs a <;> rw [ha] at h; · cases h
  cases hc : denoteArg bvs c <;> rw [hc] at h; · cases h
  cases he : denoteArg bvs e <;> rw [he] at h; · cases h
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem wordRegsRel_updWork {A : Arch} {b : WordRegBind A} (hwf : b.Wf) {rw : Regs}
    {s s' : MachSt A} (hr : WordRegsRel b rw s) (q : A.Reg) (hq : q ∈ b.workRegs)
    (hother : ∀ r, r ≠ q → s'.gpr r = s.gpr r) : WordRegsRel b rw s' := by
  have hnot := wordRegs_not_sp_ra hwf
  have hne : ∀ w ∈ b.wordRegs, w ≠ q := fun w hw he => by
    subst he; have ⟨_, _, _, _⟩ := hnot.2 w hw
    simp only [WordRegBind.workRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> contradiction
  simp only [WordRegsRel] at hr ⊢
  rcases hr with ⟨a0, a1, a2, a3, a4, a5⟩
  exact ⟨(hother _ (hne b.sp (by simp [WordRegBind.wordRegs]))).trans a0,
    (hother _ (hne b.rp (by simp [WordRegBind.wordRegs]))).trans a1,
    (hother _ (hne b.rv (by simp [WordRegBind.wordRegs]))).trans a2,
    (hother _ (hne b.r1 (by simp [WordRegBind.wordRegs]))).trans a3,
    (hother _ (hne b.r2 (by simp [WordRegBind.wordRegs]))).trans a4,
    (hother _ (hne b.r3 (by simp [WordRegBind.wordRegs]))).trans a5⟩

private theorem loadArgToGpr_w1_ne_w2 {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {sb d : Nat} {t : Ty} {a : Arg K t} {ca : List (Instr A)} {rg : A.Reg}
    (h : loadArgToGpr b sb d b.w1 a = .ok (ca, rg)) : rg ≠ b.w2 := by
  intro he; subst he
  cases a with
  | imm c =>
    dsimp only [loadArgToGpr] at h; cases him : immToBitVec64 t c <;> simp [him] at h
    exact (wordRegBind_work_ne hwf).2.2.2.2.2 h.2
  | var idx =>
    dsimp only [loadArgToGpr] at h; split at h
    · cases hlx : locOf b sb (d - 1 - idx) with
      | gpr _ => simp [hlx] at h; exact (locOf_gpr_ne_work hwf sb _ hlx).2.2.2 h.2
      | slot _ => simp [hlx] at h; exact (wordRegBind_work_ne hwf).2.2.2.2.2 h.2
    · cases h

def BinValMatch (w : Width) (aBV bBV : BitVec w.bits) : (t : Ty) → Val t → Val t → Prop
  | .bool, lb, rb => w = .w8 ∧
      aBV.setWidth 8 = BitVec.ofNat 8 lb.toNat ∧
      bBV.setWidth 8 = BitVec.ofNat 8 rb.toNat
  | .bits n, lv, rv => ∀ (hw : n = w.bits), aBV = lv.cast hw ∧ bBV = rv.cast hw
  | _, _, _ => False

theorem lowerBinBits_bodyWp {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax : Nat} {op : CoreAlu} {w : Width}
    {t resT : Ty} {lhs rhs : Arg K t} {bvs : List ((u : Ty) × Val u)}
    {la ra : Arg Val t} {rw : Regs} {slots : List (BitVec 64)} {G : Mem 64 → Prop}
    {s : MachSt A} {is : List (Instr A)} {resVal : Val resT}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hd : d < dMax) (h6 : 6 ≤ d) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ G) s.mem)
    (hl : denoteArg bvs lhs = some la) (hrhs : denoteArg bvs rhs = some ra)
    (hwbool : t = .bool → w = .w8)
    (hlo : lowerBinBits b sb d (locOf b sb d) op w lhs rhs = .ok is)
    (hval : ∀ (aBV bBV : BitVec w.bits),
      BinValMatch w aBV bBV t la.val ra.val →
      ∀ old, ValHolds64 resT resVal (A.writeSub w old (op.eval w aBV bBV)))
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length → (∀ j < sb, slots'[j]? = slots[j]?) →
      EnvRel b sb (d + 1) (⟨resT, resVal⟩ :: bvs) s' → WordRegsRel b rw s' →
      s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem → Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  dsimp only [lowerBinBits, Except.bind] at hlo
  cases h1 : loadArgToGpr b sb d b.w1 lhs <;> rw [h1] at hlo; · cases hlo
  cases h2 : argToSrc b sb d b.w2 rhs <;> rw [h2] at hlo; · cases hlo
  cases hlo
  rename_i p1 p2; rcases p1 with ⟨ca, regA⟩; rcases p2 with ⟨cb, sbSrc⟩
  have hwk := w_mem_workRegs b
  rw [List.append_assoc]
  refine bodyWp_append ca _ _ ?_
  refine loadArgToGpr_bodyWp hwf hwk.2.1 he hl hm h1 ?_
  intro s1 hs1_ne hv1 hm1 he1
  have hr1 := wordRegsRel_updWork hwf hr b.w1 hwk.2.1 hs1_ne
  refine bodyWp_append cb _ _ ?_
  refine argToSrc_bodyWp hwf hwk.2.2 he1 hrhs h2 ?_
  intro s2 hs2_ne hv2 hm2 he2
  have hsp2 : s2.gpr A.abi.sp = s.gpr A.abi.sp := by
    rw [hs2_ne A.abi.sp (work_not_sp hwf).2.2.2.symm,
      hs1_ne A.abi.sp (work_not_sp hwf).2.2.1.symm]
  have hv1_2 : ValHolds64 t la.val (s2.gpr regA) :=
    (hs2_ne regA (loadArgToGpr_w1_ne_w2 hwf h1)) ▸ hv1
  have hr2 := wordRegsRel_updWork hwf hr1 b.w2 hwk.2.2 hs2_ne
  have hm2' : (array64 (s2.gpr A.abi.sp) slots ⋆ G) s2.mem := by
    simpa [hm2, hm1, hsp2] using hm
  have hcore : ∀ rd (hrd : rd = b.w0 ∨ locOf b sb d = .gpr rd),
      bodyWp A symAddr [Instr.alu op w rd regA sbSrc false] (fun s' =>
        ValHolds64 resT resVal (s'.gpr rd) ∧ s'.gpr A.abi.sp = s2.gpr A.abi.sp ∧
        EnvRel b sb d bvs s' ∧ WordRegsRel b rw s' ∧
        ∃ slots' : List (BitVec 64), slots'.length = slots.length ∧
          (∀ j < sb, slots'[j]? = slots[j]?) ∧
          (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem) Ψ H s2 := by
    intro rd hrd; refine instrWp_alu ?_
    have hsp_rd : A.abi.sp ≠ rd := by
      rcases hrd with rfl | hlrd
      · exact (work_not_sp hwf).2.1.symm
      · exact (locOf_gpr_ne_sp hwf sb d hlrd).symm
    refine ⟨?_, MachSt.gpr_setGprW_ne _ _ _ hsp_rd, ?_, ?_, slots, rfl, fun _ _ => rfl,
      by simpa [MachSt.gpr_setGprW_ne _ _ _ hsp_rd] using hm2'⟩
    · simp only [MachSt.gpr_setFlags, MachSt.gpr_setGprW_same]; apply hval
      cases t with
      | bool =>
        have hw8 := hwbool rfl; subst hw8
        refine ⟨rfl, ?_, ?_⟩
        · simpa [Width.bits, BitVec.setWidth_eq, ValHolds64] using hv1_2
        · simpa [Width.bits, BitVec.setWidth_eq, SrcValMatch] using hv2
      | bits n => intro hn; subst hn; exact ⟨hv1_2.2, hv2 w rfl⟩
      | float _ | pair _ _ => cases hv1_2
    · rcases hrd with rfl | hlrd
      · exact (envRel_setGprW_work hwf sb d bvs s2 w hwk.1 _).mpr he2
      · exact envRel_setGpr_new hwf hlrd _ he2
    · rcases hrd with rfl | hlrd
      · exact (wordRegsRel_setGpr_work hwf rw s2 (Or.inl hwk.1) _).mpr hr2
      · exact (wordRegsRel_setGprW_ge6 hwf rw s2 w h6 hlrd _).mpr hr2
  refine emitToLoc_bodyWp hwf hd hbound (fun rd h => hcore rd (Or.inr h))
    (fun _ _ => hcore b.w0 (Or.inl rfl)) ?_
  intro s' slots' hlen hsb he' hr' hsp' hm'
  exact hk s' slots' hlen hsb he' hr' (hsp'.trans hsp2) hm'

theorem lowerCmpBits_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax : Nat} {o : CmpOp} {w : Width}
    {t : Ty} {lhs rhs : Arg K t} {bvs : List ((u : Ty) × Val u)}
    {la ra : Arg Val t} {rw : Regs} {slots : List (BitVec 64)} {G : Mem 64 → Prop}
    {s : MachSt A} {is : List (Instr A)} {resVal : Bool}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hd : d < dMax) (h6 : 6 ≤ d) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ G) s.mem)
    (hl : denoteArg bvs lhs = some la) (hrhs : denoteArg bvs rhs = some ra)
    (hwbool : t = .bool → w = .w8)
    (hlo : lowerCmpBits b sb d (locOf b sb d) o w lhs rhs = .ok is)
    (hval : ∀ (aBV bBV : BitVec w.bits),
      BinValMatch w aBV bBV t la.val ra.val → o.evalBits aBV bBV = resVal)
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length → (∀ j < sb, slots'[j]? = slots[j]?) →
      EnvRel b sb (d + 1) (⟨.bool, resVal⟩ :: bvs) s' → WordRegsRel b rw s' →
      s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem → Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  dsimp only [lowerCmpBits, Except.bind] at hlo
  cases hcc : b.condOfCmp? o with
  | none => simp [hcc] at hlo
  | some cc =>
    simp only [hcc] at hlo
    cases h1 : loadArgToGpr b sb d b.w1 lhs <;> rw [h1] at hlo; · cases hlo
    cases h2 : argToSrc b sb d b.w2 rhs <;> rw [h2] at hlo; · cases hlo
    cases hlo
    rename_i p1 p2; rcases p1 with ⟨ca, regA⟩; rcases p2 with ⟨cb, sbSrc⟩
    have hwk := w_mem_workRegs b
    simp only [List.append_assoc]
    refine bodyWp_append ca _ _ ?_
    refine loadArgToGpr_bodyWp hwf hwk.2.1 he hl hm h1 ?_
    intro s1 hs1_ne hv1 hm1 he1
    have hr1 := wordRegsRel_updWork hwf hr b.w1 hwk.2.1 hs1_ne
    refine bodyWp_append cb _ _ ?_
    refine argToSrc_bodyWp hwf hwk.2.2 he1 hrhs h2 ?_
    intro s2 hs2_ne hv2 hm2 he2
    have hsp2 : s2.gpr A.abi.sp = s.gpr A.abi.sp := by
      rw [hs2_ne A.abi.sp (work_not_sp hwf).2.2.2.symm,
        hs1_ne A.abi.sp (work_not_sp hwf).2.2.1.symm]
    have hv1_2 : ValHolds64 t la.val (s2.gpr regA) :=
      (hs2_ne regA (loadArgToGpr_w1_ne_w2 hwf h1)) ▸ hv1
    have hr2 := wordRegsRel_updWork hwf hr1 b.w2 hwk.2.2 hs2_ne
    refine instrWp_cmp ?_
    let s3 := s2.setFlags
      (A.cmpFlags w ((s2.gpr regA).setWidth w.bits) (sbSrc.evalW w s2.gpr) s2.flags)
    have hcond : A.evalCond s3.flags cc = resVal := by
      dsimp only [s3]; rw [MachSt.flags_setFlags, hwf.cond_sound o cc w _ _ _ hcc]; apply hval
      cases t with
      | bool =>
        have hw8 := hwbool rfl; subst hw8
        refine ⟨rfl, ?_, ?_⟩
        · simpa [Width.bits, BitVec.setWidth_eq, ValHolds64] using hv1_2
        · simpa [Width.bits, BitVec.setWidth_eq, SrcValMatch] using hv2
      | bits n => intro hn; subst hn; exact ⟨hv1_2.2, hv2 w rfl⟩
      | float _ | pair _ _ => cases hv1_2
    have hm3 : (array64 (s3.gpr A.abi.sp) slots ⋆ G) s3.mem := by
      simpa [s3, hm2, hm1, hsp2] using hm
    have hcore : ∀ rd (hrd : rd = b.w0 ∨ locOf b sb d = .gpr rd),
        bodyWp A symAddr [Instr.setcc rd cc] (fun s' =>
          ValHolds64 .bool resVal (s'.gpr rd) ∧ s'.gpr A.abi.sp = s3.gpr A.abi.sp ∧
          EnvRel b sb d bvs s' ∧ WordRegsRel b rw s' ∧
          ∃ slots' : List (BitVec 64), slots'.length = slots.length ∧
            (∀ j < sb, slots'[j]? = slots[j]?) ∧
            (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem) Ψ H s3 := by
      intro rd hrd; refine instrWp_setcc ?_
      have hsp_rd : A.abi.sp ≠ rd := by
        rcases hrd with rfl | hlrd
        · exact (work_not_sp hwf).2.1.symm
        · exact (locOf_gpr_ne_sp hwf sb d hlrd).symm
      refine ⟨by
        dsimp only [ValHolds64, Width.bits]
        rw [MachSt.gpr_setGprW_same, hawf.writeSub_setWidth .w8, hcond],
        MachSt.gpr_setGprW_ne s3 .w8 _ hsp_rd, ?_, ?_, slots, rfl, fun _ _ => rfl,
        by simpa [MachSt.gpr_setGprW_ne s3 .w8 _ hsp_rd] using hm3⟩
      · rcases hrd with rfl | hlrd
        · exact (envRel_setGprW_work hwf sb d bvs s3 .w8 hwk.1 _).mpr he2
        · exact envRel_setGpr_new hwf hlrd _ he2
      · rcases hrd with rfl | hlrd
        · exact (wordRegsRel_setGprW_work hwf rw s3 .w8 (Or.inl hwk.1) _).mpr hr2
        · exact (wordRegsRel_setGprW_ge6 hwf rw s3 .w8 h6 hlrd _).mpr hr2
    refine emitToLoc_bodyWp hwf hd hbound (fun rd h => hcore rd (Or.inr h))
      (fun _ _ => hcore b.w0 (Or.inl rfl)) ?_
    intro s' slots' hlen hsb he' hr' hsp' hm'
    exact hk s' slots' hlen hsb he' hr' (hsp'.trans hsp2) hm'

theorem lowerSelect_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax : Nat} {t : Ty}
    {c : Arg K .bool} {tArg fArg : Arg K t} {bvs : List ((u : Ty) × Val u)}
    {ca : Arg Val .bool} {ta fa : Arg Val t} {rw : Regs} {slots : List (BitVec 64)}
    {G : Mem 64 → Prop} {s : MachSt A} {is : List (Instr A)}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hd : d < dMax) (h6 : 6 ≤ d) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ G) s.mem)
    (hcD : denoteArg bvs c = some ca) (htD : denoteArg bvs tArg = some ta)
    (hfD : denoteArg bvs fArg = some fa)
    (hlo : lowerSelect b sb d (locOf b sb d) c tArg fArg = .ok is)
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length → (∀ j < sb, slots'[j]? = slots[j]?) →
      EnvRel b sb (d + 1) (⟨t, if ca.val then ta.val else fa.val⟩ :: bvs) s' →
      WordRegsRel b rw s' → s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem → Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  dsimp only [lowerSelect, Except.bind] at hlo
  cases hcc : loadArgToGpr b sb d b.w0 c <;> rw [hcc] at hlo; · cases hlo
  cases hct : loadArgInto b sb d b.w1 tArg <;> rw [hct] at hlo; · cases hlo
  cases hcf : loadArgInto b sb d b.w2 fArg <;> rw [hcf] at hlo; · cases hlo
  cases hlo; rename_i p0 ct cf; rcases p0 with ⟨cc, rc⟩
  have hwk := w_mem_workRegs b; have ⟨_, _, _, hw01, hw02, hw12⟩ := wordRegBind_work_ne hwf
  have hwsp := work_not_sp hwf; simp only [List.append_assoc]
  refine bodyWp_append cc _ _ (loadArgToGpr_bodyWp hwf hwk.1 he hcD hm hcc ?_)
  intro s1 hs1_ne hv1 hm1 he1
  have hsp1 : s1.gpr A.abi.sp = s.gpr A.abi.sp := hs1_ne A.abi.sp hwsp.2.1.symm
  have hr1 := wordRegsRel_updWork hwf hr b.w0 hwk.1 hs1_ne
  refine instrWp_alu (instrWp_movi (instrWp_alu ?_))
  let mask := 0#64 - (s1.gpr rc &&& 1#64)
  suffices hpost : ∀ s2 : MachSt A, s2.gpr b.w0 = mask → s2.gpr A.abi.sp = s.gpr A.abi.sp →
      s2.mem = s.mem → EnvRel b sb d bvs s2 → WordRegsRel b rw s2 →
      bodyWp A symAddr (ct ++ (cf ++ emitToLoc b.w0 (locOf b sb d) fun rd =>
        [.alu .and .w64 b.w1 b.w1 (.reg b.w0) false,
         .alu .xor .w64 b.w0 b.w0 (.imm 0xFFFFFFFFFFFFFFFF#64) false,
         .alu .and .w64 b.w2 b.w2 (.reg b.w0) false,
         .alu .or .w64 rd b.w1 (.reg b.w2) false])) Kpost Ψ H s2 by
    refine hpost _ ?_ ?_ ?_ ?_ ?_
    · simp only [MachSt.gpr_setFlags, MachSt.gpr_setGprW_same, hawf.writeSub_w64,
        MachSt.gpr_setGpr_same, MachSt.gpr_setGpr_ne _ _ hw01, CoreAlu.eval, Src.evalW, Src.eval,
        Width.bits, BitVec.setWidth_eq, mask]
    · simp only [MachSt.gpr_setFlags, MachSt.gpr_setGprW_ne _ _ _ hwsp.2.1.symm,
        MachSt.gpr_setGpr_ne _ _ hwsp.2.2.1.symm, hsp1]
    · simpa only [MachSt.mem_setFlags, MachSt.mem_setGprW, MachSt.mem_setGpr] using hm1
    · rw [envRel_setFlags, envRel_setGprW_work hwf sb d bvs _ .w64 hwk.1 _,
        envRel_setGpr_work hwf sb d bvs _ hwk.2.1 _, envRel_setFlags,
        envRel_setGprW_work hwf sb d bvs _ .w64 hwk.1 _]; exact he1
    · rw [wordRegsRel_setFlags, wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.1) _,
        wordRegsRel_setGpr_work hwf rw _ (Or.inl hwk.2.1) _, wordRegsRel_setFlags,
        wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.1) _]; exact hr1
  intro s2 hs2_w0 hs2_sp hs2_mem he2 hr2
  have hm2 : (array64 (s2.gpr A.abi.sp) slots ⋆ G) s2.mem := by simpa [hs2_sp, hs2_mem] using hm
  refine bodyWp_append ct _ _ (loadArgInto_bodyWp hawf hwf hwk.2.1 he2 htD hm2 hct ?_)
  intro s3 hs3_ne hv3 hm3_eq he3
  have hs3_w0 : s3.gpr b.w0 = mask := (hs3_ne b.w0 hw01).trans hs2_w0
  have hs3_sp : s3.gpr A.abi.sp = s.gpr A.abi.sp := (hs3_ne A.abi.sp hwsp.2.2.1.symm).trans hs2_sp
  have hm3 : (array64 (s3.gpr A.abi.sp) slots ⋆ G) s3.mem := by
    simpa [hs3_sp, hm3_eq, hs2_mem] using hm
  have hr3 := wordRegsRel_updWork hwf hr2 b.w1 hwk.2.1 hs3_ne
  refine bodyWp_append cf _ _ (loadArgInto_bodyWp hawf hwf hwk.2.2 he3 hfD hm3 hcf ?_)
  intro s4 hs4_ne hv4 hm4_eq he4
  have hs4_w0 : s4.gpr b.w0 = mask := (hs4_ne b.w0 hw02).trans hs3_w0
  have hs4_w1 : s4.gpr b.w1 = s3.gpr b.w1 := hs4_ne b.w1 hw12
  have hs4_sp : s4.gpr A.abi.sp = s.gpr A.abi.sp :=
    (hs4_ne A.abi.sp hwsp.2.2.2.symm).trans hs3_sp
  have hm4 : (array64 (s4.gpr A.abi.sp) slots ⋆ G) s4.mem := by
    simpa [hs4_sp, hm4_eq, hm3_eq, hs2_mem] using hm
  have hr4 := wordRegsRel_updWork hwf hr3 b.w2 hwk.2.2 hs4_ne
  have hcore : ∀ rd (hrd : rd = b.w0 ∨ locOf b sb d = .gpr rd),
      bodyWp A symAddr
        [.alu .and .w64 b.w1 b.w1 (.reg b.w0) false,
         .alu .xor .w64 b.w0 b.w0 (.imm 0xFFFFFFFFFFFFFFFF#64) false,
         .alu .and .w64 b.w2 b.w2 (.reg b.w0) false,
         .alu .or .w64 rd b.w1 (.reg b.w2) false] (fun s' =>
          ValHolds64 t (if ca.val then ta.val else fa.val) (s'.gpr rd) ∧
          s'.gpr A.abi.sp = s4.gpr A.abi.sp ∧ EnvRel b sb d bvs s' ∧ WordRegsRel b rw s' ∧
          ∃ slots' : List (BitVec 64), slots'.length = slots.length ∧
            (∀ j < sb, slots'[j]? = slots[j]?) ∧
            (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem) Ψ H s4 := by
    intro rd hrd
    refine instrWp_alu (instrWp_alu (instrWp_alu (instrWp_alu ?_)))
    have hsp_rd : A.abi.sp ≠ rd := by
      rcases hrd with rfl | hlrd
      · exact hwsp.2.1.symm
      · exact (locOf_gpr_ne_sp hwf sb d hlrd).symm
    have heval : ((s4.gpr b.w1 &&& mask) |||
        (s4.gpr b.w2 &&& (mask ^^^ 0xFFFFFFFFFFFFFFFF#64))) =
        if ca.val then s3.gpr b.w1 else s4.gpr b.w2 := by
      rw [hs4_w1]; exact bv64_select_mask_any ca.val (s1.gpr rc) (s3.gpr b.w1) (s4.gpr b.w2) hv1
    refine ⟨?_, ?_, ?_, ?_, slots, rfl, fun _ _ => rfl, ?_⟩
    · simp only [MachSt.gpr_setFlags, MachSt.gpr_setGprW_same, MachSt.gpr_setGprW_ne _ _ _ hw01,
        MachSt.gpr_setGprW_ne _ _ _ hw01.symm, MachSt.gpr_setGprW_ne _ _ _ hw02.symm,
        MachSt.gpr_setGprW_ne _ _ _ hw12, MachSt.gpr_setGprW_ne _ _ _ hw12.symm,
        hawf.writeSub_w64, BitVec.setWidth_eq, Src.evalW, Src.eval, Width.bits,
        CoreAlu.eval, hs4_w0]
      rw [heval]; cases ca.val <;> first | exact hv4 | exact hs4_w1 ▸ hv3
    · simp only [MachSt.gpr_setFlags, MachSt.gpr_setGprW_ne _ _ _ hsp_rd,
        MachSt.gpr_setGprW_ne _ _ _ hwsp.2.2.2.symm, MachSt.gpr_setGprW_ne _ _ _ hwsp.2.1.symm,
        MachSt.gpr_setGprW_ne _ _ _ hwsp.2.2.1.symm]
    · simp only [envRel_setFlags]
      rcases hrd with rfl | hlrd
      · rw [envRel_setGprW_work hwf sb d bvs _ .w64 hwk.1 _,
          envRel_setFlags, envRel_setGprW_work hwf sb d bvs _ .w64 hwk.2.2 _,
          envRel_setFlags, envRel_setGprW_work hwf sb d bvs _ .w64 hwk.1 _,
          envRel_setFlags, envRel_setGprW_work hwf sb d bvs _ .w64 hwk.2.1 _]; exact he4
      · refine envRel_setGpr_new hwf hlrd _ ?_
        rw [envRel_setFlags, envRel_setGprW_work hwf sb d bvs _ .w64 hwk.2.2 _,
          envRel_setFlags, envRel_setGprW_work hwf sb d bvs _ .w64 hwk.1 _,
          envRel_setFlags, envRel_setGprW_work hwf sb d bvs _ .w64 hwk.2.1 _]; exact he4
    · simp only [wordRegsRel_setFlags]
      rcases hrd with rfl | hlrd
      · rw [wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.1) _,
          wordRegsRel_setFlags, wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.2.2) _,
          wordRegsRel_setFlags, wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.1) _,
          wordRegsRel_setFlags, wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.2.1) _]
        exact hr4
      · rw [wordRegsRel_setGprW_ge6 hwf rw _ .w64 h6 hlrd _,
          wordRegsRel_setFlags, wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.2.2) _,
          wordRegsRel_setFlags, wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.1) _,
          wordRegsRel_setFlags, wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.2.1) _]
        exact hr4
    · simpa [MachSt.mem_setFlags, MachSt.mem_setGprW, MachSt.gpr_setFlags,
        MachSt.gpr_setGprW_ne _ _ _ hsp_rd, MachSt.gpr_setGprW_ne _ _ _ hwsp.2.2.2.symm,
        MachSt.gpr_setGprW_ne _ _ _ hwsp.2.1.symm, MachSt.gpr_setGprW_ne _ _ _ hwsp.2.2.1.symm,
        hs4_sp, hm4_eq, hm3_eq, hs2_mem] using hm
  refine emitToLoc_bodyWp hwf hd hbound (fun rd h => hcore rd (Or.inr h))
    (fun _ _ => hcore b.w0 (Or.inl rfl)) ?_
  intro s' slots' hlen hsb he' hr' hsp' hm'
  exact hk s' slots' hlen hsb he' hr' (hsp'.trans hs4_sp) hm'

private theorem bool_xor_eq (a b : Bool) :
    (BitVec.ofNat 8 a.toNat ^^^ BitVec.ofNat 8 b.toNat) = BitVec.ofNat 8 (a ^^ b).toNat := by
  cases a <;> cases b <;> decide
private theorem bool_and_eq (a b : Bool) :
    (BitVec.ofNat 8 a.toNat &&& BitVec.ofNat 8 b.toNat) = BitVec.ofNat 8 (a && b).toNat := by
  cases a <;> cases b <;> decide
private theorem bool_or_eq (a b : Bool) :
    (BitVec.ofNat 8 a.toNat ||| BitVec.ofNat 8 b.toNat) = BitVec.ofNat 8 (a || b).toNat := by
  cases a <;> cases b <;> decide

private theorem lowerOp_bin_bits {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax n : Nat} {op : CoreAlu}
    (fn : BitVec n → BitVec n → BitVec n) {lhs rhs : Arg K (.bits n)}
    {bvs : List ((u : Ty) × Val u)} {la ra : Arg Val (.bits n)}
    {rw : Regs} {slots : List (BitVec 64)} {G : Mem 64 → Prop} {s : MachSt A}
    {is : List (Instr A)} {d' : Nat} {err : String}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hd : d < dMax) (h6 : 6 ≤ d) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ G) s.mem)
    (hl : denoteArg bvs lhs = some la) (hrhs : denoteArg bvs rhs = some ra)
    (hlo : (do
      let some w := Width.ofBits? n | .error err
      .ok (← lowerBinBits b sb d (locOf b sb d) op w lhs rhs, d + 1)) = .ok (is, d'))
    (hmatch : ∀ w (hn : n = w.bits) (x y : BitVec w.bits),
      op.eval w x y = (fn (x.cast hn.symm) (y.cast hn.symm)).cast hn)
    (hk : ∀ s' (slots' : List (BitVec 64)), d' = d + 1 →
      slots'.length = slots.length → (∀ j < sb, slots'[j]? = slots[j]?) →
      EnvRel b sb d' (⟨.bits n, fn la.val ra.val⟩ :: bvs) s' →
      WordRegsRel b rw s' → s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem → Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  cases hw : Width.ofBits? n with
  | none => simp [hw] at hlo
  | some w =>
    simp only [hw] at hlo
    cases h' : lowerBinBits b sb d (locOf b sb d) op w lhs rhs <;> rw [h'] at hlo; · cases hlo
    cases hlo; have hnw := width_ofBits?_eq hw
    refine lowerBinBits_bodyWp hwf hd h6 hbound he hr hm hl hrhs (fun h => by cases h)
      h' (fun aBV bBV hab old => ?_) (fun s' slots' => hk s' slots' rfl)
    obtain ⟨ha_eq, hb_eq⟩ := hab hnw; subst hnw
    rw [ha_eq, hb_eq, hmatch w rfl _ _]; exact valHolds64_bits_writeSub hawf w old _

private theorem lowerOp_bin_bool {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax : Nat} {op : CoreAlu}
    (fn : Bool → Bool → Bool) {lhs rhs : Arg K .bool}
    {bvs : List ((u : Ty) × Val u)} {la ra : Arg Val .bool}
    {rw : Regs} {slots : List (BitVec 64)} {G : Mem 64 → Prop} {s : MachSt A}
    {is : List (Instr A)} {d' : Nat}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hd : d < dMax) (h6 : 6 ≤ d) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ G) s.mem)
    (hl : denoteArg bvs lhs = some la) (hrhs : denoteArg bvs rhs = some ra)
    (hlo : (do .ok (← lowerBinBits b sb d (locOf b sb d) op .w8 lhs rhs, d + 1)) = .ok (is, d'))
    (hmatch : ∀ x y : Bool, op.eval .w8 (BitVec.ofNat 8 x.toNat) (BitVec.ofNat 8 y.toNat) =
      BitVec.ofNat 8 (fn x y).toNat)
    (hk : ∀ s' (slots' : List (BitVec 64)), d' = d + 1 →
      slots'.length = slots.length → (∀ j < sb, slots'[j]? = slots[j]?) →
      EnvRel b sb d' (⟨.bool, fn la.val ra.val⟩ :: bvs) s' →
      WordRegsRel b rw s' → s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem → Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  cases h' : lowerBinBits b sb d (locOf b sb d) op .w8 lhs rhs <;> rw [h'] at hlo; · cases hlo
  cases hlo
  refine lowerBinBits_bodyWp hwf hd h6 hbound he hr hm hl hrhs (fun _ => rfl)
    h' (fun aBV bBV hab old => ?_) (fun s' slots' => hk s' slots' rfl)
  rcases hab with ⟨_, ha_eq, hb_eq⟩
  have ha' : aBV = BitVec.ofNat 8 la.val.toNat := by
    simpa [Width.bits, BitVec.setWidth_eq] using ha_eq
  have hb' : bBV = BitVec.ofNat 8 ra.val.toNat := by
    simpa [Width.bits, BitVec.setWidth_eq] using hb_eq
  dsimp only [ValHolds64]; rw [ha', hb', hmatch la.val ra.val]; exact hawf.writeSub_setWidth .w8 _ _

private theorem wordRegsRel_upd_ge6 {A : Arch} {b : WordRegBind A} (hwf : b.Wf) {rw : Regs}
    {s s' : MachSt A} (hr : WordRegsRel b rw s) {sb d : Nat} (h6 : 6 ≤ d) {rd : A.Reg}
    (hl : locOf b sb d = .gpr rd) (hne : ∀ q, q ≠ rd → s'.gpr q = s.gpr q) :
    WordRegsRel b rw s' := by
  have hneq : ∀ {w : A.Reg}, w ∈ b.wordRegs → w ≠ rd :=
    fun hw => wordRegs_ne_locOf_ge6 hwf h6 hl hw
  exact ⟨(hne _ (hneq (by simp [WordRegBind.wordRegs]))).trans hr.1,
    (hne _ (hneq (by simp [WordRegBind.wordRegs]))).trans hr.2.1,
    (hne _ (hneq (by simp [WordRegBind.wordRegs]))).trans hr.2.2.1,
    (hne _ (hneq (by simp [WordRegBind.wordRegs]))).trans hr.2.2.2.1,
    (hne _ (hneq (by simp [WordRegBind.wordRegs]))).trans hr.2.2.2.2.1,
    (hne _ (hneq (by simp [WordRegBind.wordRegs]))).trans hr.2.2.2.2.2⟩

private theorem lowerOp_unary1_bodyWp {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax : Nat} {t resT : Ty} {x : Arg K t}
    {bvs : List ((u : Ty) × Val u)} {xa : Arg Val t} {rw : Regs}
    {slots : List (BitVec 64)} {G : Mem 64 → Prop} {s : MachSt A} (resVal : Val resT)
    (mkIns : A.Reg → A.Reg → Instr A)
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hd : d < dMax) (h6 : 6 ≤ d) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ G) s.mem)
    (hx : denoteArg bvs x = some xa)
    {ca : List (Instr A)} {rx : A.Reg}
    (hload : loadArgToGpr b sb d b.w1 x = .ok (ca, rx))
    (hstep : ∀ s1 rd, ValHolds64 t xa.val (s1.gpr rx) →
      (rd = b.w0 ∨ locOf b sb d = .gpr rd) →
      ∀ {K1 : MachSt A → Prop},
      (∀ s', ValHolds64 resT resVal (s'.gpr rd) →
        (∀ q, q ≠ rd → s'.gpr q = s1.gpr q) → s'.mem = s1.mem → K1 s') →
      bodyWp A symAddr [mkIns rd rx] K1 Ψ H s1)
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length → (∀ j < sb, slots'[j]? = slots[j]?) →
      EnvRel b sb (d + 1) (⟨resT, resVal⟩ :: bvs) s' →
      WordRegsRel b rw s' → s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem → Kpost s') :
    bodyWp A symAddr
      (ca ++ emitToLoc b.w0 (locOf b sb d) fun rd => [mkIns rd rx]) Kpost Ψ H s := by
  have hwk := w_mem_workRegs b; have hwsp := work_not_sp hwf
  refine bodyWp_append ca _ _ (loadArgToGpr_bodyWp hwf hwk.2.1 he hx hm hload ?_)
  intro s1 hs1_ne hv1 hm1 he1
  have hsp1 : s1.gpr A.abi.sp = s.gpr A.abi.sp := hs1_ne A.abi.sp hwsp.2.2.1.symm
  have hr1 := wordRegsRel_updWork hwf hr b.w1 hwk.2.1 hs1_ne
  have hm1' : (array64 (s1.gpr A.abi.sp) slots ⋆ G) s1.mem := by simpa [hsp1, hm1] using hm
  have hcore : ∀ rd (hrd : rd = b.w0 ∨ locOf b sb d = .gpr rd),
      bodyWp A symAddr [mkIns rd rx] (fun s' =>
        ValHolds64 resT resVal (s'.gpr rd) ∧ s'.gpr A.abi.sp = s1.gpr A.abi.sp ∧
        EnvRel b sb d bvs s' ∧ WordRegsRel b rw s' ∧
        ∃ slots' : List (BitVec 64), slots'.length = slots.length ∧
          (∀ j < sb, slots'[j]? = slots[j]?) ∧
          (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem) Ψ H s1 := by
    intro rd hrd; refine hstep s1 rd hv1 hrd fun s' hv' hne hm' => ?_
    have hsp_rd : A.abi.sp ≠ rd := by
      rcases hrd with rfl | hlrd
      · exact hwsp.2.1.symm
      · exact (locOf_gpr_ne_sp hwf sb d hlrd).symm
    have hspr : s'.gpr A.abi.sp = s1.gpr A.abi.sp := hne A.abi.sp hsp_rd
    refine ⟨hv', hspr, ?_, ?_, slots, rfl, fun _ _ => rfl, by simpa [hm', hspr] using hm1'⟩
    · refine envRel_map_loc (fun i hi item _ h => ?_) he1
      cases hl : locOf b sb (d - 1 - i) with
      | gpr r =>
        have hr_ne : r ≠ rd := by
          rcases hrd with rfl | hlrd
          · exact (locOf_gpr_ne_work hwf sb _ hl).2.1
          · intro e; subst e; have := locOf_gpr_inj hwf sb (d - 1 - i) d hl hlrd; omega
        simpa [LocHolds, hl, hne r hr_ne] using h
      | slot k => simpa [LocHolds, hl, hspr, hm'] using h
    · rcases hrd with rfl | hlrd
      · exact wordRegsRel_updWork hwf hr1 b.w0 hwk.1 hne
      · exact wordRegsRel_upd_ge6 hwf hr1 h6 hlrd hne
  refine emitToLoc_bodyWp hwf hd hbound (fun rd h => hcore rd (Or.inr h))
    (fun _ _ => hcore b.w0 (Or.inl rfl)) ?_
  intro s' slots' hlen hsb he' hr' hsp' hm'
  exact hk s' slots' hlen hsb he' hr' (hsp'.trans hsp1) hm'

private theorem isSome_ofBits?_bounds {n : Nat} (h : (Width.ofBits? n).isSome = true) :
    0 < n ∧ n ≤ 64 := by
  cases h0 : Width.ofBits? n <;> simp [h0] at h
  rw [width_ofBits?_eq h0]; exact ⟨Width.bits_pos _, Width.bits_le_64 _⟩

private theorem bv_sext_eq64 {m : Nat} (hm : m = 64) (v : BitVec m) (g : BitVec 64)
    (h : g.setWidth m = v) : g.setWidth 64 = v.signExtend 64 := by
  subst hm; simpa [BitVec.signExtend_eq] using h

theorem lowerOp_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax : Nat} {ts : List Ty} {op : Op K ts}
    {bvs : List ((u : Ty) × Val u)} {args' : Tup (Arg Val) _} {rw : Regs}
    {slots : List (BitVec 64)} {G : Mem 64 → Prop} {s : MachSt A} {is : List (Instr A)}
    {d' : Nat} {Q : Tup Val ts → Prop}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hd : d < dMax) (h6 : 6 ≤ d) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ G) s.mem)
    (hden : denoteArgs bvs op.args = some args')
    (hop : op.code.wp (vals args') Q)
    (hlo : lowerOp b sb d op = .ok (is, d'))
    (hk : ∀ (rvs : Tup Val ts) s' (slots' : List (BitVec 64)),
      Q rvs → d' = d + ts.length →
      slots'.length = slots.length → (∀ j < sb, slots'[j]? = slots[j]?) →
      EnvRel b sb d' (pushTup rvs bvs) s' → WordRegsRel b rw s' →
      s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem → Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  rcases op with ⟨code, args⟩
  have hwk := w_mem_workRegs b; have hne := wordRegBind_work_ne hwf; have hwsp := work_not_sp hwf
  have hsl : ∀ lvl < d, ∀ j, locOf b sb lvl = .slot j → j < slots.length :=
    envRel_slots_bound b (Nat.le_of_lt hd) hbound
  cases code with
  | copy t =>
    rcases args with ⟨x, ⟨⟩⟩; have hx := denoteArgs_one hden
    dsimp only [lowerOp] at hlo; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at hlo
      cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at hlo; · cases hlo
      cases hlo
      exact lowerOp_unary1_bodyWp hwf (resT := .bool) args'.1.val (fun rd rx => .mov .w8 rd rx)
        hd h6 hbound he hr hm hx h1
        (fun s1 rd hv1 _ _ h => instrWp_mov (h _ (by
          dsimp only [ValHolds64, Width.bits] at hv1 ⊢
          rw [MachSt.gpr_setGprW_same, hawf.writeSub_setWidth .w8]; exact hv1)
          (fun q hq => MachSt.gpr_setGprW_ne _ _ _ hq) rfl))
        (fun s' sl hn hb he' hr' hs hm' => hk _ s' sl hop rfl hn hb he' hr' hs hm')
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at hlo
      cases hw : Width.ofBits? n with
      | none => simp [hw] at hlo
      | some w =>
        simp only [hw] at hlo; have hnw := width_ofBits?_eq hw; subst hnw
        cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at hlo; · cases hlo
        cases hlo
        exact lowerOp_unary1_bodyWp hwf (resT := .bits w.bits) args'.1.val
          (fun rd rx => .mov w rd rx) hd h6 hbound he hr hm hx h1
          (fun s1 rd hv1 _ _ h => instrWp_mov (h _ ⟨w.bits_le_64, by
            rw [MachSt.gpr_setGprW_same, hawf.writeSub_setWidth]; exact hv1.2⟩
            (fun q hq => MachSt.gpr_setGprW_ne _ _ _ hq) rfl))
          (fun s' sl hn hb he' hr' hs hm' => hk _ s' sl hop rfl hn hb he' hr' hs hm')
    | float _ | pair _ _ => dsimp only [lowerOpCode] at hlo; cases hlo
  | add t =>
    rcases args with ⟨x, y, ⟨⟩⟩; have ⟨hx, hy⟩ := denoteArgs_two hden
    dsimp only [lowerOp, lowerOpCode] at hlo; cases t with
    | bool =>
      exact lowerOp_bin_bool hawf hwf (· ^^ ·) hd h6 hbound he hr hm hx hy hlo bool_xor_eq
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | bits n =>
      exact lowerOp_bin_bits hawf hwf (· + ·) hd h6 hbound he hr hm hx hy hlo
        (fun _ hn _ _ => by subst hn; rfl)
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | float _ | pair _ _ => cases hlo
  | sub t =>
    rcases args with ⟨x, y, ⟨⟩⟩; have ⟨hx, hy⟩ := denoteArgs_two hden
    dsimp only [lowerOp, lowerOpCode] at hlo; cases t with
    | bool =>
      exact lowerOp_bin_bool hawf hwf (· ^^ ·) hd h6 hbound he hr hm hx hy hlo bool_xor_eq
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | bits n =>
      exact lowerOp_bin_bits hawf hwf (· - ·) hd h6 hbound he hr hm hx hy hlo
        (fun _ hn _ _ => by subst hn; rfl)
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | float _ | pair _ _ => cases hlo
  | mul t =>
    rcases args with ⟨x, y, ⟨⟩⟩; have ⟨hx, hy⟩ := denoteArgs_two hden
    dsimp only [lowerOp, lowerOpCode] at hlo; cases t with
    | bool =>
      exact lowerOp_bin_bool hawf hwf (· && ·) hd h6 hbound he hr hm hx hy hlo bool_and_eq
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | bits n =>
      exact lowerOp_bin_bits hawf hwf (· * ·) hd h6 hbound he hr hm hx hy hlo
        (fun _ hn _ _ => by subst hn; rfl)
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | float _ | pair _ _ => cases hlo
  | and t =>
    rcases args with ⟨x, y, ⟨⟩⟩; have ⟨hx, hy⟩ := denoteArgs_two hden
    dsimp only [lowerOp, lowerOpCode] at hlo; cases t with
    | bool =>
      exact lowerOp_bin_bool hawf hwf (· && ·) hd h6 hbound he hr hm hx hy hlo bool_and_eq
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | bits n =>
      exact lowerOp_bin_bits hawf hwf (· &&& ·) hd h6 hbound he hr hm hx hy hlo
        (fun _ hn _ _ => by subst hn; rfl)
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | float _ | pair _ _ => cases hlo
  | or t =>
    rcases args with ⟨x, y, ⟨⟩⟩; have ⟨hx, hy⟩ := denoteArgs_two hden
    dsimp only [lowerOp, lowerOpCode] at hlo; cases t with
    | bool =>
      exact lowerOp_bin_bool hawf hwf (· || ·) hd h6 hbound he hr hm hx hy hlo bool_or_eq
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | bits n =>
      exact lowerOp_bin_bits hawf hwf (· ||| ·) hd h6 hbound he hr hm hx hy hlo
        (fun _ hn _ _ => by subst hn; rfl)
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | float _ | pair _ _ => cases hlo
  | xor t =>
    rcases args with ⟨x, y, ⟨⟩⟩; have ⟨hx, hy⟩ := denoteArgs_two hden
    dsimp only [lowerOp, lowerOpCode] at hlo; cases t with
    | bool =>
      exact lowerOp_bin_bool hawf hwf (· ^^ ·) hd h6 hbound he hr hm hx hy hlo bool_xor_eq
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | bits n =>
      exact lowerOp_bin_bits hawf hwf (· ^^^ ·) hd h6 hbound he hr hm hx hy hlo
        (fun _ hn _ _ => by subst hn; rfl)
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | float _ | pair _ _ => cases hlo
  | shl t =>
    rcases args with ⟨x, y, ⟨⟩⟩; have ⟨hx, hy⟩ := denoteArgs_two hden
    dsimp only [lowerOp, lowerOpCode] at hlo; cases t with
    | bits n =>
      exact lowerOp_bin_bits hawf hwf (fun x y => x <<< (y.toNat % n)) hd h6 hbound he hr hm hx hy
        hlo (fun _ hn _ _ => by subst hn; rfl)
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | bool | float _ | pair _ _ => cases hlo
  | lshr t =>
    rcases args with ⟨x, y, ⟨⟩⟩; have ⟨hx, hy⟩ := denoteArgs_two hden
    dsimp only [lowerOp, lowerOpCode] at hlo; cases t with
    | bits n =>
      exact lowerOp_bin_bits hawf hwf (fun x y => x >>> (y.toNat % n)) hd h6 hbound he hr hm hx hy
        hlo (fun _ hn _ _ => by subst hn; rfl)
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | bool | float _ | pair _ _ => cases hlo
  | ashr t =>
    rcases args with ⟨x, y, ⟨⟩⟩; have ⟨hx, hy⟩ := denoteArgs_two hden
    dsimp only [lowerOp, lowerOpCode] at hlo; cases t with
    | bits n =>
      exact lowerOp_bin_bits hawf hwf (fun x y => BitVec.sshiftRight x (y.toNat % n))
        hd h6 hbound he hr hm hx hy hlo (fun _ hn _ _ => by subst hn; rfl)
        (fun s' sl hd' hn hb he' hr' hs hm' => hk _ s' sl hop hd' hn hb he' hr' hs hm')
    | bool | float _ | pair _ _ => cases hlo
  | neg t =>
    rcases args with ⟨x, ⟨⟩⟩; have hx := denoteArgs_one hden
    dsimp only [lowerOp] at hlo; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at hlo
      cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at hlo; · cases hlo
      cases hlo
      exact lowerOp_unary1_bodyWp hwf (resT := .bool) args'.1.val (fun rd rx => .mov .w8 rd rx)
        hd h6 hbound he hr hm hx h1
        (fun s1 rd hv1 _ _ h => instrWp_mov (h _ (by
          dsimp only [ValHolds64, Width.bits] at hv1 ⊢
          rw [MachSt.gpr_setGprW_same, hawf.writeSub_setWidth .w8]; exact hv1)
          (fun q hq => MachSt.gpr_setGprW_ne _ _ _ hq) rfl))
        (fun s' sl hn hb he' hr' hs hm' => hk _ s' sl hop rfl hn hb he' hr' hs hm')
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at hlo
      cases hw : Width.ofBits? n with
      | none => simp [hw] at hlo
      | some w =>
        simp only [hw] at hlo; have hnw := width_ofBits?_eq hw; subst hnw
        cases h1 : loadArgToGpr b sb d b.w2 x <;> rw [h1] at hlo; · cases hlo
        cases hlo; rename_i p; rcases p with ⟨ca, rx⟩
        refine instrWp_movi ?_
        let s1 := s.setGpr b.w1 0#64
        have hsp1 : s1.gpr A.abi.sp = s.gpr A.abi.sp := MachSt.gpr_setGpr_ne _ _ hwsp.2.2.1.symm
        have hm1 : (array64 (s1.gpr A.abi.sp) slots ⋆ G) s1.mem := by simpa [s1, hsp1] using hm
        have he1 : EnvRel b sb d bvs s1 := (envRel_setGpr_work hwf sb d bvs s hwk.2.1 _).mpr he
        have hr1 : WordRegsRel b rw s1 :=
          (wordRegsRel_setGpr_work hwf rw s (Or.inl hwk.2.1) _).mpr hr
        refine bodyWp_append ca _ _ (loadArgToGpr_bodyWp hwf hwk.2.2 he1 hx hm1 h1 ?_)
        intro s2 hs2_ne hv2 hm2 he2
        have hs2_w1 : s2.gpr b.w1 = 0#64 :=
          (hs2_ne b.w1 hne.2.2.2.2.2).trans (MachSt.gpr_setGpr_same _ _ _)
        have hsp2 : s2.gpr A.abi.sp = s.gpr A.abi.sp :=
          (hs2_ne A.abi.sp hwsp.2.2.2.symm).trans hsp1
        have hm2' : (array64 (s2.gpr A.abi.sp) slots ⋆ G) s2.mem := by simpa [hsp2, hm2] using hm
        have hr2 := wordRegsRel_updWork hwf hr1 b.w2 hwk.2.2 hs2_ne
        have hcore : ∀ rd (hrd : rd = b.w0 ∨ locOf b sb d = .gpr rd),
            bodyWp A symAddr [.alu .sub w rd b.w1 (.reg rx) false] (fun s' =>
              ValHolds64 (.bits w.bits) (lift1 (- ·) id (.bits w.bits) args'.1.val) (s'.gpr rd) ∧
              s'.gpr A.abi.sp = s2.gpr A.abi.sp ∧ EnvRel b sb d bvs s' ∧ WordRegsRel b rw s' ∧
              ∃ slots' : List (BitVec 64), slots'.length = slots.length ∧
                (∀ j < sb, slots'[j]? = slots[j]?) ∧
                (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem) Ψ H s2 := by
          intro rd hrd; refine instrWp_alu ?_
          have hsp_rd : A.abi.sp ≠ rd := by
            rcases hrd with rfl | hlrd
            · exact hwsp.2.1.symm
            · exact (locOf_gpr_ne_sp hwf sb d hlrd).symm
          refine ⟨⟨w.bits_le_64, ?_⟩, MachSt.gpr_setGprW_ne _ _ _ hsp_rd, ?_, ?_,
            slots, rfl, fun _ _ => rfl, by simpa [MachSt.gpr_setGprW_ne _ _ _ hsp_rd] using hm2'⟩
          · simp only [MachSt.gpr_setFlags, MachSt.gpr_setGprW_same, hawf.writeSub_setWidth,
              CoreAlu.eval, Src.evalW, Src.eval, Width.bits, hs2_w1, lift1]
            rw [hv2.2, BitVec.setWidth_zero, BitVec.zero_sub]
          · rcases hrd with rfl | hlrd
            · exact (envRel_setGprW_work hwf sb d bvs s2 w hwk.1 _).mpr he2
            · exact envRel_setGpr_new hwf hlrd _ he2
          · rcases hrd with rfl | hlrd
            · exact (wordRegsRel_setGprW_work hwf rw s2 w (Or.inl hwk.1) _).mpr hr2
            · exact (wordRegsRel_setGprW_ge6 hwf rw s2 w h6 hlrd _).mpr hr2
        refine emitToLoc_bodyWp hwf hd hbound (fun rd h => hcore rd (Or.inr h))
          (fun _ _ => hcore b.w0 (Or.inl rfl)) ?_
        intro s' slots' hlen hsb he' hr' hsp' hm'
        exact hk _ s' slots' hop rfl hlen hsb he' hr' (hsp'.trans hsp2) hm'
    | float _ | pair _ _ => dsimp only [lowerOpCode] at hlo; cases hlo
  | not t =>
    rcases args with ⟨x, ⟨⟩⟩; have hx := denoteArgs_one hden
    dsimp only [lowerOp] at hlo; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at hlo
      cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at hlo; · cases hlo
      cases hlo
      exact lowerOp_unary1_bodyWp hwf (resT := .bool) (!args'.1.val)
        (fun rd rx => .alu .xor .w8 rd rx (.imm 1#64) false) hd h6 hbound he hr hm hx h1
        (fun s1 rd hv1 _ _ h => instrWp_alu (h _ (by
          dsimp only [ValHolds64] at hv1 ⊢
          rw [MachSt.gpr_setFlags, MachSt.gpr_setGprW_same, hawf.writeSub_setWidth .w8]
          simp only [CoreAlu.eval, Src.evalW, Src.eval, Width.bits]
          rw [hv1]; cases args'.1.val <;> decide)
          (fun q hq => MachSt.gpr_setGprW_ne _ _ _ hq) rfl))
        (fun s' sl hn hb he' hr' hs hm' => hk _ s' sl hop rfl hn hb he' hr' hs hm')
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at hlo
      cases hw : Width.ofBits? n with
      | none => simp [hw] at hlo
      | some w =>
        simp only [hw] at hlo; have hnw := width_ofBits?_eq hw; subst hnw
        cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at hlo; · cases hlo
        cases hlo
        exact lowerOp_unary1_bodyWp hwf (resT := .bits w.bits) (~~~args'.1.val)
          (fun rd rx => .alu .xor w rd rx (.imm (maskOfBits64 w.bits)) false)
          hd h6 hbound he hr hm hx h1
          (fun s1 rd hv1 _ _ h => instrWp_alu (h _ ⟨w.bits_le_64, by
            simp only [MachSt.gpr_setFlags, MachSt.gpr_setGprW_same, hawf.writeSub_setWidth,
              CoreAlu.eval, Src.evalW, Src.eval, maskOfBits64_setWidth, hv1.2]
            exact BitVec.xor_allOnes⟩ (fun q hq => MachSt.gpr_setGprW_ne _ _ _ hq) rfl))
          (fun s' sl hn hb he' hr' hs hm' => hk _ s' sl hop rfl hn hb he' hr' hs hm')
    | float _ | pair _ _ => dsimp only [lowerOpCode] at hlo; cases hlo
  | cmp o t m hm_ty =>
    subst hm_ty; rcases args with ⟨x, y, ⟨⟩⟩; have ⟨hx, hy⟩ := denoteArgs_two hden
    dsimp only [lowerOp] at hlo; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at hlo
      cases hlo' : lowerCmpBits b sb d (locOf b sb d) (normBoolCmp o) .w8 x y <;>
        rw [hlo'] at hlo; · cases hlo
      cases hlo
      refine lowerCmpBits_bodyWp hawf hwf hd h6 hbound he hr hm hx hy (fun _ => rfl) hlo'
        (fun aBV bBV hab => ?_)
        (fun s' sl hn hb he' hr' hs hm' => hk _ s' sl hop rfl hn hb he' hr' hs hm')
      rcases hab with ⟨_, ha_eq, hb_eq⟩
      have ha' : aBV = BitVec.ofNat 8 args'.1.val.toNat := by
        simpa [Width.bits, BitVec.setWidth_eq] using ha_eq
      have hb' : bBV = BitVec.ofNat 8 args'.2.1.val.toNat := by
        simpa [Width.bits, BitVec.setWidth_eq] using hb_eq
      rw [ha', hb']; exact normBoolCmp_eq o _ _
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at hlo
      cases hw : Width.ofBits? n with
      | none => simp [hw] at hlo
      | some w =>
        simp only [hw] at hlo; have hnw := width_ofBits?_eq hw; subst hnw
        cases hlo' : lowerCmpBits b sb d (locOf b sb d) o w x y <;> rw [hlo'] at hlo; · cases hlo
        cases hlo
        refine lowerCmpBits_bodyWp hawf hwf hd h6 hbound he hr hm hx hy (fun h => by cases h)
          hlo' (fun _ _ hab => ?_)
          (fun s' sl hn hb he' hr' hs hm' => hk _ s' sl hop rfl hn hb he' hr' hs hm')
        obtain ⟨ha_eq, hb_eq⟩ := hab rfl; rw [ha_eq, hb_eq]; rfl
    | float _ | pair _ _ => dsimp only [lowerOpCode] at hlo; cases hlo
  | select t =>
    rcases args with ⟨c, x, y, ⟨⟩⟩; have ⟨hcD, hxD, hyD⟩ := denoteArgs_three hden
    dsimp only [lowerOp, lowerOpCode, Except.bind] at hlo; split at hlo
    · cases hlo' : lowerSelect b sb d (locOf b sb d) c x y <;> rw [hlo'] at hlo; · cases hlo
      cases hlo
      exact lowerSelect_bodyWp hawf hwf hd h6 hbound he hr hm hcD hxD hyD hlo'
        (fun s' sl hn hb he' hr' hs hm' => hk _ s' sl hop rfl hn hb he' hr' hs hm')
    · cases hlo
  | zext m n =>
    rcases args with ⟨x, ⟨⟩⟩; have hx := denoteArgs_one hden
    dsimp only [lowerOp, lowerOpCode, Except.bind] at hlo; split at hlo
    · rename_i hok; rcases hok with ⟨hmn, hwm, hwn⟩
      have hm64 := (isSome_ofBits?_bounds hwm).2
      have hn64 := (isSome_ofBits?_bounds hwn).2
      cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at hlo; · cases hlo
      cases hlo
      exact lowerOp_unary1_bodyWp hwf (resT := .bits n) (args'.1.val.setWidth n)
        (fun rd rx => .alu .and .w64 rd rx (.imm (maskOfBits64 m)) false)
        hd h6 hbound he hr hm hx h1
        (fun s1 rd hv1 _ _ h => instrWp_alu (h _ ⟨hn64, by
          simp only [MachSt.gpr_setFlags, MachSt.gpr_setGprW_same, hawf.writeSub_w64,
            BitVec.setWidth_eq, CoreAlu.eval, Src.evalW, Src.eval, Width.bits]
          rw [bv64_zext_mask_clean hm64 hmn hn64 _, hv1.2]⟩
          (fun q hq => MachSt.gpr_setGprW_ne _ _ _ hq) rfl))
        (fun s' sl hn hb he' hr' hs hm' => hk _ s' sl hop.2 rfl hn hb he' hr' hs hm')
    · cases hlo
  | sext m n =>
    rcases args with ⟨x, ⟨⟩⟩; have hx := denoteArgs_one hden
    dsimp only [lowerOp, lowerOpCode, Except.bind] at hlo; split at hlo
    · rename_i hok; rcases hok with ⟨hmn, hwm, hwn⟩
      have hm_pos_64 := isSome_ofBits?_bounds hwm
      have hn64 := (isSome_ofBits?_bounds hwn).2
      cases h1 : loadArgInto b sb d b.w1 x <;> rw [h1] at hlo; · cases hlo
      cases hlo; rename_i ca; rw [List.append_assoc]
      refine bodyWp_append ca _ _ (loadArgInto_bodyWp hawf hwf hwk.2.1 he hx hm h1 ?_)
      intro s1 hs1_ne hv1 hm1 he1
      have hsp1 : s1.gpr A.abi.sp = s.gpr A.abi.sp := hs1_ne A.abi.sp hwsp.2.2.1.symm
      have hr1 := wordRegsRel_updWork hwf hr b.w1 hwk.2.1 hs1_ne
      have hm1' : (array64 (s1.gpr A.abi.sp) slots ⋆ G) s1.mem := by simpa [hsp1, hm1] using hm
      have hmid :
          bodyWp A symAddr
            (if m == 64 then [] else
              [.alu .shl .w64 b.w1 b.w1 (.imm (BitVec.ofNat 64 (64 - m))) false,
               .alu .ashr .w64 b.w1 b.w1 (.imm (BitVec.ofNat 64 (64 - m))) false])
            (fun s2 =>
              ValHolds64 (.bits n) (args'.1.val.signExtend n) (s2.gpr b.w1) ∧
              s2.gpr A.abi.sp = s1.gpr A.abi.sp ∧ EnvRel b sb d bvs s2 ∧ WordRegsRel b rw s2 ∧
              (array64 (s2.gpr A.abi.sp) slots ⋆ G) s2.mem) Ψ H s1 := by
        by_cases hm64 : m = 64
        · have hn_eq : n = 64 := by omega
          have hm_b : (m == 64) = true := beq_iff_eq.mpr hm64
          simp only [hm_b, ↓reduceIte]; dsimp only [bodyWp]
          refine ⟨⟨hn64, ?_⟩, rfl, he1, hr1, hm1'⟩
          rw [hn_eq]; exact bv_sext_eq64 hm64 _ _ hv1.2
        · have hbm : (m == 64) = false := beq_false_of_ne hm64
          have hmlt : m < 64 := Nat.lt_of_le_of_ne hm_pos_64.2 hm64
          simp only [hbm, Bool.false_eq_true, ↓reduceIte]
          refine instrWp_alu (instrWp_alu ?_)
          refine ⟨⟨hn64, ?_⟩, by simp [MachSt.gpr_setGprW_ne _ _ _ hwsp.2.2.1.symm], ?_, ?_,
            by simpa [MachSt.gpr_setGprW_ne _ _ _ hwsp.2.2.1.symm] using hm1'⟩
          · simp only [MachSt.gpr_setFlags, MachSt.gpr_setGprW_same, hawf.writeSub_w64,
              BitVec.setWidth_eq, CoreAlu.eval, Src.evalW, Src.eval, Width.bits]
            have hse := bv64_sext_shl_ashr hm_pos_64.1 hmlt hmn hn64 (s1.gpr b.w1)
            dsimp only at hse; rw [hse, hv1.2]
          · simp only [envRel_setFlags]
            rw [envRel_setGprW_work hwf sb d bvs _ .w64 hwk.2.1 _, envRel_setFlags,
                envRel_setGprW_work hwf sb d bvs _ .w64 hwk.2.1 _]; exact he1
          · simp only [wordRegsRel_setFlags]
            rw [wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.2.1) _, wordRegsRel_setFlags,
                wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.2.1) _]; exact hr1
      refine bodyWp_append _ _ _ (bodyWp_mono (fun s2 h2 => ?_) hmid)
      rcases h2 with ⟨hv2, hsp2, he2, hr2, hm2⟩
      cases hloc : locOf b sb d with
      | gpr rd =>
        refine instrWp_mov ?_
        have hsp_rd : A.abi.sp ≠ rd := (locOf_gpr_ne_sp hwf sb d hloc).symm
        refine hk _ _ slots hop.2 rfl rfl (fun _ _ => rfl)
          (envRel_push1 (envRel_setGpr_new hwf hloc _ he2) (by
            dsimp only [LocHolds]; rw [hloc]; dsimp only
            refine ⟨hn64, by simpa [MachSt.gpr_setGprW_same, hawf.writeSub_w64] using hv2.2⟩))
          ((wordRegsRel_setGprW_ge6 hwf rw s2 .w64 h6 hloc _).mpr hr2)
          ((MachSt.gpr_setGprW_ne _ _ _ hsp_rd).trans (hsp2.trans hsp1))
          (by simpa [MachSt.gpr_setGprW_ne _ _ _ hsp_rd, hsp2, hsp1] using hm2)
      | slot k =>
        have hlt : k < slots.length := by
          have ⟨_, hlt0⟩ := locOf_slot_lt b sb d dMax k hd hloc; omega
        have hks : ∀ lvl < d, locOf b sb lvl ≠ .slot k := fun lvl hl heq => by
          have := locOf_inj hwf sb lvl d (heq.trans hloc.symm); omega
        have hst := store_array64 (s2.gpr b.w1) hlt hm2
        refine instrWp_slotSt hst.1 ?_
        refine hk _ _ (slots.set k (s2.gpr b.w1)) hop.2 rfl (by simp [List.length_set])
          (fun j hj => by
            rw [List.getElem?_set_ne (by have := locOf_slot_ge_sb b sb d k hloc; omega)])
          (envRel_push1 (envRel_setSlot_ge hlt hks hsl hm2 (s2.gpr b.w1) he2) (by
            dsimp only [LocHolds]; rw [hloc]; dsimp only
            refine ⟨s2.gpr b.w1, ?_, hv2⟩
            simpa [List.getElem_set_self (by simp; exact hlt)] using
              loadVal_array64 (i := k) (by simpa [List.length_set] using hlt) hst.2))
          ((wordRegsRel_setMem _ _ _ _).mpr hr2) (hsp2.trans hsp1)
          (by simpa [MachSt.mem_setMem] using hst.2)
    · cases hlo
  | trunc m n =>
    rcases args with ⟨x, ⟨⟩⟩; have hx := denoteArgs_one hden
    dsimp only [lowerOp, lowerOpCode, Except.bind] at hlo
    cases hwn : Width.ofBits? n with
    | none => simp [hwn] at hlo
    | some wn =>
      simp only [hwn] at hlo; have hnw := width_ofBits?_eq hwn; subst hnw; split at hlo
      · rename_i hok; rcases hok with ⟨hnm, _⟩
        cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at hlo; · cases hlo
        cases hlo
        exact lowerOp_unary1_bodyWp hwf (resT := .bits wn.bits) (args'.1.val.setWidth wn.bits)
          (fun rd rx => .mov wn rd rx) hd h6 hbound he hr hm hx h1
          (fun s1 rd hv1 _ _ h => instrWp_mov (h _ ⟨wn.bits_le_64, by
            rw [MachSt.gpr_setGprW_same, hawf.writeSub_setWidth, ← hv1.2,
              BitVec.setWidth_setWidth_of_le (s1.gpr _) hnm]⟩
            (fun q hq => MachSt.gpr_setGprW_ne _ _ _ hq) rfl))
          (fun s' sl hn hb he' hr' hs hm' => hk _ s' sl hop.2 rfl hn hb he' hr' hs hm')
      · cases hlo
  | ofBool n =>
    rcases args with ⟨x, ⟨⟩⟩; have hx := denoteArgs_one hden
    dsimp only [lowerOp, lowerOpCode, Except.bind] at hlo; split at hlo
    · rename_i hwn; have hn64 := (isSome_ofBits?_bounds hwn).2
      cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at hlo; · cases hlo
      cases hlo
      exact lowerOp_unary1_bodyWp hwf (resT := .bits n) (BitVec.ofNat n args'.1.val.toNat)
        (fun rd rx => .alu .and .w64 rd rx (.imm 1#64) false) hd h6 hbound he hr hm hx h1
        (fun s1 rd hv1 _ _ h => instrWp_alu (h _ ⟨hn64, by
          simp only [MachSt.gpr_setFlags, MachSt.gpr_setGprW_same, hawf.writeSub_w64,
            BitVec.setWidth_eq, CoreAlu.eval, Src.evalW, Src.eval, Width.bits]
          exact bv_ofBool_eq n hn64 args'.1.val _ hv1⟩
          (fun q hq => MachSt.gpr_setGprW_ne _ _ _ hq) rfl))
        (fun s' sl hn hb he' hr' hs hm' => hk _ s' sl hop rfl hn hb he' hr' hs hm')
    · cases hlo
  | ternlog _ _ | rotl _ | rotr _ | fshl _ | fshr _ | bswap _ | clz _ | cls _ | rbit _
  | ctz _ | popcnt _ | blend _ _ _ | addc _ | subb _ | umulw _ | smulw _ | udiv _ | sdiv _
  | urem _ | srem _ | udiv0 _ | sdiv0 _ | mkpair _ _ | unpair _ _ | bitcast _ _ _ | shufd _ _
  | shufb _ | alignr _ _ | blendw _ _ | sha256rnds2 | sha256msg1 | sha256msg2 | fadd _ | fsub _
  | fmul _ | fdiv _ | ffma _ | fsqrt _ | fneg _ | fabs _ | fcmp _ _ _ _ | fptoui _ _ | fptosi _ _
  | uitofp _ _ | sitofp _ _ | fcvt _ _ =>
    dsimp only [lowerOp, lowerOpCode] at hlo; cases hlo

end LeanQbe.T.Vll
