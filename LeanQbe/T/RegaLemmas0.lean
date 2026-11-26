module

public import LeanQbe.T.Rega
public import LeanQbe.T.TargetLemmas

/-!
# `RegaLemmas` Part 0: Slot Splices and `execMovi_spec`

Extracted from `RegaLemmas1.lean` to keep every file well under `2,500` LOC:
* `slice`, `unpack_ofFn`, `packW`, `extract_packW`, `unpack_packW`, `unpack_inj`,
  `splice`, `Splice`.
* `execMovi_spec`: machine `FallsTo` specification for flag-liveness-gated `execMovi`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Rega

/-- The `w.slots` words of `σ` starting at slot `i`. -/
@[expose]
def slice (σ : List (BitVec 64)) (i k : Nat) : List (BitVec 64) := (σ.drop i).take k

/-! ## Slot words and splices -/

theorem unpack_ofFn (w : SlotWidth) (bv : BitVec 512) :
    unpackSlotWords w bv = List.ofFn (n := w.slots) fun n => bv.extractLsb' (64 * n) 64 := by
  cases w <;> simp [unpackSlotWords, List.ofFn_succ]

@[expose]
def packW : List (BitVec 64) → BitVec 512
  | [] => 0
  | x :: xs => x.setWidth 512 ||| (packW xs <<< 64)

theorem extract_packW : ∀ (xs : List (BitVec 64)) (n : Nat) (h : n < xs.length), n < 8 →
    (packW xs).extractLsb' (64 * n) 64 = xs[n]
  | [], _, h, _ => by simp at h
  | x :: xs, 0, _, _ => by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp [packW, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hj]
    omega
  | x :: xs, n + 1, h, h8 => by
    have hn : n < xs.length := by simp at h; omega
    have ih := extract_packW xs n hn (by omega)
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    show _ = (xs[n]'hn).getLsbD j
    rw [← ih]
    simp [packW, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hj]
    simp [show 64 * (n + 1) + j < 512 by omega, show ¬ 64 * (n + 1) + j < 64 by omega,
      show 64 * (n + 1) + j - 64 = 64 * n + j by omega,
      BitVec.getLsbD_of_ge x _ (by omega : 64 ≤ 64 * (n + 1) + j)]

theorem unpack_packW {w : SlotWidth} {ws : List (BitVec 64)} (h : ws.length = w.slots) :
    unpackSlotWords w (packW ws) = ws := by
  rw [unpack_ofFn]; apply List.ext_getElem (by simp [h])
  intro n h1 h2; simp only [List.getElem_ofFn]
  exact extract_packW ws n h2 (by simp at h1; have := SlotWidth.slots_le_eight w; omega)

theorem unpack_inj {w : SlotWidth} {bv bv' : BitVec 512}
    (h : unpackSlotWords w bv = unpackSlotWords w bv') :
    bv.setWidth w.bits = bv'.setWidth w.bits := by
  rw [unpack_ofFn, unpack_ofFn] at h; apply BitVec.eq_of_getLsbD_eq; intro j hj
  have hb := SlotWidth.bits_eq_64_mul_slots w
  have hn : j / 64 < w.slots := by omega
  have e := congrArg (fun l => l[j / 64]?) h
  simp [hn] at e
  have e2 := congrArg (fun x => BitVec.getLsbD x (j % 64)) e
  have hj' : j < 64 * w.slots := by omega
  simp [hj', Nat.mod_lt] at e2 ⊢; have : 64 * (j / 64) + j % 64 = j := by omega
  rw [this] at e2; exact e2

@[expose]
def splice (σ : List (BitVec 64)) (i k : Nat) (ws : List (BitVec 64)) : List (BitVec 64) :=
  σ.take i ++ ws ++ σ.drop (i + k)

section Splice
variable {σ ws : List (BitVec 64)} {i k : Nat}

theorem length_splice (h : i + k ≤ σ.length) (hw : ws.length = k) :
    (splice σ i k ws).length = σ.length := by
  simp [splice, hw]; omega

theorem getElem?_splice (h : i + k ≤ σ.length) (hw : ws.length = k) (j : Nat) :
    (splice σ i k ws)[j]? =
      if j < i then σ[j]? else if j < i + k then ws[j - i]? else σ[j]? := by
  unfold splice; have hi : (σ.take i).length = i := by simp; omega
  split
  · rw [List.append_assoc, List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt (by omega)]
  · rw [List.append_assoc, List.getElem?_append_right (by omega), hi]
    split
    · rw [List.getElem?_append_left (by omega)]
    · rw [List.getElem?_append_right (by omega), List.getElem?_drop, hw]; congr 1; omega

theorem getElem?_slice (n : Nat) : (slice σ i k)[n]? = if n < k then σ[i + n]? else none := by
  simp only [slice, List.getElem?_take, List.getElem?_drop]

theorem slice_splice_self (h : i + k ≤ σ.length) (hw : ws.length = k) :
    slice (splice σ i k ws) i k = ws := by
  apply List.ext_getElem?; intro n; rw [getElem?_slice, getElem?_splice h hw]; split
  · simp only [show ¬ (i + n < i) by omega, show i + n < i + k by omega, ↓reduceIte]
    congr 1; omega
  · rw [List.getElem?_eq_none (by omega)]

theorem slice_splice_disj (h : i + k ≤ σ.length) (hw : ws.length = k) {j kj : Nat}
    (hd : j + kj ≤ i ∨ i + k ≤ j) : slice (splice σ i k ws) j kj = slice σ j kj := by
  apply List.ext_getElem?; intro n; rw [getElem?_slice, getElem?_slice, getElem?_splice h hw]
  split; split; rfl; simp only [show ¬ (j + n < i + k) by omega, ↓reduceIte]; rfl

theorem getElem?_splice_disj (h : i + k ≤ σ.length) (hw : ws.length = k) {j : Nat}
    (hd : j < i ∨ i + k ≤ j) : (splice σ i k ws)[j]? = σ[j]? := by
  rw [getElem?_splice h hw]; split; rfl; simp only [show ¬ (j < i + k) by omega, ↓reduceIte]

theorem slice_length (h : i + k ≤ σ.length) : (slice σ i k).length = k := by
  simp [slice]; omega

theorem splice_slice : splice σ i k (slice σ i k) = σ := by
  simp only [splice, slice, List.append_assoc]
  rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]

theorem slice_one (h : i < σ.length) : slice σ i 1 = [σ[i]] := by
  apply List.ext_getElem?; intro n; rw [getElem?_slice]
  rcases n with _ | n <;> simp [List.getElem?_eq_getElem h]
end Splice

theorem execMovi_spec {T : Target} {h : T.mach.Host} {k : Nat}
    {st : SymState T.toIsa} {deadHint : Bool} {d : T.Reg} {c : BitVec 64}
    {s : T.mach.MData} {post : T.mach.State → Prop} :
    T.mach.FallsTo T.gpr.condReads h k (execMovi T.toIsa st deadHint d c).1
      (d :: T.frame.scratch) [] (execMovi T.toIsa st deadHint d c).2 s
      (fun s' => T.mach.getGpr s' d = c ∧ T.mach.mem s' = T.mach.mem s) post := by
  unfold execMovi
  cases hmd : T.gpr.moviDeadFlags? with
  | none => exact T.gprSpec.movi_spec
  | some fn =>
    by_cases hcond : ((st.flags.isNone && !stHasFlagReg st.regs) || deadHint) = true
    · simp only [hcond, ↓reduceIte]; exact T.gprSpec.moviDeadFlags?_spec hmd
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]; exact T.gprSpec.movi_spec

end Rega
end LeanQbe.T
