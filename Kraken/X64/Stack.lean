module

public import Kraken.SeparationMem
import all Kraken.Separation
import all Kraken.Mem

/-!
# Stack cells shared by the x64 calling conventions

The memory a procedure specification talks about at a call, in the separation logic of
`Kraken.Separation` over byte maps `Mem 64`:

* `RetCell ra a`: the 8 bytes at `a` hold the return address `ra`, as `call` wrote them
  (`[rsp]` on entry, under every x64 convention);
* `Owned n a`: `n` bytes at `a` the procedure owns but knows nothing about;
* `Reserve d r`: `d` bytes of free stack just below `r`, not wrapping past address `0`: the
  procedure's *stack reservation* (Bedrock's `reserving` clause). The caller supplies it, the
  procedure may use it, and it comes back as owned bytes. It is exact, not "at least";
* `Shadow r`: the 32 bytes above the return address at `r` that the Windows x64 convention hands
  to the callee (`[rsp + 8, rsp + 40)` on entry).

Kraken has no faulting model, so stack exhaustion cannot be a runtime error; the reservation in the
precondition is the only sound treatment, and the no-wrap bound in `Reserve` is what keeps a caller
near address `0` from handing out bytes at the top of memory.

The cells are `Eq (bs.At a)` with explicit byte lists (`Kraken.SeparationMem`); `Owned` hides the
list existentially, and `Owned.elim`/`Owned.intro` open and close it at a load or store.
-/

public section

open Std
open Std.ExtHashMap

namespace Kraken.Stack

/-! ## Cells -/

/-- The bytes a return address occupies: the slot at `a` holds `ra`, as `call` wrote it. -/
abbrev RetCell (ra : Int64) (a : BitVec 64) : Mem 64 → Prop :=
  Eq ((Int.toBytes 8 ra.toBitVec.toInt).At a)

/-- `n` bytes at `a`, owned, contents unknown. -/
@[expose] def Owned (n : Nat) (a : BitVec 64) : Mem 64 → Prop :=
  fun m => ∃ bs : List UInt8, bs.length = n ∧ m = bs.At a

/-- Open an owned block at the head of a tree into its bytes. -/
theorem Owned.elim {n : Nat} {a : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ Owned n a ⋆ R) : ∃ bs : List UInt8, bs.length = n ∧ (m =⋆ Eq (bs.At a) ⋆ R) :=
  let ⟨x, y, hu, hd, ⟨bs, hl, hx⟩, hy⟩ := h
  ⟨bs, hl, x, y, hu, hd, hx.symm, hy⟩

/-- Forget the contents of a block at the head of a tree. -/
theorem Owned.intro {n : Nat} {a : BitVec 64} {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ Eq (bs.At a) ⋆ R) (hl : bs.length = n) : m =⋆ Owned n a ⋆ R :=
  sep_mono (fun _ hx => ⟨bs, hl, hx.symm⟩) (fun _ h => h) h

theorem Owned.zero (a : BitVec 64) : Owned 0 a = emp := by
  funext m; apply propext; constructor
  · rintro ⟨bs, hl, rfl⟩
    rw [List.length_eq_zero_iff.mp hl]
    simp [List.At, emp]
  · intro h
    refine ⟨[], rfl, ?_⟩
    simp only [emp] at h
    simp [h, List.At]

/-- A block is its two halves. -/
theorem Owned.split (i j : Nat) (a : BitVec 64) (h : i + j ≤ 2 ^ 64) :
    Owned (i + j) a = Owned i a ⋆ Owned j (a + .ofNat 64 i) := by
  funext m; apply propext; constructor
  · rintro ⟨bs, hl, rfl⟩
    have hAt := Mem.At_append_sep (bs.take i) (bs.drop i) a (by simp; omega)
    rw [List.take_append_drop] at hAt
    have hti : (bs.take i).length = i := by simp; omega
    rw [hti] at hAt
    have h2 : (Eq ((bs.take i).At a) ⋆ Eq ((bs.drop i).At (a + .ofNat 64 i))) (bs.At a) := by
      rw [← hAt]
    exact sep_mono (fun _ hx => ⟨_, hti, hx.symm⟩) (fun _ hx => ⟨_, by simp; omega, hx.symm⟩) h2
  · rintro ⟨x, y, hu, hd, ⟨b1, h1, rfl⟩, ⟨b2, h2, rfl⟩⟩
    refine ⟨b1 ++ b2, by simp; omega, ?_⟩
    have hAt := Mem.At_append_sep b1 b2 a (by omega)
    have h3 : (Eq (b1.At a) ⋆ Eq (b2.At (a + .ofNat 64 b1.length))) m := by
      rw [h1]
      exact ⟨_, _, hu, hd, rfl, rfl⟩
    rw [← hAt] at h3
    exact h3.symm

/-! ## The reservation -/

/-- A pure fact on the right of a separating conjunction. -/
private theorem sep_pure_r {P Q : Mem 64 → Prop} {φ : Prop} :
    (P ⋆ fun m => φ ∧ Q m) = fun m => φ ∧ (P ⋆ Q) m := by
  funext m; apply propext; constructor
  · rintro ⟨a, b, h1, h2, ha, hφ, hb⟩; exact ⟨hφ, a, b, h1, h2, ha, hb⟩
  · rintro ⟨hφ, a, b, h1, h2, ha, hb⟩; exact ⟨a, b, h1, h2, ha, hφ, hb⟩

/-- `d` bytes of free stack just below `r`, not wrapping past address `0`. A `def`, so that it moves
as one cell until it is split. -/
@[expose] def Reserve (d : Nat) (r : BitVec 64) : Mem 64 → Prop :=
  fun m => d ≤ r.toNat ∧ Owned d (r - .ofNat 64 d) m

theorem Reserve.le_head {d : Nat} {r : BitVec 64} {K : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ Reserve d r ⋆ K) : d ≤ r.toNat := by
  obtain ⟨_, _, _, _, h1, _⟩ := h; exact h1.1

/-- The bound of a reservation second in a tree, behind one cell (the return address). -/
theorem Reserve.le_second {d : Nat} {r : BitVec 64} {X K : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ X ⋆ (Reserve d r ⋆ K)) : d ≤ r.toNat := by
  obtain ⟨_, _, _, _, _, h2⟩ := h; exact Reserve.le_head h2

/-- The bound of a reservation third in a tree (behind the return address and the shadow space). -/
theorem Reserve.le_third {d : Nat} {r : BitVec 64} {X Y K : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ X ⋆ (Y ⋆ (Reserve d r ⋆ K))) : d ≤ r.toNat := by
  obtain ⟨_, _, _, _, _, h2⟩ := h; exact Reserve.le_second h2

theorem Reserve.zero (r : BitVec 64) : Reserve 0 r = emp := by
  funext m
  simp [Reserve, Owned.zero, Nat.zero_le]

/-- A reservation is its block once the bound is known. -/
theorem Reserve_eq (d : Nat) (r : BitVec 64) (h : d ≤ r.toNat) :
    Reserve d r = Owned d (r - .ofNat 64 d) := by
  funext m; exact propext ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩

/-- The reservation, with `a` bytes carved off its top: the rest is a smaller reservation `a` bytes
lower. Used at a procedure's entry (its own bytes off the top), at a call (the return-address slot
off what is left), and in reverse at its exit. The carved bytes do not carry the bound, hence `h`. -/
theorem Reserve_split (a d : Nat) (r : BitVec 64) (h : a ≤ r.toNat) :
    Reserve (a + d) r = Owned a (r - .ofNat 64 a) ⋆ Reserve d (r - .ofNat 64 a) := by
  have hr : (r - BitVec.ofNat 64 a).toNat = r.toNat - a := by
    rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; have := r.isLt; omega)]
    have := r.isLt
    simp; omega
  unfold Reserve
  rw [sep_pure_r, hr]
  funext m; apply propext
  have e1 : r - BitVec.ofNat 64 (a + d) + BitVec.ofNat 64 d = r - BitVec.ofNat 64 a := by
    bv_omega
  have e2 : r - BitVec.ofNat 64 a - BitVec.ofNat 64 d = r - BitVec.ofNat 64 (a + d) := by
    bv_omega
  have hsplit : ∀ (_ : a + d ≤ 2 ^ 64), Owned (a + d) (r - BitVec.ofNat 64 (a + d)) =
      Owned a (r - BitVec.ofNat 64 a) ⋆ Owned d (r - BitVec.ofNat 64 a - BitVec.ofNat 64 d) := by
    intro hw
    rw [Nat.add_comm a d, Owned.split d a _ (by omega), sep_comm, Nat.add_comm d a, e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, by rw [← hsplit (by have := r.isLt; omega)]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, by rw [hsplit (by have := r.isLt; omega)]; exact h2⟩

/-! ## The Windows x64 shadow space -/

/-- The 32 bytes above the return-address slot at `r`, not wrapping past the top of memory. -/
@[expose] def Shadow (r : BitVec 64) : Mem 64 → Prop :=
  fun m => r.toNat + 40 ≤ 2 ^ 64 ∧ Owned 32 (r + 8) m

theorem Shadow_eq (r : BitVec 64) (h : r.toNat + 40 ≤ 2 ^ 64) : Shadow r = Owned 32 (r + 8) := by
  funext m; exact propext ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩

/-- The bound of a shadow space second in a tree, behind one cell (the return address). -/
theorem Shadow.le_second {r : BitVec 64} {X K : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ X ⋆ (Shadow r ⋆ K)) : r.toNat + 40 ≤ 2 ^ 64 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨h1, _⟩, _⟩ := h; exact h1

/-- The shadow space as the home slot of the first argument (`[rsp + 8]`) and the other three. -/
theorem Shadow_split (r : BitVec 64) (h : r.toNat + 40 ≤ 2 ^ 64) :
    Shadow r = Owned 8 (r + 8) ⋆ Owned 24 (r + 16) := by
  rw [Shadow_eq r h, show (32 : Nat) = 8 + 24 from rfl, Owned.split 8 24 _ (by omega)]
  congr 2
  bv_omega

end Kraken.Stack
