module

public import Kraken.SeparationMem
public import Kraken.X64.Semantics
import all Kraken.Separation
import all Kraken.Mem

/-!
# Model for the x64 stack

Certain stack conventions are required by the hardware (e.g., `call` and `ret` consume
a stack slot); other conventions are common among the various calling conventions
(rsp+8 is generally 16-byte aligned on procedure entry). We also model a procedure
reserving the stack space required for its callee.

* `RetCell ra a`: the 8 bytes at `a` hold the return address `ra`;
* `Owned n a`: `n` bytes at `a` the procedure owns but knows nothing about;
* `Reserve d r`: the `d` bytes of free stack just below `r`: the procedure's *stack reservation*
  (Bedrock's `reserving` clause). The caller supplies it for use by the callee, and it comes
  back as owned bytes. It is an exact size;
* `Shadow r`: the 32 bytes above the return address at `r` that the Windows x64 convention hands
  to the callee (`[rsp + 8, rsp + 40)` on entry).
-/

public section

open Std
open Std.ExtHashMap

namespace Kraken.X64.Stack

/-- The slot at `a` holds return address `ra`. -/
abbrev RetCell (ra : Int64) (a : BitVec 64) : Mem 64 → Prop :=
  Eq ((Int.toBytes 8 ra.toBitVec.toInt).At a)

/-- `n` bytes at `a`, owned, contents unknown. -/
@[expose] def Owned (n : Nat) (a : BitVec 64) : Mem 64 → Prop :=
  fun m => ∃ bs : List UInt8, bs.length = n ∧ m = bs.At a

theorem Owned.elim {n : Nat} {a : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ Owned n a ⋆ R) : ∃ bs : List UInt8, bs.length = n ∧ (m =⋆ Eq (bs.At a) ⋆ R) :=
  let ⟨x, y, hu, hd, ⟨bs, hl, hx⟩, hy⟩ := h
  ⟨bs, hl, x, y, hu, hd, hx.symm, hy⟩

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

/-- `d` bytes of free stack just below `r`. -/
abbrev Reserve (d : Nat) (r : BitVec 64) : Mem 64 → Prop := Owned d (r - .ofNat 64 d)

/-- The 32 bytes above the return-address slot at `r` (the Windows x64 shadow space). -/
abbrev Shadow (r : BitVec 64) : Mem 64 → Prop := Owned 32 (r + 8)

/-- The shadow space split into the first argument's home slot (`r + 8`) and the remaining ones. -/
theorem Shadow_split (r : BitVec 64) : Shadow r = Owned 8 (r + 8) ⋆ Owned 24 (r + 16) := by
  rw [Shadow, show (32 : Nat) = 8 + 24 from rfl, Owned.split 8 24 _ (by omega)]
  congr 2
  bv_omega

/-- `rsp + 8` is a multiple of 16 on procedure entry; common to SysV and Win64. -/
abbrev EntryAligned (t : MachineData) : Prop := (t.regs.get64 .rsp).toNat % 16 = 8

end Kraken.X64.Stack
