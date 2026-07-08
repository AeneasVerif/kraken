prelude
import Lean


/-!
# Basic definitions for BitVec.
-/

namespace BitVec

def unsigned {w} (x : BitVec w) := Int.ofNat x.toNat

theorem unsigned_append {n m : Nat} (a : BitVec n) (b : BitVec m) :
    (a ++ b).unsigned = a.unsigned * (2 ^ m) + b.unsigned := by
  dsimp only [unsigned]
  rw [BitVec.toNat_append]
  have hb := b.isLt
  have h := (Nat.shiftLeft_add_eq_or_of_lt hb a.toNat)
  rw [← h, Nat.shiftLeft_eq]
  simp

abbrev signed {w} (x : BitVec w) := x.toInt

def take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
def drop {w} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w-n)

def replaceLow {w n} (old : BitVec w) (new : BitVec n) : BitVec w :=
  (BitVec.append (old.drop n) new).setWidth _
def replace {w1} (old : BitVec w1) (i : Nat) {w2} (new : BitVec w2) : BitVec w1 :=
  (old.drop (i + w2) ++ new ++ old.take i).setWidth _

end BitVec
