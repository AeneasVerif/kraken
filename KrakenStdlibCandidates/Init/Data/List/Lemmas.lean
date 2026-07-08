prelude
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import KrakenStdlibCandidates.Init.GrindInternHooks


/-!
# Grind homomorphism lemmas for List.
-/

namespace List

attribute [grind_homo] length_nil
attribute [grind_homo] length_cons
attribute [grind_homo] length_append
attribute [grind_homo] length_drop
attribute [grind_homo] length_take
attribute [grind_homo] length_reverse
attribute [grind_homo] length_map
attribute [grind_homo] length_replicate
attribute [grind_homo] length_tail
attribute [grind_homo] length_concat
attribute [grind_homo] length_zipWith
attribute [grind_homo] length_zip
attribute [grind_homo] length_set
attribute [grind_homo] length_insertIdx
attribute [grind_homo] length_eraseIdx
attribute [grind_homo] length_modify
attribute [grind_homo] length_singleton
attribute [grind_homo] length_dropLast
attribute [grind_homo] length_dropLast_cons
attribute [grind_homo] length_replace

@[grind_homo] theorem getD_append_left {α : Type} (s1 s2 : List α) (i : Nat) (h : i < s1.length) (d : α) :
    (s1 ++ s2).getD i d = s1.getD i d := by
  induction s1 generalizing i with
  | nil => contradiction
  | cons a s1' ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      apply ih
      exact Nat.lt_of_succ_lt_succ h

@[grind_homo] theorem getD_append_right {α : Type} (s1 s2 : List α) (i : Nat) (h : s1.length ≤ i) (d : α) :
    (s1 ++ s2).getD i d = s2.getD (i - s1.length) d := by
  induction s1 generalizing i with
  | nil => rfl
  | cons a s1' ih =>
    cases i with
    | zero => contradiction
    | succ i' =>
      simp only [cons_append, getD, length_cons, Nat.succ_sub_succ]
      apply ih
      exact Nat.le_of_succ_le_succ h

@[grind_homo] theorem getD_append_length {α : Type} (s : List α) (x : α) (d : α) :
    (s ++ [x]).getD s.length d = x := by
  induction s with
  | nil => rfl
  | cons a s' ih =>
    change (s' ++ [x]).getD s'.length d = x
    exact ih

attribute [grind_homo] drop_drop
attribute [grind_homo] take_take



end List
