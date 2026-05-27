/-
Kraken - Helper Theorems
-/

import Kraken.Semantics
import Kraken.Tactics

-- UInt64.ofInt (k : Int) ≠ 0 when k is a natural number with k < 2^64 and k ≠ 0
-- This proof uses only core Lean lemmas (no Batteries/Mathlib)
theorem UInt64_ofInt_natCast_ne_zero (k : Nat) (h_lt : k < 2^64) (h_ne : k ≠ 0) :
    UInt64.ofInt (k : Int) ≠ 0 := by
  simp only [UInt64.ofInt, ne_eq]
  intro h
  have h1 := congrArg UInt64.toNat h
  simp only [UInt64.toNat_ofNat] at h1
  -- Int mod to Nat conversion
  have h_klt : (k : Int) < 2^64 := Int.ofNat_lt.mpr h_lt
  have h_mod : (↑k : Int) % (2^64 : Int) = k := Int.emod_eq_of_lt (Int.natCast_nonneg k) h_klt
  conv at h1 => lhs; rw [show (↑k : Int) % (2^64 : Int) = ↑k from h_mod]
  simp only [Int.toNat_natCast] at h1
  -- h1: (UInt64.ofNat k).toNat = 0 % 2^64
  have h2 : (UInt64.ofNat k).toNat = k % 2^64 := UInt64.toNat_ofNat
  have hkmod : k % 2^64 = k := Nat.mod_eq_of_lt h_lt
  have hzero : (0 : Nat) % 2^64 = 0 := Nat.zero_mod (2^64)
  rw [h2, hkmod, hzero] at h1
  exact h_ne h1

theorem withAddressesAux_map_fst_idxOf_self (pc : Int64) (l : List (Directive × Nat)) :
    ((Executable.withAddressesAux pc l).map (·.1)).idxOf pc = 0 := by
  cases pc
  rename_i u
  cases u
  rename_i bv
  cases bv
  rename_i fin
  cases fin
  cases l with
  | nil => rfl
  | cons hd tl =>
    cases hd with | mk d z =>
      dsimp [Executable.withAddressesAux, List.idxOf, BEq.beq]
      simp [List.findIdx, List.findIdx.go]

theorem Executable.directivesFromStart [layout : Layout] prog :
    (layout prog).directivesFromAddress layout.start = prog.mapIdx (fun i d => (d, layout.size i)) := by
  dsimp [directivesFromAddress, withAddresses, Layout.apply]
  rw [withAddressesAux_map_fst_idxOf_self]
  rfl

theorem mapIdx_go_eq_map [layout : Layout] (h : ∀ i, layout.size i = 0) (prog : List Directive) (acc : Array (Directive × Nat)) :
    List.mapIdx.go (fun i d => (d, layout.size i)) prog acc = acc.toList ++ prog.map (fun d => (d, 0)) := by
  induction prog generalizing acc with
  | nil =>
    dsimp [List.mapIdx.go]
    simp
  | cons hd tl ih =>
    dsimp [List.mapIdx.go]
    have hz : layout.size acc.size = 0 := h acc.size
    rw [hz]
    rw [ih]
    simp

theorem mapIdx_eq_map [layout : Layout] (h : ∀ i, layout.size i = 0) (prog : List Directive) :
    prog.mapIdx (fun i d => (d, layout.size i)) = prog.map (fun d => (d, 0)) := by
  dsimp [List.mapIdx]
  rw [mapIdx_go_eq_map h]
  simp

theorem withAddressesAux_zero_size (pc : Int64) (prog : List Directive) :
    ((Executable.withAddressesAux pc (prog.map (fun d => (d, 0)))).filter (·.1 = pc)).map (·.2) =
      prog.map (fun d => (d, 0)) := by
  induction prog generalizing pc with
  | nil => rfl
  | cons hd tl ih =>
    dsimp [List.map]
    dsimp [Executable.withAddressesAux]
    simp
    rw [ih pc]

theorem Executable.directivesAtStart [layout : Layout] prog (h : ∀ i, layout.size i = 0) :
    (layout prog).directivesAtAddress layout.start = prog.mapIdx (fun i d => (d, layout.size i)) := by
  dsimp [directivesAtAddress, withAddresses, Layout.apply]
  rw [mapIdx_eq_map h]
  apply withAddressesAux_zero_size
