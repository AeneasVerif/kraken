module

@[expose] public section

/-
Common Kraken executable layout.
-/

namespace Kraken

abbrev Executable (Directive : Type) := Int64 × List (Directive × Nat)

-- JP: why is `size` not `Directive → Nat`?
class Layout (Directive : Type) where
  start : Int64
  size : Nat → Nat

def Layout.apply {Directive : Type} (l : Layout Directive) (prog : List Directive) : Executable Directive :=
  (l.start, prog.mapIdx (fun i d => (d, l.size i)))

-- TODO: Why not just define a top-level function `def layout [Layout] := layout.apply` (with apply inlined)?
-- Coercions are certainly an antipattern, and such a def wouldn't require to bind `[layout : Layout]` all the time.
instance {Directive : Type} : CoeFun (Layout Directive) (fun _ => List Directive → Executable Directive) where
  coe := Layout.apply

-- Returns each directive paired with its start address and size.
-- TODO: tail-recursive version for efficiency?
def Executable.withAddresses {Directive : Type} (e : Executable Directive) : List (Int64 × Directive × Nat) :=
  let (start_addr, ds) := e
  match ds with
  | [] => []
  | (instr, instr_sz) :: ds =>
    (start_addr, instr, instr_sz) :: Executable.withAddresses (start_addr + .ofNat instr_sz, ds)
termination_by e.2

def Executable.directivesAtAddress {Directive : Type} (e : Executable Directive) (a : Int64) : List (Directive × Nat) :=
  let starts_at_a := e.withAddresses.dropWhile (·.1 ≠ a)
  (starts_at_a.takeWhile (·.1 = a)).map (·.2)

def Executable.directivesFromAddress {Directive : Type} (e : Executable Directive) (a : Int64) : List (Directive × Nat) :=
  let starts_at_a := e.withAddresses.dropWhile (·.1 ≠ a)
  starts_at_a.map (·.2)

def Executable.fetch? {Directive : Type} (e : Executable Directive) (a : Int64) : Option (Directive × Nat) :=
  (e.directivesAtAddress a).find? (0 < ·.2)

theorem Executable.withAddresses_map_snd {Directive : Type} (ds : List (Directive × Nat)) (a : Int64) :
    (Executable.withAddresses (a, ds)).map (·.2) = ds := by
  induction ds generalizing a with
  | nil =>
    rw [Executable.withAddresses]
    rfl
  | cons d ds ih =>
    rw [Executable.withAddresses]
    simp [ih]

theorem Executable.withAddresses_dropWhile_start {Directive : Type} (ds : List (Directive × Nat)) (a : Int64) :
    (Executable.withAddresses (a, ds)).dropWhile (fun x => x.1 ≠ a) =
      Executable.withAddresses (a, ds) := by
  cases ds with
  | nil =>
    rw [Executable.withAddresses]
    rfl
  | cons d ds =>
    rw [Executable.withAddresses]
    simp [List.dropWhile]

theorem Executable.directivesFromStart {Directive : Type} [layout : Layout Directive] (prog : List Directive) :
    (layout prog).directivesFromAddress layout.start =
      prog.mapIdx (fun i d => (d, layout.size i)) := by
  dsimp [Executable.directivesFromAddress, Layout.apply]
  rw [Executable.withAddresses_dropWhile_start]
  rw [Executable.withAddresses_map_snd]

theorem directivesAtFromPrefix {Directive : Type} (e: Executable Directive) (a: Int64):
  ∃ rest, e.directivesFromAddress a = e.directivesAtAddress a ++ rest := by
  dsimp [Executable.directivesFromAddress, Executable.directivesAtAddress]
  refine ⟨((e.withAddresses.dropWhile (·.1 ≠ a)).dropWhile (·.1 = a)).map (·.2), ?_⟩
  rw [← List.map_append]
  rw [List.takeWhile_append_dropWhile]

@[grind hom] theorem Int64.toBitVec_ofNat_grind (a : Nat) :
    (Int64.ofNat a).toBitVec = OfNat.ofNat a := by
  rw [Int64.toBitVec_ofNat']; rfl

/-- The sum of sizes of the first `n` directives of `e`. -/
def Executable.sizeBefore {Directive : Type} (e : Executable Directive) (n : Nat) : Nat := ((e.2.take n).map (·.2)).sum

/--
The address of the `n`-th directive of `e`: the start address of `e` plus the sum of sizes of the
first `n` directives.
-/
def Executable.addrOf {Directive : Type} (e : Executable Directive) (n : Nat) : Int64 := e.1 + .ofNat (e.sizeBefore n)

@[simp] theorem Executable.addrOf_zero {Directive : Type} (e : Executable Directive) : e.addrOf 0 = e.1 := by
  grind [sizeBefore, addrOf]

theorem Executable.sizeBefore_succ {Directive : Type} (e : Executable Directive) {n : Nat} {d : Directive} {z : Nat}
    (hd : e.2[n]? = some (d, z)) :
    e.sizeBefore (n + 1) = e.sizeBefore n + z := by
  grind [sizeBefore, List.take_add_one]

theorem Executable.addrOf_succ {Directive : Type} (e : Executable Directive) {n : Nat} {d : Directive} {z : Nat}
    (hd : e.2[n]? = some (d, z)) : e.addrOf (n + 1) = e.addrOf n + .ofNat z := by
  grind [addrOf, sizeBefore, List.take_add_one]

theorem Executable.getElem?_withAddresses_pair {Directive : Type} :
    ∀ (ds : List (Directive × Nat)) (a : Int64) (k : Nat),
      (Kraken.Executable.withAddresses (a, ds))[k]?
        = ds[k]?.map (fun dz => (Executable.addrOf (a, ds) k, dz))
  | [], a, k => by rw [Kraken.Executable.withAddresses]; simp
  | (d, z) :: ds, a, 0 => by
    rw [Kraken.Executable.withAddresses]
    simp
  | (d, z) :: ds, a, k + 1 => by
    rw [Kraken.Executable.withAddresses]
    simp only [List.getElem?_cons_succ, getElem?_withAddresses_pair ds _ k]
    congr 2
    funext dz
    simp only [addrOf, sizeBefore, List.take_succ_cons, List.map_cons, List.sum_cons]
    grind

theorem Executable.getElem?_withAddresses_eq {Directive : Type} (e : Executable Directive) (k : Nat) :
    (Kraken.Executable.withAddresses (e.1, e.2))[k]? = e.2[k]?.map (fun dz => (e.addrOf k, dz)) :=
  getElem?_withAddresses_pair e.2 e.1 k

private theorem dropWhile_eq_drop_of {α : Type _} {p : α → Bool} {l : List α} {j : Nat}
    (hprior : ∀ k, k < j → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[j]? = some c → p c = false) :
    l.dropWhile p = l.drop j := by
  rw [List.dropWhile_eq_drop_findIdx_not]
  by_cases hj : j < l.length
  · rw [(List.findIdx_eq hj).mpr ⟨by simp [hhead _ (List.getElem?_eq_getElem hj)],
      fun k hk => by simp [hprior k hk _ (List.getElem?_eq_getElem (by omega))]⟩]
  · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hj), List.drop_eq_nil_iff]
    refine Nat.le_of_eq (List.findIdx_eq_length.mpr fun x hx => ?_).symm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [hprior i (by omega) _ (List.getElem?_eq_getElem hi)]

theorem Executable.withAddresses_dropWhile_addrOf {Directive : Type} (e : Executable Directive) (j n : Nat)
    (hj : e.addrOf j = e.addrOf n)
    (hfresh : ∀ k, k < j → e.addrOf k ≠ e.addrOf n) :
    (Kraken.Executable.withAddresses (e.1, e.2)).dropWhile (·.1 ≠ e.addrOf n)
      = (Kraken.Executable.withAddresses (e.1, e.2)).drop j := by
  apply dropWhile_eq_drop_of
  · intro k hk c hc
    rw [Executable.getElem?_withAddresses_eq] at hc
    obtain ⟨dz, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simpa using hfresh k hk
  · intro c hc
    rw [Executable.getElem?_withAddresses_eq] at hc
    obtain ⟨dz, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simpa using hj

end Kraken
