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

instance {Directive : Type} : CoeFun (Layout Directive) (fun _ => List Directive → Executable Directive) where
  coe := Layout.apply

def Executable.withAddresses {Directive : Type} (e : Executable Directive) : List (Int64 × Directive × Nat) :=
  let (_, withAddresses) :=
    e.2.foldl (fun (currAddr, acc) (d, z) => (currAddr + .ofNat z, (currAddr, d, z) :: acc)) (e.1, [])
  withAddresses.reverse

private theorem withAddresses_foldl_aux {Directive : Type} (ds : List (Directive × Nat)) (currAddr : Int64)
    (acc : List (Int64 × Directive × Nat)) :
    (ds.foldl (fun (currAddr, acc) (d, z) => (currAddr + .ofNat z, (currAddr, d, z) :: acc)) (currAddr, acc)).2.reverse =
      acc.reverse ++ (ds.foldl (fun (currAddr, acc) (d, z) => (currAddr + .ofNat z, (currAddr, d, z) :: acc)) (currAddr, [])).2.reverse := by
  induction ds generalizing currAddr acc with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨d, z⟩ := hd
    simp only [List.foldl_cons]
    rw [ih (currAddr + .ofNat z) ((currAddr, d, z) :: acc)]
    rw [ih (currAddr + .ofNat z) [(currAddr, d, z)]]
    simp

theorem Executable.withAddresses_nil {Directive : Type} (a : Int64) :
    Executable.withAddresses (Directive := Directive) (a, []) = [] := rfl

theorem Executable.withAddresses_cons {Directive : Type} (a : Int64) (d : Directive) (z : Nat) (ds : List (Directive × Nat)) :
    Executable.withAddresses (a, (d, z) :: ds) = (a, d, z) :: Executable.withAddresses (a + .ofNat z, ds) := by
  dsimp [Executable.withAddresses]
  rw [withAddresses_foldl_aux ds (a + .ofNat z) [(a, d, z)]]
  rfl

def Executable.directivesAtAddress {Directive : Type} (e : Executable Directive) (a : Int64) : List (Directive × Nat) :=
  let starts_at_a := e.withAddresses.dropWhile (·.1 ≠ a)
  (starts_at_a.takeWhile (·.1 = a)).map (·.2)

def Executable.directivesFromAddress {Directive : Type} (e : Executable Directive) (a : Int64) : List (Directive × Nat) :=
  let starts_at_a := e.withAddresses.dropWhile (·.1 ≠ a)
  starts_at_a.map (·.2)

theorem Executable.withAddresses_map_snd {Directive : Type} (ds : List (Directive × Nat)) (a : Int64) :
    (Executable.withAddresses (a, ds)).map (·.2) = ds := by
  induction ds generalizing a with
  | nil =>
    rw [Executable.withAddresses_nil]
    rfl
  | cons d ds ih =>
    rw [Executable.withAddresses_cons]
    simp [ih]

theorem Executable.withAddresses_dropWhile_start {Directive : Type} (ds : List (Directive × Nat)) (a : Int64) :
    (Executable.withAddresses (a, ds)).dropWhile (fun x => x.1 ≠ a) =
      Executable.withAddresses (a, ds) := by
  cases ds with
  | nil =>
    rw [Executable.withAddresses_nil]
    rfl
  | cons d ds =>
    rw [Executable.withAddresses_cons]
    simp [List.dropWhile]

theorem Executable.directivesFromStart {Directive : Type} [layout : Layout Directive] (prog : List Directive) :
    (layout prog).directivesFromAddress layout.start =
      prog.mapIdx (fun i d => (d, layout.size i)) := by
  dsimp [Executable.directivesFromAddress, Layout.apply]
  rw [Executable.withAddresses_dropWhile_start]
  rw [Executable.withAddresses_map_snd]

theorem directivesAtFromPrefix {Directive : Type} (e: Executable Directive) (a: Int64):
  let starts_at_a := e.withAddresses.dropWhile (·.1 ≠ a)
  e.directivesFromAddress a = e.directivesAtAddress a ++ (starts_at_a.dropWhile (·.1 = a)).map (·.2)
:= by
  dsimp [Executable.directivesFromAddress, Executable.directivesAtAddress]
  rw [← List.map_append]
  rw [List.takeWhile_append_dropWhile]

theorem withAddresses_dropWhile_eq {Directive : Type} (start_addr : Int64) (ds : List (Directive × Nat))
    (p : (Int64 × Directive × Nat) → Bool) {x : Int64 × Directive × Nat} {xs : List (Int64 × Directive × Nat)}
    (h : (Executable.withAddresses (start_addr, ds)).dropWhile p = x :: xs) :
    p x = false ∧ ∃ ds', x :: xs = Executable.withAddresses (x.1, ds') := by
  induction ds generalizing start_addr with
  | nil =>
    rw [Executable.withAddresses_nil] at h
    contradiction
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    rw [Executable.withAddresses_cons] at h
    simp only [List.dropWhile_cons] at h
    split at h
    · exact ih (start_addr + .ofNat sz) h
    · rename_i hp
      injection h with hx hxs
      subst hx hxs
      refine ⟨Bool.eq_false_iff.mpr hp, (d, sz) :: tail, ?_⟩
      rw [Executable.withAddresses_cons]

theorem withAddresses_takeWhile_foldl {Directive : Type} (start_addr : Int64) (ds : List (Directive × Nat))
    (p : (Int64 × Directive × Nat) → Bool) {y : Int64 × Directive × Nat} {ys : List (Int64 × Directive × Nat)}
    (h : (Executable.withAddresses (start_addr, ds)).dropWhile p = y :: ys) :
    (((Executable.withAddresses (start_addr, ds)).takeWhile p).map (·.2)).foldl
      (fun a (_, sz) => a + .ofNat sz) start_addr = y.1 := by
  induction ds generalizing start_addr with
  | nil =>
    rw [Executable.withAddresses_nil] at h
    contradiction
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    rw [Executable.withAddresses_cons] at h ⊢
    simp only [List.dropWhile_cons, List.takeWhile_cons] at h ⊢
    split at h
    · rename_i hp
      simp [hp]
      exact ih (start_addr + .ofNat sz) h
    · rename_i hp
      simp [hp]
      injection h with hy _
      rw [← hy]

def Executable.WellFormed {Directive : Type} (e : Executable Directive) : Prop :=
  ∀ a y ys,
    (e.withAddresses.dropWhile (·.1 ≠ a)).dropWhile (·.1 = a) = y :: ys →
    e.withAddresses.dropWhile (·.1 ≠ y.1) = y :: ys

private theorem int64_add_ofNat_assoc (a : Int64) (m n : Nat) :
    a + Int64.ofNat m + Int64.ofNat n = a + Int64.ofNat (m + n) := by
  rw [Int64.add_assoc, ← Int64.ofNat_add]

private theorem int64_add_ofNat_ne_self (a : Int64) {k : Nat} (hk_pos : 0 < k) (hk_lt : k < 2 ^ 64) :
    a + Int64.ofNat k ≠ a := by
  intro h
  have hbv : ((a + Int64.ofNat k).toBitVec - a.toBitVec).toNat = (a.toBitVec - a.toBitVec).toNat :=
    congrArg (fun x : Int64 => (x.toBitVec - a.toBitVec).toNat) h
  simp at hbv
  omega

private theorem withAddresses_dropWhile_eq_offset {Directive : Type} (cur a : Int64) (ds : List (Directive × Nat))
    {y : Int64 × Directive × Nat} {ys : List (Int64 × Directive × Nat)}
    (h : (Executable.withAddresses (cur, ds)).dropWhile (·.1 = a) = y :: ys) :
    y.1 ≠ a ∧ ∃ k ≤ (ds.map (·.2)).sum, y.1 = cur + Int64.ofNat k := by
  induction ds generalizing cur with
  | nil =>
    rw [Executable.withAddresses_nil] at h
    contradiction
  | cons hd tl ih =>
    obtain ⟨d, sz⟩ := hd
    rw [Executable.withAddresses_cons, List.dropWhile_cons] at h
    split at h
    · obtain ⟨hne, k', hk', hy⟩ := ih (cur + Int64.ofNat sz) h
      have hle : sz + k' ≤ (((d, sz) :: tl).map (·.2)).sum := by
        simp only [List.map_cons, List.sum_cons]
        omega
      refine ⟨hne, sz + k', hle, ?_⟩
      rw [hy, int64_add_ofNat_assoc]
    · rename_i hp
      injection h with hy _
      subst hy
      have hne : cur ≠ a := by simpa using hp
      refine ⟨hne, 0, Nat.zero_le _, ?_⟩
      simp

private theorem withAddresses_dropWhile_offset {Directive : Type} (start_addr a : Int64) (ds : List (Directive × Nat))
    {y : Int64 × Directive × Nat} {ys : List (Int64 × Directive × Nat)}
    (h : ((Executable.withAddresses (start_addr, ds)).dropWhile (·.1 ≠ a)).dropWhile (·.1 = a) = y :: ys) :
    ∃ k, 0 < k ∧ k ≤ (ds.map (·.2)).sum ∧ y.1 = start_addr + Int64.ofNat k := by
  induction ds generalizing start_addr with
  | nil =>
    rw [Executable.withAddresses_nil] at h
    contradiction
  | cons hd tl ih =>
    obtain ⟨d, sz⟩ := hd
    rw [Executable.withAddresses_cons, List.dropWhile_cons] at h
    split at h
    · obtain ⟨k', hk'_pos, hk'_le, hy⟩ := ih (start_addr + Int64.ofNat sz) h
      have hpos : 0 < sz + k' := by omega
      have hle : sz + k' ≤ (((d, sz) :: tl).map (·.2)).sum := by
        simp only [List.map_cons, List.sum_cons]
        omega
      refine ⟨sz + k', hpos, hle, ?_⟩
      rw [hy, int64_add_ofNat_assoc]
    · rename_i hp
      have h_eq : start_addr = a := by simpa using hp
      subst h_eq
      have h' : (Executable.withAddresses (start_addr, (d, sz) :: tl)).dropWhile (·.1 = start_addr) = y :: ys := by
        rw [Executable.withAddresses_cons]
        exact h
      obtain ⟨hne, k, hk_le, hy⟩ := withAddresses_dropWhile_eq_offset start_addr start_addr ((d, sz) :: tl) h'
      have hk_pos : 0 < k := by
        cases k with
        | zero =>
          simp at hy
          exact absurd hy hne
        | succ n => omega
      exact ⟨k, hk_pos, hk_le, hy⟩

theorem Executable.wellFormed_of_sum_lt {Directive : Type} (e : Executable Directive)
    (hsum : (e.2.map (·.2)).sum < 2 ^ 64) :
    e.WellFormed := by
  obtain ⟨start_addr, ds⟩ := e
  intro a y ys h
  induction ds generalizing start_addr with
  | nil =>
    rw [Executable.withAddresses_nil] at h
    contradiction
  | cons hd tl ih =>
    obtain ⟨d, sz⟩ := hd
    simp only [List.map_cons, List.sum_cons] at hsum
    have hsum_tl : (tl.map (·.2)).sum < 2 ^ 64 := by omega
    obtain ⟨k, hk_pos, hk_le, hy_eq⟩ := withAddresses_dropWhile_offset start_addr a ((d, sz) :: tl) h
    simp only [List.map_cons, List.sum_cons] at hk_le
    have hk_lt : k < 2 ^ 64 := by omega
    have h_ne_y : (start_addr ≠ y.1) = True := eq_true (by
      rw [hy_eq]
      exact Ne.symm (int64_add_ofNat_ne_self start_addr hk_pos hk_lt))
    rw [Executable.withAddresses_cons, List.dropWhile_cons]
    simp only [decide_eq_true_eq, h_ne_y, ↓reduceIte]
    rw [Executable.withAddresses_cons, List.dropWhile_cons] at h
    split at h
    · exact ih (start_addr + Int64.ofNat sz) hsum_tl h
    · rename_i hp
      have h_eq : start_addr = a := by simpa using hp
      subst h_eq
      simp only [List.dropWhile_cons, decide_true, ↓reduceIte] at h
      by_cases h_next : start_addr + Int64.ofNat sz = start_addr
      · rw [h_next] at h ⊢
        cases tl with
        | nil =>
          rw [Executable.withAddresses_nil] at h
          contradiction
        | cons hd2 tl2 =>
          have h_drop_start : (Executable.withAddresses (start_addr, hd2 :: tl2)).dropWhile (·.1 ≠ start_addr) =
              Executable.withAddresses (start_addr, hd2 :: tl2) := by
            obtain ⟨d2, sz2⟩ := hd2
            rw [Executable.withAddresses_cons, List.dropWhile_cons]
            simp
          rw [← h_drop_start] at h
          exact ih start_addr hsum_tl h
      · cases h_tl : Executable.withAddresses (start_addr + Int64.ofNat sz, tl) with
        | nil =>
          rw [h_tl] at h
          contradiction
        | cons z zs =>
          have hz : z.1 = start_addr + Int64.ofNat sz := by
            cases tl with
            | nil => rw [Executable.withAddresses_nil] at h_tl; contradiction
            | cons hd2 tl2 =>
              obtain ⟨d2, sz2⟩ := hd2
              rw [Executable.withAddresses_cons] at h_tl
              injection h_tl with hz_eq _
              rw [← hz_eq]
          rw [h_tl, List.dropWhile_cons] at h
          simp only [hz, decide_eq_true_eq, h_next, ↓reduceIte] at h
          rw [h, List.dropWhile_cons]
          simp

end Kraken
