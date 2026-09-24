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

theorem Executable.directivesAtAddress_eq {Directive : Type} [layout : Layout Directive] (prog : List Directive) (a : Int64) :
    (layout prog).directivesAtAddress a =
      (((Executable.withAddresses (layout.start, prog.mapIdx (fun i d => (d, layout.size i)))).dropWhile (·.1 ≠ a)).takeWhile (·.1 = a)).map (·.2) :=
  rfl

@[simp] theorem Int64.add_right_eq_self (a b : Int64) : (a + b = a) ↔ b = 0 := by
  grind

@[simp] theorem Int64.self_eq_add_right (a b : Int64) : (a = a + b) ↔ b = 0 := by
  rw [eq_comm, Int64.add_right_eq_self]

@[simp] theorem Int64.add_add_eq_add (a b c : Int64) : (a + b + c = a + b) ↔ c = 0 :=
  Int64.add_right_eq_self (a + b) c

@[simp] theorem Int64.add_eq_add_add (a b c : Int64) : (a + b = a + b + c) ↔ c = 0 :=
  Int64.self_eq_add_right (a + b) c


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

theorem Executable.WellFormed.directivesFromAddress_drop2 {Directive : Type}
    {a0 : Int64} {d0 d1 d2 : Directive} {sz0 sz1 sz2 : Nat} {rest : List (Directive × Nat)}
    (hwf : Executable.WellFormed (a0, (d0, sz0) :: (d1, sz1) :: (d2, sz2) :: rest))
    (hsz1 : Int64.ofNat sz1 ≠ 0) :
    Executable.directivesFromAddress (a0, (d0, sz0) :: (d1, sz1) :: (d2, sz2) :: rest)
      (a0 + Int64.ofNat sz0 + Int64.ofNat sz1) = (d2, sz2) :: rest := by
  let a1 := a0 + Int64.ofNat sz0
  let a2 := a1 + Int64.ofNat sz1
  have ha2_ne_a1 : a2 ≠ a1 := by
    intro h
    have hbv : (a2.toBitVec - a1.toBitVec).toNat = (a1.toBitVec - a1.toBitVec).toNat :=
      congrArg (fun x : Int64 => (x.toBitVec - a1.toBitVec).toNat) h
    dsimp [a2] at hbv
    simp at hbv
    have hbv' : (Int64.ofNat sz1).toBitVec.toNat = (0 : Int64).toBitVec.toNat := by
      simp
      omega
    exact hsz1 (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq hbv'))
  let e : Executable Directive := (a0, (d0, sz0) :: (d1, sz1) :: (d2, sz2) :: rest)
  let suf := Executable.withAddresses (a2 + Int64.ofNat sz2, rest)
  have h_wa : e.withAddresses = (a0, d0, sz0) :: (a1, d1, sz1) :: (a2, d2, sz2) :: suf := by
    dsimp [e, a1, a2, suf]
    rw [Executable.withAddresses_cons, Executable.withAddresses_cons, Executable.withAddresses_cons]
  have h_drop_a0 : e.withAddresses.dropWhile (·.1 ≠ a0) =
      (a0, d0, sz0) :: (a1, d1, sz1) :: (a2, d2, sz2) :: suf := by
    rw [h_wa, List.dropWhile_cons]
    simp
  have h_drop_a2 : e.withAddresses.dropWhile (·.1 ≠ a2) = (a2, d2, sz2) :: suf := by
    by_cases h10 : a1 = a0
    · have ha2_ne_a0 : (a2 = a0) = False := eq_false (h10 ▸ ha2_ne_a1)
      have h_step : (e.withAddresses.dropWhile (·.1 ≠ a0)).dropWhile (·.1 = a0) = (a2, d2, sz2) :: suf := by
        rw [h_drop_a0, List.dropWhile_cons, List.dropWhile_cons, List.dropWhile_cons]
        simp [h10, ha2_ne_a0]
      exact hwf a0 (a2, d2, sz2) suf h_step
    · have ha1_ne_a0 : (a1 = a0) = False := eq_false h10
      have h_step1 : (e.withAddresses.dropWhile (·.1 ≠ a0)).dropWhile (·.1 = a0) =
          (a1, d1, sz1) :: (a2, d2, sz2) :: suf := by
        rw [h_drop_a0, List.dropWhile_cons, List.dropWhile_cons]
        simp [ha1_ne_a0]
      have h_drop_a1 : e.withAddresses.dropWhile (·.1 ≠ a1) =
          (a1, d1, sz1) :: (a2, d2, sz2) :: suf :=
        hwf a0 (a1, d1, sz1) ((a2, d2, sz2) :: suf) h_step1
      have ha2_ne_a1' : (a2 = a1) = False := eq_false ha2_ne_a1
      have h_step2 : (e.withAddresses.dropWhile (·.1 ≠ a1)).dropWhile (·.1 = a1) = (a2, d2, sz2) :: suf := by
        rw [h_drop_a1, List.dropWhile_cons, List.dropWhile_cons]
        simp [ha2_ne_a1']
      exact hwf a1 (a2, d2, sz2) suf h_step2
  dsimp [Executable.directivesFromAddress]
  change (e.withAddresses.dropWhile (·.1 ≠ a2)).map (·.2) = (d2, sz2) :: rest
  rw [h_drop_a2, List.map_cons]
  congr 1
  exact Executable.withAddresses_map_snd rest (a2 + Int64.ofNat sz2)

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

@[simp] def takeAtAddressWith {Directive : Type} (isZero : Directive → Bool) : List (Directive × Nat) → List (Directive × Nat)
  | [] => []
  | (d, sz) :: ds =>
    if isZero d then
      (d, sz) :: takeAtAddressWith isZero ds
    else
      [(d, sz)]

theorem withAddresses_takeWhile_eq {Directive : Type} (isZero : Directive → Bool)
    (a : Int64) (ds : List (Directive × Nat))
    (hvalid : ∀ p ∈ ds, if isZero p.1 then p.2 = 0 else Int64.ofNat p.2 ≠ 0) :
    ((Executable.withAddresses (a, ds)).takeWhile (·.1 = a)).map (·.2) =
      takeAtAddressWith isZero ds := by
  induction ds generalizing a with
  | nil =>
    rw [Executable.withAddresses_nil]
    rfl
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    have hhead := hvalid (d, sz) (List.mem_cons_self ..)
    have htail : ∀ p ∈ tail, if isZero p.1 then p.2 = 0 else Int64.ofNat p.2 ≠ 0 :=
      fun p hp => hvalid p (List.mem_cons_of_mem _ hp)
    rw [Executable.withAddresses_cons, List.takeWhile_cons]
    simp only [decide_true, ↓reduceIte, List.map_cons, takeAtAddressWith]
    cases h_zero : isZero d
    · simp only [h_zero, Bool.false_eq_true, ↓reduceIte] at hhead ⊢
      congr 1
      cases tail with
      | nil =>
        rw [Executable.withAddresses_nil]
        rfl
      | cons hd2 tl2 =>
        obtain ⟨d2, sz2⟩ := hd2
        rw [Executable.withAddresses_cons, List.takeWhile_cons]
        simp [hhead]
    · simp only [h_zero, ↓reduceIte] at hhead ⊢
      subst hhead
      simp [ih a htail]

private theorem sum_take_succ {Directive : Type} (ds : List (Directive × Nat)) (k : Nat) (hk : k < ds.length) :
    (((ds.take (k + 1)).map (fun (_, sz) => Int64.ofNat sz)).sum) =
      (((ds.take k).map (fun (_, sz) => Int64.ofNat sz)).sum) + Int64.ofNat ds[k].2 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append, List.sum_append]
  simp

private theorem withAddresses_dropWhile_eq_invariant {Directive : Type} (isZero : Directive → Bool)
    (start_addr : Int64) (ds : List (Directive × Nat))
    (hwf : Executable.WellFormed (start_addr, ds))
    (hvalid : ∀ p ∈ ds, if isZero p.1 then p.2 = 0 else Int64.ofNat p.2 ≠ 0)
    (k : Nat) (hk : k < ds.length) :
    let a_k := start_addr + ((ds.take k).map (fun (_, sz) => Int64.ofNat sz)).sum
    ((Executable.withAddresses (start_addr, ds)).dropWhile (·.1 ≠ a_k)).dropWhile (·.1 = a_k) =
      (Executable.withAddresses (a_k, ds.drop k)).dropWhile (·.1 = a_k) ∧
    ((k = 0 ∨ ∃ hlt : k - 1 < ds.length, isZero ds[k - 1].1 = false) →
      (Executable.withAddresses (start_addr, ds)).dropWhile (·.1 ≠ a_k) =
        Executable.withAddresses (a_k, ds.drop k)) := by
  induction k with
  | zero =>
    dsimp only
    simp only [List.take_zero, List.map_nil, List.sum_nil, Int64.add_zero, List.drop_zero]
    have h0 := Executable.withAddresses_dropWhile_start ds start_addr
    exact ⟨congrArg (List.dropWhile (·.1 = start_addr)) h0, fun _ => h0⟩
  | succ k ih =>
    have hk_lt : k < ds.length := Nat.lt_of_succ_lt hk
    obtain ⟨ih_inv, _⟩ := ih hk_lt
    let a_k := start_addr + ((ds.take k).map (fun (_, sz) => Int64.ofNat sz)).sum
    let a_next := start_addr + ((ds.take (k + 1)).map (fun (_, sz) => Int64.ofNat sz)).sum
    have ha_next : a_next = a_k + Int64.ofNat ds[k].2 := by
      dsimp [a_next, a_k]
      rw [sum_take_succ ds k hk_lt, Int64.add_assoc]
    have h_drop_k : ds.drop k = (ds[k].1, ds[k].2) :: ds.drop (k + 1) :=
      List.drop_eq_getElem_cons hk_lt
    have h_mem_k : ds[k] ∈ ds := List.getElem_mem hk_lt
    have hvalid_k := hvalid ds[k] h_mem_k
    cases h_zero : isZero ds[k].1
    · simp only [h_zero, Bool.false_eq_true, ↓reduceIte] at hvalid_k
      have h_rhs : (Executable.withAddresses (a_k, ds.drop k)).dropWhile (·.1 = a_k) =
          Executable.withAddresses (a_next, ds.drop (k + 1)) := by
        rw [h_drop_k, Executable.withAddresses_cons, List.dropWhile_cons]
        simp only [decide_true, ↓reduceIte, ← ha_next]
        cases h_rem : ds.drop (k + 1) with
        | nil =>
          rw [Executable.withAddresses_nil]
          rfl
        | cons hd2 tl2 =>
          obtain ⟨d2, sz2⟩ := hd2
          rw [Executable.withAddresses_cons, List.dropWhile_cons]
          simp [ha_next, hvalid_k]
      have h_step_eq : (Executable.withAddresses (start_addr, ds)).dropWhile (·.1 ≠ a_next) =
          Executable.withAddresses (a_next, ds.drop (k + 1)) := by
        have h_drop_eq : ((Executable.withAddresses (start_addr, ds)).dropWhile (·.1 ≠ a_k)).dropWhile (·.1 = a_k) =
            Executable.withAddresses (a_next, ds.drop (k + 1)) := by
          exact ih_inv.trans h_rhs
        cases h_rem : ds.drop (k + 1) with
        | nil =>
          have h_len := congrArg List.length h_rem
          simp at h_len
          omega
        | cons hd2 tl2 =>
          obtain ⟨d2, sz2⟩ := hd2
          rw [h_rem] at h_drop_eq
          rw [Executable.withAddresses_cons] at h_drop_eq ⊢
          exact hwf a_k (a_next, d2, sz2) (Executable.withAddresses (a_next + Int64.ofNat sz2, tl2)) h_drop_eq
      exact ⟨congrArg (List.dropWhile (·.1 = a_next)) h_step_eq, fun _ => h_step_eq⟩
    · simp only [h_zero, ↓reduceIte] at hvalid_k
      have ha_eq : a_next = a_k := by
        rw [ha_next, hvalid_k]
        simp
      have h_rhs : (Executable.withAddresses (a_k, ds.drop k)).dropWhile (·.1 = a_k) =
          (Executable.withAddresses (a_next, ds.drop (k + 1))).dropWhile (·.1 = a_next) := by
        rw [h_drop_k, Executable.withAddresses_cons, List.dropWhile_cons]
        simp [← ha_next, ha_eq]
      refine ⟨?_, ?_⟩
      · change ((Executable.withAddresses (start_addr, ds)).dropWhile (·.1 ≠ a_next)).dropWhile (·.1 = a_next) =
          (Executable.withAddresses (a_next, ds.drop (k + 1))).dropWhile (·.1 = a_next)
        have ih_inv' : ((Executable.withAddresses (start_addr, ds)).dropWhile (·.1 ≠ a_k)).dropWhile (·.1 = a_k) =
            (Executable.withAddresses (a_k, ds.drop k)).dropWhile (·.1 = a_k) := ih_inv
        rw [ha_eq]
        rw [ha_eq] at h_rhs
        exact ih_inv'.trans h_rhs
      · rintro (h_zero_eq | ⟨_, h_false⟩)
        · omega
        · simp [h_zero] at h_false

theorem Executable.directivesAtAddress_after {Directive : Type} [layout : Layout Directive]
    (isZero : Directive → Bool) (prog : List Directive)
    (hwf : (layout prog).WellFormed)
    (hvalid : ∀ p ∈ (layout prog).2, if isZero p.1 then p.2 = 0 else Int64.ofNat p.2 ≠ 0)
    (n : Nat) (hn : n < prog.length)
    (hprev : n = 0 ∨ ∃ hlt : n - 1 < prog.length, isZero prog[n - 1] = false) :
    let ds := prog.mapIdx (fun i d => (d, layout.size i))
    let len := ((ds.take n).map (fun (_, sz) => Int64.ofNat sz)).sum
    (layout prog).directivesAtAddress (layout.start + len) =
      takeAtAddressWith isZero (ds.drop n) := by
  dsimp [Executable.directivesAtAddress, Layout.apply]
  let ds := prog.mapIdx (fun i d => (d, layout.size i))
  have h_len : ds.length = prog.length := List.length_mapIdx
  have hn_ds : n < ds.length := h_len.symm ▸ hn
  have hprev_ds : n = 0 ∨ ∃ hlt : n - 1 < ds.length, isZero ds[n - 1].1 = false := by
    rcases hprev with rfl | ⟨hlt, hz⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨h_len.symm ▸ hlt, ?_⟩
      simpa [ds] using hz
  have h_drop := (withAddresses_dropWhile_eq_invariant isZero layout.start ds hwf hvalid n hn_ds).2 hprev_ds
  rw [h_drop]
  apply withAddresses_takeWhile_eq isZero _ (ds.drop n)
  intro p hp
  exact hvalid p (List.mem_of_mem_drop hp)

theorem Executable.directivesAtStart_of_valid {Directive : Type} [layout : Layout Directive]
    (isZero : Directive → Bool) (prog : List Directive)
    (hvalid : ∀ p ∈ (layout prog).2, if isZero p.1 then p.2 = 0 else Int64.ofNat p.2 ≠ 0) :
    (layout prog).directivesAtAddress layout.start =
      takeAtAddressWith isZero (prog.mapIdx (fun i d => (d, layout.size i))) := by
  dsimp [Executable.directivesAtAddress, Layout.apply]
  rw [Executable.withAddresses_dropWhile_start]
  exact withAddresses_takeWhile_eq isZero layout.start _ hvalid

end Kraken
