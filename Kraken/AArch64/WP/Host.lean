module

public import Kraken.AArch64.Semantics
public import Kraken.AArch64.Inert
public import Kraken.Data.List.Infix

private theorem takeWhile_eq_take_of {α : Type _} {p : α → Bool} {l : List α} {n : Nat}
    (hprior : ∀ k, k < n → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[n]? = some c → p c = false) :
    l.takeWhile p = l.take n := by
  rw [List.takeWhile_eq_take_findIdx_not]
  by_cases hn : n < l.length
  · rw [(List.findIdx_eq hn).mpr ⟨by simp [hhead _ (List.getElem?_eq_getElem hn)],
      fun k hk => by simp [hprior k hk _ (List.getElem?_eq_getElem (by omega))]⟩]
  · rw [(List.take_of_length_le (Nat.le_of_not_lt hn) : l.take n = l), List.take_of_length_le]
    refine Nat.le_of_eq (List.findIdx_eq_length.mpr fun x hx => ?_).symm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [hprior i (by omega) _ (List.getElem?_eq_getElem hi)]

private theorem exists_least_le {P : Nat → Prop} {n : Nat} (h : P n) :
    ∃ j, j ≤ n ∧ P j ∧ ∀ k, k < j → ¬P k := by
  induction n using Nat.strongRecOn with
  | ind n ih => grind

public class Host where
  prog : Program
  layout : Layout
  /-- Any directive that occupies zero space in the executable must be semantically inert. -/
  zero_inert : ∀ i d, prog[i]? = some d → @Kraken.Layout.size _ layout i = 0 → d.Inert
  /-- Two directives at the same address have the same offset in the executable. -/
  addr_determines_offset : ∀ j k, (layout.apply prog).addrOf j = (layout.apply prog).addrOf k →
    (layout.apply prog).sizeBefore j = (layout.apply prog).sizeBefore k

public instance [Host] : Layout := Host.layout

@[expose] public def Host.exe [Host] : Executable := Host.layout.apply Host.prog

@[expose] public def Host.addrOf [Host] (k : Nat) : Int64 := Host.exe.addrOf k

public instance [Host] : Labels := Executable.labels Host.exe

public theorem Host.sizeBefore_eq_of_addrOf_eq [Host] {j k : Nat} (h : Host.addrOf j = Host.addrOf k) :
    Host.exe.sizeBefore j = Host.exe.sizeBefore k :=
  Host.addr_determines_offset j k h

public theorem Host.inert_of_getElem? [Host] {i : Nat} {d : Directive} (h : Host.prog[i]? = some d)
    (hz : Kraken.Layout.size Instr i = 0) : d.Inert :=
  Host.zero_inert i d h hz

@[expose] public def Host.startAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h)

@[expose] public def Host.endAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h + p.length)

export Host (startAddr endAddr)

public theorem Layout.apply_getElem? [layout : Layout] (p : Program) (i : Nat) :
    (layout p).program[i]? = (p[i]?).map (fun d => {directive := d, size := Kraken.Layout.size Instr i}) := by
  simp [Kraken.Layout.apply, List.getElem?_mapIdx]

public theorem Host.exe_getElem? [Host] (i : Nat) :
    Host.exe.program[i]? = Host.prog[i]?.map (fun d => {directive := d, size := Kraken.Layout.size Instr i}) :=
  Layout.apply_getElem? _ _

public theorem Host.addrOf_succ [Host] {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (Kraken.Layout.size Instr k) :=
  Kraken.Executable.addrOf_succ _ (c := {directive := d, size := Kraken.Layout.size Instr k}) (by rw [Host.exe_getElem?, hd]; rfl)

section
variable [Host]

public theorem Host.inert_of_size_zero {d : Directive} (h : {directive := d, size := 0} ∈ Host.exe.program) : d.Inert := by
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp h
  grind [Host.exe_getElem?, Host.inert_of_getElem?]

public theorem Host.directivesAtAddress_addrOf {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) :
    ∃ pre : List (Kraken.Sized Directive), Host.exe.directivesAtAddress (Host.addrOf k) = pre ++ [c] ∧
      ∀ c ∈ pre, c.size = 0 := by
  obtain ⟨j, hjk, hj, hmin⟩ :=
    exists_least_le (P := fun i => Host.exe.addrOf i = Host.exe.addrOf k) rfl
  have hsize := Host.sizeBefore_eq_of_addrOf_eq hj
  have hpre : ∀ c ∈ (Host.exe.program.drop j).take (k - j), c.size = 0 := by
    have := Host.exe.sizeBefore_add j (k - j)
    rw [Nat.add_sub_cancel' hjk] at this
    have hsum : (((Host.exe.program.drop j).take (k - j)).map (·.size)).sum = 0 := by omega
    exact fun c hc => List.sum_eq_zero_iff_forall_eq_nat.mp hsum _ (List.mem_map_of_mem hc)
  have haddr : ∀ m, j ≤ m → m ≤ k → Host.exe.addrOf m = Host.exe.addrOf k := fun m hjm hmk => by
    grind [Kraken.Executable.addrOf, Host.exe.sizeBefore_mono hjm, Host.exe.sizeBefore_mono hmk]
  have hnext : Host.exe.addrOf (k + 1) ≠ Host.exe.addrOf k := fun h => by
    grind [Host.sizeBefore_eq_of_addrOf_eq h]
  refine ⟨(Host.exe.program.drop j).take (k - j), ?_, hpre⟩
  show ((Host.exe.withAddresses.dropWhile
    (·.addr ≠ Host.exe.addrOf k)).takeWhile (·.addr = Host.exe.addrOf k)).map (·.toSized) = _
  rw [Kraken.Executable.withAddresses_dropWhile_addrOf _ j k hj hmin,
    takeWhile_eq_take_of (n := k - j + 1)]
  · rw [List.map_take, List.map_drop, Kraken.Executable.withAddresses_map_snd, List.take_add_one,
      List.getElem?_drop, Nat.add_sub_cancel' hjk, hc]
    rfl
  · intro m hm c hc
    have := haddr (j + m) (by omega) (by omega)
    grind [Kraken.Executable.getElem?_withAddresses_eq]
  · intro c hc
    grind [Kraken.Executable.getElem?_withAddresses_eq]

end

/-! ## Label resolution -/

private theorem findSome?_eq_of_getElem? {α β : Type _} {f : α → Option β} {l : List α} {k : Nat}
    {a : α} {b : β} (hk : l[k]? = some a) (hf : f a = some b)
    (hprior : ∀ j, j < k → ∀ c, l[j]? = some c → f c = none) :
    l.findSome? f = some b := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp [hf]
    | succ k =>
      rw [List.findSome?_cons, hprior 0 (Nat.succ_pos k) x (by simp)]
      exact ih (by simpa using hk) (fun j hj c hc => hprior (j + 1) (by omega) c (by simpa using hc))

/--
Labels resolve to their first definition: if the `k`-th directive of the host program is `.label l`
and no earlier directive is, then `l` resolves to `Host.addrOf k`.

`Host` does not require labels to be unique, and the hypothesis `hfirst` cannot be dropped: a jump
to a label that is defined twice goes to the first definition.
-/
public theorem Host.label_eq_addrOf [Host] {l : Label} {k : Nat}
    (hk : Host.prog[k]? = some (.label l))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label l)) :
    Labels.label l = Host.addrOf k := by
  show (Host.exe.withAddresses.findSome? _).getD (-1) = Host.addrOf k
  rw [findSome?_eq_of_getElem? (k := k)
    (a := { directive := .label l, size := Kraken.Layout.size Instr k, addr := Host.exe.addrOf k })
    (b := Host.exe.addrOf k)]
  · rfl
  · rw [Kraken.Executable.getElem?_withAddresses_eq, Host.exe_getElem?, hk]
    rfl
  · simp
  · intro j hj c hc
    rw [Kraken.Executable.getElem?_withAddresses_eq, Host.exe_getElem?] at hc
    cases hd : Host.prog[j]? with
    | none => simp [hd] at hc
    | some d =>
      simp only [hd, Option.map_some, Option.some.injEq] at hc
      subst hc
      have hne : d ≠ .label l := fun h => hfirst j hj (by rw [hd, h])
      simp [hne]

/-- A label that the host program does not define resolves to `-1`. -/
public theorem Host.label_undefined [Host] {l : Label}
    (h : ∀ i : Nat, Host.prog[i]? ≠ some (.label l)) : Labels.label l = -1 := by
  show (Host.exe.withAddresses.findSome? _).getD (-1) = -1
  rw [List.findSome?_eq_none_iff.mpr]
  · rfl
  intro x hx
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  rw [Kraken.Executable.getElem?_withAddresses_eq, Host.exe_getElem?] at hi
  cases hd : Host.prog[i]? with
  | none => simp [hd] at hi
  | some d =>
    simp only [hd, Option.map_some, Option.some.injEq] at hi
    subst hi
    have hne : d ≠ .label l := fun e => h i (by rw [hd, e])
    simp [hne]

/-- No label is defined twice in the host program. `Host` does not provide this. -/
@[expose] public def Host.LabelsUnique [Host] : Prop :=
  ∀ (i j : Nat) (l : Label),
    Host.prog[i]? = some (.label l) → Host.prog[j]? = some (.label l) → i = j

/-- Under `LabelsUnique`, every definition of a label is its first definition. -/
public theorem Host.LabelsUnique.first [Host] (hu : Host.LabelsUnique) {l : Label} {k : Nat}
    (hk : Host.prog[k]? = some (.label l)) : ∀ j, j < k → Host.prog[j]? ≠ some (.label l) :=
  fun j hj h => Nat.ne_of_lt hj (hu j k l h hk)

public theorem Host.label_eq_addrOf_of_unique [Host] (hu : Host.LabelsUnique) {l : Label} {k : Nat}
    (hk : Host.prog[k]? = some (.label l)) : Labels.label l = Host.addrOf k :=
  Host.label_eq_addrOf hk (hu.first hk)

/-- The labels defined by a program, in order. `LabelsUnique` holds if this list has no duplicates. -/
@[expose] public def Program.definedLabels (p : Program) : List Label :=
  p.filterMap fun | .label l => some l | _ => none

private theorem eq_of_nodup_definedLabels {p : Program} (h : (Program.definedLabels p).Nodup) :
    ∀ (i j : Nat) (l : Label), p[i]? = some (.label l) → p[j]? = some (.label l) → i = j := by
  induction p with
  | nil => simp
  | cons d p ih =>
    have hmem : ∀ {j : Nat} {l : Label}, p[j]? = some (.label l : Directive) → l ∈ (Program.definedLabels p) := fun hj =>
      List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? hj, rfl⟩
    have htail : (Program.definedLabels p).Nodup := by
      cases d <;> simp_all [Program.definedLabels]
    intro i j l hi hj
    cases i <;> cases j
    · rfl
    · simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
      subst hi
      simp only [Program.definedLabels, List.filterMap_cons, List.nodup_cons] at h
      exact absurd (hmem hj) h.1
    · simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
      subst hj
      simp only [Program.definedLabels, List.filterMap_cons, List.nodup_cons] at h
      exact absurd (hmem hi) h.1
    · simp only [List.getElem?_cons_succ] at hi hj
      rw [ih htail _ _ _ hi hj]

/-- A decidable sufficient condition for `LabelsUnique`, for concrete hosts. -/
public theorem Host.labelsUnique_of_nodup [Host] (h : (Program.definedLabels Host.prog).Nodup) :
    Host.LabelsUnique :=
  eq_of_nodup_definedLabels h

/-! ## Concrete hosts -/

/--
A `Host` from a program and a layout that gives size zero only to labels and keeps the executable
below `2 ^ 64` bytes. For concrete programs both side conditions are decidable.
-/
@[reducible, expose] public def Host.ofLayout (prog : Program) (layout : Layout)
    (hzero : ∀ i d, prog[i]? = some d → @Kraken.Layout.size _ layout i = 0 → ∃ l, d = .label l)
    (hsmall : (layout.apply prog).sizeBefore prog.length < 2 ^ 64) : Host where
  prog := prog
  layout := layout
  zero_inert i d hd hz := by
    obtain ⟨l, rfl⟩ := hzero i d hd hz
    exact @Directive.inert_label l
  addr_determines_offset _ _ h :=
    Kraken.Executable.sizeBefore_eq_of_addrOf_eq _ (by simpa [Kraken.Layout.apply] using hsmall) h
