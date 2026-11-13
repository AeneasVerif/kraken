module

public import Kraken.X64.Semantics
public import Kraken.X64.Inert
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

private theorem findSome?_of_getElem? {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {j : Nat} {a : α} {b : β}, l[j]? = some a → f a = some b →
      (∀ i, i < j → ∀ x, l[i]? = some x → f x = none) → l.findSome? f = some b
  | [], _, _, _, h, _, _ => by simp at h
  | x :: l, 0, a, b, h, hf, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [hf]
  | x :: l, j + 1, a, b, h, hf, hprior => by
    have hx : f x = none := hprior 0 (by omega) x rfl
    simp only [List.findSome?_cons, hx]
    exact findSome?_of_getElem? (j := j) (by simpa using h) hf
      (fun i hi y hy => hprior (i + 1) (by omega) y (by simpa using hy))

public class Host where
  prog : Program
  layout : Layout
  /-- Any directive that occupies zero space in the executable must be semantically inert. -/
  zero_inert : ∀ i d, prog[i]? = some d → layout.size i = 0 → d.Inert
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
    (hz : Host.layout.size i = 0) : d.Inert :=
  Host.zero_inert i d h hz

@[expose] public def Host.startAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h)

@[expose] public def Host.endAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h + p.length)

export Host (startAddr endAddr)

public theorem Layout.apply_getElem? [layout : Layout] (p : Program) (i : Nat) :
    (layout p).program[i]? = (p[i]?).map (fun d => {directive := d, size := layout.size i}) := by
  simp [Kraken.Layout.apply, List.getElem?_mapIdx]

public theorem Host.exe_getElem? [Host] (i : Nat) :
    Host.exe.program[i]? = Host.prog[i]?.map (fun d => {directive := d, size := Host.layout.size i}) :=
  Layout.apply_getElem? _ _

public theorem Host.addrOf_succ [Host] {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (Host.layout.size k) :=
  Kraken.Executable.addrOf_succ _ (c := {directive := d, size := Host.layout.size k}) (by rw [Host.exe_getElem?, hd]; rfl)

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

/-- The address of a label is the address of its first occurrence in the ambient program. -/
public theorem Host.label_addrOf {l : Label} {j : Nat} (hj : Host.prog[j]? = some (.label l))
    (hfirst : ∀ i, i < j → Host.prog[i]? ≠ some (.label l)) :
    label l = Host.addrOf j := by
  show ((Host.exe.withAddresses.findSome?
      (fun {directive, addr, ..} => if directive = .label l then .some addr else .none)).getD (-1))
    = Host.addrOf j
  rw [findSome?_of_getElem? (j := j) (b := Host.addrOf j)
    (a := {directive := .label l, size := Host.layout.size j, addr := Host.exe.addrOf j})]
  · rfl
  · rw [Kraken.Executable.getElem?_withAddresses_eq, Host.exe_getElem?, hj]
    rfl
  · simp [Host.addrOf]
  · intro i hi x hx
    rw [Kraken.Executable.getElem?_withAddresses_eq, Host.exe_getElem?] at hx
    cases hpi : Host.prog[i]? with
    | none => simp [hpi] at hx
    | some d =>
      simp only [hpi, Option.map_some, Option.some.injEq] at hx
      subst hx
      have hne : d ≠ .label l := fun h => hfirst i hi (h ▸ hpi)
      simp [hne]

end
