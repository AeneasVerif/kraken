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

public class Host where
  prog : Program

@[expose] public def Host.exe [Host] [layout : Layout] : Executable := layout Host.prog

@[expose] public def Host.addrOf [Host] [Layout] (k : Nat) : Int64 := Host.exe.addrOf k

public instance [Host] [Layout] : Labels := Executable.labels Host.exe

/-- A set of abstract assumptions about the `Layout` of a `Host` program that most specs need and
that every reasonable assembler satisfies. -/
public class Layout.Valid [Host] [Layout] : Prop where
  /-- Any directive that occupies zero space in the executable must be semantically inert. -/
  zero_inert : ∀ i d, Host.prog[i]? = some d → Kraken.Layout.size Directive i = 0 → d.Inert
  /-- Two directives at the same address have the same offset in the executable. -/
  addr_determines_offset : ∀ j k, Host.addrOf j = Host.addrOf k → Host.exe.sizeBefore j = Host.exe.sizeBefore k

@[expose] public def Host.startAddr [Host] [Layout] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h)

@[expose] public def Host.endAddr [Host] [Layout] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h + p.length)

export Host (startAddr endAddr)

public theorem Layout.apply_getElem? [layout : Layout] (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  simp [Kraken.Layout.apply, List.getElem?_mapIdx]

public theorem Host.exe_getElem? [Host] [Layout] (i : Nat) :
    Host.exe.2[i]? = Host.prog[i]?.map (fun d => (d, Kraken.Layout.size Directive i)) :=
  Layout.apply_getElem? _ _

public theorem Host.addrOf_succ [Host] [Layout] {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (Kraken.Layout.size Directive k) :=
  Kraken.Executable.addrOf_succ _ (by rw [Host.exe_getElem?, hd]; rfl)

section
variable [Host] [Layout] [hv : Layout.Valid]

public theorem Host.inert_of_size_zero {d : Directive} (h : (d, 0) ∈ Host.exe.2) : d.Inert := by
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp h
  grind [Host.exe_getElem?, Layout.Valid.zero_inert]

public theorem Host.directivesAtAddress_addrOf {k : Nat} {d : Directive} {z : Nat}
    (hd : Host.exe.2[k]? = some (d, z)) (hz : 0 < z) :
    ∃ pre, Host.exe.directivesAtAddress (Host.addrOf k) = pre ++ [(d, z)] ∧
      ∀ c ∈ pre, c.2 = 0 := by
  obtain ⟨j, hjk, hj, hmin⟩ :=
    exists_least_le (P := fun i => Host.exe.addrOf i = Host.exe.addrOf k) rfl
  have hsize := hv.addr_determines_offset j k hj
  have hpre : ∀ c ∈ (Host.exe.2.drop j).take (k - j), c.2 = 0 := by
    have := Host.exe.sizeBefore_add j (k - j)
    rw [Nat.add_sub_cancel' hjk] at this
    have hsum : (((Host.exe.2.drop j).take (k - j)).map (·.2)).sum = 0 := by omega
    exact fun c hc => List.sum_eq_zero_iff_forall_eq_nat.mp hsum _ (List.mem_map_of_mem hc)
  have haddr : ∀ m, j ≤ m → m ≤ k → Host.exe.addrOf m = Host.exe.addrOf k := fun m hjm hmk => by
    grind [Kraken.Executable.addrOf, Host.exe.sizeBefore_mono hjm, Host.exe.sizeBefore_mono hmk]
  have hnext : Host.exe.addrOf (k + 1) ≠ Host.exe.addrOf k := fun h => by
    grind [hv.addr_determines_offset (k + 1) k h]
  refine ⟨(Host.exe.2.drop j).take (k - j), ?_, hpre⟩
  show (((Kraken.Executable.withAddresses (Host.exe.1, Host.exe.2)).dropWhile
    (·.1 ≠ Host.exe.addrOf k)).takeWhile (·.1 = Host.exe.addrOf k)).map (·.2) = _
  rw [Kraken.Executable.withAddresses_dropWhile_addrOf _ j k hj hmin,
    takeWhile_eq_take_of (n := k - j + 1)]
  · rw [List.map_take, List.map_drop, Kraken.Executable.withAddresses_map_snd, List.take_add_one,
      List.getElem?_drop, Nat.add_sub_cancel' hjk, hd]
    rfl
  · intro m hm c hc
    have := haddr (j + m) (by omega) (by omega)
    grind [Kraken.Executable.getElem?_withAddresses_eq]
  · intro c hc
    grind [Kraken.Executable.getElem?_withAddresses_eq]

end
