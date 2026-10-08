module

public import Kraken.X64.Semantics
public import Kraken.X64.Inert
public import Kraken.Data.List.Infix

private theorem findSome?_eq_of {α β : Type _} {f : α → Option β} {l : List α} :
    ∀ {n : Nat} {b : β}, l[n]?.bind f = some b →
      (∀ k, k < n → l[k]?.bind f = none) → l.findSome? f = some b := by
  induction l with
  | nil => intro n b hn _; simp at hn
  | cons x xs ih =>
    intro n b hn hlt
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.bind_some] at hn
      simp [hn]
    | succ m =>
      have h0 : f x = none := by simpa using hlt 0 (Nat.succ_pos m)
      rw [List.findSome?_cons, h0,
        ih (by simpa using hn) (fun k hk => by simpa using hlt (k + 1) (by omega))]

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

namespace Kraken.Executable

public theorem label_addrOf (e : Kraken.Executable Directive) (l : Label) (n : Nat)
    (hn : e.2[n]? = some (.label l, 0))
    (hfirst : ∀ k z, k < n → e.2[k]? ≠ some (.label l, z)) :
    (_root_.Executable.labels e).label l = e.addrOf n := by
  show (e.withAddresses.findSome? _).getD (-1) = e.addrOf n
  rw [findSome?_eq_of (n := n)]
  · rfl
  · show ((Kraken.Executable.withAddresses (e.1, e.2))[n]?.bind _) = _
    simp [getElem?_withAddresses_eq, hn, addrOf]
  · intro k hk
    show ((Kraken.Executable.withAddresses (e.1, e.2))[k]?.bind _) = _
    rcases hm : e.2[k]? with _ | ⟨d, z⟩ <;> simp only [getElem?_withAddresses_eq, hm] <;> simp
    rintro rfl
    exact hfirst k z hk hm

end Kraken.Executable

public class Host where
  prog : Program
  labels_nodup : (Program.labels prog).Nodup

@[expose] public def Host.exe [Host] [layout : Layout] : Executable := layout Host.prog

@[expose] public def Host.addrOf [Host] [Layout] (k : Nat) : Int64 := Host.exe.addrOf k

public instance [Host] [Layout] : Labels := Executable.labels Host.exe

/-- A set of abstract assumptions about the `Layout` of a `Host` program that most specs need and
that every reasonable assembler satisfies. -/
public class Layout.Valid [Host] [Layout] : Prop where
  /-- Labels have size zero. -/
  label_size : ∀ i l, Host.prog[i]? = some (.label l) → Kraken.Layout.size Directive i = 0
  /-- Any directive that occupies zero space in the executable must be semantically inert. -/
  zero_inert : ∀ i d, Host.prog[i]? = some d → Kraken.Layout.size Directive i = 0 → d.Inert
  /-- The laid out executable fits into 2^64 bytes of address space. -/
  fits : ∀ j k m, j ≤ m → m < k → k ≤ Host.prog.length →
    Host.addrOf j = Host.addrOf k → Kraken.Layout.size Directive m = 0

@[expose] public def Host.startAddr [Host] [Layout] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h)

@[expose] public def Host.endAddr [Host] [Layout] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h + p.length)

export Host (startAddr endAddr)

public theorem Layout.apply_getElem? [layout : Layout] (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  simp [Kraken.Layout.apply, List.getElem?_mapIdx]

public theorem Layout.length_apply [layout : Layout] (p : Program) : (layout p).2.length = p.length := by
  simp [Kraken.Layout.apply]

public theorem Host.exe_getElem? [Host] [Layout] (i : Nat) :
    Host.exe.2[i]? = Host.prog[i]?.map (fun d => (d, Kraken.Layout.size Directive i)) :=
  Layout.apply_getElem? _ _

public theorem Host.length_exe [Host] [Layout] : Host.exe.2.length = Host.prog.length :=
  Layout.length_apply _

public theorem Host.addrOf_zero [Host] [Layout] : Host.addrOf 0 = Kraken.Layout.start Directive := by
  simp [Host.addrOf, Host.exe, Kraken.Layout.apply]

public theorem Host.addrOf_succ [Host] [Layout] {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (Kraken.Layout.size Directive k) :=
  Kraken.Executable.addrOf_succ _ (by rw [Host.exe_getElem?, hd]; rfl)

section
variable [Host] [Layout] [hv : Layout.Valid]

public theorem Host.inert_of_size_zero {m : Nat} {d : Directive}
    (h : Host.exe.2[m]? = some (d, 0)) : d.Inert := by
  grind [Host.exe_getElem?, Layout.Valid.zero_inert]

private theorem Host.zero_between {j m n : Nat} (hjm : j ≤ m) (hmn : m < n) (hn : n ≤ Host.prog.length)
    (heq : Host.addrOf j = Host.addrOf n) :
    ∃ d, Host.exe.2[m]? = some (d, 0) := by
  refine ⟨Host.prog[m], ?_⟩
  rw [Host.exe_getElem?, List.getElem?_eq_getElem (by omega), hv.fits j n m hjm hmn hn heq]
  rfl

private theorem Host.inert_between {j j' : Nat}
    (hzero : ∀ m, j ≤ m → m < j' → ∃ d, Host.exe.2[m]? = some (d, 0)) :
    ∀ c ∈ (Host.exe.2.drop j).take (j' - j), c.2 = 0 ∧ c.1.Inert := by
  intro c hc
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
  have := hzero (j + m) (by grind) (by grind)
  grind [Host.inert_of_size_zero]

public theorem Host.directivesAtAddress_addrOf {k : Nat} {d : Directive} {z : Nat}
    (hd : Host.exe.2[k]? = some (d, z)) (hz : 0 < z) :
    ∃ pre, Host.exe.directivesAtAddress (Host.addrOf k) = pre ++ [(d, z)] ∧
      ∀ c ∈ pre, c.2 = 0 ∧ c.1.Inert := by
  have hk : k < Host.prog.length := by
    rw [← Host.length_exe]; exact (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨j, hjk, hj, hmin⟩ :=
    exists_least_le (P := fun i => Host.exe.addrOf i = Host.exe.addrOf k) rfl
  have hzero : ∀ m, j ≤ m → m < k → ∃ d, Host.exe.2[m]? = some (d, 0) :=
    fun m hjm hmk => Host.zero_between hjm hmk (Nat.le_of_lt hk) hj
  have haddr : ∀ m, j ≤ m → m ≤ k → Host.exe.addrOf m = Host.exe.addrOf k := by
    intro m
    induction m with
    | zero => grind
    | succ m ih =>
      intro hjm hmk
      by_cases hjm' : j = m + 1
      · grind
      · obtain ⟨d', hd'⟩ := hzero m (by omega) (by omega)
        rw [Kraken.Executable.addrOf_succ _ hd', ih (by omega) (by omega)]
        simp
  have hnext : Host.exe.addrOf (k + 1) ≠ Host.exe.addrOf k := fun h => by
    have := hv.fits k (k + 1) k (Nat.le_refl _) (Nat.lt_succ_self _) (by omega) h.symm
    grind [Host.exe_getElem?]
  refine ⟨(Host.exe.2.drop j).take (k - j), ?_, Host.inert_between hzero⟩
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

public theorem Host.fetch?_addrOf {k : Nat} {d : Directive} {z : Nat}
    (hd : Host.exe.2[k]? = some (d, z)) (hz : 0 < z) :
    Host.exe.fetch? (Host.addrOf k) = some (d, z) := by
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hd hz
  unfold Kraken.Executable.fetch?
  rw [hat, List.find?_append, List.find?_eq_none.mpr fun c hc => by simp [(hpre c hc).1]]
  simp [hz]

public theorem Host.label_eq {p : Program} {k i : Nat} {l : Label}
    (hp : p.IsInfixAt Host.prog k) (hi : p[i]? = some (.label l)) :
    label l = Host.addrOf (k + i) := by
  obtain ⟨hlt, hpi⟩ := List.getElem?_eq_some_iff.mp hi
  have hP : Host.prog[k + i]? = some (.label l) := by
    rw [List.isInfixAt_iff_getElem?.mp hp i hlt, hpi]
  have hdir : Host.exe.2[k + i]? = some (.label l, 0) := by
    rw [Host.exe_getElem?, hP, hv.label_size _ l hP]
    rfl
  refine Kraken.Executable.label_addrOf Host.exe l (k + i) hdir fun m z hm hdm => ?_
  rw [Host.exe_getElem?] at hdm
  obtain ⟨d', hd', heq⟩ := Option.map_eq_some_iff.mp hdm
  simp only [Prod.mk.injEq] at heq
  rw [heq.1] at hd'
  exact absurd (Host.labels_nodup.eq_of_getElem?_label hd' hP) (by omega)

end
