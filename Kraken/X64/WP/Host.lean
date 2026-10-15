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

public inductive Instr.IsPadding : Instr → Prop
  | nop {asz osz : Width} {n : Nat} : Instr.IsPadding (.regular asz osz (.nop n))
  | nopalign {asz osz : Width} {a : Nat} {p : Option Nat} : Instr.IsPadding (.regular asz osz (.nopalign a p))

attribute [grind cases] Instr.IsPadding

public class Host where
  prog : Program
  layout : Layout
  labels_nodup : (Program.labels prog).Nodup
  /-- Labels have size zero. -/
  label_size : ∀ i l, prog[i]? = some (.label l) → @Kraken.Layout.size _ layout i = 0
  instr_size_pos : ∀ i ins, prog[i]? = some (.instr ins) → ¬ ins.IsPadding → 0 < @Kraken.Layout.size _ layout i
  instr_addr_ne : ∀ i ins, prog[i]? = some (.instr ins) → (layout.apply prog).addrOf i ≠ -1
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
    (hz : Kraken.Layout.size Directive i = 0) : d.Inert :=
  Host.zero_inert i d h hz

@[expose] public def Host.startAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h)

@[expose] public def Host.endAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h + p.length)

export Host (startAddr endAddr)

public theorem Layout.apply_getElem? [layout : Layout] (p : Program) (i : Nat) :
    (layout p).program[i]? = (p[i]?).map (fun d => {directive := d, size := Kraken.Layout.size Directive i}) := by
  simp [Kraken.Layout.apply, List.getElem?_mapIdx]

public theorem Host.exe_getElem? [Host] (i : Nat) :
    Host.exe.program[i]? = Host.prog[i]?.map (fun d => {directive := d, size := Kraken.Layout.size Directive i}) :=
  Layout.apply_getElem? _ _

public theorem Host.addrOf_succ [Host] {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (Kraken.Layout.size Directive k) :=
  Kraken.Executable.addrOf_succ _ (c := {directive := d, size := Kraken.Layout.size Directive k}) (by rw [Host.exe_getElem?, hd]; rfl)

section
variable [Host]

public theorem Host.inert_of_size_zero {d : Directive} (h : {directive := d, size := 0} ∈ Host.exe.program) : d.Inert := by
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp h
  grind [Host.exe_getElem?, Host.inert_of_getElem?]

public theorem Host.directivesAtAddress_addrOf {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) :
    ∃ pre, Host.exe.directivesAtAddress (Host.addrOf k) = pre ++ [c] ∧
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

public theorem Kraken.Executable.label_addrOf (e : Kraken.Executable Directive) (l : Label) (n : Nat)
    (hn : e.program[n]? = some {directive := .label l, size := 0})
    (hfirst : ∀ k z, k < n → e.program[k]? ≠ some {directive := .label l, size := z}) :
    (_root_.Executable.labels e).label l = e.addrOf n := by
  show (e.withAddresses.findSome? _).getD (-1) = e.addrOf n
  rw [findSome?_eq_of (n := n)]
  · rfl
  · simp [Kraken.Executable.getElem?_withAddresses_eq, hn, Kraken.Executable.addrOf]
  · intro k hk
    rcases hm : e.program[k]? with _ | ⟨d, z⟩ <;> simp only [Kraken.Executable.getElem?_withAddresses_eq, hm] <;> simp
    rintro rfl
    exact hfirst k z hk hm

public theorem Host.label_eq [Host] {p : Program} {k i : Nat} {l : Label}
    (hp : p.IsInfixAt Host.prog k) (hi : p[i]? = some (.label l)) :
    label l = Host.addrOf (k + i) := by
  obtain ⟨hlt, hpi⟩ := List.getElem?_eq_some_iff.mp hi
  have hP : Host.prog[k + i]? = some (.label l) := by
    rw [List.isInfixAt_iff_getElem?.mp hp i hlt, hpi]
  have hdir : Host.exe.program[k + i]? = some {directive := .label l, size := 0} := by
    rw [Host.exe_getElem?, hP, Host.label_size _ l hP]
    rfl
  refine Kraken.Executable.label_addrOf Host.exe l (k + i) hdir fun m z hm hdm => ?_
  rw [Host.exe_getElem?] at hdm
  obtain ⟨d', hd', heq⟩ := Option.map_eq_some_iff.mp hdm
  simp only [Kraken.Sized.mk.injEq] at heq
  rw [heq.1] at hd'
  exact absurd (Host.labels_nodup.eq_of_getElem?_label hd' hP) (by omega)

public theorem Host.label_cases [Host] (l : Label) :
    label l = -1 ∨ ∃ i, Host.prog[i]? = some (.label l) ∧ label l = Host.addrOf i := by
  have hl : label l = (Host.exe.withAddresses.findSome?
      (fun {directive, addr, ..} => if directive = .label l then .some addr else .none)).getD (-1) := rfl
  rw [hl]
  cases h : Host.exe.withAddresses.findSome?
      (fun {directive, addr, ..} => if directive = .label l then .some addr else .none) with
  | none => exact Or.inl rfl
  | some a =>
    right
    obtain ⟨x, hx, hfx⟩ := List.exists_of_findSome?_eq_some h
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    rw [Kraken.Executable.getElem?_withAddresses_eq] at hi
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hi
    rw [Host.exe_getElem?] at hc
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hc
    dsimp only at hfx
    split at hfx
    · next hdl =>
      subst hdl
      cases hfx
      exact ⟨i, hd, rfl⟩
    · cases hfx
