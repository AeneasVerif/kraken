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
  layout : Layout
  /-- Labels have size zero. -/
  label_size : ∀ i l, prog[i]? = some (.label l) → @Kraken.Layout.size _ layout i = 0
  /-- Any directive that occupies zero space in the executable must be semantically inert. -/
  zero_inert : ∀ i d, prog[i]? = some d → @Kraken.Layout.size _ layout i = 0 → d.Inert
  /-- Two directives at the same address have the same offset in the executable. -/
  addr_determines_offset : ∀ j k, (layout.apply prog).addrOf j = (layout.apply prog).addrOf k →
    (layout.apply prog).sizeBefore j = (layout.apply prog).sizeBefore k

public instance [Host] : Layout := Host.layout

@[expose] public def Host.exe [Host] : Executable := Host.layout.apply Host.prog

@[expose] public def Host.addrOf [Host] (k : Nat) : Int64 := Host.exe.addrOf k

public instance [Host] : Labels := Executable.labels Host.exe

@[grind →] public theorem Host.sizeBefore_eq_of_addrOf_eq [Host] {j k : Nat} (h : Host.addrOf j = Host.addrOf k) :
    Host.exe.sizeBefore j = Host.exe.sizeBefore k :=
  Host.addr_determines_offset j k h

public theorem Host.inert_of_getElem? [Host] {i : Nat} {d : Directive} (h : Host.prog[i]? = some d)
    (hz : Kraken.Layout.size Directive i = 0) : d.Inert :=
  Host.zero_inert i d h hz

@[simp] public theorem Host.exe_getElem? [Host] (i : Nat) :
    Host.exe.program[i]? = Host.prog[i]?.map (fun d => {directive := d, size := Kraken.Layout.size Directive i}) := by
  simp [Host.exe, Kraken.Layout.apply, List.getElem?_mapIdx]

public theorem Host.addrOf_succ [Host] {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (Kraken.Layout.size Directive k) :=
  Kraken.Executable.addrOf_succ _ (c := {directive := d, size := Kraken.Layout.size Directive k}) (by rw [Host.exe_getElem?, hd]; rfl)

section
variable [Host]

@[grind =] public theorem Host.addrOf_def (k : Nat) :
    Host.addrOf k = Host.exe.startAddr + .ofNat (Host.exe.sizeBefore k) := rfl

@[grind →] public theorem Host.sizeBefore_succ {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) :
    Host.exe.sizeBefore (k + 1) = Host.exe.sizeBefore k + Kraken.Layout.size Directive k :=
  Host.exe.sizeBefore_succ (c := {directive := d, size := Kraken.Layout.size Directive k})
    (by rw [Host.exe_getElem?, hd]; rfl)

public theorem Host.sizeBefore_mono {j k : Nat} (h : j ≤ k) : Host.exe.sizeBefore j ≤ Host.exe.sizeBefore k :=
  Host.exe.sizeBefore_mono h

grind_pattern Host.sizeBefore_mono => Host.exe.sizeBefore j, Host.exe.sizeBefore k

public theorem Host.inert_of_size_zero {d : Directive} (h : {directive := d, size := 0} ∈ Host.exe.program) : d.Inert := by
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp h
  grind [Host.exe_getElem?, Host.inert_of_getElem?]

public theorem Host.directivesAtAddress_addrOf {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d)
    (hz : 0 < Kraken.Layout.size Directive k) :
    ∃ pre, Host.exe.directivesAtAddress (Host.addrOf k) =
      pre ++ [{directive := d, size := Kraken.Layout.size Directive k}] ∧ ∀ c ∈ pre, c.size = 0 := by
  have hc : Host.exe.program[k]? = some {directive := d, size := Kraken.Layout.size Directive k} := by
    rw [Host.exe_getElem?, hd]; rfl
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


public theorem Host.nextAddr_addrOf {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d)
    (hz : 0 < Kraken.Layout.size Directive k) :
    Host.exe.nextAddr (Host.addrOf k) = Host.addrOf (k + 1) := by
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hd hz
  have hpre0 : (pre.map (·.size)).sum = 0 := List.sum_eq_zero_iff_forall_eq_nat.mpr fun n hn => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    exact hpre c hc
  rw [Kraken.Executable.nextAddr, hat, List.map_append, List.sum_append, hpre0, Host.addrOf_succ hd]
  simp
end

public structure Embedding [Host] (p : Program) where
  start : Nat
  isInfixAt : p.IsInfixAt Host.prog start

section
variable [Host]

@[expose] public def Embedding.startAddr {p : Program} (e : Embedding p) : Int64 := Host.addrOf e.start

@[expose] public def Embedding.endAddr {p : Program} (e : Embedding p) : Int64 :=
  Host.addrOf (e.start + p.length)


@[grind =] public theorem Embedding.startAddr_def {p : Program} (e : Embedding p) :
    e.startAddr = Host.addrOf e.start := rfl

@[grind =] public theorem Embedding.endAddr_def {p : Program} (e : Embedding p) :
    e.endAddr = Host.addrOf (e.start + p.length) := rfl

@[expose] public def Embedding.head {d : Directive} {p : Program} (e : Embedding (d :: p)) : Embedding [d] :=
  ⟨e.start, List.IsInfixAt.trans (List.isInfixAt_cons_head d p) e.isInfixAt⟩

@[expose] public def Embedding.tail {d : Directive} {p : Program} (e : Embedding (d :: p)) : Embedding p :=
  ⟨e.start + 1, List.IsInfixAt.trans (List.isInfixAt_cons_tail d p) e.isInfixAt⟩

@[simp, grind norm] public theorem Embedding.head_start {d : Directive} {p : Program} (e : Embedding (d :: p)) :
    e.head.start = e.start := rfl

@[simp, grind norm] public theorem Embedding.tail_start {d : Directive} {p : Program} (e : Embedding (d :: p)) :
    e.tail.start = e.start + 1 := rfl
end

public structure Fragment [Host] where
  prog : Program
  embedding : Embedding prog

public class FunDecls [Host] where
  funs : List Fragment

@[expose] public def FunDecls.at [Host] [FunDecls] (a : Int64) : Option Fragment :=
  FunDecls.funs.find? (·.embedding.startAddr == a)

public theorem FunDecls.startAddr_of_at [Host] [FunDecls] {a : Int64} {f : Fragment}
    (h : FunDecls.at a = some f) : f.embedding.startAddr = a := by
  simpa using List.find?_some h
