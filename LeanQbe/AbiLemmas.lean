module

public import LeanQbe.Abi
import all Kraken.Mem
import all Kraken.Separation

/-!
# Lemmas about `LeanQbe.Abi` and the memory operations of `LeanQbe.Ops`

* Framing: `loadVal`, `storeOk` and `storeMem` on a source memory `m` carry over to any machine
  memory `M` with `(Eq m ⋆ F) M`, and `storeMem` preserves the split.
* `sep_mono`, `sep_mono_r`: monotonicity of `⋆`.
* `Target.entry_exit`, `Target.retAddr_of_entry`, `Target.exit_of_entry`: from the callee's stack
  footprint on entry to the one on exit.

Generic: imports neither `Kraken.X64` nor `Kraken.AArch64`.
-/

@[expose] public section

open Std

namespace LeanQbe

/-! ## Separation logic -/

theorem sep_mono {P P' Q : Mem 64 → Prop} (h : ∀ x, P x → P' x) {M : Mem 64} :
    (P ⋆ Q) M → (P' ⋆ Q) M := by
  rintro ⟨a, b, hu, hd, ha, hb⟩
  exact ⟨a, b, hu, hd, h a ha, hb⟩

theorem sep_mono_r {P Q Q' : Mem 64 → Prop} (h : ∀ x, Q x → Q' x) {M : Mem 64} :
    (P ⋆ Q) M → (P ⋆ Q') M := by
  rintro ⟨a, b, hu, hd, ha, hb⟩
  exact ⟨a, b, hu, hd, ha, h b hb⟩

/-! ## Framing the memory operations -/

private theorem allSome_isSome {α : Type} :
    ∀ {l : List (Option α)} {bs : List α}, l.allSome = some bs → ∀ x ∈ l, x.isSome
  | [], _, _, x, hx => by cases hx
  | y :: l, bs, h, x, hx => by
    simp only [List.allSome, List.mapM_cons, id, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, rfl, bs', hl, -⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · exact allSome_isSome hl x hx

/-- The bytes a successful `loadBytes` reads are mapped. -/
theorem Mem.mem_of_loadBytes {w : Nat} {m : Mem w} {a : BitVec w} {n : Nat} {bs : List UInt8}
    (h : m.loadBytes a n = some bs) {i : Nat} (hi : i < n) : a + BitVec.ofNat w i ∈ m := by
  have := allSome_isSome h (m.get? (a + BitVec.ofNat w i))
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  rwa [ExtHashMap.get?_eq_getElem?, ← ExtHashMap.mem_iff_isSome_getElem?] at this

/-- In a disjoint union, the left part's entries are unchanged. -/
private theorem getElem?_union_left {m b : Mem 64} (hd : m.inter b = ∅) {k : BitVec 64}
    (hk : k ∈ m) : (m.union b)[k]? = m[k]? := by
  have hkb : k ∉ b := fun hkb =>
    (ExtHashMap.eq_empty_iff_forall_not_mem.mp hd k)
      (by rw [ExtHashMap.inter_eq, ExtHashMap.mem_inter_iff]; exact ⟨hk, hkb⟩)
  rw [ExtHashMap.union_eq, ExtHashMap.getElem?_union, ExtHashMap.getElem?_eq_none hkb]
  simp

private theorem loadBytes_frame {m M : Mem 64} {F : Mem 64 → Prop} (hM : (Eq m ⋆ F) M)
    {a : BitVec 64} {n : Nat} {bs : List UInt8} (h : m.loadBytes a n = some bs) :
    M.loadBytes a n = some bs := by
  obtain ⟨m1, b, rfl, hd, rfl, -⟩ := hM
  rw [← h, Mem.loadBytes, Mem.loadBytes]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ExtHashMap.get?_eq_getElem?, ExtHashMap.get?_eq_getElem?,
    getElem?_union_left hd (Mem.mem_of_loadBytes h (List.mem_range.mp hi))]

private theorem loadInt_frame {m M : Mem 64} {F : Mem 64 → Prop} (hM : (Eq m ⋆ F) M)
    {a : BitVec 64} {n : Nat} {i : Int} (h : m.loadInt a n = some i) :
    M.loadInt a n = some i := by
  rw [Mem.loadInt, Option.map_eq_some_iff] at h
  obtain ⟨bs, hbs, rfl⟩ := h
  rw [Mem.loadInt, loadBytes_frame hM hbs]
  rfl

theorem loadVal_frame {m M : Mem 64} {F : Mem 64 → Prop} (hM : (Eq m ⋆ F) M) {k : Cls} {sz : Sz}
    {sg : Bool} {a v : Val} (h : loadVal m k sz sg a = some v) : loadVal M k sz sg a = some v := by
  rw [loadVal, Option.map_eq_some_iff] at h
  obtain ⟨i, hi, rfl⟩ := h
  rw [loadVal, loadInt_frame hM hi]
  rfl

theorem storeOk_frame {m M : Mem 64} {F : Mem 64 → Prop} (hM : (Eq m ⋆ F) M) {sz : Sz} {a : Val}
    (h : storeOk m sz a) : storeOk M sz a := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, loadInt_frame hM hi⟩

/-- Storing into mapped bytes of the source memory preserves the split. -/
theorem Mem.storeInt_frame {m M : Mem 64} {F : Mem 64 → Prop} (hM : (Eq m ⋆ F) M) {a : BitVec 64}
    {n : Nat} (hmap : ∀ i < n, a + BitVec.ofNat 64 i ∈ m) (v : Int) :
    (Eq (m.storeInt a n v) ⋆ F) (M.storeInt a n v) := by
  obtain ⟨m1, b, rfl, hd, hm, hF⟩ := hM
  subst hm
  have hsub : ∀ k, k ∈ (Int.toBytes n v).At a → k ∈ m := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hk
    exact hmap i (by simpa [Int.toBytes_length] using hi)
  have hnb : ∀ k, k ∈ m → k ∉ b := fun k hk hkb =>
    (ExtHashMap.eq_empty_iff_forall_not_mem.mp hd k)
      (by rw [ExtHashMap.inter_eq, ExtHashMap.mem_inter_iff]; exact ⟨hk, hkb⟩)
  refine ⟨m.storeInt a n v, b, ?_, ?_, rfl, hF⟩
  · simp only [Mem.storeInt, Mem.storeBytes]
    apply ExtHashMap.ext_getElem?
    intro k
    simp only [ExtHashMap.union_eq, ExtHashMap.getElem?_union]
    by_cases hk : k ∈ (Int.toBytes n v).At a
    · rw [ExtHashMap.getElem?_eq_none (hnb k (hsub k hk))]
      simp
    · rw [ExtHashMap.getElem?_eq_none hk]
      simp
  · simp only [Mem.storeInt, Mem.storeBytes]
    apply ExtHashMap.eq_empty_iff_forall_not_mem.mpr
    intro k hk
    rw [ExtHashMap.inter_eq, ExtHashMap.mem_inter_iff, ExtHashMap.union_eq,
      ExtHashMap.mem_union_iff] at hk
    obtain ⟨hk1 | hk1, hk2⟩ := hk
    · exact hnb k hk1 hk2
    · exact hnb k (hsub k hk1) hk2

theorem storeMem_frame {m M : Mem 64} {F : Mem 64 → Prop} (hM : (Eq m ⋆ F) M) {sz : Sz} {a : Val}
    (h : storeOk m sz a) (v : Val) : (Eq (storeMem m sz a v) ⋆ F) (storeMem M sz a v) := by
  obtain ⟨i, hi⟩ := h
  rw [Mem.loadInt, Option.map_eq_some_iff] at hi
  obtain ⟨bs, hbs, -⟩ := hi
  have hmap := fun j (hj : j < sz.bytes) => Mem.mem_of_loadBytes hbs hj
  cases sz <;> exact Mem.storeInt_frame hM hmap _

/-! ## Regions and words -/

/-- The 8 bytes at `a` hold `v` (little endian), as an x64 or AArch64 64-bit store leaves them. -/
def word (a v : Val) : Mem 64 → Prop := Eq ((Int.toBytes 8 v.toInt).At a)

theorem word_region {a v : Val} {f : Mem 64} (h : word a v f) : region a 8 f :=
  ⟨Int.toBytes 8 v.toInt, Int.toBytes_length _ _, h.symm⟩

/-- A region in a separating conjunction has concrete bytes. -/
theorem region_sep_elim {a : BitVec 64} {n : Nat} {F : Mem 64 → Prop} {M : Mem 64}
    (h : (region a n ⋆ F) M) : ∃ bs : List UInt8, bs.length = n ∧ (Eq (bs.At a) ⋆ F) M := by
  obtain ⟨f1, f2, hu, hd, ⟨bs, hl, rfl⟩, hF⟩ := h
  exact ⟨bs, hl, _, f2, hu, hd, rfl, hF⟩

theorem region_split {a : BitVec 64} {n1 n2 : Nat} (h : n1 + n2 ≤ 2 ^ 64) :
    region a (n1 + n2) = region a n1 ⋆ region (a + BitVec.ofNat 64 n1) n2 := by
  funext f
  apply propext
  constructor
  · rintro ⟨bs, hl, rfl⟩
    have e := Mem.At_append_sep (bs.take n1) (bs.drop n1) a (by simp; omega)
    rw [List.take_append_drop, List.length_take, Nat.min_eq_left (by omega)] at e
    obtain ⟨f1, f2, hu, hd, h1, h2⟩ := (congrFun e (bs.At a)).mp rfl
    exact ⟨f1, f2, hu, hd, ⟨_, by simp; omega, h1.symm⟩, ⟨_, by simp; omega, h2.symm⟩⟩
  · rintro ⟨f1, f2, hu, hd, ⟨bs1, hl1, rfl⟩, ⟨bs2, hl2, rfl⟩⟩
    have e := Mem.At_append_sep bs1 bs2 a (by omega)
    rw [hl1] at e
    exact ⟨bs1 ++ bs2, by simp; omega, ((congrFun e f).mpr ⟨_, _, hu, hd, rfl, rfl⟩).symm⟩

theorem region_zero {a : BitVec 64} : region a 0 = ExtHashMap.emp := by
  funext f
  apply propext
  constructor
  · rintro ⟨bs, hl, rfl⟩
    rw [List.length_eq_zero_iff] at hl
    subst hl
    simp [ExtHashMap.emp, List.At]
  · intro hf
    refine ⟨[], rfl, ?_⟩
    simp [ExtHashMap.emp] at hf
    simp [hf, List.At]

/-! ## Stack footprints -/

namespace Target

variable (T : Target)

theorem entry_exit {sp : Val} {ra : T.Addr} {n : Nat} (hn : n + T.raBytes ≤ 2 ^ 64)
    {f : Mem 64} : T.Entry sp ra n f → T.Exit sp n f := by
  rintro ⟨f1, f2, rfl, hd, ⟨bs1, hl1, rfl⟩, hra⟩
  obtain ⟨bs2, hl2, rfl⟩ := T.retAddr_region _ _ _ hra
  refine ⟨bs1 ++ bs2, by simp [hl1, hl2], ?_⟩
  have := Mem.At_append_sep bs1 bs2 (sp - BitVec.ofNat 64 n) (by omega)
  rw [hl1, BitVec.sub_add_cancel] at this
  exact ((congrFun this _).mpr ⟨_, _, rfl, hd, rfl, rfl⟩).symm

theorem retAddr_of_entry' {m : Mem 64} {sp : Val} {ra : T.Addr} {n : Nat} {R : Mem 64 → Prop}
    {M : Mem 64} (h : (Eq m ⋆ T.Entry sp ra n ⋆ R) M) :
    (T.RetAddr sp ra ⋆ (Eq m ⋆ region (sp - BitVec.ofNat 64 n) n ⋆ R)) M := by
  have e : (Eq m ⋆ T.Entry sp ra n ⋆ R) =
      (T.RetAddr sp ra ⋆ (Eq m ⋆ region (sp - BitVec.ofNat 64 n) n ⋆ R)) := by
    simp only [Entry]; ac_rfl
  exact e ▸ h

theorem retAddr_of_entry {m : Mem 64} {sp : Val} {ra : T.Addr} {n : Nat} {R : Mem 64 → Prop}
    {M : Mem 64} (h : (Eq m ⋆ T.Entry sp ra n ⋆ R) M) : ∃ R', (T.RetAddr sp ra ⋆ R') M :=
  ⟨_, T.retAddr_of_entry' h⟩

theorem exit_of_entry {m : Mem 64} {sp : Val} {ra : T.Addr} {n : Nat} {R : Mem 64 → Prop}
    {M : Mem 64} (hn : n + T.raBytes ≤ 2 ^ 64) :
    (Eq m ⋆ T.Entry sp ra n ⋆ R) M → (Eq m ⋆ T.Exit sp n ⋆ R) M :=
  sep_mono fun _ => sep_mono_r fun _ => T.entry_exit hn

/-- `exit_of_entry` with the frame associated to the right on entry (the shape of
`Rega.MemFacts.exit`). -/
theorem exit_of_entry_assoc {m : Mem 64} {sp : Val} {ra : T.Addr} {n : Nat} {R : Mem 64 → Prop}
    {M : Mem 64} (hn : n + T.raBytes ≤ 2 ^ 64) :
    (Eq m ⋆ (T.Entry sp ra n ⋆ R)) M → (Eq m ⋆ T.Exit sp n ⋆ R) M := by
  rw [← ExtHashMap.sep_assoc]
  exact T.exit_of_entry hn

end Target

end LeanQbe
