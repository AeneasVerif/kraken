module

public import Kraken.Bedrock2.SemanticsLemmas
import all Kraken.Mem

@[expose] public section

open Std Std.ExtHashMap

namespace Kraken.Bedrock2

variable {w : Nat} {ext : ExtSpec w} {e : Env}

def ExtSpec.Responsive (ext : ExtSpec w) : Prop :=
  ∀ t mGive a args post, ext t mGive a args post →
    ∃ mReceive rets, post mReceive rets ∧ ∀ k, k ∈ mReceive → k ∈ mGive

def FreeBlock (m : Mem w) (base : BitVec w) (B : Nat) : Prop :=
  B ≤ 2 ^ w ∧ ∀ i < B, base + .ofNat w i ∉ m

theorem FreeBlock.mono {m m' : Mem w} {base : BitVec w} {B : Nat} (h : FreeBlock m base B)
    (hsub : ∀ k, k ∈ m' → k ∈ m) : FreeBlock m' base B :=
  ⟨h.1, fun i hi hk => h.2 i hi (hsub _ hk)⟩

private theorem mem_of_split {m m1 m2 : Mem w} (h : split m m1 m2) {k : BitVec w} :
    k ∈ m ↔ k ∈ m1 ∨ k ∈ m2 := by
  obtain ⟨rfl, -⟩ := h
  simp [union_eq, mem_union_iff]

private theorem not_mem_of_split {m m1 m2 : Mem w} (h : split m m1 m2) {k : BitVec w}
    (hk : k ∈ m1) : k ∉ m2 := by
  obtain ⟨-, hi⟩ := h
  intro hk2
  exact eq_empty_iff_forall_not_mem.mp hi k (by simp [inter_eq, mem_inter_iff, hk, hk2])

private theorem split_union {m1 m2 : Mem w} (h : ∀ k, k ∈ m1 → k ∉ m2) :
    split (m1.union m2) m1 m2 :=
  ⟨rfl, eq_empty_iff_forall_not_mem.mpr fun k hk => by
    simp only [inter_eq, mem_inter_iff] at hk
    exact h k hk.1 hk.2⟩

private theorem allSome_isSome {α : Type} {l : List (Option α)} {r : List α}
    (h : l.allSome = some r) : ∀ x ∈ l, x.isSome := by
  induction l generalizing r with
  | nil => simp
  | cons x l ih =>
    cases x <;> simp [List.allSome, Option.bind_eq_some_iff] at h
    exact fun y hy => (List.mem_cons.mp hy).elim (by rintro rfl; rfl) (ih h.choose_spec.1 y)

private theorem mem_of_store? {sz : AccessSize} {m m' : Mem w} {a v : BitVec w}
    (hs : store? sz m a v = some m') {k : BitVec w} (hk : k ∈ m') : k ∈ m := by
  simp only [store?, Option.map_eq_some_iff] at hs
  obtain ⟨bs, hl, rfl⟩ := hs
  simp only [Mem.storeInt, Mem.storeBytes, union_eq, mem_union_iff, mem_At_iff,
    Int.toBytes_length] at hk
  rcases hk with hk | ⟨i, hi, rfl⟩
  · exact hk
  · have := allSome_isSome hl _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    exact mem_iff_isSome_getElem?.mpr (by simpa [get?_eq_getElem?] using this)

private theorem ofNat_add_inj {base : BitVec w} {i j : Nat} (hi : i < 2 ^ w) (hj : j < 2 ^ w)
    (h : base + .ofNat w i = base + .ofNat w j) : i = j := by
  have h' := congrArg BitVec.toNat ((BitVec.add_right_inj base).mp h)
  simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using h'

private theorem FreeBlock.stackalloc (fill : UInt8) {m : Mem w} {base : BitVec w} {B n : Nat}
    (hfree : FreeBlock m base B) (hn : n ≤ B) :
    let a := base + .ofNat w (B - n)
    let mStack := (List.replicate n fill).At a
    anybytes a n mStack ∧ (∀ k, k ∈ m → k ∉ mStack) ∧
      FreeBlock (m.union mStack) base (B - n) := by
  obtain ⟨hBw, hfr⟩ := hfree
  have hstk : ∀ k, k ∈ (List.replicate n fill).At (base + .ofNat w (B - n)) ↔
      ∃ i < n, k = base + .ofNat w (B - n + i) := fun k => by
    simp [mem_At_iff, BitVec.add_assoc, BitVec.ofNat_add]
  have hd : ∀ k, k ∈ m → k ∉ (List.replicate n fill).At (base + .ofNat w (B - n)) := by
    intro k hk hk'
    obtain ⟨i, hi, rfl⟩ := (hstk k).1 hk'
    exact hfr _ (by omega) hk
  refine ⟨⟨_, rfl, List.length_replicate, by omega⟩, hd, by omega, fun i hi hk => ?_⟩
  rcases (mem_of_split (split_union hd)).1 hk with hk | hk
  · exact hfr i (by omega) hk
  · obtain ⟨j, hj, hij⟩ := (hstk _).1 hk
    have := ofNat_add_inj (by omega) (by omega) hij
    omega

theorem Exec.exists_post_of_freeBlock (hext : ext.Responsive) {B : Nat} {c : Cmd} {t : Trace w}
    {m : Mem w} {l : Locals w} {post : Trace w → Mem w → Locals w → Prop}
    (h : Exec ext e B c t m l post) {base : BitVec w} (hfree : FreeBlock m base B) :
    ∃ t' m' l', post t' m' l' ∧ ∀ k, k ∈ m' → k ∈ m := by
  induction h generalizing base with
  | skip _ _ _ _ _ hp => exact ⟨_, _, _, hp, fun _ => id⟩
  | set _ _ _ _ _ _ _ _ _ hp => exact ⟨_, _, _, hp, fun _ => id⟩
  | unset _ _ _ _ _ _ hp => exact ⟨_, _, _, hp, fun _ => id⟩
  | store _ _ _ _ _ _ _ _ _ _ _ _ _ hs hp => exact ⟨_, _, _, hp, fun _ => mem_of_store? hs⟩
  | stackalloc x n body B t mSmall l post hn _ ih =>
    obtain ⟨hany, hd, hfree'⟩ := hfree.stackalloc 0 hn
    obtain ⟨t', mC', l', ⟨mS', mSt', hany', hsp', hp⟩, hsub⟩ :=
      ih _ _ _ hany (split_union hd) hfree'
    refine ⟨_, _, _, hp, fun k hk => ?_⟩
    rcases (mem_of_split (split_union hd)).1 (hsub k ((mem_of_split hsp').2 (.inl hk))) with h | h
    · exact h
    · refine absurd ?_ (not_mem_of_split hsp' hk)
      obtain ⟨bs, rfl, hl, -⟩ := hany'
      rw [mem_At_iff] at h ⊢
      simpa [hl] using h
  | if_true _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih hfree
  | if_false _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih hfree
  | seq _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    obtain ⟨_, _, _, hm, hsub⟩ := ih1 hfree
    obtain ⟨_, _, _, hp, hsub'⟩ := ih2 _ _ _ hm (hfree.mono hsub)
    exact ⟨_, _, _, hp, fun k hk => hsub k (hsub' k hk)⟩
  | while_false _ _ _ _ _ _ _ _ _ _ hp => exact ⟨_, _, _, hp, fun _ => id⟩
  | while_true _ _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    obtain ⟨_, _, _, hm, hsub⟩ := ih1 hfree
    obtain ⟨_, _, _, hp, hsub'⟩ := ih2 _ _ _ hm (hfree.mono hsub)
    exact ⟨_, _, _, hp, fun k hk => hsub k (hsub' k hk)⟩
  | call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk ih =>
    obtain ⟨_, _, _, hm, hsub⟩ := ih hfree
    obtain ⟨_, -, _, -, hp⟩ := hk _ _ _ hm
    exact ⟨_, _, _, hp, hsub⟩
  | interact _ _ _ _ _ _ _ _ _ mKeep mGive _ hs _ hx hk =>
    obtain ⟨mR, rets, hmid, hR⟩ := hext _ _ _ _ _ hx
    obtain ⟨l', -, hp⟩ := hk _ _ hmid
    have hd : ∀ k, k ∈ mKeep → k ∉ mR := fun k hk hkR => not_mem_of_split hs hk (hR k hkR)
    exact ⟨_, _, _, hp _ (split_union hd), fun k hk => ((mem_of_split (split_union hd)).1 hk).elim
      (fun hk => (mem_of_split hs).2 (.inl hk)) (fun hk => (mem_of_split hs).2 (.inr (hR k hk)))⟩

theorem Exec.nonvacuous (hext : ext.Responsive) {B : Nat} {c : Cmd} {t : Trace w} {m : Mem w}
    {l : Locals w} {post : Trace w → Mem w → Locals w → Prop} (h : Exec ext e B c t m l post)
    {base : Nat} (hwrap : base + B ≤ 2 ^ w)
    (hfree : ∀ a : BitVec w, base ≤ a.toNat → a.toNat < base + B → a ∉ m) :
    ∃ t' m' l', post t' m' l' := by
  refine (h.exists_post_of_freeBlock hext (base := .ofNat w base) ⟨by omega, fun i hi => ?_⟩).imp
    fun _ => .imp fun _ => .imp fun _ => And.left
  refine hfree _ ?_ ?_ <;>
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod] <;>
    rw [Nat.mod_eq_of_lt (by omega)] <;> omega

theorem Exec.nonvacuous_of_empty (hext : ext.Responsive) {B : Nat} {c : Cmd} {t : Trace w}
    {l : Locals w} {post : Trace w → Mem w → Locals w → Prop} (h : Exec ext e B c t ∅ l post)
    (hB : B < 2 ^ w) : ∃ t' m' l', post t' m' l' :=
  h.nonvacuous hext (base := 1) (by omega) fun _ _ _ => not_mem_empty

private theorem exists_unhit (f : BitVec w → Nat) (n : Nat) :
    ∀ (m : Mem w) (S : List Nat), m.size = n → S.Nodup → n < S.length →
      ∃ j ∈ S, ∀ a, a ∈ m → f a ≠ j := by
  induction n with
  | zero =>
    intro m S hn _ hS
    obtain ⟨j, S', rfl⟩ : ∃ j S', S = j :: S' := by cases S <;> simp_all
    have hm : m = ∅ := eq_empty_iff_size_eq_zero.mpr hn
    exact ⟨j, List.mem_cons_self, fun a ha => absurd ha (hm ▸ not_mem_empty)⟩
  | succ n ih =>
    intro m S hn hnd hS
    have hm : m ≠ ∅ := fun h => by simp [eq_empty_iff_size_eq_zero.mp h] at hn
    obtain ⟨k0, hk0⟩ : ∃ k0, k0 ∈ m :=
      Classical.byContradiction fun h => hm (eq_empty_iff_forall_not_mem.mpr fun a ha => h ⟨a, ha⟩)
    have hsz : (m.erase k0).size = n := by simp [size_erase, hk0, hn]
    have hlen : n < (S.erase (f k0)).length := by
      rw [List.length_erase]
      split <;> omega
    obtain ⟨j, hj, hfj⟩ := ih (m.erase k0) (S.erase (f k0)) hsz (hnd.erase _) hlen
    obtain ⟨hne, hjS⟩ := (hnd.mem_erase_iff).mp hj
    refine ⟨j, hjS, fun a ha => ?_⟩
    by_cases hak : a = k0
    · subst hak
      exact Ne.symm hne
    · exact hfj a (mem_erase.mpr ⟨by simpa using Ne.symm hak, ha⟩)

theorem exists_block_of_size {m : Mem w} {B : Nat} (h : (m.size + 1) * (B + 1) ≤ 2 ^ w) :
    ∃ base : Nat, 0 < base ∧ base + B ≤ 2 ^ w ∧
      ∀ a : BitVec w, base ≤ a.toNat → a.toNat < base + B → a ∉ m := by
  obtain ⟨j, hj, hfj⟩ := exists_unhit (fun a => a.toNat / (B + 1)) _ m (List.range (m.size + 1))
    rfl List.nodup_range (by simp)
  rw [List.mem_range] at hj
  have hjB : (j + 1) * (B + 1) ≤ (m.size + 1) * (B + 1) := Nat.mul_le_mul_right _ (by omega)
  refine ⟨j * (B + 1) + 1, by omega, by rw [Nat.add_mul] at hjB; omega, fun a h1 h2 ha => ?_⟩
  refine hfj a ha (Nat.div_eq_of_lt_le (by omega) ?_)
  rw [Nat.add_mul]
  omega

theorem Exec.nonvacuous_of_size (hext : ext.Responsive) {B : Nat} {c : Cmd} {t : Trace w}
    {m : Mem w} {l : Locals w} {post : Trace w → Mem w → Locals w → Prop}
    (h : Exec ext e B c t m l post) (hsz : (m.size + 1) * (B + 1) ≤ 2 ^ w) :
    ∃ t' m' l', post t' m' l' :=
  let ⟨_, _, hwrap, hfree⟩ := exists_block_of_size hsz
  h.nonvacuous hext hwrap hfree

end Kraken.Bedrock2
