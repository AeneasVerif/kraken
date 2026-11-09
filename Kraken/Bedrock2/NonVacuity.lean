module

public import Kraken.Bedrock2.Interp
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

def Handler.Complete (ext : ExtSpec w) (handler : Handler w) : Prop :=
  ∀ t m mKeep mGive a args mid, split m mKeep mGive → ext t mGive a args mid →
    ∃ mReceive rets, handler t m a args = some (mGive, mReceive, rets) ∧
      ∀ k, k ∈ mReceive → k ∈ mGive

theorem Exec.exists_run {handler : Handler w} (hh : Handler.Ok ext handler)
    (hc : Handler.Complete ext handler) (fill : UInt8) {B : Nat} {c : Cmd} {t : Trace w}
    {m : Mem w} {l : Locals w} {post : Trace w → Mem w → Locals w → Prop}
    (h : Exec ext e B c t m l post) {base : BitVec w} (hfree : FreeBlock m base B) :
    ∃ F o t' m' l', (∀ fuel, F ≤ fuel → ∀ s,
        run e fill fuel c t m l (o ++ s) handler = some (t', m', l', s)) ∧
      (∀ a ∈ o, ∃ i ≤ B, a = base + .ofNat w i) ∧ ∀ k, k ∈ m' → k ∈ m := by
  induction h generalizing base with
  | skip _ t m l =>
    exact ⟨0, [], t, m, l, fun _ _ _ => by simp [run], by simp, fun _ => id⟩
  | set x _ _ t m l _ v hv _ =>
    exact ⟨0, [], t, m, l.insert x v, fun _ _ _ => by simp [run, hv], by simp, fun _ => id⟩
  | unset x _ t m l =>
    exact ⟨0, [], t, m, l.erase x, fun _ _ _ => by simp [run], by simp, fun _ => id⟩
  | store _ _ _ _ t _ l _ _ _ m' ha hv hs _ =>
    exact ⟨0, [], t, m', l, fun _ _ _ => by simp [run, ha, hv, hs], by simp,
      fun _ => mem_of_store? hs⟩
  | stackalloc x n body B t mSmall l post hn hbody ih =>
    have hBw := hfree.1
    obtain ⟨hany, hd, hfree'⟩ := hfree.stackalloc fill hn
    obtain ⟨F, o, t1, m1, l1, hrun, hor, hsub⟩ := ih _ _ _ hany (split_union hd) hfree'
    obtain ⟨mS', mSt', ⟨bs, rfl, hbl, -⟩, hsp', -⟩ :=
      run_of_exec hh (hbody _ _ _ hany (split_union hd)) (hrun F (Nat.le_refl _) [])
    have hc1 : n ≤ 2 ^ w ∧ (List.range n).all
        (fun i => !mSmall.contains (base + .ofNat w (B - n) + .ofNat w i)) = true := by
      refine ⟨by omega, ?_⟩
      simp only [List.all_eq_true, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.eq_false_iff, ne_eq, contains_iff_mem]
      exact fun i hi hk => hd _ hk ((mem_At_iff _ _ _).2 ⟨i, by simp [hi], rfl⟩)
    have hc2 : (List.range n).all
        (fun i => m1.contains (base + .ofNat w (B - n) + .ofNat w i)) = true := by
      simp only [List.all_eq_true, List.mem_range, contains_iff_mem]
      exact fun i hi => (mem_of_split hsp').2 (.inr ((mem_At_iff _ _ _).2 ⟨i, by omega, rfl⟩))
    refine ⟨F, (base + .ofNat w (B - n)) :: o, t1,
      m1.filter fun k _ => !((List.replicate n fill).At (base + .ofNat w (B - n))).contains k, l1,
      fun fuel hF s => ?_, ?_, fun k hk => ?_⟩
    · simp only [run, List.cons_append, hc1, and_self, ite_true, hrun fuel hF s,
        Option.bind_eq_bind, Option.bind_some, hc2, ite_true]
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨B - n, by omega, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := hor a ha
        exact ⟨i, by omega, rfl⟩
    · rw [mem_filter] at hk
      obtain ⟨hk1, hk2⟩ := hk
      rcases (mem_of_split (split_union hd)).1 (hsub k hk1) with h | h
      · exact h
      · rw [getKey_eq] at hk2
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hk2
        rw [← contains_iff_mem, hk2] at h
        exact absurd h Bool.false_ne_true
  | if_true _ _ _ _ _ _ _ _ _ hv hnz _ ih =>
    obtain ⟨F, o, t', m', l', hr, ho, hs⟩ := ih hfree
    exact ⟨F, o, t', m', l', fun fuel hF s => by
      simp only [run, hv, hnz, Option.bind_eq_bind, Option.bind_some, ne_eq, not_false_eq_true,
        ite_true, hr fuel hF s], ho, hs⟩
  | if_false _ _ _ _ _ _ _ _ _ hv hz _ ih =>
    obtain ⟨F, o, t', m', l', hr, ho, hs⟩ := ih hfree
    exact ⟨F, o, t', m', l', fun fuel hF s => by simp [run, hv, hz, hr fuel hF s], ho, hs⟩
  | seq _ _ _ _ _ _ _ _ h1 _ ih1 ih2 =>
    obtain ⟨F1, o1, _, _, _, hr1, ho1, hs1⟩ := ih1 hfree
    have hmid := run_of_exec hh h1 (hr1 F1 (Nat.le_refl _) [])
    obtain ⟨F2, o2, t2, m2, l2, hr2, ho2, hs2⟩ := ih2 _ _ _ hmid (hfree.mono hs1)
    refine ⟨max F1 F2, o1 ++ o2, t2, m2, l2, fun fuel hF s => ?_,
      fun a ha => (List.mem_append.mp ha).elim (ho1 a) (ho2 a), fun k hk => hs1 k (hs2 k hk)⟩
    simp only [run, List.append_assoc, hr1 fuel (by omega) (o2 ++ s), Option.bind_eq_bind,
      Option.bind_some]
    exact hr2 fuel (by omega) s
  | while_false _ _ _ t m l _ _ hv hz _ =>
    refine ⟨1, [], t, m, l, fun fuel hF s => ?_, by simp, fun _ => id⟩
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp [run, hv, hz]
  | while_true _ _ _ _ _ _ _ _ _ hv hnz h1 _ ih1 ih2 =>
    obtain ⟨F1, o1, _, _, _, hr1, ho1, hs1⟩ := ih1 hfree
    have hmid := run_of_exec hh h1 (hr1 F1 (Nat.le_refl _) [])
    obtain ⟨F2, o2, t2, m2, l2, hr2, ho2, hs2⟩ := ih2 _ _ _ hmid (hfree.mono hs1)
    refine ⟨max F1 F2 + 1, o1 ++ o2, t2, m2, l2, fun fuel hF s => ?_,
      fun a ha => (List.mem_append.mp ha).elim (ho1 a) (ho2 a), fun k hk => hs1 k (hs2 k hk)⟩
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [run, hv, hnz, List.append_assoc, hr1 fuel (by omega) (o2 ++ s),
      Option.bind_eq_bind, Option.bind_some, ne_eq, not_false_eq_true, ite_true]
    exact hr2 fuel (by omega) s
  | call _ _ _ _ _ _ _ _ _ _ _ _ hf ha hl hb hk ih =>
    obtain ⟨F, o, t1, m1, l1, hr, ho, hs⟩ := ih hfree
    obtain ⟨rv, hrv, l', hl', -⟩ := hk _ _ _ (run_of_exec hh hb (hr F (Nat.le_refl _) []))
    refine ⟨F + 1, o, t1, m1, l', fun fuel hF s => ?_, ho, hs⟩
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp [run, hf, ha, hl, hr fuel (by omega) s, hrv, hl']
  | interact _ action _ args _ t _ _ _ mKeep mGive _ hs ha hx hk =>
    obtain ⟨mR, rets, hhd, hR⟩ := hc _ _ _ _ _ _ _ hs hx
    obtain ⟨-, hmid⟩ := hh _ _ _ _ _ _ _ _ _ _ hs hx hhd
    obtain ⟨l', hl', -⟩ := hk _ _ hmid
    have hd : ∀ k, k ∈ mKeep → k ∉ mR := fun k hk hkR => not_mem_of_split hs hk (hR k hkR)
    have hemp : mKeep ∩ mR = ∅ := inter_eq.symm.trans (split_union hd).2
    exact ⟨0, [], ((mGive, action, args), (mR, rets)) :: t, mKeep.union mR, l',
      fun _ _ _ => by simp [run, ha, hhd, filter_of_split hs, hemp, hl'], by simp, fun k hk =>
        ((mem_of_split (split_union hd)).1 hk).elim
          (fun hk => (mem_of_split hs).2 (.inl hk)) (fun hk => (mem_of_split hs).2 (.inr (hR k hk)))⟩

theorem Exec.exists_run_post {handler : Handler w} (hh : Handler.Ok ext handler)
    (hc : Handler.Complete ext handler) (fill : UInt8) {B : Nat} {c : Cmd} {t : Trace w}
    {m : Mem w} {l : Locals w} {post : Trace w → Mem w → Locals w → Prop}
    (h : Exec ext e B c t m l post) {base : BitVec w} (hfree : FreeBlock m base B) :
    ∃ fuel o t' m' l', run e fill fuel c t m l o handler = some (t', m', l', []) ∧
      post t' m' l' ∧ ∀ a ∈ o, ∃ i ≤ B, a = base + .ofNat w i := by
  obtain ⟨F, o, t', m', l', hr, ho, -⟩ := h.exists_run hh hc fill hfree
  have hr := hr F (Nat.le_refl _) []
  rw [List.append_nil] at hr
  exact ⟨F, o, t', m', l', hr, run_of_exec hh h hr, ho⟩

theorem Exec.exists_run_of_block {handler : Handler w} (hh : Handler.Ok ext handler)
    (hc : Handler.Complete ext handler) (fill : UInt8) {B : Nat} {c : Cmd} {t : Trace w}
    {m : Mem w} {l : Locals w} {post : Trace w → Mem w → Locals w → Prop}
    (h : Exec ext e B c t m l post) {base : Nat} (hbase : 0 < base) (hwrap : base + B < 2 ^ w)
    (hfree : ∀ a : BitVec w, base ≤ a.toNat → a.toNat < base + B → a ∉ m) :
    ∃ fuel o t' m' l', run e fill fuel c t m l o handler = some (t', m', l', []) ∧
      post t' m' l' ∧ ∀ a ∈ o, a ≠ 0 ∧ base ≤ a.toNat ∧ a.toNat ≤ base + B := by
  have htoNat : ∀ i ≤ B, (BitVec.ofNat w base + .ofNat w i).toNat = base + i := by
    intro i hi
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨fuel, o, t', m', l', hr, hp, ho⟩ := h.exists_run_post hh hc fill
    (base := .ofNat w base) ⟨by omega, fun i hi => hfree _ (by rw [htoNat i (by omega)]; omega)
      (by rw [htoNat i (by omega)]; omega)⟩
  refine ⟨fuel, o, t', m', l', hr, hp, fun a ha => ?_⟩
  obtain ⟨i, hi, rfl⟩ := ho a ha
  refine ⟨fun h0 => ?_, by rw [htoNat i hi]; omega, by rw [htoNat i hi]; omega⟩
  have := congrArg BitVec.toNat h0
  rw [htoNat i hi] at this
  simp at this
  omega

end Kraken.Bedrock2
