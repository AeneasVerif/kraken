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


/-! ## Words and slots -/

theorem toBytes_ofInt_ofBytes {bs : List UInt8} (hl : bs.length = 8) :
    Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes bs)).toInt = bs := by
  rw [← Int.toBytes_emod]
  have h1 : ((BitVec.ofInt 64 (Int.ofBytes bs)).toInt).take (8 * 8) =
      (Int.ofBytes bs).take (8 * 8) := by
    simp only [Int.take, BitVec.toInt_ofInt]
    exact Int.bmod_emod
  rw [h1, Int.toBytes_emod, ← hl]
  exact Int.toBytes_ofBytes_all bs

/-- Owned 8 bytes always hold some word. -/
theorem region_word {a : Val} {f : Mem 64} : region a 8 f ↔ ∃ v, word a v f :=
  ⟨fun ⟨bs, hl, hf⟩ => ⟨BitVec.ofInt 64 (Int.ofBytes bs), by
      show (Int.toBytes 8 _).At a = f
      rw [toBytes_ofInt_ofBytes hl]; exact hf.symm⟩,
   fun ⟨_, h⟩ => word_region h⟩

theorem slots_nil {a : Val} : slots a [] = ExtHashMap.emp := rfl

theorem slots_cons {a v : Val} {vs : List Val} : slots a (v :: vs) = word a v ⋆ slots (a + 8#64) vs :=
  rfl

theorem slots_append {a : Val} (σ₁ σ₂ : List Val) :
    slots a (σ₁ ++ σ₂) = slots a σ₁ ⋆ slots (a + BitVec.ofNat 64 (8 * σ₁.length)) σ₂ := by
  induction σ₁ generalizing a with
  | nil => simp [slots_nil, ExtHashMap.emp_sep]
  | cons v vs ih =>
    have e : a + 8#64 + BitVec.ofNat 64 (8 * vs.length) =
        a + BitVec.ofNat 64 (8 * (v :: vs).length) := by
      simp only [List.length_cons]
      rw [BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [List.cons_append, slots_cons, slots_cons, ih, e, ExtHashMap.sep_assoc]

/-- Slot `i` of `σ` in isolation. -/
theorem slots_get {a : Val} (σ : List Val) (i : Nat) (hi : i < σ.length) :
    slots a σ = slots a (σ.take i) ⋆
      (word (a + BitVec.ofNat 64 (8 * i)) σ[i] ⋆
        slots (a + BitVec.ofNat 64 (8 * i) + 8#64) (σ.drop (i + 1))) := by
  conv => lhs; rw [← List.take_append_drop i σ, List.drop_eq_getElem_cons hi]
  rw [slots_append, slots_cons, List.length_take_of_le (by omega)]

/-- Slots are owned memory. -/
theorem slots_region {a : Val} {σ : List Val} {f : Mem 64} (hσ : 8 * σ.length ≤ 2 ^ 64)
    (h : slots a σ f) : region a (8 * σ.length) f := by
  induction σ generalizing a f with
  | nil => show region a 0 f; rw [region_zero]; exact h
  | cons v vs ih =>
    have e : 8 * (v :: vs).length = 8 + 8 * vs.length := by simp; omega
    rw [e, region_split (by simp at hσ; omega)]
    exact sep_mono (fun _ => word_region) (sep_mono_r (fun _ => ih (by simp at hσ; omega)) h)

/-- Owned memory holds some slots. -/
theorem region_slots {a : Val} {n : Nat} {f : Mem 64} (hn : 8 * n ≤ 2 ^ 64)
    (h : region a (8 * n) f) : ∃ σ : List Val, σ.length = n ∧ slots a σ f := by
  induction n generalizing a f with
  | zero => exact ⟨[], rfl, by rw [region_zero] at h; exact h⟩
  | succ n ih =>
    have e : 8 * (n + 1) = 8 + 8 * n := by omega
    rw [e, region_split (by omega)] at h
    obtain ⟨f1, f2, hu, hd, h1, h2⟩ := h
    obtain ⟨v, hv⟩ := region_word.mp h1
    obtain ⟨σ, hl, hσ⟩ := ih (by omega) h2
    exact ⟨v :: σ, by simp [hl], f1, f2, hu, hd, hv, hσ⟩

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

/-! ## Function contracts: weakening and linking -/

/-- A contract for a stronger source spec. -/
theorem FnSpec.of_spec {h : T.Host} {sym : String} {spec spec' : Spec} {n nX : Nat}
    (hf : T.FnSpec h sym spec n nX) (hs : ∀ args m Q X, spec' args m Q X → spec args m Q X) :
    T.FnSpec h sym spec' n nX :=
  fun args m Q X hspec => hf args m Q X (hs args m Q X hspec)

/-- A contract with a smaller exit stack guarantee. -/
theorem FnSpec.mono_exit {h : T.Host} {sym : String} {spec : Spec} {n nX nX' : Nat}
    (hf : T.FnSpec h sym spec n nX) (hX : nX' ≤ nX) : T.FnSpec h sym spec n nX' := by
  intro args m Q X hspec s ra R ha hr hsp hmem
  refine eventually_weaken _ _ _ _ ?_ (hf args m Q X hspec s ra R ha hr hsp hmem)
  rintro st (hret | ⟨sym', as, m', hX', hd, hpc, has, hsp', ra', n', F, hn', hb', hra', hm'⟩)
  · exact Or.inl hret
  · exact Or.inr ⟨sym', as, m', hX', hd, hpc, has, hsp', ra', n', F, by omega, hb', hra', hm'⟩

/-- A contract with a larger stack bound: the extra stack is part of the caller's frame. -/
theorem FnSpec.mono_stack {h : T.Host} {sym : String} {spec : Spec} {n n' nX : Nat}
    (hf : T.FnSpec h sym spec n nX) (hn : n ≤ n') (hn' : n' + T.raBytes ≤ 2 ^ 64) :
    T.FnSpec h sym spec n' nX := by
  intro args m Q X hspec s ra R ha hr hsp hmem
  -- `region (sp - n') n' = region (sp - n') (n' - n) ⋆ region (sp - n) n`
  have eaddr : T.get s T.sp - BitVec.ofNat 64 n' + BitVec.ofNat 64 (n' - n) =
      T.get s T.sp - BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    have := (T.get s T.sp).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hsplit : region (T.get s T.sp - BitVec.ofNat 64 n') n' =
      region (T.get s T.sp - BitVec.ofNat 64 n') (n' - n) ⋆
        region (T.get s T.sp - BitVec.ofNat 64 n) n := by
    have := region_split (a := T.get s T.sp - BitVec.ofNat 64 n') (n1 := n' - n) (n2 := n)
      (by omega)
    rw [Nat.sub_add_cancel hn, eaddr] at this
    exact this
  have hmem' : (T.mem s =⋆ Eq m ⋆ T.Entry (T.get s T.sp) ra n ⋆
      (region (T.get s T.sp - BitVec.ofNat 64 n') (n' - n) ⋆ R)) := by
    have : (Eq m ⋆ T.Entry (T.get s T.sp) ra n' ⋆ R) =
        (Eq m ⋆ T.Entry (T.get s T.sp) ra n ⋆
          (region (T.get s T.sp - BitVec.ofNat 64 n') (n' - n) ⋆ R)) := by
      simp only [Target.Entry, hsplit]; ac_rfl
    exact this ▸ hmem
  refine eventually_weaken _ _ _ _ ?_ (hf args m Q X hspec s ra _ ha hr hsp hmem')
  rintro st (⟨hpc, rets, m', hQ, hrets, hres, hm⟩ |
    ⟨sym', as, m', hX', hd, hpc, has, hsp', ra', n'', F, hn'', hb'', hra', hm⟩)
  · refine Or.inl ⟨hpc, rets, m', hQ, hrets, hres, ?_⟩
    have hsplit' : T.Exit (T.get s T.sp) n' =
        region (T.get s T.sp - BitVec.ofNat 64 n') (n' - n) ⋆ T.Exit (T.get s T.sp) n := by
      simp only [Target.Exit]
      have := region_split (a := T.get s T.sp - BitVec.ofNat 64 n') (n1 := n' - n)
        (n2 := n + T.raBytes) (by omega)
      rw [show n' - n + (n + T.raBytes) = n' + T.raBytes by omega, eaddr] at this
      exact this
    have : (Eq m' ⋆ T.Exit (T.get s T.sp) n' ⋆ R) =
        (Eq m' ⋆ T.Exit (T.get s T.sp) n ⋆
          (region (T.get s T.sp - BitVec.ofNat 64 n') (n' - n) ⋆ R)) := by
      rw [hsplit']; ac_rfl
    exact this ▸ hm
  · refine Or.inr ⟨sym', as, m', hX', hd, hpc, has, hsp', ra', n'', F ⋆
      region (T.get s T.sp - BitVec.ofNat 64 n') (n' - n), hn'', hb'', hra', ?_⟩
    have : (Eq m' ⋆ T.Entry (T.get (T.data st) T.sp) ra' n'' ⋆ F ⋆
          (region (T.get s T.sp - BitVec.ofNat 64 n') (n' - n) ⋆ R)) =
        (Eq m' ⋆ T.Entry (T.get (T.data st) T.sp) ra' n'' ⋆
          (F ⋆ region (T.get s T.sp - BitVec.ofNat 64 n') (n' - n)) ⋆ R) := by
      ac_rfl
    exact this ▸ hm

/--
Linking (decision D6: acyclic call graph). Functions `fs` listed callees first: if each function's
contract holds in host `h` as soon as the contracts of the functions before it hold, then all hold.
The per-function premise is what the compiler theorem gives for a function whose callees are
earlier in the list (and what hand-written code or an external assumption gives otherwise).
-/
theorem link {h : T.Host} (Γ : Env) (bound : String → Nat) (nX : Nat) :
    ∀ fs : List String,
      (∀ (pre : List String) (f : String) (post : List String), fs = pre ++ f :: post →
        (∀ g, g ∈ pre → T.FnSpec h g (Γ g) (bound g) nX) → T.FnSpec h f (Γ f) (bound f) nX) →
      ∀ f, f ∈ fs → T.FnSpec h f (Γ f) (bound f) nX := by
  intro fs hstep
  have key : ∀ k, k ≤ fs.length → ∀ g, g ∈ fs.take k → T.FnSpec h g (Γ g) (bound g) nX := by
    intro k
    induction k with
    | zero => intro _ g hg; simp at hg
    | succ k ih =>
      intro hk g hg
      have hk' : k < fs.length := by omega
      rw [List.take_add_one, List.getElem?_eq_getElem hk'] at hg
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact ih (by omega) g hg
      · exact hstep (fs.take k) fs[k] (fs.drop (k + 1))
          (by rw [← List.drop_eq_getElem_cons hk', List.take_append_drop]) (ih (by omega))
  intro f hf
  exact key fs.length (Nat.le_refl _) f (by simpa using hf)

end Target

end LeanQbe
