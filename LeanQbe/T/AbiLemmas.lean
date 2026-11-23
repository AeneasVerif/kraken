module

public import LeanQbe.T.TargetLemmas
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.Logic.Bytes
import all Kraken.Separation

/-!
# Target-Generic ABI, Stack Alignment, Region, and Slot-Frame Lemmas

Target-generic helpers (zero `Amd64`/`Arm64`/`Kraken.X64`/`Kraken.AArch64` imports, zero
untyped-IR imports) supporting `FrameTarget` proofs and downstream `Rega`/`Main`:
* 64-bit stack-pointer alignment and `Int64`/`BitVec 64` arithmetic (`aligned16_*`,
  `ofInt_toInt_*`).
* `AbiGprHolds` canonicalization from sub-word `GprHolds` (`abiGprHolds_*_of_gprHolds`).
* `region` / `cell64` / `array64` splitting and combining (`cell64_region`, `region_cell64`,
  `region_frame_split*`, `array64_region`, `region_array64`).
* `Target.Entry` / `Target.Exit` / `Target.FnSpec` stack-footprint and linking lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open Std Std.ExtHashMap

/-! ## 1. 64-bit stack alignment, `Int64`, and `Nat.blt` arithmetic -/

theorem Nat.blt_iff_lt (a b : Nat) : Nat.blt a b = true ↔ a < b := by
  simp [Nat.blt, Nat.ble_eq, Nat.lt_iff_add_one_le]

theorem Int64_toBitVec_ofNat (o : Nat) : (Int64.ofNat o).toBitVec = BitVec.ofNat 64 o := rfl

theorem ofInt_toInt_ofNat (o : Nat) :
    BitVec.ofInt 64 (Int64.ofNat o).toInt = BitVec.ofNat 64 o := by
  rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]
  rfl

theorem ofInt_toInt_ofBitVec (x : BitVec 64) :
    BitVec.ofInt 64 (Int64.ofBitVec x).toInt = x := by
  rw [Int64.toInt, Int64.toBitVec_ofBitVec, BitVec.ofInt_toInt]

theorem ofInt_toInt_add (a b : BitVec 64) :
    BitVec.ofInt 64 (a.toInt + b.toInt) = a + b := by
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

theorem ofInt_toInt_add_toNat (a b : BitVec 64) :
    BitVec.ofInt 64 (a.toInt + (b.toNat : Int)) = a + b := by
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem aligned16_sub {sp : BitVec 64} {n : Nat}
    (hsp : sp.toNat % 16 = 0) (hn : n % 16 = 0) :
    (sp - BitVec.ofNat 64 n).toNat % 16 = 0 := by
  have h16 : (16 : Nat) ∣ 2 ^ 64 := by decide
  have hmod : (BitVec.ofNat 64 n).toNat % 16 = 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd n h16, hn]
  have hsp_lt : sp.toNat < 2 ^ 64 := sp.isLt
  have hn_lt : (BitVec.ofNat 64 n).toNat < 2 ^ 64 := BitVec.isLt _
  rw [BitVec.toNat_sub]
  omega

theorem aligned16_add {sp : BitVec 64} {n : Nat}
    (hsp : sp.toNat % 16 = 0) (hn : n % 16 = 0) :
    (sp + BitVec.ofNat 64 n).toNat % 16 = 0 := by
  have h16 : (16 : Nat) ∣ 2 ^ 64 := by decide
  have hmod : (BitVec.ofNat 64 n).toNat % 16 = 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd n h16, hn]
  rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ h16]
  omega

theorem aligned16_add8_sub {sp : BitVec 64} {n : Nat}
    (hsp : (sp + 8#64).toNat % 16 = 0) (hn : n % 16 = 8) :
    (sp - BitVec.ofNat 64 n).toNat % 16 = 0 := by
  have h16 : (16 : Nat) ∣ 2 ^ 64 := by decide
  have hsp_lt : sp.toNat < 2 ^ 64 := sp.isLt
  have hn_lt : (BitVec.ofNat 64 n).toNat < 2 ^ 64 := BitVec.isLt _
  have hmod : (BitVec.ofNat 64 n).toNat % 16 = 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd n h16, hn]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ h16] at hsp
  rw [BitVec.toNat_sub]
  omega

theorem aligned16_add8_sub_call {sp : BitVec 64} {n : Nat}
    (hsp : (sp + 8#64).toNat % 16 = 0) (hn : n % 16 = 8) :
    (sp - BitVec.ofNat 64 n - BitVec.ofNat 64 8 + 8#64).toNat % 16 = 0 := by
  have e : sp - BitVec.ofNat 64 n - BitVec.ofNat 64 8 + 8#64 = sp - BitVec.ofNat 64 n :=
    BitVec.sub_add_cancel _ 8#64
  rw [e]
  exact aligned16_add8_sub hsp hn

/-! ## 2. `AbiGprHolds` canonicalization from `GprHolds` -/

theorem abiGprHolds_bool_of_gprHolds {w : BitVec 64} {b : Bool} (h : GprHolds w .bool b) :
    AbiGprHolds ((w.setWidth 8).setWidth 64) .bool b := by
  dsimp only [GprHolds] at h
  dsimp only [AbiGprHolds]; rw [h]
  apply BitVec.eq_of_toNat_eq
  have hb : b.toNat < 2 := by cases b <;> decide
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 8),
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]

theorem abiGprHolds_bits_of_gprHolds {n : Nat} {w : BitVec 64} {v : BitVec n}
    (h : GprHolds w (.bits n) v) :
    AbiGprHolds ((w.setWidth n).setWidth 64) (.bits n) v := by
  dsimp only [GprHolds] at h
  exact ⟨h.1, by rw [h.2]⟩

theorem abiGprHolds_bits64_of_gprHolds {w v : BitVec 64} (h : GprHolds w (.bits 64) v) :
    AbiGprHolds w (.bits 64) v := by
  dsimp only [GprHolds] at h
  exact ⟨h.1, by simpa using h.2⟩

/-! ## 3. `region`, `cell64`, and `array64` splitting/combining -/

theorem cell64_region {a v : BitVec 64} {f : Mem 64} (h : cell64 a v f) : region a 8 f :=
  ⟨Int.toBytes 8 v.toInt, Int.toBytes_length _ _, h.symm⟩

theorem toBytes8_ofInt_ofBytes {bs : List UInt8} (hl : bs.length = 8) :
    Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes bs)).toInt = bs := by
  rw [← Int.toBytes_emod]
  have h1 : ((BitVec.ofInt 64 (Int.ofBytes bs)).toInt).take (8 * 8) =
      (Int.ofBytes bs).take (8 * 8) := by
    grind
  rw [h1, Int.toBytes_emod, ← hl]
  exact Int.toBytes_ofBytes_all bs

theorem region_cell64 {a : BitVec 64} {f : Mem 64} :
    region a 8 f ↔ ∃ v, cell64 a v f :=
  ⟨fun ⟨bs, hl, hf⟩ => ⟨BitVec.ofInt 64 (Int.ofBytes bs), by
      show (Int.toBytes 8 _).At a = f
      rw [toBytes8_ofInt_ofBytes hl]; exact hf.symm⟩,
   fun ⟨_, h⟩ => cell64_region h⟩

theorem region_sep_cell64 {a : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (region a 8 ⋆ R) m) : ∃ v, (cell64 a v ⋆ R) m := by
  obtain ⟨f1, f2, hu, hd, hf1, hf2⟩ := h
  obtain ⟨v, hv⟩ := region_cell64.mp hf1
  exact ⟨v, f1, f2, hu, hd, hv, hf2⟩

theorem region_split3 {a : BitVec 64} {n1 n2 n3 : Nat} (h : n1 + n2 + n3 ≤ 2 ^ 64) :
    region a (n1 + n2 + n3) =
      (region a n1 ⋆ region (a + BitVec.ofNat 64 n1) n2 ⋆
        region (a + BitVec.ofNat 64 n1 + BitVec.ofNat 64 n2) n3) := by
  rw [region_split h, region_split (by omega), ptr_add_ofNat]

theorem region_frame_split {a : BitVec 64} {slots frame : Nat}
    (hle : slots ≤ frame) (hF : frame ≤ 2 ^ 64) :
    region a frame = (region a slots ⋆ region (a + BitVec.ofNat 64 slots) (frame - slots)) := by
  have he : frame = slots + (frame - slots) := by omega
  conv => lhs; rw [he]
  exact region_split (by omega)

theorem region_frame_split_ra {a : BitVec 64} {slots frame : Nat}
    (hle : slots + 8 ≤ frame) (hF : frame ≤ 2 ^ 64) :
    region a frame =
      (region a slots ⋆ (region (a + BitVec.ofNat 64 slots) 8 ⋆
        region (a + BitVec.ofNat 64 slots + 8#64) (frame - slots - 8))) := by
  have he : frame = slots + (8 + (frame - slots - 8)) := by omega
  conv => lhs; rw [he]
  rw [region_split (by omega), region_split (by omega)]

theorem array64_region {a : BitVec 64} {xs : List (BitVec 64)} {f : Mem 64}
    (hxs : 8 * xs.length ≤ 2 ^ 64) (h : array64 a xs f) :
    region a (8 * xs.length) f := by
  induction xs generalizing a f with
  | nil => show region a 0 f; rw [region_zero]; exact h
  | cons v vs ih =>
    have hlen : (v :: vs).length = vs.length + 1 := List.length_cons
    have e : 8 * (v :: vs).length = 8 + 8 * vs.length := by omega
    rw [e, region_split (by omega)]
    exact sep_mono (fun _ => cell64_region) (sep_mono_r (fun _ => ih (by omega)) h)

theorem region_array64 {a : BitVec 64} {n : Nat} {f : Mem 64}
    (hn : 8 * n ≤ 2 ^ 64) (h : region a (8 * n) f) :
    ∃ xs : List (BitVec 64), xs.length = n ∧ array64 a xs f := by
  induction n generalizing a f with
  | zero => exact ⟨[], rfl, by rw [region_zero] at h; exact h⟩
  | succ n ih =>
    have e : 8 * (n + 1) = 8 + 8 * n := by omega
    rw [e, region_split (by omega)] at h
    obtain ⟨f1, f2, hu, hd, h1, h2⟩ := h
    obtain ⟨v, hv⟩ := region_cell64.mp h1
    obtain ⟨σ, hl, hσ⟩ := ih (by omega) h2
    exact ⟨v :: σ, by simp [hl], f1, f2, hu, hd, hv, hσ⟩

/-! ## 4. Target stack footprints and function contract helpers -/

namespace Target

variable (T : Target)

theorem entry_exit {sp : BitVec 64} {ra : T.mach.Addr} {n : Nat}
    (hn : n + T.frame.raBytes ≤ 2 ^ 64) {f : Mem 64} :
    T.Entry sp ra n f → T.Exit sp n f := by
  rintro ⟨f1, f2, rfl, hd, ⟨bs1, hl1, rfl⟩, hra⟩
  obtain ⟨bs2, hl2, rfl⟩ := T.frameSpec.retAddr_region _ _ _ hra
  refine ⟨bs1 ++ bs2, by simp [hl1, hl2], ?_⟩
  have hsep := Mem.At_append_sep bs1 bs2 (sp - BitVec.ofNat 64 n) (by omega)
  rw [hl1, BitVec.sub_add_cancel] at hsep
  exact ((congrFun hsep _).mpr ⟨_, _, rfl, hd, rfl, rfl⟩).symm

theorem retAddr_of_entry' {m : Mem 64} {sp : BitVec 64} {ra : T.mach.Addr} {n : Nat}
    {R : Mem 64 → Prop} {M : Mem 64} (h : (Eq m ⋆ T.Entry sp ra n ⋆ R) M) :
    (T.frameSpec.RetAddr sp ra ⋆ (Eq m ⋆ region (sp - BitVec.ofNat 64 n) n ⋆ R)) M := by
  have e : (Eq m ⋆ T.Entry sp ra n ⋆ R) =
      (T.frameSpec.RetAddr sp ra ⋆ (Eq m ⋆ region (sp - BitVec.ofNat 64 n) n ⋆ R)) := by
    dsimp only [Entry]; ac_rfl
  exact e ▸ h

theorem retAddr_of_entry {m : Mem 64} {sp : BitVec 64} {ra : T.mach.Addr} {n : Nat}
    {R : Mem 64 → Prop} {M : Mem 64} (h : (Eq m ⋆ T.Entry sp ra n ⋆ R) M) :
    ∃ R', (T.frameSpec.RetAddr sp ra ⋆ R') M :=
  ⟨_, T.retAddr_of_entry' h⟩

theorem exit_of_entry {m : Mem 64} {sp : BitVec 64} {ra : T.mach.Addr} {n : Nat}
    {R : Mem 64 → Prop} {M : Mem 64} (hn : n + T.frame.raBytes ≤ 2 ^ 64) :
    (Eq m ⋆ T.Entry sp ra n ⋆ R) M → (Eq m ⋆ T.Exit sp n ⋆ R) M :=
  sep_mono fun _ => sep_mono_r fun _ => T.entry_exit hn

theorem exit_of_entry_assoc {m : Mem 64} {sp : BitVec 64} {ra : T.mach.Addr} {n : Nat}
    {R : Mem 64 → Prop} {M : Mem 64} (hn : n + T.frame.raBytes ≤ 2 ^ 64) :
    (Eq m ⋆ (T.Entry sp ra n ⋆ R)) M → (Eq m ⋆ T.Exit sp n ⋆ R) M := by
  rw [← sep_assoc]
  exact T.exit_of_entry hn

theorem FnSpec.of_spec {h : T.mach.Host} {sym : Sym} {as bs : List Ty}
    {spec spec' : Spec as bs} {n nX : Nat}
    (hf : T.FnSpec h sym spec n nX) (hs : ∀ args m Q X, spec' args m Q X → spec args m Q X) :
    T.FnSpec h sym spec' n nX :=
  fun args m Q X hspec => hf args m Q X (hs args m Q X hspec)

theorem FnSpec.mono_exit {h : T.mach.Host} {sym : Sym} {as bs : List Ty}
    {spec : Spec as bs} {n nX nX' : Nat}
    (hf : T.FnSpec h sym spec n nX) (hX : nX' ≤ nX) : T.FnSpec h sym spec n nX' := by
  intro args m Q X hspec s ra R ha hr hsp hmem
  refine eventually_weaken _ _ _ _ ?_ (hf args m Q X hspec s ra R ha hr hsp hmem)
  grind

theorem FnSpec.mono_stack {h : T.mach.Host} {sym : Sym} {as bs : List Ty}
    {spec : Spec as bs} {n n' nX : Nat}
    (hf : T.FnSpec h sym spec n nX) (hn : n ≤ n') (hn' : n' + T.frame.raBytes ≤ 2 ^ 64) :
    T.FnSpec h sym spec n' nX := by
  intro args m Q X hspec s ra R ha hr hsp hmem
  have eaddr : T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n' + BitVec.ofNat 64 (n' - n) =
      T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n := by
    grind
  have hsplit : region (T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n') n' =
      (region (T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n') (n' - n) ⋆
        region (T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n) n) := by
    have := region_split (a := T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n')
      (n1 := n' - n) (n2 := n) (by omega)
    grind
  have hmem' : (T.mach.mem s =⋆ Eq m ⋆ T.Entry (T.mach.getGpr s T.frame.sp) ra n ⋆
      (region (T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n') (n' - n) ⋆ R)) := by
    have : (Eq m ⋆ T.Entry (T.mach.getGpr s T.frame.sp) ra n' ⋆ R) =
        (Eq m ⋆ T.Entry (T.mach.getGpr s T.frame.sp) ra n ⋆
          (region (T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n') (n' - n) ⋆ R)) := by
      dsimp only [Target.Entry]; rw [hsplit]; ac_rfl
    exact this ▸ hmem
  refine eventually_weaken _ _ _ _ ?_ (hf args m Q X hspec s ra _ ha hr hsp hmem')
  rintro st (⟨hpc, rets, m', hQ, hrets, hres, hm⟩ |
    ⟨sym', cs, xs, m', hX', hd, hpc, has, hsp', ra', n'', F, hn'', hb'', hra', hm⟩)
  · refine Or.inl ⟨hpc, rets, m', hQ, hrets, hres, ?_⟩
    have hsplit' : T.Exit (T.mach.getGpr s T.frame.sp) n' =
        (region (T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n') (n' - n) ⋆
          T.Exit (T.mach.getGpr s T.frame.sp) n) := by
      dsimp only [Target.Exit]
      have := region_split (a := T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n')
        (n1 := n' - n) (n2 := n + T.frame.raBytes) (by omega)
      grind
    have : (Eq m' ⋆ T.Exit (T.mach.getGpr s T.frame.sp) n' ⋆ R) =
        (Eq m' ⋆ T.Exit (T.mach.getGpr s T.frame.sp) n ⋆
          (region (T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n') (n' - n) ⋆ R)) := by
      rw [hsplit']; ac_rfl
    exact this ▸ hm
  · refine Or.inr ⟨sym', cs, xs, m', hX', hd, hpc, has, hsp', ra', n'',
      F ⋆ region (T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n') (n' - n),
      hn'', hb'', hra', ?_⟩
    have : (Eq m' ⋆ T.Entry (T.mach.getGpr (T.mach.data st) T.frame.sp) ra' n'' ⋆ F ⋆
          (region (T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n') (n' - n) ⋆ R)) =
        (Eq m' ⋆ T.Entry (T.mach.getGpr (T.mach.data st) T.frame.sp) ra' n'' ⋆
          (F ⋆ region (T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 n') (n' - n)) ⋆ R) := by
      ac_rfl
    exact this ▸ hm

theorem link {h : T.mach.Host} (Γ : Env) (sig : Sym → List Ty × List Ty)
    (bound : Sym → Nat) (nX : Nat) :
    ∀ fs : List Sym,
      (∀ (pre : List Sym) (f : Sym) (post : List Sym), fs = pre ++ f :: post →
        (∀ g, g ∈ pre → T.FnSpec h g (Γ g (sig g).1 (sig g).2) (bound g) nX) →
        T.FnSpec h f (Γ f (sig f).1 (sig f).2) (bound f) nX) →
      ∀ f, f ∈ fs → T.FnSpec h f (Γ f (sig f).1 (sig f).2) (bound f) nX := by
  intro fs hstep
  have key : ∀ k, k ≤ fs.length → ∀ g, g ∈ fs.take k →
      T.FnSpec h g (Γ g (sig g).1 (sig g).2) (bound g) nX := by
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

end LeanQbe.T
