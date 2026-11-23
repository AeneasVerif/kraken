module

public import LeanQbe.T.Target

/-!
# Shared Combinators and Framing Lemmas for `LeanQbe.T.Target`

Target-generic framing, sequencing, and operand-preservation lemmas shared across
`RegaLemmas`, scalar/vector instruction selection (`Gpr*`, `Vec*`), and `Frame*` proofs.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

@[simp] theorem unpackSlotWords_length (w : SlotWidth) (v : BitVec 512) :
    (unpackSlotWords w v).length = w.slots := by cases w <;> rfl

@[simp] theorem SlotWidth.bits_eq_64_mul_slots (w : SlotWidth) :
    w.bits = 64 * w.slots := by cases w <;> rfl
theorem SlotWidth.slots_le_eight (w : SlotWidth) : w.slots ≤ 8 := by cases w <;> decide
theorem SlotWidth.bits_le_512 (w : SlotWidth) : w.bits ≤ 512 := by cases w <;> decide

@[simp] theorem FlagMask.disjoint_none (reads : FlagMask) :
    FlagMask.disjoint reads FlagMask.none = true := by
  dsimp only [FlagMask.disjoint, FlagMask.none]; simp

private theorem FlagMask.disjoint_iff_bits {reads m : FlagMask} :
    FlagMask.disjoint reads m = true ↔ ∀ i (_ : i < 8), reads[i] = true → m[i] = false := by
  simp only [FlagMask.disjoint, beq_iff_eq]
  constructor
  · intro h i hi hr
    have hi0 : (reads &&& m)[i] = false := by rw [h]; simp
    simp only [BitVec.getElem_and, hr, Bool.true_and] at hi0
    exact hi0
  · intro h
    apply BitVec.eq_of_getElem_eq; intro i hi
    cases hr : reads[i] <;> simp [hr, h i hi]

theorem FlagMask.disjoint_or_iff (reads m₁ m₂ : FlagMask) :
    FlagMask.disjoint reads (m₁ ||| m₂) = true ↔
      FlagMask.disjoint reads m₁ = true ∧ FlagMask.disjoint reads m₂ = true := by
  simp only [FlagMask.disjoint_iff_bits, BitVec.getElem_or, Bool.or_eq_false_iff]
  exact ⟨fun h => ⟨fun i hi hr => (h i hi hr).1, fun i hi hr => (h i hi hr).2⟩,
    fun ⟨h₁, h₂⟩ i hi hr => ⟨h₁ i hi hr, h₂ i hi hr⟩⟩

theorem FlagMask.disjoint_of_sub {reads m₁ m₂ : FlagMask}
    (hsub : m₁ &&& ~~~m₂ = 0#8) (h : FlagMask.disjoint reads m₂ = true) :
    FlagMask.disjoint reads m₁ = true := by
  rw [FlagMask.disjoint_iff_bits] at h ⊢
  intro i hi hr
  have h1 : (m₁ &&& ~~~m₂)[i] = false := by rw [hsub]; simp
  simp only [BitVec.getElem_and, BitVec.getElem_not] at h1
  have h2 := h i hi hr
  cases hm1 : m₁[i] <;> simp_all

namespace Machine
variable {R V C D : Type} {M : Machine R V C D}

@[simp] theorem KeepsGpr.refl (s : M.MData) (clob : List R) : M.KeepsGpr s s clob := fun _ _ => rfl
theorem KeepsGpr.trans {s₁ s₂ s₃ : M.MData} {g₁ g₂ : List R}
    (h₁ : M.KeepsGpr s₁ s₂ g₁) (h₂ : M.KeepsGpr s₂ s₃ g₂) : M.KeepsGpr s₁ s₃ (g₁ ++ g₂) := by
  intro r hr; rw [List.mem_append, not_or] at hr; exact (h₂ r hr.2).trans (h₁ r hr.1)
theorem KeepsGpr.mono {s s' : M.MData} {g₁ g₂ : List R}
    (h : M.KeepsGpr s s' g₁) (hsub : ∀ r ∈ g₁, r ∈ g₂) : M.KeepsGpr s s' g₂ :=
  fun r hr => h r fun h1 => hr (hsub r h1)

@[simp] theorem KeepsVec.refl (s : M.MData) (clob : List V) : M.KeepsVec s s clob := fun _ _ => rfl
theorem KeepsVec.trans {s₁ s₂ s₃ : M.MData} {v₁ v₂ : List V}
    (h₁ : M.KeepsVec s₁ s₂ v₁) (h₂ : M.KeepsVec s₂ s₃ v₂) : M.KeepsVec s₁ s₃ (v₁ ++ v₂) := by
  intro v hv; rw [List.mem_append, not_or] at hv; exact (h₂ v hv.2).trans (h₁ v hv.1)
theorem KeepsVec.mono {s s' : M.MData} {v₁ v₂ : List V}
    (h : M.KeepsVec s s' v₁) (hsub : ∀ v ∈ v₁, v ∈ v₂) : M.KeepsVec s s' v₂ :=
  fun v hv => h v fun h1 => hv (hsub v h1)

@[simp] theorem UpdFlags.refl (cr : C → FlagMask) (s : M.MData) (mask : FlagMask) :
    M.UpdFlags cr s s mask := fun _ _ => rfl
theorem UpdFlags.trans {cr : C → FlagMask} {s₁ s₂ s₃ : M.MData} {m₁ m₂ : FlagMask}
    (h₁ : M.UpdFlags cr s₁ s₂ m₁) (h₂ : M.UpdFlags cr s₂ s₃ m₂) :
    M.UpdFlags cr s₁ s₃ (m₁ ||| m₂) := by
  intro c hc; obtain ⟨h1, h2⟩ := (FlagMask.disjoint_or_iff (cr c) m₁ m₂).mp hc
  exact (h₂ c h2).trans (h₁ c h1)
theorem UpdFlags.mono {cr : C → FlagMask} {s s' : M.MData} {m₁ m₂ : FlagMask}
    (h : M.UpdFlags cr s s' m₁) (hsub : m₁ &&& ~~~m₂ = 0#8) : M.UpdFlags cr s s' m₂ :=
  fun c hc => h c (FlagMask.disjoint_of_sub hsub hc)

@[simp] theorem Frame.refl (cr : C → FlagMask) (s : M.MData)
    (g : List R) (v : List V) (f : FlagMask) :
    M.Frame cr s s g v f := ⟨KeepsGpr.refl s g, KeepsVec.refl s v, UpdFlags.refl cr s f⟩
theorem Frame.trans {cr : C → FlagMask} {s₁ s₂ s₃ : M.MData}
    {g₁ g₂ : List R} {v₁ v₂ : List V} {f₁ f₂ : FlagMask}
    (h₁ : M.Frame cr s₁ s₂ g₁ v₁ f₁) (h₂ : M.Frame cr s₂ s₃ g₂ v₂ f₂) :
    M.Frame cr s₁ s₃ (g₁ ++ g₂) (v₁ ++ v₂) (f₁ ||| f₂) :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩
theorem Frame.weaken {cr : C → FlagMask} {s s' : M.MData}
    {g₁ g₂ : List R} {v₁ v₂ : List V} {f₁ f₂ : FlagMask}
    (h : M.Frame cr s s' g₁ v₁ f₁) (hg : ∀ r ∈ g₁, r ∈ g₂) (hv : ∀ v ∈ v₁, v ∈ v₂)
    (hf : f₁ &&& ~~~f₂ = 0#8) : M.Frame cr s s' g₂ v₂ f₂ :=
  ⟨h.1.mono hg, h.2.1.mono hv, h.2.2.mono hf⟩

theorem FallsTo.nil {cr : C → FlagMask} {h : M.Host} {k : Nat}
    {g : List R} {v : List V} {f : FlagMask} {s : M.MData} {Q : M.MData → Prop}
    {post : M.State → Prop} (hq : Q s) : M.FallsTo cr h k [] g v f s Q post :=
  fun _ hk => by simpa using hk s hq (Frame.refl cr s g v f)

theorem FallsTo.conseq {cr : C → FlagMask} {h : M.Host} {k : Nat} {c : List D}
    {g : List R} {v : List V} {f : FlagMask} {s : M.MData} {Q₁ Q₂ : M.MData → Prop}
    {post : M.State → Prop} (hft : M.FallsTo cr h k c g v f s Q₁ post)
    (hq : ∀ s', Q₁ s' → M.Frame cr s s' g v f → Q₂ s') : M.FallsTo cr h k c g v f s Q₂ post :=
  fun hc hk => hft hc fun s' h1 hf => hk s' (hq s' h1 hf) hf

theorem FallsTo.weaken {cr : C → FlagMask} {h : M.Host} {k : Nat} {c : List D}
    {g₁ g₂ : List R} {v₁ v₂ : List V} {f₁ f₂ : FlagMask} {s : M.MData} {Q : M.MData → Prop}
    {post : M.State → Prop} (hft : M.FallsTo cr h k c g₁ v₁ f₁ s Q post)
    (hg : ∀ r ∈ g₁, r ∈ g₂) (hv : ∀ v ∈ v₁, v ∈ v₂) (hf : f₁ &&& ~~~f₂ = 0#8) :
    M.FallsTo cr h k c g₂ v₂ f₂ s Q post :=
  fun hc hk => hft hc fun s' hq hfr => hk s' hq (hfr.weaken hg hv hf)

theorem FallsTo.comp {cr : C → FlagMask} {h : M.Host} {k : Nat} {c₁ c₂ : List D}
    {g₁ g₂ : List R} {v₁ v₂ : List V} {f₁ f₂ : FlagMask} {s : M.MData}
    {Q₁ Q₂ : M.MData → Prop} {post : M.State → Prop}
    (h₁ : M.FallsTo cr h k c₁ g₁ v₁ f₁ s Q₁ post)
    (h₂ : ∀ s', Q₁ s' → M.Frame cr s s' g₁ v₁ f₁ →
      M.FallsTo cr h (k + c₁.length) c₂ g₂ v₂ f₂ s' Q₂ post) :
    M.FallsTo cr h k (c₁ ++ c₂) (g₁ ++ g₂) (v₁ ++ v₂) (f₁ ||| f₂) s Q₂ post :=
  fun hc hk => h₁ hc.append.1 fun s₁ hq₁ hfr₁ => h₂ s₁ hq₁ hfr₁ hc.append.2 fun s₂ hq₂ hfr₂ => by
    simpa [List.length_append, Nat.add_assoc] using hk s₂ hq₂ (hfr₁.trans hfr₂)

theorem PArgHolds.frame {cr : C → FlagMask} {s s' : M.MData}
    {gClob : List R} {vClob : List V} {fClob : FlagMask}
    (hfr : M.Frame cr s s' gClob vClob fClob) {t : Ty} {pa : PArg R V C t} {v : Val t}
    (hh : M.PArgHolds s t pa v) (hg : ∀ r, pa = .gpr r → r ∉ gClob)
    (hv : ∀ vr, pa = .vec vr → vr ∉ vClob)
    (hf : ∀ c (ht : t = .bool), pa = ht ▸ .flag c → FlagMask.disjoint (cr c) fClob = true) :
    M.PArgHolds s' t pa v := by
  cases pa with
  | gpr r => dsimp only [PArgHolds] at hh ⊢; rwa [hfr.1 r (hg r rfl)]
  | vec vr => dsimp only [PArgHolds] at hh ⊢; rwa [hfr.2.1 vr (hv vr rfl)]
  | flag c => dsimp only [PArgHolds] at hh ⊢; rwa [hfr.2.2 c (hf c rfl rfl)]
  | imm _ => exact hh

theorem PDstHolds.frame {cr : C → FlagMask} {s s' : M.MData}
    {gClob : List R} {vClob : List V} {fClob : FlagMask}
    (hfr : M.Frame cr s s' gClob vClob fClob) {t : Ty} {pd : PDst R V C t} {v : Val t}
    (hh : M.PDstHolds s t pd v) (hg : ∀ r, pd = .gpr r → r ∉ gClob)
    (hv : ∀ vr, pd = .vec vr → vr ∉ vClob)
    (hf : ∀ c (ht : t = .bool), pd = ht ▸ .flag c → FlagMask.disjoint (cr c) fClob = true) :
    M.PDstHolds s' t pd v := by
  cases pd with
  | gpr r => dsimp only [PDstHolds] at hh ⊢; rwa [hfr.1 r (hg r rfl)]
  | vec vr => dsimp only [PDstHolds] at hh ⊢; rwa [hfr.2.1 vr (hv vr rfl)]
  | flag c => dsimp only [PDstHolds] at hh ⊢; rwa [hfr.2.2 c (hf c rfl rfl)]

theorem AbiHolds.frame {s s' : M.MData} {gClob : List R} {vClob : List V}
    (hkg : M.KeepsGpr s s' gClob) (hkv : M.KeepsVec s s' vClob)
    {t : Ty} {a : AbiReg R V t} {v : Val t} (hh : M.AbiHolds s t a v)
    (hg : ∀ r, a = .gpr r → r ∉ gClob) (hv : ∀ vr, a = .vec vr → vr ∉ vClob) :
    M.AbiHolds s' t a v := by
  cases a with
  | gpr r => dsimp only [AbiHolds] at hh ⊢; rwa [hkg r (hg r rfl)]
  | vec vr => dsimp only [AbiHolds] at hh ⊢; rwa [hkv vr (hv vr rfl)]

end Machine

theorem VecHolds.of_setWidth_eq {v v' : BitVec 512} {w : SlotWidth} {t : Ty} {val : Val t}
    (hle : t.size ≤ w.bits) (heq : v'.setWidth w.bits = v.setWidth w.bits)
    (h : VecHolds v t val) : VecHolds v' t val := by
  refine ⟨h.1, ?_⟩
  rw [← BitVec.setWidth_setWidth_of_le v' hle, heq, BitVec.setWidth_setWidth_of_le v hle, h.2]

/-- Pack a list of 64-bit stack-slot granules into a 512-bit vector word starting at bit `shift`. -/
private def packSlotWordsAux : List (BitVec 64) → Nat → BitVec 512
  | [], _ => 0#512
  | w :: ws, shift => (w.setWidth 512 <<< shift) ||| packSlotWordsAux ws (shift + 64)

/-- Pack `w.slots` 64-bit slot granules into a 512-bit vector word
(inverse to `unpackSlotWords`). -/
def packSlotWords (w : SlotWidth) (ws : List (BitVec 64)) : BitVec 512 :=
  packSlotWordsAux (ws.take w.slots) 0

private theorem getLsbD_packSlotWordsAux (ws : List (BitVec 64)) (k idx : Nat) (hidx : idx < 512) :
    (packSlotWordsAux ws (64 * k)).getLsbD idx =
      if k ≤ idx / 64 then
        match ws[idx / 64 - k]? with
        | some w => w.getLsbD (idx % 64)
        | none => false
      else false := by
  induction ws generalizing k with
  | nil => simp [packSlotWordsAux]
  | cons w ws ih =>
    have hih := ih (k + 1)
    rw [Nat.mul_add, Nat.mul_one] at hih
    simp only [packSlotWordsAux, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, hih]
    by_cases hlt : idx < 64 * k
    · have hkgt : ¬(k ≤ idx / 64) := by omega
      have hk1gt : ¬(k + 1 ≤ idx / 64) := by omega
      simp [hlt, hkgt, hk1gt]
    · have hk1 : ¬(idx < 64 * k) := hlt
      by_cases heq : idx / 64 = k
      · have hmod : idx - 64 * k = idx % 64 := by omega
        have hmodlt : idx % 64 < 512 := by omega
        simp [hk1, heq, hmod, hidx, hmodlt, Nat.not_succ_le_self]
      · have hk1ge : k + 1 ≤ idx / 64 := by omega
        have hge : k ≤ idx / 64 := by omega
        have hwfalse : w.getLsbD (idx - 64 * k) = false :=
          BitVec.getLsbD_of_ge w (idx - 64 * k) (by omega)
        have hget : (w :: ws)[idx / 64 - k]? = ws[idx / 64 - (k + 1)]? := by
          have : idx / 64 - k = (idx / 64 - (k + 1)) + 1 := by omega
          rw [this]; rfl
        simp [hk1, hwfalse, hk1ge, hget, hge]

private theorem extractLsb'_packSlotWordsAux (ws : List (BitVec 64)) (j : Nat)
    (hj512 : 64 * j + 64 ≤ 512) (hjlen : j < ws.length) :
    (packSlotWordsAux ws 0).extractLsb' (64 * j) 64 = ws[j] := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  have h := getLsbD_packSlotWordsAux ws 0 (64 * j + i) (by omega)
  simp only [Nat.mul_zero] at h
  rw [h]
  have hdiv : (64 * j + i) / 64 = j := by omega
  have hmod : (64 * j + i) % 64 = i := by omega
  simp [hdiv, hmod, List.getElem?_eq_getElem hjlen]

private theorem unpackSlotWords_getElem (w : SlotWidth) (v : BitVec 512) (j : Nat)
    (hj : j < w.slots) :
    (unpackSlotWords w v)[j]'(by rw [unpackSlotWords_length]; exact hj) =
      v.extractLsb' (64 * j) 64 := by
  cases w <;> simp only [SlotWidth.slots] at hj
  · rcases j with _ | j <;> first | rfl | omega
  · rcases j with _ | _ | j <;> first | rfl | omega
  · rcases j with _ | _ | _ | _ | j <;> first | rfl | omega
  · rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega

theorem unpackSlotWords_packSlotWords (w : SlotWidth) (ws : List (BitVec 64))
    (hlen : ws.length = w.slots) : unpackSlotWords w (packSlotWords w ws) = ws := by
  refine List.ext_getElem (by rw [unpackSlotWords_length, hlen]) fun j _ hj2 => ?_
  have hj : j < w.slots := hlen ▸ hj2
  have hwle : 64 * j + 64 ≤ 512 := by have := w.slots_le_eight; omega
  have htake : ws.take w.slots = ws := List.take_of_length_le (Nat.le_of_eq hlen)
  rw [unpackSlotWords_getElem w (packSlotWords w ws) j hj, packSlotWords, htake]
  exact extractLsb'_packSlotWordsAux ws j hwle hj2

end LeanQbe.T
