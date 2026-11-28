module

public import LeanQbe.T.Unified.CfgContify
public import LeanQbe.T.Unified.CfgRecoveryLemmas
public import LeanQbe.T.BedrockWord.Exec
import LeanQbe.T.FlatLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.MainLemmas
import LeanQbe.T.GroupLfpLemmas
import LeanQbe.T.ZeroPeelLemmas1
import LeanQbe.T.Bedrock2.Phoas
import Kraken.Mem
import Kraken.ToBytes

/-!
# Soundness Lemmas for Stage-1 CFG Recovery, Contification & Private Frame Promotion
(`Unified.CfgContifyLemmas`)

Proof companion to `LeanQbe.T.Unified.CfgContify` behind the module-system proof firewall
(`*Lemmas*` imports stay private, `0` `@[expose]` on theorems):

* §1. `Mem 64` private-frame theory (`writeSlots`, `PrivFrameOk`, `FrameRel`,
  `storeMem_of_loadVal_i64`, `loadVal_writeSlots_slot`, `storeMem_writeSlots_slot`,
  `disjoint_frame_of_static`, `disjoint_frame_of_range`).
* §2. `EnvMapOk`, `SlotsLvlsOk`, `ContSymStateOk`, `evalContOp_sound`, and prefix lemmas
  for `liftContifyBlock` / `liftContifyGroupNode` / `liftContifyGroupNodes`.
* §3. `loadEntryFrameAux_wp`, `flushFrame_wp`, `emitAliasGuard_wp`, `lowerUnpromotedTail_wp`,
  `liftContEdgeMapped_wp`, `liftContifyBlock_wp`, `liftContifyRegion_wf` / `_mid_wf`.
* §4. `TFlat.isMemFree` relocation (`wp_memFree_relocate`), `ContifyRegionStep`, `PsiContReg`,
  `PsiContHyb`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T
open LeanQbe.T.BedrockWord

/-! ## §1. `Mem 64` Private-Frame Theory (`writeSlots`, `FrameRel`, Alias Disjointness) -/

/-- Write concrete 64-bit slot values `vs` at `slotAddr sp₀ (base + i)` in `Mem 64`. -/
@[expose] def writeSlots (m : Mem 64) (sp₀ : BitVec 64) :
    Nat → List (BitVec 64) → Mem 64
  | _, [] => m
  | k, v :: vs => writeSlots (storeMem m i64 (slotAddr sp₀ k) v) sp₀ (k + 1) vs

/-- Entry precondition ensuring private stack slots `[sp₀ - 8*nSlots, sp₀)` are mapped. -/
@[expose] def PrivFrameOk (nSlots : Nat) (sp₀ : BitVec 64) (m : Mem 64) : Prop :=
  nSlots > 0 → nSlots ≤ 64 ∧ ∀ k < nSlots, storeOk m i64 (slotAddr sp₀ k)

/-- Relation connecting concrete memory `mConc` and promoted-register public memory `mPub`. -/
@[expose] def FrameRel (nSlots : Nat) (sp₀ : BitVec 64) (slots : List (BitVec 64))
    (mConc mPub : Mem 64) : Prop :=
  if nSlots = 0 then
    mConc = mPub
  else
    slots.length = nSlots ∧ nSlots ≤ 64 ∧
    (∀ k < nSlots, storeOk mPub i64 (slotAddr sp₀ k)) ∧
    mConc = writeSlots mPub sp₀ 0 slots

/-- Pack promoted-slot values into `Tup Val (List.replicate n i64)`. -/
@[expose] def packSlotTup : (n : Nat) → List (BitVec 64) → Tup Val (List.replicate n i64)
  | 0, _ => ()
  | n + 1, [] => (0#64, packSlotTup n [])
  | n + 1, v :: vs => (v, packSlotTup n vs)

/-- Pack full boundary tuple `(r, sp₀, slots)` into `Tup Val (contSig nSlots)`. -/
@[expose] def packContTup (nSlots : Nat) (r : Regs) (sp₀ : BitVec 64)
    (slots : List (BitVec 64)) : Tup Val (contSig nSlots) :=
  match nSlots with
  | 0 => r.toRegsV.toTup
  | k + 1 => tupAppend r.toRegsV.toTup (sp₀, packSlotTup (k + 1) slots)

theorem loadVal_i64_of_storeOk {m : Mem 64} {a : BitVec 64} (h : storeOk m i64 a) :
    ∃ v : Val i64, loadVal m i64 a = some v := by
  rcases h with ⟨i, hi⟩
  refine ⟨BitVec.ofInt 64 i, ?_⟩
  dsimp only [loadVal]
  rw [hi]; rfl

theorem storeOk_i64_of_loadVal {m : Mem 64} {a : BitVec 64} {v : Val i64}
    (h : loadVal m i64 a = some v) : storeOk m i64 a := by
  dsimp only [loadVal] at h
  cases hi : m.loadInt a i64.bytes with
  | none => rw [hi] at h; cases h
  | some i => exact ⟨i, hi⟩

theorem storeMem_of_loadVal_i64 (m : Mem 64) (a : BitVec 64) (v : Val i64)
    (h : loadVal m i64 a = some v) : storeMem m i64 a v = m := by
  have hall := (ZeroPeel.storeOk_iff_forall_mem m i64 a).1 (storeOk_i64_of_loadVal h)
  obtain ⟨bs, mRest, hlen, hbytes, hsp⟩ := Bedrock2.mem_split_At m a 8 (by decide) fun i hi => by
    simpa [Std.ExtHashMap.get?_eq_getElem?] using hall i hi
  have hli := Mem.loadInt_sep bs a 8 (Eq mRest) m
    (Bedrock2.split_iff_sep.1 hsp) hlen (by decide)
  dsimp only [loadVal] at h; rw [show i64.bytes = 8 from rfl, hli] at h
  dsimp only [Option.bind_some, Option.some.injEq] at h
  have hto : Int.toBytes 8 ((toBits i64 v).setWidth (8 * 8)).toInt = bs := by
    have hvEq : BitVec.ofInt 64 (Int.ofBytes bs) = v := by simpa [ofBits] using h
    rw [show 8 * 8 = 64 by rfl, show (toBits i64 v).setWidth 64 = v by simp [toBits], ← hvEq]
    have hu := UInt64.toBytes_ofBytes bs (by omega)
    dsimp only [UInt64.toBytes, UInt64.ofBytes, UInt64.toBitVec] at hu
    rwa [List.take_of_length_le (by omega)] at hu
  rw [Bedrock2.storeMem_eq_union m i64 a v (by decide)]
  apply Std.ExtHashMap.ext_getElem?; intro p
  rw [show i64.bytes = 8 by rfl, hto, Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  by_cases hmem : p ∈ bs.At a
  · rcases (mem_At_iff bs a p).1 hmem with ⟨i, hi, rfl⟩
    rw [← Std.ExtHashMap.get?_eq_getElem?, get?_At_idx bs a i (by omega) (by omega),
      hbytes i (by omega), List.getElem?_eq_getElem hi]; rfl
  · rw [Std.ExtHashMap.getElem?_eq_none hmem]; cases m[p]? <;> rfl

private theorem slotAddr_plus_toNat (sp₀ : BitVec 64) (base k r : Nat)
    (hk : k < base) (hbase : base ≤ 64) (hr : r < 8) :
    ((slotAddr sp₀ k + BitVec.ofNat 64 r) + (BitVec.ofNat 64 (8 * base) - sp₀)).toNat =
      8 * (base - k - 1) + r := by
  dsimp only [slotAddr]
  have heq : (sp₀ - BitVec.ofNat 64 (8 * (k + 1)) + BitVec.ofNat 64 r) +
      (BitVec.ofNat 64 (8 * base) - sp₀) =
      BitVec.ofNat 64 (8 * (base - k - 1) + r) := by
    apply BitVec.eq_of_toNat_eq
    have hb64 : 8 * base < 2 ^ 64 := by omega
    have hk64 : 8 * (k + 1) ≤ 8 * base := by omega
    have hr64 : r < 2 ^ 64 := by omega
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hb64, Nat.mod_eq_of_lt (by omega : 8 * (k + 1) < 2 ^ 64),
        Nat.mod_eq_of_lt hr64, Nat.mod_eq_of_lt (by omega : 8 * (base - k - 1) + r < 2 ^ 64)]
    have hsp : sp₀.toNat < 2 ^ 64 := sp₀.isLt
    omega
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem slotAddr_disjoint (sp₀ : BitVec 64) {k₁ k₂ : Nat}
    (hk1 : k₁ < 64) (hk2 : k₂ < 64) (hne : k₁ ≠ k₂) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    slotAddr sp₀ k₁ + BitVec.ofNat 64 i ≠ slotAddr sp₀ k₂ + BitVec.ofNat 64 j := by
  intro heq
  have hsh := congrArg (fun x => (x + (BitVec.ofNat 64 (8 * 64) - sp₀)).toNat) heq
  rw [slotAddr_plus_toNat sp₀ 64 k₁ i hk1 (Nat.le_refl _) hi,
      slotAddr_plus_toNat sp₀ 64 k₂ j hk2 (Nat.le_refl _) hj] at hsh
  omega

theorem disjoint_frame_of_static (sp₀ o : BitVec 64) {nSlots bytes k i j : Nat}
    (hn : nSlots ≤ 64) (hb : bytes ≤ 4096) (ho : o.toNat ≤ 4096)
    (hk : k < nSlots) (hi : i < bytes) (hj : j < 8) :
    (sp₀ + o) + BitVec.ofNat 64 i ≠ slotAddr sp₀ k + BitVec.ofNat 64 j := by
  intro heq
  have hsh := congrArg (fun x => (x + (BitVec.ofNat 64 (8 * 64) - sp₀)).toNat) heq
  rw [slotAddr_plus_toNat sp₀ 64 k j (by omega) (Nat.le_refl _) hj] at hsh
  have hlhs : (((sp₀ + o) + BitVec.ofNat 64 i) + (BitVec.ofNat 64 (8 * 64) - sp₀)).toNat =
      8 * 64 + o.toNat + i := by
    have hbv : ((sp₀ + o) + BitVec.ofNat 64 i) + (BitVec.ofNat 64 (8 * 64) - sp₀) =
        BitVec.ofNat 64 (8 * 64 + o.toNat + i) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      have hsp : sp₀.toNat < 2 ^ 64 := sp₀.isLt
      have ho' : o.toNat < 2 ^ 64 := o.isLt
      rw [Nat.mod_eq_of_lt (by omega : 8 * 64 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 8 * 64 + o.toNat + i < 2 ^ 64)]
      omega
    rw [hbv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hlhs] at hsh
  omega

theorem disjoint_frame_of_range (sp₀ a : BitVec 64) {nSlots bytes k i j : Nat}
    (hn : nSlots ≤ 64) (hb : bytes ≤ 16)
    (hlo : 8 * nSlots ≤ (a - (sp₀ - BitVec.ofNat 64 (8 * nSlots))).toNat)
    (hhi : (a - (sp₀ - BitVec.ofNat 64 (8 * nSlots))).toNat ≤ 2 ^ 64 - bytes)
    (hk : k < nSlots) (hi : i < bytes) (hj : j < 8) :
    a + BitVec.ofNat 64 i ≠ slotAddr sp₀ k + BitVec.ofNat 64 j := by
  intro heq
  have hsh := congrArg (fun x => (x + (BitVec.ofNat 64 (8 * nSlots) - sp₀)).toNat) heq
  rw [slotAddr_plus_toNat sp₀ nSlots k j hk hn hj] at hsh
  have hlhs : (a + BitVec.ofNat 64 i + (BitVec.ofNat 64 (8 * nSlots) - sp₀)).toNat =
      (a - (sp₀ - BitVec.ofNat 64 (8 * nSlots))).toNat + i := by
    have hbv : a + BitVec.ofNat 64 i + (BitVec.ofNat 64 (8 * nSlots) - sp₀) =
        (a - (sp₀ - BitVec.ofNat 64 (8 * nSlots))) + BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      have ha : a.toNat < 2 ^ 64 := a.isLt
      have hsp : sp₀.toNat < 2 ^ 64 := sp₀.isLt
      rw [Nat.mod_eq_of_lt (by omega : 8 * nSlots < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
      omega
    rw [hbv, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
  rw [hlhs] at hsh
  omega

private theorem bytes_le_of_disj {n : Nat} {a b : BitVec 64}
    (h : ∀ i, i < n → b ≠ a + BitVec.ofNat 64 i) : n ≤ 2 ^ 64 :=
  Nat.le_of_not_lt fun hgt =>
    h (b - a).toNat (Nat.lt_trans (BitVec.isLt _) hgt) (by
      have hs : BitVec.ofNat 64 (b - a).toNat = b - a :=
        BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt (BitVec.isLt _))
      rw [hs, BitVec.add_comm a, BitVec.sub_add_cancel])

theorem storeMem_comm_disjoint (m : Mem 64) (t₁ t₂ : Ty) (a₁ a₂ : BitVec 64)
    (v₁ : Val t₁) (v₂ : Val t₂)
    (hdisj : ∀ i j, i < t₁.bytes → j < t₂.bytes →
      a₂ + BitVec.ofNat 64 j ≠ a₁ + BitVec.ofNat 64 i) :
    storeMem (storeMem m t₁ a₁ v₁) t₂ a₂ v₂ = storeMem (storeMem m t₂ a₂ v₂) t₁ a₁ v₁ := by
  by_cases h01 : t₁.bytes = 0
  · simp [ZeroPeel.storeMem_eq_storeBytes, h01, Int.toBytes, ZeroPeel.storeBytes_nil]
  by_cases h02 : t₂.bytes = 0
  · simp [ZeroPeel.storeMem_eq_storeBytes, h02, Int.toBytes, ZeroPeel.storeBytes_nil]
  have ht1 := bytes_le_of_disj (a := a₁) (b := a₂) fun i hi => by
    simpa using hdisj i 0 hi (by omega)
  have ht2 := bytes_le_of_disj (a := a₂) (b := a₁) fun j hj => by
    simpa using (hdisj 0 j (by omega) hj).symm
  let bs₁ := Int.toBytes t₁.bytes ((toBits t₁ v₁).setWidth (8 * t₁.bytes)).toInt
  let bs₂ := Int.toBytes t₂.bytes ((toBits t₂ v₂).setWidth (8 * t₂.bytes)).toInt
  have hl1 : bs₁.length = t₁.bytes := Int.toBytes_length _ _
  have hl2 : bs₂.length = t₂.bytes := Int.toBytes_length _ _
  rw [Bedrock2.storeMem_eq_union _ _ _ _ ht2, Bedrock2.storeMem_eq_union _ _ _ _ ht1,
    Bedrock2.storeMem_eq_union _ _ _ _ ht1, Bedrock2.storeMem_eq_union _ _ _ _ ht2]
  apply Std.ExtHashMap.ext_getElem?; intro p
  simp only [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  by_cases h2 : p ∈ bs₂.At a₂
  · have hnot1 : p ∉ bs₁.At a₁ := by
      rw [mem_At_iff, hl2] at h2; rw [mem_At_iff, hl1]
      rintro ⟨i, hi, rfl⟩; rcases h2 with ⟨j, hj, heq⟩; exact hdisj i j hi hj heq.symm
    rw [Std.ExtHashMap.getElem?_eq_none hnot1]; cases (bs₂.At a₂)[p]? <;> cases m[p]? <;> rfl
  · rw [Std.ExtHashMap.getElem?_eq_none h2]; cases (bs₁.At a₁)[p]? <;> cases m[p]? <;> rfl

theorem storeMem_storeMem_same (m : Mem 64) (t : Ty) (a : BitVec 64) (v₁ v₂ : Val t)
    (hb : t.bytes ≤ 2 ^ 64) :
    storeMem (storeMem m t a v₁) t a v₂ = storeMem m t a v₂ := by
  let bs₁ := Int.toBytes t.bytes ((toBits t v₁).setWidth (8 * t.bytes)).toInt
  let bs₂ := Int.toBytes t.bytes ((toBits t v₂).setWidth (8 * t.bytes)).toInt
  have hl1 : bs₁.length = t.bytes := Int.toBytes_length _ _
  have hl2 : bs₂.length = t.bytes := Int.toBytes_length _ _
  rw [Bedrock2.storeMem_eq_union _ _ _ _ hb, Bedrock2.storeMem_eq_union _ _ _ _ hb,
    Bedrock2.storeMem_eq_union _ _ _ _ hb]
  apply Std.ExtHashMap.ext_getElem?; intro p
  simp only [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  by_cases h2 : p ∈ bs₂.At a
  · rcases Option.isSome_iff_exists.1 (Std.ExtHashMap.mem_iff_isSome_getElem?.1 h2) with ⟨b, hb⟩
    rw [hb]; rfl
  · have hnot1 : p ∉ bs₁.At a := by
      intro h1; apply h2
      rw [mem_At_iff, hl1] at h1
      rw [mem_At_iff, hl2]
      exact h1
    rw [Std.ExtHashMap.getElem?_eq_none h2, Std.ExtHashMap.getElem?_eq_none hnot1]
    cases m[p]? <;> rfl

theorem loadVal_writeSlots_disjoint (m : Mem 64) (sp₀ : BitVec 64) (t : Ty) (a : BitVec 64) :
    ∀ (base : Nat) (vs : List (BitVec 64)),
      (∀ k i j, base ≤ k → k < base + vs.length → i < 8 → j < t.bytes →
        a + BitVec.ofNat 64 j ≠ slotAddr sp₀ k + BitVec.ofNat 64 i) →
      loadVal (writeSlots m sp₀ base vs) t a = loadVal m t a
  | _, [], _ => rfl
  | base, v :: vs, hdisj => by
      dsimp only [writeSlots]
      rw [loadVal_writeSlots_disjoint _ sp₀ t a (base + 1) vs (fun k i j hk1 hk2 =>
            hdisj k i j (by omega) (by simp at hk2 ⊢; omega))]
      exact loadVal_storeMem_disjoint m i64 t (slotAddr sp₀ base) a v
        (fun i j hi hj => hdisj base i j (Nat.le_refl _) (by simp) hi hj)

theorem storeOk_writeSlots_disjoint (m : Mem 64) (sp₀ : BitVec 64) (t : Ty) (a : BitVec 64) :
    ∀ (base : Nat) (vs : List (BitVec 64)),
      (∀ k i j, base ≤ k → k < base + vs.length → i < 8 → j < t.bytes →
        a + BitVec.ofNat 64 j ≠ slotAddr sp₀ k + BitVec.ofNat 64 i) →
      (storeOk (writeSlots m sp₀ base vs) t a ↔ storeOk m t a)
  | _, [], _ => Iff.rfl
  | base, v :: vs, hdisj => by
      dsimp only [writeSlots]
      rw [storeOk_writeSlots_disjoint _ sp₀ t a (base + 1) vs (fun k i j hk1 hk2 =>
            hdisj k i j (by omega) (by simp at hk2 ⊢; omega))]
      exact storeOk_storeMem_disjoint m i64 t (slotAddr sp₀ base) a v
        (fun i j hi hj => hdisj base i j (Nat.le_refl _) (by simp) hi hj)

theorem storeMem_writeSlots_disjoint (m : Mem 64) (sp₀ : BitVec 64) (t : Ty) (a : BitVec 64)
    (v : Val t) :
    ∀ (base : Nat) (vs : List (BitVec 64)),
      (∀ k i j, base ≤ k → k < base + vs.length → i < 8 → j < t.bytes →
        a + BitVec.ofNat 64 j ≠ slotAddr sp₀ k + BitVec.ofNat 64 i) →
      storeMem (writeSlots m sp₀ base vs) t a v = writeSlots (storeMem m t a v) sp₀ base vs
  | _, [], _ => rfl
  | base, u :: vs, hdisj => by
      dsimp only [writeSlots]
      rw [storeMem_writeSlots_disjoint _ sp₀ t a v (base + 1) vs (fun k i j hk1 hk2 =>
            hdisj k i j (by omega) (by simp at hk2 ⊢; omega))]
      rw [storeMem_comm_disjoint m i64 t (slotAddr sp₀ base) a u v
        (fun i j hi hj => hdisj base i j (Nat.le_refl _) (by simp) hi hj)]

theorem loadVal_writeSlots_slot (sp₀ : BitVec 64) :
    ∀ (base : Nat) (vs : List (BitVec 64)) (m : Mem 64) (k : Nat),
      base ≤ k → k < base + vs.length → base + vs.length ≤ 64 →
      ∃ v, vs[k - base]? = some v ∧
        loadVal (writeSlots m sp₀ base vs) i64 (slotAddr sp₀ k) = some v
  | _, [], _, _, hlo, hhi, _ => by simp at hhi; omega
  | base, u :: vs, m, k, hlo, hhi, hlim => by
      dsimp only [writeSlots]
      by_cases hEq : k = base
      · cases hEq
        refine ⟨u, by simp, ?_⟩
        rw [loadVal_writeSlots_disjoint _ sp₀ i64 (slotAddr sp₀ base) (base + 1) vs
          (fun k' i j hk1 hk2 hi hj =>
            slotAddr_disjoint sp₀ (by simp at hlim; omega) (by simp at hlim; omega)
              (by omega) hj hi)]
        exact loadVal_storeMem m i64 (slotAddr sp₀ base) u (by decide)
      · have ih := loadVal_writeSlots_slot sp₀ (base + 1) vs
          (storeMem m i64 (slotAddr sp₀ base) u) k (by omega) (by simp at hhi ⊢; omega)
          (by simp at hlim ⊢; omega)
        rcases ih with ⟨v, hv, hload⟩
        refine ⟨v, ?_, hload⟩
        have hidx : k - base = (k - (base + 1)) + 1 := by omega
        rw [hidx]
        exact hv

theorem storeMem_writeSlots_slot (sp₀ : BitVec 64) (v : BitVec 64) :
    ∀ (base : Nat) (vs : List (BitVec 64)) (m : Mem 64) (k : Nat),
      base ≤ k → k < base + vs.length → base + vs.length ≤ 64 →
      storeMem (writeSlots m sp₀ base vs) i64 (slotAddr sp₀ k) v =
        writeSlots m sp₀ base (vs.set (k - base) v)
  | _, [], _, _, hlo, hhi, _ => by simp at hhi; omega
  | base, u :: vs, m, k, hlo, hhi, hlim => by
      dsimp only [writeSlots]
      by_cases hEq : k = base
      · cases hEq
        rw [Nat.sub_self, List.set_cons_zero]
        dsimp only [writeSlots]
        rw [storeMem_writeSlots_disjoint _ sp₀ i64 (slotAddr sp₀ base) v (base + 1) vs
          (fun k' i j hk1 hk2 hi hj =>
            slotAddr_disjoint sp₀ (by simp at hlim; omega) (by simp at hlim; omega)
              (by omega) hj hi)]
        rw [storeMem_storeMem_same _ _ _ _ _ (by decide)]
      · have hidx : k - base = (k - (base + 1)) + 1 := by omega
        rw [hidx, List.set_cons_succ]
        dsimp only [writeSlots]
        exact storeMem_writeSlots_slot sp₀ v (base + 1) vs
          (storeMem m i64 (slotAddr sp₀ base) u) k (by omega) (by simp at hhi ⊢; omega)
          (by simp at hlim ⊢; omega)

theorem storeOk_writeSlots (m : Mem 64) (sp₀ : BitVec 64) (t : Ty) (a : BitVec 64) :
    ∀ (base : Nat) (vs : List (BitVec 64)),
      storeOk m t a → storeOk (writeSlots m sp₀ base vs) t a
  | _, [], hok => hok
  | base, v :: vs, hok =>
      storeOk_writeSlots _ sp₀ t a (base + 1) vs
        (storeOk_storeMem m i64 t (slotAddr sp₀ base) a v hok)

theorem frameRel_set_slot {nSlots : Nat} {sp₀ : BitVec 64} {slots : List (BitVec 64)}
    {mConc mPub : Mem 64} (hnPos : nSlots ≠ 0) (hfr : FrameRel nSlots sp₀ slots mConc mPub)
    {k : Nat} (hk : k < nSlots) (v : BitVec 64) :
    FrameRel nSlots sp₀ (slots.set k v) (storeMem mConc i64 (slotAddr sp₀ k) v) mPub := by
  dsimp only [FrameRel] at hfr ⊢
  rw [ite_eq_right hnPos] at hfr ⊢
  rcases hfr with ⟨hlen, hle, hok, rfl⟩
  refine ⟨by simpa [List.length_set] using hlen, hle, hok, ?_⟩
  simpa [Nat.sub_zero] using storeMem_writeSlots_slot sp₀ v 0 slots mPub k
    (Nat.zero_le _) (by omega) (by omega)

theorem frameRel_store_disjoint {nSlots : Nat} {sp₀ : BitVec 64} {slots : List (BitVec 64)}
    {mConc mPub : Mem 64} (hfr : FrameRel nSlots sp₀ slots mConc mPub)
    (t : Ty) (a : BitVec 64) (v : Val t)
    (hdisj : ∀ k i j, k < nSlots → i < 8 → j < t.bytes →
      a + BitVec.ofNat 64 j ≠ slotAddr sp₀ k + BitVec.ofNat 64 i) :
    FrameRel nSlots sp₀ slots (storeMem mConc t a v) (storeMem mPub t a v) := by
  by_cases hn : nSlots = 0
  · subst hn; dsimp only [FrameRel] at hfr ⊢; simp only [↓reduceIte] at hfr ⊢; rw [hfr]
  · dsimp only [FrameRel] at hfr ⊢
    rw [ite_eq_right hn] at hfr ⊢
    rcases hfr with ⟨hlen, hle, hok, rfl⟩
    refine ⟨hlen, hle, fun k hk => storeOk_storeMem mPub t i64 a (slotAddr sp₀ k) v (hok k hk), ?_⟩
    exact storeMem_writeSlots_disjoint mPub sp₀ t a v 0 slots
      (fun k i j _ hk2 => hdisj k i j (by omega))

theorem frameRel_zero {sp₀ : BitVec 64} {slots : List (BitVec 64)} {mConc mPub : Mem 64}
    (hfr : FrameRel 0 sp₀ slots mConc mPub) : mConc = mPub := by
  simpa [FrameRel] using hfr

/-! ## §2. `EnvMapOk`, `SlotsLvlsOk`, `ContSymStateOk`, `evalContOp_sound`, and Prefix Lemmas -/

private theorem bv64_shl3_eq_mul8 (x : BitVec 64) :
    x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, show 2 ^ 3 = 8 by decide,
      Nat.mul_comm]

private theorem bv64_mul8_eq_ofNat (x : BitVec 64) :
    x * 8#64 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [show 8 % 2 ^ 64 = 8 by decide, Nat.mul_comm x.toNat 8]

private theorem bv64_untag_aligned {w tag : BitVec 64} (hal : AlignedAddr w)
    (ht : tag.toNat < 8) :
    (w ||| tag) &&& ~~~7#64 = w := by
  have htag0 : tag &&& ~~~7#64 = 0#64 := by
    match h : tag.toNat with
    | 0 => have : tag = 0#64 := BitVec.eq_of_toNat_eq (by simp [h]); rw [this]; decide
    | 1 => have : tag = 1#64 := BitVec.eq_of_toNat_eq (by simp [h]); rw [this]; decide
    | 2 => have : tag = 2#64 := BitVec.eq_of_toNat_eq (by simp [h]); rw [this]; decide
    | 3 => have : tag = 3#64 := BitVec.eq_of_toNat_eq (by simp [h]); rw [this]; decide
    | 4 => have : tag = 4#64 := BitVec.eq_of_toNat_eq (by simp [h]); rw [this]; decide
    | 5 => have : tag = 5#64 := BitVec.eq_of_toNat_eq (by simp [h]); rw [this]; decide
    | 6 => have : tag = 6#64 := BitVec.eq_of_toNat_eq (by simp [h]); rw [this]; decide
    | 7 => have : tag = 7#64 := BitVec.eq_of_toNat_eq (by simp [h]); rw [this]; decide
    | _ + 8 => omega
  ext i
  have hwi := congrArg (·[i]) hal
  have hti := congrArg (·[i]) htag0
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_zero]
    at hwi hti ⊢
  cases hw : w[i] <;> cases htag : tag[i] <;> cases h7 : (7#64)[i] <;> simp_all

@[expose] def cLevelVal {t : Ty} (bvs : List ((t' : Ty) × Val t')) (lvl : Nat) : Option (Val t) :=
  if lvl < bvs.length then lookupV bvs t (bvs.length - 1 - lvl) else none

theorem cLevelVal_prepend {t : Ty} (extra bvs : List ((t' : Ty) × Val t'))
    {lvl : Nat} {x : Val t} (h : cLevelVal bvs lvl = some x) :
    cLevelVal (extra ++ bvs) lvl = some x := by
  dsimp only [cLevelVal] at h ⊢
  split at h
  · rename_i hlt
    have hlt' : lvl < (extra ++ bvs).length := by rw [List.length_append]; omega
    rw [ite_eq_left hlt']
    dsimp only [lookupV] at h ⊢
    rw [show (extra ++ bvs).length - 1 - lvl = extra.length + (bvs.length - 1 - lvl) by
      rw [List.length_append]; omega]
    rw [listGet?_append_skip]
    exact h
  · cases h

theorem cLevelVal_lt_len {bvs : List ((t : Ty) × Val t)} {t : Ty} {lvl : Nat} {x : Val t}
    (hl : cLevelVal bvs lvl = some x) : lvl < bvs.length := by
  dsimp only [cLevelVal] at hl
  split at hl <;> rename_i hlt
  · exact hlt
  · cases hl

/-- Symbolic value correctness invariant for Stage-1 `ContSymVal`. -/
@[expose] def ContSymValMatch (bvs : List ((t : Ty) × Val t)) (sp₀ rp₀ : BitVec 64) :
    ContSymVal → (t : Ty) → Val t → Prop
  | .spOffset off, t, v => ∀ h : t = i64, cast (congrArg Val h) v = sp₀ + off
  | .rpOffset off, t, v => ∀ h : t = i64, cast (congrArg Val h) v = rp₀ + off
  | .const w, t, v => ∀ h : t = i64, cast (congrArg Val h) v = w
  | .alignedConst w, t, v => ∀ h : t = i64, cast (congrArg Val h) v = w ∧ AlignedAddr w
  | .taggedAligned w tag, t, v =>
      ∀ h : t = i64, cast (congrArg Val h) v = w ||| tag ∧ AlignedAddr w ∧ tag.toNat < 8
  | .shl3 lvl, t, v => ∀ h : t = i64,
      ∃ x : Val i64, cLevelVal bvs lvl = some x ∧
        cast (congrArg Val h) v = BitVec.ofNat 64 (8 * x.toNat)
  | .stride base lvl, t, v => ∀ h : t = i64,
      ∃ x : Val i64, cLevelVal bvs lvl = some x ∧
        cast (congrArg Val h) v = base + BitVec.ofNat 64 (8 * x.toNat)
  | .ite cLvl tSym eSym, t, v => ∀ h : t = i64,
      ∃ b : Val .bool, cLevelVal bvs cLvl = some b ∧
        ((b = true → ContSymValMatch bvs sp₀ rp₀ tSym i64 (cast (congrArg Val h) v)) ∧
         (b = false → ContSymValMatch bvs sp₀ rp₀ eSym i64 (cast (congrArg Val h) v)))
  | .boolConst c, t, v => ∀ h : t = .bool, cast (congrArg Val h) v = c
  | .cmpUlt lvl bound, t, v => ∀ h : t = .bool,
      ∃ x : Val i64, cLevelVal bvs lvl = some x ∧
        cast (congrArg Val h) v = BitVec.ult x bound
  | .top, _, _ => True

@[expose] def ContSymFactsOk (bvs : List ((t : Ty) × Val t)) (facts : List SymFact) : Prop :=
  ∀ f ∈ facts, match f with
    | .ultBound lvl bound => ∃ x : Val i64, cLevelVal bvs lvl = some x ∧ x.toNat < bound.toNat

private theorem contCtx_push :
    ∀ {ts : List Ty} (xs : Tup Val ts) {bvs : List ((t : Ty) × Val t)} {Γ : List Ty},
      bvs.map Sigma.fst = Γ → (pushTup xs bvs).map Sigma.fst = pushTypes ts Γ
  | [], (), _, _, h => h
  | _ :: _, (_, xs), _, _, h => contCtx_push xs (congrArg (_ :: ·) h)

structure ContSymStateOk (bvs : List ((t : Ty) × Val t)) (sp₀ rp₀ : BitVec 64)
    (st : ContSymState) : Prop where
  lenEq   : st.env.length = bvs.length
  ctxOk   : bvs.map Sigma.fst = st.ctx
  valsOk  : ∀ idx, idx < bvs.length →
    match listGet? st.env idx, listGet? bvs idx with
    | some sv, some ⟨t, v⟩ => ContSymValMatch bvs sp₀ rp₀ sv t v
    | _, _ => True
  factsOk : ContSymFactsOk bvs st.facts

theorem contSymValMatch_prepend (extra bvs : List ((t' : Ty) × Val t'))
    (sp₀ rp₀ : BitVec 64) :
    (sv : ContSymVal) → (t : Ty) → (v : Val t) →
    ContSymValMatch bvs sp₀ rp₀ sv t v → ContSymValMatch (extra ++ bvs) sp₀ rp₀ sv t v
  | .spOffset _, _, _, h => h
  | .rpOffset _, _, _, h => h
  | .const _, _, _, h => h
  | .alignedConst _, _, _, h => h
  | .taggedAligned _ _, _, _, h => h
  | .shl3 _, _, _, h => fun heq =>
      let ⟨x, hx, hval⟩ := h heq
      ⟨x, cLevelVal_prepend extra bvs hx, hval⟩
  | .stride _ _, _, _, h => fun heq =>
      let ⟨x, hx, hval⟩ := h heq
      ⟨x, cLevelVal_prepend extra bvs hx, hval⟩
  | .ite _ tS eS, _, _, h => fun heq =>
      let ⟨b, hb, ht, he⟩ := h heq
      ⟨b, cLevelVal_prepend extra bvs hb,
       fun hc => contSymValMatch_prepend extra bvs sp₀ rp₀ tS i64 _ (ht hc),
       fun hc => contSymValMatch_prepend extra bvs sp₀ rp₀ eS i64 _ (he hc)⟩
  | .boolConst _, _, _, h => h
  | .cmpUlt _ _, _, _, h => fun heq =>
      let ⟨x, hx, hval⟩ := h heq
      ⟨x, cLevelVal_prepend extra bvs hx, hval⟩
  | .top, _, _, _ => trivial

private theorem contSymFactsOk_prepend (extra bvs : List ((t' : Ty) × Val t'))
    {facts : List SymFact} (h : ContSymFactsOk bvs facts) :
    ContSymFactsOk (extra ++ bvs) facts := by
  intro f hf
  cases f with
  | ultBound lvl bound =>
      obtain ⟨x, hx, hlt⟩ := h _ hf
      exact ⟨x, cLevelVal_prepend extra bvs hx, hlt⟩

private theorem castTy_same_eq' {V : Ty → Type} {t' t : Ty} {v' : V t'} {v : V t}
    (h : castTy t' t v' = some v) : ∃ heq : t' = t, heq ▸ v' = v := by
  cases t' with
  | bool => cases t with
      | bool => cases h; exact ⟨rfl, rfl⟩
      | _ => cases h
  | bits m => cases t with
      | bits n =>
          dsimp only [castTy] at h
          split at h
          · rename_i heq; subst heq; cases h; exact ⟨rfl, rfl⟩
          · cases h
      | _ => cases h
  | float f => cases t with
      | float g =>
          dsimp only [castTy] at h
          split at h
          · rename_i heq; subst heq; cases h; exact ⟨rfl, rfl⟩
          · cases h
      | _ => cases h
  | pair a1 b1 => cases t with
      | pair a2 b2 =>
          dsimp only [castTy] at h
          cases h1 : tyDecEq a1 a2 <;> rw [h1] at h; · cases h
          cases h2 : tyDecEq b1 b2 <;> rw [h2] at h; · cases h
          rename_i e1 e2; subst e1 e2; cases h; exact ⟨rfl, rfl⟩
      | _ => cases h

theorem evalContArg_symValMatch {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {st : ContSymState} (hst : ContSymStateOk bvs sp₀ rp₀ st) {t : Ty} {a : Arg K t}
    {a' : Arg Val t} (ha : denoteArg bvs a = some a') :
    ContSymValMatch bvs sp₀ rp₀ (st.evalArg a) t a'.val := by
  cases a with
  | imm _ =>
      cases ha
      dsimp only [ContSymState.evalArg, Arg.val]
      cases t with
      | bool => exact fun _ => rfl
      | bits n =>
          by_cases h64 : n = 64
          · subst h64; exact fun _ => rfl
          · have hne : Ty.bits n ≠ Ty.bits 64 := fun he => h64 (by cases he; rfl)
            split
            · contradiction
            · exact absurd ‹_› hne
            · exact trivial
      | float _ | pair _ _ => trivial
  | var idx =>
      dsimp only [denoteArg, lookupV] at ha
      cases hg : listGet? bvs idx with
      | none => rw [hg] at ha; cases ha
      | some p =>
          rcases p with ⟨t', v'⟩
          rw [hg] at ha; dsimp only at ha
          cases hc : castTy t' t v' with
          | none => rw [hc] at ha; cases ha
          | some _ =>
              rw [hc] at ha; cases ha
              obtain ⟨heq, hv⟩ := castTy_same_eq' hc
              subst heq; cases hv
              have hlt : idx < bvs.length := listGet?_isSome_lt bvs (by rw [hg]; rfl)
              have hval := hst.valsOk idx hlt
              rw [hg] at hval
              dsimp only [ContSymState.evalArg, ContSymState.getSym]
              cases he : listGet? st.env idx with
              | none => exact trivial
              | some _ => rw [he] at hval; exact hval

theorem contSymStateOk_init (r : Regs) :
    ContSymStateOk (pushRegsV r.toRegsV) r.sp r.rp ContSymState.init := by
  refine ⟨rfl, rfl, ?_, fun _ h => nomatch h⟩
  intro idx hlt
  match idx with
  | 0 | 1 | 2 | 3 => exact trivial
  | 4 => exact fun _ => by simp only [cast_eq, Regs.toRegsV]; exact (BitVec.add_zero r.rp).symm
  | 5 => exact fun _ => by simp only [cast_eq, Regs.toRegsV]; exact (BitVec.add_zero r.sp).symm
  | _ + 6 => exact absurd hlt (by simp [pushRegsV, RegsV.toTup, pushTup])

private theorem listGet?_replicate_contTop :
    ∀ (ts : List Ty) (idx : Nat), idx < ts.length →
      listGet? (List.replicate ts.length ContSymVal.top) idx = some .top
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: ts, idx + 1, hi => listGet?_replicate_contTop ts idx (Nat.lt_of_succ_lt_succ hi)

private theorem contSymStateOk_pushTop (extra : List ((t : Ty) × Val t)) (ts : List Ty)
    {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64} {st : ContSymState}
    (hst : ContSymStateOk bvs sp₀ rp₀ st) (heq : extra.length = ts.length)
    (hctx : (extra ++ bvs).map Sigma.fst = pushTypes ts st.ctx) :
    ContSymStateOk (extra ++ bvs) sp₀ rp₀
      (st.pushRes ts (List.replicate ts.length .top)) := by
  refine ⟨by simp [ContSymState.pushRes, heq, hst.lenEq], hctx, ?_,
    contSymFactsOk_prepend extra bvs hst.factsOk⟩
  intro idx hlt
  dsimp only [ContSymState.pushRes]
  by_cases hi : idx < extra.length
  · have hltRep : idx < (List.replicate ts.length ContSymVal.top).length := by simpa [heq] using hi
    rw [listGet?_append_left (List.replicate ts.length .top) st.env hltRep,
        listGet?_append_left extra bvs hi,
        listGet?_replicate_contTop ts idx (by omega)]
    cases listGet? extra idx <;> trivial
  · have hk : ∃ k, idx = extra.length + k ∧ k < bvs.length := by
      refine ⟨idx - extra.length, by omega, ?_⟩
      rw [List.length_append] at hlt; omega
    rcases hk with ⟨k, rfl, hk⟩
    have hrep : (List.replicate ts.length ContSymVal.top).length = extra.length := by simp [heq]
    have hskip : listGet? (List.replicate ts.length ContSymVal.top ++ st.env) (extra.length + k) =
        listGet? st.env k := by rw [← hrep, listGet?_append_skip]
    rw [hskip, listGet?_append_skip extra bvs k]
    have h0 := hst.valsOk k hk
    cases h1 : listGet? st.env k <;> cases h2 : listGet? bvs k
    · exact trivial
    · exact trivial
    · exact trivial
    · rw [h1, h2] at h0; exact contSymValMatch_prepend extra bvs sp₀ rp₀ _ _ _ h0

theorem contSymStateOk_cons {t : Ty} (v : Val t) (sv : ContSymVal)
    {bvs : List ((t' : Ty) × Val t')} {sp₀ rp₀ : BitVec 64} {st : ContSymState}
    (hst : ContSymStateOk bvs sp₀ rp₀ st)
    (hsv : ContSymValMatch (⟨t, v⟩ :: bvs) sp₀ rp₀ sv t v) :
    ContSymStateOk (⟨t, v⟩ :: bvs) sp₀ rp₀
      { env := sv :: st.env, ctx := t :: st.ctx, facts := st.facts } := by
  refine ⟨by simp [hst.lenEq], congrArg (t :: ·) hst.ctxOk, ?_,
    contSymFactsOk_prepend [⟨t, v⟩] bvs hst.factsOk⟩
  intro idx hlt
  cases idx with
  | zero => exact hsv
  | succ k =>
      have hk : k < bvs.length := Nat.lt_of_succ_lt_succ hlt
      have h0 := hst.valsOk k hk
      dsimp only [listGet?]
      cases h1 : listGet? st.env k <;> cases h2 : listGet? bvs k
      · exact trivial
      · exact trivial
      · exact trivial
      · rw [h1, h2] at h0; exact contSymValMatch_prepend [⟨t, v⟩] bvs sp₀ rp₀ _ _ _ h0

private theorem contVar_levelVal {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {st : ContSymState} (hst : ContSymStateOk bvs sp₀ rp₀ st) {t : Ty} {idx lvl : Nat}
    {a' : Arg Val t} (hlvl : st.toLevel? idx = some lvl)
    (hden : denoteArg bvs (.var idx) = some a') :
    cLevelVal bvs lvl = some a'.val := by
  dsimp only [ContSymState.toLevel?] at hlvl
  split at hlvl <;> rename_i hlt
  · cases hlvl
    have hb : idx < bvs.length := by rwa [← hst.lenEq]
    have hltL : bvs.length - 1 - idx < bvs.length := by omega
    rw [hst.lenEq]
    dsimp only [cLevelVal]
    rw [ite_eq_left hltL, show bvs.length - 1 - (bvs.length - 1 - idx) = idx by omega]
    dsimp only [denoteArg] at hden
    cases hl : lookupV bvs t idx with
    | none => rw [hl] at hden; cases hden
    | some _ => rw [hl] at hden; cases hden; rfl
  · cases hlvl

theorem contAsConst_eq {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {sv : ContSymVal} {v : Val i64} (hm : ContSymValMatch bvs sp₀ rp₀ sv i64 v)
    {w : BitVec 64} (hc : sv.asConst? = some w) : v = w := by
  cases sv with
  | const _ => cases hc; simpa using hm rfl
  | alignedConst _ => cases hc; simpa using (hm rfl).1
  | spOffset _ | rpOffset _ | taggedAligned _ _ | shl3 _ | stride _ _ | ite _ _ _
  | boolConst _ | cmpUlt _ _ | top => cases hc

private theorem contMkAdd_sound {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {sx sy : ContSymVal} {vx vy : Val i64}
    (hx : ContSymValMatch bvs sp₀ rp₀ sx i64 vx) (hy : ContSymValMatch bvs sp₀ rp₀ sy i64 vy) :
    ContSymValMatch (⟨i64, vx + vy⟩ :: bvs) sp₀ rp₀ (contMkAdd sx sy) i64 (vx + vy) := by
  have hx' := contSymValMatch_prepend [⟨i64, vx + vy⟩] bvs sp₀ rp₀ sx i64 vx hx
  have hy' := contSymValMatch_prepend [⟨i64, vx + vy⟩] bvs sp₀ rp₀ sy i64 vy hy
  dsimp only [contMkAdd]
  split
  · intro _; have h1 := hx rfl; have h2 := hy rfl
    simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2, BitVec.add_assoc]
  · intro _; have h1 := hx rfl; have h2 := hy rfl
    simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2, BitVec.add_comm, BitVec.add_assoc]
  · intro _; have h1 := hx rfl; have h2 := hy rfl
    simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2, BitVec.add_assoc]
  · intro _; have h1 := hx rfl; have h2 := hy rfl
    simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2, BitVec.add_comm, BitVec.add_assoc]
  · intro _; obtain ⟨idx, hidx, hvy⟩ := hy' rfl
    have h1 := (hx rfl).1; simp only [cast_eq] at h1 hvy ⊢
    exact ⟨idx, hidx, by rw [h1, hvy]⟩
  · intro _; obtain ⟨idx, hidx, hvy⟩ := hy' rfl
    have h1 := hx rfl; simp only [cast_eq] at h1 hvy ⊢
    exact ⟨idx, hidx, by rw [h1, hvy]⟩
  · intro _; obtain ⟨idx, hidx, hvx⟩ := hx' rfl
    have h2 := (hy rfl).1; simp only [cast_eq] at h2 hvx ⊢
    exact ⟨idx, hidx, by rw [hvx, h2, BitVec.add_comm]⟩
  · intro _; obtain ⟨idx, hidx, hvx⟩ := hx' rfl
    have h2 := hy rfl; simp only [cast_eq] at h2 hvx ⊢
    exact ⟨idx, hidx, by rw [hvx, h2, BitVec.add_comm]⟩
  · cases hax : sx.asConst? <;> cases hay : sy.asConst?
    · exact trivial
    · exact trivial
    · exact trivial
    · intro _; simp only [cast_eq]
      rw [contAsConst_eq hx hax, contAsConst_eq hy hay]

private theorem contMkSub_sound {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {sx sy : ContSymVal} {vx vy : Val i64}
    (hx : ContSymValMatch bvs sp₀ rp₀ sx i64 vx) (hy : ContSymValMatch bvs sp₀ rp₀ sy i64 vy) :
    ContSymValMatch (⟨i64, vx - vy⟩ :: bvs) sp₀ rp₀ (contMkSub sx sy) i64 (vx - vy) := by
  dsimp only [contMkSub]
  split
  · intro _; have h1 := hx rfl; have h2 := hy rfl
    simp only [cast_eq] at h1 h2 ⊢
    rw [h1, h2, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  · cases hax : sx.asConst? <;> cases hay : sy.asConst?
    · exact trivial
    · exact trivial
    · exact trivial
    · intro _; simp only [cast_eq]; rw [contAsConst_eq hx hax, contAsConst_eq hy hay]

private theorem contMkOrTag_sound {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {sx sy : ContSymVal} {vx vy : Val i64}
    (hx : ContSymValMatch bvs sp₀ rp₀ sx i64 vx) (hy : ContSymValMatch bvs sp₀ rp₀ sy i64 vy) :
    ContSymValMatch (⟨i64, vx ||| vy⟩ :: bvs) sp₀ rp₀ (contMkOrTag sx sy) i64 (vx ||| vy) := by
  dsimp only [contMkOrTag]
  split
  · rename_i w tag
    by_cases hu : BitVec.ult tag 8#64 = true
    · rw [ite_eq_left hu]; intro _
      obtain ⟨hvx, hal⟩ := hx rfl; have hvy := hy rfl
      simp only [cast_eq] at hvx hvy ⊢
      exact ⟨by rw [hvx, hvy], hal, of_decide_eq_true hu⟩
    · rw [ite_eq_right (by simpa using hu)]; intro _
      obtain ⟨hvx, _⟩ := hx rfl; have hvy := hy rfl
      simp only [cast_eq] at hvx hvy ⊢; rw [hvx, hvy]
  · rename_i tag w
    by_cases hu : BitVec.ult tag 8#64 = true
    · rw [ite_eq_left hu]; intro _
      obtain ⟨hvy, hal⟩ := hy rfl; have hvx := hx rfl
      simp only [cast_eq] at hvx hvy ⊢
      exact ⟨by rw [hvx, hvy, BitVec.or_comm], hal, of_decide_eq_true hu⟩
    · rw [ite_eq_right (by simpa using hu)]; intro _
      obtain ⟨hvy, _⟩ := hy rfl; have hvx := hx rfl
      simp only [cast_eq] at hvx hvy ⊢; rw [hvx, hvy]
  · intro _; have h1 := hx rfl; have h2 := hy rfl; simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2]
  · exact trivial

private theorem contMkUntag_sound {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {sx sy : ContSymVal} {vx vy : Val i64}
    (hx : ContSymValMatch bvs sp₀ rp₀ sx i64 vx) (hy : ContSymValMatch bvs sp₀ rp₀ sy i64 vy) :
    ContSymValMatch (⟨i64, vx &&& vy⟩ :: bvs) sp₀ rp₀ (contMkUntag sx sy) i64 (vx &&& vy) := by
  dsimp only [contMkUntag]
  split
  · rename_i w tag m
    by_cases hm : m = ~~~7#64
    · subst hm; simp only [beq_self_eq_true, ↓reduceIte]; intro _
      obtain ⟨hvx, hal, ht⟩ := hx rfl; have hvy := hy rfl
      simp only [cast_eq] at hvx hvy ⊢
      rw [hvx, hvy, bv64_untag_aligned hal ht]; exact ⟨rfl, hal⟩
    · simp only [beq_false_of_ne hm, Bool.false_eq_true, ↓reduceIte]; exact trivial
  · rename_i m w tag
    by_cases hm : m = ~~~7#64
    · subst hm; simp only [beq_self_eq_true, ↓reduceIte]; intro _
      obtain ⟨hvy, hal, ht⟩ := hy rfl; have hvx := hx rfl
      simp only [cast_eq] at hvx hvy ⊢
      rw [hvx, hvy, BitVec.and_comm, bv64_untag_aligned hal ht]; exact ⟨rfl, hal⟩
    · simp only [beq_false_of_ne hm, Bool.false_eq_true, ↓reduceIte]; exact trivial
  · intro _; have h1 := hx rfl; have h2 := hy rfl; simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2]
  · intro _; have h1 := (hx rfl).1; have h2 := hy rfl
    simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2]
  · intro _; have h1 := hx rfl; have h2 := (hy rfl).1
    simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2]
  · exact trivial

private theorem evalContOp_top_step {ts : List Ty} (op : Op K ts) {st : ContSymState}
    {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {args' : Tup (Arg Val) op.sig}
    (hst : ContSymStateOk bvs sp₀ rp₀ st)
    (htop : evalContOp st op = List.replicate ts.length .top)
    {P₁ P₂ : Tup Val ts → Prop}
    (hstep : ∀ r, P₁ r →
      ContSymStateOk (pushTup r bvs) sp₀ rp₀ (st.pushRes ts (evalContOp st op)) → P₂ r)
    (hop : (⟨op.code, args'⟩ : Op Val ts).wp P₁) :
    (⟨op.code, args'⟩ : Op Val ts).wp P₂ := by
  apply Op.wp_mono (fun r hr => ?_) hop
  have hok := contSymStateOk_pushTop (pushTup r []) ts hst (pushTup_length r [])
    (by rw [← pushTup_append r [] bvs]; exact contCtx_push r hst.ctxOk)
  rw [← pushTup_append r [] bvs, ← htop] at hok
  exact hstep r hr hok

theorem evalContOp_wp_mono {ts : List Ty} (op : Op K ts) {st : ContSymState}
    {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {args' : Tup (Arg Val) op.sig}
    (hst : ContSymStateOk bvs sp₀ rp₀ st)
    (hargs : denoteArgs bvs op.args = some args')
    {P₁ P₂ : Tup Val ts → Prop}
    (hstep : ∀ r, P₁ r →
      ContSymStateOk (pushTup r bvs) sp₀ rp₀ (st.pushRes ts (evalContOp st op)) → P₂ r)
    (hop : (⟨op.code, args'⟩ : Op Val ts).wp P₁) :
    (⟨op.code, args'⟩ : Op Val ts).wp P₂ := by
  rcases op with ⟨code, args⟩
  cases code with
  | copy t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, ⟨⟩⟩; rcases args' with ⟨a', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals] at hop ⊢
            apply hstep (a'.val, ()) hop
            dsimp only [evalContOp, evalContOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            exact contSymStateOk_cons (t := i64) a'.val _ hst
              (contSymValMatch_prepend [⟨i64, a'.val⟩] bvs sp₀ rp₀ _ _ _
                (evalContArg_symValMatch hst ha))
          · exact evalContOp_top_step ⟨.copy (.bits n), args⟩ hst
              (by rcases args with ⟨_, ⟨⟩⟩; dsimp only [evalContOp, evalContOpCode]; simp [h64])
              hstep hop
      | bool =>
          rcases args with ⟨a, ⟨⟩⟩; rcases args' with ⟨a', ⟨⟩⟩
          dsimp only [denoteArgs] at hargs
          cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
          cases hargs
          dsimp only [Op.wp, OpCode.wp, vals] at hop ⊢
          apply hstep (a'.val, ()) hop
          exact contSymStateOk_cons (t := .bool) a'.val _ hst
            (contSymValMatch_prepend [⟨.bool, a'.val⟩] bvs sp₀ rp₀ _ _ _
              (evalContArg_symValMatch hst ha))
      | float _ | pair _ _ =>
          exact evalContOp_top_step ⟨.copy _, args⟩ hst rfl hstep hop
  | not t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, ⟨⟩⟩; rcases args' with ⟨a', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift1] at hop ⊢
            apply hstep _ hop
            have hma := evalContArg_symValMatch hst ha
            dsimp only [evalContOp, evalContOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            cases hc : (st.evalArg a).asConst? with
            | none => exact contSymStateOk_cons (t := i64) _ _ hst trivial
            | some _ => exact contSymStateOk_cons (t := i64) _ _ hst (fun _ => by
                simp only [cast_eq]; rw [contAsConst_eq hma hc])
          · exact evalContOp_top_step ⟨.not (.bits n), args⟩ hst
              (by rcases args with ⟨_, ⟨⟩⟩; dsimp only [evalContOp, evalContOpCode]; simp [h64])
              hstep hop
      | _ => exact evalContOp_top_step ⟨.not _, args⟩ hst rfl hstep hop
  | add t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat] at hop ⊢
            apply hstep _ hop
            dsimp only [evalContOp, evalContOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            exact contSymStateOk_cons (t := i64) _ _ hst
              (contMkAdd_sound (evalContArg_symValMatch hst ha) (evalContArg_symValMatch hst hb))
          · exact evalContOp_top_step ⟨.add (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, ⟨⟩⟩; dsimp only [evalContOp, evalContOpCode]; simp [h64])
              hstep hop
      | _ => exact evalContOp_top_step ⟨.add _, args⟩ hst rfl hstep hop
  | sub t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat] at hop ⊢
            apply hstep _ hop
            dsimp only [evalContOp, evalContOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            exact contSymStateOk_cons (t := i64) _ _ hst
              (contMkSub_sound (evalContArg_symValMatch hst ha) (evalContArg_symValMatch hst hb))
          · exact evalContOp_top_step ⟨.sub (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, ⟨⟩⟩; dsimp only [evalContOp, evalContOpCode]; simp [h64])
              hstep hop
      | _ => exact evalContOp_top_step ⟨.sub _, args⟩ hst rfl hstep hop
  | or t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift2] at hop ⊢
            apply hstep _ hop
            dsimp only [evalContOp, evalContOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            exact contSymStateOk_cons (t := i64) _ _ hst
              (contMkOrTag_sound (evalContArg_symValMatch hst ha)
                (evalContArg_symValMatch hst hb))
          · exact evalContOp_top_step ⟨.or (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, ⟨⟩⟩; dsimp only [evalContOp, evalContOpCode]; simp [h64])
              hstep hop
      | _ => exact evalContOp_top_step ⟨.or _, args⟩ hst rfl hstep hop
  | and t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift2] at hop ⊢
            apply hstep _ hop
            dsimp only [evalContOp, evalContOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            exact contSymStateOk_cons (t := i64) _ _ hst
              (contMkUntag_sound (evalContArg_symValMatch hst ha)
                (evalContArg_symValMatch hst hb))
          · exact evalContOp_top_step ⟨.and (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, ⟨⟩⟩; dsimp only [evalContOp, evalContOpCode]; simp [h64])
              hstep hop
      | _ => exact evalContOp_top_step ⟨.and _, args⟩ hst rfl hstep hop
  | shl t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat] at hop ⊢
            apply hstep _ hop
            have hmb := evalContArg_symValMatch hst hb
            dsimp only [evalContOp, evalContOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            split
            · rename_i idx heq
              cases hl : st.toLevel? idx with
              | none => exact contSymStateOk_cons (t := i64) _ _ hst trivial
              | some lvl =>
                  by_cases hty : st.levelHasTy lvl i64 = true
                  · simp only [hty, ↓reduceIte]
                    apply contSymStateOk_cons (t := i64) _ _ hst
                    intro _; simp only [cast_eq]
                    refine ⟨a'.val,
                      cLevelVal_prepend [⟨i64, _⟩] bvs (contVar_levelVal hst hl ha), ?_⟩
                    rw [contAsConst_eq hmb heq, show (3#64 : BitVec 64).toNat % 64 = 3 by decide,
                        bv64_shl3_eq_mul8]
                  · simp only [hty, Bool.false_eq_true, ↓reduceIte]
                    exact contSymStateOk_cons (t := i64) _ _ hst trivial
            · exact contSymStateOk_cons (t := i64) _ _ hst trivial
          · exact evalContOp_top_step ⟨.shl (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, ⟨⟩⟩; dsimp only [evalContOp, evalContOpCode]; simp [h64])
              hstep hop
      | _ => exact evalContOp_top_step ⟨.shl _, args⟩ hst rfl hstep hop
  | mul t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat] at hop ⊢
            apply hstep _ hop
            have hma := evalContArg_symValMatch hst ha
            have hmb := evalContArg_symValMatch hst hb
            dsimp only [evalContOp, evalContOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            split
            · rename_i idx heqB
              cases hl : st.toLevel? idx with
              | none => exact contSymStateOk_cons (t := i64) _ _ hst trivial
              | some lvl =>
                  by_cases hty : st.levelHasTy lvl i64 = true
                  · simp only [hty, ↓reduceIte]
                    apply contSymStateOk_cons (t := i64) _ _ hst
                    intro _; simp only [cast_eq]
                    refine ⟨a'.val,
                      cLevelVal_prepend [⟨i64, _⟩] bvs (contVar_levelVal hst hl ha), ?_⟩
                    rw [contAsConst_eq hmb heqB, bv64_mul8_eq_ofNat]
                  · simp only [hty, Bool.false_eq_true, ↓reduceIte]
                    exact contSymStateOk_cons (t := i64) _ _ hst trivial
            · rename_i idx heqA _
              cases hl : st.toLevel? idx with
              | none => exact contSymStateOk_cons (t := i64) _ _ hst trivial
              | some lvl =>
                  by_cases hty : st.levelHasTy lvl i64 = true
                  · simp only [hty, ↓reduceIte]
                    apply contSymStateOk_cons (t := i64) _ _ hst
                    intro _; simp only [cast_eq]
                    refine ⟨b'.val,
                      cLevelVal_prepend [⟨i64, _⟩] bvs (contVar_levelVal hst hl hb), ?_⟩
                    rw [contAsConst_eq hma heqA, BitVec.mul_comm, bv64_mul8_eq_ofNat]
                  · simp only [hty, Bool.false_eq_true, ↓reduceIte]
                    exact contSymStateOk_cons (t := i64) _ _ hst trivial
            · rename_i x y heqA heqB
              refine contSymStateOk_cons (t := i64) _ _ hst (fun _ => ?_)
              simp only [cast_eq]
              rw [contAsConst_eq hma heqA, contAsConst_eq hmb heqB, BitVec.mul_comm]
            · exact contSymStateOk_cons (t := i64) _ _ hst trivial
          · exact evalContOp_top_step ⟨.mul (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, ⟨⟩⟩; dsimp only [evalContOp, evalContOpCode]; simp [h64])
              hstep hop
      | _ => exact evalContOp_top_step ⟨.mul _, args⟩ hst rfl hstep hop
  | select t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨c, tA, eA, ⟨⟩⟩; rcases args' with ⟨c', tA', eA', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases hc : denoteArg bvs c <;> rw [hc] at hargs; · cases hargs
            cases ht : denoteArg bvs tA <;> rw [ht] at hargs; · cases hargs
            cases he : denoteArg bvs eA <;> rw [he] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals] at hop ⊢
            apply hstep _ hop
            have hmt := contSymValMatch_prepend [⟨i64, if c'.val then tA'.val else eA'.val⟩]
              bvs sp₀ rp₀ _ _ _ (evalContArg_symValMatch hst ht)
            have hme := contSymValMatch_prepend [⟨i64, if c'.val then tA'.val else eA'.val⟩]
              bvs sp₀ rp₀ _ _ _ (evalContArg_symValMatch hst he)
            dsimp only [evalContOp, evalContOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            cases c with
            | imm cb =>
                cases hc; cases cb
                · exact contSymStateOk_cons (t := i64) _ _ hst hme
                · exact contSymStateOk_cons (t := i64) _ _ hst hmt
            | var idx =>
                dsimp only
                cases hl : st.toLevel? idx with
                | none => exact contSymStateOk_cons (t := i64) _ _ hst trivial
                | some lvl =>
                    by_cases hty : st.levelHasTy lvl .bool = true
                    · simp only [hty, ↓reduceIte]
                      apply contSymStateOk_cons (t := i64) _ _ hst
                      intro _; simp only [cast_eq]
                      refine ⟨c'.val,
                        cLevelVal_prepend [⟨i64, _⟩] bvs (contVar_levelVal hst hl hc), ?_⟩
                      exact ⟨fun htr => by simpa [htr] using hmt,
                        fun hfl => by simpa [hfl] using hme⟩
                    · simp only [hty, Bool.false_eq_true, ↓reduceIte]
                      exact contSymStateOk_cons (t := i64) _ _ hst trivial
          · exact evalContOp_top_step ⟨.select (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, _, ⟨⟩⟩
                  dsimp only [evalContOp, evalContOpCode]; simp [h64])
              hstep hop
      | _ => exact evalContOp_top_step ⟨.select _, args⟩ hst rfl hstep hop
  | cmp cmpOp t _ h =>
      subst h
      cases cmpOp with
      | ult =>
          cases t with
          | bits n =>
              by_cases h64 : n = 64
              · subst h64
                rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
                dsimp only [denoteArgs] at hargs
                cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
                cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
                cases hargs
                dsimp only [Op.wp, OpCode.wp, vals, liftCmp, CmpOp.evalBits, Ty.hasFloat] at hop ⊢
                apply hstep _ hop
                have hmb := evalContArg_symValMatch hst hb
                dsimp only [evalContOp, evalContOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
                split
                · rename_i idx bound heq
                  cases hl : st.toLevel? idx with
                  | none => exact contSymStateOk_cons (t := .bool) _ _ hst trivial
                  | some lvl =>
                      by_cases hty : st.levelHasTy lvl i64 = true
                      · simp only [hty, ↓reduceIte]
                        apply contSymStateOk_cons (t := .bool) _ _ hst
                        intro _; simp only [cast_eq]
                        refine ⟨a'.val,
                          cLevelVal_prepend [⟨.bool, _⟩] bvs (contVar_levelVal hst hl ha), ?_⟩
                        rw [contAsConst_eq hmb heq]
                      · simp only [hty, Bool.false_eq_true, ↓reduceIte]
                        exact contSymStateOk_cons (t := .bool) _ _ hst trivial
                · exact contSymStateOk_cons (t := .bool) _ _ hst trivial
              · exact evalContOp_top_step ⟨.cmp .ult (.bits n), args⟩ hst
                  (by rcases args with ⟨_, _, ⟨⟩⟩
                      dsimp only [evalContOp, evalContOpCode]; simp [h64])
                  hstep hop
          | _ => exact evalContOp_top_step ⟨.cmp .ult _, args⟩ hst rfl hstep hop
      | _ =>
          exact evalContOp_top_step ⟨.cmp _ _, args⟩ hst
            (by cases t <;> rfl) hstep hop
  | _ => exact evalContOp_top_step ⟨_, args⟩ hst rfl hstep hop

theorem pushContCondFact_sound {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {st : ContSymState} (hst : ContSymStateOk bvs sp₀ rp₀ st) {c : Arg K .bool} {c' : Arg Val .bool}
    (hc : denoteArg bvs c = some c') (taken : Bool) (hval : c'.val = taken) :
    ContSymStateOk bvs sp₀ rp₀ (st.pushCondFact c taken) := by
  dsimp only [ContSymState.pushCondFact]
  cases taken
  · exact hst
  · cases c with
    | imm _ => exact hst
    | var idx =>
        simp only [↓reduceIte]
        have hmv := evalContArg_symValMatch hst hc
        dsimp only [ContSymState.evalArg] at hmv
        cases hgs : st.getSym idx with
        | cmpUlt lvl bound =>
            refine ⟨hst.lenEq, hst.ctxOk, hst.valsOk, ?_⟩
            intro f hf
            rcases List.mem_cons.1 hf with rfl | hf
            · rw [hgs] at hmv
              obtain ⟨x, hx, hult⟩ := hmv rfl
              rw [hval] at hult
              exact ⟨x, hx, of_decide_eq_true hult.symm⟩
            · exact hst.factsOk f hf
        | _ => exact hst

theorem pushContCondFact_ctx (st : ContSymState) (c : Arg K .bool) (taken : Bool) :
    (st.pushCondFact c taken).ctx = st.ctx := by
  dsimp only [ContSymState.pushCondFact]
  cases taken
  · rfl
  · cases c with
    | imm _ => rfl
    | var idx => simp only [↓reduceIte]; cases st.getSym idx <;> rfl

theorem pushContCondFact_env (st : ContSymState) (c : Arg K .bool) (taken : Bool) :
    (st.pushCondFact c taken).env = st.env := by
  dsimp only [ContSymState.pushCondFact]
  cases taken
  · rfl
  · cases c with
    | imm _ => rfl
    | var idx => simp only [↓reduceIte]; cases st.getSym idx <;> rfl

theorem evalContOp_len (st : ContSymState) {ts : List Ty} (op : Op K ts) :
    (evalContOp st op).length = ts.length := by
  rcases op with ⟨code, args⟩
  cases code <;> dsimp only [evalContOp, evalContOpCode]
  all_goals try (simp; done)
  all_goals try cases ‹CmpOp›
  all_goals try cases ‹Ty›
  all_goals try (simp; done)
  all_goals
    first
    | (rcases args with ⟨a, ⟨⟩⟩; simp only [List.length_cons, List.length_nil];
       repeat (first | rfl | split))
    | (rcases args with ⟨a, b, ⟨⟩⟩; simp only [List.length_cons, List.length_nil];
       repeat (first | rfl | split))
    | (rcases args with ⟨c, t, e, ⟨⟩⟩; simp only [List.length_cons, List.length_nil];
       try cases c
       repeat (first | rfl | split))

theorem spSlotOf?_sound :
    ∀ (nSlots : Nat) (sv : ContSymVal) (k : Nat),
      spSlotOf? nSlots sv = some k →
      k < nSlots ∧ sv = .spOffset (0#64 - BitVec.ofNat 64 (8 * (k + 1))) := by
  intro nSlots sv k h
  dsimp only [spSlotOf?] at h
  have hmem := List.mem_of_find?_eq_some h
  have hpred := List.find?_some h
  rw [List.mem_range] at hmem
  exact ⟨hmem, beq_iff_eq.1 hpred⟩

theorem isStaticOutsideFrame_disjoint {nSlots : Nat} {t : Ty} {sv : ContSymVal}
    (h : isStaticOutsideFrame nSlots t.bytes sv = true)
    {bvs : List ((t' : Ty) × Val t')} {sp₀ rp₀ a' : BitVec 64}
    (hm : ContSymValMatch bvs sp₀ rp₀ sv i64 a') :
    ∀ k i j, k < nSlots → i < 8 → j < t.bytes →
      a' + BitVec.ofNat 64 j ≠ slotAddr sp₀ k + BitVec.ofNat 64 i := by
  cases sv with
  | spOffset o =>
      dsimp only [isStaticOutsideFrame] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have ha : a' = sp₀ + o := by simpa using hm rfl
      subst ha
      intro k i j hk hi hj
      exact disjoint_frame_of_static sp₀ o h.1.1 h.1.2 h.2 hk hj hi
  | rpOffset _ | const _ | alignedConst _ | taggedAligned _ _ | shl3 _ | stride _ _
  | ite _ _ _ | boolConst _ | cmpUlt _ _ | top =>
      cases h

/-! ### `EnvMapOk` & `SlotsLvlsOk` for `remapArg` / `remapArgs` / `remapRegsExpr` -/

@[expose] def EnvMapOk (bvsConc bvsTflat : List ((t : Ty) × Val t))
    (Γ : List Ty) (d : Nat) (em : List Nat) : Prop :=
  bvsTflat.length = d ∧ bvsConc.map Sigma.fst = Γ ∧ em.length = bvsConc.length ∧
  ∀ idx < bvsConc.length, ∃ tl < d, listGet? em idx = some tl ∧
    ∀ t, lookupV bvsConc t idx = lookupV bvsTflat t (d - 1 - tl)

@[expose] def SlotsLvlsOk (bvsTflat : List ((t : Ty) × Val t)) (d : Nat)
    (sLvls : List Nat) (slots : List (BitVec 64)) : Prop :=
  bvsTflat.length = d ∧ sLvls.length = slots.length ∧
  ∀ k < slots.length, ∃ sl < d, listGet? sLvls k = some sl ∧
    ∀ v, slots[k]? = some v → cLevelVal (t := i64) bvsTflat sl = some v

theorem cLevelVal_lookupV_tflat {bvsTflat : List ((t : Ty) × Val t)} {d tl : Nat}
    (hlen : bvsTflat.length = d) (hlt : tl < d) {t : Ty} :
    lookupV bvsTflat t (d - 1 - tl) = cLevelVal bvsTflat tl := by
  dsimp only [cLevelVal]
  rw [hlen, ite_eq_left hlt]

private theorem ctxTypes_len' {α : Type} {f : α → Type}
    {Γ : List α} {bvs : List ((a : α) × f a)} (h : bvs.map Sigma.fst = Γ) :
    Γ.length = bvs.length := by
  rw [← h, List.length_map]

private theorem listGet?_set_ne {α : Type} :
    ∀ (l : List α) (i j : Nat) (v : α), i ≠ j → listGet? (l.set i v) j = listGet? l j
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, hne => absurd rfl hne
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: xs, i + 1, j + 1, v, hne =>
      listGet?_set_ne xs i j v (fun h => hne (congrArg Nat.succ h))

private theorem listGet?_set_eq {α : Type} :
    ∀ (l : List α) (i : Nat) (v : α), i < l.length → listGet? (l.set i v) i = some v
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => rfl
  | _ :: xs, i + 1, v, hi => listGet?_set_eq xs i v (Nat.lt_of_succ_lt_succ hi)

theorem envMapOk_ext {bvsConc bvsTflat : List ((t : Ty) × Val t)}
    {Γ : List Ty} {d : Nat} {em : List Nat}
    (extra : List ((t : Ty) × Val t))
    (h : EnvMapOk bvsConc bvsTflat Γ d em) :
    EnvMapOk bvsConc (extra ++ bvsTflat) Γ (d + extra.length) em := by
  rcases h with ⟨hbt, hctx, heLen, hIdx⟩
  refine ⟨by rw [List.length_append, hbt, Nat.add_comm], hctx, heLen, fun idx hi => ?_⟩
  obtain ⟨tl, hlt, hget, hlook⟩ := hIdx idx hi
  refine ⟨tl, Nat.lt_of_lt_of_le hlt (Nat.le_add_right d extra.length), hget, fun t => ?_⟩
  rw [hlook t]
  dsimp only [lookupV]
  rw [show d + extra.length - 1 - tl = extra.length + (d - 1 - tl) by omega,
      listGet?_append_skip]

theorem envMapOk_cons {bvsConc bvsTflat : List ((t : Ty) × Val t)}
    {Γ : List Ty} {d : Nat} {em : List Nat} {t : Ty} (v : Val t)
    (h : EnvMapOk bvsConc bvsTflat Γ d em) :
    EnvMapOk (⟨t, v⟩ :: bvsConc) (⟨t, v⟩ :: bvsTflat) (t :: Γ) (d + 1) (d :: em) := by
  rcases h with ⟨hbt, hctx, heLen, hIdx⟩
  refine ⟨by simp [hbt], congrArg (t :: ·) hctx, by simp [heLen], fun idx hi => ?_⟩
  cases idx with
  | zero =>
      refine ⟨d, Nat.lt_succ_self d, rfl, fun t' => ?_⟩
      rw [Nat.add_sub_cancel, Nat.sub_self]; rfl
  | succ k =>
      obtain ⟨tl, hlt, hget, hlook⟩ := hIdx k (Nat.lt_of_succ_lt_succ hi)
      refine ⟨tl, Nat.lt_succ_of_lt hlt, hget, fun t' => ?_⟩
      dsimp only [lookupV, listGet?] at hlook ⊢
      rw [hlook t']
      have hsucc : d + 1 - 1 - tl = (d - 1 - tl) + 1 := by omega
      rw [hsucc]; rfl

theorem envMapOk_push {bvsConc bvsTflat : List ((t : Ty) × Val t)}
    {Γ : List Ty} {d : Nat} {em : List Nat} :
    ∀ {ts : List Ty} (xs : Tup Val ts),
      EnvMapOk bvsConc bvsTflat Γ d em →
      EnvMapOk (pushTup xs bvsConc) (pushTup xs bvsTflat) (pushTypes ts Γ)
        (d + ts.length) (pushEnvMap ts d em)
  | [], (), h => h
  | _ :: ts, (x, xs), h => by
      have h1 := envMapOk_push xs (envMapOk_cons x h)
      rw [Nat.add_assoc, Nat.add_comm 1 ts.length] at h1
      exact h1

theorem slotsLvlsOk_ext (extra : List ((t : Ty) × Val t))
    {bvsTflat : List ((t : Ty) × Val t)} {d : Nat} {sLvls : List Nat} {slots : List (BitVec 64)}
    (h : SlotsLvlsOk bvsTflat d sLvls slots) :
    SlotsLvlsOk (extra ++ bvsTflat) (d + extra.length) sLvls slots := by
  rcases h with ⟨hlen, hsLen, hIdx⟩
  refine ⟨by rw [List.length_append, hlen, Nat.add_comm], hsLen, fun k hk => ?_⟩
  obtain ⟨sl, hsl, hg, hcv⟩ := hIdx k hk
  exact ⟨sl, Nat.lt_of_lt_of_le hsl (Nat.le_add_right d extra.length), hg,
    fun v hv => cLevelVal_prepend extra bvsTflat (hcv v hv)⟩

theorem slotsLvlsOk_set {bvsTflat : List ((t : Ty) × Val t)} {d : Nat}
    {sLvls : List Nat} {slots : List (BitVec 64)}
    (h : SlotsLvlsOk bvsTflat d sLvls slots)
    {k : Nat} (hk : k < slots.length) {vLvl : Nat} (hvlt : vLvl < d) (v : BitVec 64)
    (hcv : cLevelVal (t := i64) bvsTflat vLvl = some v) :
    SlotsLvlsOk bvsTflat d (sLvls.set k vLvl) (slots.set k v) := by
  rcases h with ⟨hlen, hsLen, hIdx⟩
  refine ⟨hlen, by simp [hsLen], fun j hj => ?_⟩
  rw [List.length_set] at hj
  by_cases hEq : k = j
  · subst hEq
    refine ⟨vLvl, hvlt, listGet?_set_eq sLvls k vLvl (by omega), fun w hw => ?_⟩
    rw [List.getElem?_set_self (by omega)] at hw; cases hw; exact hcv
  · obtain ⟨sl, hsl, hg, hcv0⟩ := hIdx j hj
    refine ⟨sl, hsl, by rw [listGet?_set_ne sLvls k j vLvl hEq]; exact hg, fun w hw => ?_⟩
    rw [List.getElem?_set_ne (by omega)] at hw
    exact hcv0 w hw

private theorem checkArg_idx_lt' {Γ : List Ty} {t : Ty} {i : Nat}
    (hchk : checkArg Γ t (.var i) = true) : i < Γ.length := by
  apply listGet?_isSome_lt Γ
  dsimp only [checkArg] at hchk
  cases hg : listGet? Γ i with
  | none => rw [hg] at hchk; cases hchk
  | some _ => rfl

theorem denoteArg_remap {bvsConc bvsTflat vsTail : List ((t : Ty) × Val t)}
    {Γ : List Ty} {d : Nat} {em : List Nat}
    (hem : EnvMapOk bvsConc bvsTflat Γ d em)
    {t : Ty} {a : Arg K t} (hchk : checkArg Γ t a = true) :
    denoteArg (bvsTflat ++ vsTail) (remapArg d em a) = denoteArg bvsConc a := by
  cases a with
  | imm _ => rfl
  | var idx =>
      have hi : (idx : Nat) < Γ.length := checkArg_idx_lt' hchk
      have hc : Γ.length = bvsConc.length := ctxTypes_len' hem.2.1
      have hltConc : (idx : Nat) < bvsConc.length := Nat.lt_of_lt_of_eq hi hc
      obtain ⟨tl, hlt, hget, hlook⟩ := hem.2.2.2 idx hltConc
      dsimp only [remapArg]
      rw [hget]
      dsimp only [denoteArg]
      rw [hlook t]
      dsimp only [lookupV]
      have hltTf : d - 1 - tl < bvsTflat.length := by rw [hem.1]; omega
      rw [listGet?_append_left bvsTflat vsTail hltTf]

theorem denoteArgs_remap {bvsConc bvsTflat vsTail : List ((t : Ty) × Val t)}
    {Γ : List Ty} {d : Nat} {em : List Nat}
    (hem : EnvMapOk bvsConc bvsTflat Γ d em) :
    {ts : List Ty} → {as : Tup (Arg K) ts} → checkArgs Γ as = true →
    denoteArgs (bvsTflat ++ vsTail) (remapArgs d em as) = denoteArgs bvsConc as
  | [], (), _ => rfl
  | _ :: _, (_, _), hchk => by
      dsimp only [checkArgs] at hchk; simp only [Bool.and_eq_true] at hchk
      dsimp only [remapArgs, denoteArgs]
      rw [denoteArg_remap hem hchk.1, denoteArgs_remap hem hchk.2]

theorem denoteRegsExpr_remap {bvsConc bvsTflat vsTail : List ((t : Ty) × Val t)}
    {Γ : List Ty} {d : Nat} {em : List Nat}
    (hem : EnvMapOk bvsConc bvsTflat Γ d em)
    {e : RegsExpr K} (hchk : checkRegsExpr Γ e = true) :
    denoteRegsExpr (bvsTflat ++ vsTail) (remapRegsExpr d em e) = denoteRegsExpr bvsConc e := by
  dsimp only [checkRegsExpr] at hchk; simp only [Bool.and_eq_true] at hchk
  dsimp only [remapRegsExpr, denoteRegsExpr]
  rw [denoteArg_remap hem hchk.1.1.1.1.1,
      denoteArg_remap hem hchk.1.1.1.1.2,
      denoteArg_remap hem hchk.1.1.1.2,
      denoteArg_remap hem hchk.1.1.2,
      denoteArg_remap hem hchk.1.2,
      denoteArg_remap hem hchk.2]

/-! ## §3. Entry Load, Frame Flush, Alias Guard, Tail, Edge, and Block `wp` Soundness -/

/-- Boundary continuation invariant for `nSlots` regions: `ContLsMatch`. -/
@[expose] def ContLsMatch (nSlots : Nat) (pcs : List (BitVec 64))
    (ls : List ((ts : List Ty) × Cont ts)) (Pred : CodeSpec) : Prop :=
  ∀ pc idx, findLabelIdx pcs pc = some idx →
    ∃ J, lookupL ls (contSig nSlots) idx = some J ∧
      ∀ r : Regs, ∀ sp₀ : BitVec 64, ∀ slots : List (BitVec 64),
      ∀ mConc mPub : Mem 64,
        (nSlots > 0 → r.sp = sp₀) →
        FrameRel nSlots sp₀ slots mConc mPub →
        Pred pc ⟨r, mConc⟩ →
        J (packContTup nSlots r sp₀ slots) mPub

theorem contLsMatch_nil (nSlots : Nat) (Pred : CodeSpec) : ContLsMatch nSlots [] [] Pred :=
  fun _ _ h => by cases h

private theorem castListTy_self_cont (ts : List Ty) (l : Cont ts) :
    castListTy ts ts l = some l := by
  dsimp only [castListTy]
  cases h : listTyDecEq ts ts with
  | isFalse hne => exact absurd rfl hne
  | isTrue heq => have h' : heq = rfl := rfl; rw [h']

theorem contLsMatch_cons (nSlots : Nat) {pc : BitVec 64} {J : Cont (contSig nSlots)}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)} {Pred : CodeSpec}
    (hJ : ∀ r : Regs, ∀ sp₀ : BitVec 64, ∀ slots : List (BitVec 64),
      ∀ mConc mPub : Mem 64, (nSlots > 0 → r.sp = sp₀) →
      FrameRel nSlots sp₀ slots mConc mPub → Pred pc ⟨r, mConc⟩ →
      J (packContTup nSlots r sp₀ slots) mPub)
    (hls : ContLsMatch nSlots pcs ls Pred) :
    ContLsMatch nSlots (pc :: pcs) (⟨contSig nSlots, J⟩ :: ls) Pred := by
  intro tgt idx hf
  dsimp only [findLabelIdx] at hf
  by_cases heq : pc = tgt
  · subst heq
    simp only [beq_self_eq_true, ↓reduceIte] at hf
    cases hf
    refine ⟨J, ?_, hJ⟩
    dsimp only [lookupL, listGet?]
    exact castListTy_self_cont (contSig nSlots) J
  · simp only [beq_false_of_ne heq, Bool.false_eq_true, ↓reduceIte] at hf
    cases hf' : findLabelIdx pcs tgt with
    | none => rw [hf'] at hf; cases hf
    | some idx' => rw [hf'] at hf; cases hf; exact hls tgt idx' hf'

private theorem denoteArgs_append_val {vs : List ((t : Ty) × Val t)} :
    {as bs : List Ty} → {xs : Tup (Arg K) as} → {ys : Tup (Arg K) bs} →
    {xs' : Tup (Arg Val) as} → {ys' : Tup (Arg Val) bs} →
    denoteArgs vs xs = some xs' → denoteArgs vs ys = some ys' →
    denoteArgs vs (tupAppend xs ys) = some (tupAppend xs' ys') ∧
      vals (tupAppend xs' ys') = tupAppend (vals xs') (vals ys')
  | [], _, (), _, (), _, _, hy => by simp only [tupAppend, hy, and_self]
  | _ :: _, _, (x, xs), ys, (x', xs'), ys', hx, hy => by
      dsimp only [denoteArgs] at hx
      cases hdx : denoteArg vs x <;> rw [hdx] at hx; · cases hx
      cases hxs : denoteArgs vs xs <;> rw [hxs] at hx; · cases hx
      cases hx
      obtain ⟨hApp, hVals⟩ := denoteArgs_append_val hxs hy
      refine ⟨?_, ?_⟩
      · simp only [tupAppend, denoteArgs, hdx, hApp]
      · simp only [tupAppend, vals, hVals]

private theorem lookupV_append_left {bvs vsTail : List ((t : Ty) × Val t)} {t : Ty} {i : Nat}
    (hi : i < bvs.length) : lookupV (bvs ++ vsTail) t i = lookupV bvs t i := by
  dsimp only [lookupV]; rw [listGet?_append_left bvs vsTail hi]

private theorem denote_mkSlotArgs {bvs vsTail : List ((t : Ty) × Val t)} {d : Nat}
    (hb : bvs.length = d) :
    ∀ (n : Nat) (sLvls : List Nat) (slots : List (BitVec 64)),
      sLvls.length = n → slots.length = n →
      (∀ k < n, ∃ sl < d, listGet? sLvls k = some sl ∧
        ∀ v, slots[k]? = some v → cLevelVal (t := i64) bvs sl = some v) →
      ∃ args', denoteArgs (bvs ++ vsTail) (mkSlotArgs d n sLvls) = some args' ∧
        vals args' = packSlotTup n slots
  | 0, [], [], _, _, _ => ⟨(), rfl, rfl⟩
  | _ + 1, [], _, h1, _, _ => by simp at h1
  | _ + 1, _, [], _, h2, _ => by simp at h2
  | n + 1, l :: ls, v :: vs, h1, h2, hOk => by
      obtain ⟨sl, hsl, hg0, hcv0⟩ := hOk 0 (Nat.zero_lt_succ n)
      cases hg0
      have hv0 := hcv0 v rfl
      have harg : denoteArg (bvs ++ vsTail) (.var (d - 1 - l)) =
          some (@Arg.var Val i64 v) := by
        dsimp only [denoteArg]
        rw [lookupV_append_left (vsTail := vsTail) (by omega), cLevelVal_lookupV_tflat hb hsl, hv0]
      obtain ⟨args', hArgs, hVals⟩ := denote_mkSlotArgs (vsTail := vsTail) hb n ls vs
        (by simp at h1; omega) (by simp at h2; omega) fun k hk => by
          obtain ⟨sl', hsl', hg', hcv'⟩ := hOk (k + 1) (Nat.succ_lt_succ hk)
          exact ⟨sl', hsl', hg', fun w hw => hcv' w hw⟩
      refine ⟨(@Arg.var Val i64 v, args'), ?_, ?_⟩
      · simp only [mkSlotArgs, denoteArgs, harg, hArgs]
      · simp only [vals, packSlotTup, Arg.val, hVals]

theorem denote_mkJumpTuple {bvs vsTail : List ((t : Ty) × Val t)}
    {d sp0Lvl nSlots : Nat} (hb : bvs.length = d)
    {nxt : RegsExpr K} {nxt' : RegsExpr Val}
    (hnxt : denoteRegsExpr (bvs ++ vsTail) nxt = some nxt')
    {sp₀ : BitVec 64}
    (hsp : nSlots > 0 → sp0Lvl < d ∧ cLevelVal (t := i64) bvs sp0Lvl = some sp₀)
    {sLvls : List Nat} {slots : List (BitVec 64)}
    (hs : nSlots > 0 → SlotsLvlsOk bvs d sLvls slots ∧ slots.length = nSlots) :
    ∃ args', denoteArgs (bvs ++ vsTail) (mkJumpTuple d sp0Lvl nxt nSlots sLvls) = some args' ∧
      vals args' = packContTup nSlots nxt'.eval sp₀ slots := by
  have ⟨argsN, hArgsN, hValsN⟩ : ∃ a', denoteArgs (bvs ++ vsTail) nxt.toTup = some a' ∧
      vals a' = nxt'.eval.toRegsV.toTup := by
    dsimp only [denoteRegsExpr] at hnxt
    cases h0 : denoteArg (bvs ++ vsTail) nxt.sp <;> rw [h0] at hnxt; · cases hnxt
    cases h1 : denoteArg (bvs ++ vsTail) nxt.rp <;> rw [h1] at hnxt; · cases hnxt
    cases h2 : denoteArg (bvs ++ vsTail) nxt.rv <;> rw [h2] at hnxt; · cases hnxt
    cases h3 : denoteArg (bvs ++ vsTail) nxt.r1 <;> rw [h3] at hnxt; · cases hnxt
    cases h4 : denoteArg (bvs ++ vsTail) nxt.r2 <;> rw [h4] at hnxt; · cases hnxt
    cases h5 : denoteArg (bvs ++ vsTail) nxt.r3 <;> rw [h5] at hnxt; · cases hnxt
    cases hnxt
    refine ⟨(_, _, _, _, _, _, ()), ?_, rfl⟩
    dsimp only [RegsExpr.toTup, denoteArgs]; rw [h0, h1, h2, h3, h4, h5]
  cases nSlots with
  | zero => exact ⟨argsN, hArgsN, hValsN⟩
  | succ n =>
      obtain ⟨hspLt, hspV⟩ := hsp (Nat.zero_lt_succ n)
      obtain ⟨hsOk, hsLen⟩ := hs (Nat.zero_lt_succ n)
      have hspArg : denoteArg (bvs ++ vsTail) (.var (d - 1 - sp0Lvl)) =
          some (@Arg.var Val i64 sp₀) := by
        dsimp only [denoteArg]
        rw [lookupV_append_left (vsTail := vsTail) (by omega), cLevelVal_lookupV_tflat hb hspLt,
            hspV]
      obtain ⟨argsS, hArgsS, hValsS⟩ := denote_mkSlotArgs (vsTail := vsTail) hb (n + 1) sLvls slots
        (by rw [hsOk.2.1, hsLen]) hsLen (fun k hk => hsOk.2.2 k (by omega))
      have hTail : denoteArgs (bvs ++ vsTail) (ts := List.replicate (n + 2) i64)
          (.var (d - 1 - sp0Lvl), mkSlotArgs d (n + 1) sLvls) =
          some (@Arg.var Val i64 sp₀, argsS) := by
        simp only [denoteArgs, hspArg, hArgsS]
      obtain ⟨hApp, hVals⟩ := denoteArgs_append_val hArgsN hTail
      refine ⟨tupAppend argsN (@Arg.var Val i64 sp₀, argsS), hApp, ?_⟩
      exact hVals.trans (by rw [hValsN]; simp only [vals, Arg.val, hValsS]; rfl)

theorem lowerContJumpTo_wp {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    {nSlots : Nat} {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)}
    {Pred : CodeSpec} (hls : ContLsMatch nSlots pcs ls Pred)
    {bvs vsTail : List ((t : Ty) × Val t)} {d sp0Lvl : Nat} (hb : bvs.length = d)
    {targetPc : BitVec 64} {j : Nat} (hj : findLabelIdx pcs targetPc = some j)
    {nxt : RegsExpr K} {nxt' : RegsExpr Val}
    (hnxt : denoteRegsExpr (bvs ++ vsTail) nxt = some nxt')
    {sp₀ : BitVec 64}
    (hsp : nSlots > 0 → sp0Lvl < d ∧ cLevelVal (t := i64) bvs sp0Lvl = some sp₀)
    {sLvls : List Nat} {slots : List (BitVec 64)}
    (hs : nSlots > 0 → SlotsLvlsOk bvs d sLvls slots ∧ slots.length = nSlots)
    (hnSp : nSlots > 0 → nxt'.eval.sp = sp₀)
    {mConc mPub : Mem 64} (hfr : FrameRel nSlots sp₀ slots mConc mPub)
    (hP : Pred targetPc ⟨nxt'.eval, mConc⟩) :
    wp Γ Q X (denote Val Cont (lowerContJumpTo nSlots pcs targetPc
      (mkJumpTuple d sp0Lvl nxt nSlots sLvls)) (bvs ++ vsTail) ls) mPub := by
  dsimp only [lowerContJumpTo]; rw [hj]
  obtain ⟨args', hargs', hvals⟩ := denote_mkJumpTuple hb hnxt hsp hs
  obtain ⟨J, hJ, hJP⟩ := hls targetPc j hj
  dsimp only [denote]; rw [hJ, hargs']; dsimp only [wp]; rw [hvals]
  exact hJP nxt'.eval sp₀ slots mConc mPub hnSp hfr hP

private theorem flushFrameAux_wp {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    (sp0Lvl : Nat) (sp₀ : BitVec 64) {vsTail : List ((t : Ty) × Val t)}
    {ls : List ((ts : List Ty) × Cont ts)} {kCont : TFlat rs} :
    ∀ (k : Nat) (sLvls : List Nat) (slotsTail : List (BitVec 64))
      (bvs : List ((t : Ty) × Val t)) (d : Nat) (m : Mem 64),
      bvs.length = d →
      sp0Lvl < d → cLevelVal (t := i64) bvs sp0Lvl = some sp₀ →
      sLvls.length = slotsTail.length →
      (∀ j < slotsTail.length, ∃ sl < d, listGet? sLvls j = some sl ∧
        ∀ v, slotsTail[j]? = some v → cLevelVal (t := i64) bvs sl = some v) →
      (∀ j < slotsTail.length, storeOk m i64 (slotAddr sp₀ (k + j))) →
      (∀ extra : List ((t : Ty) × Val t), extra.length = sLvls.length →
        wp Γ Q X (denote Val Cont kCont ((extra ++ bvs) ++ vsTail) ls)
          (writeSlots m sp₀ k slotsTail)) →
      wp Γ Q X (denote Val Cont (flushFrameAux sp0Lvl k sLvls d kCont) (bvs ++ vsTail) ls) m
  | _, [], [], bvs, _, m, _, _, _, _, _, _, hK => by
      simpa [flushFrameAux, writeSlots] using hK [] rfl
  | _, _ :: _, [], _, _, _, _, _, _, h1, _, _, _ => by simp at h1
  | _, [], _ :: _, _, _, _, _, _, _, h1, _, _, _ => by simp at h1
  | k, sLvl :: rest, v :: vs, bvs, d, m, hbd, hspLt, hspV, hsLen, hOk, hMem, hK => by
      have hspArg : denoteArg (bvs ++ vsTail) (.var (d - 1 - sp0Lvl)) =
          some (@Arg.var Val i64 sp₀) := by
        dsimp only [denoteArg]
        rw [lookupV_append_left (vsTail := vsTail) (by omega), cLevelVal_lookupV_tflat hbd hspLt,
            hspV]
      have himm : denoteArg (bvs ++ vsTail) (@Arg.imm K i64 (BitVec.ofNat 64 (8 * (k + 1)))) =
          some (@Arg.imm Val i64 (BitVec.ofNat 64 (8 * (k + 1)))) := rfl
      dsimp only [flushFrameAux, denote, op2, denoteArgs]
      rw [hspArg, himm]
      dsimp only [wp, Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat, pushTup, Arg.val]
      rw [ite_eq_right Bool.false_ne_true]
      let addr := sp₀ - BitVec.ofNat 64 (8 * (k + 1))
      let bvs1 := ⟨i64, addr⟩ :: bvs
      obtain ⟨sl0, hsl0Lt, hg0, hcv0⟩ := hOk 0 (Nat.zero_lt_succ _)
      cases hg0
      have hv0 := hcv0 v rfl
      have hbvs1Len : bvs1.length = d + 1 := by simp [bvs1, hbd]
      have hsArg : denoteArg (bvs1 ++ vsTail) (.var (d + 1 - 1 - sLvl)) =
          some (@Arg.var Val i64 v) := by
        dsimp only [denoteArg]
        rw [lookupV_append_left (vsTail := vsTail) (by omega),
            cLevelVal_lookupV_tflat hbvs1Len (Nat.lt_succ_of_lt hsl0Lt)]
        have hcv' : cLevelVal (t := i64) bvs1 sLvl = some v :=
          cLevelVal_prepend [⟨i64, addr⟩] bvs hv0
        rw [hcv']
      have haArg : denoteArg (bvs1 ++ vsTail) (.var 0) = some (@Arg.var Val i64 addr) := rfl
      rw [show (⟨i64, sp₀ - BitVec.ofNat 64 (8 * (k + 1))⟩ :: (bvs ++ vsTail) :
          List ((t : Ty) × Val t)) = bvs1 ++ vsTail from rfl]
      rw [hsArg, haArg]
      dsimp only [wp, Arg.val]
      have hok0 : storeOk m i64 addr := by
        simpa [addr, slotAddr, Nat.add_zero] using hMem 0 (Nat.zero_lt_succ _)
      refine ⟨hok0, ?_⟩
      apply flushFrameAux_wp sp0Lvl sp₀ (k + 1) rest vs bvs1 (d + 1)
        (storeMem m i64 addr v) (by simp [bvs1, hbd]) (Nat.lt_succ_of_lt hspLt)
        (cLevelVal_prepend [⟨i64, addr⟩] bvs hspV) (by simp at hsLen; omega)
        (fun j hj => by
          obtain ⟨sl', hsl', hg', hcv'⟩ := hOk (j + 1) (Nat.succ_lt_succ hj)
          exact ⟨sl', Nat.lt_succ_of_lt hsl', hg', fun w hw =>
            cLevelVal_prepend [⟨i64, addr⟩] bvs (hcv' w hw)⟩)
        (fun j hj => by
          have hst := hMem (j + 1) (Nat.succ_lt_succ hj)
          rw [show k + (j + 1) = (k + 1) + j by omega] at hst
          exact storeOk_storeMem m i64 i64 addr (slotAddr sp₀ ((k + 1) + j)) v hst)
        (fun extra hex => by
          have hex' := hK (extra ++ [⟨i64, addr⟩]) (by simp [hex])
          simpa [bvs1, List.append_assoc, writeSlots, slotAddr, addr] using hex')

theorem flushFrame_wp {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    {nSlots sp0Lvl d : Nat} {sp₀ : BitVec 64} {sLvls : List Nat} {slots : List (BitVec 64)}
    {bvs vsTail : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {kCont : Nat → TFlat rs} {mConc mPub : Mem 64}
    (hb : bvs.length = d) (hfr : FrameRel nSlots sp₀ slots mConc mPub)
    (hsp : nSlots > 0 → sp0Lvl < d ∧ cLevelVal (t := i64) bvs sp0Lvl = some sp₀)
    (hs : nSlots > 0 → SlotsLvlsOk bvs d sLvls slots ∧ slots.length = nSlots)
    (hz : nSlots = 0 → sLvls = [])
    (hK : ∀ extra : List ((t : Ty) × Val t), extra.length = sLvls.length →
      wp Γ Q X (denote Val Cont (kCont (d + sLvls.length)) ((extra ++ bvs) ++ vsTail) ls) mConc) :
    wp Γ Q X (denote Val Cont (flushFrame sp0Lvl sLvls d kCont) (bvs ++ vsTail) ls) mPub := by
  by_cases hn : nSlots = 0
  · subst hn
    have hsl : sLvls = [] := hz rfl; subst hsl
    have hmeq := frameRel_zero hfr; subst hmeq
    simpa [flushFrame, flushFrameAux] using hK [] rfl
  · have hPos : nSlots > 0 := Nat.pos_of_ne_zero hn
    obtain ⟨hspLt, hspV⟩ := hsp hPos
    obtain ⟨hsOk, hsLen⟩ := hs hPos
    have hfr' := hfr
    dsimp only [FrameRel] at hfr'; rw [ite_eq_right hn] at hfr'
    rcases hfr' with ⟨_, _, hMem, rfl⟩
    dsimp only [flushFrame]
    exact flushFrameAux_wp sp0Lvl sp₀ 0 sLvls slots bvs d mPub hb hspLt hspV
      (by rw [hsOk.2.1]) (fun j hj => hsOk.2.2 j hj)
      (fun j hj => by simpa [Nat.zero_add] using hMem j (by omega)) hK

private theorem contDenoteArg_shift (extra vs : List ((t : Ty) × Val t)) {t : Ty} (a : Arg K t) :
    denoteArg (extra ++ vs) (shiftArg extra.length a) = denoteArg vs a := by
  cases a with
  | imm _ => rfl
  | var i => dsimp only [shiftArg, denoteArg, lookupV]; rw [Nat.add_comm i _, listGet?_append_skip]

private theorem contDenoteRegsExpr_shift (extra vs : List ((t : Ty) × Val t)) (r : RegsExpr K) :
    denoteRegsExpr (extra ++ vs) (shiftRegsExpr extra.length r) = denoteRegsExpr vs r := by
  dsimp only [shiftRegsExpr, denoteRegsExpr]
  rw [contDenoteArg_shift, contDenoteArg_shift, contDenoteArg_shift,
      contDenoteArg_shift, contDenoteArg_shift, contDenoteArg_shift]

theorem emitAliasGuard_wp {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    {sp0Lvl nSlots d bytes : Nat} {sp₀ : BitVec 64} {aT : Arg K i64} {a' : Arg Val i64}
    {bvs vsTail : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {tArm fArm : TFlat rs} {m : Mem 64}
    (hb : bvs.length = d) (hspLt : sp0Lvl < d)
    (hspV : cLevelVal (t := i64) bvs sp0Lvl = some sp₀)
    (ha : denoteArg (bvs ++ vsTail) aT = some a')
    (hn : nSlots ≤ 64) (hbytes : bytes ≤ 16)
    (hT : ∀ extra : List ((t : Ty) × Val t), extra.length = 5 →
      (∀ k i j, k < nSlots → i < 8 → j < bytes →
        a'.val + BitVec.ofNat 64 j ≠ slotAddr sp₀ k + BitVec.ofNat 64 i) →
      wp Γ Q X (denote Val Cont tArm ((extra ++ bvs) ++ vsTail) ls) m)
    (hF : ∀ extra : List ((t : Ty) × Val t), extra.length = 5 →
      wp Γ Q X (denote Val Cont fArm ((extra ++ bvs) ++ vsTail) ls) m) :
    wp Γ Q X (denote Val Cont (emitAliasGuard sp0Lvl nSlots d aT bytes tArm fArm)
      (bvs ++ vsTail) ls) m := by
  have hspArg : denoteArg (bvs ++ vsTail) (.var (d - 1 - sp0Lvl)) =
      some (@Arg.var Val i64 sp₀) := by
    dsimp only [denoteArg]
    rw [lookupV_append_left (vsTail := vsTail) (by omega), cLevelVal_lookupV_tflat hb hspLt, hspV]
  have himm0 : denoteArg (bvs ++ vsTail) (@Arg.imm K i64 (BitVec.ofNat 64 (8 * nSlots))) =
      some (@Arg.imm Val i64 (BitVec.ofNat 64 (8 * nSlots))) := rfl
  dsimp only [emitAliasGuard, denote, op2, denoteArgs]
  rw [hspArg, himm0]
  dsimp only [wp, Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat, pushTup, Arg.val]
  rw [ite_eq_right Bool.false_ne_true]
  let lo := sp₀ - BitVec.ofNat 64 (8 * nSlots)
  have ha1 : denoteArg (⟨i64, lo⟩ :: (bvs ++ vsTail)) (shiftArg 1 aT) = some a' :=
    (contDenoteArg_shift [⟨i64, lo⟩] (bvs ++ vsTail) aT).trans ha
  have hv0 : denoteArg (⟨i64, lo⟩ :: (bvs ++ vsTail)) (.var 0) =
      some (@Arg.var Val i64 lo) := rfl
  rw [ha1, hv0]
  dsimp only [wp, Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat, Arg.val, pushTup]
  rw [ite_eq_right Bool.false_ne_true]
  let dist := a'.val - lo
  dsimp only [denoteArg, wp, Op.wp, OpCode.wp, vals, liftCmp, CmpOp.evalBits, Ty.hasFloat,
    pushTup, Arg.val]
  let c1 := BitVec.ule (BitVec.ofNat 64 (8 * nSlots)) dist
  let c2 := BitVec.ule dist (BitVec.ofNat 64 (2 ^ 64 - bytes))
  let ok := c1 && c2
  constructor
  · intro hOk
    have ⟨hc1, hc2⟩ := Bool.and_eq_true_iff.1 hOk
    apply hT [⟨.bool, ok⟩, ⟨.bool, c2⟩, ⟨.bool, c1⟩, ⟨i64, dist⟩, ⟨i64, lo⟩] rfl
    intro k i j hk hi hj
    by_cases hb0 : bytes = 0
    · subst hb0; omega
    · have hlo : 8 * nSlots ≤ dist.toNat := by
        have hbv : (BitVec.ofNat 64 (8 * nSlots)).toNat ≤ dist.toNat := by
          dsimp only [c1, BitVec.ule] at hc1
          exact BitVec.le_def.1 (of_decide_eq_true hc1)
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hbv; exact hbv
      have hhi : dist.toNat ≤ 2 ^ 64 - bytes := by
        have hbv : dist.toNat ≤ (BitVec.ofNat 64 (2 ^ 64 - bytes)).toNat := by
          dsimp only [c2, BitVec.ule] at hc2
          exact BitVec.le_def.1 (of_decide_eq_true hc2)
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hbv; exact hbv
      exact disjoint_frame_of_range sp₀ a'.val hn hbytes hlo hhi hk hj hi
  · intro _
    exact hF [⟨.bool, ok⟩, ⟨.bool, c2⟩, ⟨.bool, c1⟩, ⟨i64, dist⟩, ⟨i64, lo⟩] rfl

theorem mkRetEnvelope_wp {Γ : Env} {X : XPost} {Ψ : CodeSpec}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {tgt : Arg K i64} {tgt' : Arg Val i64} (ht : denoteArg vs tgt = some tgt')
    {nxt : RegsExpr K} {nxt' : RegsExpr Val} (hn : denoteRegsExpr vs nxt = some nxt')
    {m : Mem 64} (hP : Ψ tgt'.val ⟨nxt'.eval, m⟩) :
    wp Γ (retEnvQ Ψ) X (denote Val Cont (mkRetEnvelope tgt nxt) vs ls) m := by
  dsimp only [denoteRegsExpr] at hn
  cases h0 : denoteArg vs nxt.sp <;> rw [h0] at hn; · cases hn
  cases h1 : denoteArg vs nxt.rp <;> rw [h1] at hn; · cases hn
  cases h2 : denoteArg vs nxt.rv <;> rw [h2] at hn; · cases hn
  cases h3 : denoteArg vs nxt.r1 <;> rw [h3] at hn; · cases hn
  cases h4 : denoteArg vs nxt.r2 <;> rw [h4] at hn; · cases hn
  cases h5 : denoteArg vs nxt.r3 <;> rw [h5] at hn; · cases hn
  cases hn
  dsimp only [mkRetEnvelope, denote, RegionAbi.retSig, denoteArgs]
  rw [ht, h0, h1, h2, h3, h4, h5]
  exact hP

theorem lowerUnpromotedTail_wp {cm : CodeMap} {Γ : Env} {Ψ : CodeSpec} {H : HaltPost} :
    ∀ (b : BlockFlat) {gCtx : List Ty} {bvsConc bvsTflat vsTail : List ((t : Ty) × Val t)}
      {ls : List ((ts : List Ty) × Cont ts)} {d : Nat} {em : List Nat} {m : Mem 64},
      EnvMapOk bvsConc bvsTflat gCtx d em →
      b.wfCheck gCtx = true →
      b.noHlt = true →
      b.wp cm.symEnv Ψ H bvsConc m →
      wp Γ (retEnvQ Ψ) (haltXPost H)
        (denote Val Cont (lowerUnpromotedTail cm b d em) (bvsTflat ++ vsTail) ls) m
  | .let_ (ts := ts) op k, gCtx, bvsConc, bvsTflat, vsTail, ls, d, em, m, hem, hwf, hno, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfA, hwfK⟩
      dsimp only [BlockFlat.noHlt] at hno
      dsimp only [BlockFlat.wp] at hbp
      cases hda : denoteArgs bvsConc op.args with
      | none => rw [hda] at hbp; exact False.elim hbp
      | some args' =>
          rw [hda] at hbp
          dsimp only [lowerUnpromotedTail, denote]
          rw [denoteArgs_remap hem hwfA, hda]
          dsimp only [wp]
          exact Op.wp_mono (fun r hr => by
            rw [pushTup_append]
            exact lowerUnpromotedTail_wp k (vsTail := vsTail) (ls := ls)
              (envMapOk_push r hem) hwfK hno hr) hbp
  | .load t a k, gCtx, bvsConc, bvsTflat, vsTail, ls, d, em, m, hem, hwf, hno, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfA, hwfK⟩
      dsimp only [BlockFlat.noHlt] at hno
      dsimp only [BlockFlat.wp] at hbp
      cases hda : denoteArg bvsConc a with
      | none => rw [hda] at hbp; exact False.elim hbp
      | some a' =>
          rw [hda] at hbp
          rcases hbp with ⟨v, hv, hkv⟩
          dsimp only [lowerUnpromotedTail, denote]
          rw [denoteArg_remap hem hwfA, hda]
          exact ⟨v, hv, lowerUnpromotedTail_wp k (envMapOk_cons v hem) hwfK hno hkv⟩
  | .store v a k, gCtx, bvsConc, bvsTflat, vsTail, ls, d, em, m, hem, hwf, hno, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfVA, hwfK⟩
      rcases Bool.and_eq_true_iff.1 hwfVA with ⟨hwfV, hwfA⟩
      dsimp only [BlockFlat.noHlt] at hno
      dsimp only [BlockFlat.wp] at hbp
      cases hdv : denoteArg bvsConc v <;> rw [hdv] at hbp; · exact False.elim hbp
      cases hda : denoteArg bvsConc a <;> rw [hda] at hbp; · exact False.elim hbp
      rcases hbp with ⟨hok, hk⟩
      dsimp only [lowerUnpromotedTail, denote]
      rw [denoteArg_remap hem hwfV, hdv, denoteArg_remap hem hwfA, hda]
      exact ⟨hok, lowerUnpromotedTail_wp k hem hwfK hno hk⟩
  | .codeAddr sym k, gCtx, bvsConc, bvsTflat, vsTail, ls, d, em, m, hem, hwf, hno, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      dsimp only [BlockFlat.noHlt] at hno
      rcases hbp with ⟨a, ha, hk⟩
      have had : cm.addrOf? sym = some a := ha
      dsimp only [lowerUnpromotedTail]; rw [had]
      dsimp only [denote, op1, denoteArgs, denoteArg, wp, Op.wp, OpCode.wp, vals]
      exact lowerUnpromotedTail_wp k (envMapOk_cons a hem) hwf hno hk
  | .jnz c t e, gCtx, bvsConc, bvsTflat, vsTail, ls, d, em, m, hem, hwf, hno, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfCT, hwfE⟩
      rcases Bool.and_eq_true_iff.1 hwfCT with ⟨hwfC, hwfT⟩
      dsimp only [BlockFlat.noHlt] at hno
      rcases Bool.and_eq_true_iff.1 hno with ⟨hnoT, hnoE⟩
      dsimp only [BlockFlat.wp] at hbp
      cases hdc : denoteArg bvsConc c <;> rw [hdc] at hbp; · exact False.elim hbp
      rcases hbp with ⟨hbt, hbe⟩
      dsimp only [lowerUnpromotedTail, denote]
      rw [denoteArg_remap hem hwfC, hdc]
      exact ⟨fun htr => lowerUnpromotedTail_wp t hem hwfT hnoT (hbt htr),
             fun hfl => lowerUnpromotedTail_wp e hem hwfE hnoE (hbe hfl)⟩
  | .ijmp tgt nxt, gCtx, bvsConc, bvsTflat, vsTail, ls, d, em, m, hem, hwf, _, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfT, hwfN⟩
      dsimp only [BlockFlat.wp] at hbp
      cases hdt : denoteArg bvsConc tgt <;> rw [hdt] at hbp; · exact False.elim hbp
      cases hdn : denoteRegsExpr bvsConc nxt <;> rw [hdn] at hbp; · exact False.elim hbp
      dsimp only [lowerUnpromotedTail]
      exact mkRetEnvelope_wp (by rw [denoteArg_remap hem hwfT, hdt])
        (by rw [denoteRegsExpr_remap hem hwfN, hdn]) hbp
  | .halt c, gCtx, bvsConc, bvsTflat, vsTail, ls, d, em, m, hem, hwf, _, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      dsimp only [BlockFlat.wp] at hbp
      cases hdc : denoteArg bvsConc c <;> rw [hdc] at hbp; · exact False.elim hbp
      dsimp only [lowerUnpromotedTail, denote, denoteArgs]
      rw [denoteArg_remap hem hwf, hdc]
      dsimp only [denoteArgs, wp, vals, haltXPost]
      exact ⟨rfl, ⟨rfl, hbp⟩⟩
  | .hlt, _, _, _, _, _, _, _, _, _, _, hno, _ => by
      dsimp only [BlockFlat.noHlt] at hno; cases hno

theorem cLevelVal_of_envMap {bvsConc bvsTflat : List ((t : Ty) × Val t)}
    {gCtx : List Ty} {d : Nat} {em : List Nat}
    (hem : EnvMapOk bvsConc bvsTflat gCtx d em)
    {st : ContSymState} {sp₀ rp₀ : BitVec 64} (hst : ContSymStateOk bvsConc sp₀ rp₀ st)
    {t : Ty} {lvl : Nat} {x : Val t} (hl : cLevelVal bvsConc lvl = some x) :
    lvl < st.env.length ∧
      ∃ tl < d, listGet? em (st.env.length - 1 - lvl) = some tl ∧
        cLevelVal bvsTflat tl = some x := by
  have hlt : lvl < bvsConc.length := cLevelVal_lt_len hl
  have hltS : lvl < st.env.length := by rwa [hst.lenEq]
  have hidxLt : st.env.length - 1 - lvl < bvsConc.length := by
    rw [hst.lenEq]; omega
  obtain ⟨tl, htlLt, hget, hlook⟩ := hem.2.2.2 (st.env.length - 1 - lvl) hidxLt
  refine ⟨hltS, tl, htlLt, hget, ?_⟩
  rw [← cLevelVal_lookupV_tflat hem.1 htlLt, ← hlook t]
  dsimp only [cLevelVal] at hl
  rw [ite_eq_left hlt, ← hst.lenEq] at hl
  exact hl

private theorem lookupV_extra_shift' {V : Ty → Type} (extra bvs vsTail : List ((t : Ty) × V t))
    {t : Ty} {i : Nat} {v : V t} (hlt : i < bvs.length) (hl : lookupV bvs t i = some v) :
    lookupV ((extra ++ bvs) ++ vsTail) t (i + extra.length) = some v := by
  rw [List.append_assoc, lookupV, Nat.add_comm i extra.length, listGet?_append_skip,
      listGet?_append_left bvs vsTail hlt]
  exact hl

theorem checkStrideTargets_mem_isSome' {pcs : List (BitVec 64)} {base : BitVec 64} :
    ∀ (k : Nat) (targets : List (BitVec 64)) (i : Nat),
      checkStrideTargets pcs base k targets = true →
      k ≤ i → i < k + targets.length →
      (findLabelIdx pcs (base + BitVec.ofNat 64 (8 * i))).isSome = true
  | _, [], _, _, hlo, hhi => by simp at hhi; omega
  | k, t :: ts, i, hchk, hlo, hhi => by
      dsimp only [checkStrideTargets] at hchk; simp only [Bool.and_eq_true] at hchk
      by_cases hi : i = k
      · subst hi; rw [← of_decide_eq_true hchk.1.1]; exact hchk.1.2
      · exact checkStrideTargets_mem_isSome' (k + 1) ts i hchk.2 (by omega)
          (by simp [List.length_cons] at hhi ⊢; omega)

theorem lowerContStride_wp {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    {nSlots sp0Lvl d : Nat} {pcs : List (BitVec 64)}
    {ls : List ((ts : List Ty) × Cont ts)} {Pred : CodeSpec}
    (hls : ContLsMatch nSlots pcs ls Pred)
    {bvsTflat vsTail : List ((t : Ty) × Val t)} (hb : bvsTflat.length = d)
    {idxVar : Nat} {x : Val i64} (hlook : lookupV bvsTflat i64 idxVar = some x)
    (hltIdx : idxVar < bvsTflat.length)
    {nxt : RegsExpr K} {nxt' : RegsExpr Val}
    (hnxt : denoteRegsExpr (bvsTflat ++ vsTail) nxt = some nxt')
    {sp₀ : BitVec 64}
    (hsp : nSlots > 0 → sp0Lvl < d ∧ cLevelVal (t := i64) bvsTflat sp0Lvl = some sp₀)
    {sLvls : List Nat} {slots : List (BitVec 64)}
    (hs : nSlots > 0 → SlotsLvlsOk bvsTflat d sLvls slots ∧ slots.length = nSlots)
    {base : BitVec 64} (hnSp : nSlots > 0 → nxt'.eval.sp = sp₀)
    {mConc mPub : Mem 64} (hfr : FrameRel nSlots sp₀ slots mConc mPub) :
    ∀ (k : Nat) (extra : List ((t : Ty) × Val t)) (targets : List (BitVec 64)),
      targets ≠ [] → checkStrideTargets pcs base k targets = true →
      k ≤ x.toNat → x.toNat < k + targets.length →
      Pred (base + BitVec.ofNat 64 (8 * x.toNat)) ⟨nxt'.eval, mConc⟩ →
      wp Γ Q X (denote Val Cont (lowerContStride nSlots pcs idxVar
        (mkJumpTuple d sp0Lvl nxt nSlots sLvls) k extra.length targets)
        ((extra ++ bvsTflat) ++ vsTail) ls) mPub := by
  have htup : ∃ args', denoteArgs (bvsTflat ++ vsTail) (mkJumpTuple d sp0Lvl nxt nSlots sLvls) =
      some args' ∧ vals args' = packContTup nSlots nxt'.eval sp₀ slots :=
    denote_mkJumpTuple hb hnxt hsp hs
  rcases htup with ⟨args', hArgs, hVals⟩
  have hShiftArgs : ∀ (extra : List ((t : Ty) × Val t)),
      denoteArgs ((extra ++ bvsTflat) ++ vsTail)
        (shiftArgTup extra.length (mkJumpTuple d sp0Lvl nxt nSlots sLvls)) = some args' := by
    intro extra
    have hGen : ∀ (ts : List Ty) (xs : Tup (Arg K) ts) (xs' : Tup (Arg Val) ts),
        denoteArgs (bvsTflat ++ vsTail) xs = some xs' →
        denoteArgs ((extra ++ bvsTflat) ++ vsTail) (shiftArgTup extra.length xs) = some xs' := by
      intro ts
      induction ts with
      | nil => intro xs xs' hx; cases xs; cases xs'; rfl
      | cons _ _ ih =>
          intro xs xs' hx
          rcases xs with ⟨a, as⟩; rcases xs' with ⟨a', as'⟩
          dsimp only [denoteArgs] at hx
          cases ha : denoteArg (bvsTflat ++ vsTail) a <;> rw [ha] at hx; · cases hx
          cases has : denoteArgs (bvsTflat ++ vsTail) as <;> rw [has] at hx; · cases hx
          cases hx
          dsimp only [shiftArgTup, denoteArgs]
          have haS : denoteArg ((extra ++ bvsTflat) ++ vsTail) (shiftArg extra.length a) =
              some a' := by
            rw [List.append_assoc, contDenoteArg_shift, ha]
          rw [haS, ih as as' has]
    exact hGen _ _ _ hArgs
  intro k extra targets hne hchk hlo hhi hP
  induction targets generalizing k extra with
  | nil => exact absurd rfl hne
  | cons tPc rest ih =>
      cases rest with
      | nil =>
          dsimp only [checkStrideTargets] at hchk
          simp only [Bool.and_eq_true, Bool.and_true] at hchk
          have hx : x.toNat = k := by simp at hhi; omega
          have hlast : tPc = base + BitVec.ofNat 64 (8 * k) := of_decide_eq_true hchk.1
          rcases Option.isSome_iff_exists.1 hchk.2 with ⟨j, hj⟩
          rw [hx, ← hlast] at hP
          dsimp only [lowerContStride, lowerContJumpTo]; rw [hj]
          obtain ⟨J, hJ, hJP⟩ := hls tPc j hj
          dsimp only [denote]; rw [hJ, hShiftArgs extra]; dsimp only [wp]; rw [hVals]
          exact hJP nxt'.eval sp₀ slots mConc mPub hnSp hfr hP
      | cons r0 rs' =>
          dsimp only [checkStrideTargets] at hchk
          rcases Bool.and_eq_true_iff.1 hchk with ⟨h1, hchkRest⟩
          rcases Bool.and_eq_true_iff.1 h1 with ⟨htEqB, hlabB⟩
          have htEq : tPc = base + BitVec.ofNat 64 (8 * k) := beq_iff_eq.1 htEqB
          rcases Option.isSome_iff_exists.1 hlabB with ⟨j, hj⟩
          dsimp only [lowerContStride]
          have hdenV : denoteArg ((extra ++ bvsTflat) ++ vsTail) (.var (idxVar + extra.length)) =
              some (@Arg.var Val i64 x) := by
            dsimp only [denoteArg]
            rw [lookupV_extra_shift' extra bvsTflat vsTail hltIdx hlook]
          dsimp only [denote, op2, denoteArgs]; rw [hdenV]
          dsimp only [denoteArg, wp, Op.wp, OpCode.wp, vals, liftCmp, Ty.hasFloat, Arg.val]
          have hkLt : k < 2 ^ 64 := Nat.lt_of_le_of_lt hlo x.isLt
          constructor
          · intro htr
            dsimp only [CmpOp.evalBits] at htr
            have hxEq : x = BitVec.ofNat 64 k := of_decide_eq_true htr
            have hnat : x.toNat = k := by rw [hxEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkLt]
            rw [hnat, ← htEq] at hP
            dsimp only [lowerContJumpTo]; rw [hj]
            obtain ⟨J, hJ, hJP⟩ := hls tPc j hj
            dsimp only [denote]; rw [hJ]
            have hcons := hShiftArgs (⟨.bool, CmpOp.evalBits .eq x (BitVec.ofNat 64 k)⟩ :: extra)
            simp only [List.length_cons, List.cons_append, List.append_assoc, pushTup] at hcons ⊢
            rw [hcons]
            dsimp only [wp]; rw [hVals]
            exact hJP nxt'.eval sp₀ slots mConc mPub hnSp hfr hP
          · intro hfl
            dsimp only [CmpOp.evalBits] at hfl
            have hne : x ≠ BitVec.ofNat 64 k := fun he => by simp [he] at hfl
            have hnatNe : x.toNat ≠ k := by
              intro he; apply hne; apply BitVec.eq_of_toNat_eq
              rw [he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkLt]
            have ihRes := ih (k + 1)
              (⟨.bool, CmpOp.evalBits .eq x (BitVec.ofNat 64 k)⟩ :: extra) (by simp)
              hchkRest (by omega) (by simp [List.length_cons] at hhi ⊢; omega)
            simpa [pushTup, List.length_cons, List.append_assoc] using ihRes

theorem lowerContGuarded_wp {Γ : Env} {X : XPost} {Ψ_cold Pred : CodeSpec}
    {nSlots sp0Lvl d : Nat} {pcs : List (BitVec 64)}
    {ls : List ((ts : List Ty) × Cont ts)} (hls : ContLsMatch nSlots pcs ls Pred)
    {bvsTflat vsTail : List ((t : Ty) × Val t)} (hb : bvsTflat.length = d)
    {tgt : Arg K i64} {tgt' : Arg Val i64} (htgt : denoteArg (bvsTflat ++ vsTail) tgt = some tgt')
    {nxt : RegsExpr K} {nxt' : RegsExpr Val}
    (hnxt : denoteRegsExpr (bvsTflat ++ vsTail) nxt = some nxt')
    {sp₀ : BitVec 64}
    (hsp : nSlots > 0 → sp0Lvl < d ∧ cLevelVal (t := i64) bvsTflat sp0Lvl = some sp₀)
    {sLvls : List Nat} {slots : List (BitVec 64)}
    (hs : nSlots > 0 → SlotsLvlsOk bvsTflat d sLvls slots ∧ slots.length = nSlots)
    (hz : nSlots = 0 → sLvls = []) (hnSp : nSlots > 0 → nxt'.eval.sp = sp₀)
    {mConc mPub : Mem 64} (hfr : FrameRel nSlots sp₀ slots mConc mPub) :
    ∀ (extra : List ((t : Ty) × Val t)) (hotTargets : List (BitVec 64)),
      hotTargets.all (fun p => (findLabelIdx pcs p).isSome) = true →
      (∀ p ∈ hotTargets, tgt'.val = p → Pred p ⟨nxt'.eval, mConc⟩) →
      Ψ_cold tgt'.val ⟨nxt'.eval, mConc⟩ →
      wp Γ (retEnvQ Ψ_cold) X
        (denote Val Cont (lowerContGuarded nSlots sp0Lvl sLvls pcs tgt nxt d extra.length
          hotTargets) ((extra ++ bvsTflat) ++ vsTail) ls) mPub
  | extra, [], _, _, hCold => by
      dsimp only [lowerContGuarded]
      apply flushFrame_wp (bvs := extra ++ bvsTflat) (by rw [List.length_append, hb, Nat.add_comm])
        hfr (fun hPos => let ⟨hlt, hv⟩ := hsp hPos; ⟨Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _),
          cLevelVal_prepend extra bvsTflat hv⟩)
        (fun hPos => let ⟨hsOk, hsLen⟩ := hs hPos; ⟨slotsLvlsOk_ext extra hsOk, hsLen⟩) hz
      intro extraF hexF
      have hlen : (extraF ++ extra).length = extra.length + sLvls.length := by
        simp [hexF, Nat.add_comm]
      have htgtS : denoteArg (((extraF ++ extra) ++ bvsTflat) ++ vsTail)
          (shiftArg (extra.length + sLvls.length) tgt) = some tgt' := by
        rw [List.append_assoc, ← hlen, contDenoteArg_shift, htgt]
      have hnxtS : denoteRegsExpr (((extraF ++ extra) ++ bvsTflat) ++ vsTail)
          (shiftRegsExpr (extra.length + sLvls.length) nxt) = some nxt' := by
        rw [List.append_assoc, ← hlen, contDenoteRegsExpr_shift, hnxt]
      simpa [List.append_assoc] using mkRetEnvelope_wp htgtS hnxtS hCold
  | extra, hPc :: rest, hchk, hPred, hCold => by
      simp only [List.all_cons, Bool.and_eq_true] at hchk
      rcases Option.isSome_iff_exists.1 hchk.1 with ⟨j, hj⟩
      have htgtS : denoteArg ((extra ++ bvsTflat) ++ vsTail) (shiftArg extra.length tgt) =
          some tgt' := by
        rw [List.append_assoc, contDenoteArg_shift, htgt]
      dsimp only [lowerContGuarded, denote, op2, denoteArgs]; rw [htgtS]
      dsimp only [denoteArg, wp, Op.wp, OpCode.wp, vals, liftCmp, Ty.hasFloat]
      constructor
      · intro htr
        dsimp only [CmpOp.evalBits, Arg.val] at htr
        have heq : tgt'.val = hPc := of_decide_eq_true htr
        have hP := hPred hPc List.mem_cons_self heq
        let ex1 := ⟨.bool, CmpOp.evalBits .eq tgt'.val hPc⟩ :: extra
        have hex1 : ex1.length = extra.length + 1 := by simp [ex1]
        have hnxt1 : denoteRegsExpr ((ex1 ++ bvsTflat) ++ vsTail)
            (shiftRegsExpr (extra.length + 1) nxt) = some nxt' := by
          rw [← hex1, List.append_assoc, contDenoteRegsExpr_shift, hnxt]
        have hres := lowerContJumpTo_wp (Γ := Γ) (Q := retEnvQ Ψ_cold) (X := X) hls
          (d := d + extra.length + 1)
          (bvs := ex1 ++ bvsTflat) (by simp [ex1, hb]; omega) hj hnxt1
          (fun hPos => let ⟨hlt, hv⟩ := hsp hPos
            ⟨by omega, cLevelVal_prepend ex1 bvsTflat hv⟩)
          (fun hPos => let ⟨hsOk, hsLen⟩ := hs hPos
            ⟨by simpa [Nat.add_assoc, ex1] using slotsLvlsOk_ext ex1 hsOk, hsLen⟩) hnSp hfr hP
        simpa [ex1, List.append_assoc, pushTup, Arg.val] using hres
      · intro _
        have ih := lowerContGuarded_wp (Γ := Γ) (X := X) hls hb htgt hnxt hsp hs hz hnSp hfr
          (⟨.bool, CmpOp.evalBits .eq tgt'.val hPc⟩ :: extra) rest hchk.2
          (fun p hp => hPred p (List.mem_cons_of_mem _ hp)) hCold
        simpa [pushTup, List.length_cons, List.append_assoc, Arg.val] using ih

theorem contSymState_toSymVal_eval {st : ContSymState} {t : Ty} (a : Arg K t) :
    st.toSymState.evalArg a = (st.evalArg a).toSymVal := by
  cases a with
  | imm c =>
      cases t with
      | bits n =>
          by_cases h : n = 64
          · subst h; rfl
          · have hne : Ty.bits n ≠ Ty.bits 64 := fun he => h (by cases he; rfl)
            simp [SymState.evalArg, ContSymState.evalArg, ContSymVal.toSymVal, hne]
      | bool | float _ | pair _ _ => rfl
  | var idx =>
      dsimp only [ContSymState.toSymState, SymState.evalArg, ContSymState.evalArg,
        SymState.getSym, ContSymState.getSym]
      induction st.env generalizing idx with
      | nil => cases idx <;> rfl
      | cons x xs ih =>
          cases idx with
          | zero => rfl
          | succ k => exact ih k

theorem rpZero_contNxtRp {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {st : ContSymState} (hst : ContSymStateOk bvs sp₀ rp₀ st)
    {nxt : RegsExpr K} {nxt' : RegsExpr Val} (hnxtB : denoteRegsExpr bvs nxt = some nxt')
    {abi : RegionAbi} (hrpOk : (!abi.isContified || st.toSymState.isRpZero nxt.rp) = true)
    (hCont : abi.isContified = true) :
    nxt'.eval.rp = rp₀ := by
  have hz : st.toSymState.isRpZero nxt.rp = true := by rw [hCont] at hrpOk; simpa using hrpOk
  dsimp only [SymState.isRpZero] at hz
  rw [contSymState_toSymVal_eval] at hz
  have hrp : ∃ v, denoteArg bvs nxt.rp = some v := by
    dsimp only [denoteRegsExpr] at hnxtB
    cases h0 : denoteArg bvs nxt.sp <;> rw [h0] at hnxtB; · cases hnxtB
    cases h1 : denoteArg bvs nxt.rp <;> rw [h1] at hnxtB; · cases hnxtB
    exact ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := hrp
  have hm := evalContArg_symValMatch hst hv
  cases hev : st.evalArg nxt.rp with
  | rpOffset off =>
      rw [hev] at hz hm
      by_cases h0 : off = 0#64
      · subst h0
        have hvEq : v.val = rp₀ + 0#64 := hm rfl
        dsimp only [denoteRegsExpr] at hnxtB
        cases h0' : denoteArg bvs nxt.sp <;> rw [h0'] at hnxtB; · cases hnxtB
        rw [hv] at hnxtB
        cases h2 : denoteArg bvs nxt.rv <;> rw [h2] at hnxtB; · cases hnxtB
        cases h3 : denoteArg bvs nxt.r1 <;> rw [h3] at hnxtB; · cases hnxtB
        cases h4 : denoteArg bvs nxt.r2 <;> rw [h4] at hnxtB; · cases hnxtB
        cases h5 : denoteArg bvs nxt.r3 <;> rw [h5] at hnxtB; · cases hnxtB
        cases hnxtB
        simpa [RegsExpr.eval] using hvEq
      · exfalso
        have hne : (0#64 : BitVec 64) ≠ off := fun h => h0 h.symm
        dsimp only [ContSymVal.toSymVal] at hz
        simp [hne.symm] at hz
  | spOffset _ | const _ | alignedConst _ | taggedAligned _ _ | shl3 _ | stride _ _
  | ite _ _ _ | boolConst _ | cmpUlt _ _ | top =>
      rw [hev] at hz; dsimp only [ContSymVal.toSymVal] at hz; cases hz

theorem contSymState_hasUltBound {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {st : ContSymState} (hst : ContSymStateOk bvs sp₀ rp₀ st) {lvl k : Nat}
    (h : st.toSymState.hasUltBound lvl k = true) :
    ∃ x : Val i64, cLevelVal bvs lvl = some x ∧ x.toNat < k := by
  dsimp only [SymState.hasUltBound, ContSymState.toSymState] at h
  rw [List.any_eq_true] at h
  obtain ⟨⟨l, bound⟩, hfMem, hfOk⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfOk
  rcases hfOk with ⟨rfl, hle⟩
  obtain ⟨x, hx, hlt⟩ := hst.factsOk (.ultBound l bound) hfMem
  exact ⟨x, hx, Nat.lt_of_lt_of_le hlt hle⟩

theorem contCall_retNxt_false {d : Nat} (r : Tup Val (RegionAbi.contified false).retSig)
    (bvs : List ((t : Ty) × Val t)) (_hb : bvs.length = d) :
    ∃ nxt' : RegsExpr Val,
      denoteRegsExpr (pushTup r bvs)
        ⟨.var (d + 6 - 1 - d), .var (d + 6 - 1 - (d + 1)), .var (d + 6 - 1 - (d + 2)),
         .var (d + 6 - 1 - (d + 3)), .var (d + 6 - 1 - (d + 4)),
         .var (d + 6 - 1 - (d + 5))⟩ = some nxt' ∧
      nxt'.eval.toRegsV.toTup = r := by
  dsimp only [RegionAbi.retSig] at r
  rcases r with ⟨sp, rp, rv, r1, r2, r3, ⟨⟩⟩
  refine ⟨⟨.var sp, .var rp, .var rv, .var r1, .var r2, .var r3⟩, ?_, rfl⟩
  have he5 : d + 6 - 1 - d = 5 := by omega
  have he4 : d + 6 - 1 - (d + 1) = 4 := by omega
  have he3 : d + 6 - 1 - (d + 2) = 3 := by omega
  have he2 : d + 6 - 1 - (d + 3) = 2 := by omega
  have he1 : d + 6 - 1 - (d + 4) = 1 := by omega
  have he0 : d + 6 - 1 - (d + 5) = 0 := by omega
  dsimp only [denoteRegsExpr]
  rw [he5, he4, he3, he2, he1, he0]
  dsimp only [RegionAbi.retSig, pushTup, denoteArg, lookupV, listGet?, castTy]
  simp only [↓reduceDIte]

theorem contCall_retNxt_true {d : Nat} (r : Tup Val (RegionAbi.contified true).retSig)
    (bvs : List ((t : Ty) × Val t)) (_hb : bvs.length = d) :
    ∃ (c' : Arg Val .bool) (nxt' : RegsExpr Val),
      denoteArg (pushTup r bvs) (.var 6) = some c' ∧
      c'.val = r.1 ∧
      denoteRegsExpr (pushTup r bvs)
        ⟨.var (d + 7 - 1 - (d + 1)), .var (d + 7 - 1 - (d + 2)), .var (d + 7 - 1 - (d + 3)),
         .var (d + 7 - 1 - (d + 4)), .var (d + 7 - 1 - (d + 5)),
         .var (d + 7 - 1 - (d + 6))⟩ = some nxt' ∧
      nxt'.eval.toRegsV.toTup = r.2 := by
  dsimp only [RegionAbi.retSig] at r
  rcases r with ⟨isAlt, sp, rp, rv, r1, r2, r3, ⟨⟩⟩
  refine ⟨.var isAlt, ⟨.var sp, .var rp, .var rv, .var r1, .var r2, .var r3⟩, rfl, rfl, ?_, rfl⟩
  have he5 : d + 7 - 1 - (d + 1) = 5 := by omega
  have he4 : d + 7 - 1 - (d + 2) = 4 := by omega
  have he3 : d + 7 - 1 - (d + 3) = 3 := by omega
  have he2 : d + 7 - 1 - (d + 4) = 2 := by omega
  have he1 : d + 7 - 1 - (d + 5) = 1 := by omega
  have he0 : d + 7 - 1 - (d + 6) = 0 := by omega
  dsimp only [denoteRegsExpr]
  rw [he5, he4, he3, he2, he1, he0]
  dsimp only [RegionAbi.retSig, pushTup, denoteArg, lookupV, listGet?, castTy]
  simp only [↓reduceDIte]

private theorem writeSlots_noop_of_loadVal (m : Mem 64) (sp₀ : BitVec 64) :
    ∀ (base : Nat) (slots : List (BitVec 64)),
      (∀ j < slots.length, ∃ v, slots[j]? = some v ∧
        loadVal m i64 (slotAddr sp₀ (base + j)) = some v) →
      writeSlots m sp₀ base slots = m
  | _, [], _ => rfl
  | base, v :: vs, h => by
      obtain ⟨w, hw, hload⟩ := h 0 (Nat.zero_lt_succ _)
      cases hw
      dsimp only [writeSlots]
      rw [show base + 0 = base from Nat.add_zero base] at hload
      rw [storeMem_of_loadVal_i64 m (slotAddr sp₀ base) v hload]
      exact writeSlots_noop_of_loadVal m sp₀ (base + 1) vs fun j hj => by
        obtain ⟨u, hu, hlu⟩ := h (j + 1) (Nat.succ_lt_succ hj)
        refine ⟨u, hu, ?_⟩
        rw [show base + (j + 1) = (base + 1) + j by omega] at hlu
        exact hlu

private theorem loadEntryFrameAux_step {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    (r₀ : Regs) (totalK : Nat) {ls : List ((ts : List Ty) × Cont ts)}
    {kCont : TFlat rs} (m₀ : Mem 64)
    (hMem : ∀ j < totalK, storeOk m₀ i64 (slotAddr r₀.sp j)) :
    ∀ (rem : Nat) (loaded : List (BitVec 64)) (extra : List ((t : Ty) × Val t)),
      rem ≤ totalK →
      loaded.length = totalK - rem →
      extra.length = 2 * (totalK - rem) →
      (∀ j < loaded.length, ∃ v, loaded[j]? = some v ∧
        cLevelVal (t := i64) (extra ++ pushRegsV r₀.toRegsV) (6 + 2 * j + 1) = some v ∧
        loadVal m₀ i64 (slotAddr r₀.sp j) = some v) →
      (∀ (slots : List (BitVec 64)) (extraFinal : List ((t : Ty) × Val t)),
        slots.length = totalK → extraFinal.length = 2 * totalK →
        (∀ j < totalK, ∃ v, slots[j]? = some v ∧
          cLevelVal (t := i64) (extraFinal ++ pushRegsV r₀.toRegsV) (6 + 2 * j + 1) = some v ∧
          loadVal m₀ i64 (slotAddr r₀.sp j) = some v) →
        wp Γ Q X (denote Val Cont kCont (extraFinal ++ pushRegsV r₀.toRegsV) ls) m₀) →
      wp Γ Q X (denote Val Cont (loadEntryFrameAux 0 totalK rem kCont)
        (extra ++ pushRegsV r₀.toRegsV) ls) m₀
  | 0, loaded, extra, _, hLen, hExLen, hLoaded, hK => by
      rw [Nat.sub_zero] at hLen hExLen
      exact hK loaded extra hLen hExLen (by simpa [hLen] using hLoaded)
  | rem + 1, loaded, extra, hLe, hLen, hExLen, hLoaded, hK => by
      have hkLt : totalK - (rem + 1) < totalK := by omega
      have hBvsLen : (extra ++ pushRegsV r₀.toRegsV).length = 6 + 2 * (totalK - (rem + 1)) := by
        rw [List.length_append, hExLen]; simp [pushRegsV, RegsV.toTup, pushTup]; omega
      have hSp : cLevelVal (t := i64) (extra ++ pushRegsV r₀.toRegsV) 0 = some r₀.sp :=
        cLevelVal_prepend extra (pushRegsV r₀.toRegsV) rfl
      have hspArg : denoteArg (extra ++ pushRegsV r₀.toRegsV)
          (.var (6 + 2 * (totalK - (rem + 1)) - 1 - 0)) = some (@Arg.var Val i64 r₀.sp) := by
        dsimp only [denoteArg]
        rw [cLevelVal_lookupV_tflat hBvsLen (by omega), hSp]
      dsimp only [loadEntryFrameAux, denote, op2, denoteArgs]; rw [hspArg]
      dsimp only [denoteArg, wp, Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat, pushTup]
      let addr := r₀.sp - BitVec.ofNat 64 (8 * (totalK - (rem + 1) + 1))
      obtain ⟨v, hv⟩ := loadVal_i64_of_storeOk (hMem (totalK - (rem + 1)) hkLt)
      dsimp only [denote, denoteArg, lookupV, listGet?, castTy, pushTup]; simp only [↓reduceDIte]
      dsimp only [wp]
      refine ⟨v, hv, ?_⟩
      let extra2 := ⟨i64, v⟩ :: ⟨i64, addr⟩ :: extra
      have hkEq : totalK - rem = totalK - (rem + 1) + 1 := by omega
      have hRes := loadEntryFrameAux_step r₀ totalK m₀ hMem rem (loaded ++ [v]) extra2 (by omega)
        (by simp [hLen, hkEq]) (by simp [extra2, hExLen, hkEq]; omega)
        (fun j hj => by
          rw [List.length_append, List.length_singleton] at hj
          by_cases hjEq : j = loaded.length
          · subst hjEq
            refine ⟨v, by simp, ?_, by rw [hLen]; exact hv⟩
            dsimp only [cLevelVal]
            have hbl : (extra2 ++ pushRegsV r₀.toRegsV).length = 6 + 2 * loaded.length + 2 := by
              simp [extra2, hBvsLen, hLen]
            rw [ite_eq_left (by omega)]
            have hidx : (extra2 ++ pushRegsV r₀.toRegsV).length - 1 -
                (6 + 2 * loaded.length + 1) = 0 := by omega
            rw [hidx]; rfl
          · obtain ⟨u, hu, hcu, hlu⟩ := hLoaded j (by omega)
            refine ⟨u, ?_, ?_, hlu⟩
            · rw [List.getElem?_append_left (by omega)]; exact hu
            · simpa [extra2, List.cons_append] using
                cLevelVal_prepend [⟨i64, v⟩, ⟨i64, addr⟩] (extra ++ pushRegsV r₀.toRegsV) hcu)
        hK
      simpa [extra2, List.cons_append] using hRes

private theorem denote_mkEntrySlotArgs (bvs : List ((t : Ty) × Val t)) (d : Nat)
    (hb : bvs.length = d) :
    ∀ (n idx : Nat) (slotsTail : List (BitVec 64)),
      slotsTail.length = n →
      (∀ j < n, ∃ v, slotsTail[j]? = some v ∧
        cLevelVal (t := i64) bvs (6 + 2 * (idx + j) + 1) = some v) →
      ∃ args', denoteArgs bvs (mkEntrySlotArgs d n idx) = some args' ∧
        vals args' = packSlotTup n slotsTail
  | 0, _, [], _, _ => ⟨(), rfl, rfl⟩
  | _ + 1, _, [], h, _ => by simp at h
  | n + 1, idx, v :: vs, h, hOk => by
      obtain ⟨w, hw, hcv⟩ := hOk 0 (Nat.zero_lt_succ n)
      cases hw
      have hlt : 6 + 2 * idx + 1 < d := by
        have hl := cLevelVal_lt_len (by simpa [Nat.add_zero] using hcv)
        omega
      have harg : denoteArg bvs (.var (d - 1 - (6 + 2 * idx + 1))) =
          some (@Arg.var Val i64 v) := by
        dsimp only [denoteArg]
        have hcv' : cLevelVal (t := i64) bvs (6 + 2 * idx + 1) = some v := by
          simpa [Nat.add_zero] using hcv
        rw [cLevelVal_lookupV_tflat hb hlt, hcv']
      obtain ⟨args', hargs', hvals⟩ := denote_mkEntrySlotArgs bvs d hb n (idx + 1) vs
        (by simp at h; omega) fun j hj => by
          obtain ⟨u, hu, hcu⟩ := hOk (j + 1) (Nat.succ_lt_succ hj)
          refine ⟨u, hu, ?_⟩
          rw [show idx + 1 + j = idx + (j + 1) by omega]
          exact hcu
      refine ⟨(@Arg.var Val i64 v, args'), ?_, ?_⟩
      · simp only [mkEntrySlotArgs, denoteArgs, harg, hargs']
      · simp only [vals, packSlotTup, Arg.val, hvals]

private theorem denote_baseRegArgs_ext (r₀ : Regs) (extra : List ((t : Ty) × Val t)) {d : Nat}
    (hd : d = extra.length + 6) :
    ∃ args', denoteArgs (extra ++ pushRegsV r₀.toRegsV)
        (⟨.var (d - 1 - 0), .var (d - 1 - 1), .var (d - 1 - 2),
          .var (d - 1 - 3), .var (d - 1 - 4), .var (d - 1 - 5)⟩ : RegsExpr K).toTup =
        some args' ∧
      vals args' = r₀.toRegsV.toTup := by
  rcases r₀ with ⟨sp, rp, rv, r1, r2, r3⟩
  have h5 : d - 1 - 0 = extra.length + 5 := by omega
  have h4 : d - 1 - 1 = extra.length + 4 := by omega
  have h3 : d - 1 - 2 = extra.length + 3 := by omega
  have h2 : d - 1 - 3 = extra.length + 2 := by omega
  have h1 : d - 1 - 4 = extra.length + 1 := by omega
  have h0 : d - 1 - 5 = extra.length + 0 := by omega
  refine ⟨(.var sp, .var rp, .var rv, .var r1, .var r2, .var r3, ()), ?_, rfl⟩
  dsimp only [RegsExpr.toTup, denoteArgs, denoteArg, lookupV]
  rw [h5, h4, h3, h2, h1, h0]
  simp only [listGet?_append_skip, pushRegsV, Regs.toRegsV, RegsV.toTup, pushTup, listGet?,
    castTy, ↓reduceDIte]

theorem loadEntryFrameAux_wp {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    {nSlots : Nat} (hn : nSlots ≤ 64) (r₀ : Regs) (m₀ : Mem 64)
    (hPriv : PrivFrameOk nSlots r₀.sp m₀)
    {ls : List ((ts : List Ty) × Cont ts)} {kCont : TFlat rs}
    (hK : ∀ (slots : List (BitVec 64)) (bvsFinal : List ((t : Ty) × Val t)),
      bvsFinal.length = 6 + 2 * nSlots →
      FrameRel nSlots r₀.sp slots m₀ m₀ →
      (∃ args', denoteArgs bvsFinal (mkEntryFrameArgs nSlots) = some args' ∧
        vals args' = packContTup nSlots r₀ r₀.sp slots) →
      wp Γ Q X (denote Val Cont kCont bvsFinal ls) m₀) :
    wp Γ Q X (denote Val Cont (loadEntryFrameAux 0 nSlots nSlots kCont)
      (pushRegsV r₀.toRegsV) ls) m₀ := by
  by_cases hn0 : nSlots = 0
  · subst hn0
    dsimp only [loadEntryFrameAux]
    apply hK [] (pushRegsV r₀.toRegsV) rfl (by dsimp only [FrameRel]; rfl)
    rcases r₀ with ⟨sp, rp, rv, r1, r2, r3⟩
    dsimp only [contSig] at *
    refine ⟨(.var sp, .var rp, .var rv, .var r1, .var r2, .var r3, ()), ?_, rfl⟩
    simp [mkEntryFrameArgs, pushRegsV, Regs.toRegsV, RegsV.toTup,
      pushTup, denoteArgs, denoteArg, lookupV, listGet?, castTy]
  · have hPos : nSlots > 0 := Nat.pos_of_ne_zero hn0
    rcases hPriv hPos with ⟨_, hMem⟩
    apply loadEntryFrameAux_step r₀ nSlots m₀ hMem nSlots [] []
      (Nat.le_refl _) (by simp) (by simp) (fun j hj => by cases hj)
    intro slots extraFinal hSLen hExLen hLoaded
    have hBvsLen : (extraFinal ++ pushRegsV r₀.toRegsV).length = 6 + 2 * nSlots := by
      rw [List.length_append, hExLen]; simp [pushRegsV, RegsV.toTup, pushTup]; omega
    have hFr : FrameRel nSlots r₀.sp slots m₀ m₀ := by
      dsimp only [FrameRel]; rw [ite_eq_right hn0]
      refine ⟨hSLen, hn, hMem, ?_⟩
      exact (writeSlots_noop_of_loadVal m₀ r₀.sp 0 slots fun j hj => by
        obtain ⟨v, hv, _, hlv⟩ := hLoaded j (by omega)
        exact ⟨v, hv, by simpa [Nat.zero_add] using hlv⟩).symm
    apply hK slots (extraFinal ++ pushRegsV r₀.toRegsV) hBvsLen hFr
    cases nSlots with
    | zero => exact absurd rfl hn0
    | succ k =>
        obtain ⟨aR, hAR, hV⟩ := denote_baseRegArgs_ext r₀ extraFinal (d := 6 + 2 * (k + 1))
          (by rw [hExLen]; omega)
        have hSpArg : denoteArg (extraFinal ++ pushRegsV r₀.toRegsV)
            (.var (6 + 2 * (k + 1) - 1 - 0)) = some (@Arg.var Val i64 r₀.sp) := by
          dsimp only [denoteArg, lookupV]
          rw [show 6 + 2 * (k + 1) - 1 - 0 = extraFinal.length + 5 by omega,
              listGet?_append_skip]
          rfl
        obtain ⟨aS, hAS, hVS⟩ := denote_mkEntrySlotArgs (extraFinal ++ pushRegsV r₀.toRegsV)
          (6 + 2 * (k + 1)) hBvsLen (k + 1) 0 slots hSLen fun j hj => by
            obtain ⟨v, hv, hcv, _⟩ := hLoaded j hj
            exact ⟨v, hv, by simpa [Nat.zero_add] using hcv⟩
        have hTail : denoteArgs (extraFinal ++ pushRegsV r₀.toRegsV)
            (ts := List.replicate (k + 2) i64)
            (.var (6 + 2 * (k + 1) - 1 - 0), mkEntrySlotArgs (6 + 2 * (k + 1)) (k + 1) 0) =
            some (@Arg.var Val i64 r₀.sp, aS) := by
          simp only [denoteArgs, hSpArg, hAS]
        obtain ⟨hApp, hVals⟩ := denoteArgs_append_val hAR hTail
        dsimp only [mkEntryFrameArgs]
        refine ⟨tupAppend aR (@Arg.var Val i64 r₀.sp, aS), hApp, ?_⟩
        exact hVals.trans (by rw [hV]; simp only [vals, Arg.val, hVS]; rfl)

/-! ## §4. Region Well-Formedness, `ContifyRegionStep`, `PsiContReg`, `PsiContHyb` -/

theorem liftContifyRegion_wf (cm : CodeMap) (cr : ContifyRegion) :
    (liftContifyRegion cm cr).Wf :=
  Func.wf_of_denote (liftContifyTFlat cm cr) rfl

theorem liftContifyRegion_mid_wf (cm : CodeMap) (cr : ContifyRegion) (t : LegalTarget)
    (hs : ((liftContifyRegion cm cr).earlyOpt).body.supportsSource t = true) :
    ((liftContifyRegion cm cr).mid t).Wf :=
  midEnd_ok t (liftContifyRegion cm cr) ((liftContifyRegion cm cr).mid t)
    (liftContifyRegion_wf cm cr) (by simp [hs])

theorem checkContGroupNodes_forall (cm : CodeMap) (cr : ContifyRegion)
    (callees : List ContCalleeMeta) (pcs : List (BitVec 64)) :
    ∀ gs, checkContGroupNodes cm cr callees pcs gs = true →
      ∀ g ∈ gs, checkContGroupNode cm cr callees pcs g = true
  | [], _, _, h => by cases h
  | g :: gs, hchk, x, hx => by
      dsimp only [checkContGroupNodes] at hchk
      rcases Bool.and_eq_true_iff.1 hchk with ⟨hg, hgs⟩
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact hg
      · exact checkContGroupNodes_forall cm cr callees pcs gs hgs x hx'

theorem checkContGroupNode_entryPc_mem :
    ∀ (cm : CodeMap) (cr : ContifyRegion) (callees : List ContCalleeMeta)
      (pcs : List (BitVec 64)) (g : GroupTree),
      checkContGroupNode cm cr callees pcs g = true → g.entryPc ∈ g.allPcs
  | _, _, _, _, .leaf pc, _ => by
      simp only [GroupTree.entryPc, GroupTree.allPcs]
      exact List.mem_cons_self
  | cm, cr, callees, pcs, .loop header nodes, hchk => by
      dsimp only [checkContGroupNode] at hchk
      simp only [Bool.and_eq_true] at hchk
      have hin : header ∈ nodes.map GroupTree.entryPc := by
        simpa using hchk.1.2
      rw [List.mem_map] at hin
      rcases hin with ⟨c, hcMem, hcEq⟩
      have hsub := checkContGroupNode_entryPc_mem cm cr callees
        (pushLabelPcs (nodes.map GroupTree.entryPc) pcs) c
        (checkContGroupNodes_forall cm cr callees _ nodes hchk.2 c hcMem)
      rw [hcEq] at hsub
      simp only [GroupTree.entryPc, GroupTree.allPcs]
      exact List.mem_flatMap.2 ⟨c, hcMem, hsub⟩

@[expose] def ContTupMemPred (nSlots : Nat) : (gs : List GroupTree) →
    Tup Cont (gs.map fun _ => contSig nSlots) → CodeSpec → Prop
  | [], (), _ => True
  | g :: gs, (J, Js), Pred =>
      (∀ r sp₀ slots mConc mPub, (nSlots > 0 → r.sp = sp₀) →
        FrameRel nSlots sp₀ slots mConc mPub →
        Pred g.entryPc ⟨r, mConc⟩ → J (packContTup nSlots r sp₀ slots) mPub) ∧
      ContTupMemPred nSlots gs Js Pred

theorem contLsMatch_pushTup_group (nSlots : Nat) :
    ∀ (gs : List GroupTree) (Js : Tup Cont (gs.map fun _ => contSig nSlots))
      (pcs : List (BitVec 64)) (ls : List ((ts : List Ty) × Cont ts)) (Pred : CodeSpec),
      ContTupMemPred nSlots gs Js Pred → ContLsMatch nSlots pcs ls Pred →
      ContLsMatch nSlots (pushLabelPcs (gs.map GroupTree.entryPc) pcs) (pushTup Js ls) Pred
  | [], (), _, _, _, _, hls => hls
  | g :: gs, (J, Js), pcs, ls, Pred, ⟨hJ, hrest⟩, hls =>
      contLsMatch_pushTup_group nSlots gs Js (g.entryPc :: pcs)
        (⟨contSig nSlots, J⟩ :: ls) Pred hrest (contLsMatch_cons nSlots hJ hls)

@[expose] def ContifyRegionStep (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (Ψ : Xcap.Lfp.Pred (BitVec 64 × State)) :
    Xcap.Lfp.Pred (BitVec 64 × State) :=
  fun p => ∃ b, cm.lookupAddr p.1 = some b ∧
    b.wp cm.symEnv (fun pc' st' =>
      if (wit.regions.flatMap ContifyRegion.allPcs).contains pc' then
        Ψ (pc', st') ∧ Ψ_cold pc' st'
      else Ψ_cold pc' st') H (pushRegsV p.2.regs.toRegsV) p.2.mem

theorem contifyRegionStep_mono (cm : CodeMap) (wit : ContifyWitness)
    (Ψ_cold : CodeSpec) (H : HaltPost) :
    Xcap.Lfp.mono (ContifyRegionStep cm wit Ψ_cold H) := by
  rintro Ψ₁ Ψ₂ hle ⟨pc, st⟩ ⟨b, hlu, hbp⟩
  refine ⟨b, hlu, blockFlat_wp_mono ?_ b _ _ hbp⟩
  intro pc' st' h
  by_cases hc : (wit.regions.flatMap ContifyRegion.allPcs).contains pc' = true
  · simp only [hc, ↓reduceIte] at h ⊢
    exact ⟨hle (pc', st') h.1, h.2⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact h

/-- Least Knaster–Tarski code specification covering all blocks inside `wit.regions`. -/
@[expose] def PsiContReg (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) : CodeSpec :=
  fun pc st => Xcap.Lfp.lfp (ContifyRegionStep cm wit Ψ_cold H) (pc, st)

/-- Hybrid Stage-1 code specification combining lifted regions (`PsiContReg`) inside
`wit.allPcs` with cold/residual invariant `Ψ_cold`. -/
@[expose] def PsiContHyb (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) : CodeSpec :=
  fun pc st =>
    if (wit.regions.flatMap ContifyRegion.allPcs).contains pc then
      PsiContReg cm wit Ψ_cold H pc st ∧ Ψ_cold pc st
    else Ψ_cold pc st

end LeanQbe.T.Unified
