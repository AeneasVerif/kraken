module

public import LeanQbe.T.LeanLCNF.Sem.H
public import LeanQbe.T.LeanLCNF.Sem.P
public import LeanQbe.T.LeanLCNF.Sem.RcCheck
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1
public import LeanQbe.T.Logic.ProofKit

/-!
# Tier-P ↔ Tier-H Value Representation and Perceus RC Invariant (`ValRep`)

Defines:
- `ScalarRep`, `ObjRep`, `objFieldsRep`, and `ValRep`, relating pure `PVal` values at `LcTy`
  to Tier-H `Word`s and `LcnfObj` heaps (`σ.objs`).
- `HeapClean`, `Backed`, `RcFrame`, `VarInv`, `SharedPredInv`, and `RcInv`, tracking
  live variable representations, exclusivity (`excl → rc = 1`), child-borrow backing,
  and `HandlesRcSound (frameHandles rf) σ.objs` across `RcCtx` transitions.
- Core heap preservation lemmas for fresh allocation, `inc`, non-cold `dec`, `DecColdClean`,
  exclusive `del`, and exclusive in-place mutations (`oset`, `uset`, `sset`, `setTag`).
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

public section

/-! ## 1. BitVec, Tagged Integer, and Little-Endian Byte Helpers -/

theorem boxNat_and1_ne_zero (n : Nat) :
    (BitVec.ofNat 64 (2 * n + 1) &&& 1#64) ≠ 0#64 := by
  intro h
  have hm := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_zero] at hm
  change ((2 * n + 1) % 2 ^ 64 &&& 1) = 0 at hm
  rw [Nat.and_one_is_mod] at hm
  omega

theorem boxNat_rshift1_toNat {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * n + 1) >>> 1).toNat = n := by
  have hlt : 2 * n + 1 < 2 ^ 64 := by omega
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  omega

theorem bv64_tagged_bits_eq_ofNat {w : Nat} (hw : w < 64) (v : BitVec w) :
    (BitVec.setWidth 64 v <<< 1 ||| 1#64) = BitVec.ofNat 64 (2 * v.toNat + 1) := by
  have hv : v.toNat < 2 ^ w := v.isLt
  have hp : 2 ^ w ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : 2 * v.toNat + 1 < 2 ^ 64 := by omega
  have hvlt : v.toNat < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  simp only [Nat.shiftLeft_eq, Nat.pow_one]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hlt, Nat.mul_comm v.toNat 2]
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    have hpow : 1 < 2 ^ (k + 1) := Nat.one_lt_two_pow (by omega)
    have hdiv : 1 / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt hpow
    have h1 : (1 : Nat).testBit (k + 1) = false := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
      rfl
    simp only [Nat.testBit_or, h1, Bool.or_false]
    have h2k : 2 * v.toNat = v.toNat * 2 := Nat.mul_comm _ _
    have h2k1 : 2 * v.toNat + 1 = v.toNat * 2 + 1 := by omega
    have lhs_eq : (2 * v.toNat).testBit (k + 1) = (v.toNat * 2).testBit (k + 1) := by
      rw [h2k]
    have rhs_eq : (2 * v.toNat + 1).testBit (k + 1) = (v.toNat * 2 + 1).testBit (k + 1) := by
      rw [h2k1]
    have hdiv2 : (v.toNat * 2 + 1) / 2 = v.toNat := by omega
    rw [lhs_eq, rhs_eq, Nat.testBit_succ, Nat.testBit_succ]
    simp [hdiv2]

theorem bv64_tagged_bits_and1 {w : Nat} (hw : w < 64) (v : BitVec w) :
    ((BitVec.setWidth 64 v <<< 1 ||| 1#64) &&& 1#64) ≠ 0#64 := by
  rw [bv64_tagged_bits_eq_ofNat hw v]
  exact boxNat_and1_ne_zero v.toNat

theorem bv64_tagged_bits_unbox {w : Nat} (hw : w < 64) (v : BitVec w) :
    BitVec.setWidth w ((BitVec.setWidth 64 v <<< 1 ||| 1#64) >>> 1) = v := by
  rw [bv64_tagged_bits_eq_ofNat hw v]
  have hp : 2 ^ w ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : v.toNat < 2 ^ 63 := Nat.lt_of_lt_of_le v.isLt hp
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, boxNat_rshift1_toNat hlt]
  exact Nat.mod_eq_of_lt v.isLt

theorem writeNatLE_length (n k : Nat) : (writeNatLE n k).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [writeNatLE, ih]

private theorem readNatLE_cons_succ (b : UInt8) (bs : List UInt8) (off k : Nat) :
    readNatLE (b :: bs) (off + 1) k = readNatLE bs off k := by
  induction k generalizing off with
  | zero => simp [readNatLE]
  | succ k ih =>
    simp only [readNatLE, List.getD_cons_succ]
    rw [ih (off + 1)]

theorem readNatLE_writeNatLE (n k : Nat) :
    readNatLE (writeNatLE n k) 0 k = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [readNatLE, Nat.mod_one]
  | succ k ih =>
    simp only [readNatLE, writeNatLE, List.getD, List.getElem?_cons_zero,
      Option.getD_some, readNatLE_cons_succ]
    have hu8 : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      change (BitVec.ofNat 8 (n % 256)).toNat = n % 256
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.mod_lt n (by decide))
    rw [hu8, ih (n / 256)]
    have hpow : 256 ^ (k + 1) = 256 * 256 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    have h1 := Nat.div_add_mod n 256
    have h2 := Nat.div_add_mod (n / 256) (256 ^ k)
    have hlt1 : n % 256 < 256 := Nat.mod_lt n (by decide)
    have hlt2 : n / 256 % 256 ^ k < 256 ^ k := Nat.mod_lt _ (Nat.pow_pos (by decide))
    have hle : 256 * (n / 256 % 256 ^ k + 1) ≤ 256 * 256 ^ k :=
      Nat.mul_le_mul_left 256 (by omega)
    have hltSum : n % 256 + 256 * (n / 256 % 256 ^ k) < 256 * 256 ^ k := by
      rw [Nat.mul_add, Nat.mul_one] at hle
      omega
    have hn_decomp : n = (256 * 256 ^ k) * (n / 256 / 256 ^ k) +
        (n % 256 + 256 * (n / 256 % 256 ^ k)) := by
      calc n = 256 * (n / 256) + n % 256 := h1.symm
        _ = 256 * (256 ^ k * (n / 256 / 256 ^ k) + n / 256 % 256 ^ k) + n % 256 := by rw [h2]
        _ = (256 * 256 ^ k) * (n / 256 / 256 ^ k) +
            (n % 256 + 256 * (n / 256 % 256 ^ k)) := by
          rw [Nat.mul_add, Nat.mul_assoc]; omega
    have hmod : ((256 * 256 ^ k) * (n / 256 / 256 ^ k) +
        (n % 256 + 256 * (n / 256 % 256 ^ k))) % (256 * 256 ^ k) =
        n % 256 + 256 * (n / 256 % 256 ^ k) := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hltSum]
    rw [← hn_decomp] at hmod
    exact hmod.symm

theorem readBitsLE_writeNatLE_64 (v : BitVec 64) :
    readBitsLE 64 (writeNatLE v.toNat 8) 0 = v := by
  unfold readBitsLE
  have hlen : (64 + 7) / 8 = 8 := rfl
  rw [hlen, readNatLE_writeNatLE]
  have h256 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  rw [h256, Nat.mod_eq_of_lt v.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem readBitsLE_eq_pval (w : Nat) (bs : List UInt8) (off : Nat) :
    PVal.readBitsLE w bs off = readBitsLE w bs off := by
  have aux : ∀ k bs off, PVal.readNatLE bs off k = readNatLE bs off k := by
    intro k
    induction k with
    | zero => intro _ _; rfl
    | succ k ih =>
      intro bs off
      simp only [PVal.readNatLE, readNatLE]
      rw [ih]
  simp only [PVal.readBitsLE, readBitsLE, aux]

theorem writeNatLE_eq_pval (n k : Nat) : PVal.writeNatLE n k = writeNatLE n k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [PVal.writeNatLE, writeNatLE, ih]

theorem writeBytesAt_eq_pval (bs : List UInt8) (off : Nat) (patch : List UInt8) :
    PVal.writeBytesAt bs off patch = writeBytesAt bs off patch := rfl

theorem writeBytesAt_length {bs : List UInt8} {off : Nat} {patch : List UInt8}
    (h : off + patch.length ≤ bs.length) :
    (writeBytesAt bs off patch).length = bs.length := by
  unfold writeBytesAt
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

theorem bv64_and1_zero_iff_even (x : BitVec 64) :
    (x &&& 1#64 = 0#64) ↔ x.toNat % 2 = 0 := by
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_zero] at ht
    change (x.toNat &&& 1) = 0 at ht
    rw [Nat.and_one_is_mod] at ht
    exact ht
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_zero]
    change (x.toNat &&& 1) = 0
    rw [Nat.and_one_is_mod]
    exact h

theorem bv64_and1_zero_of_mod8_val {a : BitVec 64} (h : a.toNat % 8 = 0) :
    (a &&& 1#64) = 0#64 :=
  (bv64_and1_zero_iff_even a).mpr (by omega)

theorem obj_addr_and1_zero {o : LcnfObj} (hwf : o.Wf) : (o.addr &&& 1#64) = 0#64 :=
  bv64_and1_zero_of_mod8_val hwf.2.1

/-! ## 2. Value Representation (`ScalarRep`, `ObjRep`, `ValRep`) -/

/-- Pure scalar representation at bit-width `w` matching Tier-H `Word`. -/
@[expose] def ScalarRep (w : Nat) (pv : PVal) (word : Word) : Prop :=
  (∃ bv : BitVec w, pv = .bits w bv ∧ word = ⟨.bits w, bv⟩) ∨
  (∃ cidx : Nat, pv = .ctor cidx [] [] ∧ cidx < 2 ^ w ∧
    word = ⟨.bits w, BitVec.ofNat w cidx⟩) ∨
  (pv = .erased ∧ word = ⟨.bits w, 0#w⟩)

mutual
/-- Representation of a pure `PVal` as a 64-bit object/tagged word `bv` in `objs`. -/
@[expose] def ObjRep : PVal → BitVec 64 → List LcnfObj → Prop
  | .erased, bv, _ => bv = 1#64
  | .bits w v, bv, objs =>
      (w < 64 ∧ bv = BitVec.setWidth 64 v <<< 1 ||| 1#64) ∨
      (w = 64 ∧ ∃ o ∈ objs, o.addr = bv ∧ o.Wf ∧ o.tag = 0 ∧
        o.fields = [] ∧ o.scalarData = writeNatLE v.toNat 8)
  | .nat n, bv, objs => natRep bv n objs
  | .ctor cidx fields scal, bv, objs =>
      (fields = [] ∧ scal = [] ∧ cidx < 2 ^ 63 ∧ bv = BitVec.ofNat 64 (2 * cidx + 1)) ∨
      (¬(fields = [] ∧ scal = []) ∧
        ∃ o ∈ objs, o.addr = bv ∧ o.Wf ∧ o.tag = cidx ∧ o.tag ≤ 244 ∧
          o.scalarData = scal ∧ objFieldsRep fields o.fields objs)
  | .str s, bv, objs =>
      ∃ o ∈ objs, o.addr = bv ∧ o.Wf ∧ StrCanon o ∧
        strPayload o = s.toUTF8.toList ∧ o.strLen = s.length
  | .arr xs, bv, objs =>
      ∃ o ∈ objs, o.addr = bv ∧ o.Wf ∧ ArrCanon o ∧ objFieldsRep xs o.fields objs
  | .barr bs, bv, objs =>
      ∃ o ∈ objs, o.addr = bv ∧ o.Wf ∧ BaCanon o ∧ o.scalarData = bs
  | .int _, _, _ => False
  | .clo _ _ _, _, _ => False

/-- Elementwise object-field representation for `ctor` and `arr`. -/
@[expose] def objFieldsRep : List PVal → List (BitVec 64) → List LcnfObj → Prop
  | [], [], _ => True
  | p :: ps, b :: bs, objs => ObjRep p b objs ∧ objFieldsRep ps bs objs
  | _, _, _ => False
end

/-- Typed correspondence between a pure `PVal` and a Tier-H `Word` at LCNF type `ty`. -/
@[expose] def ValRep (ty : LcTy) (pv : PVal) (w : Word) (objs : List LcnfObj) : Prop :=
  if ty.isScalar then ScalarRep ty.width pv w
  else
    ∃ bv : BitVec 64, w = Word.i64 bv ∧ ObjRep pv bv objs ∧
      (ty = .object → (bv &&& 1#64) = 0#64) ∧
      (ty = .tagged → (bv &&& 1#64) ≠ 0#64)

/-- Non-RC object field equality between two `LcnfObj` snapshots. -/
@[expose] def ObjDataEq (o o' : LcnfObj) : Prop :=
  o'.addr = o.addr ∧ o'.Wf ∧ o'.tag = o.tag ∧ o'.fields = o.fields ∧
  o'.scalarData = o.scalarData ∧ o'.arrSize = o.arrSize ∧ o'.strLen = o.strLen ∧
  o'.limbs = o.limbs ∧ o'.cap = o.cap ∧ o'.other = o.other ∧ o'.csSz = o.csSz

theorem objDataEq_refl (o : LcnfObj) (hwf : o.Wf) : ObjDataEq o o :=
  ⟨rfl, hwf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem objDataEq_withRc {o : LcnfObj} (hwf : o.Wf) (rc' : BitVec 32)
    (hrc : 0 ≤ rc'.toInt) : ObjDataEq o (o.withRc rc') := by
  rcases hwf with ⟨h1, h2, _, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨rfl, ⟨h1, h2, hrc, h4, h5, h6, h7, h8, h9, h10⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem objDataEq_strCanon {o o' : LcnfObj} (hd : ObjDataEq o o') (hc : StrCanon o) :
    StrCanon o' := by
  rcases hd with ⟨ha, hwf, ht, _, hs, has, hsl, _, hc', ho, hcs⟩
  rcases hc with ⟨hc1, hc2, _, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12⟩
  exact ⟨ha ▸ hc1, ha ▸ hc2, hwf.2.2.1, hcs ▸ hc4, ho ▸ hc5, ht ▸ hc6,
    has ▸ hc7, has ▸ hc' ▸ hc8, hc' ▸ hc9, hs ▸ has ▸ hc10, hs ▸ hc11, hsl ▸ hc12⟩

theorem objDataEq_arrCanon {o o' : LcnfObj} (hd : ObjDataEq o o') (hc : ArrCanon o) :
    ArrCanon o' := by
  rcases hd with ⟨ha, hwf, ht, hf, _, _, _, _, hc', ho, hcs⟩
  rcases hc with ⟨hc1, hc2, _, hc4, hc5, hc6, hc7, hc8⟩
  exact ⟨ha ▸ hc1, ha ▸ hc2, hwf.2.2.1, hcs ▸ hc4, ho ▸ hc5, ht ▸ hc6,
    hf ▸ hc' ▸ hc7, hc' ▸ hc8⟩

theorem objDataEq_baCanon {o o' : LcnfObj} (hd : ObjDataEq o o') (hc : BaCanon o) :
    BaCanon o' := by
  rcases hd with ⟨ha, hwf, ht, _, hs, has, _, _, hc', ho, hcs⟩
  rcases hc with ⟨hc1, hc2, _, hc4, hc5, hc6, hc7, hc8, hc9⟩
  exact ⟨ha ▸ hc1, ha ▸ hc2, hwf.2.2.1, hcs ▸ hc4, ho ▸ hc5, ht ▸ hc6,
    has ▸ hs ▸ hc7, has ▸ hc' ▸ hc8, hc' ▸ hc9⟩

theorem objDataEq_mpzNatCanon {o o' : LcnfObj} {n : Nat} (hd : ObjDataEq o o')
    (hc : mpzNatCanon o n) : mpzNatCanon o' n := by
  rcases hd with ⟨_, hwf, ht, _, _, has, _, hl, _, ho, _⟩
  rcases hc with ⟨_, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9⟩
  exact ⟨hwf, ht ▸ hc2, ho ▸ hc3, has ▸ hl ▸ hc4, hl ▸ hc5, hl ▸ hc6, hl ▸ hc7, hl ▸ hc8, hc9⟩

theorem objFieldsRep_length {pvs : List PVal} {bvs : List (BitVec 64)} {objs : List LcnfObj}
    (h : objFieldsRep pvs bvs objs) : pvs.length = bvs.length := by
  induction pvs generalizing bvs with
  | nil => cases bvs with | nil => rfl | cons _ _ => exact False.elim h
  | cons p ps ih =>
    cases bvs with
    | nil => exact False.elim h
    | cons b bs =>
      dsimp only [objFieldsRep] at h
      simp [ih h.2]

theorem objFieldsRep_getElem {pvs : List PVal} {bvs : List (BitVec 64)} {objs : List LcnfObj}
    (h : objFieldsRep pvs bvs objs) {i : Nat} (hi : i < pvs.length) (hb : i < bvs.length) :
    ObjRep pvs[i] bvs[i] objs := by
  induction pvs generalizing bvs i with
  | nil => cases hi
  | cons p ps ih =>
    cases bvs with
    | nil => exact False.elim h
    | cons b bs =>
      dsimp only [objFieldsRep] at h
      cases i with
      | zero => exact h.1
      | succ k => exact ih h.2 (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hb)

theorem objFieldsRep_set {pvs : List PVal} {bvs : List (BitVec 64)} {objs : List LcnfObj}
    (h : objFieldsRep pvs bvs objs) (i : Nat) {pv : PVal} {bv : BitVec 64}
    (hpv : ObjRep pv bv objs) :
    objFieldsRep (pvs.set i pv) (bvs.set i bv) objs := by
  induction pvs generalizing bvs i with
  | nil =>
    cases bvs with
    | nil => simp [objFieldsRep]
    | cons _ _ => exact False.elim h
  | cons p ps ih =>
    cases bvs with
    | nil => exact False.elim h
    | cons b bs =>
      dsimp only [objFieldsRep] at h
      cases i with
      | zero => exact ⟨hpv, h.2⟩
      | succ k => exact ⟨h.1, ih h.2 k⟩

private theorem sizeOf_mem_lt_list {α : Type} [SizeOf α] {a : α} {xs : List α} (h : a ∈ xs) :
    sizeOf a < sizeOf xs := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | hx
    · change sizeOf a < 1 + sizeOf a + sizeOf xs; omega
    · have ihx := ih hx
      change sizeOf a < 1 + sizeOf x + sizeOf xs; omega

theorem objRep_mono_pred {P : BitVec 64 → Prop} {objs objs' : List LcnfObj}
    (hpres : ∀ o ∈ objs, o.Wf → P o.addr → ∃ o' ∈ objs', ObjDataEq o o')
    (hclosed : ∀ o ∈ objs, o.Wf → P o.addr → ∀ f ∈ o.childFields,
      (f &&& 1#64) = 0#64 → P f) :
    ∀ (pv : PVal) (bv : BitVec 64),
      ObjRep pv bv objs → (bv &&& 1#64 = 0#64 → P bv) → ObjRep pv bv objs' := by
  have hmut :
      ∀ (n : Nat) (pv : PVal) (bv : BitVec 64), sizeOf pv ≤ n →
        ObjRep pv bv objs → (bv &&& 1#64 = 0#64 → P bv) → ObjRep pv bv objs' := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro pv bv hsz hrep hp
      have hfields : ∀ pvs bvs, (∀ p ∈ pvs, sizeOf p < sizeOf pv) →
          objFieldsRep pvs bvs objs → (∀ f ∈ bvs, (f &&& 1#64) = 0#64 → P f) →
          objFieldsRep pvs bvs objs' := by
        intro pvs
        induction pvs with
        | nil =>
          intro bvs _ hf _
          cases bvs with | nil => trivial | cons _ _ => exact False.elim hf
        | cons q qs ihqs =>
          intro bvs hqsz hf hpf
          cases bvs with
          | nil => exact False.elim hf
          | cons b bs =>
            dsimp only [objFieldsRep] at hf ⊢
            have hqlt : sizeOf q < sizeOf pv := hqsz q List.mem_cons_self
            exact ⟨ih (sizeOf q) (by omega) q b (Nat.le_refl _) hf.1
              (fun hb0 => hpf b List.mem_cons_self hb0),
              ihqs bs (fun r hr => hqsz r (List.mem_cons_of_mem _ hr)) hf.2
                (fun f hfm hf0 => hpf f (List.mem_cons_of_mem _ hfm) hf0)⟩
      cases pv with
      | erased => exact hrep
      | bits w v =>
        rcases hrep with ⟨hw, hbv⟩ | ⟨hw, o, ho, hoa, hwf, ht, hfs, hsd⟩
        · exact Or.inl ⟨hw, hbv⟩
        · have hb0 : bv &&& 1#64 = 0#64 := hoa ▸ obj_addr_and1_zero hwf
          obtain ⟨o', ho', hd⟩ := hpres o ho hwf (hoa ▸ hp hb0)
          exact Or.inr ⟨hw, o', ho', hd.1.trans hoa, hd.2.1,
            hd.2.2.1.trans ht, hd.2.2.2.1.trans hfs, hd.2.2.2.2.1.trans hsd⟩
      | nat m =>
        dsimp only [ObjRep] at hrep ⊢
        by_cases hm : m < 2 ^ 63
        · simp only [natRep, hm, ↓reduceIte] at hrep ⊢
          exact hrep
        · simp only [natRep, hm, ↓reduceIte] at hrep ⊢
          rcases hrep with ⟨hb0, o, ho, hoa, hc⟩
          obtain ⟨o', ho', hd⟩ := hpres o ho hc.1 (hoa ▸ hp hb0)
          exact ⟨hb0, o', ho', hd.1.trans hoa, objDataEq_mpzNatCanon hd hc⟩
      | ctor cidx fs sc =>
        rcases hrep with ⟨hfs, hsc, hc63, hbv⟩ | ⟨hne, o, ho, hoa, hwf, ht, ht244, hsc, hfr⟩
        · exact Or.inl ⟨hfs, hsc, hc63, hbv⟩
        · have hb0 : bv &&& 1#64 = 0#64 := hoa ▸ obj_addr_and1_zero hwf
          have hpa : P o.addr := hoa ▸ hp hb0
          obtain ⟨o', ho', hd⟩ := hpres o ho hwf hpa
          have hcf : o.childFields = o.fields := by simp [LcnfObj.childFields, ht244]
          have hszfs : ∀ p ∈ fs, sizeOf p < sizeOf (PVal.ctor cidx fs sc) := by
            intro p hp'
            have := sizeOf_mem_lt_list hp'
            simp only [PVal.ctor.sizeOf_spec]
            omega
          refine Or.inr ⟨hne, o', ho', hd.1.trans hoa, hd.2.1, hd.2.2.1.trans ht,
            hd.2.2.1 ▸ ht244, hd.2.2.2.2.1.trans hsc, hd.2.2.2.1 ▸ ?_⟩
          exact hfields fs o.fields hszfs hfr fun f hf hf0 =>
            hclosed o ho hwf hpa f (hcf ▸ hf) hf0
      | str s =>
        rcases hrep with ⟨o, ho, hoa, hwf, hcan, hpl, hsl⟩
        obtain ⟨o', ho', hd⟩ := hpres o ho hwf (hoa ▸ hp (hoa ▸ obj_addr_and1_zero hwf))
        refine ⟨o', ho', hd.1.trans hoa, hd.2.1, objDataEq_strCanon hd hcan, ?_,
          hd.2.2.2.2.2.2.1.trans hsl⟩
        unfold strPayload at hpl ⊢
        rw [hd.2.2.2.2.1]
        exact hpl
      | arr xs =>
        rcases hrep with ⟨o, ho, hoa, hwf, hcan, hfr⟩
        have hb0 : bv &&& 1#64 = 0#64 := hoa ▸ obj_addr_and1_zero hwf
        have hpa : P o.addr := hoa ▸ hp hb0
        obtain ⟨o', ho', hd⟩ := hpres o ho hwf hpa
        have hcf : o.childFields = o.fields := by
          have : o.tag = arrayTag := hcan.2.2.2.2.2.1
          simp [LcnfObj.childFields, this]
        have hszxs : ∀ p ∈ xs, sizeOf p < sizeOf (PVal.arr xs) := by
          intro p hp'
          have := sizeOf_mem_lt_list hp'
          simp only [PVal.arr.sizeOf_spec]
          omega
        refine ⟨o', ho', hd.1.trans hoa, hd.2.1, objDataEq_arrCanon hd hcan, hd.2.2.2.1 ▸ ?_⟩
        exact hfields xs o.fields hszxs hfr fun f hf hf0 =>
          hclosed o ho hwf hpa f (hcf ▸ hf) hf0
      | barr bs =>
        rcases hrep with ⟨o, ho, hoa, hwf, hcan, hsd⟩
        obtain ⟨o', ho', hd⟩ := hpres o ho hwf (hoa ▸ hp (hoa ▸ obj_addr_and1_zero hwf))
        exact ⟨o', ho', hd.1.trans hoa, hd.2.1, objDataEq_baCanon hd hcan, hd.2.2.2.2.1.trans hsd⟩
      | int _ => exact False.elim hrep
      | clo _ _ _ => exact False.elim hrep
  exact fun pv bv hrep hp => hmut (sizeOf pv) pv bv (Nat.le_refl _) hrep hp

theorem objFieldsRep_mono_pred {P : BitVec 64 → Prop} {objs objs' : List LcnfObj}
    (hpres : ∀ o ∈ objs, o.Wf → P o.addr → ∃ o' ∈ objs', ObjDataEq o o')
    (hclosed : ∀ o ∈ objs, o.Wf → P o.addr → ∀ f ∈ o.childFields,
      (f &&& 1#64) = 0#64 → P f)
    {pvs : List PVal} {bvs : List (BitVec 64)}
    (hfr : objFieldsRep pvs bvs objs) (hp : ∀ f ∈ bvs, (f &&& 1#64) = 0#64 → P f) :
    objFieldsRep pvs bvs objs' := by
  induction pvs generalizing bvs with
  | nil => cases bvs with | nil => trivial | cons _ _ => exact False.elim hfr
  | cons q qs ih =>
    cases bvs with
    | nil => exact False.elim hfr
    | cons b bs =>
      dsimp only [objFieldsRep] at hfr ⊢
      exact ⟨objRep_mono_pred hpres hclosed q b hfr.1 (fun hb => hp b List.mem_cons_self hb),
        ih hfr.2 (fun f hf => hp f (List.mem_cons_of_mem _ hf))⟩

theorem valRep_mono_pred {P : BitVec 64 → Prop} {objs objs' : List LcnfObj}
    (hpres : ∀ o ∈ objs, o.Wf → P o.addr → ∃ o' ∈ objs', ObjDataEq o o')
    (hclosed : ∀ o ∈ objs, o.Wf → P o.addr → ∀ f ∈ o.childFields,
      (f &&& 1#64) = 0#64 → P f)
    {ty : LcTy} {pv : PVal} {w : Word}
    (hvr : ValRep ty pv w objs)
    (hp : ¬ty.isScalar → ∀ bv, w = Word.i64 bv → (bv &&& 1#64 = 0#64 → P bv)) :
    ValRep ty pv w objs' := by
  unfold ValRep at hvr ⊢
  split at hvr
  · next hsc => rw [ite_eq_left hsc]; exact hvr
  · next hsc =>
    rw [ite_eq_right hsc]
    rcases hvr with ⟨bv, rfl, hrep, hobj, htag⟩
    exact ⟨bv, rfl, objRep_mono_pred hpres hclosed pv bv hrep (hp hsc bv rfl), hobj, htag⟩

/-! ## 3. Well-Founded Tree Size & Acyclicity (`objRep_not_self_field`) -/

mutual
@[expose] def valNodes : PVal → Nat
  | .ctor _ fs _ => 1 + listValNodes fs
  | .arr xs => 1 + listValNodes xs
  | _ => 1

@[expose] def listValNodes : List PVal → Nat
  | [] => 0
  | p :: ps => valNodes p + listValNodes ps
end

private theorem valNodes_pos (pv : PVal) : 1 ≤ valNodes pv := by
  cases pv <;> simp [valNodes] <;> omega

private theorem listValNodes_mem_le {p : PVal} {ps : List PVal} (h : p ∈ ps) :
    valNodes p ≤ listValNodes ps := by
  induction ps with
  | nil => cases h
  | cons q qs ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp only [listValNodes]; omega
    · have := ih h'; simp only [listValNodes]; omega

private theorem listValNodes_lt_imp_exists {ps qs : List PVal} {bs : List (BitVec 64)}
    {objs : List LcnfObj} (hp : objFieldsRep ps bs objs) (hq : objFieldsRep qs bs objs)
    (hlt : listValNodes qs < listValNodes ps) :
    ∃ p ∈ ps, ∃ q ∈ qs, ∃ b : BitVec 64,
      valNodes q < valNodes p ∧ ObjRep p b objs ∧ ObjRep q b objs := by
  induction ps generalizing qs bs with
  | nil =>
    cases bs with
    | nil => cases qs with | nil => simp [listValNodes] at hlt | cons _ _ => exact False.elim hq
    | cons _ _ => exact False.elim hp
  | cons p ps ih =>
    cases bs with
    | nil => exact False.elim hp
    | cons b bs =>
      cases qs with
      | nil => exact False.elim hq
      | cons q qs =>
        dsimp only [objFieldsRep] at hp hq
        simp only [listValNodes] at hlt
        by_cases hqp : valNodes q < valNodes p
        · exact ⟨p, List.mem_cons_self, q, List.mem_cons_self, b, hqp, hp.1, hq.1⟩
        · obtain ⟨p', hp', q', hq', b', hlt', hr1, hr2⟩ := ih hp.2 hq.2 (by omega)
          exact ⟨p', List.mem_cons_of_mem _ hp', q', List.mem_cons_of_mem _ hq', b',
            hlt', hr1, hr2⟩

theorem obj_eq_of_addr_nodup {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup)
    {o1 o2 : LcnfObj} (h1 : o1 ∈ objs) (h2 : o2 ∈ objs) (heq : o1.addr = o2.addr) :
    o1 = o2 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h1
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h2
  have hij := nodup_map_getElem_eq LcnfObj.addr hnd hi hj heq
  subst hij
  rfl

private theorem objRep_is_even_of_valNodes_gt1 {pv : PVal} {bv : BitVec 64}
    {objs : List LcnfObj} (hrep : ObjRep pv bv objs) (hgt : 1 < valNodes pv) :
    (bv &&& 1#64) = 0#64 := by
  cases pv with
  | ctor c fs sc =>
    rcases hrep with ⟨rfl, _, _⟩ | ⟨_, o, _, hoa, hwf, _⟩
    · simp [valNodes, listValNodes] at hgt
    · exact hoa ▸ obj_addr_and1_zero hwf
  | arr xs =>
    rcases hrep with ⟨o, _, hoa, hwf, _⟩
    exact hoa ▸ obj_addr_and1_zero hwf
  | _ => simp [valNodes] at hgt

private theorem objRep_tag_of_valNodes_gt1 {pv : PVal} {bv : BitVec 64}
    {objs : List LcnfObj} (_hnd : (objs.map LcnfObj.addr).Nodup)
    (hrep : ObjRep pv bv objs) (hgt : 1 < valNodes pv) :
    ∃ o ∈ objs, o.addr = bv ∧ (pv.tag? = some o.tag ∨ o.tag = arrayTag) := by
  cases pv with
  | ctor c fs sc =>
    rcases hrep with ⟨rfl, _, _⟩ | ⟨_, o, ho, hoa, _, ht, _⟩
    · simp [valNodes, listValNodes] at hgt
    · exact ⟨o, ho, hoa, Or.inl (by simp [PVal.tag?, ht])⟩
  | arr xs =>
    rcases hrep with ⟨o, ho, hoa, _, hcan, _⟩
    exact ⟨o, ho, hoa, Or.inr hcan.2.2.2.2.2.1⟩
  | _ => simp [valNodes] at hgt

theorem objRep_not_smaller {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup) :
    ∀ (n : Nat) (pv pv' : PVal) (bv : BitVec 64),
      valNodes pv ≤ n → valNodes pv' < valNodes pv →
      ObjRep pv bv objs → ObjRep pv' bv objs → False := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro pv pv' bv hsz hlt hr1 hr2
    have hge1 : 1 ≤ valNodes pv' := valNodes_pos pv'
    have hgt : 1 < valNodes pv := by omega
    have hbv0 : bv &&& 1#64 = 0#64 := objRep_is_even_of_valNodes_gt1 hr1 hgt
    cases pv with
    | ctor c fs sc =>
      rcases hr1 with ⟨rfl, _, _⟩ | ⟨_, o, ho, hoa, hwf, ht, ht244, _, hfr⟩
      · simp [valNodes, listValNodes] at hgt
      · cases pv' with
        | erased =>
          dsimp only [ObjRep] at hr2
          rw [hr2] at hbv0
          exact absurd hbv0 (by decide)
        | bits w' v' =>
          rcases hr2 with ⟨hw', hbv⟩ | ⟨_, o', ho', hoa', _, ht', hfs', _⟩
          · exact bv64_tagged_bits_and1 hw' v' (hbv ▸ hbv0)
          · have heq := obj_eq_of_addr_nodup hnd ho ho' (hoa.trans hoa'.symm)
            subst heq
            have hfl := objFieldsRep_length hfr
            rw [hfs'] at hfl
            have hfs0 : fs = [] := List.eq_nil_of_length_eq_zero hfl
            subst hfs0
            simp [valNodes, listValNodes] at hgt
        | nat m =>
          dsimp only [ObjRep, natRep] at hr2
          split at hr2
          · rw [hr2] at hbv0; exact boxNat_and1_ne_zero m hbv0
          · rcases hr2 with ⟨_, o', ho', hoa', hc⟩
            have heq := obj_eq_of_addr_nodup hnd ho ho' (hoa.trans hoa'.symm)
            subst heq
            have htag : o.tag = mpzTag := hc.2.1
            have : mpzTag ≤ 244 := htag ▸ ht244
            exact absurd this (by decide)
        | str s =>
          rcases hr2 with ⟨o', ho', hoa', _, hcan, _⟩
          have heq := obj_eq_of_addr_nodup hnd ho ho' (hoa.trans hoa'.symm)
          subst heq
          have : stringTag ≤ 244 := hcan.2.2.2.2.2.1 ▸ ht244
          exact absurd this (by decide)
        | barr bs =>
          rcases hr2 with ⟨o', ho', hoa', _, hcan, _⟩
          have heq := obj_eq_of_addr_nodup hnd ho ho' (hoa.trans hoa'.symm)
          subst heq
          have : sarrayTag ≤ 244 := hcan.2.2.2.2.2.1 ▸ ht244
          exact absurd this (by decide)
        | int _ => exact False.elim hr2
        | clo _ _ _ => exact False.elim hr2
        | arr xs' =>
          rcases hr2 with ⟨o', ho', hoa', _, hcan, _⟩
          have heq := obj_eq_of_addr_nodup hnd ho ho' (hoa.trans hoa'.symm)
          subst heq
          have : arrayTag ≤ 244 := hcan.2.2.2.2.2.1 ▸ ht244
          exact absurd this (by decide)
        | ctor c' fs' sc' =>
          rcases hr2 with ⟨_, _, _, hbv⟩ | ⟨_, o', ho', hoa', _, ht', _, _, hfr'⟩
          · exact boxNat_and1_ne_zero c' (hbv ▸ hbv0)
          · have heq := obj_eq_of_addr_nodup hnd ho ho' (hoa.trans hoa'.symm)
            subst heq
            simp only [valNodes] at hlt
            obtain ⟨p, hp, q, hq, b, hlt', hrp, hrq⟩ :=
              listValNodes_lt_imp_exists hfr hfr' (by omega)
            have hpsz : valNodes p < valNodes (PVal.ctor c fs sc) := by
              have := listValNodes_mem_le hp
              simp only [valNodes]; omega
            exact ih (valNodes p) (by omega) p q b (Nat.le_refl _) hlt' hrp hrq
    | arr xs =>
      rcases hr1 with ⟨o, ho, hoa, hwf, hcan, hfr⟩
      have htagA : o.tag = arrayTag := hcan.2.2.2.2.2.1
      cases pv' with
      | erased =>
        dsimp only [ObjRep] at hr2
        exact absurd (hr2 ▸ hbv0) (by decide)
      | bits w' v' =>
        rcases hr2 with ⟨hw', hbv⟩ | ⟨_, o', ho', hoa', _, ht', _⟩
        · exact bv64_tagged_bits_and1 hw' v' (hbv ▸ hbv0)
        · have heq := obj_eq_of_addr_nodup hnd ho ho' (hoa.trans hoa'.symm)
          subst heq
          have : arrayTag = 0 := htagA.symm.trans ht'
          exact absurd this (by decide)
      | nat m =>
        dsimp only [ObjRep, natRep] at hr2
        split at hr2
        · exact boxNat_and1_ne_zero m (hr2 ▸ hbv0)
        · rcases hr2 with ⟨_, o', ho', hoa', hc⟩
          have heq := obj_eq_of_addr_nodup hnd ho ho' (hoa.trans hoa'.symm)
          subst heq
          have : arrayTag = mpzTag := htagA.symm.trans hc.2.1
          exact absurd this (by decide)
      | str s =>
        rcases hr2 with ⟨o', ho', hoa', _, hcan', _⟩
        have heq := obj_eq_of_addr_nodup hnd ho ho' (hoa.trans hoa'.symm)
        subst heq
        have : arrayTag = stringTag := htagA.symm.trans hcan'.2.2.2.2.2.1
        exact absurd this (by decide)
      | barr bs =>
        rcases hr2 with ⟨o', ho', hoa', _, hcan', _⟩
        have heq := obj_eq_of_addr_nodup hnd ho ho' (hoa.trans hoa'.symm)
        subst heq
        have : arrayTag = sarrayTag := htagA.symm.trans hcan'.2.2.2.2.2.1
        exact absurd this (by decide)
      | int _ => exact False.elim hr2
      | clo _ _ _ => exact False.elim hr2
      | ctor c' fs' sc' =>
        rcases hr2 with ⟨_, _, _, hbv⟩ | ⟨_, o', ho', hoa', _, _, ht244, _⟩
        · exact boxNat_and1_ne_zero c' (hbv ▸ hbv0)
        · have heq := obj_eq_of_addr_nodup hnd ho ho' (hoa.trans hoa'.symm)
          subst heq
          have : arrayTag ≤ 244 := htagA ▸ ht244
          exact absurd this (by decide)
      | arr xs' =>
        rcases hr2 with ⟨o', ho', hoa', _, _, hfr'⟩
        have heq := obj_eq_of_addr_nodup hnd ho ho' (hoa.trans hoa'.symm)
        subst heq
        simp only [valNodes] at hlt
        obtain ⟨p, hp, q, hq, b, hlt', hrp, hrq⟩ :=
          listValNodes_lt_imp_exists hfr hfr' (by omega)
        have hpsz : valNodes p < valNodes (PVal.arr xs) := by
          have := listValNodes_mem_le hp
          simp only [valNodes]; omega
        exact ih (valNodes p) (by omega) p q b (Nat.le_refl _) hlt' hrp hrq
    | _ => simp [valNodes] at hgt

private theorem objFieldsRep_mem {ps : List PVal} {bs : List (BitVec 64)} {objs : List LcnfObj}
    {b : BitVec 64} (h : objFieldsRep ps bs objs) (hb : b ∈ bs) :
    ∃ p ∈ ps, ObjRep p b objs := by
  induction ps generalizing bs with
  | nil => cases bs with | nil => cases hb | cons _ _ => exact False.elim h
  | cons q qs ih =>
    cases bs with
    | nil => exact False.elim h
    | cons x xs =>
      dsimp only [objFieldsRep] at h
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact ⟨q, List.mem_cons_self, h.1⟩
      · obtain ⟨r, hr, hrep⟩ := ih h.2 hb'
        exact ⟨r, List.mem_cons_of_mem _ hr, hrep⟩

theorem objRep_arr_not_in_fields {xs : List PVal} {bv : BitVec 64} {objs : List LcnfObj}
    (hnd : (objs.map LcnfObj.addr).Nodup)
    {o : LcnfObj} (ho : o ∈ objs) (_hoa : o.addr = bv) (hwf : o.Wf) (hcan : ArrCanon o)
    (hfr : objFieldsRep xs o.fields objs) :
    o.addr ∉ o.fields := by
  intro hmem
  obtain ⟨p, hp, hrep⟩ := objFieldsRep_mem hfr hmem
  have hlt : valNodes p < valNodes (PVal.arr xs) := by
    have := listValNodes_mem_le hp
    simp only [valNodes]; omega
  have harr : ObjRep (.arr xs) o.addr objs := ⟨o, ho, rfl, hwf, hcan, hfr⟩
  exact objRep_not_smaller hnd (valNodes (.arr xs)) (.arr xs) p o.addr
    (Nat.le_refl _) hlt harr hrep

theorem objRep_ctor_not_in_fields {cidx : Nat} {fs : List PVal} {sc : List UInt8}
    {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup)
    {o : LcnfObj} (ho : o ∈ objs) (hwf : o.Wf) (ht : o.tag = cidx) (ht244 : o.tag ≤ 244)
    (hsc : o.scalarData = sc) (hne : ¬(fs = [] ∧ sc = []))
    (hfr : objFieldsRep fs o.fields objs) :
    o.addr ∉ o.fields := by
  intro hmem
  obtain ⟨p, hp, hrep⟩ := objFieldsRep_mem hfr hmem
  have hlt : valNodes p < valNodes (.ctor cidx fs sc) := by
    have := listValNodes_mem_le hp
    simp only [valNodes]; omega
  have hctor : ObjRep (.ctor cidx fs sc) o.addr objs :=
    Or.inr ⟨hne, o, ho, rfl, hwf, ht, ht244, hsc, hfr⟩
  exact objRep_not_smaller hnd (valNodes (.ctor cidx fs sc)) (.ctor cidx fs sc) p o.addr
    (Nat.le_refl _) hlt hctor hrep

/-! ## 4. `HeapClean`, `Backed`, `RcFrame`, and `RcInv` -/

/-- Full heap-well-formedness bundle required across Perceus steps (`HInv` plus object well-formedness,
heap closure, worklist capacity, and RC bound). -/
@[expose] def HInvFull (rt : BitVec 64) (σ : HState) : Prop :=
  HInv rt σ ∧
  (∀ o ∈ σ.objs, o.Wf) ∧
  lcnfHeapClosed σ.objs ∧
  σ.objs.length ≤ σ.st.workCap ∧
  (∀ o ∈ σ.objs, o.rc.toNat < 2 ^ 31 - 1)

/-- Well-formed Tier-H state plus unique heap object addresses. -/
@[expose] def HeapClean (rt : BitVec 64) (σ : HState) : Prop :=
  HInvFull rt σ ∧ (σ.objs.map LcnfObj.addr).Nodup

/-- Heap pointer `a` is kept alive in `objs` by persistence (`rc = 0`)
or reachability from `roots`. -/
@[expose] def Backed (objs : List LcnfObj) (roots : List (BitVec 64)) (a : BitVec 64) : Prop :=
  (∃ o ∈ objs, o.addr = a ∧ o.rc = 0#32) ∨ ∃ r ∈ roots, NonPersistReach objs r a

/-- Owned heap handles contributed by one `RcVar` in `RcCtx`. -/
@[expose] def varHandles (envH : HValEnv) (v : RcVar) : List (BitVec 64) :=
  if v.noRc || v.persistent || v.resetTok || v.owned == 0 then []
  else match envH v.id with
    | some (_, w) => match w.toBV64? with
      | some bv => if (bv &&& 1#64) == 0#64 then List.replicate v.owned bv else []
      | none => []
    | none => []

/-- Owned heap handles contributed by all variables in `ctx`. -/
@[expose] def localHandles (ctx : RcCtx) (envH : HValEnv) : List (BitVec 64) :=
  (ctx.vars.map (varHandles envH)).flatten

/-- Owned heap handles contributed by all variables in `ctx` except variable `skipId`. -/
@[expose] def localHandlesExcept (ctx : RcCtx) (envH : HValEnv) (skipId : Nat) :
    List (BitVec 64) :=
  ((ctx.vars.filter (fun v => v.id != skipId)).map (varHandles envH)).flatten

/-- Ghost RC tracking state matching `RcCtx`, pure env `envP`, and Tier-H env `envH`. -/
structure RcFrame where
  ctx : RcCtx
  envP : PValEnv
  envH : HValEnv
  extH : List (BitVec 64)
  ghostH : List (BitVec 64)

/-- Total active handle multiset tracked by `rf`. -/
@[expose] def frameHandles (rf : RcFrame) : List (BitVec 64) :=
  localHandles rf.ctx rf.envH ++ rf.extH ++ rf.ghostH

/-- Per-variable ownership, representation, exclusivity, and borrow-backing invariant. -/
@[expose] def VarInv (v : RcVar) (rf : RcFrame) (objs : List LcnfObj) : Prop :=
  v.isLive = true →
    ∃ pv w,
      rf.envP v.id = some pv ∧
      rf.envH v.id = some (v.ty, w) ∧
      ValRep v.ty pv w objs ∧
      (¬v.ty.isScalar →
        ∃ bv : BitVec 64, w = Word.i64 bv ∧
          (v.noRc = true → (bv &&& 1#64) ≠ 0#64) ∧
          (v.persistent = true → (bv &&& 1#64) = 0#64 →
            ∃ o ∈ objs, o.addr = bv ∧ o.rc = 0#32) ∧
          (v.excl = true →
            v.noRc = false ∧ v.persistent = false ∧ v.owned = 1 ∧
              ((bv &&& 1#64) = 0#64 → ∃ o ∈ objs, o.addr = bv ∧ o.rc = 1#32)) ∧
          (v.noRc = false → v.persistent = false → v.borrowed = true →
            (bv &&& 1#64) = 0#64 →
              Backed objs (frameHandles rf) bv ∧
              match v.parent? with
              | none => Backed objs (rf.extH ++ rf.ghostH) bv
              | some p => ∃ pv, pv ∈ rf.ctx.vars ∧ pv.id = p ∧
                  pv.noRc = false ∧ pv.persistent = false ∧
                  (0 < pv.owned ∨ pv.borrowed = true) ∧
                  Backed objs ((match rf.envH p with
                    | some (_, w) => match w.toBV64? with | some bp => [bp] | none => []
                    | none => []) ++ (rf.extH ++ rf.ghostH)) bv))

/-- Invariant for pending `isShared` predicates `(b, x)` recorded in `ctx.sharedPreds`. -/
@[expose] def SharedPredInv (rf : RcFrame) (objs : List LcnfObj) : Prop :=
  ∀ p ∈ rf.ctx.sharedPreds, ∀ vb vx,
    rf.ctx.get? p.1 = some vb →
    rf.ctx.get? p.2 = some vx →
    vb.isLive = true →
    vx.noRc = false →
    vx.persistent = false →
    (((rf.envP p.1).bind PVal.tag? = some 0 →
      ∃ bv : BitVec 64,
        rf.envH p.2 = some (vx.ty, Word.i64 bv) ∧
        (bv &&& 1#64) = 0#64 ∧
        (0 < vx.owned →
          nonPersistRefs objs bv +
            (localHandlesExcept rf.ctx rf.envH p.2 ++ rf.extH ++ rf.ghostH).count bv = 0 ∧
          ∃ o ∈ objs, o.addr = bv ∧ o.rc.toNat = vx.owned)) ∧
     ((rf.envP p.1).bind PVal.tag? = some 1 →
      0 < vx.owned →
      ∃ bv : BitVec 64,
        rf.envH p.2 = some (vx.ty, Word.i64 bv) ∧
        (bv &&& 1#64) = 0#64 ∧
        ∃ o ∈ objs, o.addr = bv ∧ (o.rc = 0#32 ∨ vx.owned < o.rc.toNat)))

/-- Combined heap and Perceus RC soundness invariant at runtime base `rt`. -/
@[expose] def RcInv (rt : BitVec 64) (rf : RcFrame) (σ : HState) : Prop :=
  HeapClean rt σ ∧
  (rf.ctx.vars.map RcVar.id).Nodup ∧
  HandlesRcSound (frameHandles rf) σ.objs ∧
  (∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs) ∧
  SharedPredInv rf σ.objs

/-! ## 5. Handle Counting, `Backed`, and `RcCtx` Structural Lemmas -/

theorem count_flatten {α : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ (xss : List (List α)), xss.flatten.count a = (xss.map (List.count a)).sum
  | [] => by simp
  | xs :: xss => by simp [List.flatten_cons, List.count_append, count_flatten a xss]

theorem varHandles_count_eq_zero_of_ne {envH : HValEnv} {v : RcVar} {a : BitVec 64}
    (hdiff : ∀ bv, envH v.id = some (v.ty, Word.i64 bv) → bv ≠ a)
    (ht : ∀ ty w, envH v.id = some (ty, w) → w.toBV64? = some a → w = Word.i64 a ∧ ty = v.ty) :
    (varHandles envH v).count a = 0 := by
  unfold varHandles
  split
  · simp
  · rcases he : envH v.id with _ | ⟨ty, w⟩
    · simp
    · rcases hw : w.toBV64? with _ | bv
      · simp [hw]
      · simp only [hw]
        split
        · by_cases hba : bv = a
          · subst hba
            obtain ⟨rfl, rfl⟩ := ht ty w he hw
            exact absurd rfl (hdiff bv he)
          · rw [List.count_eq_zero]
            intro hm
            exact hba (List.eq_of_mem_replicate hm).symm
        · simp

theorem varHandles_subset_eq {envH envH' : HValEnv} {v : RcVar}
    (heq : envH v.id = envH' v.id) : varHandles envH' v = varHandles envH v := by
  simp [varHandles, heq]

private theorem localHandles_perm_filter_list (vars : List RcVar)
    (hnd : (vars.map RcVar.id).Nodup) (envH : HValEnv) (v : RcVar) (hv : v ∈ vars) :
    ((vars.map (varHandles envH)).flatten).Perm
      (varHandles envH v ++
        ((vars.filter (fun x => x.id != v.id)).map (varHandles envH)).flatten) := by
  induction vars with
  | nil => cases hv
  | cons u us ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hndu := hnd.1
    have hndus := hnd.2
    rcases List.mem_cons.mp hv with rfl | hv'
    · have hflt : List.filter (fun x => x.id != v.id) (v :: us) = us := by
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [List.filter_eq_self.mpr]
        intro w hw
        exact bne_iff_ne.mpr fun heq => hndu ⟨w, hw, heq⟩
      simp [hflt]
    · have huv : u.id ≠ v.id := fun heq => hndu ⟨v, hv', heq.symm⟩
      have hubne : (u.id != v.id) = true := bne_iff_ne.mpr huv
      simp only [List.filter_cons, hubne, ↓reduceIte, List.map_cons, List.flatten_cons]
      have hih := ih hndus hv'
      exact (hih.append_left _).trans (List.perm_append_comm_assoc _ _ _)

theorem localHandles_perm_filter {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (envH : HValEnv) (v : RcVar) (hv : v ∈ ctx.vars) :
    (localHandles ctx envH).Perm (varHandles envH v ++ localHandlesExcept ctx envH v.id) :=
  localHandles_perm_filter_list ctx.vars hnd envH v hv

theorem localHandles_count_eq_add {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (envH : HValEnv) {v : RcVar} (hv : v ∈ ctx.vars) (a : BitVec 64) :
    (localHandles ctx envH).count a =
      (varHandles envH v).count a + (localHandlesExcept ctx envH v.id).count a := by
  rw [(localHandles_perm_filter hnd envH v hv).count_eq, List.count_append]

theorem localHandlesExcept_congr_env {ctx : RcCtx} {envH envH' : HValEnv} (x : Nat)
    (hother : ∀ y, y ≠ x → envH' y = envH y) :
    localHandlesExcept ctx envH' x = localHandlesExcept ctx envH x := by
  unfold localHandlesExcept
  congr 1
  apply List.map_congr_left
  intro v hv
  simp only [List.mem_filter, bne_iff_ne] at hv
  exact varHandles_subset_eq (hother v.id hv.2).symm

theorem localHandles_congr_var_env {ctx : RcCtx} {envH envH' : HValEnv} (x : Nat)
    (hother : ∀ y, y ≠ x → envH' y = envH y)
    (hx : ∀ v ∈ ctx.vars, v.id = x → varHandles envH' v = varHandles envH v) :
    localHandles ctx envH' = localHandles ctx envH := by
  unfold localHandles
  congr 1
  apply List.map_congr_left
  intro v hv
  by_cases hvx : v.id = x
  · exact hx v hv hvx
  · exact varHandles_subset_eq (hother v.id hvx).symm

theorem nonPersistReach_mono_pred {P : BitVec 64 → Prop} {objs objs' : List LcnfObj}
    (hpres : ∀ o ∈ objs, o.Wf → P o.addr →
      ∃ o' ∈ objs', o'.addr = o.addr ∧ o'.rc = o.rc ∧ o'.childFields = o.childFields)
    (hclosed : ∀ o ∈ objs, o.Wf → P o.addr → ∀ f ∈ o.childFields,
      (f &&& 1#64) = 0#64 → P f)
    (hwf : ∀ o ∈ objs, o.Wf)
    {r a : BitVec 64} (hr : P r) (hreach : NonPersistReach objs r a) :
    NonPersistReach objs' r a ∧ P a := by
  induction hreach with
  | refl h =>
    rcases h with ⟨o, ho, hoa, hnz⟩
    obtain ⟨o', ho', ha', hrc', _⟩ := hpres o ho (hwf o ho) (hoa ▸ hr)
    exact ⟨NonPersistReach.refl ⟨o', ho', ha'.trans hoa, hrc' ▸ hnz⟩, hr⟩
  | step _ hmem hv0 hnz ih =>
    rcases hmem with ⟨o, ho, hoa, hvcf⟩
    obtain ⟨ihr, hpu⟩ := ih
    obtain ⟨o', ho', ha', _, hcf'⟩ := hpres o ho (hwf o ho) (hoa ▸ hpu)
    have hpv : P _ := hclosed o ho (hwf o ho) (hoa ▸ hpu) _ hvcf hv0
    rcases hnz with ⟨ov, hov, hova, hovnz⟩
    obtain ⟨ov', hov', hva', hvrc', _⟩ := hpres ov hov (hwf ov hov) (hova ▸ hpv)
    exact ⟨NonPersistReach.step ihr ⟨o', ho', ha'.trans hoa, hcf'.symm ▸ hvcf⟩
      hv0 ⟨ov', hov', hva'.trans hova, hvrc' ▸ hovnz⟩, hpv⟩

theorem backed_trans_child {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup)
    (hcl : lcnfHeapClosed objs)
    (hpersist : ∀ p ∈ objs, p.rc = 0#32 → ∀ f ∈ p.childFields, (f &&& 1#64) = 0#64 →
      ∃ q ∈ objs, q.addr = f ∧ q.rc = 0#32)
    {roots : List (BitVec 64)} {a f : BitVec 64}
    (hb : Backed objs roots a) {o : LcnfObj} (ho : o ∈ objs) (hoa : o.addr = a)
    (hf : f ∈ o.childFields) (hf0 : (f &&& 1#64) = 0#64) :
    Backed objs roots f := by
  by_cases hrc0 : o.rc = 0#32
  · obtain ⟨q, hq, hqa, hqrc⟩ := hpersist o ho hrc0 f hf hf0
    exact Or.inl ⟨q, hq, hqa, hqrc⟩
  · rcases hb with ⟨p, hp, hpa, hprc⟩ | ⟨r, hr, hreach⟩
    · have := obj_eq_of_addr_nodup hnd hp ho (hpa.trans hoa.symm)
      subst this
      exact absurd hprc hrc0
    · obtain ⟨o', ho', ho'a⟩ := hcl o ho f hf hf0
      by_cases ho'rc : o'.rc = 0#32
      · exact Or.inl ⟨o', ho', ho'a, ho'rc⟩
      · exact Or.inr ⟨r, hr, NonPersistReach.step hreach ⟨o, ho, hoa, hf⟩ hf0
          ⟨o', ho', ho'a, ho'rc⟩⟩

theorem backed_trans_child_simple {objs : List LcnfObj}
    (hnd : (objs.map LcnfObj.addr).Nodup) (hcl : lcnfHeapClosed objs)
    {handles roots : List (BitVec 64)} (hrc : HandlesRcSound handles objs) {a f : BitVec 64}
    (hb : Backed objs roots a) {o : LcnfObj} (ho : o ∈ objs) (hoa : o.addr = a)
    (hf : f ∈ o.childFields) (hf0 : (f &&& 1#64) = 0#64) :
    Backed objs roots f :=
  backed_trans_child hnd hcl hrc.1 hb ho hoa hf hf0

theorem backed_mono_roots {objs : List LcnfObj} {r1 r2 : List (BitVec 64)} {a : BitVec 64}
    (hsub : ∀ r ∈ r1, r ∈ r2) (hb : Backed objs r1 a) : Backed objs r2 a := by
  rcases hb with h | ⟨r, hr, hreach⟩
  · exact Or.inl h
  · exact Or.inr ⟨r, hsub r hr, hreach⟩

theorem backed_mono_heap {P : BitVec 64 → Prop} {objs objs' : List LcnfObj}
    (hpres : ∀ o ∈ objs, o.Wf → P o.addr →
      ∃ o' ∈ objs', o'.addr = o.addr ∧ o'.rc = o.rc ∧ o'.childFields = o.childFields)
    (hclosed : ∀ o ∈ objs, o.Wf → P o.addr → ∀ f ∈ o.childFields,
      (f &&& 1#64) = 0#64 → P f)
    (hwf : ∀ o ∈ objs, o.Wf)
    {r1 r2 : List (BitVec 64)} (hsub : ∀ r ∈ r1, r ∈ r2 ∧ P r)
    {a : BitVec 64} (hpa : P a) (hb : Backed objs r1 a) :
    Backed objs' r2 a := by
  rcases hb with ⟨o, ho, hoa, hrc0⟩ | ⟨r, hr, hreach⟩
  · obtain ⟨o', ho', ha', hrc', _⟩ := hpres o ho (hwf o ho) (hoa ▸ hpa)
    exact Or.inl ⟨o', ho', ha'.trans hoa, hrc' ▸ hrc0⟩
  · obtain ⟨hr2, hpr⟩ := hsub r hr
    exact Or.inr ⟨r, hr2, (nonPersistReach_mono_pred hpres hclosed hwf hpr hreach).1⟩

theorem handlesRcSound_of_perm {h1 h2 : List (BitVec 64)} {objs : List LcnfObj}
    (hperm : h1.Perm h2) (hs : HandlesRcSound h1 objs) : HandlesRcSound h2 objs := by
  refine ⟨hs.1, fun y hy hpos => ?_⟩
  have hc := hperm.count_eq y.addr
  rw [← hc]
  exact hs.2 y hy hpos

theorem handlesRcSound_of_count_le {h1 h2 : List (BitVec 64)} {objs : List LcnfObj}
    (hle : ∀ a, h2.count a ≤ h1.count a) (hs : HandlesRcSound h1 objs) :
    HandlesRcSound h2 objs := by
  refine ⟨hs.1, fun y hy hpos => ?_⟩
  have h1y := hs.2 y hy hpos
  have hle_y := hle y.addr
  omega

theorem handlesRcSound_excl_unique {rf : RcFrame} {objs : List LcnfObj}
    (hndCtx : (rf.ctx.vars.map RcVar.id).Nodup)
    (hs : HandlesRcSound (frameHandles rf) objs)
    {v : RcVar} (hv : v ∈ rf.ctx.vars) (hno : v.noRc = false) (hpers : v.persistent = false)
    (hrtok : v.resetTok = false) (hown : v.owned = 1)
    {bv : BitVec 64} (hev : rf.envH v.id = some (v.ty, Word.i64 bv))
    {o : LcnfObj} (ho : o ∈ objs) (hwf : o.Wf) (hoa : o.addr = bv) (hrc1 : o.rc = 1#32) :
    nonPersistRefs objs bv = 0 ∧
    (localHandlesExcept rf.ctx rf.envH v.id ++ rf.extH ++ rf.ghostH).count bv = 0 ∧
    bv ∉ o.childFields := by
  have hb0 : (bv &&& 1#64) = 0#64 := hoa ▸ obj_addr_and1_zero hwf
  have htobv : (Word.i64 bv).toBV64? = some bv := rfl
  have hvh : varHandles rf.envH v = [bv] := by
    simp [varHandles, hno, hpers, hrtok, hown, hev, htobv, hb0]
  have hperm : (frameHandles rf).Perm
      (bv :: (localHandlesExcept rf.ctx rf.envH v.id ++ rf.extH ++ rf.ghostH)) := by
    unfold frameHandles
    have hp := localHandles_perm_filter hndCtx rf.envH v hv
    rw [hvh] at hp
    simpa [List.append_assoc] using hp.append_right (rf.extH ++ rf.ghostH)
  exact handlesRcSound_exclusive_no_aliases (handlesRcSound_of_perm hperm hs) ho hoa hrc1

private theorem put_go_nodup {v : RcVar} :
    ∀ {xs : List RcVar}, (xs.map RcVar.id).Nodup →
      ((RcCtx.put.go v xs).map RcVar.id).Nodup
  | [], _ => by simp [RcCtx.put.go]
  | u :: us, hnd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    unfold RcCtx.put.go
    split
    · next heq =>
      have hid : u.id = v.id := beq_iff_eq.mp heq
      simp only [List.map_cons, List.nodup_cons, List.mem_map, ← hid]
      exact hnd
    · next hne =>
      have hnev : u.id ≠ v.id := fun h => hne (beq_iff_eq.mpr h)
      have ih := put_go_nodup (v := v) hnd.2
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at ih ⊢
      refine ⟨?_, ih⟩
      rintro ⟨w, hw, heqw⟩
      have hmem : ∀ {xs : List RcVar} {w : RcVar}, w ∈ RcCtx.put.go v xs → w = v ∨ w ∈ xs := by
        intro xs
        induction xs with
        | nil => intro w hw'; simp [RcCtx.put.go] at hw'; exact Or.inl hw'
        | cons x xs ihx =>
          intro w hw'
          unfold RcCtx.put.go at hw'
          split at hw'
          · rcases List.mem_cons.mp hw' with rfl | h'
            · exact Or.inl rfl
            · exact Or.inr (List.mem_cons_of_mem _ h')
          · rcases List.mem_cons.mp hw' with rfl | h'
            · exact Or.inr List.mem_cons_self
            · rcases ihx h' with rfl | hm
              · exact Or.inl rfl
              · exact Or.inr (List.mem_cons_of_mem _ hm)
      rcases hmem hw with rfl | hmus
      · exact hnev heqw.symm
      · exact hnd.1 ⟨w, hmus, heqw⟩

theorem RcCtx.put_nodup {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup) (v : RcVar) :
    ((ctx.put v).vars.map RcVar.id).Nodup :=
  put_go_nodup hnd

private theorem put_go_mem_iff {v w : RcVar} :
    ∀ {xs : List RcVar}, (xs.map RcVar.id).Nodup →
      (w ∈ RcCtx.put.go v xs ↔ w = v ∨ (w ∈ xs ∧ w.id ≠ v.id))
  | [], _ => by simp [RcCtx.put.go]
  | x :: xs, hnd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    unfold RcCtx.put.go
    split
    · next heq =>
      have hxid : x.id = v.id := beq_iff_eq.mp heq
      constructor
      · intro h
        rcases List.mem_cons.mp h with rfl | hxs
        · exact Or.inl rfl
        · refine Or.inr ⟨List.mem_cons_of_mem _ hxs, fun hid => ?_⟩
          exact hnd.1 ⟨w, hxs, hid.trans hxid.symm⟩
      · rintro (rfl | ⟨hm, hne⟩)
        · exact List.mem_cons_self
        · rcases List.mem_cons.mp hm with rfl | hxs
          · exact absurd hxid hne
          · exact List.mem_cons_of_mem _ hxs
    · next hne =>
      have hxne : x.id ≠ v.id := fun h => hne (beq_iff_eq.mpr h)
      have ih := put_go_mem_iff (v := v) (w := w) hnd.2
      constructor
      · intro h
        rcases List.mem_cons.mp h with rfl | hxs
        · exact Or.inr ⟨List.mem_cons_self, hxne⟩
        · rcases ih.mp hxs with rfl | ⟨hm, hwne⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨List.mem_cons_of_mem _ hm, hwne⟩
      · rintro (rfl | ⟨hm, hwne⟩)
        · exact List.mem_cons_of_mem _ (ih.mpr (Or.inl rfl))
        · rcases List.mem_cons.mp hm with rfl | hxs
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih.mpr (Or.inr ⟨hxs, hwne⟩))

theorem RcCtx.put_mem_iff {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {v w : RcVar} : w ∈ (ctx.put v).vars ↔ w = v ∨ (w ∈ ctx.vars ∧ w.id ≠ v.id) :=
  put_go_mem_iff hnd

private theorem find?_id_mem_iff (v : RcVar) :
    ∀ (vars : List RcVar), (vars.map RcVar.id).Nodup →
      (List.find? (fun x => x.id == v.id) vars = some v ↔ v ∈ vars)
  | [], _ => by simp
  | u :: us, hnd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.find?_cons]
    by_cases huv : u.id = v.id
    · have hbeq : (u.id == v.id) = true := beq_iff_eq.mpr huv
      rw [hbeq]
      constructor
      · intro h; simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_self
      · intro hm
        rcases List.mem_cons.mp hm with rfl | hus
        · rfl
        · exact absurd huv (fun heq => hnd.1 ⟨v, hus, heq.symm⟩)
    · have hbeq : (u.id == v.id) = false := by simp [huv]
      rw [hbeq, find?_id_mem_iff v us hnd.2]
      constructor
      · intro hm; exact List.mem_cons_of_mem _ hm
      · intro hm
        rcases List.mem_cons.mp hm with rfl | hus
        · exact absurd rfl huv
        · exact hus

theorem RcCtx.mem_get?_iff {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup) {v : RcVar} :
    ctx.get? v.id = some v ↔ v ∈ ctx.vars :=
  find?_id_mem_iff v ctx.vars hnd

theorem RcCtx.get?_mem {ctx : RcCtx} {x : Nat} {v : RcVar} (h : ctx.get? x = some v) :
    v ∈ ctx.vars ∧ v.id = x := by
  unfold RcCtx.get? at h
  exact ⟨List.mem_of_find?_eq_some h, beq_iff_eq.mp (by simpa using List.find?_some h)⟩

theorem RcCtx.put_get? {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (v : RcVar) (x : Nat) :
    (ctx.put v).get? x = if x == v.id then some v else ctx.get? x := by
  have hnd' := ctx.put_nodup hnd v
  split
  · next heq =>
    have hid : x = v.id := beq_iff_eq.mp heq
    subst hid
    exact (RcCtx.mem_get?_iff hnd').mpr ((ctx.put_mem_iff hnd).mpr (Or.inl rfl))
  · next hne =>
    have hxne : x ≠ v.id := fun h => hne (beq_iff_eq.mpr h)
    cases hcx : ctx.get? x with
    | none =>
      cases hpx : (ctx.put v).get? x with
      | none => rfl
      | some w =>
        obtain ⟨hwm, rfl⟩ := RcCtx.get?_mem hpx
        rcases (ctx.put_mem_iff hnd).mp hwm with rfl | ⟨hwc, _⟩
        · exact absurd rfl hxne
        · have := (RcCtx.mem_get?_iff hnd).mpr hwc
          rw [this] at hcx; cases hcx
    | some w =>
      obtain ⟨hwc, rfl⟩ := RcCtx.get?_mem hcx
      exact (RcCtx.mem_get?_iff hnd').mpr ((ctx.put_mem_iff hnd).mpr (Or.inr ⟨hwc, hxne⟩))

private theorem filter_put_go_eq (v : RcVar) :
    ∀ (vars : List RcVar),
      List.filter (fun u => u.id != v.id) (RcCtx.put.go v vars) =
      List.filter (fun u => u.id != v.id) vars
  | [] => by simp [RcCtx.put.go]
  | u :: us => by
    unfold RcCtx.put.go
    split
    · next heq =>
      have hid : u.id = v.id := beq_iff_eq.mp heq
      simp only [List.filter_cons, bne_self_eq_false, hid, Bool.false_eq_true, ↓reduceIte]
    · next hne =>
      have hne' : (u.id != v.id) = true := bne_iff_ne.mpr fun h => hne (beq_iff_eq.mpr h)
      simp only [List.filter_cons, hne', ↓reduceIte]
      congr 1
      exact filter_put_go_eq v us

theorem localHandlesExcept_put {ctx : RcCtx} (_hnd : (ctx.vars.map RcVar.id).Nodup)
    (envH : HValEnv) (v : RcVar) :
    localHandlesExcept (ctx.put v) envH v.id = localHandlesExcept ctx envH v.id := by
  unfold localHandlesExcept RcCtx.put
  dsimp only
  rw [filter_put_go_eq]

theorem localHandles_put_perm {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (envH : HValEnv) (v : RcVar) :
    (localHandles (ctx.put v) envH).Perm
      (varHandles envH v ++ localHandlesExcept ctx envH v.id) := by
  have hnd' := ctx.put_nodup hnd v
  have hvmem : v ∈ (ctx.put v).vars := (ctx.put_mem_iff hnd).mpr (Or.inl rfl)
  have hp := localHandles_perm_filter hnd' envH v hvmem
  rwa [localHandlesExcept_put hnd] at hp

theorem localHandles_invalidateChildren {ctx : RcCtx} (envH : HValEnv) (p : Nat) :
    localHandles (ctx.invalidateChildren p) envH = localHandles ctx envH := by
  unfold localHandles RcCtx.invalidateChildren
  dsimp only
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  dsimp only [Function.comp_def]
  split <;> simp [varHandles]

private theorem filter_map_id_congr {α : Type} (q : α → Bool) (f : α → α)
    (hq : ∀ x, q (f x) = q x) :
    ∀ xs : List α, List.filter q (xs.map f) = (xs.filter q).map f
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.filter_cons, hq]
    by_cases hx : q x = true
    · simp [hx, filter_map_id_congr q f hq xs]
    · simp [hx, filter_map_id_congr q f hq xs]

theorem localHandlesExcept_invalidateChildren {ctx : RcCtx} (envH : HValEnv) (p s : Nat) :
    localHandlesExcept (ctx.invalidateChildren p) envH s = localHandlesExcept ctx envH s := by
  unfold localHandlesExcept RcCtx.invalidateChildren
  dsimp only
  have hflt := filter_map_id_congr (fun v : RcVar => v.id != s)
    (fun v : RcVar => if (v.parent? == some p) = true then
      { v with borrowed := false, parent? := none } else v)
    (fun v => by split <;> rfl) ctx.vars
  rw [hflt, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  dsimp only [Function.comp_def]
  split <;> simp [varHandles]

@[expose] public def nonScalarWords (ps : List LcParam) (as : List Word) : List Word :=
  (ps.zip as).filterMap fun (p, w) => if !p.ty.isScalar then some w else none

@[expose] public def setBytesTrue (m : List Bool) (bOff nb : Nat) : List Bool :=
  List.ofFn fun (i : Fin m.length) =>
    if bOff ≤ i.1 && i.1 < bOff + nb then true else m[i]

@[expose] public def initScalarBytes (sm : List (Nat × Nat × List Bool))
    (x n off nb : Nat) : List (Nat × Nat × List Bool) :=
  sm.filterMap fun (y, sz, m) =>
    if y == x then
      let m' := setBytesTrue m (8 * (n - sz) + off) nb
      if m'.all id then none else some (y, sz, m')
    else some (y, sz, m)

@[expose] public def scalarSlotReady (sm : List (Nat × Nat × List Bool))
    (x n off nb : Nat) : Bool :=
  match sm.find? (·.1 == x) with
  | none => true
  | some (_, sz, m) =>
    let bOff := 8 * (n - sz) + off
    sz ≤ n && bOff + nb ≤ m.length &&
      (List.range nb).all fun d => (m[bOff + d]?).getD false

@[expose] public def scalarSlotInBounds (sm : List (Nat × Nat × List Bool))
    (x n off nb : Nat) : Bool :=
  match sm.find? (·.1 == x) with
  | none => true
  | some (_, sz, m) => sz ≤ n && 8 * (n - sz) + off + nb ≤ m.length

@[expose] public def isVarScalarInit (sm : List (Nat × Nat × List Bool)) (x : Nat) : Bool :=
  sm.all (·.1 != x)

@[expose] public def argScalarInit (sm : List (Nat × Nat × List Bool)) : LcArg → Bool
  | .erased => true
  | .var x => isVarScalarInit sm x

@[expose] public def ctorBindMask (x : Nat) (ci : LcCtor)
    (sm : List (Nat × Nat × List Bool)) : List (Nat × Nat × List Bool) :=
  let sm' := sm.filter (·.1 != x)
  let len := 8 * ci.usize + ci.ssize
  if !ci.isScalar && 0 < len then (x, ci.size, List.replicate len false) :: sm' else sm'

@[expose] public def valScalarWf (sm : List (Nat × Nat × List Bool)) (ty : LcTy) :
    LcVal → Bool
  | .lit (.nat _) => true
  | .lit (.scalar _) => true
  | .erased => true
  | .ctor _ as => as.all (argScalarInit sm)
  | .oproj _ _ => true
  | .uproj i y => scalarSlotReady sm y i 0 8
  | .sproj n off y => scalarSlotReady sm y n off ty.toTTy.bytes
  | .box _ y => isVarScalarInit sm y
  | .unbox y => isVarScalarInit sm y
  | .isShared _ => true
  | .fap _ as => as.all (argScalarInit sm)
  | _ => false

end
