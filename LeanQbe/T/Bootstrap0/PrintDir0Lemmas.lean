module

public import LeanQbe.T.Bootstrap0.PrintDir0
public import LeanQbe.T.Bootstrap0.Bridge0
public import LeanQbe.T.Amd64.PrintAsm0
public import LeanQbe.T.Amd64.PrintAsm0Lemmas
public import Kraken.X64.PrintATT

/-!
# Bit-for-Bit Equivalence Proofs for `PrintDir0` (`PrintDir0Lemmas`)

Proves exact byte-for-byte equivalence between the closure-free `Dir0 → ByteArray` printer
`LeanQbe.T.Bootstrap0.PrintDir0` and `PrintAsm0.printAsm0 ∘ Bridge0.dir0ToAmd64` (and hence
`Kraken.X64.toATT` via `PrintAsm0Lemmas`):

* `printDir0Bytes_eq_printAsm0` / `printDir0Bytes_eq_toATT`: single-directive byte equivalence
  across all `27` constructors of `Dir0`.
* `printDirs0Bytes_eq_toATT`: full program byte equivalence against
  `Kraken.X64.toATT (Bridge0.toAmd64Program symName ds)`.
* `printDirs0LinesBytes_eq_toATT` / `printModule0Bytes_eq_toATT`: newline-terminated program
  and whole-module (`.text\n` + `.globl`) equivalence.

All proofs use strictly standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and
zero private-import bypasses.
-/

set_option autoImplicit false

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T.Amd64
open Kraken.X64

/-! ## 1. Symbol-Table Validity Predicates -/

/-- Exact match between `(symBytes, symOffs)` entry `sym` and `symName sym`. -/
@[expose] public def SymSliceMatch (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) (sym : Sym0) : Prop :=
  let idx := 2 * sym.toNat
  idx + 1 < symOffs.size ∧
    let off := symOffs[idx]!
    let len := symOffs[idx + 1]!
    off + len ≤ symBytes.size ∧
      symBytes.extract off (off + len) = (symName sym).toUTF8

/-- Per-directive symbol-table validity hypothesis for `printDir0Bytes`. -/
@[expose] public def Dir0SymsOk (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) (d : Dir0) : Prop :=
  symBytes.size < 2 ^ 64 ∧ symOffs.size < 2 ^ 64 ∧
    match d with
    | .label (.sym id) | .jmp (.sym id) | .jcc _ (.sym id) | .callSym id =>
      SymSliceMatch symBytes symOffs symName id
    | _ => True

/-- Whole-table symbol validity for `nSyms` consecutive symbol IDs `0 .. nSyms - 1`. -/
@[expose] public def SymTabOk (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) (nSyms : Nat) : Prop :=
  symBytes.size < 2 ^ 64 ∧ symOffs.size < 2 ^ 64 ∧ 2 * nSyms ≤ symOffs.size ∧
    ∀ sym : Sym0, sym.toNat < nSyms → SymSliceMatch symBytes symOffs symName sym

/-- Decidable symbol-ID bound check for a single `Dir0`. -/
@[expose] public def dir0SymsLt (d : Dir0) (nSyms : Nat) : Bool :=
  match d with
  | .label (.sym id) | .jmp (.sym id) | .jcc _ (.sym id) | .callSym id =>
    decide (id.toNat < nSyms)
  | _ => true

/-- `SymTabOk` + `dir0SymsLt d nSyms = true` implies `Dir0SymsOk`. -/
public theorem SymTabOk.dir0SymsOk {symBytes : ByteArray} {symOffs : Array Nat}
    {symName : Sym0 → Sym} {nSyms : Nat} {d : Dir0}
    (htab : SymTabOk symBytes symOffs symName nSyms)
    (hbound : dir0SymsLt d nSyms = true) :
    Dir0SymsOk symBytes symOffs symName d := by
  refine ⟨htab.1, htab.2.1, ?_⟩
  cases d with
  | label l | jmp l | jcc _ l =>
    cases l with
    | sym id => exact htab.2.2.2 id (of_decide_eq_true hbound)
    | loc _ _ => trivial
  | callSym id => exact htab.2.2.2 id (of_decide_eq_true hbound)
  | _ => trivial

/-! ## 2. `ByteArray` and `String.toUTF8` Algebra Helpers -/

private theorem ba_eq_of_data_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) :
    a = b := by
  cases a with
  | mk da =>
    cases b with
    | mk db =>
      congr 1
      exact Array.ext' h

private theorem ba_push_data_toList (ba : ByteArray) (b : UInt8) :
    (ba.push b).data.toList = ba.data.toList ++ [b] := by
  cases ba with
  | mk ds =>
    dsimp only [ByteArray.push]
    exact Array.toList_push

private theorem ba_push_eq_append (ba : ByteArray) (b : UInt8) (s : String)
    (h : s.toUTF8.data.toList = [b]) : ba.push b = ba ++ s.toUTF8 := by
  apply ba_eq_of_data_toList
  rw [ba_push_data_toList, ByteArray.toList_data_append, h]

private theorem toUTF8_append (s t : String) : (s ++ t).toUTF8 = s.toUTF8 ++ t.toUTF8 := by
  rw [String.toUTF8_eq_toByteArray, String.toUTF8_eq_toByteArray,
    String.toUTF8_eq_toByteArray, String.toByteArray_append]

private theorem toUTF8_empty : "".toUTF8 = ByteArray.empty := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_empty]

private theorem emptyWithCapacity_eq_empty (c : Nat) :
    ByteArray.emptyWithCapacity c = ByteArray.empty := rfl

private theorem ite_true_eq {p : Prop} [Decidable p] {α : Sort _} {a b : α} (h : p) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

private theorem dite_true_eq {p : Prop} [Decidable p] {α : Sort _} {a : p → α} {b : ¬ p → α}
    (h : p) : (if h' : p then a h' else b h') = a h := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

private theorem fromUTF8!_toUTF8 (s : String) : String.fromUTF8! s.toUTF8 = s := by
  dsimp only [String.fromUTF8!]
  rw [String.toUTF8_eq_toByteArray, dite_true_eq s.isValidUTF8, String.fromUTF8_eq_ofByteArray]

private theorem toUTF8_data_length (s : String) :
    s.toUTF8.data.toList.length = s.utf8ByteSize := by
  rw [String.toUTF8_eq_toByteArray, Array.length_toList]
  rfl

private theorem list_drop_eq_cons {α : Type} :
    ∀ (xs : List α) (i : Nat) (h : i < xs.length),
      xs.drop i = xs[i] :: xs.drop (i + 1)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, h => list_drop_eq_cons xs i (Nat.lt_of_succ_lt_succ h)

private theorem emitStrLoop_eq (s : String) :
    ∀ (k i : Nat) (ba : ByteArray),
      k = s.utf8ByteSize - i →
      (PrintAsm0.emitStrLoop ba s i).data.toList =
        ba.data.toList ++ s.toUTF8.data.toList.drop i
  | 0, i, ba, hk => by
    have hge : ¬ i < s.utf8ByteSize := by omega
    rw [PrintAsm0.emitStrLoop.eq_def]
    simp only [hge, ↓reduceDIte]
    have hlen := toUTF8_data_length s
    have hdrop : s.toUTF8.data.toList.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop, List.append_nil]
  | k + 1, i, ba, hk => by
    have hlt : i < s.utf8ByteSize := by omega
    rw [PrintAsm0.emitStrLoop.eq_def]
    simp only [hlt, ↓reduceDIte]
    have hstep : k = s.utf8ByteSize - Nat.add i 1 := by
      rw [Nat.add_eq]; omega
    have ih := emitStrLoop_eq s k (Nat.add i 1) (ba.push (s.getUTF8Byte ⟨i⟩ hlt)) hstep
    rw [ih, ba_push_data_toList, List.append_assoc]
    congr 1
    have hlen : i < s.toUTF8.data.toList.length := by
      rw [toUTF8_data_length]; exact hlt
    have hbyte : s.getUTF8Byte ⟨i⟩ hlt = s.toUTF8.data.toList[i]'hlen := by
      rw [String.getUTF8Byte_eq_getElem]
      simp only [String.toUTF8_eq_toByteArray]
      rfl
    rw [hbyte, List.cons_append, List.nil_append, Nat.add_eq]
    exact (list_drop_eq_cons s.toUTF8.data.toList i hlen).symm

private theorem emitStr_eq (ba : ByteArray) (s : String) :
    PrintAsm0.emitStr ba s = ba ++ s.toUTF8 := by
  apply ba_eq_of_data_toList
  dsimp only [PrintAsm0.emitStr]
  rw [emitStrLoop_eq s s.utf8ByteSize 0 ba (by omega),
    List.drop_zero, ByteArray.toList_data_append]

/-! ## 3. Decimal Formatting & Primitive Equivalence (`PrintDir0` = `PrintAsm0`) -/

private theorem pow10Up_eq_asm0 :
    ∀ (k : Nat) (q p : UInt64), k ≤ 20 →
      PrintDir0.pow10Up (UInt32.ofNat k) q p = PrintAsm0.pow10Up k q p
  | 0, q, p, _ => by
    rw [PrintDir0.pow10Up.eq_def]
    have hz : (UInt32.ofNat 0 = 0) := rfl
    simp only [hz, ↓reduceDIte]
    rfl
  | k + 1, q, p, hk => by
    rw [PrintDir0.pow10Up.eq_def]
    have hne : UInt32.ofNat (k + 1) ≠ 0 := by
      intro h
      have hn := congrArg UInt32.toNat h
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hn
      exact Nat.succ_ne_zero k hn
    have hsub : UInt32.ofNat (k + 1) - 1 = UInt32.ofNat k := by
      apply UInt32.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      change (UInt32.ofNat (k + 1) - 1).toNat = (UInt32.ofNat k).toNat
      have h1 : (1 : UInt32) ≤ UInt32.ofNat (k + 1) := by
        rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        change 1 ≤ k + 1; omega
      rw [UInt32.toNat_sub_of_le _ _ h1, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      change k + 1 - 1 = k; omega
    simp only [hne, ↓reduceDIte, hsub]
    dsimp only [PrintAsm0.pow10Up]
    by_cases hle : p ≤ q
    · simp only [hle, ↓reduceIte]
      exact pow10Up_eq_asm0 k q (p * 10) (by omega)
    · simp only [hle, ↓reduceIte]

private theorem emitPowDown_eq_asm0 :
    ∀ (k : Nat) (ba : ByteArray) (n p : UInt64), k ≤ 20 →
      PrintDir0.emitPowDown (UInt32.ofNat k) ba n p = PrintAsm0.emitPowDown k ba n p
  | 0, ba, n, p, _ => by
    rw [PrintDir0.emitPowDown.eq_def]
    have hz : (UInt32.ofNat 0 = 0) := rfl
    simp only [hz, ↓reduceDIte]
    rfl
  | k + 1, ba, n, p, hk => by
    rw [PrintDir0.emitPowDown.eq_def]
    have hne : UInt32.ofNat (k + 1) ≠ 0 := by
      intro h
      have hn := congrArg UInt32.toNat h
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hn
      exact Nat.succ_ne_zero k hn
    have hsub : UInt32.ofNat (k + 1) - 1 = UInt32.ofNat k := by
      apply UInt32.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      change (UInt32.ofNat (k + 1) - 1).toNat = (UInt32.ofNat k).toNat
      have h1 : (1 : UInt32) ≤ UInt32.ofNat (k + 1) := by
        rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        change 1 ≤ k + 1; omega
      rw [UInt32.toNat_sub_of_le _ _ h1, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      change k + 1 - 1 = k; omega
    simp only [hne, ↓reduceDIte, hsub]
    dsimp only [PrintAsm0.emitPowDown]
    by_cases hp : p == 1
    · simp only [hp, ↓reduceIte]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      exact emitPowDown_eq_asm0 k (ba.push (48 + (n / p).toUInt8)) (n % p) (p / 10) (by omega)

private theorem emitU64Dec_eq_asm0 (ba : ByteArray) (n : UInt64) :
    PrintDir0.emitU64Dec ba n = PrintAsm0.emitU64Dec ba n := by
  dsimp only [PrintDir0.emitU64Dec, PrintAsm0.emitU64Dec]
  rw [show (20 : UInt32) = UInt32.ofNat 20 from rfl,
    pow10Up_eq_asm0 20 (n / 10) 1 (by omega),
    emitPowDown_eq_asm0 20 ba n _ (by omega)]

private theorem emitI64Dec_eq_asm0 (ba : ByteArray) (bits : UInt64) :
    PrintDir0.emitI64Dec ba bits = PrintAsm0.emitI64Dec ba bits := by
  dsimp only [PrintDir0.emitI64Dec, PrintAsm0.emitI64Dec]
  by_cases h : (bits >>> 63) == 1
  · simp only [h, ↓reduceIte, emitU64Dec_eq_asm0]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, emitU64Dec_eq_asm0]

private theorem emitReg64_eq_asm0 (ba : ByteArray) (w : Width) (r : Reg64) :
    PrintDir0.emitReg64 ba w r = PrintAsm0.emitReg64 ba w r := by
  dsimp only [PrintDir0.emitReg64, PrintAsm0.emitReg64]
  have hext : PrintDir0.regExtNum r = PrintAsm0.regExtNum r := by cases r <;> rfl
  have hpair : ∀ ba', PrintDir0.regPairBytes ba' r = PrintAsm0.regPairBytes ba' r := by
    intro ba'; cases r <;> rfl
  have hlow : ∀ ba', PrintDir0.regLow8Bytes ba' r = PrintAsm0.regLow8Bytes ba' r := by
    intro ba'; cases r <;> rfl
  rw [hext]
  by_cases hge : PrintAsm0.regExtNum r ≥ 8
  · simp only [hge, ↓reduceIte, emitU64Dec_eq_asm0]
    cases w <;> rfl
  · simp only [hge, ↓reduceIte]
    cases w <;> simp only [hpair, hlow]

private theorem emitCc_eq_asm0 (ba : ByteArray) (cc : CondCode) :
    PrintDir0.emitCc ba cc = PrintAsm0.emitCc ba cc := by
  cases cc <;> rfl

/-! ## 4. Exact `UInt64` Decimal Equivalence (for `.loc` labels) -/

private def digitsPow10 : Nat → Nat → List UInt8
  | 0, n => [UInt8.ofNat (48 + n)]
  | k + 1, n => UInt8.ofNat (48 + n / 10 ^ (k + 1)) :: digitsPow10 k (n % 10 ^ (k + 1))

private theorem emitPowDown_zero (ba : ByteArray) (n p : UInt64) :
    PrintAsm0.emitPowDown 0 ba n p = ba.push (48 + (n / p).toUInt8) := rfl

private theorem emitPowDown_succ (fuel : Nat) (ba : ByteArray) (n p : UInt64) :
    PrintAsm0.emitPowDown (fuel + 1) ba n p =
      let ba' := ba.push (48 + (n / p).toUInt8)
      if p == 1 then ba' else PrintAsm0.emitPowDown fuel ba' (n % p) (p / 10) := rfl

private theorem pow10Up_succ (fuel : Nat) (q p : UInt64) :
    PrintAsm0.pow10Up (fuel + 1) q p =
      if p ≤ q then PrintAsm0.pow10Up fuel q (p * 10) else p := rfl

private theorem pow10_lt_u64 {k : Nat} (hk : k ≤ 19) : 10 ^ k < 2 ^ 64 := by
  have h19 : 10 ^ 19 < 2 ^ 64 := by decide
  exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hk) h19

private theorem u64_ofNat_toNat_pow10 {k : Nat} (hk : k ≤ 19) :
    (UInt64.ofNat (10 ^ k)).toNat = 10 ^ k := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (pow10_lt_u64 hk)]

private theorem emitPowDown_eq_digitsPow10 :
    ∀ (k fuel : Nat) (ba : ByteArray) (n : UInt64),
      k ≤ fuel → k ≤ 19 → n.toNat < 10 ^ (k + 1) →
      (PrintAsm0.emitPowDown fuel ba n (UInt64.ofNat (10 ^ k))).data.toList =
        ba.data.toList ++ digitsPow10 k n.toNat
  | 0, fuel, ba, n, _, _, hn => by
    have h1 : UInt64.ofNat (10 ^ 0) = 1 := rfl
    have hdiv : (n / 1).toNat = n.toNat := by
      rw [UInt64.toNat_div]; exact Nat.div_one _
    have hd : (48 + (n / 1).toUInt8) = UInt8.ofNat (48 + n.toNat) := by
      apply UInt8.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      change (48 + (n / 1).toUInt8).toNat = (UInt8.ofNat (48 + n.toNat)).toNat
      rw [UInt8.toNat_add, UInt64.toNat_toUInt8, hdiv, UInt8.toNat_ofNat']
      have hn10 : n.toNat < 10 := by simpa using hn
      change (48 + n.toNat % 256) % 256 = (48 + n.toNat) % 256
      omega
    rw [h1]
    cases fuel with
    | zero => rw [emitPowDown_zero, ba_push_data_toList, hd]; rfl
    | succ fuel' =>
      rw [emitPowDown_succ]
      simp only [beq_self_eq_true, ↓reduceIte, ba_push_data_toList, hd]
      rfl
  | k + 1, fuel, ba, n, hle, hk, hn => by
    cases fuel with
    | zero => omega
    | succ fuel' =>
      have hk19 : k ≤ 19 := by omega
      have hp_toNat : (UInt64.ofNat (10 ^ (k + 1))).toNat = 10 ^ (k + 1) :=
        u64_ofNat_toNat_pow10 hk
      have hp_ne1 : (UInt64.ofNat (10 ^ (k + 1)) == 1) = false := by
        apply beq_false_of_ne
        intro hEq
        have hgt : 10 ≤ 10 ^ (k + 1) := by
          have := Nat.pow_le_pow_right (by omega : 0 < 10) (by omega : 1 ≤ k + 1)
          simpa using this
        have hNat := congrArg UInt64.toNat hEq
        rw [hp_toNat] at hNat
        change 10 ^ (k + 1) = 1 at hNat
        omega
      have hdiv_p : UInt64.ofNat (10 ^ (k + 1)) / 10 = UInt64.ofNat (10 ^ k) := by
        apply UInt64.eq_of_toBitVec_eq
        apply BitVec.eq_of_toNat_eq
        change (UInt64.ofNat (10 ^ (k + 1)) / 10).toNat = (UInt64.ofNat (10 ^ k)).toNat
        rw [UInt64.toNat_div, hp_toNat, u64_ofNat_toNat_pow10 hk19]
        change 10 ^ (k + 1) / 10 = 10 ^ k
        rw [Nat.pow_succ, Nat.mul_div_cancel _ (by omega)]
      have hmod_lt : (n % UInt64.ofNat (10 ^ (k + 1))).toNat < 10 ^ (k + 1) := by
        rw [UInt64.toNat_mod, hp_toNat]
        exact Nat.mod_lt _ (Nat.pow_pos (by omega))
      have hd : (48 + (n / UInt64.ofNat (10 ^ (k + 1))).toUInt8) =
          UInt8.ofNat (48 + n.toNat / 10 ^ (k + 1)) := by
        have hq_lt : n.toNat / 10 ^ (k + 1) < 10 := by
          rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))]
          have hp : 10 * 10 ^ (k + 1) = 10 ^ (k + 2) := by
            rw [Nat.mul_comm, ← Nat.pow_succ]
          omega
        apply UInt8.eq_of_toBitVec_eq
        apply BitVec.eq_of_toNat_eq
        change (48 + (n / UInt64.ofNat (10 ^ (k + 1))).toUInt8).toNat =
          (UInt8.ofNat (48 + n.toNat / 10 ^ (k + 1))).toNat
        rw [UInt8.toNat_add, UInt64.toNat_toUInt8, UInt64.toNat_div, hp_toNat, UInt8.toNat_ofNat']
        change (48 + (n.toNat / 10 ^ (k + 1)) % 256) % 256 = (48 + n.toNat / 10 ^ (k + 1)) % 256
        omega
      rw [emitPowDown_succ]
      simp only [hp_ne1, Bool.false_eq_true, ↓reduceIte, hdiv_p]
      rw [emitPowDown_eq_digitsPow10 k fuel' _ (n % UInt64.ofNat (10 ^ (k + 1)))
          (by omega) hk19 hmod_lt]
      rw [ba_push_data_toList, List.append_assoc, hd, UInt64.toNat_mod, hp_toNat,
        List.singleton_append]
      rfl

private theorem pow10Up_spec_aux (n : UInt64) :
    ∀ (fuel j : Nat),
      j + fuel = 20 → j ≤ 19 → (j = 0 ∨ 10 ^ j ≤ n.toNat) →
      ∃ k, k ≤ 19 ∧ PrintAsm0.pow10Up fuel (n / 10) (UInt64.ofNat (10 ^ j)) =
          UInt64.ofNat (10 ^ k) ∧
        (k = 0 ∨ 10 ^ k ≤ n.toNat) ∧ n.toNat < 10 ^ (k + 1)
  | 0, j, hsum, hj, _ => by omega
  | fuel' + 1, j, hsum, hj, hlow => by
    rw [pow10Up_succ]
    have hp_toNat : (UInt64.ofNat (10 ^ j)).toNat = 10 ^ j := u64_ofNat_toNat_pow10 hj
    have hq_toNat : (n / 10).toNat = n.toNat / 10 := by
      rw [UInt64.toNat_div]; rfl
    by_cases hle : UInt64.ofNat (10 ^ j) ≤ n / 10
    · simp only [hle, ↓reduceIte]
      have hle_nat : 10 ^ j ≤ n.toNat / 10 := by
        have h := UInt64.le_iff_toNat_le.mp hle
        rwa [hp_toNat, hq_toNat] at h
      have hnext_le : 10 ^ (j + 1) ≤ n.toNat := by
        rw [Nat.pow_succ]; omega
      have hn_lt20 : n.toNat < 10 ^ 20 := by
        have h264 : 2 ^ 64 < 10 ^ 20 := by decide
        exact Nat.lt_trans n.toNat_lt_size h264
      have hj1 : j + 1 ≤ 19 := by
        by_cases h19 : j + 1 ≤ 19
        · exact h19
        · have hge20 : 20 ≤ j + 1 := by omega
          have hpow : 10 ^ 20 ≤ 10 ^ (j + 1) := Nat.pow_le_pow_right (by omega) hge20
          omega
      have hmul : UInt64.ofNat (10 ^ j) * 10 = UInt64.ofNat (10 ^ (j + 1)) := by
        apply UInt64.eq_of_toBitVec_eq
        apply BitVec.eq_of_toNat_eq
        change (UInt64.ofNat (10 ^ j) * 10).toNat = (UInt64.ofNat (10 ^ (j + 1))).toNat
        rw [UInt64.toNat_mul, hp_toNat, u64_ofNat_toNat_pow10 hj1]
        change (10 ^ j * 10) % 2 ^ 64 = 10 ^ (j + 1)
        rw [← Nat.pow_succ, Nat.mod_eq_of_lt (pow10_lt_u64 hj1)]
      rw [hmul]
      exact pow10Up_spec_aux n fuel' (j + 1) (by omega) hj1 (Or.inr hnext_le)
    · simp only [hle, ↓reduceIte]
      have hgt_nat : n.toNat / 10 < 10 ^ j := by
        have h : ¬ (UInt64.ofNat (10 ^ j)).toNat ≤ (n / 10).toNat :=
          fun hle' => hle (UInt64.le_iff_toNat_le.mpr hle')
        rw [hp_toNat, hq_toNat] at h
        omega
      have hlt_next : n.toNat < 10 ^ (j + 1) := by
        rw [Nat.pow_succ]; omega
      exact ⟨j, hj, rfl, hlow, hlt_next⟩

private theorem mod_ten_mul_div_ten (m p : Nat) (hp : 0 < p) :
    m % (10 * p) / 10 = m / 10 % p := by
  have h1 : m = 10 * (m / 10) + m % 10 := (Nat.div_add_mod m 10).symm
  have h2 : m / 10 = p * (m / 10 / p) + m / 10 % p := (Nat.div_add_mod (m / 10) p).symm
  have hrem_lt : 10 * (m / 10 % p) + m % 10 < 10 * p := by
    have ha : m / 10 % p < p := Nat.mod_lt _ hp
    have hb : m % 10 < 10 := Nat.mod_lt _ (by omega)
    omega
  have hdecomp : m = (10 * p) * (m / 10 / p) + (10 * (m / 10 % p) + m % 10) := by
    have : 10 * (p * (m / 10 / p) + m / 10 % p) =
        (10 * p) * (m / 10 / p) + 10 * (m / 10 % p) := by
      rw [Nat.mul_add, Nat.mul_assoc]
    omega
  have hmod : m % (10 * p) = 10 * (m / 10 % p) + m % 10 := by
    calc m % (10 * p)
        = ((10 * p) * (m / 10 / p) + (10 * (m / 10 % p) + m % 10)) % (10 * p) :=
          congrArg (· % (10 * p)) hdecomp
      _ = (10 * (m / 10 % p) + m % 10) % (10 * p) := Nat.mul_add_mod _ _ _
      _ = 10 * (m / 10 % p) + m % 10 := Nat.mod_eq_of_lt hrem_lt
  rw [hmod]
  have hb : m % 10 < 10 := Nat.mod_lt _ (by omega)
  omega

private theorem digitsPow10_succ_right :
    ∀ (k m : Nat),
      digitsPow10 (k + 1) m = digitsPow10 k (m / 10) ++ [UInt8.ofNat (48 + m % 10)]
  | 0, _ => rfl
  | k + 1, m => by
    change UInt8.ofNat (48 + m / 10 ^ (k + 2)) :: digitsPow10 (k + 1) (m % 10 ^ (k + 2)) =
      (UInt8.ofNat (48 + (m / 10) / 10 ^ (k + 1)) :: digitsPow10 k ((m / 10) % 10 ^ (k + 1))) ++
        [UInt8.ofNat (48 + m % 10)]
    rw [List.cons_append, digitsPow10_succ_right k (m % 10 ^ (k + 2))]
    have hdiv : m / 10 ^ (k + 2) = (m / 10) / 10 ^ (k + 1) := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      rw [Nat.pow_succ, Nat.mul_comm]
    have hmod_div : m % 10 ^ (k + 2) / 10 = m / 10 % 10 ^ (k + 1) := by
      have hp : 10 ^ (k + 2) = 10 * 10 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hp]
      exact mod_ten_mul_div_ten m (10 ^ (k + 1)) (Nat.pow_pos (by omega))
    have hmod_mod : m % 10 ^ (k + 2) % 10 = m % 10 := by
      have hdvd : 10 ∣ 10 ^ (k + 2) := ⟨10 ^ (k + 1), by rw [Nat.pow_succ, Nat.mul_comm]⟩
      exact Nat.mod_mod_of_dvd m hdvd
    rw [hdiv, hmod_div, hmod_mod]

private theorem digit_toUTF8_eq (d : Nat) (hd : d < 10) :
    (String.singleton d.digitChar).toUTF8.data.toList = [UInt8.ofNat (48 + d)] := by
  match d, hd with
  | 0, _ => rw [Nat.digitChar_eq_zero.mpr rfl]; rfl
  | 1, _ => rw [Nat.digitChar_eq_one.mpr rfl]; rfl
  | 2, _ => rw [Nat.digitChar_eq_two.mpr rfl]; rfl
  | 3, _ => rw [Nat.digitChar_eq_three.mpr rfl]; rfl
  | 4, _ => rw [Nat.digitChar_eq_four.mpr rfl]; rfl
  | 5, _ => rw [Nat.digitChar_eq_five.mpr rfl]; rfl
  | 6, _ => rw [Nat.digitChar_eq_six.mpr rfl]; rfl
  | 7, _ => rw [Nat.digitChar_eq_seven.mpr rfl]; rfl
  | 8, _ => rw [Nat.digitChar_eq_eight.mpr rfl]; rfl
  | 9, _ => rw [Nat.digitChar_eq_nine.mpr rfl]; rfl
  | d + 10, hd => omega

private theorem digitsPow10_eq_natRepr :
    ∀ (k m : Nat), (k = 0 ∨ 10 ^ k ≤ m) → m < 10 ^ (k + 1) →
      digitsPow10 k m = (Nat.repr m).toUTF8.data.toList
  | 0, m, _, hm => by
    have hm10 : m < 10 := by simpa using hm
    rw [Nat.repr_of_lt hm10, digit_toUTF8_eq m hm10]
    rfl
  | k + 1, m, hlow, hm => by
    have hge_pow : 10 ^ (k + 1) ≤ m := by
      rcases hlow with h | h
      · exact absurd h (Nat.succ_ne_zero k)
      · exact h
    have hge10 : 10 ≤ m := by
      have h10 : 10 ≤ 10 ^ (k + 1) := by
        have := Nat.pow_le_pow_right (by omega : 0 < 10) (by omega : 1 ≤ k + 1)
        simpa using this
      omega
    have hdiv_lt : m / 10 < 10 ^ (k + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have hp : 10 ^ (k + 1) * 10 = 10 ^ (k + 2) := (Nat.pow_succ ..).symm
      omega
    have hdiv_low : k = 0 ∨ 10 ^ k ≤ m / 10 := by
      right
      rw [Nat.le_div_iff_mul_le (by omega)]
      have hp : 10 ^ k * 10 = 10 ^ (k + 1) := (Nat.pow_succ ..).symm
      omega
    rw [digitsPow10_succ_right, digitsPow10_eq_natRepr k (m / 10) hdiv_low hdiv_lt]
    rw [Nat.repr_of_ge hge10, toUTF8_append, ByteArray.toList_data_append]
    rw [digit_toUTF8_eq (m % 10) (Nat.mod_lt m (by omega))]

private theorem emitU64Dec_asm0_eq (ba : ByteArray) (n : UInt64) :
    PrintAsm0.emitU64Dec ba n = ba ++ (Nat.repr n.toNat).toUTF8 := by
  obtain ⟨k, hk, hpow, hlow, hlt⟩ := pow10Up_spec_aux n 20 0 rfl (by omega) (Or.inl rfl)
  apply ba_eq_of_data_toList
  dsimp only [PrintAsm0.emitU64Dec]
  rw [show (1 : UInt64) = UInt64.ofNat (10 ^ 0) from rfl, hpow]
  rw [emitPowDown_eq_digitsPow10 k 20 ba n (by omega) hk hlt]
  rw [digitsPow10_eq_natRepr k n.toNat hlow hlt, ByteArray.toList_data_append]

/-! ## 5. Symbol-Table Slice & `Label0` Equivalence -/

private theorem baGetU8_eq_getElem (ba : ByteArray) (i : UInt64) (h : i.toNat < ba.size) :
    PrintDir0.baGetU8 ba i = ba[i.toNat] := by
  dsimp only [PrintDir0.baGetU8, ByteArray.get!]
  have h1 : i.toNat < ba.data.size := h
  exact getElem!_pos ba.data i.toNat h1

private theorem ba_extract_cons (ba : ByteArray) (i e : Nat) (hlt : i < e) (he : e ≤ ba.size) :
    (ba.extract i e).data.toList = ba[i] :: (ba.extract (i + 1) e).data.toList := by
  apply List.ext_getElem
  · simp only [List.length_cons, Array.length_toList]
    change (ba.extract i e).size = (ba.extract (i + 1) e).size + 1
    rw [ByteArray.size_extract, ByteArray.size_extract]
    omega
  · intro j hj1 hj2
    have hj1' : j < (ba.extract i e).size := by
      rw [Array.length_toList] at hj1
      exact hj1
    rw [show (ba.extract i e).data.toList[j] = (ba.extract i e)[j] from rfl]
    rw [ByteArray.getElem_extract hj1']
    cases j with
    | zero => rfl
    | succ j' =>
      simp only [List.getElem_cons_succ]
      have hj2' : j' < (ba.extract (i + 1) e).size := by
        simp only [List.length_cons, Array.length_toList] at hj2
        exact Nat.lt_of_succ_lt_succ hj2
      rw [show (ba.extract (i + 1) e).data.toList[j'] = (ba.extract (i + 1) e)[j'] from rfl]
      rw [ByteArray.getElem_extract hj2']
      have hidx : i + (j' + 1) = (i + 1) + j' := by omega
      congr 1

private theorem emitSymLoop_eq_extract_aux (symBytes : ByteArray) :
    ∀ (k : Nat) (i endOff : UInt64) (out : ByteArray),
      k = endOff.toNat - i.toNat → endOff.toNat ≤ symBytes.size →
      (PrintDir0.emitSymLoop symBytes i endOff out).data.toList =
        out.data.toList ++ (symBytes.extract i.toNat endOff.toNat).data.toList
  | 0, i, endOff, out, hk, hEnd => by
    have hge : ¬ i < endOff := by
      intro hlt
      have : i.toNat < endOff.toNat := hlt
      omega
    rw [PrintDir0.emitSymLoop.eq_def]
    simp only [hge, ↓reduceDIte]
    have hsz : (symBytes.extract i.toNat endOff.toNat).size = 0 := by
      rw [ByteArray.size_extract]; omega
    have hnil : (symBytes.extract i.toNat endOff.toNat).data.toList = [] := by
      rw [← List.length_eq_zero_iff]
      change (symBytes.extract i.toNat endOff.toNat).size = 0
      exact hsz
    rw [hnil, List.append_nil]
  | k + 1, i, endOff, out, hk, hEnd => by
    have hlt : i < endOff := by
      change i.toNat < endOff.toNat; omega
    have hi : i.toNat < symBytes.size := by
      have : i.toNat < endOff.toNat := hlt
      omega
    rw [PrintDir0.emitSymLoop.eq_def]
    simp only [hlt, ↓reduceDIte]
    have hadd : (i + 1).toNat = i.toNat + 1 := by
      have hsz : endOff.toNat < 2 ^ 64 := endOff.toNat_lt_size
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
    have hstep : k = endOff.toNat - (i + 1).toNat := by rw [hadd]; omega
    have ih := emitSymLoop_eq_extract_aux symBytes k (i + 1) endOff
      (out.push (PrintDir0.baGetU8 symBytes i)) hstep hEnd
    rw [ih, ba_push_data_toList, baGetU8_eq_getElem symBytes i hi, List.append_assoc]
    congr 1
    rw [hadd, ba_extract_cons symBytes i.toNat endOff.toNat hlt hEnd]
    rfl

private theorem emitSym_eq (symBytes : ByteArray) (symOffs : Array Nat) (symName : Sym0 → Sym)
    (sym : Sym0) (out : ByteArray)
    (hBa : symBytes.size < 2 ^ 64) (hOffs : symOffs.size < 2 ^ 64)
    (hm : SymSliceMatch symBytes symOffs symName sym) :
    PrintDir0.emitSym symBytes symOffs sym out = out ++ (symName sym).toUTF8 := by
  rcases hm with ⟨hIdx, hBound, hExt⟩
  have hSymLt : sym.toNat < 2 ^ 32 := sym.toNat_lt
  have hIdxVal : (sym.toUInt64 * 2).toNat = 2 * sym.toNat := by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, show (2 : UInt64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hIdx1Val : (sym.toUInt64 * 2 + 1).toNat = 2 * sym.toNat + 1 := by
    rw [UInt64.toNat_add, hIdxVal, show (1 : UInt64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hArrSz : (PrintDir0.arrSizeU64 symOffs).toNat = symOffs.size := by
    dsimp only [PrintDir0.arrSizeU64]
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hOffs]
  have hBaSz : (PrintDir0.baSizeU64 symBytes).toNat = symBytes.size := by
    dsimp only [PrintDir0.baSizeU64]
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hBa]
  have hOffNat : symOffs[2 * sym.toNat]! < 2 ^ 64 := by omega
  have hLenNat : symOffs[2 * sym.toNat + 1]! < 2 ^ 64 := by omega
  have hOffVal : (PrintDir0.arrGetU64 symOffs (sym.toUInt64 * 2)).toNat =
      symOffs[2 * sym.toNat]! := by
    dsimp only [PrintDir0.arrGetU64]
    rw [hIdxVal, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hOffNat]
  have hLenVal : (PrintDir0.arrGetU64 symOffs (sym.toUInt64 * 2 + 1)).toNat =
      symOffs[2 * sym.toNat + 1]! := by
    dsimp only [PrintDir0.arrGetU64]
    rw [hIdx1Val, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hLenNat]
  have hC1 : sym.toUInt64 * 2 < PrintDir0.arrSizeU64 symOffs := by
    change (sym.toUInt64 * 2).toNat < (PrintDir0.arrSizeU64 symOffs).toNat
    rw [hIdxVal, hArrSz]; omega
  have hC2 : 1 < PrintDir0.arrSizeU64 symOffs - sym.toUInt64 * 2 := by
    change (1 : UInt64).toNat < (PrintDir0.arrSizeU64 symOffs - sym.toUInt64 * 2).toNat
    have hle : sym.toUInt64 * 2 ≤ PrintDir0.arrSizeU64 symOffs :=
      UInt64.le_iff_toNat_le.mpr (by rw [hIdxVal, hArrSz]; omega)
    rw [UInt64.toNat_sub_of_le _ _ hle, hIdxVal, hArrSz, show (1 : UInt64).toNat = 1 from rfl]
    omega
  have hC3 : PrintDir0.arrGetU64 symOffs (sym.toUInt64 * 2) ≤ PrintDir0.baSizeU64 symBytes := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hOffVal, hBaSz]; omega
  have hC4 : PrintDir0.arrGetU64 symOffs (sym.toUInt64 * 2 + 1) ≤
      PrintDir0.baSizeU64 symBytes - PrintDir0.arrGetU64 symOffs (sym.toUInt64 * 2) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [UInt64.toNat_sub_of_le _ _ hC3, hOffVal, hLenVal, hBaSz]
    omega
  have hSumVal : (PrintDir0.arrGetU64 symOffs (sym.toUInt64 * 2) +
      PrintDir0.arrGetU64 symOffs (sym.toUInt64 * 2 + 1)).toNat =
      symOffs[2 * sym.toNat]! + symOffs[2 * sym.toNat + 1]! := by
    rw [UInt64.toNat_add, hOffVal, hLenVal, Nat.mod_eq_of_lt (by omega)]
  dsimp only [PrintDir0.emitSym]
  simp only [hC1, hC2, hC3, hC4, Bool.and_self, decide_true, ↓reduceIte]
  apply ba_eq_of_data_toList
  rw [emitSymLoop_eq_extract_aux symBytes _ _ _ out rfl (by rw [hSumVal]; omega)]
  rw [hOffVal, hSumVal, hExt, ByteArray.toList_data_append]

private theorem emitLabel0_eq_emitStr (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) (l : Label0) (out : ByteArray)
    (hBa : symBytes.size < 2 ^ 64) (hOffs : symOffs.size < 2 ^ 64)
    (hl : match l with
      | .sym id => SymSliceMatch symBytes symOffs symName id
      | .loc _ _ => True) :
    PrintDir0.emitLabel0 symBytes symOffs l out =
      PrintAsm0.emitStr out (label0ToSym symName l) := by
  cases l with
  | sym id =>
    dsimp only [PrintDir0.emitLabel0, label0ToSym]
    rw [emitSym_eq symBytes symOffs symName id out hBa hOffs hl, emitStr_eq]
  | loc fnId lblId =>
    dsimp only [PrintDir0.emitLabel0, label0ToSym]
    rw [emitStr_eq, emitU64Dec_eq_asm0, emitU64Dec_eq_asm0]
    have hpush : ∀ ba : ByteArray, ba.push 0x5f = ba ++ "_".toUTF8 :=
      fun ba => ba_push_eq_append ba 0x5f "_" rfl
    have hpfx : PrintDir0.e3 out 0x2e 0x4c 0x5f = out ++ ".L_".toUTF8 := by
      apply ba_eq_of_data_toList
      dsimp only [PrintDir0.e3]
      rw [ba_push_data_toList, ba_push_data_toList, ba_push_data_toList,
        ByteArray.toList_data_append, List.append_assoc, List.append_assoc]
      rfl
    apply ba_eq_of_data_toList
    rw [hpfx, emitU64Dec_asm0_eq, hpush, emitU64Dec_asm0_eq]
    have hf : fnId.toUInt64.toNat = fnId.toNat := UInt32.toNat_toUInt64 fnId
    have hl2 : lblId.toUInt64.toNat = lblId.toNat := UInt32.toNat_toUInt64 lblId
    rw [hf, hl2]
    change (out ++ ".L_".toUTF8 ++ (Nat.repr fnId.toNat).toUTF8 ++ "_".toUTF8 ++
        (Nat.repr lblId.toNat).toUTF8).data.toList =
      (out ++ s!".L_{fnId.toNat}_{lblId.toNat}".toUTF8).data.toList
    simp only [ByteArray.toList_data_append, toUTF8_append, List.append_assoc]
    rfl

/-! ## 6. Single-Directive Equivalence Across All `27` `Dir0` Constructors -/

private theorem dir0ToAmd64_ne_nil (symName : Sym0 → Sym) (d : Dir0) :
    dir0ToAmd64 symName d ≠ [] := by
  cases d <;> simp only [dir0ToAmd64]
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · rename_i w _ _; cases w <;> intro h <;> cases h
  · rename_i w1 _ w2 _; cases w1 <;> cases w2 <;> intro h <;> cases h
  · rename_i w _ _; cases w <;> intro h <;> cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · rename_i b _; cases b <;> intro h <;> cases h
  · rename_i b _; cases b <;> intro h <;> cases h
  · intro h; cases h
  · rename_i _ b _; cases b <;> intro h <;> cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · rename_i w b _; cases w <;> cases b <;> intro h <;> cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

private theorem dir0ToAmd64_dirSubset0_aux (symName : Sym0 → Sym) (d : Dir0) :
    ∀ x ∈ dir0ToAmd64 symName d, DirSubset0 x := by
  cases d <;> intro x hx
  all_goals
    simp only [dir0ToAmd64] at hx
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · simp only [List.mem_singleton] at hx; subst hx; cases ‹Width› <;> rfl
  · simp only [List.mem_singleton] at hx; subst hx
    rename_i rd imm
    dsimp only [moviD, moviI]
    by_cases hfit : fitsUImm32 (BitVec.ofNat 64 imm.toNat) = true
    · simp only [hfit]; rfl
    · simp only [hfit]; rfl
  · rename_i w _ _; cases w <;> (simp only [List.mem_singleton] at hx; subst hx; rfl)
  · rename_i w1 _ w2 _; cases w1 <;> cases w2 <;>
      (simp only [List.mem_singleton] at hx; subst hx; rfl)
  · rename_i w _ _; cases w <;> (simp only [List.mem_singleton] at hx; subst hx; rfl)
  · simp only [List.mem_singleton] at hx; subst hx; cases ‹Width› <;> rfl
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · rename_i b _; cases b <;> (simp only [List.mem_singleton] at hx; subst hx; rfl)
  · rename_i b _; cases b <;> (simp only [List.mem_singleton] at hx; subst hx; rfl)
  · simp only [List.mem_singleton] at hx; subst hx
    cases ‹Width› <;> cases ‹AluKind0› <;> rfl
  · rename_i w b _; cases b <;> (simp only [List.mem_singleton] at hx; subst hx; cases w <;> rfl)
  · simp only [List.mem_singleton] at hx; subst hx
    cases ‹Width› <;> cases ‹ShiftKind0› <;> rfl
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · simp only [List.mem_singleton] at hx; subst hx; cases ‹Width› <;> rfl
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · simp only [List.mem_singleton] at hx; subst hx; cases ‹Width› <;> rfl
  · rename_i w b _; cases w <;> cases b <;>
      (simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
       rcases hx with rfl | rfl | rfl <;> rfl)
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · simp only [List.mem_singleton] at hx; subst hx; rfl

private theorem int64_ofNat_toUInt64 (x : UInt64) : (Int64.ofNat x.toNat).toUInt64 = x := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change ((Int64.ofNat x.toNat).toUInt64).toNat = x.toNat
  rw [Int64.toUInt64_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt x.toNat_lt_size]

private theorem int64_ofBitVec_ofNat_toUInt64 (x : UInt64) :
    (Int64.ofBitVec (BitVec.ofNat 64 x.toNat)).toUInt64 = x := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 64 x.toNat).toNat = x.toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.toNat_lt_size]

private theorem fitsUImm32_eq (imm : UInt64) :
    fitsUImm32 (BitVec.ofNat 64 imm.toNat) = ((imm >>> 32) == 0) := by
  dsimp only [fitsUImm32]
  have h1 : (BitVec.ofNat 64 imm.toNat >>> 32) = (imm >>> 32).toBitVec := by
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 64 imm.toNat >>> 32).toNat = (imm >>> 32).toBitVec.toNat
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt imm.toNat_lt_size]
    change imm.toNat >>> 32 = (imm >>> 32).toNat
    rw [UInt64.toNat_shiftRight]
    rfl
  rw [h1]
  cases h : (imm >>> 32) == 0 with
  | true =>
    have heq : imm >>> 32 = 0 := beq_iff_eq.mp h
    simp [heq]
  | false =>
    have hne : imm >>> 32 ≠ 0 := fun heq => by simp [heq] at h
    have hbv : (imm >>> 32).toBitVec ≠ 0#64 := fun hb =>
      hne (UInt64.eq_of_toBitVec_eq hb)
    have hbeq : ((imm >>> 32).toBitVec == 0#64) = false := beq_false_of_ne hbv
    exact hbeq

private theorem eWidth_eq_asm0 (ba : ByteArray) (w : Width) :
    PrintDir0.eWidth ba w = PrintAsm0.eWidth ba w := by cases w <;> rfl

private theorem eRegRegW_eq (ba : ByteArray) (w : Width) (rd rs : Reg64) :
    PrintDir0.eRegRegW ba w rd rs =
      PrintAsm0.eOp2W ba w (.reg (regW w rd)) (.regOrMem (.reg (regW w rs))) := by
  dsimp only [PrintDir0.eRegRegW, PrintAsm0.eOp2W, PrintAsm0.emitOpd, PrintAsm0.emitRm,
    PrintAsm0.emitReg]
  rw [eWidth_eq_asm0, emitReg64_eq_asm0, emitReg64_eq_asm0]
  cases w <;> rfl

private theorem eImmReg_eq (ba : ByteArray) (w : Width) (rd : Reg64) (imm : UInt64) :
    PrintDir0.eImmReg ba w rd imm =
      PrintAsm0.eOp2W ba w (.reg (regW w rd))
        (.imm (.int64 (Int64.ofBitVec (BitVec.ofNat 64 imm.toNat)))) := by
  dsimp only [PrintDir0.eImmReg, PrintAsm0.eOp2W, PrintAsm0.emitOpd, PrintAsm0.emitConst,
    PrintAsm0.emitRm, PrintAsm0.emitReg]
  rw [eWidth_eq_asm0, emitI64Dec_eq_asm0, int64_ofBitVec_ofNat_toUInt64, emitReg64_eq_asm0]
  cases w <;> rfl

private theorem eSpSuffix_eq (ba : ByteArray) :
    PrintDir0.eSpSuffix ba = (PrintAsm0.emitReg64 (ba.push 0x28) .W64 .rsp).push 0x29 := by
  rfl

private theorem emitI64Dec_nonneg (ba : ByteArray) (i : Int64) (u : UInt64)
    (hu : i.toUInt64 = u) (h : (u >>> 63 == 1) = false) :
    PrintAsm0.emitI64Dec ba i.toUInt64 = PrintAsm0.emitU64Dec ba u := by
  dsimp only [PrintAsm0.emitI64Dec]
  rw [hu, h]
  rfl

private theorem eDivCore_eq (symName : Sym0 → Sym) (w : Width) (isSigned : Bool) (rhs : Reg64)
    (out : ByteArray) :
    PrintDir0.eDivCore out w isSigned rhs =
      PrintAsm0.emitDirsNoTrailLoop out (dir0ToAmd64 symName (.divCore w isSigned rhs)) := by
  have hfit0 : fitsUImm32 0 = true := by decide
  have h0 : ∀ ba, PrintAsm0.emitI64Dec ba (Int64.ofBitVec 0).toUInt64 =
      PrintAsm0.emitU64Dec ba 0 :=
    fun ba => emitI64Dec_nonneg ba _ 0 rfl (by decide)
  have h31 : ∀ ba, PrintAsm0.emitI64Dec ba (31 : Int64).toUInt64 =
      PrintAsm0.emitU64Dec ba 31 :=
    fun ba => emitI64Dec_nonneg ba 31 31 rfl (by decide)
  have h63 : ∀ ba, PrintAsm0.emitI64Dec ba (63 : Int64).toUInt64 =
      PrintAsm0.emitU64Dec ba 63 :=
    fun ba => emitI64Dec_nonneg ba 63 63 rfl (by decide)
  cases w <;> cases isSigned <;>
  · dsimp only [PrintDir0.eDivCore, PrintDir0.eDivSignedPfx, PrintDir0.eDivUnsignedPfx,
      PrintDir0.eSarRdx, PrintDir0.eRegRegW, PrintDir0.eImmReg, PrintDir0.eWidth,
      PrintDir0.eCommaSp, PrintDir0.e4, PrintDir0.e3, PrintDir0.e2,
      dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0, moviD, moviI, ins,
      ins32, insW, x64InsI, PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.eOp1W, PrintAsm0.eOp2W, PrintAsm0.eShW, PrintAsm0.emitCount,
      PrintAsm0.emitOpd, PrintAsm0.emitConst, PrintAsm0.emitRm, PrintAsm0.emitReg,
      PrintAsm0.eWidth, PrintAsm0.eCommaSp, PrintAsm0.e4, PrintAsm0.e3, PrintAsm0.e2]
    simp only [hfit0, emitReg64_eq_asm0, emitU64Dec_eq_asm0, emitI64Dec_eq_asm0,
      ↓reduceIte, Bool.false_eq_true, h0, h31, h63]
    try rfl

private theorem printDir0Bytes_eq_emitDirsNoTrailLoop (symBytes : ByteArray)
    (symOffs : Array Nat) (symName : Sym0 → Sym) (d : Dir0) (out : ByteArray)
    (hok : Dir0SymsOk symBytes symOffs symName d) :
    printDir0Bytes symBytes symOffs d out =
      PrintAsm0.emitDirsNoTrailLoop out (dir0ToAmd64 symName d) := by
  rcases hok with ⟨hBa, hOffs, hSym⟩
  cases d with
  | label l =>
    cases l <;>
    · dsimp only [printDir0Bytes, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0]
      rw [emitLabel0_eq_emitStr symBytes symOffs symName _ out hBa hOffs hSym]
  | jmp l =>
    cases l <;>
    · dsimp only [printDir0Bytes, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0,
        x64JmpD, x64JmpI, ins, PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
        PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
        PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, PrintAsm0.emitOpBmi2,
        PrintAsm0.emitOpCtrl, PrintAsm0.emitTarget, PrintAsm0.emitConst]
      rw [emitLabel0_eq_emitStr symBytes symOffs symName _ _ hBa hOffs hSym]
      rfl
  | jcc cc l =>
    cases l <;>
    · dsimp only [printDir0Bytes, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0,
        ins, PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
        PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
        PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, PrintAsm0.emitOpBmi2,
        PrintAsm0.emitOpCtrl]
      rw [emitCc_eq_asm0, emitLabel0_eq_emitStr symBytes symOffs symName _ _ hBa hOffs hSym]
  | callSym sym =>
    dsimp only at hSym
    dsimp only [printDir0Bytes, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0,
      x64CallD, x64CallI, ins, PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, PrintAsm0.emitOpBmi2,
      PrintAsm0.emitOpCtrl, PrintAsm0.emitTarget, PrintAsm0.emitConst]
    rw [emitSym_eq symBytes symOffs symName sym _ hBa hOffs hSym, emitStr_eq]
    rfl
  | movRR w rd rs =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, dir0ToAmd64,
      PrintAsm0.emitDirsNoTrailLoop, emitDir0, insW, x64InsI, PrintAsm0.emitOpData]
    exact eRegRegW_eq _ w rd rs
  | movRI rd imm =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, dir0ToAmd64,
      PrintAsm0.emitDirsNoTrailLoop, emitDir0, moviD, moviI]
    rw [fitsUImm32_eq imm]
    cases h : (imm >>> 32) == 0
    · dsimp only [x64InsI, PrintAsm0.emitOpData]
      exact eImmReg_eq _ .W64 rd imm
    · dsimp only [x64InsI, PrintAsm0.emitOpData]
      exact eImmReg_eq _ .W32 rd imm
  | movzx32 wSrc rd rs =>
    cases wSrc <;>
    · dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
        PrintDir0.eMovzx32, PrintDir0.eMovReg, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop,
        emitDir0, ins32, ins, x64InsI, PrintAsm0.emitOpData, PrintAsm0.emitMovExt,
        PrintAsm0.eOp2W, PrintAsm0.emitOpd, PrintAsm0.emitRm, PrintAsm0.emitReg,
        PrintDir0.eRegRegW]
      simp only [emitReg64_eq_asm0, eWidth_eq_asm0]
      rfl
  | movsx wDst rd wSrc rs =>
    cases wDst <;> cases wSrc <;>
    · dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
        PrintDir0.eMovsx, PrintDir0.eMovReg, PrintDir0.eRegRegW, dir0ToAmd64,
        PrintAsm0.emitDirsNoTrailLoop, emitDir0, ins, ins32, insW, x64InsI,
        PrintAsm0.emitOpData, PrintAsm0.emitMovExt, PrintAsm0.eOp2W, PrintAsm0.emitOpd,
        PrintAsm0.emitRm, PrintAsm0.emitReg]
      simp only [emitReg64_eq_asm0, eWidth_eq_asm0]
      rfl
  | ldMem w rd base =>
    cases w <;>
    · dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
        PrintDir0.printDir0LdSt, PrintDir0.eLdMem, PrintDir0.eRegMemAt, dir0ToAmd64,
        PrintAsm0.emitDirsNoTrailLoop, emitDir0, ins32, ins, x64InsI, PrintAsm0.emitOpData,
        PrintAsm0.emitMovExt, PrintAsm0.eOp2W, PrintAsm0.emitOpd, PrintAsm0.emitRm,
        PrintAsm0.emitAddr, PrintAsm0.emitAddrDisp, PrintAsm0.emitReg]
      simp only [emitReg64_eq_asm0]
      rfl
  | stMem w base val =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
      PrintDir0.printDir0LdSt, PrintDir0.eRegMemAt, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop,
      emitDir0, insW, x64InsI, PrintAsm0.emitOpData, PrintAsm0.eOp2W, PrintAsm0.emitOpd,
      PrintAsm0.emitRm, PrintAsm0.emitAddr, PrintAsm0.emitAddrDisp, PrintAsm0.emitReg]
    rw [eWidth_eq_asm0, emitReg64_eq_asm0, emitReg64_eq_asm0]
    cases w <;> rfl
  | ldSlot rd disp =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
      PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.eSlotMem,
      dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0, ins,
      PrintAsm0.emitOpData, PrintAsm0.eOp2W, PrintAsm0.emitOpd, PrintAsm0.emitRm,
      PrintAsm0.emitAddr, PrintAsm0.emitAddrDisp, PrintAsm0.emitReg]
    rw [int64_ofNat_toUInt64]
    by_cases hd : disp == 0
    · simp only [hd, ↓reduceIte, eSpSuffix_eq, emitReg64_eq_asm0]; rfl
    · simp only [hd, Bool.false_eq_true, ↓reduceIte, eSpSuffix_eq, emitI64Dec_eq_asm0,
        emitReg64_eq_asm0]; rfl
  | stSlot disp rs =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
      PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.eSlotMem,
      dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0, ins,
      PrintAsm0.emitOpData, PrintAsm0.eOp2W, PrintAsm0.emitOpd, PrintAsm0.emitRm,
      PrintAsm0.emitAddr, PrintAsm0.emitAddrDisp, PrintAsm0.emitReg]
    rw [int64_ofNat_toUInt64]
    by_cases hd : disp == 0
    · simp only [hd, ↓reduceIte, eSpSuffix_eq, emitReg64_eq_asm0]; rfl
    · simp only [hd, Bool.false_eq_true, ↓reduceIte, eSpSuffix_eq, emitI64Dec_eq_asm0,
        emitReg64_eq_asm0]; rfl
  | ldSlotIdx rd idx =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
      PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
      PrintDir0.eSlotIdxMem, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0, ins,
      PrintAsm0.emitOpData, PrintAsm0.eOp2W, PrintAsm0.emitOpd, PrintAsm0.emitRm,
      PrintAsm0.emitAddr, PrintAsm0.emitAddrDisp, PrintAsm0.emitScaleByte, PrintAsm0.emitReg]
    simp only [emitReg64_eq_asm0]
    rfl
  | stSlotIdx idx rs =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
      PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
      PrintDir0.eSlotIdxMem, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0, ins,
      PrintAsm0.emitOpData, PrintAsm0.eOp2W, PrintAsm0.emitOpd, PrintAsm0.emitRm,
      PrintAsm0.emitAddr, PrintAsm0.emitAddrDisp, PrintAsm0.emitScaleByte, PrintAsm0.emitReg]
    simp only [emitReg64_eq_asm0]
    rfl
  | spAdd isSub imm32 =>
    cases isSub <;>
    · dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
        PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
        PrintDir0.printDir0Sp, PrintDir0.eImmReg, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop,
        emitDir0, x64SubSpD, x64AddSpD, ins, PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1,
        PrintAsm0.eOp2W, PrintAsm0.emitOpd, PrintAsm0.emitConst, PrintAsm0.emitRm,
        PrintAsm0.emitReg]
      rw [int64_ofNat_toUInt64, emitI64Dec_eq_asm0, emitReg64_eq_asm0]
      rfl
  | spAddReg isSub r =>
    cases isSub <;>
    · dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
        PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
        PrintDir0.printDir0Sp, PrintDir0.eRegRegW, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop,
        emitDir0, ins, PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.eOp2W,
        PrintAsm0.emitOpd, PrintAsm0.emitRm, PrintAsm0.emitReg]
      rw [emitReg64_eq_asm0, emitReg64_eq_asm0]
      rfl
  | aluRR w k rd rs =>
    cases k <;>
    · dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
        PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
        PrintDir0.printDir0Sp, PrintDir0.printDir0Alu, PrintDir0.emitAluMn, dir0ToAmd64,
        alu0ToOp, PrintAsm0.emitDirsNoTrailLoop, emitDir0, insW, x64InsI,
        PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
        PrintAsm0.emitOpMulDiv]
      exact eRegRegW_eq _ w rd rs
  | unary w isNeg rd =>
    cases isNeg <;>
    · dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
        PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
        PrintDir0.printDir0Sp, PrintDir0.printDir0Alu, dir0ToAmd64,
        PrintAsm0.emitDirsNoTrailLoop, emitDir0, insW, x64InsI, PrintAsm0.emitOpData,
        PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2, PrintAsm0.eOp1W, PrintAsm0.emitRm,
        PrintAsm0.emitReg]
      rw [eWidth_eq_asm0, emitReg64_eq_asm0]
      cases w <;> rfl
  | shiftCl w k rd =>
    cases k <;>
    · dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
        PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
        PrintDir0.printDir0Sp, PrintDir0.printDir0Alu, PrintDir0.printDir0Shift,
        PrintDir0.emitShiftMn, dir0ToAmd64, shift0ToOp, PrintAsm0.emitDirsNoTrailLoop,
        emitDir0, insW, x64InsI, PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1,
        PrintAsm0.emitOpAlu2, PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry,
        PrintAsm0.emitOpShift1, PrintAsm0.emitOpShift2, PrintAsm0.eShW,
        PrintAsm0.emitCount, PrintAsm0.emitRm, PrintAsm0.emitReg]
      rw [eWidth_eq_asm0, emitReg64_eq_asm0]
      cases w <;> rfl
  | shMaskCl imm =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
      PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
      PrintDir0.printDir0Sp, PrintDir0.printDir0Alu, PrintDir0.printDir0Shift,
      PrintDir0.eImmReg, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0, ins32,
      PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.eOp2W, PrintAsm0.emitOpd,
      PrintAsm0.emitConst, PrintAsm0.emitRm, PrintAsm0.emitReg]
    rw [int64_ofNat_toUInt64, emitI64Dec_eq_asm0, emitReg64_eq_asm0]
    rfl
  | cmpRR w ra rb =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
      PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
      PrintDir0.printDir0Sp, PrintDir0.printDir0Alu, PrintDir0.printDir0Shift,
      PrintDir0.printDir0CmpTest, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0,
      insW, x64InsI, PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2]
    exact eRegRegW_eq _ w ra rb
  | testbRR ra rb =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
      PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
      PrintDir0.printDir0Sp, PrintDir0.printDir0Alu, PrintDir0.printDir0Shift,
      PrintDir0.printDir0CmpTest, dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0,
      ins8, PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2]
    exact eRegRegW_eq _ .W8 ra rb
  | setcc cc rd =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
      PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
      PrintDir0.printDir0Sp, PrintDir0.printDir0Alu, PrintDir0.printDir0Shift,
      PrintDir0.printDir0CmpTest, PrintDir0.printDir0Cond, dir0ToAmd64,
      PrintAsm0.emitDirsNoTrailLoop, emitDir0, ins8, PrintAsm0.emitOpData,
      PrintAsm0.emitRm, PrintAsm0.emitReg]
    rw [emitCc_eq_asm0, emitReg64_eq_asm0]
    rfl
  | cmovcc w cc rd rs =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
      PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
      PrintDir0.printDir0Sp, PrintDir0.printDir0Alu, PrintDir0.printDir0Shift,
      PrintDir0.printDir0CmpTest, PrintDir0.printDir0Cond, PrintDir0.eMovReg, dir0ToAmd64,
      PrintAsm0.emitDirsNoTrailLoop, emitDir0, insW, x64InsI, PrintAsm0.emitOpData,
      PrintAsm0.eRmReg, PrintAsm0.emitRm, PrintAsm0.emitReg]
    rw [emitCc_eq_asm0, emitReg64_eq_asm0, emitReg64_eq_asm0]
    cases w <;> rfl
  | divCore w isSigned rhs =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
      PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
      PrintDir0.printDir0Sp, PrintDir0.printDir0Alu, PrintDir0.printDir0Shift,
      PrintDir0.printDir0CmpTest, PrintDir0.printDir0Cond, PrintDir0.printDir0DivMulRet]
    exact eDivCore_eq symName w isSigned rhs out
  | mulq rhs =>
    dsimp only [printDir0Bytes, PrintDir0.printDir0Mem, PrintDir0.printDir0Ext,
      PrintDir0.printDir0LdSt, PrintDir0.printDir0Slot, PrintDir0.printDir0SlotIdx,
      PrintDir0.printDir0Sp, PrintDir0.printDir0Alu, PrintDir0.printDir0Shift,
      PrintDir0.printDir0CmpTest, PrintDir0.printDir0Cond, PrintDir0.printDir0DivMulRet,
      dir0ToAmd64, PrintAsm0.emitDirsNoTrailLoop, emitDir0, ins, PrintAsm0.emitOpData,
      PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2, PrintAsm0.emitOpMulDiv,
      PrintAsm0.eOp1W, PrintAsm0.emitRm, PrintAsm0.emitReg]
    rw [emitReg64_eq_asm0]
    rfl
  | ret => rfl

/-! ## 7. Bridging `PrintAsm0.emitDirsNoTrailLoop` to `PrintAsm0Lemmas` -/

private theorem emitDirsNoTrailLoop_eq_append :
    ∀ (p : List _root_.Directive) (out : ByteArray),
      (∀ d' ∈ p, DirSubset0 d') →
      PrintAsm0.emitDirsNoTrailLoop out p = out ++ printAmd64Asm0NoTrail p
  | [], out, _ => by
    dsimp only [PrintAsm0.emitDirsNoTrailLoop, printAmd64Asm0NoTrail]
    rw [emptyWithCapacity_eq_empty, ByteArray.append_empty]
  | [d'], out, hsub => by
    have hd : DirSubset0 d' := hsub d' (List.mem_cons_self ..)
    dsimp only [PrintAsm0.emitDirsNoTrailLoop, printAmd64Asm0NoTrail]
    rw [emptyWithCapacity_eq_empty, emitDir0_eq out d' hd,
      emitDir0_eq ByteArray.empty d' hd, ByteArray.empty_append]
  | d' :: d2 :: ds', out, hsub => by
    have hd : DirSubset0 d' := hsub d' (List.mem_cons_self ..)
    have htl : ∀ x ∈ d2 :: ds', DirSubset0 x :=
      fun x hx => hsub x (List.mem_cons_of_mem d' hx)
    have ih1 := emitDirsNoTrailLoop_eq_append (d2 :: ds') ((emitDir0 out d').push 0x0a) htl
    have ih2 := emitDirsNoTrailLoop_eq_append (d2 :: ds')
      ((emitDir0 ByteArray.empty d').push 0x0a) htl
    dsimp only [printAmd64Asm0NoTrail] at ih1 ih2 ⊢
    rw [emptyWithCapacity_eq_empty] at ih1 ih2 ⊢
    dsimp only [PrintAsm0.emitDirsNoTrailLoop] at ih1 ih2 ⊢
    rw [ih1, ih2, emitDir0_eq out d' hd, emitDir0_eq ByteArray.empty d' hd,
      ByteArray.empty_append, ba_push_eq_append _ 0x0a "\n" rfl,
      ba_push_eq_append (ATT.directive d').toUTF8 0x0a "\n" rfl]
    simp only [ByteArray.append_assoc]

/-! ## 8. Headline Byte-for-Byte Equivalence Theorems -/

/-- Every directive produced by `Bridge0.dir0ToAmd64` lies in `PrintAsm0`'s `DirSubset0`. -/
public theorem dir0ToAmd64_dirSubset0 (symName : Sym0 → Sym) (d : Dir0) :
    ∀ x ∈ dir0ToAmd64 symName d, DirSubset0 x :=
  dir0ToAmd64_dirSubset0_aux symName d

/-- Exact byte-for-byte equivalence between `printDir0Bytes` and `Kraken.X64.toATT` on a single
`Dir0` (matching `PrintAsm0.printAsm0 (Bridge0.dir0ToAmd64 symName d)`). -/
public theorem printDir0Bytes_eq_toATT (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) (d : Dir0) (out : ByteArray)
    (hok : Dir0SymsOk symBytes symOffs symName d) :
    printDir0Bytes symBytes symOffs d out =
      out ++ (Kraken.X64.toATT (dir0ToAmd64 symName d)).toUTF8 := by
  rw [printDir0Bytes_eq_emitDirsNoTrailLoop symBytes symOffs symName d out hok,
    emitDirsNoTrailLoop_eq_append _ out (dir0ToAmd64_dirSubset0 symName d),
    printAmd64Asm0NoTrail_eq_toATT _ (dir0ToAmd64_dirSubset0 symName d)]

/-- Exact byte-for-byte equivalence between `printDir0Bytes` and
`PrintAsm0.printAsm0 (Bridge0.dir0ToAmd64 symName d)`. -/
public theorem printDir0Bytes_eq_printAsm0 (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) (d : Dir0) (out : ByteArray)
    (hok : Dir0SymsOk symBytes symOffs symName d) :
    printDir0Bytes symBytes symOffs d out =
      out ++ (printAsm0 (dir0ToAmd64 symName d)).toUTF8 := by
  rw [printDir0Bytes_eq_toATT symBytes symOffs symName d out hok,
    printAsm0_eq_toATT _ (dir0ToAmd64_dirSubset0 symName d)]

private theorem emitDirsNoTrailLoop_append_nonempty :
    ∀ (xs ys : _root_.Program) (out : ByteArray),
      xs ≠ [] → ys ≠ [] →
      (∀ d' ∈ xs, DirSubset0 d') → (∀ d' ∈ ys, DirSubset0 d') →
      PrintAsm0.emitDirsNoTrailLoop out (xs ++ ys) =
        (PrintAsm0.emitDirsNoTrailLoop out xs).push 0x0a ++ printAmd64Asm0NoTrail ys
  | [], _, _, hxs, _, _, _ => absurd rfl hxs
  | [x], y :: ys, out, _, _, hxs, hys => by
    have hx : DirSubset0 x := hxs x (List.mem_cons_self ..)
    dsimp only [List.singleton_append, PrintAsm0.emitDirsNoTrailLoop]
    rw [emitDirsNoTrailLoop_eq_append (y :: ys) ((emitDir0 out x).push 0x0a) hys]
  | x1 :: x2 :: xs, y :: ys, out, _, _, hxs, hys => by
    have htl : ∀ d' ∈ x2 :: xs, DirSubset0 d' :=
      fun d' hd => hxs d' (List.mem_cons_of_mem x1 hd)
    have ih := emitDirsNoTrailLoop_append_nonempty (x2 :: xs) (y :: ys)
      ((emitDir0 out x1).push 0x0a) (List.cons_ne_nil x2 xs) (List.cons_ne_nil y ys) htl hys
    dsimp only [List.cons_append, PrintAsm0.emitDirsNoTrailLoop] at ih ⊢
    exact ih

private theorem toATT_nil_eq : Kraken.X64.toATT [] = "" := by
  have h := printAmd64Asm0NoTrail_eq_toATT [] (fun _ hx => by cases hx)
  have he : printAmd64Asm0NoTrail [] = "".toUTF8 := by
    dsimp only [printAmd64Asm0NoTrail, PrintAsm0.emitDirsNoTrailLoop]
    rw [emptyWithCapacity_eq_empty, toUTF8_empty]
  rw [he] at h
  have h2 := congrArg String.fromUTF8! h.symm
  rwa [fromUTF8!_toUTF8, fromUTF8!_toUTF8] at h2

private theorem toATT_append_nonempty (xs ys : _root_.Program) (hxs : xs ≠ []) (hys : ys ≠ [])
    (hxsub : ∀ d' ∈ xs, DirSubset0 d') (hysub : ∀ d' ∈ ys, DirSubset0 d') :
    Kraken.X64.toATT (xs ++ ys) = Kraken.X64.toATT xs ++ "\n" ++ Kraken.X64.toATT ys := by
  have hall : ∀ d' ∈ xs ++ ys, DirSubset0 d' := fun d' hd => by
    rcases List.mem_append.mp hd with h | h
    · exact hxsub d' h
    · exact hysub d' h
  have hxy := printAmd64Asm0NoTrail_eq_toATT (xs ++ ys) hall
  have hx := printAmd64Asm0NoTrail_eq_toATT xs hxsub
  have hy := printAmd64Asm0NoTrail_eq_toATT ys hysub
  have hsplit := emitDirsNoTrailLoop_append_nonempty xs ys ByteArray.empty hxs hys hxsub hysub
  have hxy2 : printAmd64Asm0NoTrail (xs ++ ys) =
      (printAmd64Asm0NoTrail xs).push 0x0a ++ printAmd64Asm0NoTrail ys := by
    dsimp only [printAmd64Asm0NoTrail]
    rw [emptyWithCapacity_eq_empty]
    exact hsplit
  rw [hxy, hx, hy, ba_push_eq_append _ 0x0a "\n" rfl, ← toUTF8_append, ← toUTF8_append] at hxy2
  have hstr := congrArg String.fromUTF8! hxy2
  rwa [fromUTF8!_toUTF8, fromUTF8!_toUTF8] at hstr

private theorem toAmd64Program_cons (symName : Sym0 → Sym) (d : Dir0) (ds : List Dir0) :
    toAmd64Program symName (d :: ds) = dir0ToAmd64 symName d ++ toAmd64Program symName ds :=
  List.flatMap_cons

private theorem toAmd64Program_ne_nil (symName : Sym0 → Sym) (d : Dir0) (ds : List Dir0) :
    toAmd64Program symName (d :: ds) ≠ [] := by
  rw [toAmd64Program_cons]
  intro h
  exact dir0ToAmd64_ne_nil symName d (List.append_eq_nil_iff.mp h).1

private theorem toAmd64Program_dirSubset0 (symName : Sym0 → Sym) (ds : List Dir0) :
    ∀ x ∈ toAmd64Program symName ds, DirSubset0 x := by
  intro x hx
  dsimp only [toAmd64Program] at hx
  rcases List.mem_flatMap.mp hx with ⟨d, _, hxd⟩
  exact dir0ToAmd64_dirSubset0_aux symName d x hxd

private theorem printDirs0Bytes_eq_toATT_aux (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) :
    ∀ (ds : List Dir0) (out : ByteArray),
      (∀ d ∈ ds, Dir0SymsOk symBytes symOffs symName d) →
      printDirs0Bytes symBytes symOffs ds out =
        out ++ (Kraken.X64.toATT (toAmd64Program symName ds)).toUTF8
  | [], out, _ => by
    dsimp only [printDirs0Bytes, toAmd64Program]
    rw [List.flatMap_nil, toATT_nil_eq, toUTF8_empty, ByteArray.append_empty]
  | [d], out, hok => by
    dsimp only [printDirs0Bytes]
    have hs : toAmd64Program symName [d] = dir0ToAmd64 symName d := by
      dsimp only [toAmd64Program]; simp
    rw [hs]
    exact printDir0Bytes_eq_toATT symBytes symOffs symName d out (hok d (List.mem_cons_self ..))
  | d :: d2 :: ds', out, hok => by
    have hd := hok d (List.mem_cons_self ..)
    have htl : ∀ x ∈ d2 :: ds', Dir0SymsOk symBytes symOffs symName x :=
      fun x hx => hok x (List.mem_cons_of_mem d hx)
    dsimp only [printDirs0Bytes]
    rw [printDir0Bytes_eq_toATT symBytes symOffs symName d out hd,
      ba_push_eq_append _ 0x0a "\n" rfl,
      printDirs0Bytes_eq_toATT_aux symBytes symOffs symName (d2 :: ds') _ htl,
      toAmd64Program_cons symName d (d2 :: ds'),
      toATT_append_nonempty (dir0ToAmd64 symName d) (toAmd64Program symName (d2 :: ds'))
        (dir0ToAmd64_ne_nil symName d) (toAmd64Program_ne_nil symName d2 ds')
        (dir0ToAmd64_dirSubset0 symName d) (toAmd64Program_dirSubset0 symName (d2 :: ds'))]
    simp only [toUTF8_append, ByteArray.append_assoc]

/-- Exact byte-for-byte equivalence between `printDirs0Bytes` and
`Kraken.X64.toATT (Bridge0.toAmd64Program symName ds)` (and hence `PrintAsm0.printAsm0`). -/
public theorem printDirs0Bytes_eq_toATT (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) (ds : List Dir0) (out : ByteArray)
    (hok : ∀ d ∈ ds, Dir0SymsOk symBytes symOffs symName d) :
    printDirs0Bytes symBytes symOffs ds out =
      out ++ (Kraken.X64.toATT (toAmd64Program symName ds)).toUTF8 :=
  printDirs0Bytes_eq_toATT_aux symBytes symOffs symName ds out hok

private theorem printDirs0LinesBytes_eq_toATT_aux (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) :
    ∀ (ds : List Dir0) (out : ByteArray),
      (∀ d ∈ ds, Dir0SymsOk symBytes symOffs symName d) →
      printDirs0LinesBytes symBytes symOffs ds out =
        out ++ (if ds.isEmpty then "" else
          Kraken.X64.toATT (toAmd64Program symName ds) ++ "\n").toUTF8
  | [], out, _ => by
    dsimp only [printDirs0LinesBytes]
    simp only [List.isEmpty_nil, ↓reduceIte, toUTF8_empty, ByteArray.append_empty]
  | d :: ds', out, hok => by
    have hd := hok d (List.mem_cons_self ..)
    have htl : ∀ x ∈ ds', Dir0SymsOk symBytes symOffs symName x :=
      fun x hx => hok x (List.mem_cons_of_mem d hx)
    dsimp only [printDirs0LinesBytes]
    rw [printDir0Bytes_eq_toATT symBytes symOffs symName d out hd,
      ba_push_eq_append _ 0x0a "\n" rfl,
      printDirs0LinesBytes_eq_toATT_aux symBytes symOffs symName ds' _ htl]
    cases ds' with
    | nil =>
      have hs : toAmd64Program symName [d] = dir0ToAmd64 symName d := by
        dsimp only [toAmd64Program]; simp
      simp only [List.isEmpty_nil, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hs,
        toUTF8_empty, toUTF8_append, ByteArray.append_empty, ByteArray.append_assoc]
    | cons d2 ds2 =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      rw [toAmd64Program_cons symName d (d2 :: ds2),
        toATT_append_nonempty (dir0ToAmd64 symName d) (toAmd64Program symName (d2 :: ds2))
          (dir0ToAmd64_ne_nil symName d) (toAmd64Program_ne_nil symName d2 ds2)
          (dir0ToAmd64_dirSubset0 symName d) (toAmd64Program_dirSubset0 symName (d2 :: ds2))]
      simp only [toUTF8_append, ByteArray.append_assoc, String.append_assoc]

/-- Exact byte-for-byte equivalence between `printDirs0LinesBytes` and `'\n'`-terminated
`Kraken.X64.toATT (Bridge0.toAmd64Program symName ds)`. -/
public theorem printDirs0LinesBytes_eq_toATT (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) (ds : List Dir0) (out : ByteArray)
    (hok : ∀ d ∈ ds, Dir0SymsOk symBytes symOffs symName d) :
    printDirs0LinesBytes symBytes symOffs ds out =
      out ++ (if ds.isEmpty then "" else
        Kraken.X64.toATT (toAmd64Program symName ds) ++ "\n").toUTF8 :=
  printDirs0LinesBytes_eq_toATT_aux symBytes symOffs symName ds out hok

private theorem printGlobl0Bytes_eq_aux (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) (hBa : symBytes.size < 2 ^ 64) (hOffs : symOffs.size < 2 ^ 64) :
    ∀ (fnSyms : List Sym0) (out : ByteArray),
      (∀ s ∈ fnSyms, SymSliceMatch symBytes symOffs symName s) →
      printGlobl0Bytes symBytes symOffs fnSyms out =
        out ++ (String.join (fnSyms.map fun s => s!".globl {symName s}\n")).toUTF8
  | [], out, _ => by
    dsimp only [printGlobl0Bytes]
    rw [List.map_nil, String.join_nil, toUTF8_empty, ByteArray.append_empty]
  | s :: rest, out, hs => by
    have h0 := hs s (List.mem_cons_self ..)
    have htl : ∀ x ∈ rest, SymSliceMatch symBytes symOffs symName x :=
      fun x hx => hs x (List.mem_cons_of_mem s hx)
    dsimp only [printGlobl0Bytes]
    have hpfx : PrintDir0.e4 (PrintDir0.e3 out 0x2e 0x67 0x6c) 0x6f 0x62 0x6c 0x20 =
        out ++ ".globl ".toUTF8 := by
      apply ba_eq_of_data_toList
      dsimp only [PrintDir0.e4, PrintDir0.e3]
      simp only [ba_push_data_toList, ByteArray.toList_data_append, List.append_assoc]
      rfl
    rw [hpfx, emitSym_eq symBytes symOffs symName s _ hBa hOffs h0,
      ba_push_eq_append _ 0x0a "\n" rfl,
      printGlobl0Bytes_eq_aux symBytes symOffs symName hBa hOffs rest _ htl,
      List.map_cons, String.join_cons]
    simp only [toUTF8_append, ByteArray.append_assoc, String.append_assoc]
    rfl

/-- Exact byte-for-byte equivalence for `.globl` header emission `printGlobl0Bytes`. -/
public theorem printGlobl0Bytes_eq (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) (hBa : symBytes.size < 2 ^ 64) (hOffs : symOffs.size < 2 ^ 64)
    (fnSyms : List Sym0) (out : ByteArray)
    (hs : ∀ s ∈ fnSyms, SymSliceMatch symBytes symOffs symName s) :
    printGlobl0Bytes symBytes symOffs fnSyms out =
      out ++ (String.join (fnSyms.map fun s => s!".globl {symName s}\n")).toUTF8 :=
  printGlobl0Bytes_eq_aux symBytes symOffs symName hBa hOffs fnSyms out hs

/-- Exact whole-module equivalence for `printModule0Bytes` against `.text\n` + `.globl` +
`Kraken.X64.toATT (Bridge0.toAmd64Program symName ds)`. -/
public theorem printModule0Bytes_eq_toATT (symBytes : ByteArray) (symOffs : Array Nat)
    (symName : Sym0 → Sym) (fnSyms : List Sym0) (ds : List Dir0)
    (hBa : symBytes.size < 2 ^ 64) (hOffs : symOffs.size < 2 ^ 64)
    (hFns : ∀ s ∈ fnSyms, SymSliceMatch symBytes symOffs symName s)
    (hDirs : ∀ d ∈ ds, Dir0SymsOk symBytes symOffs symName d) :
    printModule0Bytes symBytes symOffs fnSyms ds =
      (".text\n" ++
        String.join (fnSyms.map fun s => s!".globl {symName s}\n") ++
        if ds.isEmpty then "" else
          Kraken.X64.toATT (toAmd64Program symName ds) ++ "\n").toUTF8 := by
  dsimp only [printModule0Bytes]
  rw [emptyWithCapacity_eq_empty]
  have htxt : PrintDir0.e4 (PrintDir0.e2 ByteArray.empty 0x2e 0x74) 0x65 0x78 0x74 0x0a =
      ".text\n".toUTF8 := by
    apply ba_eq_of_data_toList
    dsimp only [PrintDir0.e4, PrintDir0.e2]
    simp only [ba_push_data_toList, List.append_assoc]
    rfl
  rw [htxt, printGlobl0Bytes_eq symBytes symOffs symName hBa hOffs fnSyms _ hFns,
    printDirs0LinesBytes_eq_toATT symBytes symOffs symName ds _ hDirs]
  simp only [toUTF8_append, ByteArray.append_assoc]

end LeanQbe.T.Bootstrap0
