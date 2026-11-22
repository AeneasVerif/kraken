module

public import LeanQbe.T.Amd64.PrintAsm0
public import LeanQbe.T.Amd64.Isa
public import LeanQbe.T.Driver
public import Kraken.X64.PrintATT
import all Kraken.X64.PrintATT
import all Kraken.X64.PrintIntel

/-!
# Bit-for-Bit Equivalence Proofs for Stage B (`PrintAsm0Lemmas`)

Proves byte- and string-level equivalence between `LeanQbe.T.Amd64.PrintAsm0` and Kraken's
reference AT&T assembly printer (`Kraken.X64.toATT` / `LeanQbe.T.Driver.emitAsm`) on every
directive in the `DirSubset0` envelope (which strictly contains all Stage-A `leanqbe0` / `Isel0` /
`Rega0` directives as well as the full scalar `x64ScalarTarget` / `x64Gpr` + `x64Frame` subset):

* `emitDir0_eq`: single-directive byte equivalence against `Kraken.X64.ATT.directive`.
* `printAmd64Asm0_eq_toATT` / `printAmd64Asm0NoTrail_eq_toATT`: byte equivalence on
  `List Directive`.
* `printAsm0_eq_toATT`: string equivalence `printAsm0 p = Kraken.X64.toATT p`.
* `printDir0Asm0_eq_emitAsm` / `printModule0_eq_toATT` / `printModule0_eq_driver_emitAsm`:
  whole-module equivalence including `.text\n` and `.globl <fn>\n` headers.

These proofs keep `PrintAsm0` completely outside the formal TCB relative to `Kraken.X64.PrintATT`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Kraken.X64

/-! ## 1. Decidable `DirSubset0` Envelope Predicate -/

/-- Supported constant expression subset for `PrintAsm0` (`.label _` and `.int64 _`). -/
@[expose] def isConst0 : ConstExpr → Bool
  | .label _ => true
  | .int64 _ => true
  | _ => false

/-- Supported addressing expression subset for `PrintAsm0` (64-bit addressing). -/
@[expose] def isAddr0 (a : AddrExpr) : Bool :=
  match a.base, a.disp with
  | some .rip, .sub e .after_current_instruction => isConst0 e
  | _, d => isConst0 d

/-- Supported `RegOrMem` subset for `PrintAsm0`. -/
@[expose] def isRm0 {w : Width} : RegOrMem w → Bool
  | .reg _ => true
  | .mem a => isAddr0 a

/-- Supported `Operand` subset for `PrintAsm0`. -/
@[expose] def isOpd0 {w : Width} : Operand w → Bool
  | .regOrMem x => isRm0 x
  | .imm e => isConst0 e

/-- Supported `ShiftCountExpr` subset for `PrintAsm0`. -/
@[expose] def isCount0 : ShiftCountExpr → Bool
  | .cl => true
  | .imm8 e => isConst0 e

/-- Supported `RelRegOrMem` jump/call target subset for `PrintAsm0`. -/
@[expose] def isTarget0 : RelRegOrMem → Bool
  | .rel (.sub e .after_current_instruction) => isConst0 e
  | .rel e => isConst0 e
  | .reg _ => true
  | .mem a => isAddr0 a

/-- Supported scalar `Operation` subset for `PrintAsm0` (all `27` Stage-A `leanqbe0` ops plus all
`19` `x64ScalarTarget` GPR extras = `46` scalar operations). -/
@[expose] def isOp0 {w : Width} : Operation w → Bool
  | .mov d x => isRm0 d && isOpd0 x
  | .movsx d x => isRm0 d && isRm0 x
  | .movzx d x => isRm0 d && isRm0 x
  | .setcc _ d => isRm0 d
  | .cmovcc _ _ x => isRm0 x
  | .lea _ a => isAddr0 a
  | .add d x => isRm0 d && isOpd0 x
  | .sub d x => isRm0 d && isOpd0 x
  | .and d x => isRm0 d && isOpd0 x
  | .or d x => isRm0 d && isOpd0 x
  | .xor d x => isRm0 d && isOpd0 x
  | .cmp a b => isRm0 a && isOpd0 b
  | .test a b => isRm0 a && isOpd0 b
  | .neg d => isRm0 d
  | .not d => isRm0 d
  | .mul x => isRm0 x
  | .div x => isRm0 x
  | .idiv x => isRm0 x
  | .imul1 x => isRm0 x
  | .imul none a b => isRm0 a && isOpd0 b
  | .mulx _ _ x => isRm0 x
  | .adc d x => isRm0 d && isOpd0 x
  | .sbb d x => isRm0 d && isOpd0 x
  | .adcx _ x => isRm0 x
  | .adox _ x => isRm0 x
  | .inc d => isRm0 d
  | .dec d => isRm0 d
  | .shl d c => isRm0 d && isCount0 c
  | .shr d c => isRm0 d && isCount0 c
  | .sar d c => isRm0 d && isCount0 c
  | .rol d c => isRm0 d && isCount0 c
  | .ror d c => isRm0 d && isCount0 c
  | .shld d _ c => isRm0 d && isCount0 c
  | .shrd d _ c => isRm0 d && isCount0 c
  | .bswap _ => true
  | .lzcnt _ x => isRm0 x
  | .tzcnt _ x => isRm0 x
  | .popcnt _ x => isRm0 x
  | .shlx _ x _ => isRm0 x
  | .shrx _ x _ => isRm0 x
  | .sarx _ x _ => isRm0 x
  | .rorx _ x i => isRm0 x && isConst0 i
  | .jcc _ _ => true
  | .jmp t => isTarget0 t
  | .call t => isTarget0 t
  | .ret => true
  | _ => false

/-- Decidable `Bool` check for the `DirSubset0` envelope. -/
@[expose] def isDir0 : Directive → Bool
  | .label _ => true
  | .instr (.regular .W64 _ op) => isOp0 op
  | _ => false

/-- Predicate characterizing every `Directive` supported by `PrintAsm0`. -/
@[expose] def DirSubset0 (d : Directive) : Prop :=
  isDir0 d = true

/-! ## 2. `ByteArray` / `String.toUTF8` Algebra Helpers -/

private theorem toString_str (s : String) : toString s = s := rfl

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

private theorem e2_eq_append (ba : ByteArray) (a b : UInt8) (s : String)
    (h : s.toUTF8.data.toList = [a, b]) : PrintAsm0.e2 ba a b = ba ++ s.toUTF8 := by
  apply ba_eq_of_data_toList
  dsimp only [PrintAsm0.e2]
  rw [ba_push_data_toList, ba_push_data_toList, ByteArray.toList_data_append, h,
    List.append_assoc]
  rfl

private theorem e3_eq_append (ba : ByteArray) (a b c : UInt8) (s : String)
    (h : s.toUTF8.data.toList = [a, b, c]) : PrintAsm0.e3 ba a b c = ba ++ s.toUTF8 := by
  apply ba_eq_of_data_toList
  dsimp only [PrintAsm0.e3]
  rw [ba_push_data_toList, ba_push_data_toList, ba_push_data_toList,
    ByteArray.toList_data_append, h, List.append_assoc, List.append_assoc]
  rfl

private theorem e4_eq_append (ba : ByteArray) (a b c d : UInt8) (s : String)
    (h : s.toUTF8.data.toList = [a, b, c, d]) : PrintAsm0.e4 ba a b c d = ba ++ s.toUTF8 := by
  apply ba_eq_of_data_toList
  dsimp only [PrintAsm0.e4]
  rw [ba_push_data_toList, ba_push_data_toList, ba_push_data_toList,
    ba_push_data_toList, ByteArray.toList_data_append, h, List.append_assoc,
    List.append_assoc, List.append_assoc]
  rfl

private theorem toUTF8_append (s t : String) : (s ++ t).toUTF8 = s.toUTF8 ++ t.toUTF8 := by
  rw [String.toUTF8_eq_toByteArray, String.toUTF8_eq_toByteArray,
    String.toUTF8_eq_toByteArray, String.toByteArray_append]

private theorem toUTF8_empty : "".toUTF8 = ByteArray.empty := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_empty]

private theorem toUTF8_concat_l (s1 s2 : String) (r : ByteArray) :
    s1.toUTF8 ++ (s2.toUTF8 ++ r) = (s1 ++ s2).toUTF8 ++ r := by
  rw [← ByteArray.append_assoc, ← toUTF8_append]

private theorem ite_true_eq {p : Prop} [Decidable p] {α : Sort _} {a b : α} (h : p) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

private theorem ite_false_eq {p : Prop} [Decidable p] {α : Sort _} {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

private theorem dite_true_eq {p : Prop} [Decidable p] {α : Sort _} {a : p → α} {b : ¬ p → α}
    (h : p) : (if h' : p then a h' else b h') = a h := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

private theorem fromUTF8!_toUTF8 (s : String) : String.fromUTF8! s.toUTF8 = s := by
  dsimp only [String.fromUTF8!]
  rw [String.toUTF8_eq_toByteArray, dite_true_eq s.isValidUTF8, String.fromUTF8_eq_ofByteArray]

private theorem emptyWithCapacity_eq_empty (c : Nat) :
    ByteArray.emptyWithCapacity c = ByteArray.empty := rfl

private theorem eCommaSp_eq (ba : ByteArray) :
    PrintAsm0.eCommaSp ba = ba ++ ", ".toUTF8 :=
  e2_eq_append ba 0x2c 0x20 ", " rfl

private theorem eWidth_eq (ba : ByteArray) (w : Width) :
    PrintAsm0.eWidth ba w = ba ++ (ATT.suffix w).toUTF8 := by
  cases w
  · exact ba_push_eq_append ba 0x62 "b" rfl
  · exact ba_push_eq_append ba 0x77 "w" rfl
  · exact ba_push_eq_append ba 0x6c "l" rfl
  · exact ba_push_eq_append ba 0x71 "q" rfl

/-! ## 3. String Byte Copy (`emitStr`) Equivalence -/

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

/-! ## 4. Exact `UInt64` / `Int64` Decimal Formatting Equivalence -/

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
    | zero =>
      rw [emitPowDown_zero, ba_push_data_toList, hd]
      rfl
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
        rw [Nat.pow_succ]
        omega
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
        rw [Nat.pow_succ]
        omega
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
      have hp : 10 ^ (k + 2) = 10 * 10 ^ (k + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hp]
      exact mod_ten_mul_div_ten m (10 ^ (k + 1)) (Nat.pow_pos (by omega))
    have hmod_mod : m % 10 ^ (k + 2) % 10 = m % 10 := by
      have hdvd : 10 ∣ 10 ^ (k + 2) := ⟨10 ^ (k + 1), by rw [Nat.pow_succ, Nat.mul_comm]⟩
      exact Nat.mod_mod_of_dvd m hdvd
    rw [hdiv, hmod_div, hmod_mod]

private theorem digitChar_0 : Nat.digitChar 0 = '0' := Nat.digitChar_eq_zero.mpr rfl
private theorem digitChar_1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
private theorem digitChar_2 : Nat.digitChar 2 = '2' := Nat.digitChar_eq_two.mpr rfl
private theorem digitChar_3 : Nat.digitChar 3 = '3' := Nat.digitChar_eq_three.mpr rfl
private theorem digitChar_4 : Nat.digitChar 4 = '4' := Nat.digitChar_eq_four.mpr rfl
private theorem digitChar_5 : Nat.digitChar 5 = '5' := Nat.digitChar_eq_five.mpr rfl
private theorem digitChar_6 : Nat.digitChar 6 = '6' := Nat.digitChar_eq_six.mpr rfl
private theorem digitChar_7 : Nat.digitChar 7 = '7' := Nat.digitChar_eq_seven.mpr rfl
private theorem digitChar_8 : Nat.digitChar 8 = '8' := Nat.digitChar_eq_eight.mpr rfl
private theorem digitChar_9 : Nat.digitChar 9 = '9' := Nat.digitChar_eq_nine.mpr rfl

private theorem digit_toUTF8_eq (d : Nat) (hd : d < 10) :
    (String.singleton d.digitChar).toUTF8.data.toList = [UInt8.ofNat (48 + d)] := by
  match d, hd with
  | 0, _ => rw [digitChar_0]; rfl
  | 1, _ => rw [digitChar_1]; rfl
  | 2, _ => rw [digitChar_2]; rfl
  | 3, _ => rw [digitChar_3]; rfl
  | 4, _ => rw [digitChar_4]; rfl
  | 5, _ => rw [digitChar_5]; rfl
  | 6, _ => rw [digitChar_6]; rfl
  | 7, _ => rw [digitChar_7]; rfl
  | 8, _ => rw [digitChar_8]; rfl
  | 9, _ => rw [digitChar_9]; rfl
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

private theorem emitU64Dec_eq (ba : ByteArray) (n : UInt64) :
    PrintAsm0.emitU64Dec ba n = ba ++ (Nat.repr n.toNat).toUTF8 := by
  obtain ⟨k, hk, hpow, hlow, hlt⟩ := pow10Up_spec_aux n 20 0 rfl (by omega) (Or.inl rfl)
  apply ba_eq_of_data_toList
  dsimp only [PrintAsm0.emitU64Dec]
  rw [show (1 : UInt64) = UInt64.ofNat (10 ^ 0) from rfl, hpow]
  rw [emitPowDown_eq_digitsPow10 k 20 ba n (by omega) hk hlt]
  rw [digitsPow10_eq_natRepr k n.toNat hlow hlt, ByteArray.toList_data_append]

private theorem int64_toInt_eq_u64 (i : Int64) :
    ((i.toUInt64 >>> 63) = 1 →
      i.toInt = -((0 - i.toUInt64).toNat : Int) ∧ 0 < (0 - i.toUInt64).toNat) ∧
    ((i.toUInt64 >>> 63) ≠ 1 → i.toInt = (i.toUInt64.toNat : Int)) := by
  have hlt : i.toUInt64.toNat < 2 ^ 64 := i.toUInt64.toNat_lt_size
  have hsh : (i.toUInt64 >>> 63).toNat = i.toUInt64.toNat / 2 ^ 63 := by
    rw [UInt64.toNat_shiftRight]
    change i.toUInt64.toNat >>> (63 % 64) = i.toUInt64.toNat / 2 ^ 63
    rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  have htoInt : i.toInt =
      if 2 * i.toUInt64.toNat < 2 ^ 64 then (i.toUInt64.toNat : Int)
      else (i.toUInt64.toNat : Int) - (2 ^ 64 : Nat) := rfl
  rw [htoInt]
  constructor
  · intro hneg
    have hq : i.toUInt64.toNat / 2 ^ 63 = 1 := by
      have := congrArg UInt64.toNat hneg
      rwa [hsh] at this
    have hcond : ¬ (2 * i.toUInt64.toNat < 2 ^ 64) := by omega
    simp only [hcond, ↓reduceIte]
    have hsub : (0 - i.toUInt64).toNat = 2 ^ 64 - i.toUInt64.toNat := by
      rw [UInt64.toNat_sub, UInt64.toNat_zero, Nat.add_zero]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hsub]
    omega
  · intro hpos
    have hq : i.toUInt64.toNat / 2 ^ 63 = 0 := by
      match Nat.eq_zero_or_pos (i.toUInt64.toNat / 2 ^ 63) with
      | .inl hz => exact hz
      | .inr hp =>
        exfalso
        apply hpos
        apply UInt64.eq_of_toBitVec_eq
        apply BitVec.eq_of_toNat_eq
        change (i.toUInt64 >>> 63).toNat = 1
        omega
    have hcond : 2 * i.toUInt64.toNat < 2 ^ 64 := by omega
    simp only [hcond, ↓reduceIte]

private theorem emitI64Dec_eq (ba : ByteArray) (i : Int64) :
    PrintAsm0.emitI64Dec ba i.toUInt64 = ba ++ (toString i).toUTF8 := by
  have ⟨hneg, hpos⟩ := int64_toInt_eq_u64 i
  change PrintAsm0.emitI64Dec ba i.toUInt64 = ba ++ (Int.repr i.toInt).toUTF8
  dsimp only [PrintAsm0.emitI64Dec]
  by_cases h : (i.toUInt64 >>> 63) = 1
  · simp only [h, beq_self_eq_true, ↓reduceIte]
    obtain ⟨hi, hm⟩ := hneg h
    rw [hi, Int.repr_eq_ite]
    have hneg_lt : ¬ (0 ≤ -((0 - i.toUInt64).toNat : Int)) := by omega
    simp only [hneg_lt, ↓reduceIte, Int.neg_neg, Int.toNat_natCast]
    rw [emitU64Dec_eq, toUTF8_append, ba_push_eq_append ba 0x2d "-" rfl, ByteArray.append_assoc]
  · have hbf : ((i.toUInt64 >>> 63) == 1) = false := beq_false_of_ne h
    simp only [hbf, Bool.false_eq_true, ↓reduceIte]
    rw [hpos h, Int.repr_eq_ite]
    have hge0 : (0 : Int) ≤ (i.toUInt64.toNat : Int) := Int.natCast_nonneg _
    simp only [hge0, ↓reduceIte, Int.toNat_natCast]
    exact emitU64Dec_eq ba i.toUInt64

/-! ## 5. Registers, Condition Codes, Constants, Addresses, Operands -/

private theorem emitReg64_ext_eq (ba : ByteArray) (w : Width) (r : Reg64) (idx : UInt64)
    (hidx : PrintAsm0.regExtNum r = idx) (hge : idx ≥ 8) :
    PrintAsm0.emitReg64 ba w r =
      ba ++ ("%r" ++ Nat.repr idx.toNat ++
        match w with | .W64 => "" | .W32 => "d" | .W16 => "w" | .W8 => "b").toUTF8 := by
  dsimp only [PrintAsm0.emitReg64]
  rw [hidx, ite_true_eq hge]
  rw [ba_push_eq_append ba 0x25 "%" rfl, ba_push_eq_append _ 0x72 "r" rfl,
    ByteArray.append_assoc, ← toUTF8_append, emitU64Dec_eq]
  have hpr : "%" ++ "r" = "%r" := rfl
  rw [hpr]
  cases w
  · rw [ba_push_eq_append _ 0x62 "b" rfl, toUTF8_append, toUTF8_append, ByteArray.append_assoc,
      ByteArray.append_assoc]
  · rw [ba_push_eq_append _ 0x77 "w" rfl, toUTF8_append, toUTF8_append, ByteArray.append_assoc,
      ByteArray.append_assoc]
  · rw [ba_push_eq_append _ 0x64 "d" rfl, toUTF8_append, toUTF8_append, ByteArray.append_assoc,
      ByteArray.append_assoc]
  · rw [String.append_empty, toUTF8_append, ByteArray.append_assoc]

private theorem emitReg64_lo_eq (ba : ByteArray) (w : Width) (r : Reg64)
    (hlo : PrintAsm0.regExtNum r = 0) :
    PrintAsm0.emitReg64 ba w r =
      match w with
      | .W64 => PrintAsm0.regPairBytes ((ba.push 0x25).push 0x72) r
      | .W32 => PrintAsm0.regPairBytes ((ba.push 0x25).push 0x65) r
      | .W16 => PrintAsm0.regPairBytes (ba.push 0x25) r
      | .W8 => PrintAsm0.regLow8Bytes (ba.push 0x25) r := by
  dsimp only [PrintAsm0.emitReg64]
  rw [hlo]
  have hlt : ¬ ((0 : UInt64) ≥ 8) := by decide
  rw [ite_false_eq hlt]
  rfl

private theorem nat_repr_1d (d : Nat) (hd : d < 10) (c : Char) (hc : Nat.digitChar d = c) :
    Nat.repr d = String.singleton c := by
  rw [Nat.repr_of_lt hd, hc]

private theorem u64_repr_1d (u : UInt64) (d : Nat) (hu : u.toNat = d) (hd : d < 10) (c : Char)
    (hc : Nat.digitChar d = c) : Nat.repr u.toNat = String.singleton c := by
  rw [hu, Nat.repr_of_lt hd, hc]

private theorem u64_repr_2d (u : UInt64) (n : Nat) (hu : u.toNat = n) (h10 : 10 ≤ n)
    (hd1 : n / 10 < 10) (c1 c2 : Char)
    (hc1 : Nat.digitChar (n / 10) = c1) (hc2 : Nat.digitChar (n % 10) = c2) :
    Nat.repr u.toNat = String.singleton c1 ++ String.singleton c2 := by
  rw [hu, Nat.repr_of_ge h10, Nat.repr_of_lt hd1, hc1, hc2]

private theorem emitReg64_eq (ba : ByteArray) (w : Width) (r : Reg64) :
    PrintAsm0.emitReg64 ba w r = ba ++ (ATT.reg (Reg.low r w)).toUTF8 := by
  cases r with
  | rax | rbx | rcx | rdx | rsi | rdi | rsp | rbp =>
    rw [emitReg64_lo_eq ba w _ rfl]
    cases w <;> (
      apply ba_eq_of_data_toList
      dsimp only [PrintAsm0.regPairBytes, PrintAsm0.regLow8Bytes, PrintAsm0.e2, PrintAsm0.e3]
      simp only [ba_push_data_toList, ByteArray.toList_data_append, List.append_assoc]
      rfl)
  | r8 =>
    rw [emitReg64_ext_eq ba w .r8 8 rfl (by decide),
      u64_repr_1d 8 8 rfl (by omega) '8' digitChar_8]
    cases w <;> rfl
  | r9 =>
    rw [emitReg64_ext_eq ba w .r9 9 rfl (by decide),
      u64_repr_1d 9 9 rfl (by omega) '9' digitChar_9]
    cases w <;> rfl
  | r10 =>
    rw [emitReg64_ext_eq ba w .r10 10 rfl (by decide),
      u64_repr_2d 10 10 rfl (by omega) (by omega) '1' '0' digitChar_1 digitChar_0]
    cases w <;> rfl
  | r11 =>
    rw [emitReg64_ext_eq ba w .r11 11 rfl (by decide),
      u64_repr_2d 11 11 rfl (by omega) (by omega) '1' '1' digitChar_1 digitChar_1]
    cases w <;> rfl
  | r12 =>
    rw [emitReg64_ext_eq ba w .r12 12 rfl (by decide),
      u64_repr_2d 12 12 rfl (by omega) (by omega) '1' '2' digitChar_1 digitChar_2]
    cases w <;> rfl
  | r13 =>
    rw [emitReg64_ext_eq ba w .r13 13 rfl (by decide),
      u64_repr_2d 13 13 rfl (by omega) (by omega) '1' '3' digitChar_1 digitChar_3]
    cases w <;> rfl
  | r14 =>
    rw [emitReg64_ext_eq ba w .r14 14 rfl (by decide),
      u64_repr_2d 14 14 rfl (by omega) (by omega) '1' '4' digitChar_1 digitChar_4]
    cases w <;> rfl
  | r15 =>
    rw [emitReg64_ext_eq ba w .r15 15 rfl (by decide),
      u64_repr_2d 15 15 rfl (by omega) (by omega) '1' '5' digitChar_1 digitChar_5]
    cases w <;> rfl

private theorem emitReg_eq (ba : ByteArray) {w : Width} (r : Reg w) :
    PrintAsm0.emitReg ba w r = ba ++ (ATT.reg r).toUTF8 := by
  cases r with
  | low r64 w => exact emitReg64_eq ba w r64
  | ah => exact e3_eq_append ba 0x25 0x61 0x68 "%ah" rfl
  | bh => exact e3_eq_append ba 0x25 0x62 0x68 "%bh" rfl
  | ch => exact e3_eq_append ba 0x25 0x63 0x68 "%ch" rfl
  | dh => exact e3_eq_append ba 0x25 0x64 0x68 "%dh" rfl

private theorem emitCc_eq (ba : ByteArray) (cc : CondCode) :
    PrintAsm0.emitCc ba cc = ba ++ (toString cc).toUTF8 := by
  cases cc <;> (
    apply ba_eq_of_data_toList
    dsimp only [PrintAsm0.emitCc, PrintAsm0.emitCcHi, PrintAsm0.e2]
    simp only [ba_push_data_toList, ByteArray.toList_data_append, List.append_assoc]
    rfl)

private theorem emitConst_eq (ba : ByteArray) (e : ConstExpr) (h : isConst0 e = true) :
    PrintAsm0.emitConst ba e = ba ++ (ATT.const e).toUTF8 := by
  cases e with
  | label l => exact emitStr_eq ba l
  | int64 i => exact emitI64Dec_eq ba i
  | before_current_instruction | after_current_instruction | add _ _ | sub _ _ =>
    cases h

private theorem emitAddrDisp_i64_zero (ba : ByteArray) (hv : 0 < 2 ^ 64) :
    (if (Int64.ofBitVec ⟨⟨0, hv⟩⟩).toUInt64 == 0 then ba
      else PrintAsm0.emitI64Dec ba (Int64.ofBitVec ⟨⟨0, hv⟩⟩).toUInt64) = ba ++ "".toUTF8 := by
  have hz : ((Int64.ofBitVec ⟨⟨0, hv⟩⟩).toUInt64 == 0) = true := rfl
  rw [hz, ite_true_eq rfl, toUTF8_empty, ByteArray.append_empty]

private theorem emitAddrDisp_i64_succ (ba : ByteArray) (v : Nat) (hv : v + 1 < 2 ^ 64) :
    (if (Int64.ofBitVec ⟨⟨v + 1, hv⟩⟩).toUInt64 == 0 then ba
      else PrintAsm0.emitI64Dec ba (Int64.ofBitVec ⟨⟨v + 1, hv⟩⟩).toUInt64) =
      ba ++ (ATT.const (.int64 (Int64.ofBitVec ⟨⟨v + 1, hv⟩⟩))).toUTF8 := by
  have hu : ((Int64.ofBitVec ⟨⟨v + 1, hv⟩⟩).toUInt64 == 0) = false := by
    apply beq_false_of_ne
    intro heq
    exact Nat.succ_ne_zero v (congrArg UInt64.toNat heq)
  rw [hu, ite_false_eq Bool.false_ne_true]
  exact emitI64Dec_eq ba _

private theorem emitScaleByte_eq (ba : ByteArray) (s : Width) :
    PrintAsm0.emitScaleByte ba s = ba ++ (toString s.bytes).toUTF8 := by
  cases s
  · rw [show toString Width.W8.bytes = "1" from nat_repr_1d 1 (by omega) '1' digitChar_1]
    exact ba_push_eq_append ba 0x31 "1" rfl
  · rw [show toString Width.W16.bytes = "2" from nat_repr_1d 2 (by omega) '2' digitChar_2]
    exact ba_push_eq_append ba 0x32 "2" rfl
  · rw [show toString Width.W32.bytes = "4" from nat_repr_1d 4 (by omega) '4' digitChar_4]
    exact ba_push_eq_append ba 0x34 "4" rfl
  · rw [show toString Width.W64.bytes = "8" from nat_repr_1d 8 (by omega) '8' digitChar_8]
    exact ba_push_eq_append ba 0x38 "8" rfl

private theorem emitAddr_eq (ba : ByteArray) (a : AddrExpr) (h : isAddr0 a = true) :
    PrintAsm0.emitAddr ba a = ba ++ (ATT.addr .W64 a).toUTF8 := by
  rcases a with ⟨base, idx, disp⟩
  cases base with
  | none =>
    cases idx with
    | none =>
      dsimp only [PrintAsm0.emitAddr, ATT.addr]
      simp only [Option.isNone_none, Bool.and_self, ↓reduceIte]
      exact emitConst_eq ba disp h
    | some idx' =>
      rcases idx' with ⟨ir, is⟩
      dsimp only [PrintAsm0.emitAddr, ATT.addr]
      simp only [Option.isNone_none, Option.isNone_some, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte]
      rw [ba_push_eq_append _ 0x28 "(" rfl, ba_push_eq_append _ 0x2c "," rfl]
      rw [emitReg64_eq _ .W64 ir, ba_push_eq_append _ 0x2c "," rfl]
      rw [emitScaleByte_eq _ is, ba_push_eq_append _ 0x29 ")" rfl]
      simp only [toString_str, toUTF8_append, ByteArray.append_assoc, toUTF8_empty,
        ByteArray.empty_append]
      rw [← @ByteArray.append_assoc ba]
      apply congrArg (· ++ _)
      cases disp with
      | int64 i =>
        rcases i with ⟨⟨⟨v, hv⟩⟩⟩
        cases v with
        | zero => exact emitAddrDisp_i64_zero ba hv
        | succ v' => exact emitAddrDisp_i64_succ ba v' hv
      | label l => exact emitStr_eq ba l
      | before_current_instruction | after_current_instruction | add _ _ | sub _ _ => cases h
  | some b =>
    cases b with
    | reg br =>
      cases idx with
      | none =>
        dsimp only [PrintAsm0.emitAddr, ATT.addr]
        simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [ba_push_eq_append _ 0x28 "(" rfl, emitReg64_eq _ .W64 br]
        rw [ba_push_eq_append _ 0x29 ")" rfl]
        simp only [toString_str, String.append_empty, toUTF8_append, ByteArray.append_assoc]
        rw [← @ByteArray.append_assoc ba]
        apply congrArg (· ++ _)
        cases disp with
        | int64 i =>
          rcases i with ⟨⟨⟨v, hv⟩⟩⟩
          cases v with
          | zero => exact emitAddrDisp_i64_zero ba hv
          | succ v' => exact emitAddrDisp_i64_succ ba v' hv
        | label l => exact emitStr_eq ba l
        | before_current_instruction | after_current_instruction | add _ _ | sub _ _ => cases h
      | some idx' =>
        rcases idx' with ⟨ir, is⟩
        dsimp only [PrintAsm0.emitAddr, ATT.addr]
        simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [ba_push_eq_append _ 0x28 "(" rfl, emitReg64_eq _ .W64 br]
        rw [ba_push_eq_append _ 0x2c "," rfl, emitReg64_eq _ .W64 ir]
        rw [ba_push_eq_append _ 0x2c "," rfl, emitScaleByte_eq _ is]
        rw [ba_push_eq_append _ 0x29 ")" rfl]
        simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
        rw [← @ByteArray.append_assoc ba]
        apply congrArg (· ++ _)
        cases disp with
        | int64 i =>
          rcases i with ⟨⟨⟨v, hv⟩⟩⟩
          cases v with
          | zero => exact emitAddrDisp_i64_zero ba hv
          | succ v' => exact emitAddrDisp_i64_succ ba v' hv
        | label l => exact emitStr_eq ba l
        | before_current_instruction | after_current_instruction | add _ _ | sub _ _ => cases h
    | rip =>
      cases idx with
      | none =>
        dsimp only [PrintAsm0.emitAddr, ATT.addr]
        simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [ba_push_eq_append _ 0x28 "(" rfl, e4_eq_append _ 0x25 0x72 0x69 0x70 "%rip" rfl]
        rw [ba_push_eq_append _ 0x29 ")" rfl]
        simp only [toString_str, String.append_empty, toUTF8_append, ByteArray.append_assoc]
        rw [← @ByteArray.append_assoc ba]
        apply congrArg (· ++ _)
        cases disp with
        | int64 i =>
          rcases i with ⟨⟨⟨v, hv⟩⟩⟩
          cases v with
          | zero => exact emitAddrDisp_i64_zero ba hv
          | succ v' => exact emitAddrDisp_i64_succ ba v' hv
        | label l => exact emitStr_eq ba l
        | sub e rhs =>
          cases rhs with
          | after_current_instruction =>
            dsimp only [PrintAsm0.emitAddrDisp]
            exact emitConst_eq ba e h
          | label _ | int64 _ | before_current_instruction | add _ _ | sub _ _ => cases h
        | before_current_instruction | after_current_instruction | add _ _ => cases h
      | some idx' =>
        rcases idx' with ⟨ir, is⟩
        dsimp only [PrintAsm0.emitAddr, ATT.addr]
        simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [ba_push_eq_append _ 0x28 "(" rfl, e4_eq_append _ 0x25 0x72 0x69 0x70 "%rip" rfl]
        rw [ba_push_eq_append _ 0x2c "," rfl, emitReg64_eq _ .W64 ir]
        rw [ba_push_eq_append _ 0x2c "," rfl, emitScaleByte_eq _ is]
        rw [ba_push_eq_append _ 0x29 ")" rfl]
        simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
        rw [← @ByteArray.append_assoc ba]
        apply congrArg (· ++ _)
        cases disp with
        | int64 i =>
          rcases i with ⟨⟨⟨v, hv⟩⟩⟩
          cases v with
          | zero => exact emitAddrDisp_i64_zero ba hv
          | succ v' => exact emitAddrDisp_i64_succ ba v' hv
        | label l => exact emitStr_eq ba l
        | sub e rhs =>
          cases rhs with
          | after_current_instruction =>
            dsimp only [PrintAsm0.emitAddrDisp]
            exact emitConst_eq ba e h
          | label _ | int64 _ | before_current_instruction | add _ _ | sub _ _ => cases h
        | before_current_instruction | after_current_instruction | add _ _ => cases h

private theorem emitRm_eq (ba : ByteArray) {w : Width} (rm : RegOrMem w) (h : isRm0 rm = true) :
    PrintAsm0.emitRm ba w rm = ba ++ (ATT.rm .W64 rm).toUTF8 := by
  cases rm with
  | reg r => exact emitReg_eq ba r
  | mem a => exact emitAddr_eq ba a h

private theorem emitOpd_eq (ba : ByteArray) {w : Width} (x : Operand w) (h : isOpd0 x = true) :
    PrintAsm0.emitOpd ba w x = ba ++ (ATT.operand .W64 x).toUTF8 := by
  cases x with
  | regOrMem rm => exact emitRm_eq ba rm h
  | imm e =>
    dsimp only [PrintAsm0.emitOpd, ATT.operand]
    rw [emitConst_eq _ e h, ba_push_eq_append ba 0x24 "$" rfl, toUTF8_append,
      ByteArray.append_assoc]

private theorem emitCount_eq (ba : ByteArray) (c : ShiftCountExpr) (h : isCount0 c = true) :
    PrintAsm0.emitCount ba c = ba ++ (ATT.count c).toUTF8 := by
  cases c with
  | cl => exact e3_eq_append ba 0x25 0x63 0x6c "%cl" rfl
  | imm8 e =>
    dsimp only [PrintAsm0.emitCount, ATT.count]
    rw [emitConst_eq _ e h, ba_push_eq_append ba 0x24 "$" rfl, toUTF8_append,
      ByteArray.append_assoc]

private theorem emitTarget_eq (ba : ByteArray) (t : RelRegOrMem) (h : isTarget0 t = true) :
    PrintAsm0.emitTarget ba t = ba ++ (ATT.target .W64 t).toUTF8 := by
  cases t with
  | rel e =>
    cases e with
    | sub a b =>
      cases b with
      | after_current_instruction =>
        dsimp only [PrintAsm0.emitTarget, ATT.target]
        exact emitConst_eq ba a h
      | label _ | int64 _ | before_current_instruction | add _ _ | sub _ _ =>
        cases h
    | label l => exact emitStr_eq ba l
    | int64 i => exact emitI64Dec_eq ba i
    | before_current_instruction | after_current_instruction | add _ _ =>
      cases h
  | reg r => exact emitReg_eq ba r
  | mem a => exact emitAddr_eq ba a h

/-! ## 6. Shared Operation-Format Lemmas & Complete `Operation` Equivalence -/

private theorem eOp1W_eq (ba : ByteArray) (mn : String) {w : Width} (d : RegOrMem w)
    (hd : isRm0 d = true) :
    PrintAsm0.eOp1W (ba ++ mn.toUTF8) w d =
      ba ++ s!"{mn}{ATT.suffix w} {ATT.rm .W64 d}".toUTF8 := by
  dsimp only [PrintAsm0.eOp1W]
  rw [eWidth_eq, ba_push_eq_append _ 0x20 " " rfl, emitRm_eq _ d hd]
  simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

private theorem eOp2W_eq (ba : ByteArray) (mn : String) {w : Width}
    (d : RegOrMem w) (x : Operand w) (hd : isRm0 d = true) (hx : isOpd0 x = true) :
    PrintAsm0.eOp2W (ba ++ mn.toUTF8) w d x =
      ba ++ s!"{mn}{ATT.suffix w} {ATT.operand .W64 x}, {ATT.rm .W64 d}".toUTF8 := by
  dsimp only [PrintAsm0.eOp2W]
  rw [eWidth_eq, ba_push_eq_append _ 0x20 " " rfl, emitOpd_eq _ x hx, eCommaSp_eq, emitRm_eq _ d hd]
  simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

private theorem eShW_eq (ba : ByteArray) (mn : String) {w : Width}
    (d : RegOrMem w) (c : ShiftCountExpr) (hd : isRm0 d = true) (hc : isCount0 c = true) :
    PrintAsm0.eShW (ba ++ mn.toUTF8) w d c =
      ba ++ s!"{mn}{ATT.suffix w} {ATT.count c}, {ATT.rm .W64 d}".toUTF8 := by
  dsimp only [PrintAsm0.eShW]
  rw [eWidth_eq, ba_push_eq_append _ 0x20 " " rfl, emitCount_eq _ c hc, eCommaSp_eq,
    emitRm_eq _ d hd]
  simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

private theorem eRmReg_eq (ba : ByteArray) (mn : String) {w : Width}
    (d : Reg w) (x : RegOrMem w) (hx : isRm0 x = true) :
    PrintAsm0.eRmReg (ba ++ mn.toUTF8) w d x =
      ba ++ s!"{mn} {ATT.rm .W64 x}, {ATT.reg d}".toUTF8 := by
  dsimp only [PrintAsm0.eRmReg]
  rw [ba_push_eq_append _ 0x20 " " rfl, emitRm_eq _ x hx, eCommaSp_eq, emitReg_eq _ d]
  simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

private theorem eBmi2Shift_eq (ba : ByteArray) (mn : String) {w : Width}
    (d : Reg w) (x : RegOrMem w) (c : Reg w) (hx : isRm0 x = true) :
    PrintAsm0.eBmi2Shift (ba ++ mn.toUTF8) w d x c =
      ba ++ s!"{mn} {ATT.reg c}, {ATT.rm .W64 x}, {ATT.reg d}".toUTF8 := by
  dsimp only [PrintAsm0.eBmi2Shift]
  rw [ba_push_eq_append _ 0x20 " " rfl, emitReg_eq _ c, eCommaSp_eq, emitRm_eq _ x hx,
    eCommaSp_eq, emitReg_eq _ d]
  simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

private theorem emitOpData_eq (ba : ByteArray) {w : Width} (op : Operation w)
    (h : isOp0 op = true) :
    PrintAsm0.emitOpData ba w op = ba ++ (ATT.operation .W64 op).toUTF8 := by
  cases op with
  | mov d x =>
    have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, ATT.operation]
    rw [e3_eq_append ba 0x6d 0x6f 0x76 "mov" rfl]
    exact eOp2W_eq ba "mov" d x hd hx
  | @movsx w' d x =>
    have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h
    cases x with
    | mem a =>
      dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitMovExt, ATT.operation]
      simp only [↓reduceIte]
      rw [e4_eq_append ba 0x6d 0x6f 0x76 0x73 "movs" rfl, eWidth_eq, eWidth_eq,
        ba_push_eq_append _ 0x20 " " rfl, emitAddr_eq _ a hx, eCommaSp_eq, emitRm_eq _ d hd]
      change _ = ba ++
        s!"movs{ATT.suffix w'}{ATT.suffix w} {ATT.addr .W64 a}, {ATT.rm .W64 d}".toUTF8
      simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
    | reg r =>
      dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitMovExt, ATT.operation]
      simp only [↓reduceIte]
      rw [e4_eq_append ba 0x6d 0x6f 0x76 0x73 "movs" rfl, e2_eq_append _ 0x78 0x20 "x " rfl,
        emitReg_eq _ r, eCommaSp_eq, emitRm_eq _ d hd]
      change _ = ba ++ s!"movsx {ATT.reg r}, {ATT.rm .W64 d}".toUTF8
      simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
      rw [toUTF8_concat_l "movs" "x "]
      rfl
  | @movzx w' d x =>
    have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h
    cases x with
    | mem a =>
      dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitMovExt, ATT.operation]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [e4_eq_append ba 0x6d 0x6f 0x76 0x7a "movz" rfl, eWidth_eq, eWidth_eq,
        ba_push_eq_append _ 0x20 " " rfl, emitAddr_eq _ a hx, eCommaSp_eq, emitRm_eq _ d hd]
      change _ = ba ++
        s!"movz{ATT.suffix w'}{ATT.suffix w} {ATT.addr .W64 a}, {ATT.rm .W64 d}".toUTF8
      simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
    | reg r =>
      dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitMovExt, ATT.operation]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [e4_eq_append ba 0x6d 0x6f 0x76 0x7a "movz" rfl, e2_eq_append _ 0x78 0x20 "x " rfl,
        emitReg_eq _ r, eCommaSp_eq, emitRm_eq _ d hd]
      change _ = ba ++ s!"movzx {ATT.reg r}, {ATT.rm .W64 d}".toUTF8
      simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
      rw [toUTF8_concat_l "movz" "x "]
      rfl
  | setcc cc d =>
    dsimp only [PrintAsm0.emitOpData, ATT.operation]
    rw [e3_eq_append ba 0x73 0x65 0x74 "set" rfl, emitCc_eq,
      ba_push_eq_append _ 0x20 " " rfl, emitRm_eq _ d h]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  | cmovcc cc d x =>
    dsimp only [PrintAsm0.emitOpData, ATT.operation]
    rw [e4_eq_append ba 0x63 0x6d 0x6f 0x76 "cmov" rfl, emitCc_eq,
      ByteArray.append_assoc, ← toUTF8_append]
    rw [eRmReg_eq ba ("cmov" ++ toString cc) d x h]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  | lea d a =>
    dsimp only [PrintAsm0.emitOpData, ATT.operation]
    rw [e4_eq_append ba 0x6c 0x65 0x61 0x20 "lea " rfl, emitAddr_eq _ a h,
      eCommaSp_eq, emitReg_eq _ d]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  | add d x =>
    have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, ATT.operation]
    rw [e3_eq_append ba 0x61 0x64 0x64 "add" rfl]
    exact eOp2W_eq ba "add" d x hd hx
  | sub d x =>
    have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, ATT.operation]
    rw [e3_eq_append ba 0x73 0x75 0x62 "sub" rfl]
    exact eOp2W_eq ba "sub" d x hd hx
  | and d x =>
    have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, ATT.operation]
    rw [e3_eq_append ba 0x61 0x6e 0x64 "and" rfl]
    exact eOp2W_eq ba "and" d x hd hx
  | or d x =>
    have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, ATT.operation]
    rw [e2_eq_append ba 0x6f 0x72 "or" rfl]
    exact eOp2W_eq ba "or" d x hd hx
  | xor d x =>
    have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, ATT.operation]
    rw [e3_eq_append ba 0x78 0x6f 0x72 "xor" rfl]
    exact eOp2W_eq ba "xor" d x hd hx
  | cmp a b =>
    have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2, ATT.operation]
    rw [e3_eq_append ba 0x63 0x6d 0x70 "cmp" rfl]
    exact eOp2W_eq ba "cmp" a b ha hb
  | test a b =>
    have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2, ATT.operation]
    rw [e4_eq_append ba 0x74 0x65 0x73 0x74 "test" rfl]
    exact eOp2W_eq ba "test" a b ha hb
  | neg d =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2, ATT.operation]
    rw [e3_eq_append ba 0x6e 0x65 0x67 "neg" rfl]
    exact eOp1W_eq ba "neg" d h
  | not d =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2, ATT.operation]
    rw [e3_eq_append ba 0x6e 0x6f 0x74 "not" rfl]
    exact eOp1W_eq ba "not" d h
  | mul x =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, ATT.operation]
    rw [e3_eq_append ba 0x6d 0x75 0x6c "mul" rfl]
    exact eOp1W_eq ba "mul" x h
  | div x =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, ATT.operation]
    rw [e3_eq_append ba 0x64 0x69 0x76 "div" rfl]
    exact eOp1W_eq ba "div" x h
  | idiv x =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, ATT.operation]
    rw [e4_eq_append ba 0x69 0x64 0x69 0x76 "idiv" rfl]
    exact eOp1W_eq ba "idiv" x h
  | imul1 x =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, ATT.operation]
    rw [e4_eq_append ba 0x69 0x6d 0x75 0x6c "imul" rfl]
    exact eOp1W_eq ba "imul" x h
  | imul d a b =>
    cases d with
    | none =>
      have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
      dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
        PrintAsm0.emitOpMulDiv, ATT.operation]
      rw [e4_eq_append ba 0x69 0x6d 0x75 0x6c "imul" rfl]
      exact eOp2W_eq ba "imul" a b ha hb
    | some _ => cases h
  | mulx hi lo x =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, ATT.operation]
    rw [e4_eq_append ba 0x6d 0x75 0x6c 0x78 "mulx" rfl, ba_push_eq_append _ 0x20 " " rfl,
      emitRm_eq _ x h, eCommaSp_eq, emitReg_eq _ lo, eCommaSp_eq, emitReg_eq _ hi]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
    rw [toUTF8_concat_l "mulx" " "]
    rfl
  | adc d x =>
    have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, ATT.operation]
    rw [e3_eq_append ba 0x61 0x64 0x63 "adc" rfl]
    exact eOp2W_eq ba "adc" d x hd hx
  | sbb d x =>
    have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, ATT.operation]
    rw [e3_eq_append ba 0x73 0x62 0x62 "sbb" rfl]
    exact eOp2W_eq ba "sbb" d x hd hx
  | adcx d x =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, ATT.operation]
    rw [e4_eq_append ba 0x61 0x64 0x63 0x78 "adcx" rfl]
    exact eRmReg_eq ba "adcx" d x h
  | adox d x =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, ATT.operation]
    rw [e4_eq_append ba 0x61 0x64 0x6f 0x78 "adox" rfl]
    exact eRmReg_eq ba "adox" d x h
  | inc d =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, ATT.operation]
    rw [e3_eq_append ba 0x69 0x6e 0x63 "inc" rfl]
    exact eOp1W_eq ba "inc" d h
  | dec d =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, ATT.operation]
    rw [e3_eq_append ba 0x64 0x65 0x63 "dec" rfl]
    exact eOp1W_eq ba "dec" d h
  | shl d c =>
    have ⟨hd, hc⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1, ATT.operation]
    rw [e3_eq_append ba 0x73 0x68 0x6c "shl" rfl]
    exact eShW_eq ba "shl" d c hd hc
  | shr d c =>
    have ⟨hd, hc⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1, ATT.operation]
    rw [e3_eq_append ba 0x73 0x68 0x72 "shr" rfl]
    exact eShW_eq ba "shr" d c hd hc
  | sar d c =>
    have ⟨hd, hc⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1, ATT.operation]
    rw [e3_eq_append ba 0x73 0x61 0x72 "sar" rfl]
    exact eShW_eq ba "sar" d c hd hc
  | rol d c =>
    have ⟨hd, hc⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, ATT.operation]
    rw [e3_eq_append ba 0x72 0x6f 0x6c "rol" rfl]
    exact eShW_eq ba "rol" d c hd hc
  | ror d c =>
    have ⟨hd, hc⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, ATT.operation]
    rw [e3_eq_append ba 0x72 0x6f 0x72 "ror" rfl]
    exact eShW_eq ba "ror" d c hd hc
  | shld d x c =>
    have ⟨hd, hc⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, ATT.operation]
    rw [e4_eq_append ba 0x73 0x68 0x6c 0x64 "shld" rfl, ba_push_eq_append _ 0x20 " " rfl,
      emitCount_eq _ c hc, eCommaSp_eq, emitReg_eq _ x, eCommaSp_eq, emitRm_eq _ d hd]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
    rw [toUTF8_concat_l "shld" " "]
    rfl
  | shrd d x c =>
    have ⟨hd, hc⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, ATT.operation]
    rw [e4_eq_append ba 0x73 0x68 0x72 0x64 "shrd" rfl, ba_push_eq_append _ 0x20 " " rfl,
      emitCount_eq _ c hc, eCommaSp_eq, emitReg_eq _ x, eCommaSp_eq, emitRm_eq _ d hd]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
    rw [toUTF8_concat_l "shrd" " "]
    rfl
  | bswap d =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, ATT.operation]
    rw [e4_eq_append ba 0x62 0x73 0x77 0x61 "bswa" rfl, ba_push_eq_append _ 0x70 "p" rfl,
      ba_push_eq_append _ 0x20 " " rfl, emitReg_eq _ d]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
    rw [toUTF8_concat_l "p" " ", toUTF8_concat_l "bswa" ("p" ++ " ")]
    rfl
  | lzcnt d x =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, ATT.operation]
    have hmn : (PrintAsm0.e4 ba 0x6c 0x7a 0x63 0x6e).push 0x74 = ba ++ "lzcnt".toUTF8 := by
      rw [e4_eq_append ba 0x6c 0x7a 0x63 0x6e "lzcn" rfl, ba_push_eq_append _ 0x74 "t" rfl,
        ByteArray.append_assoc, ← toUTF8_append]; rfl
    rw [hmn]
    exact eRmReg_eq ba "lzcnt" d x h
  | tzcnt d x =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, ATT.operation]
    have hmn : (PrintAsm0.e4 ba 0x74 0x7a 0x63 0x6e).push 0x74 = ba ++ "tzcnt".toUTF8 := by
      rw [e4_eq_append ba 0x74 0x7a 0x63 0x6e "tzcn" rfl, ba_push_eq_append _ 0x74 "t" rfl,
        ByteArray.append_assoc, ← toUTF8_append]; rfl
    rw [hmn]
    exact eRmReg_eq ba "tzcnt" d x h
  | popcnt d x =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, ATT.operation]
    have hmn : PrintAsm0.e3 (PrintAsm0.e3 ba 0x70 0x6f 0x70) 0x63 0x6e 0x74 =
        ba ++ "popcnt".toUTF8 := by
      rw [e3_eq_append ba 0x70 0x6f 0x70 "pop" rfl, e3_eq_append _ 0x63 0x6e 0x74 "cnt" rfl,
        ByteArray.append_assoc, ← toUTF8_append]; rfl
    rw [hmn]
    exact eRmReg_eq ba "popcnt" d x h
  | shlx d x c =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, PrintAsm0.emitOpBmi2, ATT.operation]
    rw [e4_eq_append ba 0x73 0x68 0x6c 0x78 "shlx" rfl]
    exact eBmi2Shift_eq ba "shlx" d x c h
  | shrx d x c =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, PrintAsm0.emitOpBmi2, ATT.operation]
    rw [e4_eq_append ba 0x73 0x68 0x72 0x78 "shrx" rfl]
    exact eBmi2Shift_eq ba "shrx" d x c h
  | sarx d x c =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, PrintAsm0.emitOpBmi2, ATT.operation]
    rw [e4_eq_append ba 0x73 0x61 0x72 0x78 "sarx" rfl]
    exact eBmi2Shift_eq ba "sarx" d x c h
  | rorx d x i =>
    have ⟨hx, hi⟩ := Bool.and_eq_true_iff.mp h
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, PrintAsm0.emitOpBmi2, ATT.operation]
    rw [e4_eq_append ba 0x72 0x6f 0x72 0x78 "rorx" rfl, e2_eq_append _ 0x20 0x24 " $" rfl,
      emitConst_eq _ i hi, eCommaSp_eq, emitRm_eq _ x hx, eCommaSp_eq, emitReg_eq _ d]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
    rw [toUTF8_concat_l "rorx" " $"]
    rfl
  | jcc cc l =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, PrintAsm0.emitOpBmi2,
      PrintAsm0.emitOpCtrl, ATT.operation]
    rw [ba_push_eq_append ba 0x6a "j" rfl, emitCc_eq, ba_push_eq_append _ 0x20 " " rfl,
      emitStr_eq _ l]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  | jmp t =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, PrintAsm0.emitOpBmi2,
      PrintAsm0.emitOpCtrl, ATT.operation]
    rw [e4_eq_append ba 0x6a 0x6d 0x70 0x20 "jmp " rfl, emitTarget_eq _ t h]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  | call t =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, PrintAsm0.emitOpBmi2,
      PrintAsm0.emitOpCtrl, ATT.operation]
    rw [e4_eq_append ba 0x63 0x61 0x6c 0x6c "call" rfl, ba_push_eq_append _ 0x20 " " rfl,
      emitTarget_eq _ t h]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
    rw [toUTF8_concat_l "call" " "]
    rfl
  | ret =>
    dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
      PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
      PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, PrintAsm0.emitOpBmi2,
      PrintAsm0.emitOpCtrl, ATT.operation]
    exact e3_eq_append ba 0x72 0x65 0x74 "ret" rfl
  | push _ | pop _ | movs _ | stos _ | rcl _ _ | rcr _ _
  | cld | std | nop _ | nopalign _ _ =>
    cases h

/-! ## 7. Headline Directive, Program, and Module Equivalence Theorems -/

/-- Exact byte equivalence of `emitDir0` against `Kraken.X64.ATT.directive` on `DirSubset0`. -/
theorem emitDir0_eq (ba : ByteArray) (d : Directive) (h : DirSubset0 d) :
    emitDir0 ba d = ba ++ (ATT.directive d).toUTF8 := by
  cases d with
  | label l =>
    dsimp only [emitDir0, ATT.directive]
    rw [emitStr_eq ba l, ba_push_eq_append _ 0x3a ":" rfl]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  | instr ins =>
    cases ins with
    | regular aw w op =>
      cases aw with
      | W64 =>
        dsimp only [emitDir0, ATT.directive, ATT.instr]
        exact emitOpData_eq ba op h
      | W8 | W16 | W32 => cases h
    | avx _ _ _ => cases h
  | byteArray _ | word _ _ => cases h

private theorem emitDirsLineLoop_nil (ba : ByteArray) :
    PrintAsm0.emitDirsLineLoop ba [] = ba := rfl

private theorem emitDirsLineLoop_cons (ba : ByteArray) (d : Directive) (ds : List Directive) :
    PrintAsm0.emitDirsLineLoop ba (d :: ds) =
      PrintAsm0.emitDirsLineLoop ((emitDir0 ba d).push 0x0a) ds := rfl

private theorem emitDirsNoTrailLoop_nil (ba : ByteArray) :
    PrintAsm0.emitDirsNoTrailLoop ba [] = ba := rfl

private theorem emitDirsNoTrailLoop_singleton (ba : ByteArray) (d : Directive) :
    PrintAsm0.emitDirsNoTrailLoop ba [d] = emitDir0 ba d := rfl

private theorem emitDirsNoTrailLoop_cons_cons (ba : ByteArray) (d d2 : Directive)
    (ds : List Directive) :
    PrintAsm0.emitDirsNoTrailLoop ba (d :: d2 :: ds) =
      PrintAsm0.emitDirsNoTrailLoop ((emitDir0 ba d).push 0x0a) (d2 :: ds) := rfl

private theorem emitGloblLoop_nil (ba : ByteArray) :
    PrintAsm0.emitGloblLoop ba [] = ba := rfl

private theorem emitGloblLoop_cons (ba : ByteArray) (fn : String) (rest : List String) :
    PrintAsm0.emitGloblLoop ba (fn :: rest) =
      let ba' := PrintAsm0.e4 (PrintAsm0.e3 ba 0x2e 0x67 0x6c) 0x6f 0x62 0x6c 0x20
      PrintAsm0.emitGloblLoop ((PrintAsm0.emitStr ba' fn).push 0x0a) rest := rfl

private theorem toATT_def (p : List Directive) :
    Kraken.X64.toATT p = "\n".intercalate (p.map ATT.directive) := rfl

private theorem emitDirsLineLoop_eq (p : List Directive) (ba : ByteArray)
    (hsub : ∀ d ∈ p, DirSubset0 d) :
    PrintAsm0.emitDirsLineLoop ba p =
      ba ++ (if p.isEmpty then "" else Kraken.X64.toATT p ++ "\n").toUTF8 := by
  induction p generalizing ba with
  | nil =>
    rw [emitDirsLineLoop_nil]
    simp only [List.isEmpty_nil, ↓reduceIte, toUTF8_empty, ByteArray.append_empty]
  | cons d ds ih =>
    have hd : DirSubset0 d := hsub d (List.mem_cons_self ..)
    have hds : ∀ x ∈ ds, DirSubset0 x := fun x hx => hsub x (List.mem_cons_of_mem d hx)
    rw [emitDirsLineLoop_cons, emitDir0_eq ba d hd, ba_push_eq_append _ 0x0a "\n" rfl, ih _ hds]
    cases ds with
    | nil =>
      simp only [List.isEmpty_nil, ↓reduceIte, List.isEmpty_cons, Bool.false_eq_true]
      rw [toATT_def]
      simp only [List.map_cons, List.map_nil, String.intercalate_singleton,
        toUTF8_empty, toUTF8_append, ByteArray.append_empty, ByteArray.append_assoc]
    | cons d2 ds2 =>
      rw [toATT_def, toATT_def]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, String.intercalate_cons_cons, toUTF8_append, ByteArray.append_assoc]

private theorem emitDirsNoTrailLoop_eq (p : List Directive) (ba : ByteArray)
    (hsub : ∀ d ∈ p, DirSubset0 d) :
    PrintAsm0.emitDirsNoTrailLoop ba p = ba ++ (Kraken.X64.toATT p).toUTF8 := by
  induction p generalizing ba with
  | nil =>
    rw [emitDirsNoTrailLoop_nil, toATT_def, List.map_nil,
      String.intercalate_nil, toUTF8_empty, ByteArray.append_empty]
  | cons d ds ih =>
    have hd : DirSubset0 d := hsub d (List.mem_cons_self ..)
    have hds : ∀ x ∈ ds, DirSubset0 x := fun x hx => hsub x (List.mem_cons_of_mem d hx)
    cases ds with
    | nil =>
      rw [emitDirsNoTrailLoop_singleton, toATT_def, List.map_cons, List.map_nil,
        String.intercalate_singleton]
      exact emitDir0_eq ba d hd
    | cons d2 ds2 =>
      rw [emitDirsNoTrailLoop_cons_cons, emitDir0_eq ba d hd,
        ba_push_eq_append _ 0x0a "\n" rfl, ih _ hds, toATT_def, toATT_def]
      simp only [List.map_cons, String.intercalate_cons_cons, toUTF8_append,
        ByteArray.append_assoc]

private theorem emitGloblLoop_eq (fnNames : List String) (ba : ByteArray) :
    PrintAsm0.emitGloblLoop ba fnNames =
      ba ++ (String.join (fnNames.map fun n => s!".globl {n}\n")).toUTF8 := by
  induction fnNames generalizing ba with
  | nil =>
    rw [emitGloblLoop_nil, List.map_nil, String.join_nil, toUTF8_empty, ByteArray.append_empty]
  | cons fn rest ih =>
    rw [emitGloblLoop_cons]
    have hpfx : PrintAsm0.e4 (PrintAsm0.e3 ba 0x2e 0x67 0x6c) 0x6f 0x62 0x6c 0x20 =
        ba ++ ".globl ".toUTF8 := by
      rw [e3_eq_append ba 0x2e 0x67 0x6c ".gl" rfl,
        e4_eq_append _ 0x6f 0x62 0x6c 0x20 "obl " rfl,
        ByteArray.append_assoc, ← toUTF8_append]; rfl
    dsimp only
    rw [hpfx, emitStr_eq, ba_push_eq_append _ 0x0a "\n" rfl, ih]
    rw [List.map_cons, String.join_cons]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

/-- Exact UTF-8 byte equivalence between `printAmd64Asm0` and `Kraken.X64.toATT` (with trailing
newline on non-empty programs). -/
theorem printAmd64Asm0_eq_toATT (p : List Directive) (hsub : ∀ d ∈ p, DirSubset0 d) :
    printAmd64Asm0 p =
      (if p.isEmpty then "" else Kraken.X64.toATT p ++ "\n").toUTF8 := by
  dsimp only [printAmd64Asm0]
  rw [emptyWithCapacity_eq_empty, emitDirsLineLoop_eq p ByteArray.empty hsub,
    ByteArray.empty_append]

/-- Exact UTF-8 byte equivalence between `printAmd64Asm0NoTrail` and `Kraken.X64.toATT`. -/
theorem printAmd64Asm0NoTrail_eq_toATT (p : List Directive) (hsub : ∀ d ∈ p, DirSubset0 d) :
    printAmd64Asm0NoTrail p = (Kraken.X64.toATT p).toUTF8 := by
  dsimp only [printAmd64Asm0NoTrail]
  rw [emptyWithCapacity_eq_empty, emitDirsNoTrailLoop_eq p ByteArray.empty hsub,
    ByteArray.empty_append]

/-- Exact `String` equivalence between `printAsm0` and `Kraken.X64.toATT` on `DirSubset0`. -/
theorem printAsm0_eq_toATT (p : List Directive) (hsub : ∀ d ∈ p, DirSubset0 d) :
    printAsm0 p = Kraken.X64.toATT p := by
  dsimp only [printAsm0]
  rw [printAmd64Asm0NoTrail_eq_toATT p hsub, fromUTF8!_toUTF8]

/-- Exact UTF-8 byte equivalence between `printDir0Asm0` and `.text` + `.globl` +
`Kraken.X64.toATT`. -/
theorem printDir0Asm0_eq_emitAsm (fnNames : List String) (p : List Directive)
    (hsub : ∀ d ∈ p, DirSubset0 d) :
    printDir0Asm0 fnNames p =
      (".text\n" ++
        String.join (fnNames.map fun n => s!".globl {n}\n") ++
        if p.isEmpty then "" else Kraken.X64.toATT p ++ "\n").toUTF8 := by
  dsimp only [printDir0Asm0]
  rw [emptyWithCapacity_eq_empty]
  have htxt : PrintAsm0.e4 (PrintAsm0.e2 ByteArray.empty 0x2e 0x74) 0x65 0x78 0x74 0x0a =
      ".text\n".toUTF8 := by
    rw [e2_eq_append ByteArray.empty 0x2e 0x74 ".t" rfl,
      e4_eq_append _ 0x65 0x78 0x74 0x0a "ext\n" rfl,
      ByteArray.empty_append, ← toUTF8_append]; rfl
  rw [htxt, emitGloblLoop_eq fnNames, emitDirsLineLoop_eq p _ hsub]
  simp only [toUTF8_append, ByteArray.append_assoc]

/-- Exact `String` equivalence between `printModule0` and `.text` + `.globl` +
`Kraken.X64.toATT`. -/
theorem printModule0_eq_toATT (fnNames : List String) (p : List Directive)
    (hsub : ∀ d ∈ p, DirSubset0 d) :
    printModule0 fnNames p =
      ".text\n" ++
        String.join (fnNames.map fun n => s!".globl {n}\n") ++
        if p.isEmpty then "" else Kraken.X64.toATT p ++ "\n" := by
  dsimp only [printModule0]
  rw [printDir0Asm0_eq_emitAsm fnNames p hsub, fromUTF8!_toUTF8]

/-- Exact `String` equivalence between `printModule0` and `LeanQbe.T.Driver.emitAsm` wired with
`fun code => Kraken.X64.toATT code ++ "\n"` on any non-empty `DirSubset0` program. -/
theorem printModule0_eq_driver_emitAsm (fs : List LeanQbe.T.Fn) (p : List Directive)
    (hne : p ≠ []) (hsub : ∀ d ∈ p, DirSubset0 d) :
    printModule0 (fs.map (·.name)) p =
      LeanQbe.T.Driver.emitAsm (I := x64Isa) (fun code => Kraken.X64.toATT code ++ "\n") fs p := by
  have hempty : p.isEmpty = false := by
    cases p with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  dsimp only [LeanQbe.T.Driver.emitAsm]
  rw [printModule0_eq_toATT (fs.map (·.name)) p hsub, hempty]
  simp only [Bool.false_eq_true, ↓reduceIte, List.map_map]
  rfl

end LeanQbe.T.Amd64
