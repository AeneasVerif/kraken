module

public import LeanQbe.T.Amd64.PrintAsm0
public import LeanQbe.T.Amd64.Isa
public import LeanQbe.T.Driver
public import Kraken.X64.PrintATT
import LeanQbe.T.Logic.ByteArrayDecimal
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
open ByteArrayDecimal

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

private theorem e2_eq_append (ba : ByteArray) (a b : UInt8) (s : String)
    (h : s.toUTF8.data.toList = [a, b]) : PrintAsm0.e2 ba a b = ba ++ s.toUTF8 :=
  ba_push2_eq_append ba a b s h

private theorem e3_eq_append (ba : ByteArray) (a b c : UInt8) (s : String)
    (h : s.toUTF8.data.toList = [a, b, c]) : PrintAsm0.e3 ba a b c = ba ++ s.toUTF8 :=
  ba_push3_eq_append ba a b c s h

private theorem e4_eq_append (ba : ByteArray) (a b c d : UInt8) (s : String)
    (h : s.toUTF8.data.toList = [a, b, c, d]) : PrintAsm0.e4 ba a b c d = ba ++ s.toUTF8 :=
  ba_push4_eq_append ba a b c d s h

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

private theorem emitStr_eq (ba : ByteArray) (s : String) :
    PrintAsm0.emitStr ba s = ba ++ s.toUTF8 :=
  emitStr_eq_of_steps PrintAsm0.emitStrLoop
    (fun _ _ _ h => by rw [PrintAsm0.emitStrLoop.eq_def]; simp only [h, ↓reduceDIte])
    (fun _ _ _ h => by rw [PrintAsm0.emitStrLoop.eq_def]; simp only [h, ↓reduceDIte])
    ba s

/-! ## 4. Exact `UInt64` / `Int64` Decimal Formatting Equivalence -/

private theorem emitU64Dec_eq (ba : ByteArray) (n : UInt64) :
    PrintAsm0.emitU64Dec ba n = ba ++ (Nat.repr n.toNat).toUTF8 :=
  emitU64Dec_eq_of_steps PrintAsm0.pow10Up PrintAsm0.emitPowDown
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) ba n

private theorem emitI64Dec_eq (ba : ByteArray) (i : Int64) :
    PrintAsm0.emitI64Dec ba i.toUInt64 = ba ++ (toString i).toUTF8 :=
  emitI64Dec_eq_of_u64 PrintAsm0.emitU64Dec emitU64Dec_eq ba i

/-! ## 5. Registers, Condition Codes, Constants, Addresses, Operands -/

private theorem emitReg64_ext_eq (ba : ByteArray) (w : Width) (r : Reg64) (idx : UInt64)
    (hidx : PrintAsm0.regExtNum r = idx) (hge : idx ≥ 8) :
    PrintAsm0.emitReg64 ba w r =
      ba ++ ("%r" ++ Nat.repr idx.toNat ++
        match w with | .W64 => "" | .W32 => "d" | .W16 => "w" | .W8 => "b").toUTF8 := by
  dsimp only [PrintAsm0.emitReg64]
  rw [hidx]
  simp only [hge, ↓reduceIte]
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
  simp only [hlt, ↓reduceIte]
  rfl

private theorem emitReg64_ext1 {ba : ByteArray} {w : Width} {r : Reg64} {idx : UInt64} {c : Char}
    (hidx : PrintAsm0.regExtNum r = idx) (hge : idx ≥ 8) (hd : idx.toNat < 10)
    (hc : Nat.digitChar idx.toNat = c)
    (hatt : ∀ w, ATT.reg (Reg.low r w) = "%r" ++ String.singleton c ++
      match w with | .W64 => "" | .W32 => "d" | .W16 => "w" | .W8 => "b") :
    PrintAsm0.emitReg64 ba w r = ba ++ (ATT.reg (Reg.low r w)).toUTF8 := by
  rw [emitReg64_ext_eq ba w r idx hidx hge, u64_repr_1d idx idx.toNat rfl hd c hc, hatt w]

private theorem emitReg64_ext2 {ba : ByteArray} {w : Width} {r : Reg64} {idx : UInt64}
    {c1 c2 : Char} (hidx : PrintAsm0.regExtNum r = idx) (hge : idx ≥ 8) (h10 : 10 ≤ idx.toNat)
    (hd1 : idx.toNat / 10 < 10) (hc1 : Nat.digitChar (idx.toNat / 10) = c1)
    (hc2 : Nat.digitChar (idx.toNat % 10) = c2)
    (hatt : ∀ w, ATT.reg (Reg.low r w) = "%r" ++ (String.singleton c1 ++ String.singleton c2) ++
      match w with | .W64 => "" | .W32 => "d" | .W16 => "w" | .W8 => "b") :
    PrintAsm0.emitReg64 ba w r = ba ++ (ATT.reg (Reg.low r w)).toUTF8 := by
  rw [emitReg64_ext_eq ba w r idx hidx hge,
    u64_repr_2d idx idx.toNat rfl h10 hd1 c1 c2 hc1 hc2, hatt w]

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
    exact emitReg64_ext1 (r := .r8) (idx := 8) rfl (by decide) (by decide) digitChar_8
      (fun w => by cases w <;> rfl)
  | r9 =>
    exact emitReg64_ext1 (r := .r9) (idx := 9) rfl (by decide) (by decide) digitChar_9
      (fun w => by cases w <;> rfl)
  | r10 =>
    exact emitReg64_ext2 (r := .r10) (idx := 10) rfl (by decide) (by decide) (by decide)
      digitChar_1 digitChar_0 (fun w => by cases w <;> rfl)
  | r11 =>
    exact emitReg64_ext2 (r := .r11) (idx := 11) rfl (by decide) (by decide) (by decide)
      digitChar_1 digitChar_1 (fun w => by cases w <;> rfl)
  | r12 =>
    exact emitReg64_ext2 (r := .r12) (idx := 12) rfl (by decide) (by decide) (by decide)
      digitChar_1 digitChar_2 (fun w => by cases w <;> rfl)
  | r13 =>
    exact emitReg64_ext2 (r := .r13) (idx := 13) rfl (by decide) (by decide) (by decide)
      digitChar_1 digitChar_3 (fun w => by cases w <;> rfl)
  | r14 =>
    exact emitReg64_ext2 (r := .r14) (idx := 14) rfl (by decide) (by decide) (by decide)
      digitChar_1 digitChar_4 (fun w => by cases w <;> rfl)
  | r15 =>
    exact emitReg64_ext2 (r := .r15) (idx := 15) rfl (by decide) (by decide) (by decide)
      digitChar_1 digitChar_5 (fun w => by cases w <;> rfl)

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
  simp only [hz, ↓reduceIte, toUTF8_empty, ByteArray.append_empty]

private theorem emitAddrDisp_i64_succ (ba : ByteArray) (v : Nat) (hv : v + 1 < 2 ^ 64) :
    (if (Int64.ofBitVec ⟨⟨v + 1, hv⟩⟩).toUInt64 == 0 then ba
      else PrintAsm0.emitI64Dec ba (Int64.ofBitVec ⟨⟨v + 1, hv⟩⟩).toUInt64) =
      ba ++ (ATT.const (.int64 (Int64.ofBitVec ⟨⟨v + 1, hv⟩⟩))).toUTF8 := by
  have hu : ((Int64.ofBitVec ⟨⟨v + 1, hv⟩⟩).toUInt64 == 0) = false := by
    apply beq_false_of_ne
    intro heq
    exact Nat.succ_ne_zero v (congrArg UInt64.toNat heq)
  simp only [hu, Bool.false_eq_true, ↓reduceIte]
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

private theorem emitAddrDisp_eq (ba : ByteArray) (base : Option RegOrRip) (disp : ConstExpr)
    (h : (match base, disp with
      | some .rip, .sub e .after_current_instruction => isConst0 e
      | _, d => isConst0 d) = true) :
    PrintAsm0.emitAddrDisp ba base disp =
      ba ++ (match base, disp with
        | some .rip, .sub e .after_current_instruction => ATT.const e
        | _, .int64 0 => ""
        | _, d => ATT.const d).toUTF8 := by
  cases disp with
  | int64 i =>
    rcases i with ⟨⟨⟨v, hv⟩⟩⟩
    rcases base with _ | ⟨_ | _⟩ <;> cases v <;>
      first | exact emitAddrDisp_i64_zero ba hv | exact emitAddrDisp_i64_succ ba _ hv
  | label l => rcases base with _ | ⟨_ | _⟩ <;> exact emitStr_eq ba l
  | sub e rhs =>
    rcases base with _ | ⟨_ | _⟩
    · cases h
    · cases h
    · cases rhs <;> first | exact emitConst_eq ba e h | cases h
  | before_current_instruction | after_current_instruction | add _ _ =>
    rcases base with _ | ⟨_ | _⟩ <;> cases h

private theorem emitAddrBase_eq (ba : ByteArray) (base : Option RegOrRip) :
    (match base with
      | some (.reg r) => PrintAsm0.emitReg64 ba .W64 r
      | some .rip => PrintAsm0.e4 ba 0x25 0x72 0x69 0x70
      | none => ba) =
      ba ++ (match base with
        | some (.reg r) => ATT.reg (.low r .W64)
        | some .rip => "%rip"
        | none => "").toUTF8 := by
  rcases base with _ | ⟨r | _⟩
  · rw [toUTF8_empty, ByteArray.append_empty]
  · exact emitReg64_eq ba .W64 r
  · exact e4_eq_append ba 0x25 0x72 0x69 0x70 "%rip" rfl

private theorem emitAddrIdx_eq (ba : ByteArray) (idx : Option AddrIndex) :
    (match idx with
      | some idx' =>
        PrintAsm0.emitScaleByte ((PrintAsm0.emitReg64 (ba.push 0x2c) .W64 idx'.reg).push 0x2c)
          idx'.scale
      | none => ba) =
      ba ++ (match idx with
        | some ⟨r, s⟩ => s!",{ATT.reg (.low r .W64)},{s.bytes}"
        | none => "").toUTF8 := by
  rcases idx with _ | ⟨r, s⟩
  · rw [toUTF8_empty, ByteArray.append_empty]
  · dsimp only
    rw [ba_push_eq_append _ 0x2c "," rfl, emitReg64_eq _ .W64 r,
      ba_push_eq_append _ 0x2c "," rfl, emitScaleByte_eq _ s]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

private theorem emitAddr_nonAbs_eq (ba : ByteArray) (base : Option RegOrRip)
    (idx : Option AddrIndex) (disp : ConstExpr)
    (h : (match base, disp with
      | some .rip, .sub e .after_current_instruction => isConst0 e
      | _, d => isConst0 d) = true)
    (hnone : (base.isNone && idx.isNone) = false) :
    (let ba1 := (PrintAsm0.emitAddrDisp ba base disp).push 0x28
     let ba2 := match base with
       | some (.reg r) => PrintAsm0.emitReg64 ba1 .W64 r
       | some .rip => PrintAsm0.e4 ba1 0x25 0x72 0x69 0x70
       | none => ba1
     let ba3 := match idx with
       | some idx' =>
         PrintAsm0.emitScaleByte ((PrintAsm0.emitReg64 (ba2.push 0x2c) .W64 idx'.reg).push 0x2c)
           idx'.scale
       | none => ba2
     ba3.push 0x29) = ba ++ (ATT.addr .W64 ⟨base, idx, disp⟩).toUTF8 := by
  dsimp only [ATT.addr]
  simp only [hnone, Bool.false_eq_true, ↓reduceIte]
  rw [emitAddrDisp_eq ba base disp h, ba_push_eq_append _ 0x28 "(" rfl,
    emitAddrBase_eq, emitAddrIdx_eq, ba_push_eq_append _ 0x29 ")" rfl]
  simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  rfl

private theorem emitAddr_eq (ba : ByteArray) (a : AddrExpr) (h : isAddr0 a = true) :
    PrintAsm0.emitAddr ba a = ba ++ (ATT.addr .W64 a).toUTF8 := by
  rcases a with ⟨base, idx, disp⟩
  dsimp only [isAddr0] at h
  cases base with
  | none =>
    cases idx with
    | none =>
      dsimp only [PrintAsm0.emitAddr, ATT.addr]
      simp only [Option.isNone_none, Bool.and_self, ↓reduceIte]
      exact emitConst_eq ba disp h
    | some idx' =>
      dsimp only [PrintAsm0.emitAddr]
      exact emitAddr_nonAbs_eq ba none (some idx') disp h rfl
  | some b =>
    cases idx with
    | none =>
      dsimp only [PrintAsm0.emitAddr]
      exact emitAddr_nonAbs_eq ba (some b) none disp h rfl
    | some idx' =>
      dsimp only [PrintAsm0.emitAddr]
      exact emitAddr_nonAbs_eq ba (some b) (some idx') disp h rfl

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
  | reg r =>
    dsimp only [PrintAsm0.emitTarget, ATT.target]
    rw [ba_push_eq_append ba 0x2a "*" rfl, emitReg_eq _ r, toUTF8_append, ByteArray.append_assoc]
  | mem a =>
    dsimp only [PrintAsm0.emitTarget, ATT.target]
    rw [ba_push_eq_append ba 0x2a "*" rfl, emitAddr_eq _ a h, toUTF8_append, ByteArray.append_assoc]

/-! ## 6. Shared Operation-Format Lemmas & Complete `Operation` Equivalence -/

private theorem eOp1W_eq {ba ba' : ByteArray} {mn : String} (hba : ba' = ba ++ mn.toUTF8)
    {w : Width} {d : RegOrMem w} (hd : isRm0 d = true) :
    PrintAsm0.eOp1W ba' w d = ba ++ s!"{mn}{ATT.suffix w} {ATT.rm .W64 d}".toUTF8 := by
  subst hba; dsimp only [PrintAsm0.eOp1W]
  rw [eWidth_eq, ba_push_eq_append _ 0x20 " " rfl, emitRm_eq _ d hd]
  simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

private theorem eOp2W_eq {ba ba' : ByteArray} {mn : String} (hba : ba' = ba ++ mn.toUTF8)
    {w : Width} {d : RegOrMem w} {x : Operand w} (h : (isRm0 d && isOpd0 x) = true) :
    PrintAsm0.eOp2W ba' w d x =
      ba ++ s!"{mn}{ATT.suffix w} {ATT.operand .W64 x}, {ATT.rm .W64 d}".toUTF8 := by
  have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h
  subst hba; dsimp only [PrintAsm0.eOp2W]
  rw [eWidth_eq, ba_push_eq_append _ 0x20 " " rfl, emitOpd_eq _ x hx, eCommaSp_eq, emitRm_eq _ d hd]
  simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

private theorem eShW_eq {ba ba' : ByteArray} {mn : String} (hba : ba' = ba ++ mn.toUTF8)
    {w : Width} {d : RegOrMem w} {c : ShiftCountExpr} (h : (isRm0 d && isCount0 c) = true) :
    PrintAsm0.eShW ba' w d c =
      ba ++ s!"{mn}{ATT.suffix w} {ATT.count c}, {ATT.rm .W64 d}".toUTF8 := by
  have ⟨hd, hc⟩ := Bool.and_eq_true_iff.mp h
  subst hba; dsimp only [PrintAsm0.eShW]
  rw [eWidth_eq, ba_push_eq_append _ 0x20 " " rfl, emitCount_eq _ c hc, eCommaSp_eq,
    emitRm_eq _ d hd]
  simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

private theorem eRmReg_eq {ba ba' : ByteArray} {mn : String} (hba : ba' = ba ++ mn.toUTF8)
    {w : Width} {d : Reg w} {x : RegOrMem w} (hx : isRm0 x = true) :
    PrintAsm0.eRmReg ba' w d x = ba ++ s!"{mn} {ATT.rm .W64 x}, {ATT.reg d}".toUTF8 := by
  subst hba; dsimp only [PrintAsm0.eRmReg]
  rw [ba_push_eq_append _ 0x20 " " rfl, emitRm_eq _ x hx, eCommaSp_eq, emitReg_eq _ d]
  simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

private theorem eBmi2Shift_eq {ba ba' : ByteArray} {mn : String} (hba : ba' = ba ++ mn.toUTF8)
    {w : Width} {d : Reg w} {x : RegOrMem w} {c : Reg w} (hx : isRm0 x = true) :
    PrintAsm0.eBmi2Shift ba' w d x c =
      ba ++ s!"{mn} {ATT.reg c}, {ATT.rm .W64 x}, {ATT.reg d}".toUTF8 := by
  subst hba; dsimp only [PrintAsm0.eBmi2Shift]
  rw [ba_push_eq_append _ 0x20 " " rfl, emitReg_eq _ c, eCommaSp_eq, emitRm_eq _ x hx,
    eCommaSp_eq, emitReg_eq _ d]
  simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

private theorem emitMovExt_eq (ba : ByteArray) {w w' : Width} (isSign : Bool)
    (d : RegOrMem w) (x : RegOrMem w') (hd : isRm0 d = true) (hx : isRm0 x = true) :
    PrintAsm0.emitMovExt ba w w' isSign d x =
      let pfx := if isSign then "movs" else "movz"
      ba ++ (match x with
        | .mem a => s!"{pfx}{ATT.suffix w'}{ATT.suffix w} {ATT.addr .W64 a}, {ATT.rm .W64 d}"
        | .reg r => s!"{pfx}x {ATT.reg r}, {ATT.rm .W64 d}").toUTF8 := by
  have htag : PrintAsm0.e4 ba 0x6d 0x6f 0x76 (if isSign then 0x73 else 0x7a) =
      ba ++ (if isSign then "movs" else "movz").toUTF8 := by
    cases isSign
    · exact e4_eq_append ba 0x6d 0x6f 0x76 0x7a "movz" rfl
    · exact e4_eq_append ba 0x6d 0x6f 0x76 0x73 "movs" rfl
  cases x with
  | mem a =>
    dsimp only [PrintAsm0.emitMovExt]
    rw [htag, eWidth_eq, eWidth_eq, ba_push_eq_append _ 0x20 " " rfl,
      emitAddr_eq _ a hx, eCommaSp_eq, emitRm_eq _ d hd]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  | reg r =>
    dsimp only [PrintAsm0.emitMovExt]
    rw [htag, e2_eq_append _ 0x78 0x20 "x " rfl,
      emitReg_eq _ r, eCommaSp_eq, emitRm_eq _ d hd]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

private theorem eShd_eq {ba ba' : ByteArray} {mn : String} (hba : ba' = ba ++ mn.toUTF8)
    {w : Width} {d : RegOrMem w} {x : Reg w} {c : ShiftCountExpr}
    (h : (isRm0 d && isCount0 c) = true) :
    PrintAsm0.emitRm (PrintAsm0.eCommaSp (PrintAsm0.emitReg (PrintAsm0.eCommaSp
      (PrintAsm0.emitCount (ba'.push 0x20) c)) w x)) w d =
      ba ++ s!"{mn} {ATT.count c}, {ATT.reg x}, {ATT.rm .W64 d}".toUTF8 := by
  have ⟨hd, hc⟩ := Bool.and_eq_true_iff.mp h
  subst hba
  rw [ba_push_eq_append _ 0x20 " " rfl, emitCount_eq _ c hc, eCommaSp_eq,
    emitReg_eq _ x, eCommaSp_eq, emitRm_eq _ d hd]
  simp only [toString_str, toUTF8_append, ByteArray.append_assoc]

local macro "unfold_emit_op" : tactic =>
  `(tactic| dsimp only [PrintAsm0.emitOpData, PrintAsm0.emitOpAlu1, PrintAsm0.emitOpAlu2,
    PrintAsm0.emitOpMulDiv, PrintAsm0.emitOpCarry, PrintAsm0.emitOpShift1,
    PrintAsm0.emitOpShift2, PrintAsm0.emitOpBitcnt, PrintAsm0.emitOpBmi2,
    PrintAsm0.emitOpCtrl, ATT.operation])

private theorem emitOpData_eq (ba : ByteArray) {w : Width} (op : Operation w)
    (h : isOp0 op = true) :
    PrintAsm0.emitOpData ba w op = ba ++ (ATT.operation .W64 op).toUTF8 := by
  cases op with
  | mov d x => unfold_emit_op; exact eOp2W_eq (e3_eq_append ba 0x6d 0x6f 0x76 "mov" rfl) h
  | movsx d x =>
    have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h; unfold_emit_op
    have he := emitMovExt_eq ba true d x hd hx; cases x <;> exact he
  | movzx d x =>
    have ⟨hd, hx⟩ := Bool.and_eq_true_iff.mp h; unfold_emit_op
    have he := emitMovExt_eq ba false d x hd hx; cases x <;> exact he
  | setcc cc d =>
    unfold_emit_op
    rw [e3_eq_append ba 0x73 0x65 0x74 "set" rfl, emitCc_eq,
      ba_push_eq_append _ 0x20 " " rfl, emitRm_eq _ d h]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  | cmovcc cc d x =>
    unfold_emit_op
    rw [e4_eq_append ba 0x63 0x6d 0x6f 0x76 "cmov" rfl, emitCc_eq,
      ByteArray.append_assoc, ← toUTF8_append, eRmReg_eq (mn := "cmov" ++ toString cc) rfl h]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  | lea d a =>
    unfold_emit_op
    rw [e4_eq_append ba 0x6c 0x65 0x61 0x20 "lea " rfl, emitAddr_eq _ a h,
      eCommaSp_eq, emitReg_eq _ d]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  | add d x => unfold_emit_op; exact eOp2W_eq (e3_eq_append ba 0x61 0x64 0x64 "add" rfl) h
  | sub d x => unfold_emit_op; exact eOp2W_eq (e3_eq_append ba 0x73 0x75 0x62 "sub" rfl) h
  | and d x => unfold_emit_op; exact eOp2W_eq (e3_eq_append ba 0x61 0x6e 0x64 "and" rfl) h
  | or d x => unfold_emit_op; exact eOp2W_eq (e2_eq_append ba 0x6f 0x72 "or" rfl) h
  | xor d x => unfold_emit_op; exact eOp2W_eq (e3_eq_append ba 0x78 0x6f 0x72 "xor" rfl) h
  | cmp a b => unfold_emit_op; exact eOp2W_eq (e3_eq_append ba 0x63 0x6d 0x70 "cmp" rfl) h
  | test a b =>
    unfold_emit_op; exact eOp2W_eq (e4_eq_append ba 0x74 0x65 0x73 0x74 "test" rfl) h
  | neg d => unfold_emit_op; exact eOp1W_eq (e3_eq_append ba 0x6e 0x65 0x67 "neg" rfl) h
  | not d => unfold_emit_op; exact eOp1W_eq (e3_eq_append ba 0x6e 0x6f 0x74 "not" rfl) h
  | mul x => unfold_emit_op; exact eOp1W_eq (e3_eq_append ba 0x6d 0x75 0x6c "mul" rfl) h
  | div x => unfold_emit_op; exact eOp1W_eq (e3_eq_append ba 0x64 0x69 0x76 "div" rfl) h
  | idiv x => unfold_emit_op; exact eOp1W_eq (e4_eq_append ba 0x69 0x64 0x69 0x76 "idiv" rfl) h
  | imul1 x => unfold_emit_op; exact eOp1W_eq (e4_eq_append ba 0x69 0x6d 0x75 0x6c "imul" rfl) h
  | imul d a b =>
    cases d with
    | none => unfold_emit_op; exact eOp2W_eq (e4_eq_append ba 0x69 0x6d 0x75 0x6c "imul" rfl) h
    | some _ => cases h
  | mulx hi lo x =>
    unfold_emit_op
    rw [e4_eq_append ba 0x6d 0x75 0x6c 0x78 "mulx" rfl, ba_push_eq_append _ 0x20 " " rfl,
      emitRm_eq _ x h, eCommaSp_eq, emitReg_eq _ lo, eCommaSp_eq, emitReg_eq _ hi]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
    rw [toUTF8_concat_l "mulx" " "]; rfl
  | adc d x => unfold_emit_op; exact eOp2W_eq (e3_eq_append ba 0x61 0x64 0x63 "adc" rfl) h
  | sbb d x => unfold_emit_op; exact eOp2W_eq (e3_eq_append ba 0x73 0x62 0x62 "sbb" rfl) h
  | adcx d x =>
    unfold_emit_op; exact eRmReg_eq (e4_eq_append ba 0x61 0x64 0x63 0x78 "adcx" rfl) h
  | adox d x =>
    unfold_emit_op; exact eRmReg_eq (e4_eq_append ba 0x61 0x64 0x6f 0x78 "adox" rfl) h
  | inc d => unfold_emit_op; exact eOp1W_eq (e3_eq_append ba 0x69 0x6e 0x63 "inc" rfl) h
  | dec d => unfold_emit_op; exact eOp1W_eq (e3_eq_append ba 0x64 0x65 0x63 "dec" rfl) h
  | shl d c => unfold_emit_op; exact eShW_eq (e3_eq_append ba 0x73 0x68 0x6c "shl" rfl) h
  | shr d c => unfold_emit_op; exact eShW_eq (e3_eq_append ba 0x73 0x68 0x72 "shr" rfl) h
  | sar d c => unfold_emit_op; exact eShW_eq (e3_eq_append ba 0x73 0x61 0x72 "sar" rfl) h
  | rol d c => unfold_emit_op; exact eShW_eq (e3_eq_append ba 0x72 0x6f 0x6c "rol" rfl) h
  | ror d c => unfold_emit_op; exact eShW_eq (e3_eq_append ba 0x72 0x6f 0x72 "ror" rfl) h
  | shld d x c =>
    unfold_emit_op; exact eShd_eq (e4_eq_append ba 0x73 0x68 0x6c 0x64 "shld" rfl) h
  | shrd d x c =>
    unfold_emit_op; exact eShd_eq (e4_eq_append ba 0x73 0x68 0x72 0x64 "shrd" rfl) h
  | bswap d =>
    unfold_emit_op
    rw [e4_eq_append ba 0x62 0x73 0x77 0x61 "bswa" rfl, ba_push_eq_append _ 0x70 "p" rfl,
      ba_push_eq_append _ 0x20 " " rfl, emitReg_eq _ d]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
    rw [toUTF8_concat_l "p" " ", toUTF8_concat_l "bswa" ("p" ++ " ")]; rfl
  | lzcnt d x =>
    unfold_emit_op
    have hmn : (PrintAsm0.e4 ba 0x6c 0x7a 0x63 0x6e).push 0x74 = ba ++ "lzcnt".toUTF8 := by
      rw [e4_eq_append ba 0x6c 0x7a 0x63 0x6e "lzcn" rfl, ba_push_eq_append _ 0x74 "t" rfl,
        ByteArray.append_assoc, ← toUTF8_append]; rfl
    exact eRmReg_eq hmn h
  | tzcnt d x =>
    unfold_emit_op
    have hmn : (PrintAsm0.e4 ba 0x74 0x7a 0x63 0x6e).push 0x74 = ba ++ "tzcnt".toUTF8 := by
      rw [e4_eq_append ba 0x74 0x7a 0x63 0x6e "tzcn" rfl, ba_push_eq_append _ 0x74 "t" rfl,
        ByteArray.append_assoc, ← toUTF8_append]; rfl
    exact eRmReg_eq hmn h
  | popcnt d x =>
    unfold_emit_op
    have hmn : PrintAsm0.e3 (PrintAsm0.e3 ba 0x70 0x6f 0x70) 0x63 0x6e 0x74 =
        ba ++ "popcnt".toUTF8 := by
      rw [e3_eq_append ba 0x70 0x6f 0x70 "pop" rfl, e3_eq_append _ 0x63 0x6e 0x74 "cnt" rfl,
        ByteArray.append_assoc, ← toUTF8_append]; rfl
    exact eRmReg_eq hmn h
  | shlx d x c =>
    unfold_emit_op; exact eBmi2Shift_eq (e4_eq_append ba 0x73 0x68 0x6c 0x78 "shlx" rfl) h
  | shrx d x c =>
    unfold_emit_op; exact eBmi2Shift_eq (e4_eq_append ba 0x73 0x68 0x72 0x78 "shrx" rfl) h
  | sarx d x c =>
    unfold_emit_op; exact eBmi2Shift_eq (e4_eq_append ba 0x73 0x61 0x72 0x78 "sarx" rfl) h
  | rorx d x i =>
    have ⟨hx, hi⟩ := Bool.and_eq_true_iff.mp h; unfold_emit_op
    rw [e4_eq_append ba 0x72 0x6f 0x72 0x78 "rorx" rfl, e2_eq_append _ 0x20 0x24 " $" rfl,
      emitConst_eq _ i hi, eCommaSp_eq, emitRm_eq _ x hx, eCommaSp_eq, emitReg_eq _ d]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
    rw [toUTF8_concat_l "rorx" " $"]; rfl
  | jcc cc l =>
    unfold_emit_op
    rw [ba_push_eq_append ba 0x6a "j" rfl, emitCc_eq, ba_push_eq_append _ 0x20 " " rfl,
      emitStr_eq _ l]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  | jmp t =>
    unfold_emit_op
    rw [e4_eq_append ba 0x6a 0x6d 0x70 0x20 "jmp " rfl, emitTarget_eq _ t h]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
  | call t =>
    unfold_emit_op
    rw [e4_eq_append ba 0x63 0x61 0x6c 0x6c "call" rfl, ba_push_eq_append _ 0x20 " " rfl,
      emitTarget_eq _ t h]
    simp only [toString_str, toUTF8_append, ByteArray.append_assoc]
    rw [toUTF8_concat_l "call" " "]; rfl
  | ret => unfold_emit_op; exact e3_eq_append ba 0x72 0x65 0x74 "ret" rfl
  | push _ | pop _ | movs _ | stos _ | rcl _ _ | rcr _ _
  | cld | std | nop _ | nopalign _ _ => cases h

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
