module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.IselLemmas4
meta import LeanQbe.T.Arm64.Isel
public meta import Kraken.AArch64.Print

/-!
# AArch64 `UXTW` (`zext 32 64`) Index & Address Folding Tests (`Arm64UxtwTest`)

Tests the standalone verified AArch64 `zext 32 64` index/address folding builders and specs:
1. Builder guards & instruction shapes for `armLoadZextIdx`, `armLoadSextZextIdx`,
   `armStoreZextIdx`, and `armLeaArithZext` (`ADD ... UXTW`, `[Xn, Wm, UXTW #sh]`, `UBFIZ`).
2. Kernel `rfl` directive/printer checks confirming emitted Kraken AArch64 mnemonics.
3. Verified `FallsTo` / `NoLab` theorems and `std3` axiom audit.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.Arm64UxtwTest

open LeanQbe.T LeanQbe.T.Arm64

/-! ## 1. Helper predicates & negative/positive builder checks -/

meta def isAddUxtwDir : Directive → Bool
  | .instr { operation := .ADD_e _ _ (.ext { ext := { type := .UXTW, .. }, .. }), .. } => true
  | _ => false

meta def hasMemUxtwOff : AddrExpr → Bool
  | { off := .reg { ext := { type := .UXTW, .. }, .. }, .. } => true
  | _ => false

meta def isMemUxtwDir : Directive → Bool
  | .instr { operation := .LDR _ (.addr a), .. }
  | .instr { operation := .LDRB _ a, .. }
  | .instr { operation := .LDRH _ a, .. }
  | .instr { operation := .LDRSB _ a, .. }
  | .instr { operation := .LDRSH _ a, .. }
  | .instr { operation := .STR _ a, .. }
  | .instr { operation := .STRB _ a, .. }
  | .instr { operation := .STRH _ a, .. } => hasMemUxtwOff a
  | _ => false

meta def isUbfiz32Dir : Directive → Bool
  | .instr { operation := .UBFM _ _ _ 31, .. } => true
  | _ => false

-- Negative guard checks (`SP`, bad shift, unencodable disp/scale)
#guard (armLoadZextIdx i32 (.reg .X0) .SP (.reg .X2) .s4 0).isNone
#guard (armLoadZextIdx i32 (.reg .X0) (.reg .X1) .SP .s4 0).isNone
#guard (armLoadZextIdx i32 (.reg .X0) (.reg .X1) (.reg .X2) .s8 0).isNone
#guard (armLoadZextIdx i32 (.reg .X0) (.reg .X1) (.reg .X2) .s4 0x123456).isNone
#guard (armLoadSextZextIdx 32 64 (.reg .X0) (.reg .X1) (.reg .X2) .s4 0).isNone
#guard (armLoadSextZextIdx 8 64 (.reg .X0) .SP (.reg .X2) .s1 0).isNone
#guard (armStoreZextIdx i64 (.gpr (.reg .X0)) (.reg .X1) .SP .s8 0).isNone
#guard (armStoreZextIdx i64 (.gpr (.reg .X0)) (.reg .X1) (.reg .X2) .s4 (-16384)).isNone
#guard (armLeaArithZext (some (.reg .X1)) (.reg .X2) 5 0 (.reg .X0)).isNone
#guard (armLeaArithZext (some .SP) (.reg .X2) 2 0 (.reg .X0)).isNone
#guard (armLeaArithZext none (.reg .X2) 33 0 (.reg .X0)).isNone
#guard (armLeaArithZext none (.reg .X2) 3 0 .SP).isNone
#guard (armLeaArithZext (some (.reg .X1)) .SP 2 0 (.reg .X0)).isNone
#guard (armLeaArithZext (some (.reg .X1)) (.reg .X2) 2 0x123456 (.reg .X0)).isNone

-- Single-instruction UXTW memory operands (`disp = 0`)
#guard match armLoadZextIdx i8 (.reg .X0) (.reg .X1) (.reg .X2) .s1 0 with
  | some ([d], m) => isMemUxtwDir d && m == maskNone
  | _ => false

#guard match armLoadZextIdx i16 (.reg .X0) (.reg .X1) (.reg .X2) .s2 0 with
  | some ([d], m) => isMemUxtwDir d && m == maskNone
  | _ => false

#guard match armLoadZextIdx i32 (.reg .X0) (.reg .X1) (.reg .X2) .s4 0 with
  | some ([d], m) => isMemUxtwDir d && m == maskNone
  | _ => false

#guard match armLoadZextIdx i64 (.reg .X0) (.reg .X1) (.reg .X2) .s8 0 with
  | some ([d], m) => isMemUxtwDir d && m == maskNone
  | _ => false

#guard match armLoadSextZextIdx 8 64 (.reg .X0) (.reg .X1) (.reg .X2) .s1 0 with
  | some ([d], m) => isMemUxtwDir d && m == maskNone
  | _ => false

#guard match armLoadSextZextIdx 16 64 (.reg .X0) (.reg .X1) (.reg .X2) .s2 0 with
  | some ([d], m) => isMemUxtwDir d && m == maskNone
  | _ => false

#guard match armStoreZextIdx i32 (.gpr (.reg .X0)) (.reg .X1) (.reg .X2) .s4 0 with
  | some ([d], m) => isMemUxtwDir d && m == maskNone
  | _ => false

#guard match armStoreZextIdx .bool (.flag .eq) (.reg .X1) (.reg .X2) .s1 0 with
  | some ([_, d2], m) => isMemUxtwDir d2 && m == maskNone
  | _ => false

-- Non-zero disp: `ADD_e x16, rb, w_ri, uxtw #sh` + `[x16, #disp]` or `SUB_e` + `[x16, w_ri, uxtw]`
#guard match armLoadZextIdx i32 (.reg .X0) (.reg .X1) (.reg .X2) .s4 4 with
  | some ([d1, _], m) => isAddUxtwDir d1 && m == maskNone
  | _ => false

#guard match armLoadZextIdx i64 (.reg .X0) (.reg .X1) (.reg .X2) .s8 4104 with
  | some ([d1, _], m) => isAddUxtwDir d1 && m == maskNone
  | _ => false

#guard match armLoadZextIdx i32 (.reg .X0) (.reg .X1) (.reg .X2) .s8 4 with
  | some ([d1, _], m) => isAddUxtwDir d1 && m == maskNone
  | _ => false

#guard match armLoadZextIdx i32 (.reg .X0) (.reg .X1) (.reg .X2) .s4 (-4) with
  | some ([_, d2], m) => isMemUxtwDir d2 && m == maskNone
  | _ => false

#guard match armStoreZextIdx i64 (.imm 0#64) (.reg .X1) (.reg .X2) .s8 8 with
  | some ([d1, _], m) => isAddUxtwDir d1 && m == maskNone
  | _ => false

-- `armLeaArithZext`: base + UXTW `#0..#4`, plus baseless `orr w` / `ubfiz` `#1..#32`
#guard match armLeaArithZext (some (.reg .X1)) (.reg .X2) 0 0 (.reg .X0) with
  | some ([d], m) => isAddUxtwDir d && m == maskNone
  | _ => false

#guard match armLeaArithZext (some (.reg .X1)) (.reg .X2) 4 0 (.reg .X0) with
  | some ([d], m) => isAddUxtwDir d && m == maskNone
  | _ => false

#guard match armLeaArithZext (some (.reg .X1)) (.reg .X2) 2 8 (.reg .X0) with
  | some ([d1, _], m) => isAddUxtwDir d1 && m == maskNone
  | _ => false

#guard match armLeaArithZext (some (.reg .X1)) (.reg .X2) 3 (-16) (.reg .X0) with
  | some ([d1, _], m) => isAddUxtwDir d1 && m == maskNone
  | _ => false

#guard match armLeaArithZext none (.reg .X1) 0 0 (.reg .X0) with
  | some ([.instr { operation := .ORR_s (.low (.reg .X0) .W32) (.low .XZR .W32) _, .. }], m) =>
    m == maskNone
  | _ => false

#guard match armLeaArithZext none (.reg .X1) 3 0 (.reg .X0) with
  | some ([d], m) => isUbfiz32Dir d && m == maskNone
  | _ => false

#guard match armLeaArithZext none (.reg .X1) 32 16 (.reg .X0) with
  | some ([d1, _], m) => isUbfiz32Dir d1 && m == maskNone
  | _ => false

/-! ## 2. Printer sanity checks (`uxtw`) -/

meta def renderDirs : Option (List Directive × FlagMask) → List String
  | some (ds, _) => ds.map Kraken.AArch64.Print.directive
  | none => []

#guard renderDirs (armLoadZextIdx i32 (.reg .X0) (.reg .X1) (.reg .X2) .s4 0) ==
  ["ldr w0, [x1, w2, uxtw #2]"]

#guard renderDirs (armLoadZextIdx i32 (.reg .X0) (.reg .X1) (.reg .X2) .s4 4) ==
  ["add x16, x1, w2, uxtw #2", "ldr w0, [x16, #4]"]

#guard renderDirs (armLoadSextZextIdx 8 64 (.reg .X0) (.reg .X1) (.reg .X2) .s1 0) ==
  ["ldrsb x0, [x1, w2, uxtw #0]"]

#guard renderDirs (armStoreZextIdx i64 (.gpr (.reg .X0)) (.reg .X1) (.reg .X2) .s8 0) ==
  ["str x0, [x1, w2, uxtw #3]"]

#guard renderDirs (armLeaArithZext (some (.reg .X1)) (.reg .X2) 4 0 (.reg .X0)) ==
  ["add x0, x1, w2, uxtw #4"]

/-! ## 3. Verified `FallsTo` & `NoLab` theorems -/

theorem uxtw_load_i32_fallsTo {h : Host} {k : Nat} {c : List Directive} {clob : FlagMask}
    {v : BitVec 32} {vb : BitVec 64} {vi : BitVec 32} {s : MachineData}
    {post : MachineState → Prop}
    (hc : armLoadZextIdx i32 (.reg .X0) (.reg .X1) (.reg .X2) .s4 4 = some (c, clob))
    (hvb : GprHolds (armMach.getGpr s (.reg .X1)) (.bits 64) vb)
    (hvi : GprHolds (armMach.getGpr s (.reg .X2)) (.bits 32) vi)
    (hv : loadVal (armMach.mem s) i32 (vb + (vi.setWidth 64 <<< 2) + (4 : Int64).toBitVec) =
      some v) :
    armMach.FallsTo armCondReads h k c (.reg .X0 :: armScratch) [] clob s
      (fun s' => armMach.getGpr s' (.reg .X0) = v.setWidth 64 ∧ armMach.mem s' = armMach.mem s)
      post :=
  armLoadZextIdx_zero32 hc (by simp [armScratch]) (by simp [armScratch]) (by simp [armScratch])
    hvb hvi hv

theorem uxtw_loadSext_i8_fallsTo {h : Host} {k : Nat} {c : List Directive} {clob : FlagMask}
    {v : BitVec 8} {vb : BitVec 64} {vi : BitVec 32} {s : MachineData}
    {post : MachineState → Prop}
    (hc : armLoadSextZextIdx 8 64 (.reg .X0) (.reg .X1) (.reg .X2) .s1 0 = some (c, clob))
    (hvb : GprHolds (armMach.getGpr s (.reg .X1)) (.bits 64) vb)
    (hvi : GprHolds (armMach.getGpr s (.reg .X2)) (.bits 32) vi)
    (hv : loadVal (armMach.mem s) (.bits 8)
      (vb + (vi.setWidth 64 <<< 0) + (0 : Int64).toBitVec) = some v) :
    armMach.FallsTo armCondReads h k c (.reg .X0 :: armScratch) [] clob s
      (fun s' => armMach.getGpr s' (.reg .X0) = v.signExtend 64 ∧ armMach.mem s' = armMach.mem s)
      post :=
  armLoadSextZextIdx_spec hc (by simp [armScratch]) (by simp [armScratch]) (by simp [armScratch])
    hvb hvi hv

theorem uxtw_store_i32_fallsTo {h : Host} {k : Nat} {c : List Directive} {clob : FlagMask}
    {v : Val i32} {vb : BitVec 64} {vi : BitVec 32} {s : MachineData}
    {post : MachineState → Prop} {disp : Int64} (_hdisp : disp = -4)
    (hc : armStoreZextIdx i32 (.gpr (.reg .X0)) (.reg .X1) (.reg .X2) .s4 disp = some (c, clob))
    (hv : armMach.PArgHolds s i32 (.gpr (.reg .X0)) v)
    (hvb : GprHolds (armMach.getGpr s (.reg .X1)) (.bits 64) vb)
    (hvi : GprHolds (armMach.getGpr s (.reg .X2)) (.bits 32) vi)
    (hok : storeOk (armMach.mem s) i32
      (vb + (vi.setWidth 64 <<< AddrScale.s4.shift) + disp.toBitVec)) :
    armMach.FallsTo armCondReads h k c armScratch [] clob s
      (fun s' => armMach.mem s' =
        storeMem (armMach.mem s) i32
          (vb + (vi.setWidth 64 <<< AddrScale.s4.shift) + disp.toBitVec) v) post := by
  have hspec := armStoreZextIdx_spec (h := h) (k := k) (post := post) hc
    (by simp [PArg.gprs, armScratch]) (by simp [armScratch]) (by simp [armScratch]) hv hvb hvi hok
  exact hspec

theorem uxtw_lea_base_fallsTo {h : Host} {k : Nat} {c : List Directive} {clob : FlagMask}
    {vb : BitVec 64} {vi : BitVec 32} {s : MachineData} {post : MachineState → Prop}
    (hc : armLeaArithZext (some (.reg .X1)) (.reg .X2) 4 8 (.reg .X0) = some (c, clob))
    (hvb : GprHolds (armMach.getGpr s (.reg .X1)) (.bits 64) vb)
    (hvi : GprHolds (armMach.getGpr s (.reg .X2)) (.bits 32) vi) :
    armMach.FallsTo armCondReads h k c (.reg .X0 :: armScratch) [] clob s
      (fun s' => GprHolds (armMach.getGpr s' (.reg .X0)) (.bits 64)
        (vb + (vi.setWidth 64 <<< 4) + (8 : Int64).toBitVec) ∧ armMach.mem s' = armMach.mem s)
      post :=
  armLeaArithZext_spec hc (by rintro r ⟨rfl⟩; simp [armScratch]) (by simp [armScratch])
    (by simp [armScratch]) (by rintro r ⟨rfl⟩; exact hvb) hvi

theorem uxtw_lea_ubfiz_fallsTo {h : Host} {k : Nat} {c : List Directive} {clob : FlagMask}
    {vi : BitVec 32} {s : MachineData} {post : MachineState → Prop}
    (hc : armLeaArithZext none (.reg .X1) 3 0 (.reg .X0) = some (c, clob))
    (hvi : GprHolds (armMach.getGpr s (.reg .X1)) (.bits 32) vi) :
    armMach.FallsTo armCondReads h k c (.reg .X0 :: armScratch) [] clob s
      (fun s' => GprHolds (armMach.getGpr s' (.reg .X0)) (.bits 64)
        (vi.setWidth 64 <<< 3) ∧ armMach.mem s' = armMach.mem s)
      post := by
  have hspec := armLeaArithZext_spec (h := h) (k := k) (post := post) (vb := 0#64) hc
    (by rintro _ ⟨⟩) (by simp [armScratch]) (by simp [armScratch]) (by rintro _ ⟨⟩) hvi
  simpa [Option.isSome, show (0 : Int64).toBitVec = 0#64 by rfl] using hspec

/-! ## 4. Axiom audit (`std3` only) -/

#print axioms LeanQbe.T.Arm64.armAddUxtwDir_wp
#print axioms LeanQbe.T.Arm64.armSetupAddrZext_wp
#print axioms LeanQbe.T.Arm64.armLoadZextIdx_zext
#print axioms LeanQbe.T.Arm64.armLoadZextIdx_spec
#print axioms LeanQbe.T.Arm64.armLoadZextIdx_zero32
#print axioms LeanQbe.T.Arm64.armLoadZextIdx_noLab
#print axioms LeanQbe.T.Arm64.armLoadSextZextIdx_spec
#print axioms LeanQbe.T.Arm64.armLoadSextZextIdx_noLab
#print axioms LeanQbe.T.Arm64.armStoreZextIdx_spec
#print axioms LeanQbe.T.Arm64.armStoreZextIdx_noLab
#print axioms LeanQbe.T.Arm64.armLeaArithZext_wp
#print axioms LeanQbe.T.Arm64.armLeaArithZext_spec
#print axioms LeanQbe.T.Arm64.armLeaArithZext_noLab
#print axioms LeanQbe.T.Arm64.parser_opt_uxtw_rfl
#print axioms LeanQbe.T.Arm64.armGprSpec
#print axioms LeanQbe.T.Arm64.armTarget
#print axioms uxtw_load_i32_fallsTo
#print axioms uxtw_loadSext_i8_fallsTo
#print axioms uxtw_store_i32_fallsTo
#print axioms uxtw_lea_base_fallsTo
#print axioms uxtw_lea_ubfiz_fallsTo

end LeanQbeTest.T.Arm64UxtwTest
