module
import Kraken.AArch64.Parser

set_option pp.explicit true

/-!

In AArch64, arithmetic instructions have two forms:
 - Extended form (i.e. `ADD_e`)
 - Shifted register form (i.e. `ADD_s`)
-/


/--
info: Operation.ADD_e {w : RegWidth} (dst src1 : RegOrSp w) (src2 : ExtOrImmReg) : Operation w
-/
#guard_msgs in #check Operation.ADD_e
/--
info: Operation.ADD_s {w : RegWidth} (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
-/
#guard_msgs in #check Operation.ADD_s

/-!
These forms all are represented by the same `add` mnemonic, and
they are diambiguated by the shape of the final operand.

-/



/--
info: @Kraken.Directive.instr Instr ConstExpr
  { operation_size := RegWidth.W64,
    operation :=
      @Operation.ADD_s RegWidth.W64 (↑↑XReg.X12 RegWidth.W64) (↑↑XReg.X1 RegWidth.W64)
        (@ShiftRegExpr.mk RegWidth.W64 (↑↑XReg.X1 RegWidth.W64)
          (@OfNat.ofNat Int64 (nat_lit 0) (@Int64.instOfNat (nat_lit 0)))
          ShiftType.LSL) } : Kraken.Directive Instr ConstExpr
-/
#guard_msgs in #check ⸨dir| add x12, x1, x1⸩
/--
info: @Kraken.Directive.instr Instr ConstExpr
  { operation_size := RegWidth.W64,
    operation :=
      @Operation.ADD_e RegWidth.W64 (↑↑XReg.X12 RegWidth.W64) (↑↑XReg.X1 RegWidth.W64)
        ↑{ imm := ↑"hello", shift := ImmShift.S0 } } : Kraken.Directive Instr ConstExpr
-/
#guard_msgs in #check ⸨dir| add x12, x1, hello⸩

/-!

This is not the only way in which Aarch64 uses operand shape to disambiguate the underlying
form. For instance, logical operations.

-/


/--
info: @Kraken.Directive.instr Instr ConstExpr
  { operation_size := RegWidth.W64,
    operation :=
      @Operation.AND_s RegWidth.W64 (↑↑XReg.X1 RegWidth.W64) (↑↑XReg.X1 RegWidth.W64)
        (@ShiftRegExpr.mk RegWidth.W64 ?m.1 (@OfNat.ofNat Int64 (nat_lit 0) (@Int64.instOfNat (nat_lit 0)))
          ShiftType.LSL) } : Kraken.Directive Instr ConstExpr
-/
#guard_msgs in #check ⸨dir| and x1, x1, ❰(_ : RegOrZr .W64)❱⸩

/--
info: @Kraken.Directive.instr Instr ConstExpr
  { operation_size := RegWidth.W64,
    operation :=
      @Operation.AND_i RegWidth.W64 (↑↑XReg.X1 RegWidth.W64) (↑↑XReg.X1 RegWidth.W64)
        ?m.1 } : Kraken.Directive Instr ConstExpr
-/
#guard_msgs in #check ⸨dir| and x1, x1, ❰(_ : ConstExpr)❱⸩
