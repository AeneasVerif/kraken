module

public import LeanQbe.T.BinaryLayout
public import LeanQbe.T.Arm64.TargLemmas
public import Kraken.AArch64.WP.Host

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

/-- Construct an AArch64 `Layout` from a binary start VMA and size table. -/
@[instance_reducible, expose] def armBinaryLayout (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true) : _root_.Layout :=
  LeanQbe.T.tableLayout _ _ start sizes hpos

/-- Construct a concrete AArch64 `Host` from a verified program and binary size table. -/
@[reducible, expose] def armHostOfBinary (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true)
    (prog : _root_.Program)
    (hsmall : LeanQbe.T.tableProgSmall sizes prog = true) : _root_.Host :=
  _root_.Host.ofLayout prog (armBinaryLayout start sizes hpos)
    (LeanQbe.T.tableLayout_small start sizes hpos prog hsmall)

theorem armHostOfBinary_prog (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true)
    (prog : _root_.Program)
    (hsmall : LeanQbe.T.tableProgSmall sizes prog = true) :
    @_root_.Host.prog (armHostOfBinary start sizes hpos prog hsmall) = prog :=
  rfl

private theorem arm_definedLabels_eq (prog : _root_.Program) :
    _root_.Program.definedLabels prog = prog.filterMap LeanQbe.T.dirLabel? := by
  unfold _root_.Program.definedLabels
  congr 1
  funext d
  cases d <;> rfl

theorem armHostOfBinary_labelsUnique (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true)
    {prog : _root_.Program}
    (hsmall : LeanQbe.T.tableProgSmall sizes prog = true)
    (hnodup : labelsNodupBy LeanQbe.T.dirLabel? prog = true) :
    @_root_.Host.LabelsUnique (armHostOfBinary start sizes hpos prog hsmall) := by
  apply @_root_.Host.labelsUnique_of_nodup (armHostOfBinary start sizes hpos prog hsmall)
  show (_root_.Program.definedLabels prog).Nodup
  rw [arm_definedLabels_eq]
  exact labelsNodupBy_nodup LeanQbe.T.dirLabel? hnodup

/-- Wrap a binary-derived size table as a `TargetLayout armTarget`. -/
@[expose] def armBinaryTargetLayout (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true) : TargetLayout armTarget where
  progSmall := LeanQbe.T.tableProgSmall sizes
  layoutOf := armHostOfBinary start sizes hpos
  prog_layoutOf := armHostOfBinary_prog start sizes hpos
  labelsNodup := labelsNodupBy LeanQbe.T.dirLabel?
  labelsUnique_layoutOf := fun hsmall hnodup =>
    armHostOfBinary_labelsUnique start sizes hpos hsmall hnodup

end LeanQbe.T.Arm64

end
