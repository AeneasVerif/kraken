module

public import LeanQbe.T.BinaryLayout
public import LeanQbe.T.Amd64.TargLemmas
public import Kraken.X64.WP.Host

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

/-- Construct an x86-64 `Layout` from a binary start VMA and size table. -/
@[instance_reducible, expose] def x64BinaryLayout (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true) : _root_.Layout :=
  LeanQbe.T.tableLayout _ _ start sizes hpos

/-- Construct a concrete x86-64 `Host` from a verified program and binary size table. -/
@[reducible, expose] def x64HostOfBinary (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true)
    (prog : _root_.Program)
    (hsmall : LeanQbe.T.tableProgSmall sizes prog = true) : _root_.Host :=
  _root_.Host.ofLayout prog (x64BinaryLayout start sizes hpos)
    (LeanQbe.T.tableLayout_small start sizes hpos prog hsmall)

theorem x64HostOfBinary_prog (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true)
    (prog : _root_.Program)
    (hsmall : LeanQbe.T.tableProgSmall sizes prog = true) :
    @_root_.Host.prog (x64HostOfBinary start sizes hpos prog hsmall) = prog :=
  rfl

private theorem x64_definedLabels_eq (prog : _root_.Program) :
    _root_.Program.definedLabels prog = prog.filterMap LeanQbe.T.dirLabel? := by
  unfold _root_.Program.definedLabels
  congr 1
  funext d
  cases d <;> rfl

theorem x64HostOfBinary_labelsUnique (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true)
    {prog : _root_.Program}
    (hsmall : LeanQbe.T.tableProgSmall sizes prog = true)
    (hnodup : labelsNodupBy LeanQbe.T.dirLabel? prog = true) :
    @_root_.Host.LabelsUnique (x64HostOfBinary start sizes hpos prog hsmall) := by
  apply @_root_.Host.labelsUnique_of_nodup (x64HostOfBinary start sizes hpos prog hsmall)
  show (_root_.Program.definedLabels prog).Nodup
  rw [x64_definedLabels_eq]
  exact labelsNodupBy_nodup LeanQbe.T.dirLabel? hnodup

/-- Wrap a binary-derived size table as a `TargetLayout x64Target`. -/
@[expose] def x64BinaryTargetLayout (start : Int64) (sizes : Array Nat)
    (hpos : sizes.all (· > 0) = true) : TargetLayout x64Target where
  progSmall := LeanQbe.T.tableProgSmall sizes
  layoutOf := x64HostOfBinary start sizes hpos
  prog_layoutOf := x64HostOfBinary_prog start sizes hpos
  labelsNodup := labelsNodupBy LeanQbe.T.dirLabel?
  labelsUnique_layoutOf := fun hsmall hnodup =>
    x64HostOfBinary_labelsUnique start sizes hpos hsmall hnodup

end LeanQbe.T.Amd64

end
