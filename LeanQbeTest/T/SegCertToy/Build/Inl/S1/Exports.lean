module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertToy.Build.Inl.S1.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn :=
  {
    name := "toy_inc",
    as := [i64],
    rs := [i64],
    body := TFlat.let_ (ts := [i64])
        (⟨.add i64, ((.var 0), ((.imm (BitVec.ofNat 64 1)), ()))⟩)
        (TFlat.ret ((.var 0), ()))
    }

@[expose] def fns : List Fn :=
[flat0.toFn]

end LeanQbeTest.T.SegCertToy.Build.Inl.S1.Exports
