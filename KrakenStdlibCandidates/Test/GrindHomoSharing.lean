import KrakenStdlibCandidates
import Init.Grind
open Lean.Grind in #remove_toint_instances

example (x0 : UInt8) :
    let x := x0.toUInt16
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    x.toNat = x0.toNat*2^8 :=
    by grind

example (x0 : UInt16) :
    let x := x0.toUInt32
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    x.toNat = x0.toNat*2^8 :=
    by grind

example (x0 : UInt32) :
    let x := x0.toUInt64
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    x.toNat = x0.toNat*2^8 :=
    by grind

example (x0 : UInt16) :
    let x := x0.toUSize
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    x.toNat = x0.toNat*2^8 := by
  grind

-- 16 doublings times out
