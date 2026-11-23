/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7PlusInl
public import LeanQbe.T.Examples.Kissat.FullM7FidelityInl
public import LeanQbe.T.MainCertProof

/-!
# Arch-Neutral Batched Slice-Equality Bridge (`FullM7FidelityM7PlusBridge`)

Proves definitional equality of all `38` verbatim-reusable `FullM7PlusInl` slices (`282/413`
functions) against `FullM7FidelityInl` via a single batched `t_kernel_rfl` check plus `38`
O(1) projections (zero expose attributes, `std3` axioms only).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelityM7PlusBridge

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM7PlusInl (m7PlusInlFns)
open LeanQbe.T.Examples.Kissat.FullM7FidelityInl (m7FidInlFns)

private def reuseSlices (fs : List Fn) : List (List Fn) :=
  [ (fs.drop 12).take 12
  , (fs.drop 24).take 12
  , (fs.drop 36).take 11
  , (fs.drop 47).take 12
  , (fs.drop 59).take 12
  , (fs.drop 71).take 12
  , (fs.drop 83).take 1
  , (fs.drop 84).take 1
  , (fs.drop 85).take 1
  , (fs.drop 86).take 9
  , (fs.drop 95).take 7
  , (fs.drop 102).take 1
  , (fs.drop 120).take 1
  , (fs.drop 121).take 9
  , (fs.drop 140).take 10
  , (fs.drop 150).take 10
  , (fs.drop 179).take 8
  , (fs.drop 187).take 10
  , (fs.drop 197).take 12
  , (fs.drop 209).take 12
  , (fs.drop 221).take 9
  , (fs.drop 230).take 9
  , (fs.drop 239).take 10
  , (fs.drop 249).take 9
  , (fs.drop 258).take 1
  , (fs.drop 259).take 2
  , (fs.drop 261).take 1
  , (fs.drop 262).take 11
  , (fs.drop 273).take 12
  , (fs.drop 285).take 1
  , (fs.drop 286).take 1
  , (fs.drop 287).take 11
  , (fs.drop 298).take 10
  , (fs.drop 308).take 8
  , (fs.drop 316).take 9
  , (fs.drop 325).take 7
  , (fs.drop 332).take 1
  , (fs.drop 333).take 7 ]

private theorem eq_all38_batched :
    reuseSlices m7FidInlFns = reuseSlices m7PlusInlFns := by
  t_kernel_rfl

theorem reuse_m7p_eq_2 :
    (m7FidInlFns.drop 12).take 12 = (m7PlusInlFns.drop 12).take 12 :=
  Option.some.inj (congrArg (·[0]?) eq_all38_batched)

theorem reuse_m7p_eq_3 :
    (m7FidInlFns.drop 24).take 12 = (m7PlusInlFns.drop 24).take 12 :=
  Option.some.inj (congrArg (·[1]?) eq_all38_batched)

theorem reuse_m7p_eq_4 :
    (m7FidInlFns.drop 36).take 11 = (m7PlusInlFns.drop 36).take 11 :=
  Option.some.inj (congrArg (·[2]?) eq_all38_batched)

theorem reuse_m7p_eq_5 :
    (m7FidInlFns.drop 47).take 12 = (m7PlusInlFns.drop 47).take 12 :=
  Option.some.inj (congrArg (·[3]?) eq_all38_batched)

theorem reuse_m7p_eq_6 :
    (m7FidInlFns.drop 59).take 12 = (m7PlusInlFns.drop 59).take 12 :=
  Option.some.inj (congrArg (·[4]?) eq_all38_batched)

theorem reuse_m7p_eq_7 :
    (m7FidInlFns.drop 71).take 12 = (m7PlusInlFns.drop 71).take 12 :=
  Option.some.inj (congrArg (·[5]?) eq_all38_batched)

theorem reuse_m7p_eq_8 :
    (m7FidInlFns.drop 83).take 1 = (m7PlusInlFns.drop 83).take 1 :=
  Option.some.inj (congrArg (·[6]?) eq_all38_batched)

theorem reuse_m7p_eq_9 :
    (m7FidInlFns.drop 84).take 1 = (m7PlusInlFns.drop 84).take 1 :=
  Option.some.inj (congrArg (·[7]?) eq_all38_batched)

theorem reuse_m7p_eq_10 :
    (m7FidInlFns.drop 85).take 1 = (m7PlusInlFns.drop 85).take 1 :=
  Option.some.inj (congrArg (·[8]?) eq_all38_batched)

theorem reuse_m7p_eq_11 :
    (m7FidInlFns.drop 86).take 9 = (m7PlusInlFns.drop 86).take 9 :=
  Option.some.inj (congrArg (·[9]?) eq_all38_batched)

theorem reuse_m7p_eq_12 :
    (m7FidInlFns.drop 95).take 7 = (m7PlusInlFns.drop 95).take 7 :=
  Option.some.inj (congrArg (·[10]?) eq_all38_batched)

theorem reuse_m7p_eq_13 :
    (m7FidInlFns.drop 102).take 1 = (m7PlusInlFns.drop 102).take 1 :=
  Option.some.inj (congrArg (·[11]?) eq_all38_batched)

theorem reuse_m7p_eq_16 :
    (m7FidInlFns.drop 120).take 1 = (m7PlusInlFns.drop 120).take 1 :=
  Option.some.inj (congrArg (·[12]?) eq_all38_batched)

theorem reuse_m7p_eq_17 :
    (m7FidInlFns.drop 121).take 9 = (m7PlusInlFns.drop 121).take 9 :=
  Option.some.inj (congrArg (·[13]?) eq_all38_batched)

theorem reuse_m7p_eq_19 :
    (m7FidInlFns.drop 140).take 10 = (m7PlusInlFns.drop 140).take 10 :=
  Option.some.inj (congrArg (·[14]?) eq_all38_batched)

theorem reuse_m7p_eq_20 :
    (m7FidInlFns.drop 150).take 10 = (m7PlusInlFns.drop 150).take 10 :=
  Option.some.inj (congrArg (·[15]?) eq_all38_batched)

theorem reuse_m7p_eq_23 :
    (m7FidInlFns.drop 179).take 8 = (m7PlusInlFns.drop 179).take 8 :=
  Option.some.inj (congrArg (·[16]?) eq_all38_batched)

theorem reuse_m7p_eq_24 :
    (m7FidInlFns.drop 187).take 10 = (m7PlusInlFns.drop 187).take 10 :=
  Option.some.inj (congrArg (·[17]?) eq_all38_batched)

theorem reuse_m7p_eq_25 :
    (m7FidInlFns.drop 197).take 12 = (m7PlusInlFns.drop 197).take 12 :=
  Option.some.inj (congrArg (·[18]?) eq_all38_batched)

theorem reuse_m7p_eq_26 :
    (m7FidInlFns.drop 209).take 12 = (m7PlusInlFns.drop 209).take 12 :=
  Option.some.inj (congrArg (·[19]?) eq_all38_batched)

theorem reuse_m7p_eq_27 :
    (m7FidInlFns.drop 221).take 9 = (m7PlusInlFns.drop 221).take 9 :=
  Option.some.inj (congrArg (·[20]?) eq_all38_batched)

theorem reuse_m7p_eq_28 :
    (m7FidInlFns.drop 230).take 9 = (m7PlusInlFns.drop 230).take 9 :=
  Option.some.inj (congrArg (·[21]?) eq_all38_batched)

theorem reuse_m7p_eq_29 :
    (m7FidInlFns.drop 239).take 10 = (m7PlusInlFns.drop 239).take 10 :=
  Option.some.inj (congrArg (·[22]?) eq_all38_batched)

theorem reuse_m7p_eq_30 :
    (m7FidInlFns.drop 249).take 9 = (m7PlusInlFns.drop 249).take 9 :=
  Option.some.inj (congrArg (·[23]?) eq_all38_batched)

theorem reuse_m7p_eq_31 :
    (m7FidInlFns.drop 258).take 1 = (m7PlusInlFns.drop 258).take 1 :=
  Option.some.inj (congrArg (·[24]?) eq_all38_batched)

theorem reuse_m7p_eq_32 :
    (m7FidInlFns.drop 259).take 2 = (m7PlusInlFns.drop 259).take 2 :=
  Option.some.inj (congrArg (·[25]?) eq_all38_batched)

theorem reuse_m7p_eq_33 :
    (m7FidInlFns.drop 261).take 1 = (m7PlusInlFns.drop 261).take 1 :=
  Option.some.inj (congrArg (·[26]?) eq_all38_batched)

theorem reuse_m7p_eq_34 :
    (m7FidInlFns.drop 262).take 11 = (m7PlusInlFns.drop 262).take 11 :=
  Option.some.inj (congrArg (·[27]?) eq_all38_batched)

theorem reuse_m7p_eq_35 :
    (m7FidInlFns.drop 273).take 12 = (m7PlusInlFns.drop 273).take 12 :=
  Option.some.inj (congrArg (·[28]?) eq_all38_batched)

theorem reuse_m7p_eq_36 :
    (m7FidInlFns.drop 285).take 1 = (m7PlusInlFns.drop 285).take 1 :=
  Option.some.inj (congrArg (·[29]?) eq_all38_batched)

theorem reuse_m7p_eq_37 :
    (m7FidInlFns.drop 286).take 1 = (m7PlusInlFns.drop 286).take 1 :=
  Option.some.inj (congrArg (·[30]?) eq_all38_batched)

theorem reuse_m7p_eq_38 :
    (m7FidInlFns.drop 287).take 11 = (m7PlusInlFns.drop 287).take 11 :=
  Option.some.inj (congrArg (·[31]?) eq_all38_batched)

theorem reuse_m7p_eq_39 :
    (m7FidInlFns.drop 298).take 10 = (m7PlusInlFns.drop 298).take 10 :=
  Option.some.inj (congrArg (·[32]?) eq_all38_batched)

theorem reuse_m7p_eq_40 :
    (m7FidInlFns.drop 308).take 8 = (m7PlusInlFns.drop 308).take 8 :=
  Option.some.inj (congrArg (·[33]?) eq_all38_batched)

theorem reuse_m7p_eq_41 :
    (m7FidInlFns.drop 316).take 9 = (m7PlusInlFns.drop 316).take 9 :=
  Option.some.inj (congrArg (·[34]?) eq_all38_batched)

theorem reuse_m7p_eq_42 :
    (m7FidInlFns.drop 325).take 7 = (m7PlusInlFns.drop 325).take 7 :=
  Option.some.inj (congrArg (·[35]?) eq_all38_batched)

theorem reuse_m7p_eq_43 :
    (m7FidInlFns.drop 332).take 1 = (m7PlusInlFns.drop 332).take 1 :=
  Option.some.inj (congrArg (·[36]?) eq_all38_batched)

theorem reuse_m7p_eq_44 :
    (m7FidInlFns.drop 333).take 7 = (m7PlusInlFns.drop 333).take 7 :=
  Option.some.inj (congrArg (·[37]?) eq_all38_batched)

end LeanQbe.T.Examples.Kissat.FullM7FidelityM7PlusBridge
