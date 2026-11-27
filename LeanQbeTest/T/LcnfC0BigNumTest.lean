module

public import LeanQbe.T.LeanLCNF.LcnfC0Rt
public import LeanQbe.T.LeanLCNF.LcnfC0BigNum
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumMath
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumSpec
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof
public import LeanQbe.T.InterpKissat
public import LeanQbe.T.PrintCpp
meta import LeanQbe.T.LeanLCNF.LcnfC0Rt
meta import LeanQbe.T.LeanLCNF.LcnfC0BigNum
meta import LeanQbe.T.LeanLCNF.LcnfC0BigNumMath
meta import LeanQbe.T.LeanLCNF.LcnfC0BigNumSpec
meta import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof
meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.PrintCpp

/-!
# Verification, Runtime Non-Vacuity & Axiom Audit Tests for `LcnfC0BigNum` (`Milestone R1`)

* Structural checks on `LcnfC0BaseRt` / `LcnfC0BigNumRt` layout (`33672` / `33688`),
  34-function `rtR1Mod`, and closed 39-function `rtR0R1Mod` (`rtR0_fns ++ rtR1_fns`).
* Acyclicity (`rtR1Mod.checkAcyclic`, `rtR0R1Mod.checkAcyclic`) and `PrintCpp.ppTModule`
  emission checks.
* Executable `interpModule rtR0R1Mod` checks on the concrete `Mem 64` multi-limb bignum heap
  (`nvBnMem`) exercising `lcnf_nat_slow` (add/sub/mul/div/mod/gcd/log2) and `lcnf_int_op`
  (add/mul/ediv/emod/tdiv/tmod/lt).
* Standard axiom audit (`[propext, Classical.choice, Quot.sound]`) across all 34 `Func.wp`
  theorems, `rtR1Mod_moduleOk`, headline soundness theorems, and concrete `Mem 64` NV theorems.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.LcnfC0BigNumTest

open LeanQbe.T
open LeanQbe.T.LeanLCNF

/-- Closed 39-function C0 runtime module combining R0 slab/RC (`rtR0_fns`) and R1 BigNum
(`rtR1_fns`), leaving only the panic exit `lcnf_panic`. -/
def rtR0R1Mod : LeanQbe.T.Module :=
  { fns := rtR0_fns ++ rtR1_fns, externs := [], exits := ["lcnf_panic"] }

#guard rtR1Mod.checkAcyclic
#guard rtR0R1Mod.checkAcyclic
#guard rtR1Mod.fns.length == 34
#guard rtR0R1Mod.fns.length == 39
#guard rtR1Mod.exits == ["lcnf_panic"]
#guard LcnfC0BaseRt.sizeof == 33672
#guard LcnfC0BigNumRt.sizeof == 33688
#guard LcnfC0BaseRt.sizeof + 16 == LcnfC0BigNumRt.sizeof
#guard (PrintCpp.ppTModule rtR1Mod).isOk
#guard (PrintCpp.ppTModule rtR0R1Mod).isOk

/-! ## Executable `interpModule rtR0R1Mod` Multi-Limb BigNum Runtime Checks -/

def mpzHdr (csSz other : Nat) : BitVec 64 :=
  1#64 ||| (BitVec.ofNat 64 csSz <<< 32) ||| (BitVec.ofNat 64 other <<< 48) ||| (250#64 <<< 56)

def mpzMeta (n : Nat) : BitVec 64 :=
  BitVec.ofNat 64 n ||| (BitVec.ofNat 64 n <<< 32)

def checkMpzAt (m : Mem 64) (p : BitVec 64) (other : Nat)
    (limbs : List (BitVec 64)) : Bool :=
  let n := limbs.length
  let cs := 16 + 8 * n
  (p &&& 1#64) == 0#64 &&
  loadVal m i64 p == some (mpzHdr cs other) &&
  loadVal m i64 (p + 8#64) == some (mpzMeta n) &&
  (limbs.zipIdx.all fun (v, i) => loadVal m i64 (p + BitVec.ofNat 64 (16 + 8 * i)) == some v)

/-- Multi-limb `lcnf_nat_slow` runtime checks (`add`, `sub`, `mul`, `div`, `mod`, `gcd`, `log2`)
on `nvBnMem` (`A = 3 * 2^64 - 1`, `B = 2^64 + 5`). -/
def checkNatSlowExec : Bool :=
  let okAdd :=
    match interpModule rtR0R1Mod 50000 "lcnf_nat_slow" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 1#64, nvBnAddrNatA, nvBnAddrNatB, ()) nvBnMem with
    | .ok (res, ()) m1 => checkMpzAt m1 res 0 [4#64, 4#64]
    | _ => false
  let okSub :=
    match interpModule rtR0R1Mod 50000 "lcnf_nat_slow" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 2#64, nvBnAddrNatA, nvBnAddrNatB, ()) nvBnMem with
    | .ok (res, ()) m1 => checkMpzAt m1 res 0 [0xfffffffffffffffa#64, 1#64]
    | _ => false
  let okMul :=
    match interpModule rtR0R1Mod 50000 "lcnf_nat_slow" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 3#64, nvBnAddrNatA, nvBnAddrNatB, ()) nvBnMem with
    | .ok (res, ()) m1 => checkMpzAt m1 res 0 [0xfffffffffffffffb#64, 13#64, 3#64]
    | _ => false
  let okDiv :=
    match interpModule rtR0R1Mod 50000 "lcnf_nat_slow" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 4#64, nvBnAddrNatA, nvBnAddrNatB, ()) nvBnMem with
    | .ok (res, ()) _ => res == 5#64
    | _ => false
  let okMod :=
    match interpModule rtR0R1Mod 50000 "lcnf_nat_slow" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 5#64, nvBnAddrNatA, nvBnAddrNatB, ()) nvBnMem with
    | .ok (res, ()) m1 => checkMpzAt m1 res 0 [0xfffffffffffffff5#64]
    | _ => false
  let okGcd :=
    match interpModule rtR0R1Mod 50000 "lcnf_nat_slow" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 18#64, nvBnAddrNatA, nvBnAddrNatB, ()) nvBnMem with
    | .ok (res, ()) _ => res == 3#64
    | _ => false
  let okLog2 :=
    match interpModule rtR0R1Mod 50000 "lcnf_nat_slow" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 19#64, nvBnAddrNatA, 0#64, ()) nvBnMem with
    | .ok (res, ()) _ => res == 131#64
    | _ => false
  okAdd && okSub && okMul && okDiv && okMod && okGcd && okLog2

/-- Multi-limb `lcnf_int_op` runtime checks (`add`, `mul`, `ediv`, `emod`, `tdiv`, `tmod`, `lt`)
on `nvBnMem` (`-A = -(3 * 2^64 - 1)`, `B = 2^64 + 5`). -/
def checkIntOpExec : Bool :=
  let okAdd :=
    match interpModule rtR0R1Mod 50000 "lcnf_int_op" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 4#64, nvBnAddrIntNegA, nvBnAddrIntPosB, ()) nvBnMem with
    | .ok (res, ()) m1 => checkMpzAt m1 res 1 [0xfffffffffffffffa#64, 1#64]
    | _ => false
  let okMul :=
    match interpModule rtR0R1Mod 50000 "lcnf_int_op" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 6#64, nvBnAddrIntNegA, nvBnAddrIntPosB, ()) nvBnMem with
    | .ok (res, ()) m1 => checkMpzAt m1 res 1 [0xfffffffffffffffb#64, 13#64, 3#64]
    | _ => false
  let okEdiv :=
    match interpModule rtR0R1Mod 50000 "lcnf_int_op" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 7#64, nvBnAddrIntNegA, nvBnAddrIntPosB, ()) nvBnMem with
    | .ok (res, ()) _ => res == BitVec.ofInt 64 (-5)
    | _ => false
  let okEmod :=
    match interpModule rtR0R1Mod 50000 "lcnf_int_op" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 8#64, nvBnAddrIntNegA, nvBnAddrIntPosB, ()) nvBnMem with
    | .ok (res, ()) _ => res == 33#64
    | _ => false
  let okTdiv :=
    match interpModule rtR0R1Mod 50000 "lcnf_int_op" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 14#64, nvBnAddrIntNegA, nvBnAddrIntPosB, ()) nvBnMem with
    | .ok (res, ()) _ => res == BitVec.ofInt 64 (-3)
    | _ => false
  let okTmod :=
    match interpModule rtR0R1Mod 50000 "lcnf_int_op" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 15#64, nvBnAddrIntNegA, nvBnAddrIntPosB, ()) nvBnMem with
    | .ok (res, ()) m1 => checkMpzAt m1 res 1 [0xfffffffffffffff5#64]
    | _ => false
  let okLt :=
    match interpModule rtR0R1Mod 50000 "lcnf_int_op" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 11#64, nvBnAddrIntNegA, nvBnAddrIntPosB, ()) nvBnMem with
    | .ok (res, ()) _ => res == 1#64
    | _ => false
  let okNotLt :=
    match interpModule rtR0R1Mod 50000 "lcnf_int_op" [i64, i64, i64, i64] [i64]
        (nvBnRtBase, 11#64, nvBnAddrIntPosB, nvBnAddrIntNegA, ()) nvBnMem with
    | .ok (res, ()) _ => res == 0#64
    | _ => false
  okAdd && okMul && okEdiv && okEmod && okTdiv && okTmod && okLt && okNotLt

#guard checkNatSlowExec
#guard checkIntOpExec

/-! ## Standard Axiom Audit (`[propext, Classical.choice, Quot.sound]`) -/

#print axioms rtR1_fns_wf
#print axioms rtR1_checkAcyclic
#print axioms rt_scratch_wp
#print axioms rt_scratch_cap_wp
#print axioms lcnf_nat_alloc_wp
#print axioms bn_dec_nat_wp
#print axioms bn_require_scratch_wp
#print axioms bn_trim_wp
#print axioms bn_copy_wp
#print axioms bn_zero_wp
#print axioms bn_nat_from_limbs_wp
#print axioms bn_int_from_limbs_wp
#print axioms bn_nat_len_wp
#print axioms bn_int_len_wp
#print axioms bn_load_nat_wp
#print axioms bn_load_int_wp
#print axioms bn_cmp_fixed_wp
#print axioms bn_cmp_wp
#print axioms bn_add_wp
#print axioms bn_add_one_wp
#print axioms bn_sub_wp
#print axioms bn_sub_one_wp
#print axioms bn_mul_wp
#print axioms bn_bitwise_wp
#print axioms bn_shl_wp
#print axioms bn_shr_wp
#print axioms bn_divmod_wp
#print axioms bn_nat_pow_wp
#print axioms bn_nat_gcd_wp
#print axioms lcnf_nat_arith_wp
#print axioms lcnf_nat_bits_wp
#print axioms lcnf_nat_slow_wp
#print axioms lcnf_int_conv_wp
#print axioms lcnf_int_addsub_cmp_wp
#print axioms lcnf_int_muldiv_wp
#print axioms lcnf_int_op_wp
#print axioms rtR1Mod_tableImpl
#print axioms rtR1Mod_moduleOk
#print axioms lcnf_nat_alloc_sound
#print axioms lcnf_nat_slow_sound
#print axioms lcnf_int_op_sound
#print axioms nvBnMem_ok
#print axioms nv_bn_nat_add_carry
#print axioms nv_bn_nat_mul_2x2
#print axioms nv_bn_int_add_opp_sign
#print axioms nv_bn_int_ediv_neg
#print axioms nv_bn_int_emod_neg

end LeanQbeTest.T.LcnfC0BigNumTest
