module

public import LeanQbe.T.MainFlat
public import LeanQbe.T.MainCertInline
meta import Lean
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.MainCertInline
meta import LeanQbe.T.OptFlatCfg
meta import LeanQbe.T.OptFlatMem
meta import LeanQbe.T.OptFlatValue
meta import LeanQbe.T.OptFlatAddrRange
meta import LeanQbe.T.OptFlatPathCond
meta import LeanQbe.T.CondThreadOpt
meta import LeanQbe.T.Licm
meta import LeanQbe.T.LoopRotate
meta import LeanQbe.T.TailDup
meta import LeanQbe.T.ZeroPeel
meta import LeanQbe.T.Peel
meta import LeanQbe.T.SimplifyGroupPlan
meta import LeanQbe.T.AddrRangeOpt
meta import LeanQbe.T.Legal
meta import LeanQbe.T.LegalBase
meta import LeanQbe.T.Flat
meta import LeanQbe.T.FlatDirect

/-!
# Shared Compiler Coverage Fixture (`CompilerCoverageFixture`)

Compact collection of `Fn`s materialized via `inline_mod! ... (compile := false)` and partitioned
into `covOptMod` (syntax constructors + every `true` optimization gate in `MainFlat.lean`) and
`covX64OpsMod` / `covArm64OpsMod` (shared scalar/cmp/bool/select ops + ISA-specific bit/SIMD ops).
Explicit `#guard` assertions verify inlining, `TFlat.supportsSource` on `f32`/`f64`/`fcvt`/
`bitcast`, and every `MainFlat.lean` optimization gate at its exact `earlyOptFlat`/`midStageFlat`
pipeline stage.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.CompilerCoverage

open LeanQbe.T

/-! ## 1. Computable `TFlat` Structural Equality & Pipeline Stage Helpers -/

def argTagEq {t : Ty} : Arg K t → Arg K t → Bool
  | .var x, .var y => x == y
  | .imm x, .imm y => decide (x = y)
  | _, _ => false

def tupTagEq : {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts → Bool
  | [], (), () => true
  | _ :: _, (a, as), (b, bs) => argTagEq a b && tupTagEq as bs

def opEq {ts : List Ty} (o1 o2 : Op K ts) : Bool :=
  match o1, o2 with
  | { sig := s1, code := c1, args := a1 }, { sig := s2, code := c2, args := a2 } =>
    if h1 : s1 = s2 then
      match h1 with
      | rfl =>
        let inst : DecidableEq (OpCode s1 ts) := inferInstance
        @decide (c1 = c2) (inst c1 c2) && tupTagEq a1 a2
    else false

mutual
def tflatEq : {rs : List Ty} → TFlat rs → TFlat rs → Bool
  | _, .let_ (ts := ts1) o1 k1, .let_ (ts := ts2) o2 k2 =>
    if h : ts1 = ts2 then
      match h with
      | rfl => opEq o1 o2 && tflatEq k1 k2
    else false
  | _, .load t1 a1 k1, .load t2 a2 k2 =>
    if h : t1 = t2 then
      match h with
      | rfl => argTagEq a1 a2 && tflatEq k1 k2
    else false
  | _, .store (t := t1) v1 a1 k1, .store (t := t2) v2 a2 k2 =>
    if h : t1 = t2 then
      match h with
      | rfl => argTagEq v1 v2 && argTagEq a1 a2 && tflatEq k1 k2
    else false
  | _, .call f1 (as := as1) s1 a1 k1, .call f2 (as := as2) s2 a2 k2 =>
    if h1 : as1 = as2 then
      if h2 : s1 = s2 then
        match h1, h2 with
        | rfl, rfl => f1 == f2 && tupTagEq a1 a2 && tflatEq k1 k2
      else false
    else false
  | _, .jnz c1 t1 e1, .jnz c2 t2 e2 =>
    argTagEq c1 c2 && tflatEq t1 t2 && tflatEq e1 e2
  | _, .group (sig := s1) bs1 k1, .group (sig := s2) bs2 k2 =>
    if h : s1 = s2 then
      match h with
      | rfl => tblocksEq bs1 bs2 && tflatEq k1 k2
    else false
  | _, .jump (ts := ts1) j1 a1, .jump (ts := ts2) j2 a2 =>
    if h : ts1 = ts2 then
      match h with
      | rfl => j1 == j2 && tupTagEq a1 a2
    else false
  | _, .ret a1, .ret a2 => tupTagEq a1 a2
  | _, .exit e1 _, .exit e2 _ => e1 == e2
  | _, .hlt, .hlt => true
  | _, _, _ => false

def tblocksEq {rs : List Ty} : {ss : List (List Ty)} → TBlocks rs ss → TBlocks rs ss → Bool
  | [], .nil, .nil => true
  | _ :: _, .cons b1 bs1, .cons b2 bs2 => tflatEq b1 b2 && tblocksEq bs1 bs2
end

mutual
def hasCallNamed (target : Sym) : {rs : List Ty} → TFlat rs → Bool
  | _, .let_ _ k | _, .load _ _ k | _, .store _ _ k => hasCallNamed target k
  | _, .call f _ _ k => f == target || hasCallNamed target k
  | _, .jnz _ t e => hasCallNamed target t || hasCallNamed target e
  | _, .group bs k => hasCallBlocksNamed target bs || hasCallNamed target k
  | _, .jump _ _ | _, .ret _ | _, .exit _ _ | _, .hlt => false

def hasCallBlocksNamed (target : Sym) {rs : List Ty} :
    {ss : List (List Ty)} → TBlocks rs ss → Bool
  | [], .nil => false
  | _ :: _, .cons b bs => hasCallNamed target b || hasCallBlocksNamed target bs
end

def hasCallInFn (target : Sym) (f : Fn) : Bool :=
  hasCallNamed target (reifyFunc f.body)

def toTf (fn : Fn) : TFlatFn := ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩

def earlyPreIfF (as : List Ty) {rs : List Ty} (tf : TFlat rs) : TFlat rs :=
  OptFlatValue.foldFlat as
    (OptFlatValue.copyFlat as
      (OptFlatValue.gvnFlat as
        (OptFlatValue.copyFlat as
          (OptFlatValue.canonFlat as (OptFlatValue.foldFlat as tf)))))

structure MidTrace (rs : List Ty) where
  tf0c : TFlat rs
  tfDiv : TFlat rs
  tfPreMem : TFlat rs
  tfMem : TFlat rs
  tfGvn : TFlat rs
  tfAssB : TFlat rs
  tfPreIfT : TFlat rs
  tfIfT : TFlat rs
  tfMidSimp : TFlat rs
  tfDle : TFlat rs
  tfPreAr : TFlat rs
  tfAr : TFlat rs
  tfPreLicm : TFlat rs
  tfLicm : TFlat rs
  tfPreRot : TFlat rs
  tfRot : TFlat rs
  tfPrePc : TFlat rs
  tfPathC : TFlat rs
  tfCt : TFlat rs
  tfPreTd : TFlat rs
  tfTd : TFlat rs
  tfMr : TFlat rs

def midAt (lt : LegalTarget) (as : List Ty) {rs : List Ty} (tf : TFlat rs) :
    MidTrace (lt.legalSig rs) :=
  let tfPreIfF := earlyPreIfF as tf
  let tfIfF := OptFlatCfg.ifOptFlat false as tfPreIfF
  let tfSimpE := simplifyGroupFastFlat as tfIfF
  let tfPeel := peelFastFlat as tfSimpE
  let tfZp := TFlat.zeroPeelWith { peelBudget := 24 } tfPeel
  let tfEf := OptFlatCfg.dcePFlat as (OptFlatValue.foldFlat as (OptFlatValue.copyFlat as tfZp))
  let as' : List Ty := lt.legalSig as
  let tf0 : TFlat (lt.legalSig rs) := legalFlat lt (as := as) tfEf
  let tf0c : TFlat (lt.legalSig rs) := OptFlatValue.canonFlat as' (OptFlatValue.foldFlat as' tf0)
  let tfDiv : TFlat (lt.legalSig rs) := OptFlatMem.divConstFlat as' tf0c
  let tfPreMem : TFlat (lt.legalSig rs) := OptFlatValue.copyFlat as' tfDiv
  let tfMem : TFlat (lt.legalSig rs) := OptFlatMem.memLoadFlat as' tfPreMem
  let tfGvn : TFlat (lt.legalSig rs) := OptFlatValue.gvnFlat as' tfMem
  let tfAssB : TFlat (lt.legalSig rs) := OptFlatMem.assumeBitsFlat as' tfGvn
  let tfPreIfT : TFlat (lt.legalSig rs) := OptFlatValue.foldFlat as' tfAssB
  let tfIfT : TFlat (lt.legalSig rs) := OptFlatCfg.ifOptFlat true as' tfPreIfT
  let tfMidSimp : TFlat (lt.legalSig rs) := simplifyGroupFastFlat as' tfIfT
  let tfDle : TFlat (lt.legalSig rs) := OptFlatCfg.deadLoadElimFlat as' tfMidSimp
  let tfPreAr : TFlat (lt.legalSig rs) := OptFlatValue.foldFlat as' (assumeElimFlat tfDle)
  let tfAr : TFlat (lt.legalSig rs) := addrRangeOptFlat as' tfPreAr
  let tfPreLicm : TFlat (lt.legalSig rs) := OptFlatValue.gvnFlat as' tfAr
  let tfLicm : TFlat (lt.legalSig rs) := licmFlat as' tfPreLicm
  let tfPreRot : TFlat (lt.legalSig rs) := OptFlatCfg.dcePFlat as' tfLicm
  let tfRot : TFlat (lt.legalSig rs) := loopRotateFlat as' tfPreRot
  let tfPrePc : TFlat (lt.legalSig rs) := OptFlatValue.foldFlat as' tfRot
  let tfPathC : TFlat (lt.legalSig rs) := pathCondOptFlat as' tfPrePc
  let tfCt : TFlat (lt.legalSig rs) := condThreadPassFlat as' tfPathC
  let tfPreTd : TFlat (lt.legalSig rs) :=
    OptFlatCfg.dcePFlat as' (OptFlatValue.foldFlat as' tfCt)
  let tfTd : TFlat (lt.legalSig rs) := tailDupFlat as' tfPreTd
  let tfMr : TFlat (lt.legalSig rs) := mergeRetsFlat tfTd
  { tf0c, tfDiv, tfPreMem, tfMem, tfGvn, tfAssB, tfPreIfT, tfIfT, tfMidSimp, tfDle
  , tfPreAr, tfAr, tfPreLicm, tfLicm, tfPreRot, tfRot, tfPrePc, tfPathC, tfCt
  , tfPreTd, tfTd, tfMr }

/-! ## 2. Control/Syntax & `MainFlat.lean` Optimization Gate Fixtures (`covOptMod`) -/

def fnInlHelper : Fn :=
  ⟨"cov_inl_helper", [i64], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.add i64) (.var x) (.imm 13#64)) fun (y, ()) =>
    .ret (.var y, ())⟩

def fnPairCallee : Fn :=
  ⟨"cov_pair_callee", [i64], [i64, i32], fun _ _ (x, ()) =>
    .let_ (op2 (.add i64) (.var x) (.imm 7#64)) fun (a, ()) =>
    .let_ (op1 (.trunc 64 32) (.var a)) fun (b, ()) =>
    .ret (.var a, .var b, ())⟩

def fnCalls : Fn :=
  ⟨"cov_calls", [.bool, .bool, i64], [i64, i32], fun _ _ (c1, c2, p, ()) =>
    .jnz (.var c1)
      (.exit "cov_ext_exit" (as := [i64]) (.var p, ()))
      (.jnz (.var c2) .hlt
        (.call "cov_inl_helper" (as := [i64]) (bs := [i64]) (.var p, ()) fun (h0, ()) =>
         .call "cov_ext" (as := [i64]) (bs := [i64]) (.var h0, ()) fun (e0, ()) =>
         .call "cov_pair_callee" (as := [i64]) (bs := [i64, i32]) (.var e0, ()) fun (r0, r1, ()) =>
         .ret (.var r0, .var r1, ())))⟩

def fnMemWidths : Fn :=
  ⟨"cov_mem_widths", [i64, i64], [i32], fun _ _ (p0, p1, ()) =>
    .load i8 (.var p0) fun l8 =>
    .store (.var l8) (.var p1) <|
    .load i16 (.var p0) fun l16 =>
    .store (.var l16) (.var p1) <|
    .load i32 (.var p0) fun l32 =>
    .store (.var l32) (.var p1) <|
    .ret (.var l32, ())⟩

def fnNestedCfg : Fn :=
  ⟨"cov_nested_cfg", [.bool, i64, i64, i32], [i64], fun _ _ (c, x, y, z, ()) =>
    .group (sig := [[i64, i64, i32], [i64]])
      (fun (_, jJoin, ()) =>
        .cons (fun (a, b, w, ()) =>
          .group (sig := [[i64]])
            (fun (_, ()) => .cons (fun (v, ()) => .jump jJoin (.var v, ())) .nil)
            (fun (jIn, ()) =>
              .let_ (op1 (.zext 32 64) (.var w)) fun (zw, ()) =>
              .jnz (.var c)
                (.let_ (op2 (.add i64) (.var a) (.var zw)) fun (s1, ()) => .jump jIn (.var s1, ()))
                (.jump jIn (.var b, ()))))
        (.cons (fun (res, ()) => .ret (.var res, ())) .nil))
      (fun (jPhi, _, ()) =>
        .jnz (.var c)
          (.jump jPhi (.var x, .var y, .var z, ()))
          (.jump jPhi (.var y, .var x, .imm 1#32, ())))⟩

def fnOptIfFPathMerge : Fn :=
  ⟨"cov_opt_iff_pc_mr", [.bool, i64, i64], [i64], fun _ _ (c, a, b, ()) =>
    .group (sig := [[i64]])
      (fun (_, ()) => .cons (fun (x, ()) =>
        .let_ (op2 (.cmp .eq i64 .bool rfl) (.var x) (.imm 7#64)) fun (c0, ()) =>
        .jnz (.var c0)
          (.call "cov_ext" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r, ()) =>
           .let_ (op2 (.cmp .eq i64 .bool rfl) (.var x) (.imm 7#64)) fun (c1, ()) =>
           .jnz (.var c1)
             (.ret (.var r, ()))
             (.ret (.imm 99#64, ())))
          (.ret (.imm 0#64, ()))) .nil)
      (fun (j, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.add i64) (.var a) (.imm 2#64)) fun (x1, ()) => .jump j (.var x1, ()))
          (.let_ (op2 (.add i64) (.var b) (.imm 3#64)) fun (x2, ()) => .jump j (.var x2, ())))⟩

def fnOptPeelRot : Fn :=
  ⟨"cov_opt_peel_rot", [i64], [i64], fun _ _ (n0, ()) =>
    .group (sig := [[i64, i64]])
      (fun (j, ()) => .cons (fun (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64 .bool rfl) (.var i) (.imm 8#64)) fun (c, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.add i64) (.var i) (.imm 1#64)) fun (i1, ()) =>
           .let_ (op2 (.add i64) (.var acc) (.var i1)) fun (a1, ()) =>
           .jump j (.var i1, .var a1, ()))
          (.ret (.var acc, ()))) .nil)
      (fun (j, ()) => .jump j (.imm 0#64, .var n0, ()))⟩

def fnOptZeroPeel : Fn :=
  ⟨"cov_opt_zpeel", [i64, i64], [i64], fun _ _ (n0, n1, ()) =>
    .group (sig := [[i64]])
      (fun (jDone, ()) => .cons (fun (v, ()) =>
        .let_ (op2 (.cmp .ult i64 .bool rfl) (.var v) (.var n1)) fun (c, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.add i64) (.var v) (.imm 1#64)) fun (v1, ()) =>
           .jump jDone (.var v1, ()))
          (.ret (.var v, ()))) .nil)
      (fun (jDone, ()) =>
        .group (sig := [[i64, i64]])
          (fun (jFill, ()) => .cons (fun (i, s, ()) =>
            .let_ (op2 (.cmp .ult i64 .bool rfl) (.var i) (.imm 4#64)) fun (fc, ()) =>
            .jnz (.var fc)
              (.let_ (op2 (.add i64) (.var i) (.imm 1#64)) fun (i1, ()) =>
               .jump jFill (.var i1, .var s, ()))
              (.jump jDone (.var s, ()))) .nil)
          (fun (jFill, ()) => .jump jFill (.imm 0#64, .var n0, ())))⟩

def fnOptStraight : Fn :=
  ⟨"cov_opt_straight", [i64, i64, i64, i8, i32], [i64, i64],
    fun _ _ (p0, v, p1, b8, y32, ()) =>
    .store (.var v) (.var p0) <|
    .load i64 (.var p0) fun lv0 =>
    .load i64 (.var p1) fun _ =>
    .let_ (op1 (.zext 8 64) (.var b8)) fun (zb, ()) =>
    .let_ (op2 (.and i64) (.var zb) (.imm 0xff00#64)) fun (msk, ()) =>
    .let_ (op2 (.udiv 64) (.var lv0) (.imm 3#64)) fun (q1, ()) =>
    .let_ (op2 (.sdiv 32) (.var y32) (.imm 5#32)) fun (q2, ()) =>
    .let_ (op1 (.sext 32 64) (.var q2)) fun (s2, ()) =>
    .let_ (op2 (.add i64) (.var q1) (.var s2)) fun (sum0, ()) =>
    .ret (.var sum0, .var msk, ())⟩

def fnOptMidSimpIfT : Fn :=
  ⟨"cov_opt_midsimp_ift", [.bool, i64, i64, i64], [i64], fun _ _ (c, p, v, alt, ()) =>
    .store (.var v) (.var p) <|
    .group (sig := [[i64]])
      (fun (_, ()) => .cons (fun (x, ()) =>
        .call "cov_ext" (as := [i64]) (bs := [i64]) (.var x, ()) fun (y, ()) =>
        .ret (.var y, ())) .nil)
      (fun (j, ()) =>
        .jnz (.var c)
          (.load i64 (.var p) fun lv => .jump j (.var lv, ()))
          (.jump j (.var alt, ())))⟩

def fnOptLicmAddrRange : Fn :=
  ⟨"cov_opt_licm_ar", [.bool, i64, i64, i64, i64], [i64],
    fun _ _ (flag, p, k0, i0, acc0, ()) =>
    .group (sig := [[i64, i64]])
      (fun (j, ()) => .cons (fun (i, a, ()) =>
        .load i64 (.var p) fun ro =>
        .let_ (op2 (.add i64) (.var k0) (.imm 9#64)) fun (inv, ()) =>
        .let_ (op2 (.add i64) (.var ro) (.var inv)) fun (baseInv, ()) =>
        .let_ (op2 (.cmp .ult i64 .bool rfl) (.var i) (.imm 10#64)) fun (c, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.add i64) (.var i) (.imm 1#64)) fun (i1, ()) =>
           .let_ (op2 (.add i64) (.var i) (.var k0)) fun (idx, ()) =>
           .let_ (op2 (.add i64) (.var p) (.var idx)) fun (adr, ()) =>
           .load i64 (.var adr) fun lv =>
           .let_ (op2 (.add i64) (.var a) (.var baseInv)) fun (a1, ()) =>
           .let_ (op2 (.add i64) (.var a1) (.var lv)) fun (a2, ()) =>
           .jnz (.var flag)
             (.jump j (.var i1, .var a2, ()))
             (.jump j (.var i1, .var a1, ())))
          (.ret (.var a, ()))) .nil)
      (fun (j, ()) => .jump j (.var i0, .var acc0, ()))⟩

def fnOptCondThread : Fn :=
  ⟨"cov_opt_cthread", [.bool, i64, i64], [i64], fun _ _ (c, a, b, ()) =>
    .group (sig := [[i64]])
      (fun (_, ()) => .cons (fun (x, ()) =>
        .let_ (op2 (.add i64) (.var x) (.imm 1#64)) fun (r, ()) =>
        .ret (.var r, ())) .nil)
      (fun (j, ()) =>
        .jnz (.var c)
          (.call "cov_ext" (as := [i64]) (bs := [i64]) (.var a, ()) fun (rv, ()) =>
           .jump j (.var rv, ()))
          (.jump j (.var b, ())))⟩

def fnOptTailDup : Fn :=
  ⟨"cov_opt_taildup", [.bool, i64, i64], [i64], fun _ _ (c, a, b, ()) =>
    .group (sig := [[i64]])
      (fun (_, ()) => .cons (fun (x, ()) =>
        .let_ (op2 (.add i64) (.var x) (.imm 1#64)) fun (y, ()) =>
        .let_ (op2 (.xor i64) (.var y) (.imm 3#64)) fun (z, ()) =>
        .ret (.var z, ())) .nil)
      (fun (j, ()) =>
        .jnz (.var c)
          (.call "cov_ext" (as := [i64]) (bs := [i64]) (.var a, ()) fun (rv, ()) =>
           .jump j (.var rv, ()))
          (.jump j (.var b, ())))⟩

def covOptFns : List Fn :=
  [ fnInlHelper, fnPairCallee, fnCalls, fnMemWidths, fnNestedCfg
  , fnOptIfFPathMerge, fnOptPeelRot, fnOptZeroPeel, fnOptStraight
  , fnOptMidSimpIfT, fnOptLicmAddrRange, fnOptCondThread, fnOptTailDup ]

/-! ## 3. Shared & Arch-Specific Opcode Coverage Fixtures (`covX64OpsMod`, `covArm64OpsMod`) -/

def fnScalarAll : Fn :=
  ⟨"cov_scalar_all", [i8, i16, i32, i64, .bool], [i8, i64],
    fun _ _ (x8, x16, x32, x64, b, ()) =>
    .let_ (op1 (.copy i8) (.var x8)) fun (c8, ()) =>
    .let_ (op2 (.udiv 8) (.var c8) (.imm 3#8)) fun (ud8, ()) =>
    .let_ (op1 (.ofBool 8) (.var b)) fun (ob8, ()) =>
    .let_ (op1 (.zext 8 16) (.var ob8)) fun (z8, ()) =>
    .let_ (op2 (.sub i16) (.var x16) (.var z8)) fun (s16, ()) =>
    .let_ (op1 (.neg i16) (.var s16)) fun (n16, ()) =>
    .let_ (op2 (.ashr i16) (.var n16) (.imm 1#16)) fun (ar16, ()) =>
    .let_ (op2 (.sdiv 16) (.var ar16) (.var x16)) fun (sd16, ()) =>
    .let_ (op1 (.bswap i16) (.var sd16)) fun (bs16, ()) =>
    .let_ (op1 (.trunc 16 8) (.var bs16)) fun (tr8, ()) =>
    .let_ (op1 (.sext 16 32) (.var bs16)) fun (y32, ()) =>
    .let_ (op2 (.mul i32) (.var x32) (.var y32)) fun (m32, ()) =>
    .let_ (op2 (.shl i32) (.var m32) (.imm 2#32)) fun (sl32, ()) =>
    .let_ (op2 (.rotl i32) (.var sl32) (.var y32)) fun (rl32, ()) =>
    .let_ (op2 (.urem 32) (.var rl32) (.var x32)) fun (ur32, ()) =>
    .let_ (op1 (.clz 32) (.var ur32)) fun (lz32, ()) =>
    .let_ (op1 (.cls 32) (.var lz32)) fun (ls32, ()) =>
    .let_ (op1 (.ctz 32) (.var ls32)) fun (tz32, ()) =>
    .let_ (op3 (.fshl 32) (.var tz32) (.var x32) (.var y32)) fun (fl32, ()) =>
    .let_ (op3 (.addc 32) (.var fl32) (.var y32) (.var b)) fun (ac32, _, ()) =>
    .let_ (op2 (.umulw 32) (.var ac32) (.var y32)) fun (ulo32, uhi32, ()) =>
    .let_ (op1 (.trunc 32 16) (.var ulo32)) fun (t16, ()) =>
    .let_ (op1 (.zext 16 32) (.var t16)) fun (z16, ()) =>
    .let_ (op2 (.xor i32) (.var z16) (.var uhi32)) fun (r32, ()) =>
    .let_ (op1 (.zext 32 64) (.var r32)) fun (y64, ()) =>
    .let_ (op2 (.or i64) (.var x64) (.var y64)) fun (or64, ()) =>
    .let_ (op1 (.not i64) (.var or64)) fun (nt64, ()) =>
    .let_ (op2 (.lshr i64) (.var nt64) (.imm 2#64)) fun (lr64, ()) =>
    .let_ (op2 (.rotr i64) (.var lr64) (.var y64)) fun (rr64, ()) =>
    .let_ (op1 (.bswap i64) (.var rr64)) fun (bs64, ()) =>
    .let_ (op3 (.fshr 64) (.var bs64) (.var y64) (.var x64)) fun (fr64, ()) =>
    .let_ (op3 (.subb 64) (.var fr64) (.var x64) (.var b)) fun (sb64, _, ()) =>
    .let_ (op2 (.smulw 64) (.var sb64) (.var y64)) fun (slo64, shi64, ()) =>
    .let_ (op2 (.srem 64) (.var slo64) (.var shi64)) fun (sr64, ()) =>
    .let_ (op2 (.add i8) (.var tr8) (.var ud8)) fun (res8, ()) =>
    .ret (.var res8, .var sr64, ())⟩

def fnCmpSel : Fn :=
  ⟨"cov_cmp_sel", [i8, i16, i32, i64, .bool], [i64, .bool],
    fun _ _ (a8, a16, a32, a64, b0, ()) =>
    .let_ (op2 (.cmp .eq i8 .bool rfl) (.var a8) (.imm 1#8)) fun (c0, ()) =>
    .let_ (op2 (.cmp .ne i8 .bool rfl) (.var a8) (.imm 2#8)) fun (c1, ()) =>
    .let_ (op2 (.cmp .ult i16 .bool rfl) (.var a16) (.imm 3#16)) fun (c2, ()) =>
    .let_ (op2 (.cmp .ule i16 .bool rfl) (.var a16) (.imm 4#16)) fun (c3, ()) =>
    .let_ (op2 (.cmp .ugt i32 .bool rfl) (.var a32) (.imm 5#32)) fun (c4, ()) =>
    .let_ (op2 (.cmp .uge i32 .bool rfl) (.var a32) (.imm 6#32)) fun (c5, ()) =>
    .let_ (op2 (.cmp .slt i64 .bool rfl) (.var a64) (.imm 7#64)) fun (c6, ()) =>
    .let_ (op2 (.cmp .sle i64 .bool rfl) (.var a64) (.imm 8#64)) fun (c7, ()) =>
    .let_ (op2 (.cmp .sgt i64 .bool rfl) (.var a64) (.imm 9#64)) fun (c8, ()) =>
    .let_ (op2 (.cmp .sge i64 .bool rfl) (.var a64) (.imm 10#64)) fun (c9, ()) =>
    .let_ (op1 (.copy .bool) (.var b0)) fun (bc, ()) =>
    .let_ (op2 (.and .bool) (.var bc) (.var c0)) fun (b1, ()) =>
    .let_ (op2 (.or .bool) (.var b1) (.var c1)) fun (b2, ()) =>
    .let_ (op2 (.xor .bool) (.var b2) (.var c2)) fun (b3, ()) =>
    .let_ (op1 (.not .bool) (.var b3)) fun (b4, ()) =>
    .let_ (op2 (.xor .bool) (.var b4) (.var c9)) fun (bf, ()) =>
    .let_ (op2 (.and .bool) (.var bf) (.var c7)) fun (bf1, ()) =>
    .let_ (op3 (.select i8) (.var c3) (.var a8) (.imm 5#8)) fun (s8, ()) =>
    .let_ (op3 (.select i16) (.var c4) (.var a16) (.imm 6#16)) fun (s16, ()) =>
    .let_ (op3 (.select i32) (.var c5) (.var a32) (.imm 7#32)) fun (s32, ()) =>
    .let_ (op3 (.select i64) (.var c6) (.var a64) (.imm 8#64)) fun (s64, ()) =>
    .let_ (op1 (.zext 8 64) (.var s8)) fun (z8, ()) =>
    .let_ (op1 (.zext 16 64) (.var s16)) fun (z16, ()) =>
    .let_ (op1 (.zext 32 64) (.var s32)) fun (z32, ()) =>
    .let_ (op2 (.add i64) (.var s64) (.var z8)) fun (t0, ()) =>
    .let_ (op2 (.add i64) (.var t0) (.var z16)) fun (t1, ()) =>
    .let_ (op2 (.add i64) (.var t1) (.var z32)) fun (sum, ()) =>
    .let_ (op2 (.or .bool) (.var bf1) (.var c8)) fun (bf2, ()) =>
    .ret (.var sum, .var bf2, ())⟩

def v4i32One : Val v4i32 := ((1#32, 1#32), (1#32, 1#32))
def v8i32One : Val v8i32 := (v4i32One, v4i32One)

def fnX64BitOps : Fn :=
  ⟨"cov_x64_bitops", [i8, i16, i32, i64], [i32, i64],
    fun _ _ (a8, a16, a32, a64, ()) =>
    .let_ (op1 (.clz 8) (.var a8)) fun (lz8, ()) =>
    .let_ (op1 (.ctz 8) (.var lz8)) fun (tz8, ()) =>
    .let_ (op1 (.popcnt 8) (.var tz8)) fun (pp8, ()) =>
    .let_ (op1 (.popcnt 16) (.var a16)) fun (pp16, ()) =>
    .let_ (op1 (.popcnt 32) (.var a32)) fun (pp32, ()) =>
    .let_ (op1 (.popcnt 64) (.var a64)) fun (pp64, ()) =>
    .let_ (op1 (.zext 8 16) (.var pp8)) fun (z8, ()) =>
    .let_ (op2 (.add i16) (.var pp16) (.var z8)) fun (s16, ()) =>
    .let_ (op1 (.zext 16 32) (.var s16)) fun (z16, ()) =>
    .let_ (op2 (.add i32) (.var pp32) (.var z16)) fun (s32, ()) =>
    .ret (.var s32, .var pp64, ())⟩

def fnX64Simd128 : Fn :=
  ⟨"cov_x64_simd128", [i64, v4i32, v4i32, v4f32, v4f32], [v4i32, v4f32],
    fun _ _ (p, v0, v1, f0, f1, ()) =>
    .let_ (op1 (.copy v4i32) (.var v0)) fun (cp, ()) =>
    .let_ (op2 (.add v4i32) (.var cp) (.var v1)) fun (ad, ()) =>
    .let_ (op2 (.and v4i32) (.var ad) (.var v0)) fun (an, ()) =>
    .let_ (op2 (.or v4i32) (.var an) (.var v1)) fun (orv, ()) =>
    .let_ (op2 (.xor v4i32) (.var orv) (.var v0)) fun (xv, ()) =>
    .let_ (op1 (.not v4i32) (.var xv)) fun (nv, ()) =>
    .let_ (op3 (.ternlog v4i32 0x96#8) (.var nv) (.var v0) (.var v1)) fun (tl, ()) =>
    .let_ (op2 (.rotr v4i32) (.var tl) (.imm v4i32One)) fun (rt, ()) =>
    .let_ (op2 (.lshr v4i32) (.var rt) (.imm v4i32One)) fun (ls, ()) =>
    .let_ (op1 (.shufd v4i32 0x1b#8) (.var ls)) fun (sd, ()) =>
    .let_ (op2 (.shufb v4i32) (.var sd) (.var v1)) fun (sb, ()) =>
    .let_ (op2 (.alignr v4i32 4) (.var sb) (.var v0)) fun (al, ()) =>
    .let_ (op2 (.blendw v4i32 0x0f#8) (.var al) (.var v1)) fun (bl, ()) =>
    .load v4i32 (.var p) fun ld =>
    .store (.var ld) (.var p) <|
    .let_ (op2 (.xor v4i32) (.var bl) (.var ld)) fun (outv, ()) =>
    .let_ (op2 (.fadd v4f32) (.var f0) (.var f1)) fun (fa, ()) =>
    .let_ (op2 (.fsub v4f32) (.var fa) (.var f0)) fun (fs, ()) =>
    .ret (.var outv, .var fs, ())⟩

def fnX64SimdWide : Fn :=
  ⟨"cov_x64_simd_wide", [v4i32, v4i32], [i32], fun _ _ (a, b, ()) =>
    .let_ (op2 (.mkpair v4i32 v4i32) (.var a) (.var b)) fun (w0, ()) =>
    .let_ (op2 (.mkpair v4i32 v4i32) (.var b) (.var a)) fun (w1, ()) =>
    .let_ (op1 (.copy v8i32) (.var w0)) fun (wcp, ()) =>
    .let_ (op2 (.add v8i32) (.var wcp) (.var w1)) fun (wad, ()) =>
    .let_ (op2 (.and v8i32) (.var wad) (.var w0)) fun (wan, ()) =>
    .let_ (op2 (.or v8i32) (.var wan) (.var w1)) fun (wor, ()) =>
    .let_ (op2 (.xor v8i32) (.var wor) (.var w0)) fun (wxo, ()) =>
    .let_ (op1 (.not v8i32) (.var wxo)) fun (wnv, ()) =>
    .let_ (op3 (.ternlog v8i32 0x96#8) (.var wnv) (.var w0) (.var w1)) fun (wtl, ()) =>
    .let_ (op2 (.rotr v8i32) (.var wtl) (.imm v8i32One)) fun (wrt, ()) =>
    .let_ (op2 (.lshr v8i32) (.var wrt) (.imm v8i32One)) fun (wls, ()) =>
    .let_ (op2 (.mkpair v8i32 v8i32) (.var wls) (.var w0)) fun (z0, ()) =>
    .let_ (op2 (.xor (Ty.pair v8i32 v8i32)) (.var z0) (.var z0)) fun (zx, ()) =>
    .let_ (op1 (.unpair v8i32 v8i32) (.var zx)) fun (u0, _, ()) =>
    .let_ (op1 (.unpair v4i32 v4i32) (.var u0)) fun (u1, _, ()) =>
    .let_ (op1 (.unpair (.pair i32 i32) (.pair i32 i32)) (.var u1)) fun (u2, _, ()) =>
    .let_ (op1 (.unpair i32 i32) (.var u2)) fun (r0, r1, ()) =>
    .let_ (op2 (.add i32) (.var r0) (.var r1)) fun (res, ()) =>
    .ret (.var res, ())⟩

def fnArm64BitOps : Fn :=
  ⟨"cov_arm64_bitops", [i8, i16, i32, i64], [i64], fun _ _ (a8, a16, a32, a64, ()) =>
    .let_ (op1 (.rbit 32) (.var a32)) fun (rb32, ()) =>
    .let_ (op1 (.rbit 64) (.var a64)) fun (rb64, ()) =>
    .let_ (op2 (.udiv0 8) (.var a8) (.imm 3#8)) fun (ud8, ()) =>
    .let_ (op2 (.sdiv0 16) (.var a16) (.imm 5#16)) fun (sd16, ()) =>
    .let_ (op2 (.udiv0 32) (.var rb32) (.imm 7#32)) fun (ud32, ()) =>
    .let_ (op2 (.sdiv0 64) (.var rb64) (.var a64)) fun (sd64, ()) =>
    .let_ (op1 (.zext 8 64) (.var ud8)) fun (z8, ()) =>
    .let_ (op1 (.sext 16 64) (.var sd16)) fun (s16, ()) =>
    .let_ (op1 (.zext 32 64) (.var ud32)) fun (z32, ()) =>
    .let_ (op2 (.add i64) (.var sd64) (.var z8)) fun (t0, ()) =>
    .let_ (op2 (.add i64) (.var t0) (.var s16)) fun (t1, ()) =>
    .let_ (op2 (.add i64) (.var t1) (.var z32)) fun (res, ()) =>
    .ret (.var res, ())⟩

def fnLegalFloatBitcast : Fn :=
  ⟨"cov_legal_float_bitcast", [i32, i64, f32, f64, v4i32], [v4f32],
    fun _ _ (u32, s64, xf, xd, xv, ()) =>
    .let_ (op1 (.uitofp 32 .s) (.var u32)) fun (fu, ()) =>
    .let_ (op1 (.sitofp 64 .s) (.var s64)) fun (fs, ()) =>
    .let_ (op2 (.fadd f32) (.var fu) (.var fs)) fun (fa, ()) =>
    .let_ (op2 (.fsub f32) (.var fa) (.var xf)) fun (fb, ()) =>
    .let_ (op2 (.fmul f32) (.var fb) (.var xf)) fun (fm, ()) =>
    .let_ (op2 (.fdiv f32) (.var fm) (.var xf)) fun (fd, ()) =>
    .let_ (op1 (.fsqrt f32) (.var fd)) fun (fq, ()) =>
    .let_ (op1 (.fneg f32) (.var fq)) fun (fn_, ()) =>
    .let_ (op1 (.fabs f32) (.var fn_)) fun (fab, ()) =>
    .let_ (op2 (.fcmp .eq f32 f32.mask rfl) (.var fab) (.var xf)) fun (fc, ()) =>
    .let_ (op1 (.fptoui .s 32) (.var fab)) fun (pui, ()) =>
    .let_ (op1 (.fptosi .s 64) (.var fab)) fun (psi, ()) =>
    .let_ (op1 (.fcvt .s .d) (.var fab)) fun (f2d, ()) =>
    .let_ (op1 (.uitofp 32 .d) (.var pui)) fun (du, ()) =>
    .let_ (op1 (.sitofp 64 .d) (.var psi)) fun (ds, ()) =>
    .let_ (op2 (.fadd f64) (.var f2d) (.var du)) fun (da, ()) =>
    .let_ (op2 (.fsub f64) (.var da) (.var ds)) fun (db, ()) =>
    .let_ (op2 (.fmul f64) (.var db) (.var xd)) fun (dm, ()) =>
    .let_ (op2 (.fdiv f64) (.var dm) (.var xd)) fun (dd, ()) =>
    .let_ (op1 (.fsqrt f64) (.var dd)) fun (dq, ()) =>
    .let_ (op1 (.fneg f64) (.var dq)) fun (dn, ()) =>
    .let_ (op1 (.fabs f64) (.var dn)) fun (dab, ()) =>
    .let_ (op2 (.fcmp .lt f64 f64.mask rfl) (.var dab) (.var xd)) fun (dc, ()) =>
    .let_ (op1 (.fptoui .d 64) (.var dab)) fun (dui, ()) =>
    .let_ (op1 (.fptosi .d 64) (.var dab)) fun (dsi, ()) =>
    .let_ (op1 (.fcvt .d .s) (.var dab)) fun (d2s, ()) =>
    .let_ (op1 (.bitcast i64 f64 rfl) (.var dui)) fun (bd0, ()) =>
    .let_ (op1 (.bitcast f64 i64 rfl) (.var bd0)) fun (bd1, ()) =>
    .let_ (op1 (.bitcast i32 f32 rfl) (.var pui)) fun (bc0, ()) =>
    .let_ (op1 (.bitcast f32 i32 rfl) (.var bc0)) fun (bc1, ()) =>
    .let_ (op1 (.ofBool 64) (.var fc)) fun (ob0, ()) =>
    .let_ (op1 (.ofBool 64) (.var dc)) fun (ob1, ()) =>
    .let_ (op2 (.add i64) (.var dsi) (.var bd1)) fun (s0, ()) =>
    .let_ (op2 (.add i64) (.var s0) (.var ob0)) fun (s1, ()) =>
    .let_ (op2 (.add i64) (.var s1) (.var ob1)) fun (_, ()) =>
    .let_ (op1 (.bitcast v4i32 v4f32 rfl) (.var xv)) fun (vf, ()) =>
    .let_ (op2 (.fadd v4f32) (.var vf) (.imm (((0#32, 0#32), (0#32, 0#32))))) fun (vf2, ()) =>
    .let_ (op1 (.bitcast v4f32 v4i32 rfl) (.var vf2)) fun (vi, ()) =>
    .let_ (op1 (.bitcast v4i32 v4f32 rfl) (.var vi)) fun (vf3, ()) =>
    .let_ (op2 (.fsub v4f32) (.var vf3) (.imm (((0#32, 0#32), (0#32, 0#32))))) fun (vf4, ()) =>
    .let_ (op2 (.fadd f32) (.var d2s) (.var xf)) fun (fs0, ()) =>
    .let_ (op1 (.bitcast f32 i32 rfl) (.var fs0)) fun (bi, ()) =>
    .let_ (op2 (.add i32) (.var bc1) (.var bi)) fun (bi2, ()) =>
    .let_ (op2 (.mkpair (.bits 32) (.bits 32)) (.var u32) (.var bi2)) fun (_, ()) =>
    .ret (.var vf4, ())⟩

def fnX64Float32Bitcast : Fn :=
  ⟨"cov_x64_f32_bitcast", [i32, i64, f32, v4i32], [v4f32],
    fun _ _ (u32, s64, xf, xv, ()) =>
    .let_ (op1 (.uitofp 32 .s) (.var u32)) fun (fu, ()) =>
    .let_ (op1 (.sitofp 64 .s) (.var s64)) fun (fs, ()) =>
    .let_ (op2 (.fadd f32) (.var fu) (.var fs)) fun (fa, ()) =>
    .let_ (op2 (.fsub f32) (.var fa) (.var xf)) fun (fb, ()) =>
    .let_ (op2 (.fmul f32) (.var fb) (.var xf)) fun (fm, ()) =>
    .let_ (op2 (.fdiv f32) (.var fm) (.var xf)) fun (fd, ()) =>
    .let_ (op1 (.fsqrt f32) (.var fd)) fun (fq, ()) =>
    .let_ (op1 (.fneg f32) (.var fq)) fun (fn_, ()) =>
    .let_ (op1 (.fabs f32) (.var fn_)) fun (fab, ()) =>
    .let_ (op2 (.fcmp .eq f32 f32.mask rfl) (.var fab) (.var xf)) fun (fc, ()) =>
    .let_ (op1 (.fptoui .s 32) (.var fab)) fun (pui, ()) =>
    .let_ (op1 (.fptosi .s 64) (.var fab)) fun (psi, ()) =>
    .let_ (op1 (.bitcast i32 f32 rfl) (.var pui)) fun (bc0, ()) =>
    .let_ (op1 (.bitcast f32 i32 rfl) (.var bc0)) fun (bc1, ()) =>
    .let_ (op1 (.trunc 64 32) (.var psi)) fun (tp, ()) =>
    .let_ (op2 (.add i32) (.var bc1) (.var tp)) fun (sm, ()) =>
    .let_ (op1 (.ofBool 32) (.var fc)) fun (ob, ()) =>
    .let_ (op2 (.xor i32) (.var sm) (.var ob)) fun (xr, ()) =>
    .let_ (op1 (.bitcast i32 f32 rfl) (.var xr)) fun (fval, ()) =>
    .let_ (op2 (.fadd f32) (.var fval) (.var xf)) fun (fval2, ()) =>
    .let_ (op1 (.bitcast v4i32 v4f32 rfl) (.var xv)) fun (vf, ()) =>
    .let_ (op2 (.fadd v4f32) (.var vf) (.imm (((0#32, 0#32), (0#32, 0#32))))) fun (vf2, ()) =>
    .let_ (op1 (.bitcast v4f32 v4i32 rfl) (.var vf2)) fun (vi, ()) =>
    .let_ (op1 (.bitcast v4i32 v4f32 rfl) (.var vi)) fun (vf3, ()) =>
    .let_ (op2 (.fsub v4f32) (.var vf3) (.imm (((0#32, 0#32), (0#32, 0#32))))) fun (vf4, ()) =>
    .let_ (op2 (.mkpair (.bits 32) (.bits 32)) (.var u32) (.var sm)) fun (_, ()) =>
    .let_ (op1 (.bitcast f32 i32 rfl) (.var fval2)) fun (_, ()) =>
    .ret (.var vf4, ())⟩

def covOptSrcMod : LeanQbe.T.Module := { fns := covOptFns }
def covX64OpsSrcMod : LeanQbe.T.Module :=
  { fns := [fnScalarAll, fnCmpSel, fnX64BitOps, fnX64Simd128, fnX64SimdWide] }
def covArm64OpsSrcMod : LeanQbe.T.Module :=
  { fns := [fnScalarAll, fnCmpSel, fnArm64BitOps] }

def covPol : InlinePolicy :=
  { budget := fun nm => if nm == "cov_inl_helper" then 16 else 0
  , maxCallerSize := 80
  , maxCallerCalls := 4 }

inline_mod! covOptMod covOptSrcMod covPol (compile := false)
inline_mod! covX64OpsMod covX64OpsSrcMod {} (compile := false)
inline_mod! covArm64OpsMod covArm64OpsSrcMod {} (compile := false)

/-! ## 4. Explicit `#guard` Verification of Inlining, `supportsSource`, & Every `MainFlat` Gate -/

def callsFnInlined? : Option Fn :=
  (covOptSrcMod.optInlinePolicy covPol).fns.find? (·.name == "cov_calls")

#guard (callsFnInlined?.map (hasCallInFn "cov_inl_helper")) == some false
#guard (callsFnInlined?.map (hasCallInFn "cov_pair_callee")) == some true
#guard (callsFnInlined?.map (hasCallInFn "cov_ext")) == some true

#guard TFlat.supportsSource LegalTarget.x64 (reifyFunc fnLegalFloatBitcast.body)

-- Early-stage gates (`earlyOptFlat`):
#guard
  let f := toTf fnOptIfFPathMerge
  let tf0 := earlyPreIfF f.as f.body
  let tf1 := OptFlatCfg.ifOptFlat false f.as tf0
  !(tflatEq tf0 tf1)

#guard
  let f := toTf fnOptIfFPathMerge
  let tf1 := OptFlatCfg.ifOptFlat false f.as (earlyPreIfF f.as f.body)
  let tf2 := simplifyGroupFastFlat f.as tf1
  hasSimpGroup (decide (tflatLoops tf1 ≤ 1)) tf1 &&
    (SgpImpl.buildPlan 0 tf1).2.changed && !(tflatEq tf1 tf2)

#guard
  let f := toTf fnOptPeelRot
  let tf1 := OptFlatCfg.ifOptFlat false f.as (earlyPreIfF f.as f.body)
  let tf2 := simplifyGroupFastFlat f.as tf1
  let tf3 := peelFastFlat f.as tf2
  tflatLoops tf2 ≤ 1 && tflatSize tf2 ≤ 40 && !(tflatEq tf2 tf3)

#guard
  let f := toTf fnOptZeroPeel
  let tf1 := OptFlatCfg.ifOptFlat false f.as (earlyPreIfF f.as f.body)
  let tf2 := simplifyGroupFastFlat f.as tf1
  let tf3 := peelFastFlat f.as tf2
  let tf4 := TFlat.zeroPeelWith { peelBudget := 24 } tf3
  tflatEq tf1 tf2 && tflatEq tf2 tf3 && !(tflatEq tf3 tf4)

-- Mid-stage gates (`midStageFlat`):
#guard
  let st := midAt LegalTarget.x64 fnOptStraight.as (reifyFunc fnOptStraight.body)
  !(tflatEq st.tf0c st.tfDiv) &&
    !(tflatEq st.tfPreMem st.tfMem) &&
    !(tflatEq st.tfGvn st.tfAssB) &&
    !(tflatEq st.tfMidSimp st.tfDle)

#guard
  let st := midAt LegalTarget.x64 fnOptMidSimpIfT.as (reifyFunc fnOptMidSimpIfT.body)
  !(tflatEq st.tfPreIfT st.tfIfT) &&
    hasSimpGroup (decide (tflatLoops st.tfIfT ≤ 1)) st.tfIfT &&
    (SgpImpl.buildPlan 0 st.tfIfT).2.changed &&
    !(tflatEq st.tfIfT st.tfMidSimp)

#guard
  let st := midAt LegalTarget.x64 fnOptLicmAddrRange.as (reifyFunc fnOptLicmAddrRange.body)
  (AddrRangeOpt.buildLoopTree false st.tfPreAr).2 &&
    !(tflatEq st.tfPreAr st.tfAr) &&
    (Licm.buildHoistPlan fnOptLicmAddrRange.as.length st.tfPreLicm).hasHoists &&
    (Licm.buildRoPlan fnOptLicmAddrRange.as.length st.tfPreLicm).hasChanges &&
    !(tflatEq st.tfPreLicm st.tfLicm) &&
    (LoopRotate.buildRotPlan
      (as := fnOptLicmAddrRange.as) LoopRotate.defaultRotConfig st.tfPreRot).hasRot &&
    !(tflatEq st.tfPreRot st.tfRot)

#guard
  let st := midAt LegalTarget.x64 fnOptIfFPathMerge.as (reifyFunc fnOptIfFPathMerge.body)
  !(tflatEq st.tfPrePc st.tfPathC) &&
    tflatRets st.tfTd ≥ 2 && !(tflatEq st.tfTd st.tfMr)

#guard
  let st := midAt LegalTarget.x64 fnOptCondThread.as (reifyFunc fnOptCondThread.body)
  let (cSt, _) := CondThreadOpt.collectStats 0 st.tfPathC
  (CondThreadOpt.buildCTPlan [] st.tfPathC cSt).hasChanges && !(tflatEq st.tfPathC st.tfCt)

#guard
  let st := midAt LegalTarget.x64 fnOptTailDup.as (reifyFunc fnOptTailDup.body)
  (TailDup.buildPlan {} 0 st.tfPreTd).2.changed && !(tflatEq st.tfPreTd st.tfTd)

/-! ## 5. Shared Exported `MainFlat` Transitive Closure Static Audit -/

/-- Fails if the exported transitive closure of `compileModuleFlat`, `earlyOptFlat`, or
`midStageFlat` contains `.opaqueInfo`, `WellFounded.fix`/`Classical.choice`, or any unexpected
non-theorem `.axiomInfo` constant that could stall `Lean.Kernel.whnf`. -/
private meta def auditMainFlatClosure : Lean.MetaM Unit := do
  let env ← Lean.getEnv
  let roots : List Lean.Name :=
    [`LeanQbe.T.compileModuleFlat, `LeanQbe.T.earlyOptFlat, `LeanQbe.T.midStageFlat]
  let allowedAxioms : List Lean.Name :=
    [ `Nat.land, `Nat.lor, `Nat.xor, `Nat.repr, `String.Internal.append
    , `Lean.mkAtom, `Max.leftLeaningOfLE, `Min.leftLeaningOfLE, `ByteArray.decidableLT ]
  let mut visited : Lean.NameHashSet := {}
  let mut queue : List Lean.Name := roots
  let mut opaques : List Lean.Name := []
  let mut badAxioms : List Lean.Name := []
  let mut wfOrChoice : List Lean.Name := []
  while !queue.isEmpty do
    let hd := queue.head!
    queue := queue.tail!
    if visited.contains hd then continue
    visited := visited.insert hd
    let some ci := env.find? hd | continue
    match ci with
    | .opaqueInfo _ => opaques := hd :: opaques
    | .axiomInfo ai =>
      let isP ← Lean.withEnv env <| Lean.Meta.isProp ai.type
      if !isP && !allowedAxioms.contains hd then
        badAxioms := hd :: badAxioms
    | _ => pure ()
    if hd == ``WellFounded.fix || hd == ``WellFounded.fixF || hd == ``Classical.choice then
      wfOrChoice := hd :: wfOrChoice
    for d in ci.getUsedConstantsAsSet do
      if !visited.contains d then queue := d :: queue
  if !opaques.isEmpty then
    throwError "MainFlat exported closure has unexpected opaque constants: {opaques}"
  if !wfOrChoice.isEmpty then
    throwError "MainFlat exported closure pulls non-kernel-reducible WF/choice: {wfOrChoice}"
  if !badAxioms.isEmpty then
    throwError "MainFlat exported closure has unexpected non-theorem axioms: {badAxioms}"

#eval auditMainFlatClosure

end LeanQbeTest.T.CompilerCoverage