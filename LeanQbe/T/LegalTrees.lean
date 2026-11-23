module

public import LeanQbe.T.LegalBase

/-!
# Legalization tree lifters and `legalOp` (Part 2)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Generic tree lifters for unary, binary, ternary, comparison, select, and blend ops -/

/-- Legalize any leaf-wise unary op over `t`. -/
def legalUnaryTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (mkCode : (u : Ty) → OpCode [u] [u])
    (vecSupported : (u : Ty) → Bool)
    (onBool : Arg V .bool → (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) →
      (Arg V (.float f) → Expr V L rs) → Expr V L rs) :
    (t : Ty) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | .bool, (x, ()), k => onBool x fun r => k (r, ())
  | .bits n, (x, ()), k => onBits n x fun r => k (r, ())
  | .float f, (x, ()), k => onFloat f x fun r => k (r, ())
  | .pair t1 t2, xs, k =>
    if h : target.keepsPacked (.pair t1 t2) then
      let xs' := packedToTup h xs
      if vecSupported (.pair t1 t2) then
        .let_ (op1 (mkCode (.pair t1 t2)) xs'.1) fun (r, ()) =>
          k (tupToPacked h (.var r, ()))
      else
        splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
        let rec goS : (u : Ty) → Tup (Arg V) (target.leafTys u) →
            (Tup (Arg V) (target.leafTys u) → Expr V L rs) → Expr V L rs
          | .bool, (x, ()), cont => onBool x fun r => cont (r, ())
          | .bits n, (x, ()), cont => onBits n x fun r => cont (r, ())
          | .float f, (x, ()), cont => onFloat f x fun r => cont (r, ())
          | .pair u1 u2, fxu, cont =>
            let (fx1, fx2) := tupSplit fxu
            goS u1 fx1 fun r1 => goS u2 fx2 fun r2 => cont (tupAppend r1 r2)
        goS (.pair t1 t2) fx fun fres => packLeavesToLegal target (.pair t1 t2) fres k
    else
      let hf := Bool.eq_false_iff.mpr h
      let (x1, x2) := tupSplit (splitToTup hf xs)
      legalUnaryTree target mkCode vecSupported onBool onBits onFloat t1 x1 fun r1 =>
      legalUnaryTree target mkCode vecSupported onBool onBits onFloat t2 x2 fun r2 =>
      k (tupToSplit hf (tupAppend r1 r2))

/-- Legalize `bswap t` across scalar/pair types (splitting packed vectors since `bswap` is
scalar-only on target). -/
def legalBswapTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | t, xs, k =>
    if !t.bswapOk then .hlt
    else
      legalUnaryTree target .bswap (fun _ => false)
        (fun _ _ => .hlt)
        (fun n x cont =>
          let w := target.widenWidth n
          if n == 0 then cont (.imm 0#w)
          else if n == 8 then cont x
          else if n == w then
            .let_ (op1 (.bswap (.bits w)) x) fun (r, ()) => cont (.var r)
          else if w % 8 == 0 then
            .let_ (op1 (.bswap (.bits w)) x) fun (bw, ()) =>
            .let_ (op2 (.lshr (.bits w)) (.var bw) (.imm (BitVec.ofNat w (w - n)))) fun (r, ()) =>
            cont (.var r)
          else .hlt)
        (fun _ _ _ => .hlt)
        t xs k

/-- Legalize any leaf-wise ternary op (`ternlog`, `ffma`) over `t`. -/
def legalTernaryTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (mkCode : (u : Ty) → OpCode [u, u, u] [u])
    (vecSupported : (u : Ty) → Bool)
    (onBool : Arg V .bool → Arg V .bool → Arg V .bool →
      (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) →
      Arg V (.bits (target.widenWidth n)) →
      Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) → Arg V (.float f) → Arg V (.float f) →
      (Arg V (.float f) → Expr V L rs) → Expr V L rs) :
    (t : Ty) → Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | .bool, (a, ()), (b, ()), (c, ()), k => onBool a b c fun r => k (r, ())
  | .bits n, (a, ()), (b, ()), (c, ()), k => onBits n a b c fun r => k (r, ())
  | .float f, (a, ()), (b, ()), (c, ()), k => onFloat f a b c fun r => k (r, ())
  | .pair t1 t2, xs, ys, zs, k =>
    if h : target.keepsPacked (.pair t1 t2) then
      let xs' := packedToTup h xs
      let ys' := packedToTup h ys
      let zs' := packedToTup h zs
      if vecSupported (.pair t1 t2) then
        .let_ (op3 (mkCode (.pair t1 t2)) xs'.1 ys'.1 zs'.1) fun (r, ()) =>
          k (tupToPacked h (.var r, ()))
      else
        splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
        splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
        splitLegalToLeaves target (.pair t1 t2) zs fun fz =>
        let rec goS : (u : Ty) → Tup (Arg V) (target.leafTys u) →
            Tup (Arg V) (target.leafTys u) → Tup (Arg V) (target.leafTys u) →
            (Tup (Arg V) (target.leafTys u) → Expr V L rs) → Expr V L rs
          | .bool, (a, ()), (b, ()), (c, ()), cont => onBool a b c fun r => cont (r, ())
          | .bits n, (a, ()), (b, ()), (c, ()), cont => onBits n a b c fun r => cont (r, ())
          | .float f, (a, ()), (b, ()), (c, ()), cont => onFloat f a b c fun r => cont (r, ())
          | .pair u1 u2, fxu, fyu, fzu, cont =>
            let (fx1, fx2) := tupSplit fxu
            let (fy1, fy2) := tupSplit fyu
            let (fz1, fz2) := tupSplit fzu
            goS u1 fx1 fy1 fz1 fun r1 => goS u2 fx2 fy2 fz2 fun r2 => cont (tupAppend r1 r2)
        goS (.pair t1 t2) fx fy fz fun fres => packLeavesToLegal target (.pair t1 t2) fres k
    else
      let hf := Bool.eq_false_iff.mpr h
      let (x1, x2) := tupSplit (splitToTup hf xs)
      let (y1, y2) := tupSplit (splitToTup hf ys)
      let (z1, z2) := tupSplit (splitToTup hf zs)
      legalTernaryTree target mkCode vecSupported onBool onBits onFloat t1 x1 y1 z1 fun r1 =>
      legalTernaryTree target mkCode vecSupported onBool onBits onFloat t2 x2 y2 z2 fun r2 =>
      k (tupToSplit hf (tupAppend r1 r2))

/-- Non-dependent tag distinguishing `rotl` (`some true`) and `shl` (`some false`) from all other
opcodes without dependent GADT pattern matching on fixed index lists. -/
@[reducible] def opShiftKind : {as bs : List Ty} → OpCode as bs → Option Bool
  | _, _, .rotl _ => some true
  | _, _, .shl _ => some false
  | _, _, _ => none

/-- Non-dependent tag identifying shift/rotate opcodes (`shl`/`lshr`/`ashr`/`rotl`/`rotr`). -/
@[reducible] def opIsShift : {as bs : List Ty} → OpCode as bs → Bool
  | _, _, .shl _
  | _, _, .lshr _
  | _, _, .ashr _
  | _, _, .rotl _
  | _, _, .rotr _ => true
  | _, _, _ => false

/-- Check whether `rhs` at type `u` is a uniform `.imm` when `code` is a shift/rotate opcode. -/
@[reducible] def checkUniformImmShift {V : Ty → Type} {as bs : List Ty} (u : Ty)
    (code : OpCode as bs) (rhs : Arg V u) : Bool :=
  if opIsShift code then
    match rhs with
    | .imm c => (uniformShiftLeaf? u c).isSome
    | _ => false
  else false

/-- Legalize a leaf-wise binary operation over `t`. -/
def legalBinTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (mkCode : (u : Ty) → OpCode [u, u] [u])
    (vecSupported : (u : Ty) → Bool → Bool)
    (onBool : Arg V .bool → Arg V .bool → (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) →
      Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) → Arg V (.float f) →
      (Arg V (.float f) → Expr V L rs) → Expr V L rs)
    (uniformImmRhs : (u : Ty) → Arg (LVar target V) u → Bool) :
    (t : Ty) → Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    Option (Arg (LVar target V) t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | .bool, (a, ()), (b, ()), _, k => onBool a b fun r => k (r, ())
  | .bits n, (a, ()), (b, ()), _, k => onBits n a b fun r => k (r, ())
  | .float f, (a, ()), (b, ()), _, k => onFloat f a b fun r => k (r, ())
  | .pair t1 t2, xs, ys, rawRhs, k =>
    if h : target.keepsPacked (.pair t1 t2) then
      let xs' := packedToTup h xs
      let ys' := packedToTup h ys
      let unif := checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) ys'.1
      if vecSupported (.pair t1 t2) unif then
        .let_ (op2 (mkCode (.pair t1 t2)) xs'.1 ys'.1) fun (r, ()) =>
          k (tupToPacked h (.var r, ()))
      else
        let handledDerived : Option (Expr V L rs) :=
          match opShiftKind (mkCode (.pair t1 t2)), rawRhs with
          | some true, some (.imm c) =>
            match uniformShiftLeaf? (.pair t1 t2) c with
            | some (w, s) =>
              if s == 0 then
                some (k (tupToPacked h xs'))
              else if target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true then
                let rc := splatBits w (BitVec.ofNat w (w - s)) (.pair t1 t2)
                some (.let_ (op2 (.rotr (.pair t1 t2)) xs'.1 (.imm rc)) fun (r, ()) =>
                  k (tupToPacked h (.var r, ())))
              else none
            | none => none
          | some false, some (.imm c) =>
            match uniformShiftLeaf? (.pair t1 t2) c with
            | some (w, s) =>
              if s == 0 then
                some (k (tupToPacked h xs'))
              else if target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true &&
                      target.vecIntOpSupported (.and (.pair t1 t2)) (.pair t1 t2) false then
                let rc := splatBits w (BitVec.ofNat w (w - s)) (.pair t1 t2)
                let mc := splatBits w (BitVec.allOnes w <<< s) (.pair t1 t2)
                some (.let_ (op2 (.rotr (.pair t1 t2)) xs'.1 (.imm rc)) fun (rt, ()) =>
                  .let_ (op2 (.and (.pair t1 t2)) (.var rt) (.imm mc)) fun (r, ()) =>
                    k (tupToPacked h (.var r, ())))
              else none
            | none => none
          | _, _ => none
        match handledDerived with
        | some e => e
        | none =>
          splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
          splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
          let rec goS : (u : Ty) → Tup (Arg V) (target.leafTys u) →
              Tup (Arg V) (target.leafTys u) →
              (Tup (Arg V) (target.leafTys u) → Expr V L rs) → Expr V L rs
            | .bool, (a, ()), (b, ()), cont => onBool a b fun r => cont (r, ())
            | .bits n, (a, ()), (b, ()), cont => onBits n a b fun r => cont (r, ())
            | .float f, (a, ()), (b, ()), cont => onFloat f a b fun r => cont (r, ())
            | .pair u1 u2, fxu, fyu, cont =>
              let (fx1, fx2) := tupSplit fxu
              let (fy1, fy2) := tupSplit fyu
              goS u1 fx1 fy1 fun r1 => goS u2 fx2 fy2 fun r2 => cont (tupAppend r1 r2)
          goS (.pair t1 t2) fx fy fun fres => packLeavesToLegal target (.pair t1 t2) fres k
    else
      let hf := Bool.eq_false_iff.mpr h
      let (x1, x2) := tupSplit (splitToTup hf xs)
      let (y1, y2) := tupSplit (splitToTup hf ys)
      legalBinTree target mkCode vecSupported onBool onBits onFloat uniformImmRhs t1 x1 y1 none
        fun r1 =>
      legalBinTree target mkCode vecSupported onBool onBits onFloat uniformImmRhs t2 x2 y2 none
        fun r2 =>
      k (tupToSplit hf (tupAppend r1 r2))

/-- Legalize arithmetic/bitwise/shift at a scalar `.bits n` leaf. -/
def legalBitsArith (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (n : Nat) : OpCode [.bits n, .bits n] [.bits n] →
    Arg V (.bits (target.widenWidth n)) → Arg V (.bits (target.widenWidth n)) →
    (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs
  | code, a, b, k =>
    let w := target.widenWidth n
    if n == 0 then k (.imm 0#w)
    else
      match code with
      | .add _ => .let_ (op2 (.add (.bits w)) a b) fun (r, ()) => emitMaskToN n w (.var r) k
      | .sub _ => .let_ (op2 (.sub (.bits w)) a b) fun (r, ()) => emitMaskToN n w (.var r) k
      | .mul _ => .let_ (op2 (.mul (.bits w)) a b) fun (r, ()) => emitMaskToN n w (.var r) k
      | .and _ => .let_ (op2 (.and (.bits w)) a b) fun (r, ()) => k (.var r)
      | .or _ => .let_ (op2 (.or (.bits w)) a b) fun (r, ()) => k (.var r)
      | .xor _ => .let_ (op2 (.xor (.bits w)) a b) fun (r, ()) => k (.var r)
      | .shl _ =>
        if n == w then .let_ (op2 (.shl (.bits w)) a b) fun (r, ()) => k (.var r)
        else emitCountMod n w b fun c =>
          .let_ (op2 (.shl (.bits w)) a c) fun (r, ()) => emitMaskToN n w (.var r) k
      | .lshr _ =>
        if n == w then .let_ (op2 (.lshr (.bits w)) a b) fun (r, ()) => k (.var r)
        else emitCountMod n w b fun c =>
          .let_ (op2 (.lshr (.bits w)) a c) fun (r, ()) => k (.var r)
      | .ashr _ =>
        if n == w then .let_ (op2 (.ashr (.bits w)) a b) fun (r, ()) => k (.var r)
        else emitCountMod n w b fun c => emitSextToW n w a fun sa =>
          .let_ (op2 (.ashr (.bits w)) sa c) fun (r, ()) => emitMaskToN n w (.var r) k
      | .rotl _ =>
        if n == w then .let_ (op2 (.rotl (.bits w)) a b) fun (r, ()) => k (.var r)
        else
          emitCountMod n w b fun c =>
          .let_ (op2 (.sub (.bits w)) (.imm (BitVec.ofNat w n)) c) fun (nc, ()) =>
          .let_ (op2 (.shl (.bits w)) a c) fun (lo, ()) =>
          .let_ (op2 (.lshr (.bits w)) a (.var nc)) fun (hi, ()) =>
          .let_ (op2 (.or (.bits w)) (.var lo) (.var hi)) fun (comb, ()) =>
          emitMaskToN n w (.var comb) k
      | .rotr _ =>
        if n == w then .let_ (op2 (.rotr (.bits w)) a b) fun (r, ()) => k (.var r)
        else
          emitCountMod n w b fun c =>
          .let_ (op2 (.sub (.bits w)) (.imm (BitVec.ofNat w n)) c) fun (nc, ()) =>
          .let_ (op2 (.lshr (.bits w)) a c) fun (lo, ()) =>
          .let_ (op2 (.shl (.bits w)) a (.var nc)) fun (hi, ()) =>
          .let_ (op2 (.or (.bits w)) (.var lo) (.var hi)) fun (comb, ()) =>
          emitMaskToN n w (.var comb) k
      | _ => .hlt

/-- Legalize `cmp o t` into scalar comparisons / boolean logic. -/
def legalCmpTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (o : CmpOp) : (t : Ty) → Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t.mask) → Expr V L rs) → Expr V L rs
  | .bool, (a, ()), (b, ()), k =>
    if target.boolCmp then .let_ (op2 (.cmp o .bool) a b) fun (r, ()) => k (.var r, ())
    else emitBoolCmp o a b fun r => k (r, ())
  | .bits n, (a, ()), (b, ()), k =>
    let w := target.widenWidth n
    if n == 0 then k (.imm (o.evalBits 0#0 0#0), ())
    else if n == w then .let_ (op2 (.cmp o (.bits w)) a b) fun (r, ()) => k (.var r, ())
    else
      let isSigned := match o with | .slt | .sle | .sgt | .sge => true | _ => false
      if isSigned then
        emitSextToW n w a fun sa => emitSextToW n w b fun sb =>
          .let_ (op2 (.cmp o (.bits w)) sa sb) fun (r, ()) => k (.var r, ())
      else .let_ (op2 (.cmp o (.bits w)) a b) fun (r, ()) => k (.var r, ())
  | .float _, _, _, _ => .hlt
  | .pair t1 t2, xs, ys, k =>
    splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
    splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
    let rec goMask : (u : Ty) → Tup (Arg V) (target.leafTys u) →
        Tup (Arg V) (target.leafTys u) →
        (Tup (Arg V) (target.leafTys u.mask) → Expr V L rs) → Expr V L rs
      | .bool, (a, ()), (b, ()), cont =>
        if target.boolCmp then .let_ (op2 (.cmp o .bool) a b) fun (r, ()) => cont (.var r, ())
        else emitBoolCmp o a b fun r => cont (r, ())
      | .bits n, (a, ()), (b, ()), cont =>
        let w := target.widenWidth n
        if n == 0 then cont (.imm (o.evalBits 0#0 0#0), ())
        else if n == w then .let_ (op2 (.cmp o (.bits w)) a b) fun (r, ()) => cont (.var r, ())
        else
          let isSigned := match o with | .slt | .sle | .sgt | .sge => true | _ => false
          if isSigned then
            emitSextToW n w a fun sa => emitSextToW n w b fun sb =>
              .let_ (op2 (.cmp o (.bits w)) sa sb) fun (r, ()) => cont (.var r, ())
          else .let_ (op2 (.cmp o (.bits w)) a b) fun (r, ()) => cont (.var r, ())
      | .float _, _, _, _ => .hlt
      | .pair u1 u2, fxu, fyu, cont =>
        let (fx1, fx2) := tupSplit fxu
        let (fy1, fy2) := tupSplit fyu
        goMask u1 fx1 fy1 fun m1 => goMask u2 fx2 fy2 fun m2 => cont (tupAppend m1 m2)
    goMask (.pair t1 t2) fx fy fun mres => packLeavesToLegal target (Ty.mask (.pair t1 t2)) mres k

/-- Legalize `select` over `t`. -/
def legalSelectTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (c : Arg V .bool) : (t : Ty) →
    Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | .bool, (a, ()), (b, ()), k =>
    if target.boolSelect then .let_ (op3 (.select .bool) c a b) fun (r, ()) => k (.var r, ())
    else emitBoolSelect c a b fun r => k (r, ())
  | .bits n, (a, ()), (b, ()), k =>
    .let_ (op3 (.select (.bits (target.widenWidth n))) c a b) fun (r, ()) => k (.var r, ())
  | .float f, (a, ()), (b, ()), k =>
    .let_ (op3 (.select (.float f)) c a b) fun (r, ()) => k (.var r, ())
  | .pair t1 t2, xs, ys, k =>
    splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
    splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
    let rec goSel : (u : Ty) → Tup (Arg V) (target.leafTys u) →
        Tup (Arg V) (target.leafTys u) →
        (Tup (Arg V) (target.leafTys u) → Expr V L rs) → Expr V L rs
      | .bool, (a, ()), (b, ()), cont =>
        if target.boolSelect then .let_ (op3 (.select .bool) c a b) fun (r, ()) => cont (.var r, ())
        else emitBoolSelect c a b fun r => cont (r, ())
      | .bits n, (a, ()), (b, ()), cont =>
        .let_ (op3 (.select (.bits (target.widenWidth n))) c a b) fun (r, ()) => cont (.var r, ())
      | .float f, (a, ()), (b, ()), cont =>
        .let_ (op3 (.select (.float f)) c a b) fun (r, ()) => cont (.var r, ())
      | .pair u1 u2, fxu, fyu, cont =>
        let (fx1, fx2) := tupSplit fxu
        let (fy1, fy2) := tupSplit fyu
        goSel u1 fx1 fy1 fun r1 => goSel u2 fx2 fy2 fun r2 => cont (tupAppend r1 r2)
    goSel (.pair t1 t2) fx fy fun fres => packLeavesToLegal target (.pair t1 t2) fres k

/-- Legalize `blend t` into scalar `select`s on `bool` leaves. -/
def legalBlendTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → Tup (Arg V) (target.legalTys t.mask) →
    Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | .bool, (c, ()), (a, ()), (b, ()), k =>
    if target.boolSelect then .let_ (op3 (.select .bool) c a b) fun (r, ()) => k (.var r, ())
    else emitBoolSelect c a b fun r => k (r, ())
  | .bits n, (c, ()), (a, ()), (b, ()), k =>
    .let_ (op3 (.select (.bits (target.widenWidth n))) c a b) fun (r, ()) => k (.var r, ())
  | .float f, (c, ()), (a, ()), (b, ()), k =>
    .let_ (op3 (.select (.float f)) c a b) fun (r, ()) => k (.var r, ())
  | .pair t1 t2, ms, xs, ys, k =>
    splitLegalToLeaves target (Ty.mask (.pair t1 t2)) ms fun fm =>
    splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
    splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
    let rec goBlend : (u : Ty) → Tup (Arg V) (target.leafTys u.mask) →
        Tup (Arg V) (target.leafTys u) → Tup (Arg V) (target.leafTys u) →
        (Tup (Arg V) (target.leafTys u) → Expr V L rs) → Expr V L rs
      | .bool, (c, ()), (a, ()), (b, ()), cont =>
        if target.boolSelect then .let_ (op3 (.select .bool) c a b) fun (r, ()) => cont (.var r, ())
        else emitBoolSelect c a b fun r => cont (r, ())
      | .bits n, (c, ()), (a, ()), (b, ()), cont =>
        .let_ (op3 (.select (.bits (target.widenWidth n))) c a b) fun (r, ()) => cont (.var r, ())
      | .float f, (c, ()), (a, ()), (b, ()), cont =>
        .let_ (op3 (.select (.float f)) c a b) fun (r, ()) => cont (.var r, ())
      | .pair u1 u2, fmu, fxu, fyu, cont =>
        let (fm1, fm2) := tupSplit fmu
        let (fx1, fx2) := tupSplit fxu
        let (fy1, fy2) := tupSplit fyu
        goBlend u1 fm1 fx1 fy1 fun r1 => goBlend u2 fm2 fx2 fy2 fun r2 => cont (tupAppend r1 r2)
    goBlend (.pair t1 t2) fm fx fy fun fres => packLeavesToLegal target (.pair t1 t2) fres k

/-- Legalize `fcmp o t`. -/
def legalFCmpTree (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (o : FCmpOp) : (t : Ty) → Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t.mask) → Expr V L rs) → Expr V L rs
  | .bool, _, _, _ => .hlt
  | .bits _, _, _, _ => .hlt
  | .float f, (a, ()), (b, ()), k => .let_ (op2 (.fcmp o (.float f)) a b) fun (r, ()) =>
      k (.var r, ())
  | .pair t1 t2, xs, ys, k =>
    splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
    splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
    let rec goFCmp : (u : Ty) → Tup (Arg V) (target.leafTys u) →
        Tup (Arg V) (target.leafTys u) →
        (Tup (Arg V) (target.leafTys u.mask) → Expr V L rs) → Expr V L rs
      | .float f, (a, ()), (b, ()), cont =>
        .let_ (op2 (.fcmp o (.float f)) a b) fun (r, ()) => cont (.var r, ())
      | .pair u1 u2, fxu, fyu, cont =>
        let (fx1, fx2) := tupSplit fxu
        let (fy1, fy2) := tupSplit fyu
        goFCmp u1 fx1 fy1 fun m1 => goFCmp u2 fx2 fy2 fun m2 => cont (tupAppend m1 m2)
      | _, _, _, _ => .hlt
    goFCmp (.pair t1 t2) fx fy fun mres => packLeavesToLegal target (Ty.mask (.pair t1 t2)) mres k

/-- Scalarized 128-bit-lane fallback over word streams for shuffles across arbitrary `t`
with `t.size ≠ 0 ∧ t.size % 128 = 0`. -/
def legalSimdScalar128 (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (on128 : Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 →
             Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 →
      (Arg V i32 → Arg V i32 → Arg V i32 → Arg V i32 → Expr V L rs) → Expr V L rs)
    (t : Ty) (xs ys : Tup (Arg V) (target.legalTys t))
    (k : Tup (Arg V) (target.legalTys t) → Expr V L rs) : Expr V L rs :=
  splitLegalToLeaves target t xs fun fx =>
  splitLegalToLeaves target t ys fun fy =>
  packLeavesToWords64 target t fx fun wx =>
  packLeavesToWords64 target t fy fun wy =>
  let rec goWords : List (Arg V i64) → List (Arg V i64) → List (Arg V i64) → Expr V L rs
    | x0 :: x1 :: rxs, y0 :: y1 :: rys, acc =>
      words2ToDwords4 x0 x1 fun a0 a1 a2 a3 =>
      words2ToDwords4 y0 y1 fun b0 b1 b2 b3 =>
      on128 a0 a1 a2 a3 b0 b1 b2 b3 fun r0 r1 r2 r3 =>
      dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
      goWords rxs rys (acc ++ [w0, w1])
    | _, _, acc =>
      unpackWords64ToLeaves target acc 0 t fun fres =>
        packLeavesToLegal target t fres k
  goWords wx wy []

/-- Legalize `shufd t imm`. -/
def legalShufd (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) : (t : Ty) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | t, xs, k =>
    if t.size == 0 || t.size % 128 != 0 then .hlt
    else
      let on128 := fun a0 a1 a2 a3 _ _ _ _ cont =>
        let (r0, r1, r2, r3) := scalarShufd128 imm a0 a1 a2 a3
        cont r0 r1 r2 r3
      match t with
      | .pair a b =>
        if h : target.keepsPacked (.pair a b) then
          let xs' := packedToTup h xs
          if target.vecIntOpSupported (.shufd (.pair a b) imm) (.pair a b) false then
            .let_ (op1 (.shufd (.pair a b) imm) xs'.1) fun (r, ()) => k (tupToPacked h (.var r, ()))
          else legalSimdScalar128 target on128 (.pair a b) xs xs k
        else if a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0 then
          let hf := Bool.eq_false_iff.mpr h
          let (xa, xb) := tupSplit (splitToTup hf xs)
          legalShufd target imm a xa fun ra =>
          legalShufd target imm b xb fun rb =>
          k (tupToSplit hf (tupAppend ra rb))
        else legalSimdScalar128 target on128 (.pair a b) xs xs k
      | t' => legalSimdScalar128 target on128 t' xs xs k

/-- Legalize `blendw t imm`. -/
def legalBlendw (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) : (t : Ty) → Tup (Arg V) (target.legalTys t) →
      Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | t, xs, ys, k =>
    if t.size == 0 || t.size % 128 != 0 then .hlt
    else
      match t with
      | .pair a b =>
        if h : target.keepsPacked (.pair a b) then
          let xs' := packedToTup h xs
          let ys' := packedToTup h ys
          if target.vecIntOpSupported (.blendw (.pair a b) imm) (.pair a b) false then
            .let_ (op2 (.blendw (.pair a b) imm) xs'.1 ys'.1) fun (r, ()) =>
              k (tupToPacked h (.var r, ()))
          else legalSimdScalar128 target (scalarBlendw128 imm) (.pair a b) xs ys k
        else if a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0 then
          let hf := Bool.eq_false_iff.mpr h
          let (xa, xb) := tupSplit (splitToTup hf xs)
          let (ya, yb) := tupSplit (splitToTup hf ys)
          legalBlendw target imm a xa ya fun ra =>
          legalBlendw target imm b xb yb fun rb =>
          k (tupToSplit hf (tupAppend ra rb))
        else legalSimdScalar128 target (scalarBlendw128 imm) (.pair a b) xs ys k
      | t' => legalSimdScalar128 target (scalarBlendw128 imm) t' xs ys k

/-- Legalize `alignr t imm`. -/
def legalAlignr (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) : (t : Ty) → Tup (Arg V) (target.legalTys t) →
      Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | t, xs, ys, k =>
    if t.size == 0 || t.size % 128 != 0 then .hlt
    else
      match t with
      | .pair a b =>
        if h : target.keepsPacked (.pair a b) then
          let xs' := packedToTup h xs
          let ys' := packedToTup h ys
          if target.vecIntOpSupported (.alignr (.pair a b) imm) (.pair a b) false then
            .let_ (op2 (.alignr (.pair a b) imm) xs'.1 ys'.1) fun (r, ()) =>
              k (tupToPacked h (.var r, ()))
          else legalSimdScalar128 target (scalarAlignr128 imm) (.pair a b) xs ys k
        else if a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0 then
          let hf := Bool.eq_false_iff.mpr h
          let (xa, xb) := tupSplit (splitToTup hf xs)
          let (ya, yb) := tupSplit (splitToTup hf ys)
          legalAlignr target imm a xa ya fun ra =>
          legalAlignr target imm b xb yb fun rb =>
          k (tupToSplit hf (tupAppend ra rb))
        else legalSimdScalar128 target (scalarAlignr128 imm) (.pair a b) xs ys k
      | t' => legalSimdScalar128 target (scalarAlignr128 imm) t' xs ys k

/-- Legalize `shufb t`. -/
def legalShufb (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → Tup (Arg V) (target.legalTys t) → Tup (Arg V) (target.legalTys t) →
    (Tup (Arg V) (target.legalTys t) → Expr V L rs) → Expr V L rs
  | t, xs, ys, k =>
    if t.size == 0 || t.size % 128 != 0 then .hlt
    else
      match t with
      | .pair a b =>
        if h : target.keepsPacked (.pair a b) then
          let xs' := packedToTup h xs
          let ys' := packedToTup h ys
          if target.vecIntOpSupported (.shufb (.pair a b)) (.pair a b) false then
            .let_ (op2 (.shufb (.pair a b)) xs'.1 ys'.1) fun (r, ()) =>
              k (tupToPacked h (.var r, ()))
          else legalSimdScalar128 target scalarShufb128 (.pair a b) xs ys k
        else if a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0 then
          let hf := Bool.eq_false_iff.mpr h
          let (xa, xb) := tupSplit (splitToTup hf xs)
          let (ya, yb) := tupSplit (splitToTup hf ys)
          legalShufb target a xa ya fun ra =>
          legalShufb target b xb yb fun rb =>
          k (tupToSplit hf (tupAppend ra rb))
        else legalSimdScalar128 target scalarShufb128 (.pair a b) xs ys k
      | t' => legalSimdScalar128 target scalarShufb128 t' xs ys k

/-- Helper: legalize scalar float bitwise op (`and`/`or`/`xor`/`not`/`ternlog`). -/
def legalFloatBit2 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (target : LegalTarget) (mkOp : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    (mkFOp : (f : Fmt) → OpCode [.float f, .float f] [.float f])
    (f : Fmt) (x y : Arg V (.float f)) (cont : Arg V (.float f) → Expr V L rs) : Expr V L rs :=
  if target.scalarFloatBitwise then
    .let_ (op2 (mkFOp f) x y) fun (r, ()) => cont (.var r)
  else
    let fw := f.width
    .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) x) fun (bx, ()) =>
    .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) y) fun (by_, ()) =>
    .let_ (op2 (mkOp fw) (.var bx) (.var by_)) fun (br, ()) =>
    .let_ (op1 (.bitcast (.bits fw) (.float f) rfl) (.var br)) fun (r, ()) => cont (.var r)

/-- True iff `target` supports native packed 128-bit SHA-256 instruction `code`. -/
@[reducible] def LegalTarget.sha256Legal (target : LegalTarget) {as rs : List Ty}
    (code : OpCode as rs) : Bool :=
  target.keepsPacked v4i32 && target.vecIntOpSupported code v4i32 false

/-- Legalize a single `Op (LVar target V) rs'` into a continuation receiving `Tup (LVar target V)
  rs'`. -/
def legalOp (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {outRs : List Ty}
    {rs' : List Ty} (op : Op (LVar target V) rs')
    (k : Tup (LVar target V) rs' → Expr V L outRs) : Expr V L outRs :=
  let ⟨code, args⟩ := op
  match code with
  | .copy _ =>
    let (a, ()) := args
    k (legalArg target a, ())
  | .add t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .add (fun u unif => target.vecIntOpSupported (.add u) u unif)
        (fun x y cont => .let_ (op2 (.xor .bool) x y) fun (r, ()) => cont (.var r))
        (fun n x y cont => legalBitsArith target n (.add (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt) (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .sub t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .sub (fun u unif => target.vecIntOpSupported (.sub u) u unif)
        (fun x y cont => .let_ (op2 (.xor .bool) x y) fun (r, ()) => cont (.var r))
        (fun n x y cont => legalBitsArith target n (.sub (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt) (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .mul t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .mul (fun u unif => target.vecIntOpSupported (.mul u) u unif)
        (fun x y cont => .let_ (op2 (.and .bool) x y) fun (r, ()) => cont (.var r))
        (fun n x y cont => legalBitsArith target n (.mul (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt) (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .neg t =>
    let (a, ()) := args
    if t.hasFloat then .hlt
    else
      legalUnaryTree target .neg (fun u => target.vecIntOpSupported (.neg u) u false)
        (fun x cont => cont x)
        (fun n x cont =>
          let w := target.widenWidth n
          if n == 0 then cont (.imm 0#w)
          else .let_ (op1 (.neg (.bits w)) x) fun (r, ()) => emitMaskToN n w (.var r) cont)
        (fun _ _ _ => .hlt)
        t (legalArg target a) fun r => k (r, ())
  | .and t =>
    let (a, b, ()) := args
    legalBinTree target .and (fun u unif => target.vecIntOpSupported (.and u) u unif)
      (fun x y cont => .let_ (op2 (.and .bool) x y) fun (r, ()) => cont (.var r))
      (fun n x y cont => legalBitsArith target n (.and (.bits n)) x y cont)
      (legalFloatBit2 target (fun w => .and (.bits w)) (fun f => .and (.float f)))
      (fun _ _ => false)
      t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .or t =>
    let (a, b, ()) := args
    legalBinTree target .or (fun u unif => target.vecIntOpSupported (.or u) u unif)
      (fun x y cont => .let_ (op2 (.or .bool) x y) fun (r, ()) => cont (.var r))
      (fun n x y cont => legalBitsArith target n (.or (.bits n)) x y cont)
      (legalFloatBit2 target (fun w => .or (.bits w)) (fun f => .or (.float f)))
      (fun _ _ => false)
      t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .xor t =>
    let (a, b, ()) := args
    legalBinTree target .xor (fun u unif => target.vecIntOpSupported (.xor u) u unif)
      (fun x y cont => .let_ (op2 (.xor .bool) x y) fun (r, ()) => cont (.var r))
      (fun n x y cont => legalBitsArith target n (.xor (.bits n)) x y cont)
      (legalFloatBit2 target (fun w => .xor (.bits w)) (fun f => .xor (.float f)))
      (fun _ _ => false)
      t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .not t =>
    let (a, ()) := args
    legalUnaryTree target .not (fun u => target.vecIntOpSupported (.not u) u false)
      (fun x cont => .let_ (op1 (.not .bool) x) fun (r, ()) => cont (.var r))
      (fun n x cont =>
        let w := target.widenWidth n
        if n == 0 then cont (.imm 0#w)
        else if n == w then .let_ (op1 (.not (.bits w)) x) fun (r, ()) => cont (.var r)
        else .let_ (op1 (.not (.bits w)) x) fun (r, ()) => emitMaskToN n w (.var r) cont)
      (fun f x cont =>
        if target.scalarFloatBitwise then .let_ (op1 (.not (.float f)) x) fun (r, ()) =>
          cont (.var r)
        else
          let fw := f.width
          .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) x) fun (bx, ()) =>
          .let_ (op1 (.not (.bits fw)) (.var bx)) fun (br, ()) =>
          .let_ (op1 (.bitcast (.bits fw) (.float f) rfl) (.var br)) fun (r, ()) => cont (.var r))
      t (legalArg target a) fun r => k (r, ())
  | .ternlog t imm =>
    let (a, b, c, ()) := args
    legalTernaryTree target (fun u => .ternlog u imm)
      (fun u => target.vecIntOpSupported (.ternlog u imm) u false)
      (fun x y z cont => emitTernlogBool x y z imm cont)
      (fun n x y z cont =>
        let w := target.widenWidth n
        if n == 0 then cont (.imm 0#w)
        else if target.scalarTernlog then
          .let_ (op3 (.ternlog (.bits w) imm) x y z) fun (r, ()) => emitMaskToN n w (.var r) cont
        else emitTernlogBits w x y z imm fun r => emitMaskToN n w r cont)
      (fun f x y z cont =>
        if target.scalarFloatBitwise && target.scalarTernlog then
          .let_ (op3 (.ternlog (.float f) imm) x y z) fun (r, ()) => cont (.var r)
        else
          let fw := f.width
          .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) x) fun (bx, ()) =>
          .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) y) fun (by_, ()) =>
          .let_ (op1 (.bitcast (.float f) (.bits fw) rfl) z) fun (bz, ()) =>
          (if target.scalarTernlog then
             fun cc => .let_ (op3 (.ternlog (.bits fw) imm) (.var bx) (.var by_) (.var bz))
               fun (br, ()) => cc (.var br)
           else emitTernlogBits fw (.var bx) (.var by_) (.var bz) imm) fun br =>
          .let_ (op1 (.bitcast (.bits fw) (.float f) rfl) br) fun (r, ()) => cont (.var r))
      t (legalArg target a) (legalArg target b) (legalArg target c) fun r => k (r, ())
  | .shl t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .shl (fun u unif => target.vecIntOpSupported (.shl u) u unif)
        (fun x _ cont => cont x)
        (fun n x y cont => legalBitsArith target n (.shl (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt)
        (fun u rhs => match rhs with | .imm c => (uniformShiftLeaf? u c).isSome | _ => false)
        t (legalArg target a) (legalArg target b) (some b) fun r => k (r, ())
  | .lshr t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .lshr (fun u unif => target.vecIntOpSupported (.lshr u) u unif)
        (fun x _ cont => cont x)
        (fun n x y cont => legalBitsArith target n (.lshr (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt)
        (fun u rhs => match rhs with | .imm c => (uniformShiftLeaf? u c).isSome | _ => false)
        t (legalArg target a) (legalArg target b) (some b) fun r => k (r, ())
  | .ashr t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .ashr (fun u unif => target.vecIntOpSupported (.ashr u) u unif)
        (fun x _ cont => cont x)
        (fun n x y cont => legalBitsArith target n (.ashr (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt)
        (fun u rhs => match rhs with | .imm c => (uniformShiftLeaf? u c).isSome | _ => false)
        t (legalArg target a) (legalArg target b) (some b) fun r => k (r, ())
  | .rotl t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .rotl (fun u unif => target.vecIntOpSupported (.rotl u) u unif)
        (fun x _ cont => cont x)
        (fun n x y cont => legalBitsArith target n (.rotl (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt)
        (fun u rhs => match rhs with | .imm c => (uniformShiftLeaf? u c).isSome | _ => false)
        t (legalArg target a) (legalArg target b) (some b) fun r => k (r, ())
  | .rotr t =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalBinTree target .rotr (fun u unif => target.vecIntOpSupported (.rotr u) u unif)
        (fun x _ cont => cont x)
        (fun n x y cont => legalBitsArith target n (.rotr (.bits n)) x y cont)
        (fun _ _ _ _ => .hlt)
        (fun u rhs => match rhs with | .imm c => (uniformShiftLeaf? u c).isSome | _ => false)
        t (legalArg target a) (legalArg target b) (some b) fun r => k (r, ())
  | .fshl n =>
    let (a, b, c, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let (c', ()) := legalArg target c
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then
      .let_ (op3 (.fshl w) a' b' c') fun (r, ()) => k ((.var r, ()), ())
    else
      emitCountMod n w c' fun cm =>
      .let_ (op2 (.sub (.bits w)) (.imm (BitVec.ofNat w n)) cm) fun (nc, ()) =>
      .let_ (op2 (.shl (.bits w)) a' cm) fun (lo, ()) =>
      .let_ (op2 (.lshr (.bits w)) b' (.var nc)) fun (hi, ()) =>
      .let_ (op2 (.or (.bits w)) (.var lo) (.var hi)) fun (comb, ()) =>
      emitMaskToN n w (.var comb) fun r => k ((r, ()), ())
  | .fshr n =>
    let (a, b, c, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let (c', ()) := legalArg target c
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then
      .let_ (op3 (.fshr w) a' b' c') fun (r, ()) => k ((.var r, ()), ())
    else
      emitCountMod n w c' fun cm =>
      .let_ (op2 (.sub (.bits w)) (.imm (BitVec.ofNat w n)) cm) fun (nc, ()) =>
      .let_ (op2 (.lshr (.bits w)) b' cm) fun (lo, ()) =>
      .let_ (op2 (.shl (.bits w)) a' (.var nc)) fun (hi, ()) =>
      .let_ (op2 (.or (.bits w)) (.var lo) (.var hi)) fun (comb, ()) =>
      emitMaskToN n w (.var comb) fun r => k ((r, ()), ())
  | .bswap t =>
    let (a, ()) := args
    legalBswapTree target t (legalArg target a) fun r => k (r, ())
  | .clz n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then
      .let_ (op1 (.clz w) a') fun (r, ()) => k ((.var r, ()), ())
    else
      .let_ (op1 (.clz w) a') fun (cw, ()) =>
      .let_ (op2 (.sub (.bits w)) (.var cw) (.imm (BitVec.ofNat w (w - n)))) fun (r, ()) =>
      k ((.var r, ()), ())
  | .cls n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then
      .let_ (op1 (.cls w) a') fun (r, ()) => k ((.var r, ()), ())
    else
      emitSextToW n w a' fun sa =>
      .let_ (op1 (.cls w) sa) fun (cw, ()) =>
      .let_ (op2 (.sub (.bits w)) (.var cw) (.imm (BitVec.ofNat w (w - n)))) fun (r, ()) =>
      k ((.var r, ()), ())
  | .rbit n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then
      .let_ (op1 (.rbit w) a') fun (r, ()) => k ((.var r, ()), ())
    else
      .let_ (op1 (.rbit w) a') fun (rw, ()) =>
      .let_ (op2 (.lshr (.bits w)) (.var rw) (.imm (BitVec.ofNat w (w - n)))) fun (r, ()) =>
      k ((.var r, ()), ())
  | .ctz n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then
      .let_ (op1 (.ctz w) a') fun (r, ()) => k ((.var r, ()), ())
    else
      .let_ (op2 (.or (.bits w)) a' (.imm (BitVec.ofNat w (2 ^ n)))) fun (ao, ()) =>
      .let_ (op1 (.ctz w) (.var ao)) fun (r, ()) =>
      k ((.var r, ()), ())
  | .popcnt n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else .let_ (op1 (.popcnt w) a') fun (r, ()) => k ((.var r, ()), ())
  | .cmp o t m h =>
    let (a, b, ()) := args
    if t.hasFloat then .hlt
    else
      legalCmpTree target o t (legalArg target a) (legalArg target b) fun r =>
        k (by subst h; exact (r, ()))
  | .select t =>
    let (c, a, b, ()) := args
    let (c', ()) := legalArg target c
    legalSelectTree target c' t (legalArg target a) (legalArg target b) fun r => k (r, ())
  | .blend t m h =>
    let (c, a, b, ()) := args
    let c' : Tup (Arg V) (target.legalTys t.mask) := by subst h; exact legalArg target c
    legalBlendTree target t c' (legalArg target a) (legalArg target b) fun r => k (r, ())
  | .zext m n =>
    let (a, ()) := args
    if m > n then .hlt
    else
      let (a', ()) := legalArg target a
      let wm := target.widenWidth m
      let wn := target.widenWidth n
      if m == 0 then k ((.imm 0#wn, ()), ())
      else if h : wm = wn then k ((castArgBits h a', ()), ())
      else if wm < wn then .let_ (op1 (.zext wm wn) a') fun (r, ()) => k ((.var r, ()), ())
      else .hlt
  | .sext m n =>
    let (a, ()) := args
    if m > n then .hlt
    else
      let (a', ()) := legalArg target a
      let wm := target.widenWidth m
      let wn := target.widenWidth n
      if m == 0 then k ((.imm 0#wn, ()), ())
      else
        emitSextToW m wm a' fun sx =>
        let step2 (cont : Arg V (.bits wn) → Expr V L outRs) : Expr V L outRs :=
          if h : wm = wn then cont (castArgBits h sx)
          else if wm < wn then .let_ (op1 (.sext wm wn) sx) fun (r, ()) => cont (.var r)
          else .hlt
        step2 fun r => emitMaskToN n wn r fun rm => k ((rm, ()), ())
  | .trunc m n =>
    let (a, ()) := args
    if n > m then .hlt
    else
      let (a', ()) := legalArg target a
      let wm := target.widenWidth m
      let wn := target.widenWidth n
      if n == 0 then k ((.imm 0#wn, ()), ())
      else
        let step1 (cont : Arg V (.bits wn) → Expr V L outRs) : Expr V L outRs :=
          if h : wn = wm then cont (castArgBits h.symm a')
          else if wn < wm then .let_ (op1 (.trunc wm wn) a') fun (r, ()) => cont (.var r)
          else .hlt
        step1 fun r => emitMaskToN n wn r fun rm => k ((rm, ()), ())
  | .ofBool n =>
    let (c, ()) := args
    let (c', ()) := legalArg target c
    let wn := target.widenWidth n
    if n == 0 then k ((.imm 0#wn, ()), ())
    else .let_ (op1 (.ofBool wn) c') fun (r, ()) => k ((.var r, ()), ())
  | .addc n =>
    let (a, b, c, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let (c', ()) := legalArg target c
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), (c', ()), ())
    else if n == w then
      .let_ (op3 (.addc w) a' b' c') fun (s, co, ()) => k ((.var s, ()), (.var co, ()), ())
    else
      .let_ (op1 (.ofBool w) c') fun (cw, ()) =>
      .let_ (op2 (.add (.bits w)) a' b') fun (ab, ()) =>
      .let_ (op2 (.add (.bits w)) (.var ab) (.var cw)) fun (sw, ()) =>
      emitMaskToN n w (.var sw) fun s =>
      .let_ (op2 (.ule (.bits w)) (.imm ((1#w) <<< n)) (.var sw)) fun (co, ()) =>
      k ((s, ()), (.var co, ()), ())
  | .subb n =>
    let (a, b, c, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let (c', ()) := legalArg target c
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), (c', ()), ())
    else if n == w then
      .let_ (op3 (.subb w) a' b' c') fun (d, bo, ()) => k ((.var d, ()), (.var bo, ()), ())
    else
      .let_ (op3 (.subb w) a' b' c') fun (dw, bo, ()) =>
      emitMaskToN n w (.var dw) fun d =>
      k ((d, ()), (.var bo, ()), ())
  | .umulw n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), (.imm 0#w, ()), ())
    else if n == w then
      .let_ (op2 (.umulw w) a' b') fun (lo, hi, ()) => k ((.var lo, ()), (.var hi, ()), ())
    else
      .let_ (op2 (.umulw w) a' b') fun (loW, hiW, ()) =>
      emitMaskToN n w (.var loW) fun lo =>
      .let_ (op2 (.lshr (.bits w)) (.var loW) (.imm (BitVec.ofNat w n))) fun (p1, ()) =>
      .let_ (op2 (.shl (.bits w)) (.var hiW) (.imm (BitVec.ofNat w (w - n)))) fun (p2, ()) =>
      .let_ (op2 (.or (.bits w)) (.var p1) (.var p2)) fun (hiComb, ()) =>
      emitMaskToN n w (.var hiComb) fun hi =>
      k ((lo, ()), (hi, ()), ())
  | .smulw n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), (.imm 0#w, ()), ())
    else if n == w then
      .let_ (op2 (.smulw w) a' b') fun (lo, hi, ()) => k ((.var lo, ()), (.var hi, ()), ())
    else
      emitSextToW n w a' fun sa =>
      emitSextToW n w b' fun sb =>
      .let_ (op2 (.smulw w) sa sb) fun (loW, hiW, ()) =>
      emitMaskToN n w (.var loW) fun lo =>
      .let_ (op2 (.lshr (.bits w)) (.var loW) (.imm (BitVec.ofNat w n))) fun (p1, ()) =>
      .let_ (op2 (.shl (.bits w)) (.var hiW) (.imm (BitVec.ofNat w (w - n)))) fun (p2, ()) =>
      .let_ (op2 (.or (.bits w)) (.var p1) (.var p2)) fun (hiComb, ()) =>
      emitMaskToN n w (.var hiComb) fun hi =>
      k ((lo, ()), (hi, ()), ())
  | .udiv n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then .hlt
    else .let_ (op2 (.udiv w) a' b') fun (r, ()) => k ((.var r, ()), ())
  | .sdiv n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then .hlt
    else if n == w then .let_ (op2 (.sdiv w) a' b') fun (r, ()) => k ((.var r, ()), ())
    else
      emitSextToW n w a' fun sa =>
      emitSextToW n w b' fun sb =>
      .let_ (op2 (.sdiv w) sa sb) fun (r, ()) =>
      emitMaskToN n w (.var r) fun rm => k ((rm, ()), ())
  | .urem n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then .hlt
    else .let_ (op2 (.urem w) a' b') fun (r, ()) => k ((.var r, ()), ())
  | .srem n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then .hlt
    else if n == w then .let_ (op2 (.srem w) a' b') fun (r, ()) => k ((.var r, ()), ())
    else
      emitSextToW n w a' fun sa =>
      emitSextToW n w b' fun sb =>
      .let_ (op2 (.srem w) sa sb) fun (r, ()) =>
      emitMaskToN n w (.var r) fun rm => k ((rm, ()), ())
  | .udiv0 n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else .let_ (op2 (.udiv0 w) a' b') fun (r, ()) => k ((.var r, ()), ())
  | .sdiv0 n =>
    let (a, b, ()) := args
    let (a', ()) := legalArg target a
    let (b', ()) := legalArg target b
    let w := target.widenWidth n
    if n == 0 then k ((.imm 0#w, ()), ())
    else if n == w then .let_ (op2 (.sdiv0 w) a' b') fun (r, ()) => k ((.var r, ()), ())
    else
      emitSextToW n w a' fun sa =>
      emitSextToW n w b' fun sb =>
      .let_ (op2 (.sdiv0 w) sa sb) fun (r, ()) =>
      emitMaskToN n w (.var r) fun rm => k ((rm, ()), ())
  | .mkpair a b =>
    let (va, vb, ()) := args
    let la := legalArg target va
    let lb := legalArg target vb
    if h : target.keepsPacked (.pair a b) then
      packFromLegal target a la fun pa =>
      packFromLegal target b lb fun pb =>
      .let_ (op2 (.mkpair a b) pa pb) fun (p, ()) =>
        k (tupToPacked h (.var p, ()), ())
    else
      let hf := Bool.eq_false_iff.mpr h
      k (tupToSplit hf (tupAppend la lb), ())
  | .unpair a b =>
    let (vp, ()) := args
    let lp := legalArg target vp
    if h : target.keepsPacked (.pair a b) then
      match (packedToTup h lp).1 with
      | .imm c => k (encodeImm target a c.1, encodeImm target b c.2, ())
      | .var v =>
        .let_ (op1 (.unpair a b) (.var v)) fun (va, vb, ()) =>
        unpackToLegal target a (.var va) fun la =>
        unpackToLegal target b (.var vb) fun lb =>
          k (la, lb, ())
    else
      let hf := Bool.eq_false_iff.mpr h
      let (la, lb) := tupSplit (splitToTup hf lp)
      k (la, lb, ())
  | .bitcast t u h =>
    let (a, ()) := args
    let la := legalArg target a
    if heq : t = u then
      k (heq ▸ la, ())
    else
      let isNativeTy (x : Ty) : Bool :=
        target.isLegalTy x && match x with | .bits n => target.widenWidth n == n | _ => true
      if ht : isNativeTy t then
        if hu : isNativeTy u then
          have hlt : target.legalTys t = [t] := by
            cases t with
            | bool => rfl
            | bits n =>
              have hw : target.widenWidth n = n := by
                simpa [isNativeTy] using ((Bool.and_eq_true _ _).mp ht).2
              simp [LegalTarget.legalTys, hw]
            | float _ => rfl
            | pair _ _ =>
                simp [isNativeTy, LegalTarget.isLegalTy] at ht; simp [LegalTarget.legalTys, ht]
          have hlu : target.legalTys u = [u] := by
            cases u with
            | bool => rfl
            | bits n =>
              have hw : target.widenWidth n = n := by
                simpa [isNativeTy] using ((Bool.and_eq_true _ _).mp hu).2
              simp [LegalTarget.legalTys, hw]
            | float _ => rfl
            | pair _ _ =>
                simp [isNativeTy, LegalTarget.isLegalTy] at hu; simp [LegalTarget.legalTys, hu]
          let x' : Arg V t := (cast (by rw [hlt]) la : Tup (Arg V) [t]).1
          .let_ (op1 (.bitcast t u h) x') fun (r, ()) =>
            k (cast (by simp [LVar, hlu]) (show Tup (Arg V) [u] from (.var r, ())), ())
        else
          splitLegalToLeaves target t la fun fx =>
          packLeavesToWords64 target t fx fun words =>
          unpackWords64ToLeaves target words 0 u fun fu =>
          packLeavesToLegal target u fu fun res => k (res, ())
      else
        splitLegalToLeaves target t la fun fx =>
        packLeavesToWords64 target t fx fun words =>
        unpackWords64ToLeaves target words 0 u fun fu =>
        packLeavesToLegal target u fu fun res => k (res, ())
  | .shufd t imm =>
    let (a, ()) := args
    legalShufd target imm t (legalArg target a) fun r => k (r, ())
  | .shufb t =>
    let (a, m, ()) := args
    legalShufb target t (legalArg target a) (legalArg target m) fun r => k (r, ())
  | .alignr t imm =>
    let (hi, lo, ()) := args
    legalAlignr target imm t (legalArg target hi) (legalArg target lo) fun r => k (r, ())
  | .blendw t imm =>
    let (a, b, ()) := args
    legalBlendw target imm t (legalArg target a) (legalArg target b) fun r => k (r, ())
  | .sha256rnds2 =>
    let (cdgh, abef, wk, ()) := args
    if hk : target.sha256Legal .sha256rnds2 then
      have hkp : target.keepsPacked v4i32 = true := (Bool.and_eq_true _ _).mp hk |>.1
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      let c' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target cdgh) : Tup (Arg V) [v4i32]).1
      let a' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target abef) : Tup (Arg V) [v4i32]).1
      let w' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target wk) : Tup (Arg V) [v4i32]).1
      .let_ (op3 .sha256rnds2 c' a' w') fun (r, ()) =>
        k (cast (by simp [LVar, hl]) (show Tup (Arg V) [v4i32] from (.var r, ())), ())
    else
      splitLegalToLeaves target v4i32 (legalArg target cdgh) fun fc =>
      splitLegalToLeaves target v4i32 (legalArg target abef) fun fa =>
      splitLegalToLeaves target v4i32 (legalArg target wk) fun fw =>
      packLeavesToWords64 target v4i32 fc fun wc =>
      packLeavesToWords64 target v4i32 fa fun wa =>
      packLeavesToWords64 target v4i32 fw fun ww =>
      words2ToDwords4 (wc.getD 0 (.imm 0#64)) (wc.getD 1 (.imm 0#64)) fun cd0 cd1 cd2 cd3 =>
      words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun ab0 ab1 ab2 ab3 =>
      words2ToDwords4 (ww.getD 0 (.imm 0#64)) (ww.getD 1 (.imm 0#64)) fun wk0 wk1 wk2 wk3 =>
      scalarSha256rnds2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 fun r0 r1 r2 r3 =>
      dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
      unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
      packLeavesToLegal target v4i32 fres fun res => k (res, ())
  | .sha256msg1 =>
    let (w0123, w4, ()) := args
    if hk : target.sha256Legal .sha256msg1 then
      have hkp : target.keepsPacked v4i32 = true := (Bool.and_eq_true _ _).mp hk |>.1
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      let a' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target w0123) : Tup (Arg V) [v4i32]).1
      let b' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target w4) : Tup (Arg V) [v4i32]).1
      .let_ (op2 .sha256msg1 a' b') fun (r, ()) =>
        k (cast (by simp [LVar, hl]) (show Tup (Arg V) [v4i32] from (.var r, ())), ())
    else
      splitLegalToLeaves target v4i32 (legalArg target w0123) fun fa =>
      splitLegalToLeaves target v4i32 (legalArg target w4) fun fb =>
      packLeavesToWords64 target v4i32 fa fun wa =>
      packLeavesToWords64 target v4i32 fb fun wb =>
      words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun a0 a1 a2 a3 =>
      words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun b0 b1 b2 b3 =>
      scalarSha256msg1 a0 a1 a2 a3 b0 b1 b2 b3 fun r0 r1 r2 r3 =>
      dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
      unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
      packLeavesToLegal target v4i32 fres fun res => k (res, ())
  | .sha256msg2 =>
    let (sums, w, ()) := args
    if hk : target.sha256Legal .sha256msg2 then
      have hkp : target.keepsPacked v4i32 = true := (Bool.and_eq_true _ _).mp hk |>.1
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      let a' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target sums) : Tup (Arg V) [v4i32]).1
      let b' : Arg V v4i32 := (cast (by rw [hl]) (legalArg target w) : Tup (Arg V) [v4i32]).1
      .let_ (op2 .sha256msg2 a' b') fun (r, ()) =>
        k (cast (by simp [LVar, hl]) (show Tup (Arg V) [v4i32] from (.var r, ())), ())
    else
      splitLegalToLeaves target v4i32 (legalArg target sums) fun fa =>
      splitLegalToLeaves target v4i32 (legalArg target w) fun fb =>
      packLeavesToWords64 target v4i32 fa fun wa =>
      packLeavesToWords64 target v4i32 fb fun wb =>
      words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun s0 s1 s2 s3 =>
      words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun w0 w1 w2 w3 =>
      scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 fun r0 r1 r2 r3 =>
      dwords4ToWords2 r0 r1 r2 r3 fun wr0 wr1 =>
      unpackWords64ToLeaves target [wr0, wr1] 0 v4i32 fun fres =>
      packLeavesToLegal target v4i32 fres fun res => k (res, ())
  | .fadd t =>
    let (a, b, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalBinTree target .fadd (fun u _ => target.vecFloatOpSupported (.fadd u) u)
        (fun _ _ _ => .hlt) (fun _ _ _ _ => .hlt)
        (fun f x y cont => .let_ (op2 (.fadd (.float f)) x y) fun (r, ()) => cont (.var r))
        (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .fsub t =>
    let (a, b, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalBinTree target .fsub (fun u _ => target.vecFloatOpSupported (.fsub u) u)
        (fun _ _ _ => .hlt) (fun _ _ _ _ => .hlt)
        (fun f x y cont => .let_ (op2 (.fsub (.float f)) x y) fun (r, ()) => cont (.var r))
        (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .fmul t =>
    let (a, b, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalBinTree target .fmul (fun u _ => target.vecFloatOpSupported (.fmul u) u)
        (fun _ _ _ => .hlt) (fun _ _ _ _ => .hlt)
        (fun f x y cont => .let_ (op2 (.fmul (.float f)) x y) fun (r, ()) => cont (.var r))
        (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .fdiv t =>
    let (a, b, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalBinTree target .fdiv (fun u _ => target.vecFloatOpSupported (.fdiv u) u)
        (fun _ _ _ => .hlt) (fun _ _ _ _ => .hlt)
        (fun f x y cont => .let_ (op2 (.fdiv (.float f)) x y) fun (r, ()) => cont (.var r))
        (fun _ _ => false)
        t (legalArg target a) (legalArg target b) none fun r => k (r, ())
  | .ffma t =>
    let (a, b, c, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalTernaryTree target .ffma (fun u => target.vecFloatOpSupported (.ffma u) u)
        (fun _ _ _ _ => .hlt) (fun _ _ _ _ _ => .hlt)
        (fun f x y z cont => .let_ (op3 (.ffma (.float f)) x y z) fun (r, ()) => cont (.var r))
        t (legalArg target a) (legalArg target b) (legalArg target c) fun r => k (r, ())
  | .fsqrt t =>
    let (a, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalUnaryTree target .fsqrt (fun u => target.vecFloatOpSupported (.fsqrt u) u)
        (fun _ _ => .hlt) (fun _ _ _ => .hlt)
        (fun f x cont => .let_ (op1 (.fsqrt (.float f)) x) fun (r, ()) => cont (.var r))
        t (legalArg target a) fun r => k (r, ())
  | .fneg t =>
    let (a, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalUnaryTree target .fneg (fun u => target.vecFloatOpSupported (.fneg u) u)
        (fun _ _ => .hlt) (fun _ _ _ => .hlt)
        (fun f x cont => .let_ (op1 (.fneg (.float f)) x) fun (r, ()) => cont (.var r))
        t (legalArg target a) fun r => k (r, ())
  | .fabs t =>
    let (a, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalUnaryTree target .fabs (fun u => target.vecFloatOpSupported (.fabs u) u)
        (fun _ _ => .hlt) (fun _ _ _ => .hlt)
        (fun f x cont => .let_ (op1 (.fabs (.float f)) x) fun (r, ()) => cont (.var r))
        t (legalArg target a) fun r => k (r, ())
  | .fcmp o t m h =>
    let (a, b, ()) := args
    if !t.isFloatTree then .hlt
    else
      legalFCmpTree target o t (legalArg target a) (legalArg target b) fun r =>
        k (by subst h; exact (r, ()))
  | .fptoui f n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then
      .let_ (op1 (.fptoui f w) a') fun (_, ()) => k ((.imm 0#w, ()), ())
    else
      .let_ (op1 (.fptoui f w) a') fun (r, ()) => k ((.var r, ()), ())
  | .fptosi f n =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then .hlt
    else if n == w then
      .let_ (op1 (.fptosi f w) a') fun (r, ()) => k ((.var r, ()), ())
    else
      .let_ (op1 (.fptosi f w) a') fun (r, ()) =>
      emitMaskToN n w (.var r) fun rm => k ((rm, ()), ())
  | .uitofp n f =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then
      .let_ (op1 (.uitofp w f) (.imm 0#w)) fun (r, ()) => k ((.var r, ()), ())
    else
      .let_ (op1 (.uitofp w f) a') fun (r, ()) => k ((.var r, ()), ())
  | .sitofp n f =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    let w := target.widenWidth n
    if n == 0 then
      .let_ (op1 (.sitofp w f) (.imm 0#w)) fun (r, ()) => k ((.var r, ()), ())
    else
      emitSextToW n w a' fun sa =>
      .let_ (op1 (.sitofp w f) sa) fun (r, ()) => k ((.var r, ()), ())
  | .fcvt f g =>
    let (a, ()) := args
    let (a', ()) := legalArg target a
    .let_ (op1 (.fcvt f g) a') fun (r, ()) => k ((.var r, ()), ())

end LeanQbe.T
