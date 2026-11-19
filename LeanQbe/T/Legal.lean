module

public import LeanQbe.T.LegalTrees

/-!
# Target-parameterized IR legalisation (`T5`, `G13`, Part 3: `Func.legal`, `isLegal`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Legalize `load t ptr k`. -/
def legalLoad (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (t : Ty) (ptr : Arg V i64) (k : LVar target V t → Expr V L rs) : Expr V L rs :=
  match t with
  | .bool => .load .bool ptr fun v => k (.var v, ())
  | .bits n =>
    let w := target.widenWidth n
    if n == w then .load (.bits w) ptr fun v => k (.var v, ())
    else emitLoadBits target.bitWidths n w ptr fun r => k (r, ())
  | .float f => .load (.float f) ptr fun v => k (.var v, ())
  | .pair a b =>
    if h : target.keepsPacked (.pair a b) then
      .load (.pair a b) ptr fun v =>
        k (tupToPacked h (.var v, ()))
    else if (Ty.pair a b).isByteAlignedStruct then
      let hf := Bool.eq_false_iff.mpr h
      legalLoad target a ptr fun la =>
      (if a.bytes == 0 then fun cont => cont ptr
       else fun cont => .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 a.bytes))) fun (p2, ()) =>
         cont (.var p2)) fun ptr2 =>
        legalLoad target b ptr2 fun lb =>
          k (tupToSplit hf (tupAppend la lb))
    else
      let bCount := (Ty.pair a b).bytes
      if bCount == 0 then
        unpackWords64ToLeaves target [] 0 (.pair a b) fun fres =>
          packLeavesToLegal target (.pair a b) fres k
      else
        loadByteChunksToWords64 ptr 0 (chunkBytes target.bitWidths bCount) [] (.imm 0#64) 0
          fun words =>
          unpackWords64ToLeaves target words 0 (.pair a b) fun fres =>
            packLeavesToLegal target (.pair a b) fres k

/-- Legalize `store t v ptr k`. -/
def legalStore (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (t : Ty) → LVar target V t → Arg V i64 → Expr V L rs → Expr V L rs
  | .bool, (v, ()), ptr, k => .store (t := .bool) v ptr k
  | .bits n, (v, ()), ptr, k =>
    let w := target.widenWidth n
    if n == w then .store (t := .bits w) v ptr k
    else emitStoreBits target.bitWidths n w v ptr k
  | .float f, (v, ()), ptr, k => .store (t := .float f) v ptr k
  | .pair a b, xs, ptr, k =>
    if h : target.keepsPacked (.pair a b) then
      let xs' := packedToTup h xs
      .store (t := .pair a b) xs'.1 ptr k
    else if (Ty.pair a b).isByteAlignedStruct then
      let hf := Bool.eq_false_iff.mpr h
      let (la, lb) := tupSplit (splitToTup hf xs)
      legalStore target a la ptr <|
        if a.bytes == 0 then legalStore target b lb ptr k
        else .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 a.bytes))) fun (p2, ()) =>
          legalStore target b lb (.var p2) k
    else
      let bCount := (Ty.pair a b).bytes
      if bCount == 0 then k
      else
        splitLegalToLeaves target (.pair a b) xs fun fx =>
        packLeavesToWords64 target (.pair a b) fx fun words =>
          storeByteChunksFromWords64 words ptr 0 (chunkBytes target.bitWidths bCount) k

mutual
/-- Legalize an expression `Expr (LVar target V) (LLab target L) rs` into `Expr V L (target.legalSig
  rs)`. -/
def legalExpr (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (LVar target V) (LLab target L) rs → Expr V L (target.legalSig rs)
  | .let_ op k => legalOp target op fun res => legalExpr target (k res)
  | .load t a k =>
    if h64 : target.widenWidth 64 = 64 then
      legalLoad target t (castArgBits h64 (legalArg target a).1) fun res => legalExpr target (k res)
    else .hlt
  | .store (t := t) v a k =>
    if h64 : target.widenWidth 64 = 64 then
      legalStore target t (legalArg target v) (castArgBits h64 (legalArg target a).1)
        (legalExpr target k)
    else .hlt
  | .call f (as := as) (bs := bs) args k =>
    .call f (as := target.legalSig as) (bs := target.legalSig bs) (joinArgs target args) fun res =>
      legalExpr target (k (splitParams target bs res))
  | .jnz c t e => .jnz (legalArg target c).1 (legalExpr target t) (legalExpr target e)
  | .jump j args => .jump j (joinArgs target args)
  | .ret vs => .ret (joinArgs target vs)
  | .exit f (as := as) args => .exit f (as := target.legalSig as) (joinArgs target args)
  | .hlt => .hlt
  | .group (sig := sig) bodies k =>
    .group (sig := sig.map target.legalSig)
      (fun Js => legalBlocks target (bodies (tupLiftMap target.legalSig L Js)))
      (fun Js => legalExpr target (k (tupLiftMap target.legalSig L Js)))

/-- Legalize a block list `Blocks`. -/
def legalBlocks (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (LVar target V) (LLab target L) rs sig →
    Blocks V L (target.legalSig rs) (sig.map target.legalSig)
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => legalExpr target (b (splitParams target ts xs))) (legalBlocks target bs)
end

/-- Legalize a closed typed function `Func as rs` for `target`. -/
def Func.legal (target : LegalTarget) {as rs : List Ty} (f : Func as rs) :
    Func (target.legalSig as) (target.legalSig rs) :=
  fun V L xs => legalExpr target (f (LVar target V) (LLab target L) (splitParams target as xs))

/-- Legalize a named typed function `Fn`. -/
def Fn.legal (target : LegalTarget) (fn : Fn) : Fn :=
  ⟨fn.name, target.legalSig fn.as, target.legalSig fn.rs, Func.legal target fn.body⟩

/-! ## Decidable `Legal` predicate and `supportsSource` check -/

/-- Variable kind tracked during `TFlat.isLegal`: normal legal values vs transient pack/unpack
bridges immediately around packed vector boundaries. -/
inductive VarKind
  | normal
  | unpackedBridge
  | packedBridge
  deriving DecidableEq, Repr

/-- Check variable index `idx` in `Γ` at expected type `t` and allowed kind predicate. -/
def checkVarKind (Γ : List (Ty × VarKind)) (t : Ty) (allowed : VarKind → Bool) (idx : Nat) : Bool :=
  match listGet? Γ idx with
  | some (t', k) =>
    (match tyDecEq t' t with | isTrue _ => true | isFalse _ => false) && allowed k
  | none => false

/-- Check a normal operand in `TFlat.isLegal`. -/
def checkLegalArg (Γ : List (Ty × VarKind)) (t : Ty) : Arg K t → Bool
  | .var idx => checkVarKind Γ t (· == .normal) idx
  | .imm _ => true

/-- Check a tuple of normal operands in `TFlat.isLegal`. -/
def checkLegalArgs (Γ : List (Ty × VarKind)) : {ts : List Ty} → Tup (Arg K) ts → Bool
  | [], () => true
  | t :: _, (a, as) => checkLegalArg Γ t a && checkLegalArgs Γ as

/-- Push a signature of normal legal variables onto `Γ`. -/
def pushNormal (ts : List Ty) (Γ : List (Ty × VarKind)) : List (Ty × VarKind) :=
  pushTypes (ts.map (·, VarKind.normal)) Γ

/-- Check whether `OpCode` (other than `mkpair`/`unpair`, handled by `VarKind` rules) is legal
under `target`, given whether the right-hand operand of a shift/rotate is a uniform immediate. -/
def LegalTarget.isLegalOp (target : LegalTarget) :
    {as rs : List Ty} → OpCode as rs → (uniformImmRhs : Bool) → Bool
  | _, _, .copy t, _ => target.isLegalTy t
  | _, _, .add t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.add t) (.pair a b) unif
    | _ => false
  | _, _, .sub t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.sub t) (.pair a b) unif
    | _ => false
  | _, _, .mul t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.mul t) (.pair a b) unif
    | _ => false
  | _, _, .neg t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.neg t) (.pair a b) unif
    | _ => false
  | _, _, .and t, unif =>
    match t with
    | .bool => true
    | .bits n => n ∈ target.bitWidths
    | .float f => target.scalarFloatBitwise && f ∈ target.floatFmts
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.and t) (.pair a b) unif
  | _, _, .or t, unif =>
    match t with
    | .bool => true
    | .bits n => n ∈ target.bitWidths
    | .float f => target.scalarFloatBitwise && f ∈ target.floatFmts
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.or t) (.pair a b) unif
  | _, _, .xor t, unif =>
    match t with
    | .bool => true
    | .bits n => n ∈ target.bitWidths
    | .float f => target.scalarFloatBitwise && f ∈ target.floatFmts
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.xor t) (.pair a b) unif
  | _, _, .not t, unif =>
    match t with
    | .bool => true
    | .bits n => n ∈ target.bitWidths
    | .float f => target.scalarFloatBitwise && f ∈ target.floatFmts
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.not t) (.pair a b) unif
  | _, _, .ternlog t imm, unif =>
    match t with
    | .bits n => target.scalarTernlog && n ∈ target.bitWidths
    | .float f => target.scalarTernlog && target.scalarFloatBitwise && f ∈ target.floatFmts
    | .pair a b =>
      target.keepsPacked (.pair a b) && target.vecIntOpSupported (.ternlog t imm) (.pair a b) unif
    | .bool => false
  | _, _, .shl t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.shl t) (.pair a b) unif
    | _ => false
  | _, _, .lshr t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.lshr t) (.pair a b) unif
    | _ => false
  | _, _, .ashr t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.ashr t) (.pair a b) unif
    | _ => false
  | _, _, .rotl t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.rotl t) (.pair a b) unif
    | _ => false
  | _, _, .rotr t, unif =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecIntOpSupported (.rotr t) (.pair a b) unif
    | _ => false
  | _, _, .fshl n, _ | _, _, .fshr n, _
  | _, _, .clz n, _ | _, _, .cls n, _ | _, _, .rbit n, _ | _, _, .ctz n, _ | _, _, .popcnt n, _
  | _, _, .addc n, _ | _, _, .subb n, _ | _, _, .umulw n, _ | _, _, .smulw n, _
  | _, _, .udiv n, _ | _, _, .sdiv n, _ | _, _, .urem n, _ | _, _, .srem n, _
  | _, _, .udiv0 n, _ | _, _, .sdiv0 n, _
  | _, _, .ofBool n, _ => n ∈ target.bitWidths && 0 < n
  | _, _, .bswap t, _ =>
    match t with
    | .bits n => n ∈ target.bitWidths && n % 8 == 0 && n > 8
    | _ => false
  | _, _, .cmp _ t _ _, _ =>
    match t with
    | .bits n => n ∈ target.bitWidths && 0 < n
    | .bool => target.boolCmp
    | _ => false
  | _, _, .select t, _ =>
    match t with
    | .bits n => n ∈ target.bitWidths
    | .float f => f ∈ target.floatFmts
    | .bool => target.boolSelect
    | .pair _ _ => false
  | _, _, .blend _ _ _, _ => false
  | _, _, .zext m n, _ | _, _, .sext m n, _ =>
    m ∈ target.bitWidths && n ∈ target.bitWidths && m < n
  | _, _, .trunc m n, _ =>
    m ∈ target.bitWidths && n ∈ target.bitWidths && n < m
  | _, _, .mkpair _ _, _ | _, _, .unpair _ _, _ => false
  | _, _, .bitcast t u _, _ => target.isLegalTy t && target.isLegalTy u && t != u
  | _, _, .shufd t imm, _ =>
    target.keepsPacked t && t.size != 0 && t.size % 128 == 0 &&
      target.vecIntOpSupported (.shufd t imm) t false
  | _, _, .shufb t, _ =>
    target.keepsPacked t && t.size != 0 && t.size % 128 == 0 &&
      target.vecIntOpSupported (.shufb t) t false
  | _, _, .alignr t imm, _ =>
    target.keepsPacked t && t.size != 0 && t.size % 128 == 0 &&
      target.vecIntOpSupported (.alignr t imm) t false
  | _, _, .blendw t imm, _ =>
    target.keepsPacked t && t.size != 0 && t.size % 128 == 0 &&
      target.vecIntOpSupported (.blendw t imm) t false
  | _, _, .sha256rnds2, _ => target.sha256Legal .sha256rnds2
  | _, _, .sha256msg1, _ => target.sha256Legal .sha256msg1
  | _, _, .sha256msg2, _ => target.sha256Legal .sha256msg2
  | _, _, .fadd t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fadd t) (.pair a b)
    | _ => false
  | _, _, .fsub t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fsub t) (.pair a b)
    | _ => false
  | _, _, .fmul t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fmul t) (.pair a b)
    | _ => false
  | _, _, .fdiv t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fdiv t) (.pair a b)
    | _ => false
  | _, _, .ffma t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.ffma t) (.pair a b)
    | _ => false
  | _, _, .fsqrt t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fsqrt t) (.pair a b)
    | _ => false
  | _, _, .fneg t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fneg t) (.pair a b)
    | _ => false
  | _, _, .fabs t, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | .pair a b =>
        target.keepsPacked (.pair a b) && target.vecFloatOpSupported (.fabs t) (.pair a b)
    | _ => false
  | _, _, .fcmp _ t _ _, _ =>
    match t with
    | .float f => f ∈ target.floatFmts
    | _ => false
  | _, _, .fptoui f n, _ | _, _, .fptosi f n, _ | _, _, .uitofp n f, _ | _, _, .sitofp n f, _ =>
    f ∈ target.floatFmts && n ∈ target.bitWidths
  | _, _, .fcvt f g, _ => f ∈ target.floatFmts && g ∈ target.floatFmts

/-- True iff `code` is a shift/rotate whose right-hand operand in `args` is a uniform `.imm`. -/
def isUniformImmShift : {as rs : List Ty} → OpCode as rs → Tup (Arg K) as → Bool
  | _, _, .shl t, (_, .imm c, ())
  | _, _, .lshr t, (_, .imm c, ())
  | _, _, .ashr t, (_, .imm c, ())
  | _, _, .rotl t, (_, .imm c, ())
  | _, _, .rotr t, (_, .imm c, ()) => (uniformShiftLeaf? t c).isSome
  | _, _, _, _ => false

mutual
/-- Total computable legality checker for `TFlat rs` under value context `Γ` and label context `Δ`.
  -/
def TFlat.isLegal (target : LegalTarget) {rs : List Ty}
    (Γ : List (Ty × VarKind)) (Δ : List (List Ty)) : TFlat rs → Bool
  | .let_ (ts := ts) op k =>
    let ⟨code, args⟩ := op
    match code with
    | .unpair a b =>
      let (p, ()) := args
      target.allowPackBridge && target.hasLegalLeaves (.pair a b) &&
      (match p with
       | .var idx =>
         checkVarKind Γ (.pair a b)
           (fun vk => (vk == .normal && target.isLegalTy (.pair a b)) || vk == .unpackedBridge) idx
       | .imm _ => false) &&
      let ka := if target.isLegalTy a then VarKind.normal else .unpackedBridge
      let kb := if target.isLegalTy b then VarKind.normal else .unpackedBridge
      k.isLegal target (pushTypes [(a, ka), (b, kb)] Γ) Δ
    | .mkpair a b =>
      let (va, vb, ()) := args
      let chkIn (u : Ty) : Arg K u → Bool
        | .var idx =>
          checkVarKind Γ u
            (fun vk => (vk == .normal && target.isLegalTy u) || vk == .packedBridge) idx
        | .imm _ => target.isLegalTy u
      target.allowPackBridge && target.hasLegalLeaves (.pair a b) &&
      chkIn a va && chkIn b vb &&
      let kres := if target.isLegalTy (.pair a b) then VarKind.normal else .packedBridge
      k.isLegal target ((.pair a b, kres) :: Γ) Δ
    | _ =>
      target.isLegalOp code (isUniformImmShift op.code op.args) && target.isLegalSig ts &&
        checkLegalArgs Γ args && k.isLegal target (pushNormal ts Γ) Δ
  | .load t a k =>
    target.isLegalTy t && checkLegalArg Γ i64 a && k.isLegal target ((t, .normal) :: Γ) Δ
  | .store (t := t) v a k =>
    target.isLegalTy t && checkLegalArg Γ t v && checkLegalArg Γ i64 a && k.isLegal target Γ Δ
  | .call _ (as := as) bs args k =>
    target.isLegalSig as && target.isLegalSig bs && checkLegalArgs Γ args &&
      k.isLegal target (pushNormal bs Γ) Δ
  | .jnz c t e =>
    checkLegalArg Γ .bool c && t.isLegal target Γ Δ && e.isLegal target Γ Δ
  | .jump (ts := ts) j args =>
    target.isLegalSig ts &&
      (match listGet? Δ j with
       | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
       | none => false) &&
      checkLegalArgs Γ args
  | .ret vs => target.isLegalSig rs && checkLegalArgs Γ vs
  | .exit _ (as := as) args => target.isLegalSig as && checkLegalArgs Γ args
  | .hlt => true
  | .group (sig := sig) bodies k =>
    sig.all target.isLegalSig &&
      bodies.isLegal target Γ (pushTypes sig Δ) && k.isLegal target Γ (pushTypes sig Δ)

/-- Total computable legality checker for `TBlocks rs sig`. -/
def TBlocks.isLegal (target : LegalTarget) {rs : List Ty}
    (Γ : List (Ty × VarKind)) (Δ : List (List Ty)) : {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true
  | _, .cons (ts := ts) b bs =>
    target.isLegalSig ts && b.isLegal target (pushNormal ts Γ) Δ && bs.isLegal target Γ Δ
end

/-- Computable `Legal` predicate on a closed `Func as rs` via `toTFlat`. -/
def Func.isLegal (target : LegalTarget) {as rs : List Ty} (f : Func as rs) : Bool :=
  target.isLegalSig as && target.isLegalSig rs &&
    (toTFlat (f K KL (Tup.levels as 0)) as.length 0).isLegal target (pushNormal as []) []

/-! ## Source-program supportability check for `legal_isLegal` -/

/-- True iff `target` supports every scalar leaf width (`∃ w ∈ bitWidths, n ≤ w`) and float
format (`f ∈ floatFmts`, `f.width ≤ 64`) occurring in `t`. -/
def LegalTarget.supportsTy (target : LegalTarget) : Ty → Bool
  | .bool => true
  | .bits n => target.bitWidths.any (n ≤ ·) && n ≤ 64
  | .float f => f ∈ target.floatFmts && f.width ≤ 64
  | .pair a b => target.supportsTy a && target.supportsTy b

/-- Target configuration sanity check (true by `decide` on `aarch64`, `scalar64`, `x64`, etc.). -/
def LegalTarget.valid (target : LegalTarget) : Bool :=
  (8 ∈ target.bitWidths) && (64 ∈ target.bitWidths) &&
    target.bitWidths.all (fun w => 0 < w && w % 8 == 0 && w ≤ 64) &&
    target.floatFmts.all fun f => f.width ∈ target.bitWidths && f.width ≤ 64

/-- Check that every type in `op.code` is supported by `target`. -/
def LegalTarget.supportsOpCode (target : LegalTarget) : {as rs : List Ty} → OpCode as rs → Bool
  | _, _, .copy t | _, _, .add t | _, _, .sub t | _, _, .mul t | _, _, .neg t
  | _, _, .and t | _, _, .or t | _, _, .xor t | _, _, .not t | _, _, .ternlog t _
  | _, _, .shl t | _, _, .lshr t | _, _, .ashr t | _, _, .rotl t | _, _, .rotr t
  | _, _, .bswap t | _, _, .cmp _ t _ _ | _, _, .select t | _, _, .blend t _ _
  | _, _, .fadd t | _, _, .fsub t | _, _, .fmul t | _, _, .fdiv t | _, _, .ffma t
  | _, _, .fsqrt t | _, _, .fneg t | _, _, .fabs t | _, _, .fcmp _ t _ _ => target.supportsTy t
  | _, _, .shufd t _ | _, _, .shufb t | _, _, .alignr t _ | _, _, .blendw t _ =>
    target.supportsTy t && (32 ∈ target.bitWidths)
  | _, _, .fshl n | _, _, .fshr n | _, _, .clz n | _, _, .cls n | _, _, .rbit n
  | _, _, .ctz n | _, _, .popcnt n | _, _, .ofBool n
  | _, _, .addc n | _, _, .subb n | _, _, .umulw n | _, _, .smulw n
  | _, _, .udiv n | _, _, .sdiv n | _, _, .urem n | _, _, .srem n
  | _, _, .udiv0 n | _, _, .sdiv0 n => target.supportsTy (.bits n)
  | _, _, .zext m n | _, _, .sext m n | _, _, .trunc m n =>
    target.supportsTy (.bits m) && target.supportsTy (.bits n)
  | _, _, .mkpair a b | _, _, .unpair a b => target.supportsTy a && target.supportsTy b
  | _, _, .bitcast t u _ => target.supportsTy t && target.supportsTy u
  | _, _, .sha256rnds2 | _, _, .sha256msg1 | _, _, .sha256msg2 =>
    target.supportsTy v4i32 && (32 ∈ target.bitWidths)
  | _, _, .fptoui f n | _, _, .fptosi f n | _, _, .uitofp n f | _, _, .sitofp n f =>
    target.supportsTy (.float f) && target.supportsTy (.bits n)
  | _, _, .fcvt f g => target.supportsTy (.float f) && target.supportsTy (.float g)

mutual
/-- Check that every type/operation in a `TFlat` is within `target`'s legalizable domain. -/
def TFlat.supportsSource (target : LegalTarget) {rs : List Ty} : TFlat rs → Bool
  | .let_ op k => target.supportsOpCode op.code && k.supportsSource target
  | .load t _ k => target.supportsTy t && t.bytes ≤ 2 ^ 64 && k.supportsSource target
  | .store (t := t) _ _ k => target.supportsTy t && t.bytes ≤ 2 ^ 64 && k.supportsSource target
  | .call _ (as := as) bs _ k =>
    as.all target.supportsTy && bs.all target.supportsTy && k.supportsSource target
  | .jnz _ t e => t.supportsSource target && e.supportsSource target
  | .jump (ts := ts) _ _ => ts.all target.supportsTy
  | .ret _ => rs.all target.supportsTy
  | .exit _ (as := as) _ => as.all target.supportsTy
  | .hlt => true
  | .group (sig := sig) bodies k =>
    sig.all (·.all target.supportsTy) && bodies.supportsSource target && k.supportsSource target

def TBlocks.supportsSource (target : LegalTarget) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true
  | _, .cons (ts := ts) b bs =>
    ts.all target.supportsTy && b.supportsSource target && bs.supportsSource target
end

/-- Computable check that `f : Func as rs` uses only bit widths/float formats legalizable by
  `target`. -/
def Func.supportsSource (target : LegalTarget) {as rs : List Ty} (f : Func as rs) : Bool :=
  target.valid && as.all target.supportsTy && rs.all target.supportsTy &&
    (toTFlat (f K KL (Tup.levels as 0)) as.length 0).supportsSource target

end LeanQbe.T
