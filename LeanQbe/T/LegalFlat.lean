module

public import LeanQbe.T.Flat
public import LeanQbe.T.Legal
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.MainLemmas

/-!
# Target-Neutral Fast-Path Legalization on `TFlat` (`LegalFlat`)

* `isDirectScalarTy`, `isDirectLegalOp`, `TFlat.isLegalDirect`: `O(N)` check recognizing source
  functions where every type, signature, memory access, and opcode passes through `Func.legal lt`
  unchanged (`0` PHOAS wrapper allocations).
* `legalFlat`: dispatches `O(N)` scalar identity fast-path when `lt.legalSig as = as`,
  `lt.legalSig rs = rs`, and `tf.isLegalDirect lt = true`, falling back identically to
  `reifyFunc (Func.legal lt (denoteFunc tf))` otherwise.
* `legalFlat_eq`: exact kernel equality
  `legalFlat lt tf = reifyFunc (Func.legal lt (denoteFunc tf))` under
  `tf.wfCheck (pushTypes as []) [] = true` (`std3` axioms only).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- True iff `t` is a single native scalar type invariant under `lt.legalTys` and `lt.widenWidth`
with positive bit width (rejecting `0`-width vectors/scalars and pairs). -/
@[expose] def isDirectScalarTy (lt : LegalTarget) : Ty → Bool
  | .bool => true
  | .bits n => 0 < n && n ∈ lt.bitWidths && lt.widenWidth n == n
  | .float f => f ∈ lt.floatFmts
  | .pair _ _ => false

/-- True iff `op.code` is emitted identically by `legalOp lt` without expansion, masking, sign
extension, pair splitting, or elimination (`copy` / self-cast / `bswap i8` / bool shifts). -/
@[expose] def isDirectLegalOp (lt : LegalTarget) : {as rs : List Ty} → OpCode as rs → Bool
  | _, _, .copy _ => false
  | _, _, .add t | _, _, .sub t | _, _, .mul t | _, _, .neg t
  | _, _, .shl t | _, _, .lshr t | _, _, .ashr t | _, _, .rotl t | _, _, .rotr t =>
    match t with
    | .bits n => isDirectScalarTy lt (.bits n)
    | _ => false
  | _, _, .and t | _, _, .or t | _, _, .xor t | _, _, .not t =>
    match t with
    | .bool => true
    | .bits n => isDirectScalarTy lt (.bits n)
    | .float f => lt.scalarFloatBitwise && isDirectScalarTy lt (.float f)
    | .pair _ _ => false
  | _, _, .ternlog t _ =>
    match t with
    | .bits n => lt.scalarTernlog && isDirectScalarTy lt (.bits n)
    | .float f => lt.scalarTernlog && lt.scalarFloatBitwise && isDirectScalarTy lt (.float f)
    | _ => false
  | _, _, .fshl n | _, _, .fshr n
  | _, _, .clz n | _, _, .cls n | _, _, .rbit n | _, _, .ctz n | _, _, .popcnt n
  | _, _, .ofBool n
  | _, _, .addc n | _, _, .subb n | _, _, .umulw n | _, _, .smulw n
  | _, _, .udiv n | _, _, .sdiv n | _, _, .urem n | _, _, .srem n
  | _, _, .udiv0 n | _, _, .sdiv0 n => isDirectScalarTy lt (.bits n)
  | _, _, .bswap t =>
    match t with
    | .bits n => n != 8 && t.bswapOk && isDirectScalarTy lt (.bits n)
    | _ => false
  | _, _, .cmp _ t _ _ =>
    match t with
    | .bool => lt.boolCmp
    | .bits n => isDirectScalarTy lt (.bits n)
    | _ => false
  | _, _, .select t =>
    match t with
    | .bool => lt.boolSelect
    | .bits n => isDirectScalarTy lt (.bits n)
    | .float f => isDirectScalarTy lt (.float f)
    | _ => false
  | _, _, .zext m n | _, _, .sext m n =>
    m < n && isDirectScalarTy lt (.bits m) && isDirectScalarTy lt (.bits n)
  | _, _, .trunc m n =>
    n < m && isDirectScalarTy lt (.bits m) && isDirectScalarTy lt (.bits n)
  | _, _, .bitcast t u _ =>
    (match tyDecEq t u with | isTrue _ => false | isFalse _ => true) &&
      isDirectScalarTy lt t && isDirectScalarTy lt u
  | _, _, .fadd t | _, _, .fsub t | _, _, .fmul t | _, _, .fdiv t | _, _, .ffma t
  | _, _, .fsqrt t | _, _, .fneg t | _, _, .fabs t | _, _, .fcmp _ t _ _ =>
    match t with
    | .float f => isDirectScalarTy lt (.float f)
    | _ => false
  | _, _, .fptoui f n | _, _, .fptosi f n | _, _, .uitofp n f | _, _, .sitofp n f =>
    isDirectScalarTy lt (.float f) && isDirectScalarTy lt (.bits n)
  | _, _, .mkpair _ _ | _, _, .unpair _ _ | _, _, .blend _ _ _
  | _, _, .shufd _ _ | _, _, .shufb _ | _, _, .alignr _ _ | _, _, .blendw _ _
  | _, _, .sha256rnds2 | _, _, .sha256msg1 | _, _, .sha256msg2 => false
  | _, _, .fcvt f g =>
    isDirectScalarTy lt (.float f) && isDirectScalarTy lt (.float g)

mutual
/-- Structural `O(N)` check guaranteeing `Func.legal lt` acts as the identity on `tf`. -/
@[expose] def TFlat.isLegalDirect (lt : LegalTarget) {rs : List Ty} : TFlat rs → Bool
  | .let_ op k => isDirectLegalOp lt op.code && k.isLegalDirect lt
  | .load t _ k => lt.widenWidth 64 == 64 && isDirectScalarTy lt t && k.isLegalDirect lt
  | .store (t := t) _ _ k =>
    lt.widenWidth 64 == 64 && isDirectScalarTy lt t && k.isLegalDirect lt
  | .call _ (as := as) bs _ k =>
    as.all (isDirectScalarTy lt) && bs.all (isDirectScalarTy lt) && k.isLegalDirect lt
  | .jnz _ t e => t.isLegalDirect lt && e.isLegalDirect lt
  | .jump (ts := ts) _ _ => ts.all (isDirectScalarTy lt)
  | .ret _ => rs.all (isDirectScalarTy lt)
  | .exit _ (as := as) _ => as.all (isDirectScalarTy lt)
  | .hlt => true
  | .group (sig := sig) bodies k =>
    sig.all (·.all (isDirectScalarTy lt)) && bodies.isLegalDirect lt && k.isLegalDirect lt

/-- Block-list companion of `TFlat.isLegalDirect`. -/
@[expose] def TBlocks.isLegalDirect (lt : LegalTarget) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true
  | _, .cons (ts := ts) b bs =>
    ts.all (isDirectScalarTy lt) && b.isLegalDirect lt && bs.isLegalDirect lt
end

/-- Target-neutral `TFlat` legalization with an `O(N)` scalar identity fast-path and exact
fallback to `reifyFunc (Func.legal lt (denoteFunc tf))`. -/
@[expose] def legalFlat (lt : LegalTarget) {as rs : List Ty} (tf : TFlat rs) :
    TFlat (lt.legalSig rs) :=
  match listTyDecEq (lt.legalSig as) as, listTyDecEq (lt.legalSig rs) rs,
        tf.isLegalDirect lt with
  | isTrue _, isTrue hrs, true => cast (congrArg TFlat hrs.symm) tf
  | _, _, _ => reifyFunc (Func.legal lt (denoteFunc (as := as) tf))

/-! ## Simulation proof (`legalFlat_eq`) -/

private theorem beq_false_ne {n m : Nat} (h : n ≠ m) : (n == m) = false := by
  simp [h]

private theorem directScalarTy_spec {lt : LegalTarget} {t : Ty}
    (h : isDirectScalarTy lt t = true) : lt.legalTys t = [t] := by
  cases t with
  | bool => rfl
  | bits n =>
    unfold isDirectScalarTy at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp [LegalTarget.legalTys, h.2]
  | float _ => rfl
  | pair _ _ => cases h

private theorem directScalarTy_sig_spec {lt : LegalTarget} :
    ∀ {ts : List Ty}, ts.all (isDirectScalarTy lt) = true → lt.legalSig ts = ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    dsimp only [LegalTarget.legalSig]
    rw [directScalarTy_spec h.1, directScalarTy_sig_spec h.2]; rfl

private theorem directScalarTy_sig_map_spec {lt : LegalTarget} :
    ∀ {sig : List (List Ty)}, sig.all (·.all (isDirectScalarTy lt)) = true →
      sig.map lt.legalSig = sig
  | [], _ => rfl
  | ts :: sig, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.map_cons, directScalarTy_sig_spec h.1, directScalarTy_sig_map_spec h.2]

private theorem directBits_parts {lt : LegalTarget} {n : Nat}
    (h : isDirectScalarTy lt (.bits n) = true) :
    0 < n ∧ n ∈ lt.bitWidths ∧ lt.widenWidth n = n := by
  unfold isDirectScalarTy at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem keepsPacked_of_legalTys_pair {lt : LegalTarget} {a b : Ty}
    (h : lt.legalTys (.pair a b) = [.pair a b]) :
    lt.keepsPacked (.pair a b) = true := by
  by_cases hp : lt.keepsPacked (.pair a b) = true
  · exact hp
  · exfalso
    have hf := Bool.eq_false_iff.mpr hp
    have hlen := congrArg List.length h
    simp only [LegalTarget.legalTys, hf, Bool.false_eq_true, ↓reduceIte,
      List.length_append, List.length_singleton] at hlen
    have ha := legalTys_length_ge_one lt a
    have hb := legalTys_length_ge_one lt b
    omega

private theorem setWidth_tup_heq {V : Ty → Type} {m n : Nat} (h : m = n) (c : BitVec n) :
    HEq (show Tup (Arg V) [.bits m] from (.imm (c.setWidth m), ()))
        (show Tup (Arg V) [.bits n] from (.imm c, ())) := by
  subst h; simp [BitVec.setWidth_eq]

private theorem encodeImm_heq {lt : LegalTarget} {V : Ty → Type} {t : Ty}
    (ht : lt.legalTys t = [t]) (c : Val t) :
    HEq (encodeImm (V := V) lt t c) (show Tup (Arg V) [t] from (.imm c, ())) := by
  cases t with
  | bool => exact HEq.rfl
  | bits n =>
    simp only [LegalTarget.legalTys, List.cons.injEq, Ty.bits.injEq, and_true] at ht
    dsimp only [encodeImm]
    exact setWidth_tup_heq ht c
  | float _ => exact HEq.rfl
  | pair a b =>
    have hp := keepsPacked_of_legalTys_pair ht
    unfold encodeImm
    simp only [hp, ↓reduceDIte, tupToPacked]
    exact cast_heq _ _

private theorem tupAppend_heq {α : Type} {f : α → Type} :
    {a a' b b' : List α} → (ha : a = a') → (hb : b = b') →
    {x : Tup f a} → {x' : Tup f a'} → {y : Tup f b} → {y' : Tup f b'} →
    HEq x x' → HEq y y' → HEq (tupAppend x y) (tupAppend x' y')
  | _, _, _, _, rfl, rfl, _, _, _, _, hx, hy => by
    cases eq_of_heq hx; cases eq_of_heq hy; exact HEq.rfl

private theorem tupAppend_heq_right {α : Type} {f : α → Type} {a b b' : List α} (x : Tup f a)
    (hb : b = b') {y : Tup f b} {y' : Tup f b'} (hy : HEq y y') :
    HEq (tupAppend x y) (tupAppend x y') :=
  tupAppend_heq rfl hb HEq.rfl hy

private theorem tupAppend_nil_heq {α : Type} {f : α → Type} :
    {ts : List α} → (xs : Tup f ts) → HEq (tupAppend xs (bs := []) ()) xs
  | [], () => HEq.rfl
  | _ :: _, (x, xs) => by
    have ih := tupAppend_nil_heq xs
    dsimp only [tupAppend]
    have hcons : ∀ {a : α} {as bs : List α} (h : as = bs) (x : f a)
        {u : Tup f as} {v : Tup f bs},
        HEq u v → HEq (show Tup f (a :: as) from (x, u)) (show Tup f (a :: bs) from (x, v)) :=
      fun h x _ _ huv => by subst h; cases eq_of_heq huv; exact HEq.rfl
    exact hcons (List.append_nil _) x ih

private theorem tupSplit_heq {α : Type} {f : α → Type} :
    {a a' b b' : List α} → (ha : a = a') → (hb : b = b') →
    {xy : Tup f (a ++ b)} → {xs : Tup f a'} → {ys : Tup f b'} →
    HEq xy (tupAppend xs ys) →
    HEq (tupSplit xy).1 xs ∧ HEq (tupSplit xy).2 ys
  | [], [], _, _, rfl, rfl, _, (), _, h => by
    cases eq_of_heq h; exact ⟨HEq.rfl, HEq.rfl⟩
  | _ :: a, _ :: _, _, _, rfl, rfl, (z, rest), (x, xs), ys, h => by
    dsimp only [tupAppend] at h
    have h0 : z = x ∧ HEq rest (tupAppend xs ys) := by
      cases eq_of_heq h; exact ⟨rfl, HEq.rfl⟩
    have ih := tupSplit_heq (a := a) rfl rfl h0.2
    dsimp only [tupSplit]
    cases h0.1
    refine ⟨?_, ih.2⟩
    cases eq_of_heq ih.1; exact HEq.rfl

private theorem tupAppend_split_heq {α : Type} {f : α → Type}
    {a a' b b' : List α} (ha : a = a') (hb : b = b')
    {x : Tup f a} {y : Tup f b} {x' : Tup f a'} {y' : Tup f b'}
    (h : HEq (tupAppend x y) (tupAppend x' y')) :
    HEq x x' ∧ HEq y y' := by
  subst ha; subst hb
  induction a with
  | nil =>
    rcases x with ⟨⟩; rcases x' with ⟨⟩
    cases eq_of_heq h; exact ⟨HEq.rfl, HEq.rfl⟩
  | cons _ _ ih =>
    rcases x with ⟨v, x⟩; rcases x' with ⟨v', x'⟩
    dsimp only [tupAppend] at h
    have heq := eq_of_heq h
    have hv : v = v' := (Prod.mk.inj heq).1
    have hr : HEq (tupAppend x y) (tupAppend x' y') := heq_of_eq (Prod.mk.inj heq).2
    have ihr := ih hr
    cases hv
    refine ⟨?_, ihr.2⟩
    cases eq_of_heq ihr.1; exact HEq.rfl

private theorem heq_of_eq1 {α : Type _} {β : α → Type _} (f : (x : α) → β x)
    {a b : α} (h : a = b) : HEq (f a) (f b) := by
  subst h; exact HEq.rfl

private theorem heq_of_eq2 {α γ : Type _} {β : α → γ → Type _} (f : (x : α) → (y : γ) → β x y)
    {a₁ a₂ : α} {b₁ b₂ : γ} (ha : a₁ = a₂) (hb : b₁ = b₂) : HEq (f a₁ b₁) (f a₂ b₂) := by
  subst ha; subst hb; exact HEq.rfl

private theorem var_bits_heq {V : Ty → Type} {w n : Nat} (hw : w = n)
    {r₁ : V (.bits w)} {r₂ : V (.bits n)} (hr : HEq r₁ r₂) :
    HEq (@Arg.var V (.bits w) r₁) (@Arg.var V (.bits n) r₂) := by
  subst hw; cases eq_of_heq hr; exact HEq.rfl

private theorem tup1_heq {α : Type} {f : α → Type} {a b : α} (hab : a = b)
    {xs : Tup f [a]} {y : f b} (h : HEq xs (show Tup f [b] from (y, ()))) :
    HEq xs.1 y := by
  subst hab; cases eq_of_heq h; exact HEq.rfl

private theorem tup1_list_heq {α : Type} {f : α → Type} {a b : α} (hl : [a] = [b])
    {xs : Tup f [a]} {y : f b} (h : HEq xs (show Tup f [b] from (y, ()))) :
    HEq xs.1 y :=
  tup1_heq (List.cons.inj hl).1 h

private theorem tup1_cast_heq {α : Type} {f : α → Type} {l : List α} {b : α}
    (hl : l = [b]) {xs : Tup f l} {y : f b} (h : HEq xs (show Tup f [b] from (y, ()))) :
    HEq (cast (congrArg (Tup f) hl) xs).1 y := by
  subst hl; cases eq_of_heq h; exact HEq.rfl

private theorem varsTup_single_heq {V : Ty → Type} {u : List Ty} {t : Ty}
    (h : u = [t]) {xs : Tup V u} {x : V t}
    (hx : HEq xs (show Tup V [t] from (x, ()))) :
    HEq (varsTup xs) (show Tup (Arg V) [t] from (.var x, ())) := by
  subst h; cases eq_of_heq hx; exact HEq.rfl

private theorem single_tup_heq {α : Type} {f : α → Type} {a b : α} (hab : a = b)
    {x : f a} {y : f b} (h : HEq x y) :
    HEq (show Tup f [a] from (x, ())) (show Tup f [b] from (y, ())) := by
  subst hab; cases eq_of_heq h; exact HEq.rfl

private theorem pair_tup_heq {α : Type} {f : α → Type} {a₁ a₂ b₁ b₂ : α}
    (ha : a₁ = a₂) (hb : b₁ = b₂)
    {x₁ : f a₁} {x₂ : f a₂} {y₁ : f b₁} {y₂ : f b₂} (hx : HEq x₁ x₂) (hy : HEq y₁ y₂) :
    HEq (show Tup f [a₁, b₁] from (x₁, y₁, ())) (show Tup f [a₂, b₂] from (x₂, y₂, ())) := by
  subst ha; subst hb; cases eq_of_heq hx; cases eq_of_heq hy; exact HEq.rfl

private theorem triple_tup_heq {α : Type} {f : α → Type} {a₁ a₂ b₁ b₂ c₁ c₂ : α}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂)
    {x₁ : f a₁} {x₂ : f a₂} {y₁ : f b₁} {y₂ : f b₂} {z₁ : f c₁} {z₂ : f c₂}
    (hx : HEq x₁ x₂) (hy : HEq y₁ y₂) (hz : HEq z₁ z₂) :
    HEq (show Tup f [a₁, b₁, c₁] from (x₁, y₁, z₁, ()))
        (show Tup f [a₂, b₂, c₂] from (x₂, y₂, z₂, ())) := by
  subst ha; subst hb; subst hc
  cases eq_of_heq hx; cases eq_of_heq hy; cases eq_of_heq hz; exact HEq.rfl

private inductive DirectTupRel (lt : LegalTarget) (V : Ty → Type) :
    {ts : List Ty} → Tup (LVar lt V) ts → Tup V ts → Prop
  | nil : DirectTupRel lt V (ts := []) () ()
  | cons {t : Ty} {ts : List Ty} {v₁ : LVar lt V t} {xs₁ : Tup (LVar lt V) ts}
      {v₂ : V t} {xs₂ : Tup V ts} :
      (∀ (_ : lt.legalTys t = [t]), HEq v₁ (show Tup (Arg V) [t] from (.var v₂, ()))) →
      DirectTupRel lt V xs₁ xs₂ →
      DirectTupRel lt V (ts := t :: ts) (v₁, xs₁) (v₂, xs₂)

private theorem DirectTupRel.single {lt : LegalTarget} {V : Ty → Type} {t : Ty}
    {v₁ : LVar lt V t} {v₂ : V t}
    (h : ∀ (_ : lt.legalTys t = [t]), HEq v₁ (show Tup (Arg V) [t] from (.var v₂, ()))) :
    DirectTupRel lt V (ts := [t]) (v₁, ()) (v₂, ()) :=
  .cons h .nil

private inductive DirectValCtx (lt : LegalTarget) (V : Ty → Type) :
    List Ty → List ((t : Ty) × LVar lt V t) → List ((t : Ty) × V t) → Prop
  | nil : DirectValCtx lt V [] [] []
  | cons {t : Ty} {Γ : List Ty} {v₁ : LVar lt V t} {vs₁ : List ((t : Ty) × LVar lt V t)}
      {v₂ : V t} {vs₂ : List ((t : Ty) × V t)} :
      (∀ (_ : lt.legalTys t = [t]), HEq v₁ (show Tup (Arg V) [t] from (.var v₂, ()))) →
      DirectValCtx lt V Γ vs₁ vs₂ →
      DirectValCtx lt V (t :: Γ) (⟨t, v₁⟩ :: vs₁) (⟨t, v₂⟩ :: vs₂)

private theorem DirectValCtx.push {lt : LegalTarget} {V : Ty → Type} :
    {ts : List Ty} → {xs₁ : Tup (LVar lt V) ts} → {xs₂ : Tup V ts} →
    DirectTupRel lt V xs₁ xs₂ →
    {Γ : List Ty} → {vs₁ : List ((t : Ty) × LVar lt V t)} → {vs₂ : List ((t : Ty) × V t)} →
    DirectValCtx lt V Γ vs₁ vs₂ →
    DirectValCtx lt V (pushTypes ts Γ) (pushTup xs₁ vs₁) (pushTup xs₂ vs₂)
  | [], (), (), .nil, _, _, _, h => h
  | _ :: _, (_, _), (_, _), .cons hv hr, _, _, _, h =>
    DirectValCtx.push hr (.cons hv h)

private theorem DirectValCtx.push_splitParams {lt : LegalTarget} {V : Ty → Type} :
    {ts : List Ty} → (hts : lt.legalSig ts = ts) →
    {xs₁ : Tup V (lt.legalSig ts)} → {xs₂ : Tup V ts} → HEq xs₁ xs₂ →
    {Γ : List Ty} → {vs₁ : List ((t : Ty) × LVar lt V t)} → {vs₂ : List ((t : Ty) × V t)} →
    DirectValCtx lt V Γ vs₁ vs₂ →
    DirectValCtx lt V (pushTypes ts Γ)
      (pushTup (splitParams lt ts xs₁) vs₁) (pushTup xs₂ vs₂)
  | [], _, _, (), _, _, _, _, h => h
  | t :: ts, hts, xs₁, (x₂, xs₂), hheq, Γ, vs₁, vs₂, h => by
    obtain ⟨ht, hts'⟩ := legalSig_eq_cons_iff hts
    have happ : HEq xs₁ (tupAppend (as := [t]) (bs := ts) (x₂, ()) xs₂) := hheq
    obtain ⟨hx1, hx2⟩ := tupSplit_heq (a := lt.legalTys t) (a' := [t]) ht hts' happ
    dsimp only [splitParams, pushTup, pushTypes]
    exact DirectValCtx.push_splitParams hts' hx2 (.cons (fun h' => varsTup_single_heq h' hx1) h)

private inductive DirectLabCtx (lt : LegalTarget) (L : List Ty → Type) :
    List (List Ty) → List ((ts : List Ty) × LLab lt L ts) → List ((ts : List Ty) × L ts) → Prop
  | nil : DirectLabCtx lt L [] [] []
  | cons {ts : List Ty} {Δ : List (List Ty)}
      {l₁ : LLab lt L ts} {ls₁ : List ((ts : List Ty) × LLab lt L ts)}
      {l₂ : L ts} {ls₂ : List ((ts : List Ty) × L ts)} :
      (∀ (_ : lt.legalSig ts = ts), HEq l₁ l₂) →
      DirectLabCtx lt L Δ ls₁ ls₂ →
      DirectLabCtx lt L (ts :: Δ) (⟨ts, l₁⟩ :: ls₁) (⟨ts, l₂⟩ :: ls₂)

private theorem tupLab_split_heq {L : List Ty → Type} :
    {a a' : List Ty} → {b b' : List (List Ty)} → a = a' → b = b' →
    {j₁ : L a} → {Js₁ : Tup L b} → {j₂ : L a'} → {Js₂ : Tup L b'} →
    HEq (show Tup L (a :: b) from (j₁, Js₁)) (show Tup L (a' :: b') from (j₂, Js₂)) →
    HEq j₁ j₂ ∧ HEq Js₁ Js₂
  | _, _, _, _, rfl, rfl, _, _, _, _, h => by cases eq_of_heq h; exact ⟨HEq.rfl, HEq.rfl⟩

private theorem DirectLabCtx.push_tupLiftMap {lt : LegalTarget} {L : List Ty → Type} :
    {sig : List (List Ty)} → (hsig : sig.map lt.legalSig = sig) →
    {Js₁ : Tup L (sig.map lt.legalSig)} → {Js₂ : Tup L sig} → HEq Js₁ Js₂ →
    {Δ : List (List Ty)} → {ls₁ : List ((ts : List Ty) × LLab lt L ts)} →
    {ls₂ : List ((ts : List Ty) × L ts)} →
    DirectLabCtx lt L Δ ls₁ ls₂ →
    DirectLabCtx lt L (pushTypes sig Δ)
      (pushTup (tupLiftMap lt.legalSig L Js₁) ls₁) (pushTup Js₂ ls₂)
  | [], _, _, _, _, _, _, _, h => h
  | ts :: sig, hsig, (j₁, Js₁), (j₂, Js₂), hheq, Δ, ls₁, ls₂, h => by
    simp only [List.map_cons, List.cons.injEq] at hsig
    have hj := tupLab_split_heq hsig.1 hsig.2 hheq
    dsimp only [tupLiftMap, pushTup, pushTypes]
    exact DirectLabCtx.push_tupLiftMap hsig.2 hj.2 (.cons (fun _ => hj.1) h)

private theorem directValCtx_lookupV {lt : LegalTarget} {V : Ty → Type} :
    {Γ : List Ty} → {vs₁ : List ((t : Ty) × LVar lt V t)} → {vs₂ : List ((t : Ty) × V t)} →
    DirectValCtx lt V Γ vs₁ vs₂ → {t : Ty} → (idx : Nat) →
    checkArg Γ t (.var idx) = true →
    ∃ v₁ v₂, lookupV vs₁ t idx = some v₁ ∧ lookupV vs₂ t idx = some v₂ ∧
      (∀ (_ : lt.legalTys t = [t]), HEq v₁ (show Tup (Arg V) [t] from (.var v₂, ())))
  | [], [], [], .nil, _, idx, hc => by cases idx <;> cases hc
  | t' :: _, ⟨_, v₁⟩ :: _, ⟨_, v₂⟩ :: _, .cons hv _, t, 0, hc => by
    dsimp only [checkArg, listGet?] at hc
    cases hdec : tyDecEq t' t with
    | isFalse _ => simp [hdec] at hc
    | isTrue heq =>
      subst heq
      dsimp only [lookupV, listGet?]
      rw [PassFlatKit.castTy_self, PassFlatKit.castTy_self]
      exact ⟨v₁, v₂, rfl, rfl, hv⟩
  | _ :: _, _ :: _, _ :: _, .cons _ hrest, t, idx + 1, hc =>
    directValCtx_lookupV hrest idx hc

private theorem directValCtx_denoteArg {lt : LegalTarget} {V : Ty → Type}
    {Γ : List Ty} {vs₁ : List ((t : Ty) × LVar lt V t)} {vs₂ : List ((t : Ty) × V t)}
    (hvs : DirectValCtx lt V Γ vs₁ vs₂) {t : Ty} (a : Arg K t)
    (hc : checkArg Γ t a = true) :
    ∃ a₁ a₂, denoteArg vs₁ a = some a₁ ∧ denoteArg vs₂ a = some a₂ ∧
      (∀ (_ : lt.legalTys t = [t]), HEq (legalArg lt a₁) (show Tup (Arg V) [t] from (a₂, ()))) := by
  cases a with
  | imm c => exact ⟨.imm c, .imm c, rfl, rfl, fun ht => encodeImm_heq ht c⟩
  | var idx =>
    obtain ⟨v₁, v₂, h1, h2, hv⟩ := directValCtx_lookupV hvs idx hc
    refine ⟨.var v₁, .var v₂, ?_, ?_, hv⟩
    · dsimp only [denoteArg]; rw [h1]
    · dsimp only [denoteArg]; rw [h2]

private theorem directValCtx_denoteArgs {lt : LegalTarget} {V : Ty → Type}
    {Γ : List Ty} {vs₁ : List ((t : Ty) × LVar lt V t)} {vs₂ : List ((t : Ty) × V t)}
    (hvs : DirectValCtx lt V Γ vs₁ vs₂) :
    {ts : List Ty} → (args : Tup (Arg K) ts) → checkArgs Γ args = true →
    ∃ args₁ args₂, denoteArgs vs₁ args = some args₁ ∧ denoteArgs vs₂ args = some args₂ ∧
      (∀ (_ : lt.legalSig ts = ts), HEq (joinArgs lt args₁) args₂)
  | [], (), _ => ⟨(), (), rfl, rfl, fun _ => HEq.rfl⟩
  | _ :: _, (a, as), hc => by
    dsimp only [checkArgs] at hc; simp only [Bool.and_eq_true] at hc
    obtain ⟨a₁, a₂, ha1, ha2, ha⟩ := directValCtx_denoteArg hvs a hc.1
    obtain ⟨as₁, as₂, has1, has2, has⟩ := directValCtx_denoteArgs hvs as hc.2
    refine ⟨(a₁, as₁), (a₂, as₂), ?_, ?_, fun hts => ?_⟩
    · dsimp only [denoteArgs]; rw [ha1, has1]
    · dsimp only [denoteArgs]; rw [ha2, has2]
    · obtain ⟨ht, hts'⟩ := legalSig_eq_cons_iff hts
      dsimp only [joinArgs]
      exact tupAppend_heq ht hts' (ha ht) (has hts')

private theorem directLabCtx_lookupL {lt : LegalTarget} {L : List Ty → Type} :
    {Δ : List (List Ty)} → {ls₁ : List ((ts : List Ty) × LLab lt L ts)} →
    {ls₂ : List ((ts : List Ty) × L ts)} →
    DirectLabCtx lt L Δ ls₁ ls₂ → {ts : List Ty} → (j : Nat) →
    (match listGet? Δ j with
     | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
     | none => false) = true →
    ∃ l₁ l₂, lookupL ls₁ ts j = some l₁ ∧ lookupL ls₂ ts j = some l₂ ∧
      (∀ (_ : lt.legalSig ts = ts), HEq l₁ l₂)
  | [], [], [], .nil, _, j, hc => by cases j <;> cases hc
  | ts' :: _, ⟨_, l₁⟩ :: _, ⟨_, l₂⟩ :: _, .cons hl _, ts, 0, hc => by
    dsimp only [listGet?] at hc
    cases hdec : listTyDecEq ts' ts with
    | isFalse _ => simp [hdec] at hc
    | isTrue heq =>
      subst heq
      dsimp only [lookupL, listGet?]
      rw [PassFlatKit.castListTy_self, PassFlatKit.castListTy_self]
      exact ⟨l₁, l₂, rfl, rfl, hl⟩
  | _ :: _, _ :: _, _ :: _, .cons _ hrest, ts, j + 1, hc =>
    directLabCtx_lookupL hrest j hc

private theorem expr_let_gen_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {sig₁ sig₂ ts₁ ts₂ : List Ty}
    (hsig : sig₁ = sig₂) (hts : ts₁ = ts₂)
    {code₁ : OpCode sig₁ ts₁} {code₂ : OpCode sig₂ ts₂} (hcode : HEq code₁ code₂)
    {args₁ : Tup (Arg V) sig₁} {args₂ : Tup (Arg V) sig₂} (hargs : HEq args₁ args₂)
    {k₁ : Tup V ts₁ → Expr V L rs₁} {k₂ : Tup V ts₂ → Expr V L rs₂}
    (hk : ∀ xs₁ xs₂, HEq xs₁ xs₂ → HEq (k₁ xs₁) (k₂ xs₂)) :
    HEq (Expr.let_ ⟨code₁, args₁⟩ k₁) (Expr.let_ ⟨code₂, args₂⟩ k₂) := by
  subst hrs; subst hsig; subst hts
  cases eq_of_heq hcode
  cases eq_of_heq hargs
  have : k₁ = k₂ := funext fun xs => eq_of_heq (hk xs xs HEq.rfl)
  subst this
  exact HEq.rfl

private theorem expr_load_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {t₁ t₂ : Ty} (ht : t₁ = t₂)
    {a₁ a₂ : Arg V i64} (ha : a₁ = a₂)
    {k₁ : V t₁ → Expr V L rs₁} {k₂ : V t₂ → Expr V L rs₂}
    (hk : ∀ v₁ v₂, HEq v₁ v₂ → HEq (k₁ v₁) (k₂ v₂)) :
    HEq (Expr.load t₁ a₁ k₁) (Expr.load t₂ a₂ k₂) := by
  subst hrs; subst ht; subst ha
  have : k₁ = k₂ := funext fun v => eq_of_heq (hk v v HEq.rfl)
  subst this
  exact HEq.rfl

private theorem expr_store_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {t₁ t₂ : Ty} (ht : t₁ = t₂)
    {v₁ : Arg V t₁} {v₂ : Arg V t₂} (hv : HEq v₁ v₂)
    {a₁ a₂ : Arg V i64} (ha : a₁ = a₂)
    {k₁ : Expr V L rs₁} {k₂ : Expr V L rs₂} (hk : HEq k₁ k₂) :
    HEq (Expr.store v₁ a₁ k₁) (Expr.store v₂ a₂ k₂) := by
  subst hrs; subst ht; subst ha
  cases eq_of_heq hv; cases eq_of_heq hk; exact HEq.rfl

private theorem expr_call_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) (f : Sym)
    {as₁ as₂ bs₁ bs₂ : List Ty} (has : as₁ = as₂) (hbs : bs₁ = bs₂)
    {args₁ : Tup (Arg V) as₁} {args₂ : Tup (Arg V) as₂} (hargs : HEq args₁ args₂)
    {k₁ : Tup V bs₁ → Expr V L rs₁} {k₂ : Tup V bs₂ → Expr V L rs₂}
    (hk : ∀ xs₁ xs₂, HEq xs₁ xs₂ → HEq (k₁ xs₁) (k₂ xs₂)) :
    HEq (Expr.call f (as := as₁) (bs := bs₁) args₁ k₁)
        (Expr.call f (as := as₂) (bs := bs₂) args₂ k₂) := by
  subst hrs; subst has; subst hbs
  cases eq_of_heq hargs
  have : k₁ = k₂ := funext fun xs => eq_of_heq (hk xs xs HEq.rfl)
  subst this
  exact HEq.rfl

private theorem expr_jnz_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {c₁ c₂ : Arg V .bool} (hc : c₁ = c₂)
    {t₁ : Expr V L rs₁} {t₂ : Expr V L rs₂} (ht : HEq t₁ t₂)
    {e₁ : Expr V L rs₁} {e₂ : Expr V L rs₂} (he : HEq e₁ e₂) :
    HEq (Expr.jnz c₁ t₁ e₁) (Expr.jnz c₂ t₂ e₂) := by
  subst hrs; subst hc; cases eq_of_heq ht; cases eq_of_heq he; exact HEq.rfl

private theorem expr_jump_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {ts₁ ts₂ : List Ty} (hts : ts₁ = ts₂)
    {j₁ : L ts₁} {j₂ : L ts₂} (hj : HEq j₁ j₂)
    {args₁ : Tup (Arg V) ts₁} {args₂ : Tup (Arg V) ts₂} (hargs : HEq args₁ args₂) :
    HEq (Expr.jump j₁ args₁ : Expr V L rs₁) (Expr.jump j₂ args₂ : Expr V L rs₂) := by
  subst hrs; subst hts; cases eq_of_heq hj; cases eq_of_heq hargs; exact HEq.rfl

private theorem expr_ret_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂)
    {vs₁ : Tup (Arg V) rs₁} {vs₂ : Tup (Arg V) rs₂} (hvs : HEq vs₁ vs₂) :
    HEq (Expr.ret vs₁ : Expr V L rs₁) (Expr.ret vs₂ : Expr V L rs₂) := by
  subst hrs; cases eq_of_heq hvs; exact HEq.rfl

private theorem expr_exit_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) (f : Sym) {as₁ as₂ : List Ty} (has : as₁ = as₂)
    {args₁ : Tup (Arg V) as₁} {args₂ : Tup (Arg V) as₂} (hargs : HEq args₁ args₂) :
    HEq (Expr.exit f args₁ : Expr V L rs₁) (Expr.exit f args₂ : Expr V L rs₂) := by
  subst hrs; subst has; cases eq_of_heq hargs; exact HEq.rfl

private theorem expr_hlt_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) :
    HEq (Expr.hlt : Expr V L rs₁) (Expr.hlt : Expr V L rs₂) := by
  subst hrs; exact HEq.rfl

private theorem expr_group_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {sig₁ sig₂ : List (List Ty)} (hsig : sig₁ = sig₂)
    {b₁ : Tup L sig₁ → Blocks V L rs₁ sig₁} {b₂ : Tup L sig₂ → Blocks V L rs₂ sig₂}
    (hb : ∀ Js₁ Js₂, HEq Js₁ Js₂ → HEq (b₁ Js₁) (b₂ Js₂))
    {k₁ : Tup L sig₁ → Expr V L rs₁} {k₂ : Tup L sig₂ → Expr V L rs₂}
    (hk : ∀ Js₁ Js₂, HEq Js₁ Js₂ → HEq (k₁ Js₁) (k₂ Js₂)) :
    HEq (Expr.group b₁ k₁) (Expr.group b₂ k₂) := by
  subst hrs; subst hsig
  have hbeq : b₁ = b₂ := funext fun Js => eq_of_heq (hb Js Js HEq.rfl)
  have hkeq : k₁ = k₂ := funext fun Js => eq_of_heq (hk Js Js HEq.rfl)
  subst hbeq; subst hkeq; exact HEq.rfl

private theorem blocks_nil_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) :
    HEq (Blocks.nil : Blocks V L rs₁ []) (Blocks.nil : Blocks V L rs₂ []) := by
  subst hrs; exact HEq.rfl

private theorem blocks_cons_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {ts₁ ts₂ : List Ty} (hts : ts₁ = ts₂)
    {sig₁ sig₂ : List (List Ty)} (hsig : sig₁ = sig₂)
    {b₁ : Tup V ts₁ → Expr V L rs₁} {b₂ : Tup V ts₂ → Expr V L rs₂}
    (hb : ∀ xs₁ xs₂, HEq xs₁ xs₂ → HEq (b₁ xs₁) (b₂ xs₂))
    {bs₁ : Blocks V L rs₁ sig₁} {bs₂ : Blocks V L rs₂ sig₂} (hbs : HEq bs₁ bs₂) :
    HEq (Blocks.cons b₁ bs₁) (Blocks.cons b₂ bs₂) := by
  subst hrs; subst hts; subst hsig
  have hbeq : b₁ = b₂ := funext fun xs => eq_of_heq (hb xs xs HEq.rfl)
  cases hbeq; cases eq_of_heq hbs; exact HEq.rfl

private theorem unary_args_heq {lt : LegalTarget} {V : Ty → Type} {t : Ty}
    (ht : lt.legalTys t = [t])
    {args₁ : Tup (Arg (LVar lt V)) [t]} {args₂ : Tup (Arg V) [t]}
    (hargs : ∀ _ : lt.legalSig [t] = [t], HEq (joinArgs lt args₁) args₂) :
    HEq (legalArg lt args₁.1) (show Tup (Arg V) [t] from (args₂.1, ())) := by
  rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
  have hsig : lt.legalSig [t] = [t] := by simp [LegalTarget.legalSig, ht]
  have hj := hargs hsig
  dsimp only [joinArgs] at hj
  exact (tupAppend_nil_heq (legalArg lt a₁)).symm.trans hj

private theorem binary_args_heq {lt : LegalTarget} {V : Ty → Type} {t₁ t₂ : Ty}
    (ht₁ : lt.legalTys t₁ = [t₁]) (ht₂ : lt.legalTys t₂ = [t₂])
    {args₁ : Tup (Arg (LVar lt V)) [t₁, t₂]} {args₂ : Tup (Arg V) [t₁, t₂]}
    (hargs : ∀ _ : lt.legalSig [t₁, t₂] = [t₁, t₂], HEq (joinArgs lt args₁) args₂) :
    HEq (legalArg lt args₁.1) (show Tup (Arg V) [t₁] from (args₂.1, ())) ∧
      HEq (legalArg lt args₁.2.1) (show Tup (Arg V) [t₂] from (args₂.2.1, ())) := by
  rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
  have hsig : lt.legalSig [t₁, t₂] = [t₁, t₂] := by simp [LegalTarget.legalSig, ht₁, ht₂]
  have hj := hargs hsig
  dsimp only [joinArgs] at hj
  have ha := tupAppend_heq_right (legalArg lt a₁) (List.append_nil _)
    (tupAppend_nil_heq (legalArg lt b₁))
  have hj' : HEq (tupAppend (legalArg lt a₁) (legalArg lt b₁))
      (tupAppend (as := [t₁]) (bs := [t₂]) (a₂, ()) (b₂, ())) := ha.symm.trans hj
  exact tupAppend_split_heq ht₁ ht₂ hj'

private theorem ternary_args_heq {lt : LegalTarget} {V : Ty → Type} {t₁ t₂ t₃ : Ty}
    (ht₁ : lt.legalTys t₁ = [t₁]) (ht₂ : lt.legalTys t₂ = [t₂]) (ht₃ : lt.legalTys t₃ = [t₃])
    {args₁ : Tup (Arg (LVar lt V)) [t₁, t₂, t₃]} {args₂ : Tup (Arg V) [t₁, t₂, t₃]}
    (hargs : ∀ _ : lt.legalSig [t₁, t₂, t₃] = [t₁, t₂, t₃], HEq (joinArgs lt args₁) args₂) :
    HEq (legalArg lt args₁.1) (show Tup (Arg V) [t₁] from (args₂.1, ())) ∧
      HEq (legalArg lt args₁.2.1) (show Tup (Arg V) [t₂] from (args₂.2.1, ())) ∧
      HEq (legalArg lt args₁.2.2.1) (show Tup (Arg V) [t₃] from (args₂.2.2.1, ())) := by
  rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
  have hsig : lt.legalSig [t₁, t₂, t₃] = [t₁, t₂, t₃] := by
    simp [LegalTarget.legalSig, ht₁, ht₂, ht₃]
  have hj := hargs hsig
  dsimp only [joinArgs] at hj
  have htail : lt.legalTys t₂ ++ (lt.legalTys t₃ ++ []) = lt.legalTys t₂ ++ lt.legalTys t₃ := by
    simp [List.append_nil]
  have ha := tupAppend_heq_right (legalArg lt a₁) htail
    (tupAppend_heq_right (legalArg lt b₁) (List.append_nil _)
      (tupAppend_nil_heq (legalArg lt c₁)))
  have hbc : HEq (tupAppend (legalArg lt a₁) (tupAppend (legalArg lt b₁) (legalArg lt c₁)))
      (tupAppend (as := [t₁]) (bs := [t₂, t₃]) (a₂, ())
        (tupAppend (as := [t₂]) (bs := [t₃]) (b₂, ()) (c₂, ()))) := ha.symm.trans hj
  have h23 : lt.legalTys t₂ ++ lt.legalTys t₃ = [t₂, t₃] := by simp [ht₂, ht₃]
  have hsp1 := tupAppend_split_heq ht₁ h23 hbc
  have hsp2 := tupAppend_split_heq ht₂ ht₃ hsp1.2
  exact ⟨hsp1.1, hsp2.1, hsp2.2⟩

private theorem directTupRel_single_cast {lt : LegalTarget} {V : Ty → Type} {t : Ty}
    (ht : lt.legalTys t = [t]) (r : V t) :
    DirectTupRel lt V (ts := [t])
      (cast (congrArg (Tup (Arg V)) ht.symm) (show Tup (Arg V) [t] from (.var r, ())), ())
      (r, ()) :=
  DirectTupRel.single (t := t) fun _ =>
    cast_heq (congrArg (Tup (Arg V)) ht.symm) (show Tup (Arg V) [t] from (.var r, ()))

private theorem directTupRel_bits1 {lt : LegalTarget} {V : Ty → Type} {n : Nat}
    (hw : lt.widenWidth n = n) {r₁ : V (.bits (lt.widenWidth n))} {r₂ : V (.bits n)}
    (hr : HEq r₁ r₂) :
    DirectTupRel lt V (ts := [.bits n])
      ((@Arg.var V (.bits (lt.widenWidth n)) r₁, ()), ()) (r₂, ()) :=
  DirectTupRel.single (t := .bits n) fun _ =>
    single_tup_heq (congrArg Ty.bits hw) (var_bits_heq hw hr)

private theorem directTupRel_bitsBool {lt : LegalTarget} {V : Ty → Type} {n : Nat}
    (hw : lt.widenWidth n = n) {s₁ : V (.bits (lt.widenWidth n))} {s₂ : V (.bits n)}
    {co₁ co₂ : V .bool} (hs : HEq s₁ s₂) (hc : co₁ = co₂) :
    DirectTupRel lt V (ts := [.bits n, .bool])
      ((@Arg.var V (.bits (lt.widenWidth n)) s₁, ()), (@Arg.var V .bool co₁, ()), ())
      (s₂, co₂, ()) :=
  .cons (t := .bits n) (ts := [.bool])
    (fun _ => single_tup_heq (congrArg Ty.bits hw) (var_bits_heq hw hs))
    (DirectTupRel.single (t := .bool) fun _ => by cases hc; exact HEq.rfl)

private theorem directTupRel_bits2 {lt : LegalTarget} {V : Ty → Type} {n : Nat}
    (hw : lt.widenWidth n = n) {lo₁ hi₁ : V (.bits (lt.widenWidth n))}
    {lo₂ hi₂ : V (.bits n)} (hlo : HEq lo₁ lo₂) (hhi : HEq hi₁ hi₂) :
    DirectTupRel lt V (ts := [.bits n, .bits n])
      ((@Arg.var V (.bits (lt.widenWidth n)) lo₁, ()),
       (@Arg.var V (.bits (lt.widenWidth n)) hi₁, ()), ())
      (lo₂, hi₂, ()) :=
  .cons (t := .bits n) (ts := [.bits n])
    (fun _ => single_tup_heq (congrArg Ty.bits hw) (var_bits_heq hw hlo))
    (DirectTupRel.single (t := .bits n) fun _ =>
      single_tup_heq (congrArg Ty.bits hw) (var_bits_heq hw hhi))

private theorem legalUnaryTree_bool (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (mkCode : (u : Ty) → OpCode [u] [u]) (vecS : (u : Ty) → Bool)
    (onBool : Arg V .bool → (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) → (Arg V (.float f) → Expr V L rs) → Expr V L rs)
    (xs : Tup (Arg V) [.bool]) (k : Tup (Arg V) [.bool] → Expr V L rs) :
    legalUnaryTree target mkCode vecS onBool onBits onFloat .bool xs k =
      onBool xs.1 fun r => k (r, ()) := rfl

private theorem legalUnaryTree_bits (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (mkCode : (u : Ty) → OpCode [u] [u]) (vecS : (u : Ty) → Bool)
    (onBool : Arg V .bool → (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) → (Arg V (.float f) → Expr V L rs) → Expr V L rs)
    (n : Nat) (xs : Tup (Arg V) [.bits (target.widenWidth n)])
    (k : Tup (Arg V) [.bits (target.widenWidth n)] → Expr V L rs) :
    legalUnaryTree target mkCode vecS onBool onBits onFloat (.bits n) xs k =
      onBits n xs.1 fun r => k (r, ()) := rfl

private theorem legalUnaryTree_float (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (mkCode : (u : Ty) → OpCode [u] [u]) (vecS : (u : Ty) → Bool)
    (onBool : Arg V .bool → (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) → (Arg V (.float f) → Expr V L rs) → Expr V L rs)
    (f : Fmt) (xs : Tup (Arg V) [.float f]) (k : Tup (Arg V) [.float f] → Expr V L rs) :
    legalUnaryTree target mkCode vecS onBool onBits onFloat (.float f) xs k =
      onFloat f xs.1 fun r => k (r, ()) := rfl

private theorem legalBinTree_bool (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (mkCode : (u : Ty) → OpCode [u, u] [u]) (vecS : (u : Ty) → Bool → Bool)
    (onBool : Arg V .bool → Arg V .bool → (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) →
      Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) → Arg V (.float f) →
      (Arg V (.float f) → Expr V L rs) → Expr V L rs)
    (unif : (u : Ty) → Arg (LVar target V) u → Bool)
    (xs ys : Tup (Arg V) [.bool]) (rawRhs : Option (Arg (LVar target V) .bool))
    (k : Tup (Arg V) [.bool] → Expr V L rs) :
    legalBinTree target mkCode vecS onBool onBits onFloat unif .bool xs ys rawRhs k =
      onBool xs.1 ys.1 fun r => k (r, ()) := rfl

private theorem legalBinTree_bits (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (mkCode : (u : Ty) → OpCode [u, u] [u]) (vecS : (u : Ty) → Bool → Bool)
    (onBool : Arg V .bool → Arg V .bool → (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) →
      Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) → Arg V (.float f) →
      (Arg V (.float f) → Expr V L rs) → Expr V L rs)
    (unif : (u : Ty) → Arg (LVar target V) u → Bool) (n : Nat)
    (xs ys : Tup (Arg V) [.bits (target.widenWidth n)])
    (rawRhs : Option (Arg (LVar target V) (.bits n)))
    (k : Tup (Arg V) [.bits (target.widenWidth n)] → Expr V L rs) :
    legalBinTree target mkCode vecS onBool onBits onFloat unif (.bits n) xs ys rawRhs k =
      onBits n xs.1 ys.1 fun r => k (r, ()) := rfl

private theorem legalBinTree_float (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (mkCode : (u : Ty) → OpCode [u, u] [u]) (vecS : (u : Ty) → Bool → Bool)
    (onBool : Arg V .bool → Arg V .bool → (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) →
      Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) → Arg V (.float f) →
      (Arg V (.float f) → Expr V L rs) → Expr V L rs)
    (unif : (u : Ty) → Arg (LVar target V) u → Bool) (f : Fmt)
    (xs ys : Tup (Arg V) [.float f]) (rawRhs : Option (Arg (LVar target V) (.float f)))
    (k : Tup (Arg V) [.float f] → Expr V L rs) :
    legalBinTree target mkCode vecS onBool onBits onFloat unif (.float f) xs ys rawRhs k =
      onFloat f xs.1 ys.1 fun r => k (r, ()) := rfl

private theorem legalTernaryTree_bits (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (mkCode : (u : Ty) → OpCode [u, u, u] [u]) (vecS : (u : Ty) → Bool)
    (onBool : Arg V .bool → Arg V .bool → Arg V .bool →
      (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) →
      Arg V (.bits (target.widenWidth n)) → Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) → Arg V (.float f) → Arg V (.float f) →
      (Arg V (.float f) → Expr V L rs) → Expr V L rs)
    (n : Nat) (xs ys zs : Tup (Arg V) [.bits (target.widenWidth n)])
    (k : Tup (Arg V) [.bits (target.widenWidth n)] → Expr V L rs) :
    legalTernaryTree target mkCode vecS onBool onBits onFloat (.bits n) xs ys zs k =
      onBits n xs.1 ys.1 zs.1 fun r => k (r, ()) := rfl

private theorem legalTernaryTree_float (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (mkCode : (u : Ty) → OpCode [u, u, u] [u]) (vecS : (u : Ty) → Bool)
    (onBool : Arg V .bool → Arg V .bool → Arg V .bool →
      (Arg V .bool → Expr V L rs) → Expr V L rs)
    (onBits : (n : Nat) → Arg V (.bits (target.widenWidth n)) →
      Arg V (.bits (target.widenWidth n)) → Arg V (.bits (target.widenWidth n)) →
      (Arg V (.bits (target.widenWidth n)) → Expr V L rs) → Expr V L rs)
    (onFloat : (f : Fmt) → Arg V (.float f) → Arg V (.float f) → Arg V (.float f) →
      (Arg V (.float f) → Expr V L rs) → Expr V L rs)
    (f : Fmt) (xs ys zs : Tup (Arg V) [.float f])
    (k : Tup (Arg V) [.float f] → Expr V L rs) :
    legalTernaryTree target mkCode vecS onBool onBits onFloat (.float f) xs ys zs k =
      onFloat f xs.1 ys.1 zs.1 fun r => k (r, ()) := rfl

private theorem legalCmpTree_bool (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (o : CmpOp) (xs ys : Tup (Arg V) [.bool])
    (k : Tup (Arg V) [.bool] → Expr V L rs) :
    legalCmpTree target o .bool xs ys k =
      (if target.boolCmp then Expr.let_ (op2 (.cmp o .bool) xs.1 ys.1) fun (r, ()) => k (.var r, ())
       else emitBoolCmp o xs.1 ys.1 fun r => k (r, ())) := rfl

private theorem legalCmpTree_bits (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (o : CmpOp) (n : Nat)
    (xs ys : Tup (Arg V) [.bits (target.widenWidth n)])
    (k : Tup (Arg V) [.bool] → Expr V L rs) :
    legalCmpTree target o (.bits n) xs ys k =
      let w := target.widenWidth n
      (if n == 0 then k (.imm (o.evalBits 0#0 0#0), ())
       else if n == w then
         Expr.let_ (op2 (.cmp o (.bits w)) xs.1 ys.1) fun (r, ()) => k (.var r, ())
       else
         let isSigned := match o with | .slt | .sle | .sgt | .sge => true | _ => false
         if isSigned then
           emitSextToW n w xs.1 fun sa => emitSextToW n w ys.1 fun sb =>
             Expr.let_ (op2 (.cmp o (.bits w)) sa sb) fun (r, ()) => k (.var r, ())
         else Expr.let_ (op2 (.cmp o (.bits w)) xs.1 ys.1) fun (r, ()) => k (.var r, ())) := rfl

private theorem legalSelectTree_bool (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (c : Arg V .bool) (xs ys : Tup (Arg V) [.bool])
    (k : Tup (Arg V) [.bool] → Expr V L rs) :
    legalSelectTree target c .bool xs ys k =
      (if target.boolSelect then
         Expr.let_ (op3 (.select .bool) c xs.1 ys.1) fun (r, ()) => k (.var r, ())
       else emitBoolSelect c xs.1 ys.1 fun r => k (r, ())) := rfl

private theorem legalSelectTree_bits (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (c : Arg V .bool) (n : Nat)
    (xs ys : Tup (Arg V) [.bits (target.widenWidth n)])
    (k : Tup (Arg V) [.bits (target.widenWidth n)] → Expr V L rs) :
    legalSelectTree target c (.bits n) xs ys k =
      Expr.let_ (op3 (.select (.bits (target.widenWidth n))) c xs.1 ys.1)
        fun (r, ()) => k (.var r, ()) := rfl

private theorem legalSelectTree_float (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (c : Arg V .bool) (f : Fmt) (xs ys : Tup (Arg V) [.float f])
    (k : Tup (Arg V) [.float f] → Expr V L rs) :
    legalSelectTree target c (.float f) xs ys k =
      Expr.let_ (op3 (.select (.float f)) c xs.1 ys.1) fun (r, ()) => k (.var r, ()) := rfl

private theorem legalFCmpTree_float (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (o : FCmpOp) (f : Fmt) (xs ys : Tup (Arg V) [.float f])
    (k : Tup (Arg V) [.bool] → Expr V L rs) :
    legalFCmpTree target o (.float f) xs ys k =
      Expr.let_ (op2 (.fcmp o (.float f)) xs.1 ys.1) fun (r, ()) => k (.var r, ()) := rfl

private theorem legalLoad_bits (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (n : Nat) (ptr : Arg V i64)
    (k : LVar target V (.bits n) → Expr V L rs) :
    legalLoad target (.bits n) ptr k =
      let w := target.widenWidth n
      if n == w then Expr.load (.bits w) ptr fun v => k (.var v, ())
      else emitLoadBits target.bitWidths n w ptr fun r => k (r, ()) := rfl

private theorem legalStore_bool (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (xs : LVar target V .bool) (ptr : Arg V i64) (k : Expr V L rs) :
    legalStore target .bool xs ptr k = Expr.store (t := .bool) xs.1 ptr k := rfl

private theorem legalStore_float (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (f : Fmt) (xs : LVar target V (.float f)) (ptr : Arg V i64) (k : Expr V L rs) :
    legalStore target (.float f) xs ptr k = Expr.store (t := .float f) xs.1 ptr k := rfl

private theorem legalStore_bits (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} (n : Nat) (xs : LVar target V (.bits n)) (ptr : Arg V i64) (k : Expr V L rs) :
    legalStore target (.bits n) xs ptr k =
      let w := target.widenWidth n
      if n == w then Expr.store (t := .bits w) xs.1 ptr k
      else emitStoreBits target.bitWidths n w xs.1 ptr k := rfl

private theorem single_direct_let_heq {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {lt : LegalTarget} {sig : List Ty} {t : Ty}
    (ht : lt.legalTys t = [t]) (code : OpCode sig [t])
    {args₁ args₂ : Tup (Arg V) sig} (hargs : args₁ = args₂)
    {k₁ : Tup (LVar lt V) [t] → Expr V L rs₁} {k₂ : Tup V [t] → Expr V L rs₂}
    (hk : ∀ (xs₁ : Tup (LVar lt V) [t]) (xs₂ : Tup V [t]),
      DirectTupRel lt V xs₁ xs₂ → HEq (k₁ xs₁) (k₂ xs₂)) :
    HEq (Expr.let_ ⟨code, args₁⟩
          fun (r, ()) => k₁ (cast (congrArg (Tup (Arg V)) ht.symm)
            (show Tup (Arg V) [t] from (.var r, ())), ()))
        (Expr.let_ ⟨code, args₂⟩ k₂) := by
  subst hargs
  refine expr_let_gen_heq hrs rfl rfl HEq.rfl HEq.rfl fun xs₁ xs₂ hxs => ?_
  rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
  have hreq : r₁ = r₂ := (Prod.mk.inj (eq_of_heq hxs)).1
  subst hreq
  exact hk _ (r₁, ()) (directTupRel_single_cast ht r₁)

private theorem bits1_let_heq (lt : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {n : Nat}
    (mkCode : (w : Nat) → OpCode [.bits w] [.bits w])
    (hw : lt.widenWidth n = n)
    {a₁ : Arg V (.bits (lt.widenWidth n))} {a₂ : Arg V (.bits n)} (ha : HEq a₁ a₂)
    {k₁ : Tup (LVar lt V) [.bits n] → Expr V L rs₁} {k₂ : Tup V [.bits n] → Expr V L rs₂}
    (hk : ∀ (xs₁ : Tup (LVar lt V) [.bits n]) (xs₂ : Tup V [.bits n]),
      DirectTupRel lt V xs₁ xs₂ → HEq (k₁ xs₁) (k₂ xs₂)) :
    HEq (Expr.let_ (op1 (mkCode (lt.widenWidth n)) a₁)
          fun x => k₁ ((@Arg.var V (.bits (lt.widenWidth n)) x.1, ()), ()))
        (Expr.let_ ⟨mkCode n, (a₂, ())⟩ k₂) := by
  refine expr_let_gen_heq hrs (by simp [hw]) (by simp [hw])
    (heq_of_eq1 mkCode hw) (single_tup_heq (congrArg Ty.bits hw) ha) fun xs₁ xs₂ hxs => ?_
  rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
  exact hk _ _ (directTupRel_bits1 hw (tup1_heq (congrArg Ty.bits hw) hxs))

private theorem bits2_let_heq (lt : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {n : Nat}
    (mkCode : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    (hw : lt.widenWidth n = n)
    {a₁ b₁ : Arg V (.bits (lt.widenWidth n))} {a₂ b₂ : Arg V (.bits n)}
    (ha : HEq a₁ a₂) (hb : HEq b₁ b₂)
    {k₁ : Tup (LVar lt V) [.bits n] → Expr V L rs₁} {k₂ : Tup V [.bits n] → Expr V L rs₂}
    (hk : ∀ (xs₁ : Tup (LVar lt V) [.bits n]) (xs₂ : Tup V [.bits n]),
      DirectTupRel lt V xs₁ xs₂ → HEq (k₁ xs₁) (k₂ xs₂)) :
    HEq (Expr.let_ (op2 (mkCode (lt.widenWidth n)) a₁ b₁)
          fun x => k₁ ((@Arg.var V (.bits (lt.widenWidth n)) x.1, ()), ()))
        (Expr.let_ ⟨mkCode n, (a₂, b₂, ())⟩ k₂) := by
  refine expr_let_gen_heq hrs (by simp [hw]) (by simp [hw])
    (heq_of_eq1 mkCode hw) (pair_tup_heq (congrArg Ty.bits hw) (congrArg Ty.bits hw) ha hb)
    fun xs₁ xs₂ hxs => ?_
  rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
  exact hk _ _ (directTupRel_bits1 hw (tup1_heq (congrArg Ty.bits hw) hxs))

private theorem bits3_let_heq (lt : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {n : Nat}
    (mkCode : (w : Nat) → OpCode [.bits w, .bits w, .bits w] [.bits w])
    (hw : lt.widenWidth n = n)
    {a₁ b₁ c₁ : Arg V (.bits (lt.widenWidth n))} {a₂ b₂ c₂ : Arg V (.bits n)}
    (ha : HEq a₁ a₂) (hb : HEq b₁ b₂) (hc : HEq c₁ c₂)
    {k₁ : Tup (LVar lt V) [.bits n] → Expr V L rs₁} {k₂ : Tup V [.bits n] → Expr V L rs₂}
    (hk : ∀ (xs₁ : Tup (LVar lt V) [.bits n]) (xs₂ : Tup V [.bits n]),
      DirectTupRel lt V xs₁ xs₂ → HEq (k₁ xs₁) (k₂ xs₂)) :
    HEq (Expr.let_ (op3 (mkCode (lt.widenWidth n)) a₁ b₁ c₁)
          fun x => k₁ ((@Arg.var V (.bits (lt.widenWidth n)) x.1, ()), ()))
        (Expr.let_ ⟨mkCode n, (a₂, b₂, c₂, ())⟩ k₂) := by
  refine expr_let_gen_heq hrs (by simp [hw]) (by simp [hw])
    (heq_of_eq1 mkCode hw)
    (triple_tup_heq (congrArg Ty.bits hw) (congrArg Ty.bits hw) (congrArg Ty.bits hw) ha hb hc)
    fun xs₁ xs₂ hxs => ?_
  rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
  exact hk _ _ (directTupRel_bits1 hw (tup1_heq (congrArg Ty.bits hw) hxs))

private theorem legalOp_bitcast_direct_heq (lt : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {t u : Ty} (h : t.size = u.size) (hne : t ≠ u)
    (ht_sc : isDirectScalarTy lt t = true) (hu_sc : isDirectScalarTy lt u = true)
    (a₁ : Arg (LVar lt V) t) (a₂ : Arg V t)
    (ha : ∀ (_ : lt.legalSig [t] = [t]), HEq (legalArg lt a₁) (show Tup (Arg V) [t] from (a₂, ())))
    {k₁ : Tup (LVar lt V) [u] → Expr V L rs₁} {k₂ : Tup V [u] → Expr V L rs₂}
    (hk : ∀ (xs₁ : Tup (LVar lt V) [u]) (xs₂ : Tup V [u]),
      DirectTupRel lt V xs₁ xs₂ → HEq (k₁ xs₁) (k₂ xs₂)) :
    HEq (legalOp lt ⟨.bitcast t u h, (a₁, ())⟩ k₁)
        (Expr.let_ (op1 (.bitcast t u h) a₂) k₂) := by
  have ht := directScalarTy_spec ht_sc
  have hu := directScalarTy_spec hu_sc
  have ha' : HEq (legalArg lt a₁) (show Tup (Arg V) [t] from (a₂, ())) :=
    ha (by simp [LegalTarget.legalSig, ht])
  have hBody :
      legalOp lt ⟨.bitcast t u h, (a₁, ())⟩ k₁ =
        Expr.let_ (op1 (.bitcast t u h) (cast (congrArg (Tup (Arg V)) ht) (legalArg lt a₁)).1)
          fun (r, ()) =>
            k₁ (cast (congrArg (Tup (Arg V)) hu.symm)
                  (show Tup (Arg V) [u] from (.var r, ())), ()) := by
    cases t with
    | pair _ _ => cases ht_sc
    | bool | bits _ | float _ =>
      cases u with
      | pair _ _ => cases hu_sc
      | bool | bits _ | float _ =>
        simp only [isDirectScalarTy, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          at ht_sc hu_sc
        first
        | exact absurd rfl hne
        | (dsimp only [legalOp]; simp [eq_false hne, LegalTarget.isLegalTy, ht_sc, hu_sc])
  rw [hBody]
  refine expr_let_gen_heq hrs rfl rfl HEq.rfl
    (single_tup_heq rfl (tup1_cast_heq ht ha')) fun xs₁ xs₂ hxs => ?_
  rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
  have hreq : r₁ = r₂ := (Prod.mk.inj (eq_of_heq hxs)).1
  subst hreq
  exact hk _ (r₁, ()) (DirectTupRel.single (t := u) fun _ => cast_heq _ _)

private theorem legalOp_direct_heq (lt : LegalTarget) {V : Ty → Type} {L : List Ty → Type}
    {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂) {sig ts : List Ty}
    (code : OpCode sig ts) (hcode : isDirectLegalOp lt code = true)
    (args₁ : Tup (Arg (LVar lt V)) sig) (args₂ : Tup (Arg V) sig)
    (hargs : ∀ (_ : lt.legalSig sig = sig), HEq (joinArgs lt args₁) args₂)
    {k₁ : Tup (LVar lt V) ts → Expr V L rs₁} {k₂ : Tup V ts → Expr V L rs₂}
    (hk : ∀ (xs₁ : Tup (LVar lt V) ts) (xs₂ : Tup V ts),
      DirectTupRel lt V xs₁ xs₂ → HEq (k₁ xs₁) (k₂ xs₂)) :
    HEq (legalOp lt ⟨code, args₁⟩ k₁) (Expr.let_ ⟨code, args₂⟩ k₂) := by
  cases code with
  | copy _ => cases hcode
  | add t | sub t | mul t | shl t | lshr t | ashr t | rotl t | rotr t =>
    cases t with
    | bool | float _ | pair _ _ => cases hcode
    | bits n =>
      dsimp only [isDirectLegalOp] at hcode
      obtain ⟨hn, _, hw⟩ := directBits_parts hcode
      have ht := directScalarTy_spec hcode
      obtain ⟨ha, hb⟩ := binary_args_heq ht ht hargs
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      dsimp only at ha hb
      dsimp only [legalOp, Ty.hasFloat]
      simp only [Bool.false_eq_true, ↓reduceIte]
      erw [legalBinTree_bits]
      dsimp only [legalBitsArith, emitMaskToN]
      have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
      have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
      have hwn : lt.widenWidth n ≤ n := Nat.le_of_eq hw
      simp only [hn0, Bool.false_eq_true, ↓reduceIte, hnw, hwn]
      let go := fun mk => bits2_let_heq lt hrs mk hw
        (tup1_list_heq ht ha) (tup1_list_heq ht hb) hk
      first
      | exact go (fun w => .add (.bits w)) | exact go (fun w => .sub (.bits w))
      | exact go (fun w => .mul (.bits w)) | exact go (fun w => .shl (.bits w))
      | exact go (fun w => .lshr (.bits w)) | exact go (fun w => .ashr (.bits w))
      | exact go (fun w => .rotl (.bits w)) | exact go (fun w => .rotr (.bits w))
  | neg t =>
    cases t with
    | bool | float _ | pair _ _ => cases hcode
    | bits n =>
      dsimp only [isDirectLegalOp] at hcode
      obtain ⟨hn, _, hw⟩ := directBits_parts hcode
      have ht := directScalarTy_spec hcode
      have ha := unary_args_heq ht hargs
      rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      dsimp only at ha
      dsimp only [legalOp, Ty.hasFloat]
      simp only [Bool.false_eq_true, ↓reduceIte]
      erw [legalUnaryTree_bits]
      dsimp only [emitMaskToN]
      have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
      have hwn : lt.widenWidth n ≤ n := Nat.le_of_eq hw
      simp only [hn0, Bool.false_eq_true, ↓reduceIte, hwn]
      exact bits1_let_heq lt hrs (fun w => OpCode.neg (.bits w)) hw (tup1_list_heq ht ha) hk
  | and t | or t | xor t =>
    cases t with
    | pair _ _ => cases hcode
    | bool =>
      have ha := binary_args_heq rfl rfl hargs
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      dsimp only at ha
      dsimp only [legalOp]; erw [legalBinTree_bool]
      exact single_direct_let_heq hrs (t := .bool) rfl _
        (eq_of_heq (pair_tup_heq rfl rfl (tup1_heq rfl ha.1) (tup1_heq rfl ha.2))) hk
    | bits n =>
      dsimp only [isDirectLegalOp] at hcode
      obtain ⟨hn, _, hw⟩ := directBits_parts hcode
      have ht := directScalarTy_spec hcode
      obtain ⟨ha, hb⟩ := binary_args_heq ht ht hargs
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      dsimp only at ha hb
      dsimp only [legalOp]; erw [legalBinTree_bits]
      dsimp only [legalBitsArith]
      have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
      simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      let go := fun mk => bits2_let_heq lt hrs mk hw
        (tup1_list_heq ht ha) (tup1_list_heq ht hb) hk
      first
      | exact go (fun w => .and (.bits w)) | exact go (fun w => .or (.bits w))
      | exact go (fun w => .xor (.bits w))
    | float f =>
      dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true] at hcode
      have ha := binary_args_heq rfl rfl hargs
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      dsimp only at ha
      dsimp only [legalOp]; erw [legalBinTree_float]
      dsimp only [legalFloatBit2]
      simp only [hcode.1, ↓reduceIte]
      exact single_direct_let_heq hrs (t := .float f) rfl _
        (eq_of_heq (pair_tup_heq rfl rfl (tup1_heq rfl ha.1) (tup1_heq rfl ha.2))) hk
  | not t =>
    cases t with
    | pair _ _ => cases hcode
    | bool =>
      have ha := unary_args_heq rfl hargs
      rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      dsimp only at ha
      dsimp only [legalOp]; erw [legalUnaryTree_bool]
      exact single_direct_let_heq hrs (t := .bool) rfl _
        (eq_of_heq (single_tup_heq rfl (tup1_heq rfl ha))) hk
    | bits n =>
      dsimp only [isDirectLegalOp] at hcode
      obtain ⟨hn, _, hw⟩ := directBits_parts hcode
      have ht := directScalarTy_spec hcode
      have ha := unary_args_heq ht hargs
      rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      dsimp only at ha
      dsimp only [legalOp]; erw [legalUnaryTree_bits]
      have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
      have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
      simp only [hn0, Bool.false_eq_true, ↓reduceIte, hnw]
      exact bits1_let_heq lt hrs (fun w => OpCode.not (.bits w)) hw (tup1_list_heq ht ha) hk
    | float f =>
      dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true] at hcode
      have ha := unary_args_heq rfl hargs
      rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      dsimp only at ha
      dsimp only [legalOp]; erw [legalUnaryTree_float]
      simp only [hcode.1, ↓reduceIte]
      exact single_direct_let_heq hrs (t := .float f) rfl _
        (eq_of_heq (single_tup_heq rfl (tup1_heq rfl ha))) hk
  | ternlog t imm =>
    cases t with
    | bool | pair _ _ => cases hcode
    | bits n =>
      dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true] at hcode
      obtain ⟨hn, _, hw⟩ := directBits_parts hcode.2
      have ht := directScalarTy_spec hcode.2
      obtain ⟨ha, hb, hc⟩ := ternary_args_heq ht ht ht hargs
      rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
      dsimp only at ha hb hc
      dsimp only [legalOp]; erw [legalTernaryTree_bits]
      dsimp only [emitMaskToN]
      have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
      have hwn : lt.widenWidth n ≤ n := Nat.le_of_eq hw
      simp only [hn0, Bool.false_eq_true, ↓reduceIte, hcode.1, hwn]
      exact bits3_let_heq lt hrs (fun w => OpCode.ternlog (.bits w) imm) hw
        (tup1_list_heq ht ha) (tup1_list_heq ht hb) (tup1_list_heq ht hc) hk
    | float f =>
      dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true] at hcode
      obtain ⟨ha, hb, hc⟩ := ternary_args_heq rfl rfl rfl hargs
      rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
      dsimp only at ha hb hc
      dsimp only [legalOp]; erw [legalTernaryTree_float]
      simp only [hcode.1.1, hcode.1.2, Bool.and_self, ↓reduceIte]
      exact single_direct_let_heq hrs (t := .float f) rfl _
        (eq_of_heq (triple_tup_heq rfl rfl rfl (tup1_heq rfl ha) (tup1_heq rfl hb)
          (tup1_heq rfl hc))) hk
  | fshl n | fshr n =>
    dsimp only [isDirectLegalOp] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode
    have ht := directScalarTy_spec hcode
    obtain ⟨ha, hb, hc⟩ := ternary_args_heq ht ht ht hargs
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    dsimp only at ha hb hc
    dsimp only [legalOp]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
    simp only [hn0, Bool.false_eq_true, ↓reduceIte, hnw]
    exact bits3_let_heq lt hrs _ hw
      (tup1_list_heq ht ha) (tup1_list_heq ht hb) (tup1_list_heq ht hc) hk
  | bswap t =>
    cases t with
    | bool | float _ | pair _ _ => cases hcode
    | bits n =>
      dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true] at hcode
      obtain ⟨hn, _, hw⟩ := directBits_parts hcode.2
      have ht := directScalarTy_spec hcode.2
      have ha := unary_args_heq ht hargs
      rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      dsimp only at ha
      dsimp only [legalOp, legalBswapTree]
      have hbok : (!(Ty.bits n).bswapOk) = false := by simp [hcode.1.2]
      simp only [hbok, Bool.false_eq_true, ↓reduceIte]
      erw [legalUnaryTree_bits]
      have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
      have hn8 : (n == 8) = false := by
        have := hcode.1.1; simpa [bne_iff_ne, ne_eq, beq_iff_eq] using this
      have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
      simp only [hn0, hn8, Bool.false_eq_true, ↓reduceIte, hnw]
      exact bits1_let_heq lt hrs (fun w => OpCode.bswap (.bits w)) hw (tup1_list_heq ht ha) hk
  | clz n | cls n | rbit n | ctz n =>
    dsimp only [isDirectLegalOp] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode
    have ht := directScalarTy_spec hcode
    have ha := unary_args_heq ht hargs
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    dsimp only at ha
    dsimp only [legalOp]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
    simp only [hn0, Bool.false_eq_true, ↓reduceIte, hnw]
    exact bits1_let_heq lt hrs _ hw (tup1_list_heq ht ha) hk
  | popcnt n =>
    dsimp only [isDirectLegalOp] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode
    have ht := directScalarTy_spec hcode
    have ha := unary_args_heq ht hargs
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    dsimp only at ha
    dsimp only [legalOp]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    simp only [hn0, Bool.false_eq_true, ↓reduceIte]
    exact bits1_let_heq lt hrs _ hw (tup1_list_heq ht ha) hk
  | ofBool n =>
    dsimp only [isDirectLegalOp] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode
    have ha := unary_args_heq rfl hargs
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    dsimp only [legalOp]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    simp only [hn0, Bool.false_eq_true, ↓reduceIte]
    refine expr_let_gen_heq hrs rfl (by simp [hw])
      (heq_of_eq1 OpCode.ofBool hw) (single_tup_heq rfl (tup1_heq rfl ha)) fun xs₁ xs₂ hxs => ?_
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    exact hk _ _ (directTupRel_bits1 hw (tup1_heq (congrArg Ty.bits hw) hxs))
  | addc n =>
    dsimp only [isDirectLegalOp] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode
    have ht := directScalarTy_spec hcode
    obtain ⟨ha, hb, hc⟩ := ternary_args_heq ht ht rfl hargs
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    dsimp only at ha hb hc
    dsimp only [legalOp]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
    simp only [hn0, Bool.false_eq_true, ↓reduceIte, hnw]
    refine expr_let_gen_heq hrs (by simp [hw]) (by simp [hw])
      (heq_of_eq1 OpCode.addc hw)
      (triple_tup_heq (congrArg Ty.bits hw) (congrArg Ty.bits hw) rfl
        (tup1_list_heq ht ha) (tup1_list_heq ht hb) (tup1_heq rfl hc))
      fun xs₁ xs₂ hxs => ?_
    rcases xs₁ with ⟨s₁, co₁, ⟨⟩⟩; rcases xs₂ with ⟨s₂, co₂, ⟨⟩⟩
    have hsc : HEq s₁ s₂ ∧ co₁ = co₂ := by
      have hs : HEq (show Tup V [.bits (lt.widenWidth n), .bool] from (s₁, co₁, ()))
          (show Tup V [.bits n, .bool] from (s₂, co₂, ())) := hxs
      have h1 : ∀ {a b : Nat} (h : a = b) {u₁ : V (.bits a)} {u₂ : V (.bits b)} {v₁ v₂ : V .bool},
          HEq (show Tup V [.bits a, .bool] from (u₁, v₁, ()))
              (show Tup V [.bits b, .bool] from (u₂, v₂, ())) →
          HEq u₁ u₂ ∧ v₁ = v₂ := by
        intro a b hab _ _ _ _ heq; subst hab; cases eq_of_heq heq; exact ⟨HEq.rfl, rfl⟩
      exact h1 hw hs
    exact hk _ _ (directTupRel_bitsBool hw hsc.1 hsc.2)
  | subb n =>
    dsimp only [isDirectLegalOp] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode
    have ht := directScalarTy_spec hcode
    obtain ⟨ha, hb, hc⟩ := ternary_args_heq ht ht rfl hargs
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    dsimp only at ha hb hc
    dsimp only [legalOp]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
    simp only [hn0, Bool.false_eq_true, ↓reduceIte, hnw]
    refine expr_let_gen_heq hrs (by simp [hw]) (by simp [hw])
      (heq_of_eq1 OpCode.subb hw)
      (triple_tup_heq (congrArg Ty.bits hw) (congrArg Ty.bits hw) rfl
        (tup1_list_heq ht ha) (tup1_list_heq ht hb) (tup1_heq rfl hc))
      fun xs₁ xs₂ hxs => ?_
    rcases xs₁ with ⟨s₁, co₁, ⟨⟩⟩; rcases xs₂ with ⟨s₂, co₂, ⟨⟩⟩
    have hsc : HEq s₁ s₂ ∧ co₁ = co₂ := by
      have hs : HEq (show Tup V [.bits (lt.widenWidth n), .bool] from (s₁, co₁, ()))
          (show Tup V [.bits n, .bool] from (s₂, co₂, ())) := hxs
      have h1 : ∀ {a b : Nat} (h : a = b) {u₁ : V (.bits a)} {u₂ : V (.bits b)} {v₁ v₂ : V .bool},
          HEq (show Tup V [.bits a, .bool] from (u₁, v₁, ()))
              (show Tup V [.bits b, .bool] from (u₂, v₂, ())) →
          HEq u₁ u₂ ∧ v₁ = v₂ := by
        intro a b hab _ _ _ _ heq; subst hab; cases eq_of_heq heq; exact ⟨HEq.rfl, rfl⟩
      exact h1 hw hs
    exact hk _ _ (directTupRel_bitsBool hw hsc.1 hsc.2)
  | umulw n =>
    dsimp only [isDirectLegalOp] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode
    have ht := directScalarTy_spec hcode
    obtain ⟨ha, hb⟩ := binary_args_heq ht ht hargs
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    dsimp only at ha hb
    dsimp only [legalOp]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
    simp only [hn0, Bool.false_eq_true, ↓reduceIte, hnw]
    refine expr_let_gen_heq hrs (by simp [hw]) (by simp [hw])
      (heq_of_eq1 OpCode.umulw hw)
      (pair_tup_heq (congrArg Ty.bits hw) (congrArg Ty.bits hw)
        (tup1_list_heq ht ha) (tup1_list_heq ht hb))
      fun xs₁ xs₂ hxs => ?_
    rcases xs₁ with ⟨lo₁, hi₁, ⟨⟩⟩; rcases xs₂ with ⟨lo₂, hi₂, ⟨⟩⟩
    have hlh : HEq lo₁ lo₂ ∧ HEq hi₁ hi₂ := by
      have h1 : ∀ {a b : Nat} (h : a = b)
          {u₁ v₁ : V (.bits a)} {u₂ v₂ : V (.bits b)},
          HEq (show Tup V [.bits a, .bits a] from (u₁, v₁, ()))
              (show Tup V [.bits b, .bits b] from (u₂, v₂, ())) →
          HEq u₁ u₂ ∧ HEq v₁ v₂ := by
        intro a b hab _ _ _ _ heq; subst hab; cases eq_of_heq heq; exact ⟨HEq.rfl, HEq.rfl⟩
      exact h1 hw hxs
    exact hk _ _ (directTupRel_bits2 hw hlh.1 hlh.2)
  | smulw n =>
    dsimp only [isDirectLegalOp] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode
    have ht := directScalarTy_spec hcode
    obtain ⟨ha, hb⟩ := binary_args_heq ht ht hargs
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    dsimp only at ha hb
    dsimp only [legalOp]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
    simp only [hn0, Bool.false_eq_true, ↓reduceIte, hnw]
    refine expr_let_gen_heq hrs (by simp [hw]) (by simp [hw])
      (heq_of_eq1 OpCode.smulw hw)
      (pair_tup_heq (congrArg Ty.bits hw) (congrArg Ty.bits hw)
        (tup1_list_heq ht ha) (tup1_list_heq ht hb))
      fun xs₁ xs₂ hxs => ?_
    rcases xs₁ with ⟨lo₁, hi₁, ⟨⟩⟩; rcases xs₂ with ⟨lo₂, hi₂, ⟨⟩⟩
    have hlh : HEq lo₁ lo₂ ∧ HEq hi₁ hi₂ := by
      have h1 : ∀ {a b : Nat} (h : a = b)
          {u₁ v₁ : V (.bits a)} {u₂ v₂ : V (.bits b)},
          HEq (show Tup V [.bits a, .bits a] from (u₁, v₁, ()))
              (show Tup V [.bits b, .bits b] from (u₂, v₂, ())) →
          HEq u₁ u₂ ∧ HEq v₁ v₂ := by
        intro a b hab _ _ _ _ heq; subst hab; cases eq_of_heq heq; exact ⟨HEq.rfl, HEq.rfl⟩
      exact h1 hw hxs
    exact hk _ _ (directTupRel_bits2 hw hlh.1 hlh.2)
  | udiv n | sdiv n | urem n | srem n | udiv0 n | sdiv0 n =>
    dsimp only [isDirectLegalOp] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode
    have ht := directScalarTy_spec hcode
    obtain ⟨ha, hb⟩ := binary_args_heq ht ht hargs
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    dsimp only at ha hb
    dsimp only [legalOp]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
    simp only [hn0, Bool.false_eq_true, ↓reduceIte, hnw]
    exact bits2_let_heq lt hrs _ hw (tup1_list_heq ht ha) (tup1_list_heq ht hb) hk
  | cmp o t m h =>
    subst h
    cases t with
    | float _ | pair _ _ => cases hcode
    | bool =>
      have hbc : lt.boolCmp = true := hcode
      obtain ⟨ha, hb⟩ := binary_args_heq rfl rfl hargs
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      dsimp only [legalOp, Ty.hasFloat]
      simp only [Bool.false_eq_true, ↓reduceIte]
      erw [legalCmpTree_bool]
      simp only [hbc, ↓reduceIte]
      exact single_direct_let_heq hrs (t := .bool) rfl _
        (eq_of_heq (pair_tup_heq rfl rfl (tup1_heq rfl ha) (tup1_heq rfl hb))) hk
    | bits n =>
      dsimp only [isDirectLegalOp] at hcode
      obtain ⟨hn, _, hw⟩ := directBits_parts hcode
      have ht := directScalarTy_spec hcode
      obtain ⟨ha, hb⟩ := binary_args_heq ht ht hargs
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      dsimp only [legalOp, Ty.hasFloat]
      simp only [Bool.false_eq_true, ↓reduceIte]
      erw [legalCmpTree_bits]
      have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
      have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
      simp only [hn0, Bool.false_eq_true, ↓reduceIte, hnw]
      refine expr_let_gen_heq hrs (by simp [hw]) rfl
        (heq_of_eq1 (fun w => OpCode.cmp o (.bits w) .bool rfl) hw)
        (pair_tup_heq (congrArg Ty.bits hw) (congrArg Ty.bits hw)
          (tup1_list_heq ht ha) (tup1_list_heq ht hb))
        fun xs₁ xs₂ hxs => ?_
      rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
      have hreq : r₁ = r₂ := (Prod.mk.inj (eq_of_heq hxs)).1
      subst hreq
      exact hk ((.var r₁, ()), ()) (r₁, ()) (DirectTupRel.single (t := .bool) fun _ => HEq.rfl)
  | select t =>
    cases t with
    | pair _ _ => cases hcode
    | bool =>
      have hbs : lt.boolSelect = true := hcode
      obtain ⟨hc, ha, hb⟩ := ternary_args_heq rfl rfl rfl hargs
      rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      obtain ⟨c₁', hc1⟩ : ∃ x : Arg V .bool, legalArg lt c₁ = (x, ()) := ⟨_, rfl⟩
      dsimp only [legalOp]; rw [hc1] at hc ⊢; dsimp only; erw [legalSelectTree_bool]
      simp only [hbs, ↓reduceIte]
      exact single_direct_let_heq hrs (t := .bool) rfl _
        (eq_of_heq (triple_tup_heq rfl rfl rfl (tup1_heq rfl hc) (tup1_heq rfl ha)
          (tup1_heq rfl hb))) hk
    | bits n =>
      dsimp only [isDirectLegalOp] at hcode
      obtain ⟨_, _, hw⟩ := directBits_parts hcode
      have ht := directScalarTy_spec hcode
      obtain ⟨hc, ha, hb⟩ := ternary_args_heq rfl ht ht hargs
      rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      obtain ⟨c₁', hc1⟩ : ∃ x : Arg V .bool, legalArg lt c₁ = (x, ()) := ⟨_, rfl⟩
      dsimp only [legalOp]; rw [hc1] at hc ⊢; dsimp only; erw [legalSelectTree_bits]
      refine expr_let_gen_heq hrs (by simp [hw]) (by simp [hw])
        (heq_of_eq1 (fun w => OpCode.select (.bits w)) hw)
        (triple_tup_heq rfl (congrArg Ty.bits hw) (congrArg Ty.bits hw)
          (tup1_heq rfl hc) (tup1_list_heq ht ha) (tup1_list_heq ht hb))
        fun xs₁ xs₂ hxs => ?_
      rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
      exact hk _ _ (directTupRel_bits1 hw (tup1_heq (congrArg Ty.bits hw) hxs))
    | float f =>
      obtain ⟨hc, ha, hb⟩ := ternary_args_heq rfl rfl rfl hargs
      rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      obtain ⟨c₁', hc1⟩ : ∃ x : Arg V .bool, legalArg lt c₁ = (x, ()) := ⟨_, rfl⟩
      dsimp only [legalOp]; rw [hc1] at hc ⊢; dsimp only; erw [legalSelectTree_float]
      exact single_direct_let_heq hrs (t := .float f) rfl _
        (eq_of_heq (triple_tup_heq rfl rfl rfl (tup1_heq rfl hc) (tup1_heq rfl ha)
          (tup1_heq rfl hb))) hk
  | zext m n =>
    dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true, decide_eq_true_eq] at hcode
    obtain ⟨hm, _, hwm⟩ := directBits_parts hcode.1.2
    obtain ⟨hn, _, hwn⟩ := directBits_parts hcode.2
    have htm := directScalarTy_spec hcode.1.2
    have ha := unary_args_heq htm hargs
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    dsimp only [legalOp]
    have hgt : ¬(m > n) := Nat.not_lt.mpr (Nat.le_of_lt hcode.1.1)
    have hm0 : (m == 0) = false := beq_false_ne (Nat.ne_of_gt hm)
    have hne : lt.widenWidth m ≠ lt.widenWidth n := by omega
    have hlt : lt.widenWidth m < lt.widenWidth n := by omega
    simp only [hgt, ↓reduceIte, hm0, Bool.false_eq_true, hne, ↓reduceDIte, hlt]
    refine expr_let_gen_heq hrs (by simp [hwm]) (by simp [hwn])
      (heq_of_eq2 OpCode.zext hwm hwn)
      (single_tup_heq (congrArg Ty.bits hwm) (tup1_list_heq htm ha))
      fun xs₁ xs₂ hxs => ?_
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    exact hk _ _ (directTupRel_bits1 hwn (tup1_heq (congrArg Ty.bits hwn) hxs))
  | sext m n =>
    dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true, decide_eq_true_eq] at hcode
    obtain ⟨hm, _, hwm⟩ := directBits_parts hcode.1.2
    obtain ⟨hn, _, hwn⟩ := directBits_parts hcode.2
    have htm := directScalarTy_spec hcode.1.2
    have ha := unary_args_heq htm hargs
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    dsimp only [legalOp, emitSextToW, emitMaskToN]
    have hgt : ¬(m > n) := Nat.not_lt.mpr (Nat.le_of_lt hcode.1.1)
    have hm0 : (m == 0) = false := beq_false_ne (Nat.ne_of_gt hm)
    have hwm_le : lt.widenWidth m ≤ m := Nat.le_of_eq hwm
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    have hwn_le : lt.widenWidth n ≤ n := Nat.le_of_eq hwn
    have hne : lt.widenWidth m ≠ lt.widenWidth n := by omega
    have hlt : lt.widenWidth m < lt.widenWidth n := by omega
    simp only [hgt, ↓reduceIte, hm0, Bool.false_eq_true, hwm_le, Bool.false_or,
      hne, ↓reduceDIte, hlt, hn0, hwn_le]
    refine expr_let_gen_heq hrs (by simp [hwm]) (by simp [hwn])
      (heq_of_eq2 OpCode.sext hwm hwn)
      (single_tup_heq (congrArg Ty.bits hwm) (tup1_list_heq htm ha))
      fun xs₁ xs₂ hxs => ?_
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    exact hk _ _ (directTupRel_bits1 hwn (tup1_heq (congrArg Ty.bits hwn) hxs))
  | trunc m n =>
    dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true, decide_eq_true_eq] at hcode
    obtain ⟨hm, _, hwm⟩ := directBits_parts hcode.1.2
    obtain ⟨hn, _, hwn⟩ := directBits_parts hcode.2
    have htm := directScalarTy_spec hcode.1.2
    have ha := unary_args_heq htm hargs
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    dsimp only [legalOp, emitMaskToN]
    have hgt : ¬(n > m) := Nat.not_lt.mpr (Nat.le_of_lt hcode.1.1)
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    have hne : lt.widenWidth n ≠ lt.widenWidth m := by omega
    have hlt : lt.widenWidth n < lt.widenWidth m := by omega
    have hwn_le : lt.widenWidth n ≤ n := Nat.le_of_eq hwn
    simp only [hgt, ↓reduceIte, hn0, Bool.false_eq_true, hne, ↓reduceDIte, hlt, hwn_le]
    refine expr_let_gen_heq hrs (by simp [hwm]) (by simp [hwn])
      (heq_of_eq2 OpCode.trunc hwm hwn)
      (single_tup_heq (congrArg Ty.bits hwm) (tup1_list_heq htm ha))
      fun xs₁ xs₂ hxs => ?_
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    exact hk _ _ (directTupRel_bits1 hwn (tup1_heq (congrArg Ty.bits hwn) hxs))
  | bitcast t u h =>
    dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true] at hcode
    have hne : t ≠ u := by
      cases hdec : tyDecEq t u with
      | isTrue _ => simp [hdec] at hcode
      | isFalse hne => exact hne
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    have ha' : ∀ (_ : lt.legalSig [t] = [t]),
        HEq (legalArg lt a₁) (show Tup (Arg V) [t] from (a₂, ())) := fun hsig =>
      (tupAppend_nil_heq (legalArg lt a₁)).symm.trans (hargs hsig)
    exact legalOp_bitcast_direct_heq lt hrs h hne hcode.1.2 hcode.2 a₁ a₂ ha' hk
  | fadd t | fsub t | fmul t | fdiv t =>
    cases t with
    | bool | bits _ | pair _ _ => cases hcode
    | float f =>
      have ha := binary_args_heq rfl rfl hargs
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      dsimp only [legalOp, Ty.isFloatTree]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      erw [legalBinTree_float]
      exact single_direct_let_heq hrs (t := .float f) rfl _
        (eq_of_heq (pair_tup_heq rfl rfl (tup1_heq rfl ha.1) (tup1_heq rfl ha.2))) hk
  | ffma t =>
    cases t with
    | bool | bits _ | pair _ _ => cases hcode
    | float f =>
      obtain ⟨ha, hb, hc⟩ := ternary_args_heq rfl rfl rfl hargs
      rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
      dsimp only [legalOp, Ty.isFloatTree]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      erw [legalTernaryTree_float]
      exact single_direct_let_heq hrs (t := .float f) rfl _
        (eq_of_heq (triple_tup_heq rfl rfl rfl (tup1_heq rfl ha) (tup1_heq rfl hb)
          (tup1_heq rfl hc))) hk
  | fsqrt t | fneg t | fabs t =>
    cases t with
    | bool | bits _ | pair _ _ => cases hcode
    | float f =>
      have ha := unary_args_heq rfl hargs
      rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      dsimp only [legalOp, Ty.isFloatTree]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      erw [legalUnaryTree_float]
      exact single_direct_let_heq hrs (t := .float f) rfl _
        (eq_of_heq (single_tup_heq rfl (tup1_heq rfl ha))) hk
  | fcmp o t m h =>
    subst h
    cases t with
    | bool | bits _ | pair _ _ => cases hcode
    | float f =>
      obtain ⟨ha, hb⟩ := binary_args_heq rfl rfl hargs
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      dsimp only [legalOp, Ty.isFloatTree]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      erw [legalFCmpTree_float]
      exact single_direct_let_heq hrs (t := .bool) rfl _
        (eq_of_heq (pair_tup_heq rfl rfl (tup1_heq rfl ha) (tup1_heq rfl hb))) hk
  | fptoui f n =>
    dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode.2
    have ha := unary_args_heq rfl hargs
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    dsimp only [legalOp]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    simp only [hn0, Bool.false_eq_true, ↓reduceIte]
    refine expr_let_gen_heq hrs rfl (by simp [hw])
      (heq_of_eq1 (OpCode.fptoui f) hw) (single_tup_heq rfl (tup1_heq rfl ha))
      fun xs₁ xs₂ hxs => ?_
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    exact hk _ _ (directTupRel_bits1 hw (tup1_heq (congrArg Ty.bits hw) hxs))
  | fptosi f n =>
    dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode.2
    have ha := unary_args_heq rfl hargs
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    dsimp only [legalOp]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
    simp only [hn0, Bool.false_eq_true, ↓reduceIte, hnw]
    refine expr_let_gen_heq hrs rfl (by simp [hw])
      (heq_of_eq1 (OpCode.fptosi f) hw) (single_tup_heq rfl (tup1_heq rfl ha))
      fun xs₁ xs₂ hxs => ?_
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    exact hk _ _ (directTupRel_bits1 hw (tup1_heq (congrArg Ty.bits hw) hxs))
  | uitofp n f =>
    dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode.2
    have ht := directScalarTy_spec hcode.2
    have ha := unary_args_heq ht hargs
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    dsimp only [legalOp]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    simp only [hn0, Bool.false_eq_true, ↓reduceIte]
    refine expr_let_gen_heq hrs (by simp [hw]) rfl
      (heq_of_eq1 (fun w => OpCode.uitofp w f) hw)
      (single_tup_heq (congrArg Ty.bits hw) (tup1_list_heq ht ha)) fun xs₁ xs₂ hxs => ?_
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    have hreq : r₁ = r₂ := (Prod.mk.inj (eq_of_heq hxs)).1
    subst hreq
    exact hk ((.var r₁, ()), ()) (r₁, ()) (DirectTupRel.single (t := .float f) fun _ => HEq.rfl)
  | sitofp n f =>
    dsimp only [isDirectLegalOp] at hcode; simp only [Bool.and_eq_true] at hcode
    obtain ⟨hn, _, hw⟩ := directBits_parts hcode.2
    have ht := directScalarTy_spec hcode.2
    have ha := unary_args_heq ht hargs
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    dsimp only [legalOp, emitSextToW]
    have hn0 : (n == 0) = false := beq_false_ne (Nat.ne_of_gt hn)
    have hwn : lt.widenWidth n ≤ n := Nat.le_of_eq hw
    simp only [hn0, Bool.false_eq_true, ↓reduceIte, hwn, Bool.false_or]
    refine expr_let_gen_heq hrs (by simp [hw]) rfl
      (heq_of_eq1 (fun w => OpCode.sitofp w f) hw)
      (single_tup_heq (congrArg Ty.bits hw) (tup1_list_heq ht ha)) fun xs₁ xs₂ hxs => ?_
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    have hreq : r₁ = r₂ := (Prod.mk.inj (eq_of_heq hxs)).1
    subst hreq
    exact hk ((.var r₁, ()), ()) (r₁, ()) (DirectTupRel.single (t := .float f) fun _ => HEq.rfl)
  | fcvt f g =>
    have ha := unary_args_heq rfl hargs
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    dsimp only [legalOp]
    exact single_direct_let_heq hrs (t := .float g) rfl _
      (eq_of_heq (single_tup_heq rfl (tup1_heq rfl ha))) hk
  | mkpair _ _ | unpair _ _ | blend _ _ _ | shufd _ _ | shufb _ | alignr _ _ | blendw _ _
  | sha256rnds2 | sha256msg1 | sha256msg2 => cases hcode

private theorem castArgBits_heq {V : Ty → Type} {m n : Nat} (h : m = n) (x : Arg V (.bits m)) :
    HEq (castArgBits h x) x := by
  subst h; exact HEq.rfl

mutual
private theorem legalExpr_denote_heq (lt : LegalTarget) (V : Ty → Type) (L : List Ty → Type)
    {rs : List Ty} (hrs : lt.legalSig rs = rs) :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs₁ : List ((t : Ty) × LVar lt V t)} → {vs₂ : List ((t : Ty) × V t)} →
    {ls₁ : List ((ts : List Ty) × LLab lt L ts)} → {ls₂ : List ((ts : List Ty) × L ts)} →
    DirectValCtx lt V Γ vs₁ vs₂ → DirectLabCtx lt L Δ ls₁ ls₂ →
    tf.wfCheck Γ Δ = true → tf.isLegalDirect lt = true →
    HEq (legalExpr lt (denote (LVar lt V) (LLab lt L) tf vs₁ ls₁))
        (denote V L tf vs₂ ls₂)
  | .let_ (ts := ts) ⟨code, args⟩ k, Γ, Δ, vs₁, vs₂, ls₁, ls₂, hvs, hls, hwf, hdir => by
    dsimp only [TFlat.wfCheck, TFlat.isLegalDirect] at hwf hdir
    simp only [Bool.and_eq_true] at hwf hdir
    obtain ⟨args₁, args₂, ha1, ha2, hargs⟩ := directValCtx_denoteArgs hvs args hwf.1
    dsimp only [denote]; rw [ha1, ha2]; dsimp only [legalExpr]
    exact legalOp_direct_heq lt hrs code hdir.1 args₁ args₂ hargs fun xs₁ xs₂ hxs =>
      legalExpr_denote_heq lt V L hrs k (hvs.push hxs) hls hwf.2 hdir.2
  | .load t a k, Γ, Δ, vs₁, vs₂, ls₁, ls₂, hvs, hls, hwf, hdir => by
    dsimp only [TFlat.wfCheck, TFlat.isLegalDirect] at hwf hdir
    simp only [Bool.and_eq_true, beq_iff_eq] at hwf hdir
    obtain ⟨a₁, a₂, ha1, ha2, ha⟩ := directValCtx_denoteArg hvs a hwf.1
    dsimp only [denote]; rw [ha1, ha2]; dsimp only [legalExpr]
    have h64 : lt.widenWidth 64 = 64 := hdir.1.1
    simp only [h64, ↓reduceDIte]
    have hptr : HEq (castArgBits h64 (legalArg lt a₁).1) a₂ := by
      have ht64 : lt.legalTys i64 = [i64] := by simp [LegalTarget.legalTys, h64]
      exact (castArgBits_heq h64 _).trans (tup1_list_heq ht64 (ha ht64))
    have hptr_eq : castArgBits h64 (legalArg lt a₁).1 = a₂ := eq_of_heq hptr
    rw [hptr_eq]
    cases t with
    | pair _ _ => cases hdir.1.2
    | bool =>
      dsimp only [legalLoad]
      refine expr_load_heq hrs rfl rfl fun v₁ v₂ hv => ?_
      cases eq_of_heq hv
      exact legalExpr_denote_heq lt V L hrs k (.cons (fun _ => HEq.rfl) hvs) hls hwf.2 hdir.2
    | float f =>
      dsimp only [legalLoad]
      refine expr_load_heq hrs rfl rfl fun v₁ v₂ hv => ?_
      cases eq_of_heq hv
      exact legalExpr_denote_heq lt V L hrs k (.cons (fun _ => HEq.rfl) hvs) hls hwf.2 hdir.2
    | bits n =>
      obtain ⟨_, _, hw⟩ := directBits_parts hdir.1.2
      have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
      erw [legalLoad_bits]
      simp only [hnw, ↓reduceIte]
      refine expr_load_heq hrs (congrArg Ty.bits hw) rfl fun v₁ v₂ hv => ?_
      refine legalExpr_denote_heq lt V L hrs k (.cons (fun ht' => ?_) hvs) hls hwf.2 hdir.2
      exact single_tup_heq (congrArg Ty.bits hw) (var_bits_heq hw hv)
  | .store (t := t) v a k, Γ, Δ, vs₁, vs₂, ls₁, ls₂, hvs, hls, hwf, hdir => by
    dsimp only [TFlat.wfCheck, TFlat.isLegalDirect] at hwf hdir
    simp only [Bool.and_eq_true, beq_iff_eq] at hwf hdir
    obtain ⟨v₁, v₂, hv1, hv2, hv⟩ := directValCtx_denoteArg hvs v hwf.1.1
    obtain ⟨a₁, a₂, ha1, ha2, ha⟩ := directValCtx_denoteArg hvs a hwf.1.2
    dsimp only [denote]; rw [hv1, ha1, hv2, ha2]; dsimp only [legalExpr]
    have h64 : lt.widenWidth 64 = 64 := hdir.1.1
    simp only [h64, ↓reduceDIte]
    have hptr : castArgBits h64 (legalArg lt a₁).1 = a₂ := by
      have ht64 : lt.legalTys i64 = [i64] := by simp [LegalTarget.legalTys, h64]
      exact eq_of_heq ((castArgBits_heq h64 _).trans (tup1_list_heq ht64 (ha ht64)))
    rw [hptr]
    have hk := legalExpr_denote_heq lt V L hrs k hvs hls hwf.2 hdir.2
    cases t with
    | pair _ _ => cases hdir.1.2
    | bool =>
      erw [legalStore_bool]
      have hv_heq : (legalArg lt v₁).1 = v₂ := eq_of_heq (tup1_heq rfl (hv rfl))
      rw [hv_heq]; exact expr_store_heq hrs rfl HEq.rfl rfl hk
    | float f =>
      erw [legalStore_float]
      have hv_heq : (legalArg lt v₁).1 = v₂ := eq_of_heq (tup1_heq rfl (hv rfl))
      rw [hv_heq]; exact expr_store_heq hrs rfl HEq.rfl rfl hk
    | bits n =>
      obtain ⟨_, _, hw⟩ := directBits_parts hdir.1.2
      have hnw : (n == lt.widenWidth n) = true := beq_iff_eq.mpr hw.symm
      erw [legalStore_bits]
      simp only [hnw, ↓reduceIte]
      have hlt : lt.legalTys (.bits n) = [.bits n] := directScalarTy_spec hdir.1.2
      have hv_heq : HEq (legalArg lt v₁).1 v₂ := tup1_list_heq hlt (hv hlt)
      exact expr_store_heq hrs (congrArg Ty.bits hw) hv_heq rfl hk
  | .call f (as := as) bs args k, Γ, Δ, vs₁, vs₂, ls₁, ls₂, hvs, hls, hwf, hdir => by
    dsimp only [TFlat.wfCheck, TFlat.isLegalDirect] at hwf hdir
    simp only [Bool.and_eq_true] at hwf hdir
    obtain ⟨args₁, args₂, ha1, ha2, hargs⟩ := directValCtx_denoteArgs hvs args hwf.1
    have has := directScalarTy_sig_spec hdir.1.1
    have hbs := directScalarTy_sig_spec hdir.1.2
    dsimp only [denote]; rw [ha1, ha2]; dsimp only [legalExpr]
    refine expr_call_heq hrs f has hbs (hargs has) fun xs₁ xs₂ hxs => ?_
    exact legalExpr_denote_heq lt V L hrs k (DirectValCtx.push_splitParams hbs hxs hvs) hls
      hwf.2 hdir.2
  | .jnz c t e, Γ, Δ, vs₁, vs₂, ls₁, ls₂, hvs, hls, hwf, hdir => by
    dsimp only [TFlat.wfCheck, TFlat.isLegalDirect] at hwf hdir
    simp only [Bool.and_eq_true] at hwf hdir
    obtain ⟨c₁, c₂, hc1, hc2, hc⟩ := directValCtx_denoteArg hvs c hwf.1.1
    dsimp only [denote]; rw [hc1, hc2]; dsimp only [legalExpr]
    have hc_eq : (legalArg lt c₁).1 = c₂ := eq_of_heq (tup1_heq rfl (hc rfl))
    rw [hc_eq]
    exact expr_jnz_heq hrs rfl
      (legalExpr_denote_heq lt V L hrs t hvs hls hwf.1.2 hdir.1)
      (legalExpr_denote_heq lt V L hrs e hvs hls hwf.2 hdir.2)
  | .jump (ts := ts) j args, Γ, Δ, vs₁, vs₂, ls₁, ls₂, hvs, hls, hwf, hdir => by
    dsimp only [TFlat.wfCheck, TFlat.isLegalDirect] at hwf hdir
    simp only [Bool.and_eq_true] at hwf
    obtain ⟨l₁, l₂, hl1, hl2, hl⟩ := directLabCtx_lookupL hls j hwf.1
    obtain ⟨args₁, args₂, ha1, ha2, hargs⟩ := directValCtx_denoteArgs hvs args hwf.2
    have hts := directScalarTy_sig_spec hdir
    dsimp only [denote]; rw [hl1, ha1, hl2, ha2]; dsimp only [legalExpr]
    exact expr_jump_heq hrs hts (hl hts) (hargs hts)
  | .ret vs', Γ, _, vs₁, vs₂, _, _, hvs, _, hwf, _ => by
    obtain ⟨args₁, args₂, ha1, ha2, hargs⟩ := directValCtx_denoteArgs hvs vs' hwf
    dsimp only [denote]; rw [ha1, ha2]; dsimp only [legalExpr]
    exact expr_ret_heq hrs (hargs hrs)
  | .exit f (as := as) args, Γ, _, vs₁, vs₂, _, _, hvs, _, hwf, hdir => by
    obtain ⟨args₁, args₂, ha1, ha2, hargs⟩ := directValCtx_denoteArgs hvs args hwf
    have has := directScalarTy_sig_spec hdir
    dsimp only [denote]; rw [ha1, ha2]; dsimp only [legalExpr]
    exact expr_exit_heq hrs f has (hargs has)
  | .hlt, _, _, _, _, _, _, _, _, _, _ => expr_hlt_heq hrs
  | .group (sig := sig) bodies k, Γ, Δ, vs₁, vs₂, ls₁, ls₂, hvs, hls, hwf, hdir => by
    dsimp only [TFlat.wfCheck, TFlat.isLegalDirect] at hwf hdir
    simp only [Bool.and_eq_true] at hwf hdir
    have hsig := directScalarTy_sig_map_spec hdir.1.1
    dsimp only [denote, legalExpr]
    refine expr_group_heq hrs hsig (fun Js₁ Js₂ hJs => ?_) (fun Js₁ Js₂ hJs => ?_)
    · exact legalBlocks_denoteB_heq lt V L hrs bodies hsig hvs
        (DirectLabCtx.push_tupLiftMap hsig hJs hls) hwf.1 hdir.1.2
    · exact legalExpr_denote_heq lt V L hrs k hvs
        (DirectLabCtx.push_tupLiftMap hsig hJs hls) hwf.2 hdir.2

private theorem legalBlocks_denoteB_heq (lt : LegalTarget) (V : Ty → Type) (L : List Ty → Type)
    {rs : List Ty} (hrs : lt.legalSig rs = rs) :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → (hsig : sig.map lt.legalSig = sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs₁ : List ((t : Ty) × LVar lt V t)} → {vs₂ : List ((t : Ty) × V t)} →
    {ls₁ : List ((ts : List Ty) × LLab lt L ts)} → {ls₂ : List ((ts : List Ty) × L ts)} →
    DirectValCtx lt V Γ vs₁ vs₂ → DirectLabCtx lt L Δ ls₁ ls₂ →
    tb.wfCheck Γ Δ = true → tb.isLegalDirect lt = true →
    HEq (legalBlocks lt (denoteB (LVar lt V) (LLab lt L) tb vs₁ ls₁))
        (denoteB V L tb vs₂ ls₂)
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _ => blocks_nil_heq hrs
  | _, .cons (ts := ts) b bs, hsig, Γ, Δ, vs₁, vs₂, ls₁, ls₂, hvs, hls, hwf, hdir => by
    simp only [List.map_cons, List.cons.injEq] at hsig
    dsimp only [TBlocks.wfCheck, TBlocks.isLegalDirect] at hwf hdir
    simp only [Bool.and_eq_true] at hwf hdir
    have hts := hsig.1
    dsimp only [denoteB, legalBlocks]
    refine blocks_cons_heq hrs hts hsig.2 (fun xs₁ xs₂ hxs => ?_) ?_
    · exact legalExpr_denote_heq lt V L hrs b (DirectValCtx.push_splitParams hts hxs hvs) hls
        hwf.1 hdir.1.2
    · exact legalBlocks_denoteB_heq lt V L hrs bs hsig.2 hvs hls hwf.2 hdir.2
end

private theorem levels_heq {α : Type} {a b : List α} (h : a = b) (n : Nat) :
    HEq (Tup.levels a n) (Tup.levels b n) := by
  subst h; exact HEq.rfl

private theorem toTFlat_heq {rs₁ rs₂ : List Ty} (hrs : rs₁ = rs₂)
    {e₁ : Expr K KL rs₁} {e₂ : Expr K KL rs₂} (he : HEq e₁ e₂)
    {nv₁ nv₂ nl₁ nl₂ : Nat} (hnv : nv₁ = nv₂) (hnl : nl₁ = nl₂) :
    HEq (toTFlat e₁ nv₁ nl₁) (toTFlat e₂ nv₂ nl₂) := by
  subst hrs; subst hnv; subst hnl; cases eq_of_heq he; exact HEq.rfl

/-- Exact kernel simulation: `legalFlat lt tf = reifyFunc (Func.legal lt (denoteFunc tf))`
whenever `tf` passes `wfCheck` (`std3` axioms only). -/
theorem legalFlat_eq (lt : LegalTarget) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    legalFlat lt (as := as) tf = reifyFunc (Func.legal lt (denoteFunc (as := as) tf)) := by
  dsimp only [legalFlat]
  cases ha : listTyDecEq (lt.legalSig as) as with
  | isFalse _ => rfl
  | isTrue has =>
    cases hr : listTyDecEq (lt.legalSig rs) rs with
    | isFalse _ => rfl
    | isTrue hrs =>
      cases hd : tf.isLegalDirect lt with
      | false => rfl
      | true =>
        have hBody := legalExpr_denote_heq lt K KL hrs tf
          (DirectValCtx.push_splitParams has (levels_heq has 0) .nil) .nil hwf hd
        have hFlat : HEq (reifyFunc (Func.legal lt (denoteFunc (as := as) tf)))
            (reifyFunc (denoteFunc (as := as) tf)) :=
          toTFlat_heq hrs hBody (congrArg List.length has) rfl
        rw [reifyFunc_denoteFunc_eq (as := as) tf hwf] at hFlat
        exact eq_of_heq ((cast_heq (congrArg TFlat hrs.symm) tf).trans hFlat.symm)

end LeanQbe.T
