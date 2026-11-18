module

public import LeanQbe.T.LegalLemmas

/-!
# Target legality proofs for `LeanQbe.T.Legal` (Part 1: Invariants, Bridges, Memory & Scalar Helpers)

Proves `TFlat.isLegal` context invariants (`CtxExtends`, `LvlOk`, `ArgNormal`, `ArgsNormal`,
`CLegal`, `DLegal`), pack/unpack bridges, single-instruction emitters, bit/bool/word64 helpers,
and `legalLoad`/`legalStore` legality.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalIsLegal

/-! ## Section 5: `Func.legal_isLegal` (Decidable `Legal` target invariant) -/

/-! ### Simp / equation helpers for `listGet?`, `pushTypes`, `toTFlat`, `TFlat.isLegal` -/

theorem listGet?_append_add {α : Type} : (ext xs : List α) → (k : Nat) →
    listGet? (ext ++ xs) (ext.length + k) = listGet? xs k
  | [], xs, k => by simp
  | _ :: ext, xs, k => by
    simp only [List.cons_append, List.length_cons, Nat.succ_add, listGet?]
    exact listGet?_append_add ext xs k

theorem pushTypes_eq_reverse_append {α : Type} : (xs acc : List α) →
    pushTypes xs acc = xs.reverse ++ acc
  | [], _ => rfl
  | a :: as, acc => by
    simp only [pushTypes, pushTypes_eq_reverse_append as (a :: acc), List.reverse_cons,
      List.append_assoc, List.cons_append, List.nil_append]

theorem pushTypes_length {α : Type} (xs acc : List α) :
    (pushTypes xs acc).length = xs.length + acc.length := by
  rw [pushTypes_eq_reverse_append, List.length_append, List.length_reverse]

theorem pushNormal_length (ts : List Ty) (Γ : List (Ty × VarKind)) :
    (pushNormal ts Γ).length = ts.length + Γ.length := by
  simp only [pushNormal, pushTypes_length, List.length_map]

@[simp] theorem Tup.levels_nil {α : Type} (n : Nat) : Tup.levels ([] : List α) n = () := rfl
@[simp] theorem Tup.levels_cons {α : Type} (a : α) (as : List α) (n : Nat) :
    Tup.levels (a :: as) n = (n, Tup.levels as (n + 1)) := rfl

@[simp] theorem tupLiftMap_nil {α β : Type} (g : α → β) (f : β → Type) :
    tupLiftMap g f (as := []) () = () := rfl
@[simp] theorem tupLiftMap_cons {α β : Type} (g : α → β) (f : β → Type) {a : α} {as : List α}
    (x : f (g a)) (xs : Tup f (as.map g)) :
    tupLiftMap g f (as := a :: as) (x, xs) = (x, tupLiftMap g f xs) := rfl

@[simp] theorem tupLiftMap_levels_cons {α β : Type} (g : α → β) (a : α) (as : List α) (n : Nat) :
    tupLiftMap g (fun _ => Nat) (Tup.levels ((a :: as).map g) n) =
      ((n : Nat), tupLiftMap g (fun _ => Nat) (Tup.levels (as.map g) (n + 1))) := rfl

@[simp] theorem idxArgs_nil (nv : Nat) : idxArgs nv (ts := []) () = () := rfl
@[simp] theorem idxArgs_cons (nv : Nat) {t : Ty} {ts : List Ty} (x : Arg K t) (xs : Tup (Arg K) ts) :
    idxArgs nv (ts := t :: ts) (x, xs) = (idxArg nv x, idxArgs nv xs) := rfl

@[simp] theorem idxArgs_single (nv : Nat) {t : Ty} (x : Arg K t) :
    idxArgs nv (ts := [t]) (x, ()) = (idxArg nv x, ()) := rfl

@[simp] theorem idxArgs_pair (nv : Nat) {t₁ t₂ : Ty} (x₁ : Arg K t₁) (x₂ : Arg K t₂) :
    idxArgs nv (ts := [t₁, t₂]) (x₁, x₂, ()) = (idxArg nv x₁, idxArg nv x₂, ()) := rfl

@[simp] theorem idxArgs_triple (nv : Nat) {t₁ t₂ t₃ : Ty} (x₁ : Arg K t₁) (x₂ : Arg K t₂) (x₃ : Arg K t₃) :
    idxArgs nv (ts := [t₁, t₂, t₃]) (x₁, x₂, x₃, ()) = (idxArg nv x₁, idxArg nv x₂, idxArg nv x₃, ()) := rfl

@[simp] theorem checkLegalArgs_nil (Γ : List (Ty × VarKind)) : checkLegalArgs Γ (ts := []) () = true := rfl
@[simp] theorem checkLegalArgs_cons (Γ : List (Ty × VarKind)) {t : Ty} {ts : List Ty}
    (x : Arg K t) (xs : Tup (Arg K) ts) :
    checkLegalArgs Γ (ts := t :: ts) (x, xs) = (checkLegalArg Γ t x && checkLegalArgs Γ xs) := rfl

theorem checkLegalArgs_single (Γ : List (Ty × VarKind)) {t : Ty} (x : Arg K t) :
    checkLegalArgs Γ (ts := [t]) (x, ()) = checkLegalArg Γ t x := by
  change (checkLegalArg Γ t x && checkLegalArgs Γ (ts := []) ()) = checkLegalArg Γ t x
  rw [checkLegalArgs_nil, Bool.and_true]

theorem checkLegalArgs_pair (Γ : List (Ty × VarKind)) {t₁ t₂ : Ty} (x₁ : Arg K t₁) (x₂ : Arg K t₂) :
    checkLegalArgs Γ (ts := [t₁, t₂]) (x₁, x₂, ()) = (checkLegalArg Γ t₁ x₁ && checkLegalArg Γ t₂ x₂) := by
  change (checkLegalArg Γ t₁ x₁ && (checkLegalArg Γ t₂ x₂ && checkLegalArgs Γ (ts := []) ())) = _
  rw [checkLegalArgs_nil, Bool.and_true]

theorem checkLegalArgs_triple (Γ : List (Ty × VarKind)) {t₁ t₂ t₃ : Ty}
    (x₁ : Arg K t₁) (x₂ : Arg K t₂) (x₃ : Arg K t₃) :
    checkLegalArgs Γ (ts := [t₁, t₂, t₃]) (x₁, x₂, x₃, ()) =
      (checkLegalArg Γ t₁ x₁ && checkLegalArg Γ t₂ x₂ && checkLegalArg Γ t₃ x₃) := by
  change (checkLegalArg Γ t₁ x₁ && (checkLegalArg Γ t₂ x₂ && (checkLegalArg Γ t₃ x₃ && checkLegalArgs Γ (ts := []) ()))) = _
  rw [checkLegalArgs_nil, Bool.and_true, Bool.and_assoc]

@[simp] theorem toTFlat_let {rs ts : List Ty} (op : Op K ts) (k : Tup K ts → Expr K KL rs) (nv nl : Nat) :
    toTFlat (.let_ op k) nv nl =
      .let_ { sig := op.sig, code := op.code, args := idxArgs nv op.args }
        (toTFlat (k (Tup.levels ts nv)) (nv + ts.length) nl) := rfl

@[simp] theorem toTFlat_load {rs : List Ty} (t : Ty) (a : Arg K i64) (k : K t → Expr K KL rs) (nv nl : Nat) :
    toTFlat (.load t a k) nv nl = .load t (idxArg nv a) (toTFlat (k nv) (nv + 1) nl) := rfl

@[simp] theorem toTFlat_store {rs : List Ty} (t : Ty) (v : Arg K t) (a : Arg K i64) (k : Expr K KL rs) (nv nl : Nat) :
    toTFlat (.store v a k) nv nl = .store (idxArg nv v) (idxArg nv a) (toTFlat k nv nl) := rfl

@[simp] theorem toTFlat_call {rs : List Ty} (f : String) {as bs : List Ty}
    (args : Tup (Arg K) as) (k : Tup K bs → Expr K KL rs) (nv nl : Nat) :
    toTFlat (.call (bs := bs) f args k) nv nl =
      .call f bs (idxArgs nv args) (toTFlat (k (Tup.levels bs nv)) (nv + bs.length) nl) := rfl

@[simp] theorem toTFlat_jnz {rs : List Ty} (c : Arg K .bool) (t e : Expr K KL rs) (nv nl : Nat) :
    toTFlat (.jnz c t e) nv nl = .jnz (idxArg nv c) (toTFlat t nv nl) (toTFlat e nv nl) := rfl

@[simp] theorem toTFlat_jump {rs ts : List Ty} (j : KL ts) (args : Tup (Arg K) ts) (nv nl : Nat) :
    toTFlat (.jump (rs := rs) j args) nv nl = .jump (if j < nl then nl - 1 - j else nl) (idxArgs nv args) := rfl

@[simp] theorem toTFlat_ret {rs : List Ty} (vs : Tup (Arg K) rs) (nv nl : Nat) :
    toTFlat (.ret vs) nv nl = .ret (idxArgs nv vs) := rfl

@[simp] theorem toTFlat_exit {rs as : List Ty} (f : String) (args : Tup (Arg K) as) (nv nl : Nat) :
    toTFlat (.exit (rs := rs) f args) nv nl = .exit f (idxArgs nv args) := rfl

@[simp] theorem toTFlat_hlt {rs : List Ty} (nv nl : Nat) :
    toTFlat (.hlt (V := K) (L := KL) (rs := rs)) nv nl = .hlt := rfl

@[simp] theorem toTFlat_group {rs : List Ty} {sig : List (List Ty)}
    (bodies : Tup KL sig → Blocks K KL rs sig) (k : Tup KL sig → Expr K KL rs) (nv nl : Nat) :
    toTFlat (.group bodies k) nv nl =
      .group (toTBlocks (bodies (Tup.levels sig nl)) nv (nl + sig.length))
             (toTFlat (k (Tup.levels sig nl)) nv (nl + sig.length)) := rfl

@[simp] theorem toTBlocks_nil {rs : List Ty} (nv nl : Nat) :
    toTBlocks (.nil : Blocks K KL rs []) nv nl = .nil := rfl

@[simp] theorem toTBlocks_cons {rs ts : List Ty} {sig : List (List Ty)}
    (b : Tup K ts → Expr K KL rs) (bs : Blocks K KL rs sig) (nv nl : Nat) :
    toTBlocks (.cons b bs) nv nl = .cons (toTFlat (b (Tup.levels ts nv)) (nv + ts.length) nl) (toTBlocks bs nv nl) := rfl

def OpCode.isPackBridge : {as rs : List Ty} → OpCode as rs → Bool
  | _, _, .unpair _ _ => true
  | _, _, .mkpair _ _ => true
  | _, _, _ => false

theorem TFlat.isLegal_let_of_normal (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs ts : List Ty} (op : Op K ts) (k : TFlat rs)
    (hne : op.code.isPackBridge = false) :
    (TFlat.let_ op k).isLegal target Γ Δ =
      (target.isLegalOp op.code (isUniformImmShift op.code op.args) && target.isLegalSig ts &&
        checkLegalArgs Γ op.args && k.isLegal target (pushNormal ts Γ) Δ) := by
  rcases op with @⟨sig, code, args⟩
  cases code <;>
    (try (dsimp only [OpCode.isPackBridge] at hne; contradiction)) <;>
    dsimp only [TFlat.isLegal, TFlat.isLegal._f]

theorem TFlat.isLegal_let_unpair (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs : List Ty} (a b : Ty) (p : Arg K (.pair a b)) (k : TFlat rs) :
    (TFlat.let_ { sig := [.pair a b], code := .unpair a b, args := (p, ()) } k).isLegal target Γ Δ =
      (target.allowPackBridge && target.hasLegalLeaves (.pair a b) &&
        (match p with
         | .var idx => checkVarKind Γ (.pair a b) (fun vk => (vk == .normal && target.isLegalTy (.pair a b)) || vk == .unpackedBridge) idx
         | .imm _ => false) &&
        k.isLegal target (pushTypes [(a, if target.isLegalTy a then .normal else .unpackedBridge),
          (b, if target.isLegalTy b then .normal else .unpackedBridge)] Γ) Δ) := rfl

theorem TFlat.isLegal_let_mkpair (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs : List Ty} (a b : Ty) (va : Arg K a) (vb : Arg K b) (k : TFlat rs) :
    (TFlat.let_ { sig := [a, b], code := .mkpair a b, args := (va, vb, ()) } k).isLegal target Γ Δ =
      (target.allowPackBridge && target.hasLegalLeaves (.pair a b) &&
        (match va with
         | .var idx => checkVarKind Γ a (fun vk => (vk == .normal && target.isLegalTy a) || vk == .packedBridge) idx
         | .imm _ => target.isLegalTy a) &&
        (match vb with
         | .var idx => checkVarKind Γ b (fun vk => (vk == .normal && target.isLegalTy b) || vk == .packedBridge) idx
         | .imm _ => target.isLegalTy b) &&
        k.isLegal target ((.pair a b, if target.isLegalTy (.pair a b) then .normal else .packedBridge) :: Γ) Δ) := rfl

@[simp] theorem TFlat.isLegal_load (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs : List Ty} (t : Ty) (a : Arg K i64) (k : TFlat rs) :
    (TFlat.load t a k).isLegal target Γ Δ =
      (target.isLegalTy t && checkLegalArg Γ i64 a && k.isLegal target ((t, .normal) :: Γ) Δ) := rfl

@[simp] theorem TFlat.isLegal_store (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs : List Ty} (t : Ty) (v : Arg K t) (a : Arg K i64) (k : TFlat rs) :
    (TFlat.store v a k).isLegal target Γ Δ =
      (target.isLegalTy t && checkLegalArg Γ t v && checkLegalArg Γ i64 a && k.isLegal target Γ Δ) := rfl

@[simp] theorem TFlat.isLegal_call (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs as : List Ty} (f : String) (bs : List Ty) (args : Tup (Arg K) as) (k : TFlat rs) :
    (TFlat.call f bs args k).isLegal target Γ Δ =
      (target.isLegalSig as && target.isLegalSig bs && checkLegalArgs Γ args && k.isLegal target (pushNormal bs Γ) Δ) := rfl

@[simp] theorem TFlat.isLegal_jnz (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs : List Ty} (c : Arg K .bool) (t e : TFlat rs) :
    (TFlat.jnz c t e).isLegal target Γ Δ =
      (checkLegalArg Γ .bool c && t.isLegal target Γ Δ && e.isLegal target Γ Δ) := rfl

@[simp] theorem TFlat.isLegal_jump (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs ts : List Ty} (j : Nat) (args : Tup (Arg K) ts) :
    (TFlat.jump (rs := rs) (ts := ts) j args).isLegal target Γ Δ =
      (target.isLegalSig ts &&
        (match listGet? Δ j with
         | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
         | none => false) &&
        checkLegalArgs Γ args) := rfl

@[simp] theorem TFlat.isLegal_ret (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs : List Ty} (vs : Tup (Arg K) rs) :
    (TFlat.ret vs).isLegal target Γ Δ = (target.isLegalSig rs && checkLegalArgs Γ vs) := rfl

@[simp] theorem TFlat.isLegal_exit (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs as : List Ty} (f : String) (args : Tup (Arg K) as) :
    (TFlat.exit (rs := rs) f args).isLegal target Γ Δ = (target.isLegalSig as && checkLegalArgs Γ args) := rfl

@[simp] theorem TFlat.isLegal_hlt (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs : List Ty} :
    (TFlat.hlt (rs := rs)).isLegal target Γ Δ = true := rfl

@[simp] theorem TFlat.isLegal_group (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs : List Ty} {sig : List (List Ty)} (bodies : TBlocks rs sig) (k : TFlat rs) :
    (TFlat.group bodies k).isLegal target Γ Δ =
      (sig.all target.isLegalSig && bodies.isLegal target Γ (pushTypes sig Δ) && k.isLegal target Γ (pushTypes sig Δ)) := rfl

@[simp] theorem TBlocks.isLegal_nil (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs : List Ty} :
    (TBlocks.nil (rs := rs)).isLegal target Γ Δ = true := rfl

@[simp] theorem TBlocks.isLegal_cons (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {rs ts : List Ty} {sig : List (List Ty)} (b : TFlat rs) (bs : TBlocks rs sig) :
    (TBlocks.cons (ts := ts) b bs).isLegal target Γ Δ =
      (target.isLegalSig ts && b.isLegal target (pushNormal ts Γ) Δ && bs.isLegal target Γ Δ) := rfl

theorem supportsTy_of_hasLegalLeaves {target : LegalTarget} (hv : target.valid = true) :
    ∀ {t : Ty}, target.hasLegalLeaves t = true → target.supportsTy t = true
  | .bool, _ => rfl
  | .bits n, hl => by
    have hmem : n ∈ target.bitWidths := by simpa [LegalTarget.hasLegalLeaves] using hl
    have h64 := (valid_bitWidth_spec hv hmem).2.2
    exact supportsTy_bits_iff.2 ⟨⟨n, hmem, Nat.le_refl n⟩, h64⟩
  | .float f, hl => by
    have hmem : f ∈ target.floatFmts := by simpa [LegalTarget.hasLegalLeaves] using hl
    have h64 := (valid_float_spec hv hmem).2
    simp [LegalTarget.supportsTy, hmem, h64]
  | .pair a b, hl => by
    simp only [LegalTarget.hasLegalLeaves, LegalTarget.supportsTy, Bool.and_eq_true] at hl ⊢
    exact ⟨supportsTy_of_hasLegalLeaves hv hl.1, supportsTy_of_hasLegalLeaves hv hl.2⟩

/-! ### Context extensions and normal invariants -/

def CtxExtends {α : Type} (Γ Γ' : List α) : Prop :=
  ∃ ext : List α, Γ' = ext ++ Γ

theorem CtxExtends.refl {α : Type} (Γ : List α) : CtxExtends Γ Γ := ⟨[], rfl⟩

theorem CtxExtends.trans {α : Type} {Γ₁ Γ₂ Γ₃ : List α}
    (h1 : CtxExtends Γ₁ Γ₂) (h2 : CtxExtends Γ₂ Γ₃) : CtxExtends Γ₁ Γ₃ := by
  rcases h1 with ⟨e1, rfl⟩
  rcases h2 with ⟨e2, rfl⟩
  exact ⟨e2 ++ e1, by simp [List.append_assoc]⟩

theorem CtxExtends.cons {α : Type} (p : α) (Γ : List α) : CtxExtends Γ (p :: Γ) :=
  ⟨[p], rfl⟩

theorem CtxExtends.pushTypes {α : Type} (xs acc : List α) : CtxExtends acc (LeanQbe.T.pushTypes xs acc) :=
  ⟨xs.reverse, pushTypes_eq_reverse_append xs acc⟩

theorem CtxExtends.pushNormal (ts : List Ty) (Γ : List (Ty × VarKind)) :
    CtxExtends Γ (LeanQbe.T.pushNormal ts Γ) :=
  CtxExtends.pushTypes _ Γ

def LvlOk (Γ : List (Ty × VarKind)) (t : Ty) (allowed : VarKind → Bool) (lvl : Nat) : Prop :=
  lvl < Γ.length ∧ ∃ k, listGet? Γ (Γ.length - 1 - lvl) = some (t, k) ∧ allowed k = true

abbrev LvlNormal (Γ : List (Ty × VarKind)) (t : Ty) (lvl : Nat) : Prop :=
  LvlOk Γ t (· == .normal) lvl

theorem LvlOk.mono {Γ Γ' : List (Ty × VarKind)} (hExt : CtxExtends Γ Γ')
    {t : Ty} {allowed : VarKind → Bool} {lvl : Nat}
    (h : LvlOk Γ t allowed lvl) : LvlOk Γ' t allowed lvl := by
  rcases hExt with ⟨ext, rfl⟩
  rcases h with ⟨hlt, k, hget, hall⟩
  refine ⟨by rw [List.length_append]; omega, k, ?_, hall⟩
  have heq : (ext ++ Γ).length - 1 - lvl = ext.length + (Γ.length - 1 - lvl) := by
    rw [List.length_append]; omega
  rw [heq, listGet?_append_add]
  exact hget

theorem LvlOk.weaken_pred {Γ : List (Ty × VarKind)} {t : Ty} {p q : VarKind → Bool} {lvl : Nat}
    (hpq : ∀ k, p k = true → q k = true) (h : LvlOk Γ t p lvl) : LvlOk Γ t q lvl := by
  rcases h with ⟨hlt, k, hget, hp⟩
  exact ⟨hlt, k, hget, hpq k hp⟩

theorem LvlOk.checkVarKind {Γ : List (Ty × VarKind)} {t : Ty} {allowed : VarKind → Bool} {lvl : Nat}
    (h : LvlOk Γ t allowed lvl) :
    LeanQbe.T.checkVarKind Γ t allowed (if lvl < Γ.length then Γ.length - 1 - lvl else Γ.length) = true := by
  rcases h with ⟨hlt, k, hget, hall⟩
  simp only [hlt, ↓reduceIte, LeanQbe.T.checkVarKind, hget]
  cases hd : tyDecEq t t with
  | isTrue _ => simpa using hall
  | isFalse hf => exact absurd rfl hf

theorem LvlNormal.of_head {Γ : List (Ty × VarKind)} {t : Ty} :
    LvlNormal ((t, .normal) :: Γ) t Γ.length := by
  refine ⟨by simp, .normal, ?_, rfl⟩
  have h0 : ((t, .normal) :: Γ).length - 1 - Γ.length = 0 := by simp
  rw [h0]; rfl

theorem LvlOk.of_head {Γ : List (Ty × VarKind)} {t : Ty} {k : VarKind} {allowed : VarKind → Bool}
    (hk : allowed k = true) :
    LvlOk ((t, k) :: Γ) t allowed Γ.length := by
  refine ⟨by simp, k, ?_, hk⟩
  have h0 : ((t, k) :: Γ).length - 1 - Γ.length = 0 := by simp
  rw [h0]; rfl

def ArgNormal (target : LegalTarget) (Γ : List (Ty × VarKind)) (t : Ty) : Arg K t → Prop
  | .var lvl => LvlNormal Γ t lvl ∧ target.isLegalTy t = true
  | .imm _ => target.isLegalTy t = true

theorem ArgNormal.isLegalTy {target : LegalTarget} {Γ : List (Ty × VarKind)} {t : Ty} {a : Arg K t}
    (h : ArgNormal target Γ t a) : target.isLegalTy t = true := by
  cases a with
  | var _ => exact h.2
  | imm _ => exact h

theorem ArgNormal.mono {target : LegalTarget} {Γ Γ' : List (Ty × VarKind)} (hExt : CtxExtends Γ Γ')
    {t : Ty} {a : Arg K t} (h : ArgNormal target Γ t a) : ArgNormal target Γ' t a := by
  cases a with
  | imm _ => exact h
  | var _ => exact ⟨h.1.mono hExt, h.2⟩

theorem ArgNormal.checkLegalArg {target : LegalTarget} {Γ : List (Ty × VarKind)} {t : Ty} {a : Arg K t}
    (h : ArgNormal target Γ t a) :
    LeanQbe.T.checkLegalArg Γ t (idxArg Γ.length a) = true := by
  cases a with
  | imm _ => rfl
  | var _ => exact h.1.checkVarKind

theorem ArgNormal.head (target : LegalTarget) (Γ : List (Ty × VarKind)) {t : Ty}
    (ht : target.isLegalTy t = true) :
    ArgNormal target ((t, .normal) :: Γ) t (.var Γ.length) :=
  ⟨LvlNormal.of_head, ht⟩

theorem ArgNormal.cast {target : LegalTarget} {Γ : List (Ty × VarKind)} {m n : Nat} (h : m = n)
    {x : Arg K (.bits m)} (hx : ArgNormal target Γ (.bits m) x) :
    ArgNormal target Γ (.bits n) (castArgBits h x) := by
  subst h; exact hx

def ArgsNormal (target : LegalTarget) (Γ : List (Ty × VarKind)) :
    {ts : List Ty} → Tup (Arg K) ts → Prop
  | [], () => True
  | _ :: _, (x, xs) => ArgNormal target Γ _ x ∧ ArgsNormal target Γ xs

theorem ArgsNormal.mono {target : LegalTarget} {Γ Γ' : List (Ty × VarKind)} (hExt : CtxExtends Γ Γ') :
    {ts : List Ty} → {xs : Tup (Arg K) ts} → ArgsNormal target Γ xs → ArgsNormal target Γ' xs
  | [], (), _ => trivial
  | _ :: _, (_, _), h => ⟨h.1.mono hExt, ArgsNormal.mono hExt h.2⟩

theorem ArgsNormal.isLegalSig {target : LegalTarget} {Γ : List (Ty × VarKind)} :
    {ts : List Ty} → {xs : Tup (Arg K) ts} → ArgsNormal target Γ xs → target.isLegalSig ts = true
  | [], (), _ => rfl
  | _ :: _, (_, _), h => by
    simp only [LegalTarget.isLegalSig, List.all_cons, Bool.and_eq_true]
    exact ⟨h.1.isLegalTy, ArgsNormal.isLegalSig h.2⟩

theorem ArgsNormal.checkLegalArgs {target : LegalTarget} {Γ : List (Ty × VarKind)} :
    {ts : List Ty} → {xs : Tup (Arg K) ts} → ArgsNormal target Γ xs →
      LeanQbe.T.checkLegalArgs Γ (idxArgs Γ.length xs) = true
  | [], (), _ => rfl
  | _ :: _, (_, _), h => by
    simp only [idxArgs_cons, checkLegalArgs_cons, Bool.and_eq_true]
    exact ⟨h.1.checkLegalArg, ArgsNormal.checkLegalArgs h.2⟩

theorem ArgsNormal_tupAppend {target : LegalTarget} {Γ : List (Ty × VarKind)} :
    {as bs : List Ty} → {xs : Tup (Arg K) as} → {ys : Tup (Arg K) bs} →
      ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      ArgsNormal target Γ (tupAppend xs ys)
  | [], _, (), _, _, hy => hy
  | _ :: _, _, (_, _), _, hx, hy => ⟨hx.1, ArgsNormal_tupAppend hx.2 hy⟩

theorem ArgsNormal_tupSplit {target : LegalTarget} {Γ : List (Ty × VarKind)} :
    {as bs : List Ty} → {zs : Tup (Arg K) (as ++ bs)} →
      ArgsNormal target Γ zs →
      ArgsNormal target Γ (tupSplit (as := as) (bs := bs) zs).1 ∧
      ArgsNormal target Γ (tupSplit (as := as) (bs := bs) zs).2
  | [], _, _, hz => ⟨trivial, hz⟩
  | _ :: _, _, (_, _), hz =>
    let ⟨h1, h2⟩ := ArgsNormal_tupSplit hz.2
    ⟨⟨hz.1, h1⟩, h2⟩

theorem ArgsNormal_cast_eq {target : LegalTarget} {Γ : List (Ty × VarKind)}
    {as bs : List Ty} (hc : Tup (Arg K) as = Tup (Arg K) bs) (h : as = bs)
    {xs : Tup (Arg K) as} (hx : ArgsNormal target Γ xs) :
    ArgsNormal target Γ (cast hc xs) := by
  subst h; exact hx

theorem ArgsNormal_packedToTup {target : LegalTarget} {Γ : List (Ty × VarKind)} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true)
    {xs : Tup (Arg K) (target.legalTys (.pair a b))} (hx : ArgsNormal target Γ xs) :
    ArgsNormal target Γ (packedToTup h xs) :=
  ArgsNormal_cast_eq _ (by simp [LegalTarget.legalTys, h]) hx

theorem ArgsNormal_tupToPacked {target : LegalTarget} {Γ : List (Ty × VarKind)} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true)
    {xs : Tup (Arg K) [.pair a b]} (hx : ArgsNormal target Γ xs) :
    ArgsNormal target Γ (tupToPacked h xs) :=
  ArgsNormal_cast_eq _ (by simp [LegalTarget.legalTys, h]) hx

theorem ArgsNormal_splitToTup {target : LegalTarget} {Γ : List (Ty × VarKind)} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false)
    {xs : Tup (Arg K) (target.legalTys (.pair a b))} (hx : ArgsNormal target Γ xs) :
    ArgsNormal target Γ (splitToTup h xs) :=
  ArgsNormal_cast_eq _ (by simp [LegalTarget.legalTys, h]) hx

theorem ArgsNormal_tupToSplit {target : LegalTarget} {Γ : List (Ty × VarKind)} {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false)
    {xs : Tup (Arg K) (target.legalTys a ++ target.legalTys b)} (hx : ArgsNormal target Γ xs) :
    ArgsNormal target Γ (tupToSplit h xs) :=
  ArgsNormal_cast_eq _ (by simp [LegalTarget.legalTys, h]) hx

theorem ArgsNormal_encodeImm {target : LegalTarget}
    {Γ : List (Ty × VarKind)} :
    (t : Ty) → target.supportsTy t = true → (c : Val t) →
      ArgsNormal target Γ (encodeImm target t c)
  | .bool, _, _ => ⟨rfl, trivial⟩
  | .bits n, ht, _ => ⟨by simp [ArgNormal, LegalTarget.isLegalTy, widenWidth_mem_of_supports ht], trivial⟩
  | .float f, ht, _ => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    exact ⟨by simpa [ArgNormal, LegalTarget.isLegalTy] using ht.1, trivial⟩
  | .pair a b, ht, p => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    by_cases h : target.keepsPacked (.pair a b) = true
    · simp only [encodeImm, h, ↓reduceDIte]
      exact ArgsNormal_tupToPacked h ⟨by simpa [ArgNormal, LegalTarget.isLegalTy] using h, trivial⟩
    · have hf : target.keepsPacked (.pair a b) = false := Bool.eq_false_iff.mpr h
      rw [encodeImm, dite_eq_right (fun h' => False.elim (h h'))]
      exact ArgsNormal_tupToSplit hf
        (ArgsNormal_tupAppend (ArgsNormal_encodeImm a ht.1 p.1) (ArgsNormal_encodeImm b ht.2 p.2))

theorem ArgsNormal_leafImm_hasLegalLeaves (target : LegalTarget) {Γ : List (Ty × VarKind)} :
    (t : Ty) → target.hasLegalLeaves t = true → (c : Val t) →
      ArgsNormal target Γ (leafImm target t c)
  | .bool, _, _ => ⟨rfl, trivial⟩
  | .bits n, hl, _ => by
    have hmem : n ∈ target.bitWidths := by simpa [LegalTarget.hasLegalLeaves] using hl
    exact ⟨by simp [ArgNormal, LegalTarget.isLegalTy, widenWidth_eq_self_of_mem target hmem, hmem], trivial⟩
  | .float f, hl, _ => ⟨by simpa [ArgNormal, LegalTarget.isLegalTy, LegalTarget.hasLegalLeaves] using hl, trivial⟩
  | .pair a b, hl, p => by
    simp only [LegalTarget.hasLegalLeaves, Bool.and_eq_true] at hl
    exact ArgsNormal_tupAppend (ArgsNormal_leafImm_hasLegalLeaves target a hl.1 p.1)
      (ArgsNormal_leafImm_hasLegalLeaves target b hl.2 p.2)

theorem ArgsNormal_varsTup_levels_aux (target : LegalTarget) :
    ∀ (ts : List Ty) (Γ0 Γ : List (Ty × VarKind)),
      Γ = (ts.map (·, VarKind.normal)).reverse ++ Γ0 →
      target.isLegalSig ts = true →
      ArgsNormal target Γ (varsTup (Tup.levels ts Γ0.length))
  | [], _, _, _, _ => trivial
  | t :: ts, Γ0, Γ, hΓ, hsig => by
    simp only [LegalTarget.isLegalSig, List.all_cons, Bool.and_eq_true] at hsig
    simp only [Tup.levels_cons, varsTup, ArgsNormal]
    have hih := ArgsNormal_varsTup_levels_aux target ts ((t, .normal) :: Γ0) Γ
      (by simp [hΓ, List.reverse_cons, List.append_assoc]) hsig.2
    have hmem : LvlNormal Γ t Γ0.length := by
      have hm1 : LvlNormal ((t, .normal) :: Γ0) t Γ0.length := LvlNormal.of_head
      have hex : CtxExtends ((t, .normal) :: Γ0) Γ :=
        ⟨(ts.map (·, .normal)).reverse, by simp [hΓ, List.reverse_cons, List.append_assoc]⟩
      exact hm1.mono hex
    exact ⟨⟨hmem, hsig.1⟩, by simpa using hih⟩

theorem ArgsNormal_varsTup_levels (target : LegalTarget) (ts : List Ty) (Γ : List (Ty × VarKind))
    (hsig : target.isLegalSig ts = true) :
    ArgsNormal target (pushNormal ts Γ) (varsTup (Tup.levels ts Γ.length)) :=
  ArgsNormal_varsTup_levels_aux target ts Γ (pushNormal ts Γ)
    (by simp [pushNormal, pushTypes_eq_reverse_append]) hsig

def CLegal (target : LegalTarget) (Γ : List (Ty × VarKind))
    (LG : Ctx K (LVar target K)) : Prop :=
  ∀ t lv₁ lv₂, ⟨t, lv₁, lv₂⟩ ∈ LG → ArgsNormal target Γ lv₂

theorem CLegal.mono {target : LegalTarget} {Γ Γ' : List (Ty × VarKind)} (hExt : CtxExtends Γ Γ')
    {LG : Ctx K (LVar target K)} (hc : CLegal target Γ LG) : CLegal target Γ' LG :=
  fun t lv₁ lv₂ hm => (hc t lv₁ lv₂ hm).mono hExt

theorem CLegal.pushTRel {target : LegalTarget} {Γ : List (Ty × VarKind)}
    {LG : Ctx K (LVar target K)} (hc : CLegal target Γ LG) :
    {ts : List Ty} → {xs₁ : Tup K ts} → {xs₂ : Tup (LVar target K) ts} →
      (∀ t lv₂, (∃ lv₁, ⟨t, lv₁, lv₂⟩ ∈ Tup.zip xs₁ xs₂) → ArgsNormal target Γ lv₂) →
      CLegal target Γ (Tup.zip xs₁ xs₂ ++ LG)
  | _, _, _, hxs, t, lv₁, lv₂, hm => by
    rcases List.mem_append.1 hm with h | h
    · exact hxs t lv₂ ⟨lv₁, h⟩
    · exact hc t lv₁ lv₂ h

theorem legalArg_isNormal {target : LegalTarget} {Γ : List (Ty × VarKind)} {LG : Ctx K (LVar target K)}
    (hc : CLegal target Γ LG) :
    ∀ {t : Ty} {a₁ : Arg K t} {a₂ : Arg (LVar target K) t},
      target.supportsTy t = true → ArgRel LG t a₁ a₂ →
      ArgsNormal target Γ (legalArg target a₂)
  | t, _, .var lv₂, _, hrel => by
    cases hrel with
    | var hm => exact hc t _ lv₂ hm
  | t, _, .imm c, hsupp, hrel => by
    cases hrel with
    | imm => exact ArgsNormal_encodeImm t hsupp c

theorem joinArgs_isNormal {target : LegalTarget} {Γ : List (Ty × VarKind)} {LG : Ctx K (LVar target K)}
    (hc : CLegal target Γ LG) :
    ∀ {ts : List Ty} {xs₁ : Tup (Arg K) ts} {xs₂ : Tup (Arg (LVar target K)) ts},
      ts.all target.supportsTy = true → TRel (ArgRel LG) xs₁ xs₂ →
      ArgsNormal target Γ (joinArgs target xs₂)
  | [], (), (), _, _ => trivial
  | t :: ts, (_, _), (_, _), hts, .cons h1 h2 => by
    simp only [List.all_cons, Bool.and_eq_true] at hts
    exact ArgsNormal_tupAppend (legalArg_isNormal hc hts.1 h1) (joinArgs_isNormal hc hts.2 h2)

theorem tupSplit_levels {α : Type} : (as bs : List α) → (n : Nat) →
    tupSplit (as := as) (bs := bs) (Tup.levels (as ++ bs) n) = (Tup.levels as n, Tup.levels bs (n + as.length))
  | [], _, n => by simp [Tup.levels_nil, tupSplit]
  | _ :: as, bs, n => by
    simp only [List.cons_append, Tup.levels_cons, tupSplit, tupSplit_levels as bs (n + 1),
      List.length_cons, Nat.add_assoc, Nat.add_comm 1 as.length]

theorem varsTup_levels_append {as bs : List Ty} (n : Nat) :
    varsTup (Tup.levels (as ++ bs) n) =
      tupAppend (varsTup (Tup.levels as n)) (varsTup (Tup.levels bs (n + as.length))) := by
  induction as generalizing n with
  | nil => rfl
  | cons _ as ih =>
    simp only [List.cons_append, Tup.levels_cons, varsTup, tupAppend, List.length_cons]
    exact congrArg (_, ·) (by simpa [Nat.add_assoc, Nat.add_comm 1 as.length] using ih (n + 1))

theorem CLegal.pushSplit_aux (target : LegalTarget) {Γ : List (Ty × VarKind)}
    {LG : Ctx K (LVar target K)} (hc : CLegal target Γ LG) :
    ∀ (ts : List Ty) (xs₁ : Tup K ts) (n : Nat),
      ArgsNormal target Γ (varsTup (Tup.levels (target.legalSig ts) n)) →
      CLegal target Γ (Tup.zip xs₁ (splitParams target ts (Tup.levels (target.legalSig ts) n)) ++ LG)
  | [], (), _, _ => hc
  | t :: ts, (_, _), n, hxs => by
    rw [LegalTarget.legalSig] at hxs
    rw [varsTup_levels_append] at hxs
    obtain ⟨h1, h2⟩ := ArgsNormal_tupSplit hxs
    simp only [tupSplit_tupAppend] at h1 h2
    simp only [LegalTarget.legalSig, tupSplit_levels, splitParams]
    intro t' lv₁ lv₂ hm
    rcases List.mem_append.1 hm with hm' | hm'
    · rcases List.mem_cons.1 hm' with ⟨rfl, rfl, rfl⟩ | htail
      · exact h1
      · exact CLegal.pushSplit_aux target hc ts _ (n + (target.legalTys t).length) h2 t' lv₁ lv₂
          (List.mem_append_left _ htail)
    · exact hc t' lv₁ lv₂ hm'

theorem CLegal.pushSplit (target : LegalTarget) (hv : target.valid = true)
    {Γ : List (Ty × VarKind)} {LG : Ctx K (LVar target K)} (hc : CLegal target Γ LG)
    (ts : List Ty) (hts : ts.all target.supportsTy = true) (xs₁ : Tup K ts) :
    CLegal target (pushNormal (target.legalSig ts) Γ)
      (Tup.zip xs₁ (splitParams target ts (Tup.levels (target.legalSig ts) Γ.length)) ++ LG) :=
  CLegal.pushSplit_aux target (hc.mono (CtxExtends.pushNormal _ _)) ts xs₁ Γ.length
    (ArgsNormal_varsTup_levels target (target.legalSig ts) Γ (isLegalSig_legalSig hv hts))

def DLegal (target : LegalTarget) (Δ : List (List Ty)) (LD : Ctx KL (LLab target KL)) : Prop :=
  ∀ ts l₁ l₂, ⟨ts, l₁, l₂⟩ ∈ LD →
    l₂ < Δ.length ∧ listGet? Δ (Δ.length - 1 - l₂) = some (target.legalSig ts) ∧ ts.all target.supportsTy = true

theorem DLegal.mono {target : LegalTarget} {Δ Δ' : List (List Ty)} (hExt : CtxExtends Δ Δ')
    {LD : Ctx KL (LLab target KL)} (hd : DLegal target Δ LD) : DLegal target Δ' LD := by
  intro ts l₁ l₂ hm
  obtain ⟨hlt, hget, hsupp⟩ := hd ts l₁ l₂ hm
  rcases hExt with ⟨ext, rfl⟩
  refine ⟨by rw [List.length_append]; omega, ?_, hsupp⟩
  have heq : (ext ++ Δ).length - 1 - l₂ = ext.length + (Δ.length - 1 - l₂) := by
    rw [List.length_append]; omega
  rw [heq, listGet?_append_add]
  exact hget

theorem DLegal.pushLiftMap_aux (target : LegalTarget) :
    ∀ (sig : List (List Ty)) (Δ₀ Δ : List (List Ty)),
      Δ = (sig.map target.legalSig).reverse ++ Δ₀ →
      sig.all (fun ts => ts.all target.supportsTy) = true →
      ∀ {nl₁ : Nat} {ts : List Ty} {l₁ : KL ts} {l₂ : LLab target KL ts},
        ⟨ts, l₁, l₂⟩ ∈ Tup.zip (Tup.levels sig nl₁)
          (tupLiftMap target.legalSig KL (Tup.levels (sig.map target.legalSig) Δ₀.length)) →
        l₂ < Δ.length ∧ listGet? Δ (Δ.length - 1 - l₂) = some (target.legalSig ts) ∧ ts.all target.supportsTy = true
  | [], _, _, _, _, _, _, _, _, hm => by cases hm
  | ts₀ :: sig', Δ₀, Δ, hΔ, hsig, nl₁, ts, l₁, l₂, hm => by
    simp only [List.all_cons, Bool.and_eq_true] at hsig
    rw [Tup.levels_cons, tupLiftMap_levels_cons] at hm
    simp only [Tup.zip] at hm
    have hΔ' : Δ = (sig'.map target.legalSig).reverse ++ (target.legalSig ts₀ :: Δ₀) := by
      simp [hΔ, List.reverse_cons, List.append_assoc]
    rcases List.mem_cons.1 hm with ⟨rfl, rfl, rfl⟩ | htail
    · have hex : CtxExtends (target.legalSig ts₀ :: Δ₀) Δ := ⟨(sig'.map target.legalSig).reverse, hΔ'⟩
      have h0 : (target.legalSig ts₀ :: Δ₀).length - 1 - Δ₀.length = 0 := by simp
      rcases hex with ⟨ext, rfl⟩
      refine ⟨by change Δ₀.length < (ext ++ target.legalSig ts₀ :: Δ₀).length
                 simp only [List.length_append, List.length_cons]; omega, ?_, hsig.1⟩
      have heq : (ext ++ (target.legalSig ts₀ :: Δ₀)).length - 1 - Δ₀.length =
          ext.length + ((target.legalSig ts₀ :: Δ₀).length - 1 - Δ₀.length) := by
        simp only [List.length_append, List.length_cons]
        have : (target.legalSig ts₀ :: Δ₀).length = Δ₀.length + 1 := by simp
        omega
      rw [heq, listGet?_append_add, h0]; rfl
    · have hlen1 : (target.legalSig ts₀ :: Δ₀).length = Δ₀.length + 1 := by simp
      rw [← hlen1] at htail
      exact DLegal.pushLiftMap_aux target sig' (target.legalSig ts₀ :: Δ₀) Δ hΔ' hsig.2 htail

theorem DLegal.pushLiftMap (target : LegalTarget) {Δ : List (List Ty)}
    {LD : Ctx KL (LLab target KL)} (hd : DLegal target Δ LD)
    (sig : List (List Ty)) (hsig : sig.all (fun ts => ts.all target.supportsTy) = true) (nl₁ : Nat) :
    DLegal target (LeanQbe.T.pushTypes (sig.map target.legalSig) Δ)
      (Tup.zip (Tup.levels sig nl₁) (tupLiftMap target.legalSig KL (Tup.levels (sig.map target.legalSig) Δ.length)) ++ LD) := by
  intro ts l₁ l₂ hm
  rcases List.mem_append.1 hm with h | h
  · exact DLegal.pushLiftMap_aux target sig Δ (LeanQbe.T.pushTypes (sig.map target.legalSig) Δ)
      (pushTypes_eq_reverse_append _ _) hsig h
  · exact hd.mono (CtxExtends.pushTypes _ _) ts l₁ l₂ h

abbrev IsLegalCont (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {α : Type} {rs : List Ty} (P : List (Ty × VarKind) → α → Prop) (k : α → Expr K KL rs) : Prop :=
  ∀ (Γ' : List (Ty × VarKind)) (x : α),
    CtxExtends Γ Γ' → P Γ' x → (toTFlat (k x) Γ'.length Δ.length).isLegal target Γ' Δ = true

/-! ### Unpack/pack bridge lemmas (`unpackToLeaves`, `packFromLegal`, `unpackToLegal`) -/

def UnpackBridgeArg (target : LegalTarget) (Γ : List (Ty × VarKind)) (u : Ty) : Arg K u → Prop
  | .imm _ => True
  | .var lvl =>
    LvlOk Γ u (fun vk => (vk == .normal && target.isLegalTy u) || vk == .unpackedBridge) lvl ∧
      (target.isLegalTy u = true → LvlNormal Γ u lvl)

theorem UnpackBridgeArg.mono {target : LegalTarget} {Γ Γ' : List (Ty × VarKind)} (hExt : CtxExtends Γ Γ')
    {u : Ty} {x : Arg K u} (h : UnpackBridgeArg target Γ u x) : UnpackBridgeArg target Γ' u x := by
  cases x with
  | imm _ => trivial
  | var _ => exact ⟨h.1.mono hExt, fun hleg => (h.2 hleg).mono hExt⟩

theorem UnpackBridgeArg.of_normal {target : LegalTarget} {Γ : List (Ty × VarKind)}
    {u : Ty} {x : Arg K u} (h : ArgNormal target Γ u x) : UnpackBridgeArg target Γ u x := by
  cases x with
  | imm _ => trivial
  | var _ =>
    refine ⟨?_, fun _ => h.1⟩
    exact h.1.weaken_pred fun k hk => by simp [hk, h.2]

def PackBridgeArg (target : LegalTarget) (Γ : List (Ty × VarKind)) (u : Ty) : Arg K u → Prop
  | .imm _ => target.isLegalTy u = true
  | .var lvl => LvlOk Γ u (fun vk => (vk == .normal && target.isLegalTy u) || vk == .packedBridge) lvl

theorem PackBridgeArg.mono {target : LegalTarget} {Γ Γ' : List (Ty × VarKind)} (hExt : CtxExtends Γ Γ')
    {u : Ty} {x : Arg K u} (h : PackBridgeArg target Γ u x) : PackBridgeArg target Γ' u x := by
  cases x with
  | imm _ => exact h
  | var lvl => exact LvlOk.mono hExt h

theorem PackBridgeArg.of_normal {target : LegalTarget} {Γ : List (Ty × VarKind)}
    {u : Ty} {x : Arg K u} (h : ArgNormal target Γ u x) : PackBridgeArg target Γ u x := by
  cases x with
  | imm _ => exact h.isLegalTy
  | var _ => exact h.1.weaken_pred fun k hk => by simp [hk, h.2]

theorem unpackToLeaves_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (ha : target.allowPackBridge = true) :
    ∀ (u : Ty) {Γ : List (Ty × VarKind)}, target.hasLegalLeaves u = true →
      ∀ (x : Arg K u), UnpackBridgeArg target Γ u x →
      ∀ {k : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (unpackToLeaves target u x k) Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, _, x, hx, k, hk => by
    simp only [unpackToLeaves]
    cases x with
    | imm c => exact hk Γ (.imm c, ()) (CtxExtends.refl Γ) ⟨rfl, trivial⟩
    | var lvl => exact hk Γ (.var lvl, ()) (CtxExtends.refl Γ) ⟨⟨hx.2 rfl, rfl⟩, trivial⟩
  | .bits n, Γ, hl, x, hx, k, hk => by
    have hmem : n ∈ target.bitWidths := by simpa [LegalTarget.hasLegalLeaves] using hl
    have hw : target.widenWidth n = n := widenWidth_eq_self_of_mem target hmem
    simp only [unpackToLeaves]
    split
    · next heq =>
      cases x with
      | imm c =>
        have hc : ArgNormal target Γ (.bits (target.widenWidth n)) (castArgBits heq (.imm c)) :=
          ArgNormal.cast heq (by simp [ArgNormal, LegalTarget.isLegalTy, hmem])
        exact hk Γ _ (CtxExtends.refl Γ) ⟨hc, trivial⟩
      | var lvl =>
        have hleg : target.isLegalTy (.bits n) = true := by simpa [LegalTarget.isLegalTy] using hmem
        have hc : ArgNormal target Γ (.bits (target.widenWidth n)) (castArgBits heq (.var lvl)) :=
          ArgNormal.cast heq ⟨hx.2 hleg, hleg⟩
        exact hk Γ _ (CtxExtends.refl Γ) ⟨hc, trivial⟩
    · next hne => exact absurd hw.symm hne
  | .float f, Γ, hl, x, hx, k, hk => by
    have hleg : target.isLegalTy (.float f) = true := by
      simpa [LegalTarget.isLegalTy, LegalTarget.hasLegalLeaves] using hl
    simp only [unpackToLeaves]
    cases x with
    | imm c => exact hk Γ (.imm c, ()) (CtxExtends.refl Γ) ⟨hleg, trivial⟩
    | var lvl => exact hk Γ (.var lvl, ()) (CtxExtends.refl Γ) ⟨⟨hx.2 hleg, hleg⟩, trivial⟩
  | .pair a b, Γ, hl, x, hx, k, hk => by
    have hl' := hl
    simp only [LegalTarget.hasLegalLeaves, Bool.and_eq_true] at hl'
    simp only [unpackToLeaves]
    cases x with
    | imm c => exact hk Γ _ (CtxExtends.refl Γ) (ArgsNormal_leafImm_hasLegalLeaves target (.pair a b) hl c)
    | var lvl =>
      rw [toTFlat_let]; dsimp only [op1, Tup.levels_cons, Tup.levels_nil]; rw [idxArgs_single]
      rw [TFlat.isLegal_let_unpair]
      simp only [ha, hl, Bool.true_and, idxArg, hx.1.checkVarKind]
      let ka : VarKind := if target.isLegalTy a then .normal else .unpackedBridge
      let kb : VarKind := if target.isLegalTy b then .normal else .unpackedBridge
      let Γ1 := pushTypes [(a, ka), (b, kb)] Γ
      have hExt1 : CtxExtends Γ Γ1 := CtxExtends.pushTypes _ Γ
      have hlen1' : Γ1.length = Γ.length + 2 := by simp [Γ1, pushTypes_length, Nat.add_comm]
      have hlen1 : Γ1.length = Γ.length + [a, b].length := by simpa using hlen1'
      rw [← hlen1]
      have hget0 : listGet? Γ1 (Γ1.length - 1 - Γ.length) = some (a, ka) := by
        have hrev : Γ1 = [(b, kb), (a, ka)] ++ Γ := rfl
        have hidx : Γ1.length - 1 - Γ.length = 1 := by omega
        rw [hidx, hrev]; rfl
      have hget1 : listGet? Γ1 (Γ1.length - 1 - (Γ.length + 1)) = some (b, kb) := by
        have hrev : Γ1 = [(b, kb), (a, ka)] ++ Γ := rfl
        have hidx : Γ1.length - 1 - (Γ.length + 1) = 0 := by omega
        rw [hidx, hrev]; rfl
      have hUa : UnpackBridgeArg target Γ1 a (.var Γ.length) := by
        refine ⟨⟨by omega, ka, hget0, ?_⟩, ?_⟩
        · by_cases haL : target.isLegalTy a = true <;> simp [ka, haL]
        · intro haL; refine ⟨by omega, .normal, ?_, rfl⟩; simpa [ka, haL] using hget0
      have hUb : UnpackBridgeArg target Γ1 b (.var (Γ.length + 1)) := by
        refine ⟨⟨by omega, kb, hget1, ?_⟩, ?_⟩
        · by_cases hbL : target.isLegalTy b = true <;> simp [kb, hbL]
        · intro hbL; refine ⟨by omega, .normal, ?_, rfl⟩; simpa [kb, hbL] using hget1
      change (toTFlat (unpackToLeaves target a (.var Γ.length) fun la =>
        unpackToLeaves target b (.var (Γ.length + 1)) fun lb => k (tupAppend la lb))
          Γ1.length Δ.length).isLegal target Γ1 Δ = true
      refine unpackToLeaves_isLegal target ha a hl'.1 (.var Γ.length) hUa fun Γ2 la hExt12 hla => ?_
      refine unpackToLeaves_isLegal target ha b hl'.2 (.var (Γ.length + 1)) (hUb.mono hExt12)
        fun Γ3 lb hExt23 hlb => ?_
      exact hk Γ3 (tupAppend la lb) (hExt1.trans (hExt12.trans hExt23))
        (ArgsNormal_tupAppend (hla.mono hExt23) hlb)

theorem packFromLegal_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (ha : target.allowPackBridge = true) :
    ∀ (u : Ty) {Γ : List (Ty × VarKind)}, target.hasLegalLeaves u = true →
      ∀ (xs : Tup (Arg K) (target.legalTys u)), ArgsNormal target Γ xs →
      ∀ {k : Arg K u → Expr K KL rs},
      IsLegalCont target Γ Δ (fun Γ' res => PackBridgeArg target Γ' u res) k →
      (toTFlat (packFromLegal target u xs k) Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, _, (x, ()), hxs, k, hk => by
    simp only [packFromLegal]
    exact hk Γ x (CtxExtends.refl Γ) (PackBridgeArg.of_normal hxs.1)
  | .bits n, Γ, hl, (x, ()), hxs, k, hk => by
    have hmem : n ∈ target.bitWidths := by simpa [LegalTarget.hasLegalLeaves] using hl
    have hw : target.widenWidth n = n := widenWidth_eq_self_of_mem target hmem
    simp only [packFromLegal]
    split
    · next heq =>
      exact hk Γ (castArgBits heq.symm x) (CtxExtends.refl Γ) (PackBridgeArg.of_normal (ArgNormal.cast heq.symm hxs.1))
    · next hne => exact absurd hw.symm hne
  | .float f, Γ, _, (x, ()), hxs, k, hk => by
    simp only [packFromLegal]
    exact hk Γ x (CtxExtends.refl Γ) (PackBridgeArg.of_normal hxs.1)
  | .pair a b, Γ, hl, xs, hxs, k, hk => by
    have hl' := hl
    simp only [LegalTarget.hasLegalLeaves, Bool.and_eq_true] at hl'
    simp only [packFromLegal]
    split
    · next hp =>
      exact hk Γ (packedToTup hp xs).1 (CtxExtends.refl Γ) (PackBridgeArg.of_normal (ArgsNormal_packedToTup hp hxs).1)
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      obtain ⟨hla, hlb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
      refine packFromLegal_isLegal target ha a hl'.1 _ hla fun Γ1 va hExt1 hva => ?_
      refine packFromLegal_isLegal target ha b hl'.2 _ (hlb.mono hExt1) fun Γ2 vb hExt2 hvb => ?_
      have hva' := hva.mono hExt2
      rw [toTFlat_let]; dsimp only [op2, Tup.levels_cons, Tup.levels_nil]; rw [idxArgs_pair]
      rw [TFlat.isLegal_let_mkpair]
      have hchkIn : ∀ {u : Ty} {v : Arg K u}, PackBridgeArg target Γ2 u v →
          (match idxArg Γ2.length v with
           | .var idx => checkVarKind Γ2 u (fun vk => (vk == .normal && target.isLegalTy u) || vk == .packedBridge) idx
           | .imm _ => target.isLegalTy u) = true := by
        intro u v hv'
        cases v with
        | imm _ => exact hv'
        | var _ => exact hv'.checkVarKind
      simp only [ha, hl, hchkIn hva', hchkIn hvb, Bool.true_and]
      let kres : VarKind := if target.isLegalTy (.pair a b) then .normal else .packedBridge
      let Γ3 := ((.pair a b, kres) :: Γ2)
      have hExt3 : CtxExtends Γ Γ3 := (hExt1.trans hExt2).trans (CtxExtends.cons _ _)
      have hlen3 : Γ3.length = Γ2.length + [a.pair b].length := by simp [Γ3]
      rw [← hlen3]
      change (toTFlat (k (.var Γ2.length)) Γ3.length Δ.length).isLegal target Γ3 Δ = true
      refine hk Γ3 (.var Γ2.length) hExt3 ?_
      exact LvlOk.of_head (k := kres) (by by_cases hL : target.isLegalTy (.pair a b) = true <;> simp [kres, hL])

theorem splitLegalToLeaves_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty} :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)} (xs : Tup (Arg K) (target.legalTys t)),
      ArgsNormal target Γ xs →
      ∀ {k : Tup (Arg K) (target.leafTys t) → Expr K KL rs},
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (splitLegalToLeaves target t xs k) Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, xs, hxs, k, hk => hk Γ xs (CtxExtends.refl Γ) hxs
  | .bits _, Γ, xs, hxs, k, hk => hk Γ xs (CtxExtends.refl Γ) hxs
  | .float _, Γ, xs, hxs, k, hk => hk Γ xs (CtxExtends.refl Γ) hxs
  | .pair a b, Γ, xs, hxs, k, hk => by
    simp only [splitLegalToLeaves]
    split
    · next hp =>
      have hp' := hp
      simp only [LegalTarget.keepsPacked, Bool.and_eq_true] at hp'
      exact unpackToLeaves_isLegal target hp'.1.1 (.pair a b) hp'.2 (packedToTup hp xs).1
        (UnpackBridgeArg.of_normal (ArgsNormal_packedToTup hp hxs).1) hk
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      obtain ⟨hla, hlb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
      refine splitLegalToLeaves_isLegal target a _ hla fun Γ1 fa hExt1 hfa => ?_
      exact splitLegalToLeaves_isLegal target b _ (hlb.mono hExt1) fun Γ2 fb hExt2 hfb =>
        hk Γ2 (tupAppend fa fb) (hExt1.trans hExt2) (ArgsNormal_tupAppend (hfa.mono hExt2) hfb)

theorem packLeavesToLegal_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty} :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)} (xs : Tup (Arg K) (target.leafTys t)),
      ArgsNormal target Γ xs →
      ∀ {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs},
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (packLeavesToLegal target t xs k) Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, xs, hxs, k, hk => hk Γ xs (CtxExtends.refl Γ) hxs
  | .bits _, Γ, xs, hxs, k, hk => hk Γ xs (CtxExtends.refl Γ) hxs
  | .float _, Γ, xs, hxs, k, hk => hk Γ xs (CtxExtends.refl Γ) hxs
  | .pair a b, Γ, xs, hxs, k, hk => by
    simp only [packLeavesToLegal]
    split
    · next hp =>
      have hp' := hp
      simp only [LegalTarget.keepsPacked, Bool.and_eq_true] at hp'
      have ha := hp'.1.1
      have hl := hp'.2
      have hl' := hl
      simp only [LegalTarget.hasLegalLeaves, Bool.and_eq_true] at hl'
      obtain ⟨hfa, hfb⟩ := ArgsNormal_tupSplit hxs
      refine packLeavesToLegal_isLegal target a _ hfa fun Γ1 la hExt1 hla => ?_
      refine packLeavesToLegal_isLegal target b _ (hfb.mono hExt1) fun Γ2 lb hExt2 hlb => ?_
      refine packFromLegal_isLegal target ha a hl'.1 la (hla.mono hExt2) fun Γ3 va hExt3 hva => ?_
      refine packFromLegal_isLegal target ha b hl'.2 lb (hlb.mono hExt3) fun Γ4 vb hExt4 hvb => ?_
      have hva' := hva.mono hExt4
      rw [toTFlat_let]; dsimp only [op2, Tup.levels_cons, Tup.levels_nil]; rw [idxArgs_pair]
      rw [TFlat.isLegal_let_mkpair]
      have hchkIn : ∀ {u : Ty} {v : Arg K u}, PackBridgeArg target Γ4 u v →
          (match idxArg Γ4.length v with
           | .var idx => checkVarKind Γ4 u (fun vk => (vk == .normal && target.isLegalTy u) || vk == .packedBridge) idx
           | .imm _ => target.isLegalTy u) = true := by
        intro u v hv'
        cases v with
        | imm _ => exact hv'
        | var _ => exact hv'.checkVarKind
      have hp_leg : target.isLegalTy (.pair a b) = true := hp
      simp only [ha, hl, hchkIn hva', hchkIn hvb, hp_leg, ↓reduceIte, Bool.true_and]
      let Γ5 := ((.pair a b, VarKind.normal) :: Γ4)
      have hExt5 : CtxExtends Γ Γ5 :=
        (hExt1.trans (hExt2.trans (hExt3.trans hExt4))).trans (CtxExtends.cons _ _)
      have hlen5 : Γ5.length = Γ4.length + [a.pair b].length := by simp [Γ5]
      rw [← hlen5]
      exact hk Γ5 (tupToPacked hp (.var Γ4.length, ())) hExt5
        (ArgsNormal_tupToPacked hp ⟨⟨LvlNormal.of_head, hp⟩, trivial⟩)
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      obtain ⟨hfa, hfb⟩ := ArgsNormal_tupSplit hxs
      refine packLeavesToLegal_isLegal target a _ hfa fun Γ1 la hExt1 hla => ?_
      exact packLeavesToLegal_isLegal target b _ (hfb.mono hExt1) fun Γ2 lb hExt2 hlb =>
        hk Γ2 (tupToSplit hf (tupAppend la lb)) (hExt1.trans hExt2)
          (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hla.mono hExt2) hlb))

theorem unpackToLegal_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (ha : target.allowPackBridge = true) :
    ∀ (u : Ty) {Γ : List (Ty × VarKind)}, target.hasLegalLeaves u = true →
      ∀ (x : Arg K u), UnpackBridgeArg target Γ u x →
      ∀ {k : Tup (Arg K) (target.legalTys u) → Expr K KL rs},
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (unpackToLegal target u x k) Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, _, x, hx, k, hk => by
    simp only [unpackToLegal]
    cases x with
    | imm c => exact hk Γ (.imm c, ()) (CtxExtends.refl Γ) ⟨rfl, trivial⟩
    | var lvl => exact hk Γ (.var lvl, ()) (CtxExtends.refl Γ) ⟨⟨hx.2 rfl, rfl⟩, trivial⟩
  | .bits n, Γ, hl, x, hx, k, hk => by
    have hmem : n ∈ target.bitWidths := by simpa [LegalTarget.hasLegalLeaves] using hl
    have hw : target.widenWidth n = n := widenWidth_eq_self_of_mem target hmem
    simp only [unpackToLegal]
    split
    · next heq =>
      cases x with
      | imm c =>
        exact hk Γ _ (CtxExtends.refl Γ)
          ⟨ArgNormal.cast heq (by simp [ArgNormal, LegalTarget.isLegalTy, hmem]), trivial⟩
      | var lvl =>
        have hleg : target.isLegalTy (.bits n) = true := by simpa [LegalTarget.isLegalTy] using hmem
        exact hk Γ _ (CtxExtends.refl Γ) ⟨ArgNormal.cast heq ⟨hx.2 hleg, hleg⟩, trivial⟩
    · next hne => exact absurd hw.symm hne
  | .float f, Γ, hl, x, hx, k, hk => by
    have hleg : target.isLegalTy (.float f) = true := by
      simpa [LegalTarget.isLegalTy, LegalTarget.hasLegalLeaves] using hl
    simp only [unpackToLegal]
    cases x with
    | imm c => exact hk Γ (.imm c, ()) (CtxExtends.refl Γ) ⟨hleg, trivial⟩
    | var lvl => exact hk Γ (.var lvl, ()) (CtxExtends.refl Γ) ⟨⟨hx.2 hleg, hleg⟩, trivial⟩
  | .pair a b, Γ, hl, x, hx, k, hk => by
    have hl' := hl
    simp only [LegalTarget.hasLegalLeaves, Bool.and_eq_true] at hl'
    simp only [unpackToLegal]
    split
    · next hp =>
      cases x with
      | imm c =>
        exact hk Γ _ (CtxExtends.refl Γ) (ArgsNormal_tupToPacked hp ⟨hp, trivial⟩)
      | var lvl =>
        exact hk Γ _ (CtxExtends.refl Γ) (ArgsNormal_tupToPacked hp ⟨⟨hx.2 hp, hp⟩, trivial⟩)
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      cases x with
      | imm c =>
        exact hk Γ _ (CtxExtends.refl Γ)
          (ArgsNormal_encodeImm (.pair a b) (supportsTy_of_hasLegalLeaves hv hl) c)
      | var lvl =>
        rw [toTFlat_let]; dsimp only [op1, Tup.levels_cons, Tup.levels_nil]; rw [idxArgs_single]
        rw [TFlat.isLegal_let_unpair]
        simp only [ha, hl, Bool.true_and, idxArg, hx.1.checkVarKind]
        let ka : VarKind := if target.isLegalTy a then .normal else .unpackedBridge
        let kb : VarKind := if target.isLegalTy b then .normal else .unpackedBridge
        let Γ1 := pushTypes [(a, ka), (b, kb)] Γ
        have hExt1 : CtxExtends Γ Γ1 := CtxExtends.pushTypes _ Γ
        have hlen1' : Γ1.length = Γ.length + 2 := by simp [Γ1, pushTypes_length, Nat.add_comm]
        have hlen1 : Γ1.length = Γ.length + [a, b].length := by simpa using hlen1'
        rw [← hlen1]
        have hget0 : listGet? Γ1 (Γ1.length - 1 - Γ.length) = some (a, ka) := by
          have hrev : Γ1 = [(b, kb), (a, ka)] ++ Γ := rfl
          have hidx : Γ1.length - 1 - Γ.length = 1 := by omega
          rw [hidx, hrev]; rfl
        have hget1 : listGet? Γ1 (Γ1.length - 1 - (Γ.length + 1)) = some (b, kb) := by
          have hrev : Γ1 = [(b, kb), (a, ka)] ++ Γ := rfl
          have hidx : Γ1.length - 1 - (Γ.length + 1) = 0 := by omega
          rw [hidx, hrev]; rfl
        have hUa : UnpackBridgeArg target Γ1 a (.var Γ.length) := by
          refine ⟨⟨by omega, ka, hget0, ?_⟩, ?_⟩
          · by_cases haL : target.isLegalTy a = true <;> simp [ka, haL]
          · intro haL; refine ⟨by omega, .normal, ?_, rfl⟩; simpa [ka, haL] using hget0
        have hUb : UnpackBridgeArg target Γ1 b (.var (Γ.length + 1)) := by
          refine ⟨⟨by omega, kb, hget1, ?_⟩, ?_⟩
          · by_cases hbL : target.isLegalTy b = true <;> simp [kb, hbL]
          · intro hbL; refine ⟨by omega, .normal, ?_, rfl⟩; simpa [kb, hbL] using hget1
        change (toTFlat (unpackToLegal target a (.var Γ.length) fun la =>
          unpackToLegal target b (.var (Γ.length + 1)) fun lb => k (tupToSplit hf (tupAppend la lb)))
            Γ1.length Δ.length).isLegal target Γ1 Δ = true
        refine unpackToLegal_isLegal target hv ha a hl'.1 (.var Γ.length) hUa fun Γ2 la hExt12 hla => ?_
        refine unpackToLegal_isLegal target hv ha b hl'.2 (.var (Γ.length + 1)) (hUb.mono hExt12)
          fun Γ3 lb hExt23 hlb => ?_
        exact hk Γ3 (tupToSplit hf (tupAppend la lb)) (hExt1.trans (hExt12.trans hExt23))
          (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hla.mono hExt23) hlb))

/-! ### Generic single-instruction & memory emitters -/

theorem isLegal_let_op1_normal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} {t r : Ty} (code : OpCode [t] [r]) (x : Arg K t) (k : Tup K [r] → Expr K KL rs)
    (hne : code.isPackBridge = false)
    (hcode : target.isLegalOp code false = true)
    (hx : ArgNormal target Γ t x) (hr : target.isLegalTy r = true)
    (hk : (toTFlat (k (Γ.length, ())) ((r, .normal) :: Γ).length Δ.length).isLegal target ((r, .normal) :: Γ) Δ = true) :
    (toTFlat (.let_ (op1 code x) k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  rw [toTFlat_let]; dsimp only [op1, Tup.levels_cons, Tup.levels_nil]
  rw [idxArgs_single, TFlat.isLegal_let_of_normal target Γ Δ _ _ hne]
  have hunif : isUniformImmShift code (idxArg Γ.length x, ()) = false := by
    cases code <;> rfl
  have hchk : checkLegalArgs Γ (ts := [t]) (idxArg Γ.length x, ()) = true := by
    rw [← idxArgs_single]; exact ArgsNormal.checkLegalArgs ⟨hx, trivial⟩
  simp only [hunif, hcode, LegalTarget.isLegalSig, List.all_cons, List.all_nil, hr, Bool.and_true,
    hchk, Bool.true_and]
  have hlen : ((r, .normal) :: Γ).length = Γ.length + [r].length := by simp
  rw [pushNormal, pushTypes_eq_reverse_append]
  simpa [hlen] using hk

theorem isLegal_let_op2_normal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} {t₁ t₂ r : Ty} (code : OpCode [t₁, t₂] [r]) (x : Arg K t₁) (y : Arg K t₂)
    (k : Tup K [r] → Expr K KL rs)
    (hne : code.isPackBridge = false)
    (hcode : target.isLegalOp code (isUniformImmShift code (idxArg Γ.length x, idxArg Γ.length y, ())) = true)
    (hx : ArgNormal target Γ t₁ x) (hy : ArgNormal target Γ t₂ y) (hr : target.isLegalTy r = true)
    (hk : (toTFlat (k (Γ.length, ())) ((r, .normal) :: Γ).length Δ.length).isLegal target ((r, .normal) :: Γ) Δ = true) :
    (toTFlat (.let_ (op2 code x y) k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  rw [toTFlat_let]; dsimp only [op2, Tup.levels_cons, Tup.levels_nil]
  rw [idxArgs_pair, TFlat.isLegal_let_of_normal target Γ Δ _ _ hne]
  have hchk : checkLegalArgs Γ (ts := [t₁, t₂]) (idxArg Γ.length x, idxArg Γ.length y, ()) = true := by
    rw [← idxArgs_pair]; exact ArgsNormal.checkLegalArgs ⟨hx, hy, trivial⟩
  simp only [hcode, LegalTarget.isLegalSig, List.all_cons, List.all_nil, hr, Bool.and_true,
    hchk, Bool.true_and]
  have hlen : ((r, .normal) :: Γ).length = Γ.length + [r].length := by simp
  rw [pushNormal, pushTypes_eq_reverse_append]
  simpa [hlen] using hk

theorem isLegal_let_op2_2res (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} {t₁ t₂ r₁ r₂ : Ty} (code : OpCode [t₁, t₂] [r₁, r₂]) (x : Arg K t₁) (y : Arg K t₂)
    (k : Tup K [r₁, r₂] → Expr K KL rs)
    (hne : code.isPackBridge = false)
    (hcode : target.isLegalOp code false = true)
    (hx : ArgNormal target Γ t₁ x) (hy : ArgNormal target Γ t₂ y)
    (hr₁ : target.isLegalTy r₁ = true) (hr₂ : target.isLegalTy r₂ = true)
    (hk : (toTFlat (k (Γ.length, Γ.length + 1, ())) (pushNormal [r₁, r₂] Γ).length Δ.length).isLegal
      target (pushNormal [r₁, r₂] Γ) Δ = true) :
    (toTFlat (.let_ (op2 code x y) k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  rw [toTFlat_let]; dsimp only [op2, Tup.levels_cons, Tup.levels_nil]
  rw [idxArgs_pair, TFlat.isLegal_let_of_normal target Γ Δ _ _ hne]
  have hunif : isUniformImmShift code (idxArg Γ.length x, idxArg Γ.length y, ()) = false := by
    cases code <;> rfl
  have hchk : checkLegalArgs Γ (ts := [t₁, t₂]) (idxArg Γ.length x, idxArg Γ.length y, ()) = true := by
    rw [← idxArgs_pair]; exact ArgsNormal.checkLegalArgs ⟨hx, hy, trivial⟩
  simp only [hunif, hcode, LegalTarget.isLegalSig, List.all_cons, List.all_nil, hr₁, hr₂, Bool.and_true,
    hchk, Bool.true_and]
  have hlen : (pushNormal [r₁, r₂] Γ).length = Γ.length + [r₁, r₂].length := by
    simp [pushNormal_length, Nat.add_comm]
  rw [← hlen]
  exact hk

theorem isLegal_let_op3_normal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} {t₁ t₂ t₃ r : Ty} (code : OpCode [t₁, t₂, t₃] [r])
    (x : Arg K t₁) (y : Arg K t₂) (z : Arg K t₃) (k : Tup K [r] → Expr K KL rs)
    (hne : code.isPackBridge = false)
    (hcode : target.isLegalOp code false = true)
    (hx : ArgNormal target Γ t₁ x) (hy : ArgNormal target Γ t₂ y) (hz : ArgNormal target Γ t₃ z)
    (hr : target.isLegalTy r = true)
    (hk : (toTFlat (k (Γ.length, ())) ((r, .normal) :: Γ).length Δ.length).isLegal target ((r, .normal) :: Γ) Δ = true) :
    (toTFlat (.let_ (op3 code x y z) k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  rw [toTFlat_let]; dsimp only [op3, Tup.levels_cons, Tup.levels_nil]
  rw [idxArgs_triple, TFlat.isLegal_let_of_normal target Γ Δ _ _ hne]
  have hunif : isUniformImmShift code (idxArg Γ.length x, idxArg Γ.length y, idxArg Γ.length z, ()) = false := by
    cases code <;> rfl
  have hchk : checkLegalArgs Γ (ts := [t₁, t₂, t₃]) (idxArg Γ.length x, idxArg Γ.length y, idxArg Γ.length z, ()) = true := by
    rw [← idxArgs_triple]; exact ArgsNormal.checkLegalArgs ⟨hx, hy, hz, trivial⟩
  simp only [hunif, hcode, LegalTarget.isLegalSig, List.all_cons, List.all_nil, hr, Bool.and_true,
    hchk, Bool.true_and]
  have hlen : ((r, .normal) :: Γ).length = Γ.length + [r].length := by simp
  rw [pushNormal, pushTypes_eq_reverse_append]
  simpa [hlen] using hk

theorem isLegal_let_op3_2res (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} {t₁ t₂ t₃ r₁ r₂ : Ty} (code : OpCode [t₁, t₂, t₃] [r₁, r₂])
    (x : Arg K t₁) (y : Arg K t₂) (z : Arg K t₃) (k : Tup K [r₁, r₂] → Expr K KL rs)
    (hne : code.isPackBridge = false)
    (hcode : target.isLegalOp code false = true)
    (hx : ArgNormal target Γ t₁ x) (hy : ArgNormal target Γ t₂ y) (hz : ArgNormal target Γ t₃ z)
    (hr₁ : target.isLegalTy r₁ = true) (hr₂ : target.isLegalTy r₂ = true)
    (hk : (toTFlat (k (Γ.length, Γ.length + 1, ())) (pushNormal [r₁, r₂] Γ).length Δ.length).isLegal
      target (pushNormal [r₁, r₂] Γ) Δ = true) :
    (toTFlat (.let_ (op3 code x y z) k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  rw [toTFlat_let]; dsimp only [op3, Tup.levels_cons, Tup.levels_nil]
  rw [idxArgs_triple, TFlat.isLegal_let_of_normal target Γ Δ _ _ hne]
  have hunif : isUniformImmShift code (idxArg Γ.length x, idxArg Γ.length y, idxArg Γ.length z, ()) = false := by
    cases code <;> rfl
  have hchk : checkLegalArgs Γ (ts := [t₁, t₂, t₃]) (idxArg Γ.length x, idxArg Γ.length y, idxArg Γ.length z, ()) = true := by
    rw [← idxArgs_triple]; exact ArgsNormal.checkLegalArgs ⟨hx, hy, hz, trivial⟩
  simp only [hunif, hcode, LegalTarget.isLegalSig, List.all_cons, List.all_nil, hr₁, hr₂, Bool.and_true,
    hchk, Bool.true_and]
  have hlen : (pushNormal [r₁, r₂] Γ).length = Γ.length + [r₁, r₂].length := by
    simp [pushNormal_length, Nat.add_comm]
  rw [← hlen]
  exact hk

theorem isLegal_load_normal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} (t : Ty) (a : Arg K i64) (k : K t → Expr K KL rs)
    (ht : target.isLegalTy t = true) (ha : ArgNormal target Γ i64 a)
    (hk : (toTFlat (k Γ.length) ((t, .normal) :: Γ).length Δ.length).isLegal target ((t, .normal) :: Γ) Δ = true) :
    (toTFlat (.load t a k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  rw [toTFlat_load, TFlat.isLegal_load]
  simp only [ht, ha.checkLegalArg, Bool.true_and]
  have hlen : ((t, .normal) :: Γ).length = Γ.length + 1 := by simp
  rw [← hlen]; exact hk

theorem isLegal_store_normal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} (t : Ty) (v : Arg K t) (a : Arg K i64) (k : Expr K KL rs)
    (ht : target.isLegalTy t = true) (hv : ArgNormal target Γ t v) (ha : ArgNormal target Γ i64 a)
    (hk : (toTFlat k Γ.length Δ.length).isLegal target Γ Δ = true) :
    (toTFlat (.store v a k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  rw [toTFlat_store, TFlat.isLegal_store]
  simp [ht, hv.checkLegalArg, ha.checkLegalArg, hk]

theorem uniformShiftLeaf?_splatBits :
    ∀ (u : Ty) (c : Val u) {w s : Nat} (v : BitVec w),
      uniformShiftLeaf? u c = some (w, s) →
      uniformShiftLeaf? u (splatBits w v u) = some (w, v.toNat % w)
  | .bool, _, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .bits n, c, w, s, v, h => by
    simp only [uniformShiftLeaf?] at h
    cases hn0 : (n == 0)
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      simp [splatBits, uniformShiftLeaf?, hn0]
    · simp [hn0] at h
  | .pair a b, c, w, s, v, h => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a c.1 with
    | none => simp [ha] at h
    | some p =>
      cases hb : uniformShiftLeaf? b c.2 with
      | none => simp [ha, hb] at h
      | some q =>
        simp only [ha, hb, bind, Option.bind] at h
        split at h <;> simp at h
        rename_i hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        rcases h with ⟨rfl, _⟩
        have iha := uniformShiftLeaf?_splatBits a c.1 v ha
        have ihb := uniformShiftLeaf?_splatBits b c.2 v (s := q.2) (by rw [hb, hcond.1])
        simp only [splatBits, uniformShiftLeaf?, iha, ihb, bind, Option.bind]
        simp

/-! ### Bit, bool, load/store, word64, and SIMD scalar helper lemmas -/

theorem emitMaskToN_isLegal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} {n w : Nat} (hw : w ∈ target.bitWidths)
    (x : Arg K (.bits w)) (hx : ArgNormal target Γ (.bits w) x)
    {k : Arg K (.bits w) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k) :
    (toTFlat (emitMaskToN n w x k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
  simp only [emitMaskToN]
  by_cases hn0 : (n == 0) = true
  · simp only [hn0, ↓reduceIte]; exact hk Γ (.imm 0#w) (CtxExtends.refl Γ) hleg
  · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
    by_cases hwn : w ≤ n
    · simp only [hwn, ↓reduceIte]; exact hk Γ x (CtxExtends.refl Γ) hx
    · simp only [hwn, ↓reduceIte]
      refine isLegal_let_op2_normal target (.and (.bits w)) x (.imm _) _
        rfl (by simp [LegalTarget.isLegalOp, hw]) hx hleg hleg ?_
      exact hk ((.bits w, .normal) :: Γ) (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)

theorem emitSextToW_isLegal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} {n w : Nat} (hw : w ∈ target.bitWidths)
    (x : Arg K (.bits w)) (hx : ArgNormal target Γ (.bits w) x)
    {k : Arg K (.bits w) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k) :
    (toTFlat (emitSextToW n w x k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
  simp only [emitSextToW]
  by_cases hskip : (n == 0 || decide (w ≤ n)) = true
  · simp only [hskip, ↓reduceIte]; exact hk Γ x (CtxExtends.refl Γ) hx
  · simp only [hskip, Bool.false_eq_true, ↓reduceIte]
    refine isLegal_let_op2_normal target (.shl (.bits w)) x (.imm _) _ rfl
      (by simp [LegalTarget.isLegalOp, hw]) hx hleg hleg ?_
    let Γ1 := (.bits w, VarKind.normal) :: Γ
    refine isLegal_let_op2_normal target (.ashr (.bits w)) (.var Γ.length) (.imm _) _
      rfl (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ hleg) hleg hleg ?_
    exact hk ((.bits w, .normal) :: Γ1) (.var Γ1.length)
      ((CtxExtends.cons _ Γ).trans (CtxExtends.cons _ Γ1)) (ArgNormal.head target Γ1 hleg)

theorem emitCountMod_isLegal (target : LegalTarget) (hv : target.valid = true)
    {Γ : List (Ty × VarKind)} {Δ : List (List Ty)} {rs : List Ty} {n w : Nat} (hw : w ∈ target.bitWidths)
    (c : Arg K (.bits w)) (hc : ArgNormal target Γ (.bits w) c)
    {k : Arg K (.bits w) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k) :
    (toTFlat (emitCountMod n w c k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
  have hwpos : 0 < w := (valid_bitWidth_spec hv hw).1
  simp only [emitCountMod]
  cases c with
  | imm cb => exact hk Γ (.imm _) (CtxExtends.refl Γ) hleg
  | var _ =>
    refine isLegal_let_op2_normal target (.urem w) _ (.imm _) _ rfl
      (by simp [LegalTarget.isLegalOp, hw, hwpos]) hc hleg hleg ?_
    exact hk ((.bits w, .normal) :: Γ) (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)

theorem emitBoolCmp_isLegal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} (o : CmpOp) (a b : Arg K .bool)
    (ha : ArgNormal target Γ .bool a) (hb : ArgNormal target Γ .bool b)
    {k : Arg K .bool → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' .bool r) k) :
    (toTFlat (emitBoolCmp o a b k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have h1 : ∀ {Γ0 : List (Ty × VarKind)} (x : Arg K .bool), ArgNormal target Γ0 .bool x →
      ∀ (k' : Arg K .bool → Expr K KL rs),
      IsLegalCont target Γ0 Δ (fun Γ' r => ArgNormal target Γ' .bool r) k' →
      (toTFlat (.let_ (op1 (.not .bool) x) fun (na, ()) => k' (.var na)) Γ0.length Δ.length).isLegal target Γ0 Δ = true := by
    intro Γ0 x hx k' hk'
    refine isLegal_let_op1_normal target (.not .bool) x _ rfl rfl hx rfl ?_
    exact hk' ((.bool, .normal) :: Γ0) (.var Γ0.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ0 rfl)
  have h2 : ∀ {Γ0 : List (Ty × VarKind)} (mk : OpCode [.bool, .bool] [.bool])
      (x y : Arg K .bool), mk.isPackBridge = false → target.isLegalOp mk false = true →
      (∀ xs, isUniformImmShift mk xs = false) →
      ArgNormal target Γ0 .bool x → ArgNormal target Γ0 .bool y →
      ∀ (k' : Arg K .bool → Expr K KL rs),
      IsLegalCont target Γ0 Δ (fun Γ' r => ArgNormal target Γ' .bool r) k' →
      (toTFlat (.let_ (op2 mk x y) fun (r, ()) => k' (.var r)) Γ0.length Δ.length).isLegal target Γ0 Δ = true := by
    intro Γ0 mk x y hne hcode hnu hx hy k' hk'
    refine isLegal_let_op2_normal target mk x y _ hne (by rw [hnu]; exact hcode) hx hy rfl ?_
    exact hk' ((.bool, .normal) :: Γ0) (.var Γ0.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ0 rfl)
  cases o <;> simp only [emitBoolCmp]
  · refine h2 (.xor .bool) a b rfl rfl (fun _ => rfl) ha hb _ fun Γ1 x h1x hx =>
      h1 x hx _ fun Γ2 r h2r hr => hk Γ2 r (h1x.trans h2r) hr
  · exact h2 (.xor .bool) a b rfl rfl (fun _ => rfl) ha hb _ hk
  · refine h1 a ha _ fun Γ1 na h1x hna =>
      h2 (.and .bool) na b rfl rfl (fun _ => rfl) hna (hb.mono h1x) _ fun Γ2 r h2r hr => hk Γ2 r (h1x.trans h2r) hr
  · refine h1 a ha _ fun Γ1 na h1x hna =>
      h2 (.or .bool) na b rfl rfl (fun _ => rfl) hna (hb.mono h1x) _ fun Γ2 r h2r hr => hk Γ2 r (h1x.trans h2r) hr
  · refine h1 b hb _ fun Γ1 nb h1x hnb =>
      h2 (.and .bool) a nb rfl rfl (fun _ => rfl) (ha.mono h1x) hnb _ fun Γ2 r h2r hr => hk Γ2 r (h1x.trans h2r) hr
  · refine h1 b hb _ fun Γ1 nb h1x hnb =>
      h2 (.or .bool) a nb rfl rfl (fun _ => rfl) (ha.mono h1x) hnb _ fun Γ2 r h2r hr => hk Γ2 r (h1x.trans h2r) hr
  · refine h1 b hb _ fun Γ1 nb h1x hnb =>
      h2 (.and .bool) a nb rfl rfl (fun _ => rfl) (ha.mono h1x) hnb _ fun Γ2 r h2r hr => hk Γ2 r (h1x.trans h2r) hr
  · refine h1 b hb _ fun Γ1 nb h1x hnb =>
      h2 (.or .bool) a nb rfl rfl (fun _ => rfl) (ha.mono h1x) hnb _ fun Γ2 r h2r hr => hk Γ2 r (h1x.trans h2r) hr
  · refine h1 a ha _ fun Γ1 na h1x hna =>
      h2 (.and .bool) na b rfl rfl (fun _ => rfl) hna (hb.mono h1x) _ fun Γ2 r h2r hr => hk Γ2 r (h1x.trans h2r) hr
  · refine h1 a ha _ fun Γ1 na h1x hna =>
      h2 (.or .bool) na b rfl rfl (fun _ => rfl) hna (hb.mono h1x) _ fun Γ2 r h2r hr => hk Γ2 r (h1x.trans h2r) hr

theorem emitBoolSelect_isLegal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} (c a b : Arg K .bool)
    (hc : ArgNormal target Γ .bool c) (ha : ArgNormal target Γ .bool a) (hb : ArgNormal target Γ .bool b)
    {k : Arg K .bool → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' .bool r) k) :
    (toTFlat (emitBoolSelect c a b k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  simp only [emitBoolSelect]
  refine isLegal_let_op2_normal target (.and .bool) c a _ rfl rfl hc ha rfl ?_
  let Γ1 := (.bool, VarKind.normal) :: Γ
  have h1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
  refine isLegal_let_op1_normal target (.not .bool) c _ rfl rfl (hc.mono h1) rfl ?_
  let Γ2 := (.bool, VarKind.normal) :: Γ1
  have h2 : CtxExtends Γ1 Γ2 := CtxExtends.cons _ _
  refine isLegal_let_op2_normal target (.and .bool) (.var Γ1.length) b _ rfl rfl
    (ArgNormal.head target Γ1 rfl) (hb.mono (h1.trans h2)) rfl ?_
  let Γ3 := (.bool, VarKind.normal) :: Γ2
  have h3 : CtxExtends Γ2 Γ3 := CtxExtends.cons _ _
  refine isLegal_let_op2_normal target (.or .bool) (.var Γ.length) (.var Γ2.length) _
    rfl rfl ((ArgNormal.head target Γ rfl).mono (h2.trans h3)) (ArgNormal.head target Γ2 rfl) rfl ?_
  exact hk ((.bool, .normal) :: Γ3) (.var Γ3.length)
    (h1.trans (h2.trans (h3.trans (CtxExtends.cons _ _)))) (ArgNormal.head target Γ3 rfl)

theorem emitTernlogBool_go_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (imm : BitVec 8) (k : Arg K .bool → Expr K KL rs)
    (a b c na nb nc : Arg K .bool) :
    ∀ (idx : Nat) {Γ : List (Ty × VarKind)},
      ArgNormal target Γ .bool a → ArgNormal target Γ .bool b → ArgNormal target Γ .bool c →
      ArgNormal target Γ .bool na → ArgNormal target Γ .bool nb → ArgNormal target Γ .bool nc →
      ∀ (acc : Option (Arg K .bool)),
        (∀ x, acc = some x → ArgNormal target Γ .bool x) →
        IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' .bool r) k →
        (toTFlat (emitTernlogBool.go imm k idx acc a b c na nb nc) Γ.length Δ.length).isLegal target Γ Δ = true
  | idx, Γ, ha, hb, hc, hna, hnb, hnc, acc, hacc, hk => by
    rw [emitTernlogBool.go.eq_def]
    split
    · cases acc with
      | some res => exact hk Γ res (CtxExtends.refl Γ) (hacc res rfl)
      | none => exact hk Γ (.imm false) (CtxExtends.refl Γ) rfl
    · split
      · let pa := if (idx / 4 % 2 == 1) = true then a else na
        let pb := if (idx / 2 % 2 == 1) = true then b else nb
        let pc := if (idx % 2 == 1) = true then c else nc
        have hpa : ArgNormal target Γ .bool pa := by by_cases h : (idx / 4 % 2 == 1) = true <;> simp [pa, h, ha, hna]
        have hpb : ArgNormal target Γ .bool pb := by by_cases h : (idx / 2 % 2 == 1) = true <;> simp [pb, h, hb, hnb]
        have hpc : ArgNormal target Γ .bool pc := by by_cases h : (idx % 2 == 1) = true <;> simp [pc, h, hc, hnc]
        refine isLegal_let_op2_normal target (.and .bool) pa pb _ rfl rfl hpa hpb rfl ?_
        let Γ1 := (.bool, VarKind.normal) :: Γ
        have h1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
        refine isLegal_let_op2_normal target (.and .bool) (.var Γ.length) pc _ rfl rfl
          (ArgNormal.head target Γ rfl) (hpc.mono h1) rfl ?_
        let Γ2 := (.bool, VarKind.normal) :: Γ1
        have h2 : CtxExtends Γ1 Γ2 := CtxExtends.cons _ _
        have h12 : CtxExtends Γ Γ2 := h1.trans h2
        cases acc with
        | none =>
          exact emitTernlogBool_go_isLegal target imm k a b c na nb nc (idx + 1)
            (ha.mono h12) (hb.mono h12) (hc.mono h12) (hna.mono h12) (hnb.mono h12) (hnc.mono h12)
            (some (.var Γ1.length)) (fun x hx => by cases hx; exact ArgNormal.head target Γ1 rfl)
            (fun Γ' r hrExt hr => hk Γ' r (h12.trans hrExt) hr)
        | some prev =>
          have hprev : ArgNormal target Γ2 .bool prev := (hacc prev rfl).mono h12
          refine isLegal_let_op2_normal target (.or .bool) prev (.var Γ1.length) _ rfl rfl
            hprev (ArgNormal.head target Γ1 rfl) rfl ?_
          let Γ3 := (.bool, VarKind.normal) :: Γ2
          have h3 : CtxExtends Γ2 Γ3 := CtxExtends.cons _ _
          have h13 : CtxExtends Γ Γ3 := h12.trans h3
          exact emitTernlogBool_go_isLegal target imm k a b c na nb nc (idx + 1)
            (ha.mono h13) (hb.mono h13) (hc.mono h13) (hna.mono h13) (hnb.mono h13) (hnc.mono h13)
            (some (.var Γ2.length)) (fun x hx => by cases hx; exact ArgNormal.head target Γ2 rfl)
            (fun Γ' r hrExt hr => hk Γ' r (h13.trans hrExt) hr)
      · exact emitTernlogBool_go_isLegal target imm k a b c na nb nc (idx + 1) ha hb hc hna hnb hnc acc hacc hk
termination_by idx => 8 - idx

theorem emitTernlogBool_isLegal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} (a b c : Arg K .bool) (imm : BitVec 8)
    (ha : ArgNormal target Γ .bool a) (hb : ArgNormal target Γ .bool b) (hc : ArgNormal target Γ .bool c)
    {k : Arg K .bool → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' .bool r) k) :
    (toTFlat (emitTernlogBool a b c imm k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  simp only [emitTernlogBool]
  split
  · exact hk Γ (.imm false) (CtxExtends.refl Γ) rfl
  · split
    · exact hk Γ (.imm true) (CtxExtends.refl Γ) rfl
    · refine isLegal_let_op1_normal target (.not .bool) a _ rfl rfl ha rfl ?_
      let Γ1 := (.bool, VarKind.normal) :: Γ
      have h1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
      refine isLegal_let_op1_normal target (.not .bool) b _ rfl rfl (hb.mono h1) rfl ?_
      let Γ2 := (.bool, VarKind.normal) :: Γ1
      have h2 : CtxExtends Γ1 Γ2 := CtxExtends.cons _ _
      refine isLegal_let_op1_normal target (.not .bool) c _ rfl rfl (hc.mono (h1.trans h2)) rfl ?_
      let Γ3 := (.bool, VarKind.normal) :: Γ2
      have h3 : CtxExtends Γ2 Γ3 := CtxExtends.cons _ _
      have h13 : CtxExtends Γ Γ3 := h1.trans (h2.trans h3)
      exact emitTernlogBool_go_isLegal target imm k a b c (.var Γ.length) (.var Γ1.length) (.var Γ2.length) 0
        (ha.mono h13) (hb.mono h13) (hc.mono h13)
        ((ArgNormal.head target Γ rfl).mono (h2.trans h3))
        ((ArgNormal.head target Γ1 rfl).mono h3)
        (ArgNormal.head target Γ2 rfl) none (fun _ h => by cases h)
        (fun Γ' r hrExt hr => hk Γ' r (h13.trans hrExt) hr)

theorem emitTernlogBits_go_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    {w : Nat} (hw : w ∈ target.bitWidths) (imm : BitVec 8) (k : Arg K (.bits w) → Expr K KL rs)
    (a b c na nb nc : Arg K (.bits w)) :
    ∀ (idx : Nat) {Γ : List (Ty × VarKind)},
      ArgNormal target Γ (.bits w) a → ArgNormal target Γ (.bits w) b → ArgNormal target Γ (.bits w) c →
      ArgNormal target Γ (.bits w) na → ArgNormal target Γ (.bits w) nb → ArgNormal target Γ (.bits w) nc →
      ∀ (acc : Option (Arg K (.bits w))),
        (∀ x, acc = some x → ArgNormal target Γ (.bits w) x) →
        IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k →
        (toTFlat (emitTernlogBits.go w imm k idx acc a b c na nb nc) Γ.length Δ.length).isLegal target Γ Δ = true
  | idx, Γ, ha, hb, hc, hna, hnb, hnc, acc, hacc, hk => by
    have hleg : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
    rw [emitTernlogBits.go.eq_def]
    split
    · cases acc with
      | some res => exact hk Γ res (CtxExtends.refl Γ) (hacc res rfl)
      | none => exact hk Γ (.imm 0#w) (CtxExtends.refl Γ) hleg
    · split
      · let pa := if (idx / 4 % 2 == 1) = true then a else na
        let pb := if (idx / 2 % 2 == 1) = true then b else nb
        let pc := if (idx % 2 == 1) = true then c else nc
        have hpa : ArgNormal target Γ (.bits w) pa := by by_cases h : (idx / 4 % 2 == 1) = true <;> simp [pa, h, ha, hna]
        have hpb : ArgNormal target Γ (.bits w) pb := by by_cases h : (idx / 2 % 2 == 1) = true <;> simp [pb, h, hb, hnb]
        have hpc : ArgNormal target Γ (.bits w) pc := by by_cases h : (idx % 2 == 1) = true <;> simp [pc, h, hc, hnc]
        refine isLegal_let_op2_normal target (.and (.bits w)) pa pb _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hpa hpb hleg ?_
        let Γ1 := (.bits w, VarKind.normal) :: Γ
        have h1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
        refine isLegal_let_op2_normal target (.and (.bits w)) (.var Γ.length) pc _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ hleg) (hpc.mono h1) hleg ?_
        let Γ2 := (.bits w, VarKind.normal) :: Γ1
        have h2 : CtxExtends Γ1 Γ2 := CtxExtends.cons _ _
        have h12 : CtxExtends Γ Γ2 := h1.trans h2
        cases acc with
        | none =>
          exact emitTernlogBits_go_isLegal target hw imm k a b c na nb nc (idx + 1)
            (ha.mono h12) (hb.mono h12) (hc.mono h12) (hna.mono h12) (hnb.mono h12) (hnc.mono h12)
            (some (.var Γ1.length)) (fun x hx => by cases hx; exact ArgNormal.head target Γ1 hleg)
            (fun Γ' r hrExt hr => hk Γ' r (h12.trans hrExt) hr)
        | some prev =>
          have hprev : ArgNormal target Γ2 (.bits w) prev := (hacc prev rfl).mono h12
          refine isLegal_let_op2_normal target (.or (.bits w)) prev (.var Γ1.length) _ rfl
            (by simp [LegalTarget.isLegalOp, hw]) hprev (ArgNormal.head target Γ1 hleg) hleg ?_
          let Γ3 := (.bits w, VarKind.normal) :: Γ2
          have h3 : CtxExtends Γ2 Γ3 := CtxExtends.cons _ _
          have h13 : CtxExtends Γ Γ3 := h12.trans h3
          exact emitTernlogBits_go_isLegal target hw imm k a b c na nb nc (idx + 1)
            (ha.mono h13) (hb.mono h13) (hc.mono h13) (hna.mono h13) (hnb.mono h13) (hnc.mono h13)
            (some (.var Γ2.length)) (fun x hx => by cases hx; exact ArgNormal.head target Γ2 hleg)
            (fun Γ' r hrExt hr => hk Γ' r (h13.trans hrExt) hr)
      · exact emitTernlogBits_go_isLegal target hw imm k a b c na nb nc (idx + 1) ha hb hc hna hnb hnc acc hacc hk
termination_by idx => 8 - idx

theorem emitTernlogBits_isLegal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} {w : Nat} (hw : w ∈ target.bitWidths) (a b c : Arg K (.bits w)) (imm : BitVec 8)
    (ha : ArgNormal target Γ (.bits w) a) (hb : ArgNormal target Γ (.bits w) b) (hc : ArgNormal target Γ (.bits w) c)
    {k : Arg K (.bits w) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k) :
    (toTFlat (emitTernlogBits w a b c imm k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
  simp only [emitTernlogBits]
  split
  · exact hk Γ (.imm 0#w) (CtxExtends.refl Γ) hleg
  · split
    · exact hk Γ (.imm (BitVec.allOnes w)) (CtxExtends.refl Γ) hleg
    · refine isLegal_let_op1_normal target (.not (.bits w)) a _ rfl (by simp [LegalTarget.isLegalOp, hw]) ha hleg ?_
      let Γ1 := (.bits w, VarKind.normal) :: Γ
      have h1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
      refine isLegal_let_op1_normal target (.not (.bits w)) b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) (hb.mono h1) hleg ?_
      let Γ2 := (.bits w, VarKind.normal) :: Γ1
      have h2 : CtxExtends Γ1 Γ2 := CtxExtends.cons _ _
      refine isLegal_let_op1_normal target (.not (.bits w)) c _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) (hc.mono (h1.trans h2)) hleg ?_
      let Γ3 := (.bits w, VarKind.normal) :: Γ2
      have h3 : CtxExtends Γ2 Γ3 := CtxExtends.cons _ _
      have h13 : CtxExtends Γ Γ3 := h1.trans (h2.trans h3)
      exact emitTernlogBits_go_isLegal target hw imm k a b c (.var Γ.length) (.var Γ1.length) (.var Γ2.length) 0
        (ha.mono h13) (hb.mono h13) (hc.mono h13)
        ((ArgNormal.head target Γ hleg).mono (h2.trans h3))
        ((ArgNormal.head target Γ1 hleg).mono h3)
        (ArgNormal.head target Γ2 hleg) none (fun _ h => by cases h)
        (fun Γ' r hrExt hr => hk Γ' r (h13.trans hrExt) hr)

theorem legalBitsArith_isLegal (target : LegalTarget) (hv : target.valid = true)
    {Γ : List (Ty × VarKind)} {Δ : List (List Ty)} {rs : List Ty}
    {n : Nat} (hsn : target.supportsTy (.bits n) = true)
    (code : OpCode [.bits n, .bits n] [.bits n])
    (a b : Arg K (.bits (target.widenWidth n)))
    (ha : ArgNormal target Γ (.bits (target.widenWidth n)) a)
    (hb : ArgNormal target Γ (.bits (target.widenWidth n)) b)
    {k : Arg K (.bits (target.widenWidth n)) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits (target.widenWidth n)) r) k) :
    (toTFlat (legalBitsArith target n code a b k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hw : target.widenWidth n ∈ target.bitWidths := widenWidth_mem_of_supports hsn
  have hleg : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
  simp only [legalBitsArith]
  by_cases hn0 : (n == 0) = true
  · simp only [hn0, ↓reduceIte]; exact hk Γ (.imm _) (CtxExtends.refl Γ) hleg
  · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
    cases code with
    | add _ =>
      refine isLegal_let_op2_normal target (.add (.bits (target.widenWidth n))) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
      let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ
      exact emitMaskToN_isLegal target hw (.var Γ.length) (ArgNormal.head target Γ hleg)
        fun Γ' r hrExt hr => hk Γ' r ((CtxExtends.cons _ _).trans hrExt) hr
    | sub _ =>
      refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
      exact emitMaskToN_isLegal target hw (.var Γ.length) (ArgNormal.head target Γ hleg)
        fun Γ' r hrExt hr => hk Γ' r ((CtxExtends.cons _ _).trans hrExt) hr
    | mul _ =>
      refine isLegal_let_op2_normal target (.mul (.bits (target.widenWidth n))) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
      exact emitMaskToN_isLegal target hw (.var Γ.length) (ArgNormal.head target Γ hleg)
        fun Γ' r hrExt hr => hk Γ' r ((CtxExtends.cons _ _).trans hrExt) hr
    | and _ =>
      refine isLegal_let_op2_normal target (.and (.bits (target.widenWidth n))) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
      exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
    | or _ =>
      refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
      exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
    | xor _ =>
      refine isLegal_let_op2_normal target (.xor (.bits (target.widenWidth n))) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
      exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
    | shl _ =>
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n))) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
        exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw b hb fun Γ1 c hcExt hc => ?_
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n))) a c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono hcExt) hc hleg ?_
        exact emitMaskToN_isLegal target hw (.var Γ1.length) (ArgNormal.head target Γ1 hleg)
          fun Γ2 r hrExt hr => hk Γ2 r (hcExt.trans ((CtxExtends.cons _ _).trans hrExt)) hr
    | lshr _ =>
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
        exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw b hb fun Γ1 c hcExt hc => ?_
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) a c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono hcExt) hc hleg ?_
        exact hk _ (.var Γ1.length) (hcExt.trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ1 hleg)
    | ashr _ =>
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.ashr (.bits (target.widenWidth n))) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
        exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw b hb fun Γ1 c hcExt hc => ?_
        refine emitSextToW_isLegal target hw a (ha.mono hcExt) fun Γ2 sa hsaExt hsa => ?_
        refine isLegal_let_op2_normal target (.ashr (.bits (target.widenWidth n))) sa c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hsa (hc.mono hsaExt) hleg ?_
        exact emitMaskToN_isLegal target hw (.var Γ2.length) (ArgNormal.head target Γ2 hleg)
          fun Γ3 r hrExt hr => hk Γ3 r (hcExt.trans (hsaExt.trans ((CtxExtends.cons _ _).trans hrExt))) hr
    | rotl _ =>
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.rotl (.bits (target.widenWidth n))) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
        exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw b hb fun Γ1 c hcExt hc => ?_
        refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) (.imm _) c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hleg hc hleg ?_
        let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
        have h12 : CtxExtends Γ Γ2 := hcExt.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n))) a c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h12) (hc.mono (CtxExtends.cons _ _)) hleg ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        have h13 : CtxExtends Γ Γ3 := h12.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) a (.var Γ1.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h13) ((ArgNormal.head target Γ1 hleg).mono (CtxExtends.cons _ _)) hleg ?_
        let Γ4 := (.bits (target.widenWidth n), VarKind.normal) :: Γ3
        have h14 : CtxExtends Γ Γ4 := h13.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (.var Γ2.length) (.var Γ3.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ((ArgNormal.head target Γ2 hleg).mono (CtxExtends.cons _ _))
          (ArgNormal.head target Γ3 hleg) hleg ?_
        exact emitMaskToN_isLegal target hw (.var Γ4.length) (ArgNormal.head target Γ4 hleg)
          fun Γ5 r hrExt hr => hk Γ5 r (h14.trans ((CtxExtends.cons _ _).trans hrExt)) hr
    | rotr _ =>
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.rotr (.bits (target.widenWidth n))) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ha hb hleg ?_
        exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg)
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_isLegal target hv hw b hb fun Γ1 c hcExt hc => ?_
        refine isLegal_let_op2_normal target (.sub (.bits (target.widenWidth n))) (.imm _) c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hleg hc hleg ?_
        let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
        have h12 : CtxExtends Γ Γ2 := hcExt.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n))) a c _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h12) (hc.mono (CtxExtends.cons _ _)) hleg ?_
        let Γ3 := (.bits (target.widenWidth n), VarKind.normal) :: Γ2
        have h13 : CtxExtends Γ Γ3 := h12.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.shl (.bits (target.widenWidth n))) a (.var Γ1.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (ha.mono h13) ((ArgNormal.head target Γ1 hleg).mono (CtxExtends.cons _ _)) hleg ?_
        let Γ4 := (.bits (target.widenWidth n), VarKind.normal) :: Γ3
        have h14 : CtxExtends Γ Γ4 := h13.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.or (.bits (target.widenWidth n))) (.var Γ2.length) (.var Γ3.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ((ArgNormal.head target Γ2 hleg).mono (CtxExtends.cons _ _))
          (ArgNormal.head target Γ3 hleg) hleg ?_
        exact emitMaskToN_isLegal target hw (.var Γ4.length) (ArgNormal.head target Γ4 hleg)
          fun Γ5 r hrExt hr => hk Γ5 r (h14.trans ((CtxExtends.cons _ _).trans hrExt)) hr
    | _ => simp [toTFlat_hlt]

theorem ArgNormal_getD_i64 (target : LegalTarget) {Γ : List (Ty × VarKind)} (h64 : 64 ∈ target.bitWidths)
    (ws : List (Arg K i64)) (hws : ∀ x ∈ ws, ArgNormal target Γ i64 x) (i : Nat) :
    ArgNormal target Γ i64 (ws.getD i (.imm 0#64)) := by
  have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
  induction ws generalizing i with
  | nil => simp [List.getD]; exact hleg64
  | cons w ws ih =>
    cases i with
    | zero => exact hws w (by simp)
    | succ i => exact ih (fun x hx => hws x (by simp [hx])) i

theorem pushLeafWord64_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h64 : 64 ∈ target.bitWidths) (w : Nat) :
    ∀ {Γ : List (Ty × VarKind)} (leaf : Arg K i64) (ws : List (Arg K i64)) (acc : Arg K i64) (accBits : Nat),
      ArgNormal target Γ i64 leaf → (∀ x ∈ ws, ArgNormal target Γ i64 x) → ArgNormal target Γ i64 acc →
      ∀ {k : List (Arg K i64) → Arg K i64 → Nat → Expr K KL rs},
      (∀ Γ' ws' acc' bits', CtxExtends Γ Γ' →
        (∀ x ∈ ws', ArgNormal target Γ' i64 x) → ArgNormal target Γ' i64 acc' →
        (toTFlat (k ws' acc' bits') Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (pushLeafWord64 w leaf ws acc accBits k) Γ.length Δ.length).isLegal target Γ Δ = true
  | Γ, leaf, ws, acc, accBits, hleaf, hws, hacc, k, hk => by
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    simp only [pushLeafWord64]
    by_cases hw0 : (w == 0) = true
    · simp only [hw0, ↓reduceIte]; exact hk Γ ws acc accBits (CtxExtends.refl Γ) hws hacc
    · simp only [hw0, Bool.false_eq_true, ↓reduceIte]
      by_cases hab0 : (accBits == 0) = true
      · simp only [hab0, ↓reduceIte]
        by_cases hw64 : 64 ≤ w
        · simp only [hw64, ↓reduceIte]
          refine hk Γ (ws ++ [leaf]) (.imm 0#64) 0 (CtxExtends.refl Γ) (fun x hx => ?_) hleg64
          rcases List.mem_append.1 hx with hm | hm
          · exact hws x hm
          · simp only [List.mem_singleton] at hm; subst hm; exact hleaf
        · simp only [hw64, ↓reduceIte]; exact hk Γ ws leaf w (CtxExtends.refl Γ) hws hleaf
      · simp only [hab0, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op2_normal target (.shl i64) leaf (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) hleaf hleg64 hleg64 ?_
        let Γ1 := (i64, VarKind.normal) :: Γ
        have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
        refine isLegal_let_op2_normal target (.or i64) acc (.var Γ.length) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) (hacc.mono hExt1) (ArgNormal.head target Γ hleg64) hleg64 ?_
        let Γ2 := (i64, VarKind.normal) :: Γ1
        have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
        have hlo := ArgNormal.head target Γ1 hleg64
        by_cases hlt : accBits + w < 64
        · simp only [hlt, ↓reduceIte]
          exact hk Γ2 ws (.var Γ1.length) (accBits + w) hExt2 (fun x hx => (hws x hx).mono hExt2) hlo
        · simp only [hlt, ↓reduceIte]
          by_cases heq : (accBits + w == 64) = true
          · simp only [heq, ↓reduceIte]
            refine hk Γ2 (ws ++ [.var Γ1.length]) (.imm 0#64) 0 hExt2 (fun x hx => ?_) hleg64
            rcases List.mem_append.1 hx with hm | hm
            · exact (hws x hm).mono hExt2
            · simp only [List.mem_singleton] at hm; subst hm; exact hlo
          · simp only [heq, Bool.false_eq_true, ↓reduceIte]
            refine isLegal_let_op2_normal target (.lshr i64) leaf (.imm _) _ rfl
              (by simp [LegalTarget.isLegalOp, h64]) (hleaf.mono hExt2) hleg64 hleg64 ?_
            let Γ3 := (i64, VarKind.normal) :: Γ2
            have hExt3 : CtxExtends Γ Γ3 := hExt2.trans (CtxExtends.cons _ _)
            refine hk Γ3 (ws ++ [.var Γ1.length]) (.var Γ2.length) (accBits + w - 64) hExt3
              (fun x hx => ?_) (ArgNormal.head target Γ2 hleg64)
            rcases List.mem_append.1 hx with hm | hm
            · exact (hws x hm).mono hExt3
            · simp only [List.mem_singleton] at hm; subst hm; exact hlo.mono (CtxExtends.cons _ _)

theorem packLeavesToWords64_go_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ (u : Ty) {Γ : List (Ty × VarKind)} (xs : Tup (Arg K) (target.leafTys u))
      (ws : List (Arg K i64)) (acc : Arg K i64) (accBits : Nat),
      target.supportsTy u = true →
      ArgsNormal target Γ xs → (∀ x ∈ ws, ArgNormal target Γ i64 x) → ArgNormal target Γ i64 acc →
      ∀ {k : List (Arg K i64) → Arg K i64 → Nat → Expr K KL rs},
      (∀ Γ' ws' acc' bits', CtxExtends Γ Γ' →
        (∀ x ∈ ws', ArgNormal target Γ' i64 x) → ArgNormal target Γ' i64 acc' →
        (toTFlat (k ws' acc' bits') Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (packLeavesToWords64.go target u xs ws acc accBits k) Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, (b, ()), ws, acc, accBits, _, hxs, hws, hacc, k, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    simp only [packLeavesToWords64.go]
    refine isLegal_let_op1_normal target (.ofBool 64) b _ rfl
      (by simp [LegalTarget.isLegalOp, h64]) hxs.1 hleg64 ?_
    exact pushLeafWord64_isLegal target h64 1 (.var Γ.length) ws acc accBits
      (ArgNormal.head target Γ hleg64) (fun x hx => (hws x hx).mono (CtxExtends.cons _ _))
      (hacc.mono (CtxExtends.cons _ _)) fun Γ' ws' acc' bits' hExt hws' hacc' =>
        hk Γ' ws' acc' bits' ((CtxExtends.cons _ _).trans hExt) hws' hacc'
  | .bits n, Γ, (x, ()), ws, acc, accBits, hsupp, hxs, hws, hacc, k, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    have hw := widenWidth_mem_of_supports hsupp
    have hw64 := widenWidth_le_64_of_supports hv hsupp
    simp only [packLeavesToWords64.go]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hk Γ ws acc accBits (CtxExtends.refl Γ) hws hacc
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      split
      · next heq =>
        exact pushLeafWord64_isLegal target h64 (min n 64) (castArgBits heq x) ws acc accBits
          (ArgNormal.cast heq hxs.1) hws hacc hk
      · next hne =>
        have hlt : target.widenWidth n < 64 := Nat.lt_of_le_of_ne hw64 hne
        simp only [hlt, ↓reduceIte]
        refine isLegal_let_op1_normal target (.zext (target.widenWidth n) 64) x _ rfl
          (by simp [LegalTarget.isLegalOp, hw, h64, hlt]) hxs.1 hleg64 ?_
        exact pushLeafWord64_isLegal target h64 n (.var Γ.length) ws acc accBits
          (ArgNormal.head target Γ hleg64) (fun z hz => (hws z hz).mono (CtxExtends.cons _ _))
          (hacc.mono (CtxExtends.cons _ _)) fun Γ' ws' acc' bits' hExt hws' hacc' =>
            hk Γ' ws' acc' bits' ((CtxExtends.cons _ _).trans hExt) hws' hacc'
  | .float f, Γ, (x, ()), ws, acc, accBits, hsupp, hxs, hws, hacc, k, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    have hsuppf : f ∈ target.floatFmts ∧ f.width ≤ 64 := by simpa [LegalTarget.supportsTy] using hsupp
    have hf := hsuppf.1
    have ⟨hfw, hfw64⟩ := valid_float_spec hv hf
    have hlegFw : target.isLegalTy (.bits f.width) = true := by simpa [LegalTarget.isLegalTy] using hfw
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [packLeavesToWords64.go]
    refine isLegal_let_op1_normal target (.bitcast (.float f) (.bits f.width) rfl) x _ rfl
      (by simp [LegalTarget.isLegalOp, hlegF, hlegFw, bne_iff_ne]) hxs.1 hlegFw ?_
    let Γ1 := (.bits f.width, VarKind.normal) :: Γ
    have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
    have hbi := ArgNormal.head target Γ hlegFw
    split
    · next heq =>
      exact pushLeafWord64_isLegal target h64 64 (castArgBits heq (.var Γ.length)) ws acc accBits
        (ArgNormal.cast heq hbi) (fun z hz => (hws z hz).mono hExt1) (hacc.mono hExt1)
        fun Γ' ws' acc' bits' hExt hws' hacc' => hk Γ' ws' acc' bits' (hExt1.trans hExt) hws' hacc'
    · next hne =>
      have hlt : f.width < 64 := Nat.lt_of_le_of_ne hfw64 hne
      simp only [hlt, ↓reduceIte]
      refine isLegal_let_op1_normal target (.zext f.width 64) (.var Γ.length) _ rfl
        (by simp [LegalTarget.isLegalOp, hfw, h64, hlt]) hbi hleg64 ?_
      let Γ2 := (i64, VarKind.normal) :: Γ1
      have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
      exact pushLeafWord64_isLegal target h64 f.width (.var Γ1.length) ws acc accBits
        (ArgNormal.head target Γ1 hleg64) (fun z hz => (hws z hz).mono hExt2) (hacc.mono hExt2)
        fun Γ' ws' acc' bits' hExt hws' hacc' => hk Γ' ws' acc' bits' (hExt2.trans hExt) hws' hacc'
  | .pair a b, Γ, xs, ws, acc, accBits, hsupp, hxs, hws, hacc, k, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hsupp
    obtain ⟨hfa, hfb⟩ := ArgsNormal_tupSplit hxs
    simp only [packLeavesToWords64.go]
    refine packLeavesToWords64_go_isLegal target hv a _ ws acc accBits hsupp.1 hfa hws hacc
      fun Γ1 ws1 acc1 bits1 hExt1 hws1 hacc1 => ?_
    refine packLeavesToWords64_go_isLegal target hv b _ ws1 acc1 bits1 hsupp.2 (hfb.mono hExt1) hws1 hacc1
      fun Γ2 ws2 acc2 bits2 hExt2 hws2 hacc2 => ?_
    exact hk Γ2 ws2 acc2 bits2 (hExt1.trans hExt2) hws2 hacc2

theorem packLeavesToWords64_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (t : Ty) {Γ : List (Ty × VarKind)}
    (ht : target.supportsTy t = true) (leaves : Tup (Arg K) (target.leafTys t))
    (hl : ArgsNormal target Γ leaves) {k : List (Arg K i64) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' ws => ∀ w ∈ ws, ArgNormal target Γ' i64 w) k) :
    (toTFlat (packLeavesToWords64 target t leaves k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have h64 := valid_mem64 hv
  have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
  simp only [packLeavesToWords64]
  refine packLeavesToWords64_go_isLegal target hv t leaves [] (.imm 0#64) 0 ht hl
    (fun _ hx => by cases hx) hleg64 fun Γ' ws' acc' bits' hExt hws' hacc' => ?_
  by_cases hb0 : (bits' == 0) = true
  · simp only [hb0, ↓reduceIte]; exact hk Γ' ws' hExt hws'
  · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
    refine hk Γ' (ws' ++ [acc']) hExt fun x hx => ?_
    rcases List.mem_append.1 hx with hm | hm
    · exact hws' x hm
    · simp only [List.mem_singleton] at hm; subst hm; exact hacc'

theorem extractBitsFromWords64_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (h64 : 64 ∈ target.bitWidths) {Γ : List (Ty × VarKind)}
    (words : List (Arg K i64)) (hwords : ∀ w ∈ words, ArgNormal target Γ i64 w)
    (off w : Nat) {k : Arg K i64 → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' i64 r) k) :
    (toTFlat (extractBitsFromWords64 words off w k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
  simp only [extractBitsFromWords64]
  by_cases hw0 : (w == 0) = true
  · simp only [hw0, ↓reduceIte]; exact hk Γ (.imm 0#64) (CtxExtends.refl Γ) hleg64
  · simp only [hw0, Bool.false_eq_true, ↓reduceIte]
    have hw0n := ArgNormal_getD_i64 target h64 words hwords (off / 64)
    have tail_ok : ∀ {Γ1 : List (Ty × VarKind)} (lo : Arg K i64),
        CtxExtends Γ Γ1 → ArgNormal target Γ1 i64 lo →
        (toTFlat (if off % 64 + w ≤ 64 then emitMaskToN w 64 lo k
          else .let_ (op2 (.shl i64) (words.getD (off / 64 + 1) (.imm 0#64)) (.imm (BitVec.ofNat 64 (64 - off % 64))))
            fun (hi, ()) => .let_ (op2 (.or i64) lo (.var hi)) fun (comb, ()) => emitMaskToN w 64 (.var comb) k)
          Γ1.length Δ.length).isLegal target Γ1 Δ = true := by
      intro Γ1 lo hExt1 hlo
      by_cases hle : off % 64 + w ≤ 64
      · simp only [hle, ↓reduceIte]
        exact emitMaskToN_isLegal target h64 lo hlo fun Γ2 r hExt2 hr => hk Γ2 r (hExt1.trans hExt2) hr
      · simp only [hle, ↓reduceIte]
        have hw1n := (ArgNormal_getD_i64 target h64 words hwords (off / 64 + 1)).mono hExt1
        refine isLegal_let_op2_normal target (.shl i64) _ (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) hw1n hleg64 hleg64 ?_
        let Γ2 := (i64, VarKind.normal) :: Γ1
        have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
        refine isLegal_let_op2_normal target (.or i64) lo (.var Γ1.length) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) (hlo.mono (CtxExtends.cons _ _))
          (ArgNormal.head target Γ1 hleg64) hleg64 ?_
        let Γ3 := (i64, VarKind.normal) :: Γ2
        have hExt3 : CtxExtends Γ Γ3 := hExt2.trans (CtxExtends.cons _ _)
        exact emitMaskToN_isLegal target h64 (.var Γ2.length) (ArgNormal.head target Γ2 hleg64)
          fun Γ4 r hExt4 hr => hk Γ4 r (hExt3.trans hExt4) hr
    by_cases hs0 : (off % 64 == 0) = true
    · simp only [hs0, ↓reduceIte]; exact tail_ok (words.getD (off / 64) (.imm 0#64)) (CtxExtends.refl Γ) hw0n
    · simp only [hs0, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op2_normal target (.lshr i64) (words.getD (off / 64) (.imm 0#64)) (.imm _) _ rfl
        (by simp [LegalTarget.isLegalOp, h64]) hw0n hleg64 hleg64 ?_
      exact tail_ok (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg64)

theorem unpackWords64ToLeaves_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ {Γ : List (Ty × VarKind)} (words : List (Arg K i64)),
      (∀ w ∈ words, ArgNormal target Γ i64 w) →
      ∀ (off : Nat) (u : Ty), target.supportsTy u = true →
      ∀ {k : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (unpackWords64ToLeaves target words off u k) Γ.length Δ.length).isLegal target Γ Δ = true
  | Γ, words, hwords, off, .bool, _, k, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    simp only [unpackWords64ToLeaves]
    refine extractBitsFromWords64_isLegal target h64 words hwords off 1 fun Γ1 raw hExt1 hraw => ?_
    refine isLegal_let_op2_normal target (.ne i64) raw (.imm 0#64) _ rfl
      (by simp [LegalTarget.isLegalOp, h64]) hraw hleg64 rfl ?_
    exact hk _ (.var Γ1.length, ()) (hExt1.trans (CtxExtends.cons _ _)) ⟨ArgNormal.head target Γ1 rfl, trivial⟩
  | Γ, words, hwords, off, .bits n, hsupp, k, hk => by
    have h64 := valid_mem64 hv
    have hw := widenWidth_mem_of_supports hsupp
    have hw64 := widenWidth_le_64_of_supports hv hsupp
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [unpackWords64ToLeaves]
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hk Γ (.imm 0#_, ()) (CtxExtends.refl Γ) ⟨hlegW, trivial⟩
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      refine extractBitsFromWords64_isLegal target h64 words hwords off (min n 64) fun Γ1 raw hExt1 hraw => ?_
      split
      · next heq => exact hk Γ1 (castArgBits heq.symm raw, ()) hExt1 ⟨ArgNormal.cast heq.symm hraw, trivial⟩
      · next hne =>
        have hlt : target.widenWidth n < 64 := Nat.lt_of_le_of_ne hw64 hne
        simp only [hlt, ↓reduceIte]
        refine isLegal_let_op1_normal target (.trunc 64 (target.widenWidth n)) raw _ rfl
          (by simp [LegalTarget.isLegalOp, h64, hw, hlt]) hraw hlegW ?_
        exact hk _ (.var Γ1.length, ()) (hExt1.trans (CtxExtends.cons _ _))
          ⟨ArgNormal.head target Γ1 hlegW, trivial⟩
  | Γ, words, hwords, off, .float f, hsupp, k, hk => by
    have h64 := valid_mem64 hv
    have hsuppf : f ∈ target.floatFmts ∧ f.width ≤ 64 := by simpa [LegalTarget.supportsTy] using hsupp
    have hf := hsuppf.1
    have ⟨hfw, hfw64⟩ := valid_float_spec hv hf
    have hlegFw : target.isLegalTy (.bits f.width) = true := by simpa [LegalTarget.isLegalTy] using hfw
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    simp only [unpackWords64ToLeaves]
    refine extractBitsFromWords64_isLegal target h64 words hwords off (min f.width 64) fun Γ1 raw hExt1 hraw => ?_
    split
    · next heq =>
      refine isLegal_let_op1_normal target (.bitcast (.bits 64) (.float f) _) raw _ rfl
        (by simp [LegalTarget.isLegalOp, hleg64, hlegF, bne_iff_ne]) hraw hlegF ?_
      exact hk _ (.var Γ1.length, ()) (hExt1.trans (CtxExtends.cons _ _))
        ⟨ArgNormal.head target Γ1 hlegF, trivial⟩
    · next hne =>
      have hlt : f.width < 64 := Nat.lt_of_le_of_ne hfw64 hne
      simp only [hlt, ↓reduceIte]
      refine isLegal_let_op1_normal target (.trunc 64 f.width) raw _ rfl
        (by simp [LegalTarget.isLegalOp, h64, hfw, hlt]) hraw hlegFw ?_
      let Γ2 := (.bits f.width, VarKind.normal) :: Γ1
      refine isLegal_let_op1_normal target (.bitcast (.bits f.width) (.float f) rfl) (.var Γ1.length) _ rfl
        (by simp [LegalTarget.isLegalOp, hlegFw, hlegF, bne_iff_ne]) (ArgNormal.head target Γ1 hlegFw) hlegF ?_
      exact hk _ (.var Γ2.length, ()) (hExt1.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
        ⟨ArgNormal.head target Γ2 hlegF, trivial⟩
  | Γ, words, hwords, off, .pair a b, hsupp, k, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hsupp
    simp only [unpackWords64ToLeaves]
    refine unpackWords64ToLeaves_isLegal target hv words hwords off a hsupp.1 fun Γ1 fa hExt1 hfa => ?_
    refine unpackWords64ToLeaves_isLegal target hv words (fun w hw => (hwords w hw).mono hExt1)
      (off + a.size) b hsupp.2 fun Γ2 fb hExt2 hfb => ?_
    exact hk Γ2 (tupAppend fa fb) (hExt1.trans hExt2) (ArgsNormal_tupAppend (hfa.mono hExt2) hfb)

theorem loadByteChunksToWords64_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ {Γ : List (Ty × VarKind)} (ptr : Arg K i64) (byteOff : Nat) (cs : List Nat)
      (ws : List (Arg K i64)) (acc : Arg K i64) (accBits : Nat),
      ArgNormal target Γ i64 ptr →
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths) →
      (∀ x ∈ ws, ArgNormal target Γ i64 x) → ArgNormal target Γ i64 acc →
      ∀ {k : List (Arg K i64) → Expr K KL rs},
      IsLegalCont target Γ Δ (fun Γ' ws' => ∀ x ∈ ws', ArgNormal target Γ' i64 x) k →
      (toTFlat (loadByteChunksToWords64 ptr byteOff cs ws acc accBits k) Γ.length Δ.length).isLegal target Γ Δ = true
  | Γ, ptr, byteOff, [], ws, acc, accBits, _, _, hws, hacc, k, hk => by
    simp only [loadByteChunksToWords64]
    by_cases hb0 : (accBits == 0) = true
    · simp only [hb0, ↓reduceIte]; exact hk Γ ws (CtxExtends.refl Γ) hws
    · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
      refine hk Γ (ws ++ [acc]) (CtxExtends.refl Γ) fun x hx => ?_
      rcases List.mem_append.1 hx with hm | hm
      · exact hws x hm
      · simp only [List.mem_singleton] at hm; subst hm; exact hacc
  | Γ, ptr, byteOff, c :: cs, ws, acc, accBits, hptr, hcs, hws, hacc, k, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    have hcw : 8 * c ∈ target.bitWidths := (hcs c (by simp)).2
    have hcw64 : 8 * c ≤ 64 := (valid_bitWidth_spec hv hcw).2.2
    have hlegCw : target.isLegalTy (.bits (8 * c)) = true := by simpa [LegalTarget.isLegalTy] using hcw
    simp only [loadByteChunksToWords64]
    have afterAddr : ∀ {Γ1 : List (Ty × VarKind)} (ap : Arg K i64),
        CtxExtends Γ Γ1 → ArgNormal target Γ1 i64 ap →
        (toTFlat (.load (.bits (8 * c)) ap fun raw =>
          if h : 8 * c = 64 then
            pushLeafWord64 (min (8 * c) 64) (castArgBits h (.var raw)) ws acc accBits
              fun ws' acc' bits' => loadByteChunksToWords64 ptr (byteOff + c) cs ws' acc' bits' k
          else if 8 * c < 64 then
            .let_ (op1 (.zext (8 * c) 64) (.var raw)) fun (z, ()) =>
              pushLeafWord64 (min (8 * c) 64) (.var z) ws acc accBits
                fun ws' acc' bits' => loadByteChunksToWords64 ptr (byteOff + c) cs ws' acc' bits' k
          else
            .let_ (op1 (.trunc (8 * c) 64) (.var raw)) fun (z, ()) =>
              pushLeafWord64 (min (8 * c) 64) (.var z) ws acc accBits
                fun ws' acc' bits' => loadByteChunksToWords64 ptr (byteOff + c) cs ws' acc' bits' k)
          Γ1.length Δ.length).isLegal target Γ1 Δ = true := by
      intro Γ1 ap hExt1 hap
      refine isLegal_load_normal target (.bits (8 * c)) ap _ hlegCw hap ?_
      let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ1
      have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
      have hraw := ArgNormal.head target Γ1 hlegCw
      have afterWd : ∀ {Γ3 : List (Ty × VarKind)} (wd : Arg K i64),
          CtxExtends Γ2 Γ3 → ArgNormal target Γ3 i64 wd →
          (toTFlat (pushLeafWord64 (min (8 * c) 64) wd ws acc accBits fun ws' acc' bits' =>
            loadByteChunksToWords64 ptr (byteOff + c) cs ws' acc' bits' k)
              Γ3.length Δ.length).isLegal target Γ3 Δ = true := by
        intro Γ3 wd hExt3 hwd
        have hExt13 : CtxExtends Γ Γ3 := hExt2.trans hExt3
        refine pushLeafWord64_isLegal target h64 (min (8 * c) 64) wd ws acc accBits hwd
          (fun x hx => (hws x hx).mono hExt13) (hacc.mono hExt13)
          fun Γ4 ws' acc' bits' hExt4 hws' hacc' => ?_
        have hExt14 : CtxExtends Γ Γ4 := hExt13.trans hExt4
        exact loadByteChunksToWords64_isLegal target hv ptr (byteOff + c) cs ws' acc' bits'
          (hptr.mono hExt14) (fun x hx => hcs x (by simp [hx])) hws' hacc'
          fun Γ5 res hExt5 hres => hk Γ5 res (hExt14.trans hExt5) hres
      dsimp only
      split
      · next heq => exact afterWd (castArgBits heq (.var Γ1.length)) (CtxExtends.refl Γ2) (ArgNormal.cast heq hraw)
      · next hne =>
        have hlt : 8 * c < 64 := Nat.lt_of_le_of_ne hcw64 hne
        simp only [hlt, ↓reduceIte]
        refine isLegal_let_op1_normal target (.zext (8 * c) 64) (.var Γ1.length) _ rfl
          (by simp [LegalTarget.isLegalOp, hcw, h64, hlt]) hraw hleg64 ?_
        exact afterWd (.var Γ2.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ2 hleg64)
    by_cases hbo : (byteOff == 0) = true
    · simp only [hbo, ↓reduceIte]; exact afterAddr ptr (CtxExtends.refl Γ) hptr
    · simp only [hbo, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
        (by simp [LegalTarget.isLegalOp, h64]) hptr hleg64 hleg64 ?_
      exact afterAddr (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hleg64)

theorem storeByteChunksFromWords64_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ {Γ : List (Ty × VarKind)} (words : List (Arg K i64)) (ptr : Arg K i64) (byteOff : Nat)
      (cs : List Nat) {k : Expr K KL rs},
      (∀ w ∈ words, ArgNormal target Γ i64 w) → ArgNormal target Γ i64 ptr →
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths) →
      (∀ Γ', CtxExtends Γ Γ' → (toTFlat k Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (storeByteChunksFromWords64 words ptr byteOff cs k) Γ.length Δ.length).isLegal target Γ Δ = true
  | Γ, _, _, _, [], _, _, _, _, hk => hk Γ (CtxExtends.refl Γ)
  | Γ, words, ptr, byteOff, c :: cs, k, hwords, hptr, hcs, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    have hcw : 8 * c ∈ target.bitWidths := (hcs c (by simp)).2
    have hcw64 : 8 * c ≤ 64 := (valid_bitWidth_spec hv hcw).2.2
    have hlegCw : target.isLegalTy (.bits (8 * c)) = true := by simpa [LegalTarget.isLegalTy] using hcw
    simp only [storeByteChunksFromWords64]
    refine extractBitsFromWords64_isLegal target h64 words hwords (8 * byteOff) (min (8 * c) 64)
      fun Γ1 raw hExt1 hraw => ?_
    have afterVal : ∀ {Γ2 : List (Ty × VarKind)} (val : Arg K (.bits (8 * c))),
        CtxExtends Γ1 Γ2 → ArgNormal target Γ2 (.bits (8 * c)) val →
        (toTFlat (if byteOff == 0 then .store (t := .bits (8 * c)) val ptr (storeByteChunksFromWords64 words ptr (byteOff + c) cs k)
          else .let_ (op2 (.add i64) ptr (.imm (BitVec.ofNat 64 byteOff))) fun (ap, ()) =>
            .store (t := .bits (8 * c)) val (.var ap) (storeByteChunksFromWords64 words ptr (byteOff + c) cs k))
          Γ2.length Δ.length).isLegal target Γ2 Δ = true := by
      intro Γ2 val hExt2 hval
      have hExt12 : CtxExtends Γ Γ2 := hExt1.trans hExt2
      have storeAt : ∀ {Γ3 : List (Ty × VarKind)} (ap : Arg K i64),
          CtxExtends Γ2 Γ3 → ArgNormal target Γ3 i64 ap →
          (toTFlat (.store (t := .bits (8 * c)) val ap (storeByteChunksFromWords64 words ptr (byteOff + c) cs k))
            Γ3.length Δ.length).isLegal target Γ3 Δ = true := by
        intro Γ3 ap hExt3 hap
        have hExt13 : CtxExtends Γ Γ3 := hExt12.trans hExt3
        refine isLegal_store_normal target (.bits (8 * c)) val ap _ hlegCw (hval.mono hExt3) hap ?_
        exact storeByteChunksFromWords64_isLegal target hv words ptr (byteOff + c) cs
          (fun w hw => (hwords w hw).mono hExt13) (hptr.mono hExt13) (fun x hx => hcs x (by simp [hx]))
          (fun Γ4 hExt34 => hk Γ4 (hExt13.trans hExt34))
      by_cases hbo : (byteOff == 0) = true
      · simp only [hbo, ↓reduceIte]; exact storeAt ptr (CtxExtends.refl Γ2) (hptr.mono hExt12)
      · simp only [hbo, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) (hptr.mono hExt12) hleg64 hleg64 ?_
        exact storeAt (.var Γ2.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ2 hleg64)
    split
    · next heq => exact afterVal (castArgBits heq.symm raw) (CtxExtends.refl Γ1) (ArgNormal.cast heq.symm hraw)
    · next hne =>
      have hlt : 8 * c < 64 := Nat.lt_of_le_of_ne hcw64 hne
      simp only [hlt, ↓reduceIte]
      refine isLegal_let_op1_normal target (.trunc 64 (8 * c)) raw _ rfl
        (by simp [LegalTarget.isLegalOp, h64, hcw, hlt]) hraw hlegCw ?_
      exact afterVal (.var Γ1.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ1 hlegCw)

theorem emitLoadBits_go_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) {n w : Nat} (hw : w ∈ target.bitWidths) :
    ∀ {Γ : List (Ty × VarKind)} (ptr : Arg K i64) (byteOff : Nat) (cs : List Nat)
      (acc : Option (Arg K (.bits w))) {k : Arg K (.bits w) → Expr K KL rs},
      ArgNormal target Γ i64 ptr →
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths) →
      (∀ v, acc = some v → ArgNormal target Γ (.bits w) v) →
      IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k →
      (toTFlat (emitLoadBits.go n w ptr k byteOff cs acc) Γ.length Δ.length).isLegal target Γ Δ = true
  | Γ, ptr, byteOff, [], acc, k, _, _, hacc, hk => by
    have hlegW : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [emitLoadBits.go]
    cases acc with
    | none => exact hk Γ (.imm 0#w) (CtxExtends.refl Γ) hlegW
    | some v => exact emitMaskToN_isLegal target hw v (hacc v rfl) hk
  | Γ, ptr, byteOff, c :: rest, acc, k, hptr, hcs, hacc, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    have hlegW : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
    have hcw : 8 * c ∈ target.bitWidths := (hcs c (by simp)).2
    have hlegCw : target.isLegalTy (.bits (8 * c)) = true := by simpa [LegalTarget.isLegalTy] using hcw
    simp only [emitLoadBits.go]
    have afterSv : ∀ {Γ4 : List (Ty × VarKind)} (sv : Arg K (.bits w)),
        CtxExtends Γ Γ4 → ArgNormal target Γ4 (.bits w) sv →
        (acc = none → (toTFlat (emitLoadBits.go n w ptr k (byteOff + c) rest (some sv)) Γ4.length Δ.length).isLegal target Γ4 Δ = true) ∧
        (∀ prev, acc = some prev → (toTFlat (.let_ (op2 (.or (.bits w)) prev sv) fun (u, ()) =>
          emitLoadBits.go n w ptr k (byteOff + c) rest (some (.var u))) Γ4.length Δ.length).isLegal target Γ4 Δ = true) := by
      intro Γ4 sv hExt14 hsv
      refine ⟨fun hnone => ?_, fun prev hsome => ?_⟩
      · exact emitLoadBits_go_isLegal target hv hw ptr (byteOff + c) rest (some sv)
          (hptr.mono hExt14) (fun x hx => hcs x (by simp [hx]))
          (fun v hv' => by injection hv' with hv'; subst hv'; exact hsv)
          (fun Γ5 r hExt5 hr => hk Γ5 r (hExt14.trans hExt5) hr)
      · refine isLegal_let_op2_normal target (.or (.bits w)) prev sv _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) ((hacc prev hsome).mono hExt14) hsv hlegW ?_
        let Γ5 := (.bits w, VarKind.normal) :: Γ4
        have hExt15 : CtxExtends Γ Γ5 := hExt14.trans (CtxExtends.cons _ _)
        exact emitLoadBits_go_isLegal target hv hw ptr (byteOff + c) rest (some (.var Γ4.length))
          (hptr.mono hExt15) (fun x hx => hcs x (by simp [hx]))
          (fun v hv' => by injection hv' with hv'; subst hv'; exact ArgNormal.head target Γ4 hlegW)
          (fun Γ6 r hExt6 hr => hk Γ6 r (hExt15.trans hExt6) hr)
    cases acc with
    | none =>
      have finishSv : ∀ {Γ4 : List (Ty × VarKind)} (sv : Arg K (.bits w)),
          CtxExtends Γ Γ4 → ArgNormal target Γ4 (.bits w) sv →
          (toTFlat (emitLoadBits.go n w ptr k (byteOff + c) rest (some sv)) Γ4.length Δ.length).isLegal target Γ4 Δ = true :=
        fun sv hExt hsv => (afterSv sv hExt hsv).1 rfl
      by_cases hbo : (byteOff == 0) = true
      · simp only [hbo, ↓reduceIte]
        refine isLegal_load_normal target (.bits (8 * c)) ptr _ hlegCw hptr ?_
        let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ
        have hraw := ArgNormal.head target Γ hlegCw
        split
        · next heq => exact finishSv (castArgBits heq (.var Γ.length)) (CtxExtends.cons _ _) (ArgNormal.cast heq hraw)
        · next hne =>
          by_cases hlt : 8 * c < w
          · simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.zext (8 * c) w) (.var Γ.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hlt]) hraw hlegW ?_
            exact finishSv (.var Γ2.length) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ2 hlegW)
          · have hgt : w < 8 * c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
            simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.trunc (8 * c) w) (.var Γ.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hgt]) hraw hlegW ?_
            exact finishSv (.var Γ2.length) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ2 hlegW)
      · simp only [hbo, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) hptr hleg64 hleg64 ?_
        let Γ1 := (i64, VarKind.normal) :: Γ
        refine isLegal_load_normal target (.bits (8 * c)) (.var Γ.length) _ hlegCw (ArgNormal.head target Γ hleg64) ?_
        let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ1
        have hExt12 : CtxExtends Γ Γ2 := (CtxExtends.cons _ _).trans (CtxExtends.cons _ _)
        have hraw := ArgNormal.head target Γ1 hlegCw
        split
        · next heq =>
          refine isLegal_let_op2_normal target (.shl (.bits w)) (castArgBits heq (.var Γ1.length)) (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.cast heq hraw) hlegW hlegW ?_
          exact finishSv (.var Γ2.length) (hExt12.trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ2 hlegW)
        · next hne =>
          by_cases hlt : 8 * c < w
          · simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.zext (8 * c) w) (.var Γ1.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hlt]) hraw hlegW ?_
            let Γ3 := (.bits w, VarKind.normal) :: Γ2
            refine isLegal_let_op2_normal target (.shl (.bits w)) (.var Γ2.length) (.imm _) _ rfl
              (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ2 hlegW) hlegW hlegW ?_
            exact finishSv (.var Γ3.length) (hExt12.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
              (ArgNormal.head target Γ3 hlegW)
          · have hgt : w < 8 * c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
            simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.trunc (8 * c) w) (.var Γ1.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hgt]) hraw hlegW ?_
            let Γ3 := (.bits w, VarKind.normal) :: Γ2
            refine isLegal_let_op2_normal target (.shl (.bits w)) (.var Γ2.length) (.imm _) _ rfl
              (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ2 hlegW) hlegW hlegW ?_
            exact finishSv (.var Γ3.length) (hExt12.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
              (ArgNormal.head target Γ3 hlegW)
    | some prev =>
      have finishSv : ∀ {Γ4 : List (Ty × VarKind)} (sv : Arg K (.bits w)),
          CtxExtends Γ Γ4 → ArgNormal target Γ4 (.bits w) sv →
          (toTFlat (.let_ (op2 (.or (.bits w)) prev sv) fun (u, ()) =>
            emitLoadBits.go n w ptr k (byteOff + c) rest (some (.var u))) Γ4.length Δ.length).isLegal target Γ4 Δ = true :=
        fun sv hExt hsv => (afterSv sv hExt hsv).2 prev rfl
      by_cases hbo : (byteOff == 0) = true
      · simp only [hbo, ↓reduceIte]
        refine isLegal_load_normal target (.bits (8 * c)) ptr _ hlegCw hptr ?_
        let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ
        have hraw := ArgNormal.head target Γ hlegCw
        split
        · next heq => exact finishSv (castArgBits heq (.var Γ.length)) (CtxExtends.cons _ _) (ArgNormal.cast heq hraw)
        · next hne =>
          by_cases hlt : 8 * c < w
          · simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.zext (8 * c) w) (.var Γ.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hlt]) hraw hlegW ?_
            exact finishSv (.var Γ2.length) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ2 hlegW)
          · have hgt : w < 8 * c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
            simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.trunc (8 * c) w) (.var Γ.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hgt]) hraw hlegW ?_
            exact finishSv (.var Γ2.length) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ2 hlegW)
      · simp only [hbo, Bool.false_eq_true, ↓reduceIte]
        refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) hptr hleg64 hleg64 ?_
        let Γ1 := (i64, VarKind.normal) :: Γ
        refine isLegal_load_normal target (.bits (8 * c)) (.var Γ.length) _ hlegCw (ArgNormal.head target Γ hleg64) ?_
        let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ1
        have hExt12 : CtxExtends Γ Γ2 := (CtxExtends.cons _ _).trans (CtxExtends.cons _ _)
        have hraw := ArgNormal.head target Γ1 hlegCw
        split
        · next heq =>
          refine isLegal_let_op2_normal target (.shl (.bits w)) (castArgBits heq (.var Γ1.length)) (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.cast heq hraw) hlegW hlegW ?_
          exact finishSv (.var Γ2.length) (hExt12.trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ2 hlegW)
        · next hne =>
          by_cases hlt : 8 * c < w
          · simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.zext (8 * c) w) (.var Γ1.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hlt]) hraw hlegW ?_
            let Γ3 := (.bits w, VarKind.normal) :: Γ2
            refine isLegal_let_op2_normal target (.shl (.bits w)) (.var Γ2.length) (.imm _) _ rfl
              (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ2 hlegW) hlegW hlegW ?_
            exact finishSv (.var Γ3.length) (hExt12.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
              (ArgNormal.head target Γ3 hlegW)
          · have hgt : w < 8 * c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
            simp only [hlt, ↓reduceIte]
            refine isLegal_let_op1_normal target (.trunc (8 * c) w) (.var Γ1.length) _ rfl
              (by simp [LegalTarget.isLegalOp, hcw, hw, hgt]) hraw hlegW ?_
            let Γ3 := (.bits w, VarKind.normal) :: Γ2
            refine isLegal_let_op2_normal target (.shl (.bits w)) (.var Γ2.length) (.imm _) _ rfl
              (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ2 hlegW) hlegW hlegW ?_
            exact finishSv (.var Γ3.length) (hExt12.trans ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _)))
              (ArgNormal.head target Γ3 hlegW)

theorem emitLoadBits_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) {n w : Nat} (hw : w ∈ target.bitWidths)
    {Γ : List (Ty × VarKind)} (ptr : Arg K i64) (hptr : ArgNormal target Γ i64 ptr)
    {k : Arg K (.bits w) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k) :
    (toTFlat (emitLoadBits target.bitWidths n w ptr k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have hlegW : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
  simp only [emitLoadBits]
  by_cases hb0 : ((n + 7) / 8 == 0) = true
  · simp only [hb0, ↓reduceIte]; exact hk Γ (.imm 0#w) (CtxExtends.refl Γ) hlegW
  · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
    refine emitLoadBits_go_isLegal target hv hw ptr 0 _ none hptr ?_ (fun _ h => by cases h) hk
    exact (chunkBytes_pos_mem_sum target.bitWidths (valid_mem8 hv) ((n + 7) / 8)).1

theorem emitStoreBits_go_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) {w : Nat} (hw : w ∈ target.bitWidths) :
    ∀ {Γ : List (Ty × VarKind)} (v : Arg K (.bits w)) (ptr : Arg K i64) (byteOff : Nat)
      (cs : List Nat) {k : Expr K KL rs},
      ArgNormal target Γ (.bits w) v → ArgNormal target Γ i64 ptr →
      (∀ c ∈ cs, 0 < c ∧ 8 * c ∈ target.bitWidths) →
      (∀ Γ', CtxExtends Γ Γ' → (toTFlat k Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (emitStoreBits.go w v ptr k byteOff cs) Γ.length Δ.length).isLegal target Γ Δ = true
  | Γ, _, _, _, [], _, _, _, _, hk => hk Γ (CtxExtends.refl Γ)
  | Γ, v, ptr, byteOff, c :: rest, k, hvarg, hptr, hcs, hk => by
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    have hlegW : target.isLegalTy (.bits w) = true := by simpa [LegalTarget.isLegalTy] using hw
    have hcw : 8 * c ∈ target.bitWidths := (hcs c (by simp)).2
    have hlegCw : target.isLegalTy (.bits (8 * c)) = true := by simpa [LegalTarget.isLegalTy] using hcw
    simp only [emitStoreBits.go]
    have storeAt : ∀ {Γ3 : List (Ty × VarKind)} (val : Arg K (.bits (8 * c))) (ap : Arg K i64),
        CtxExtends Γ Γ3 → ArgNormal target Γ3 (.bits (8 * c)) val → ArgNormal target Γ3 i64 ap →
        (toTFlat (.store (t := .bits (8 * c)) val ap (emitStoreBits.go w v ptr k (byteOff + c) rest))
          Γ3.length Δ.length).isLegal target Γ3 Δ = true := by
      intro Γ3 val ap hExt13 hval hap
      refine isLegal_store_normal target (.bits (8 * c)) val ap _ hlegCw hval hap ?_
      exact emitStoreBits_go_isLegal target hv hw v ptr (byteOff + c) rest
        (hvarg.mono hExt13) (hptr.mono hExt13) (fun x hx => hcs x (by simp [hx]))
        (fun Γ4 hExt34 => hk Γ4 (hExt13.trans hExt34))
    by_cases hbo : (byteOff == 0) = true
    · simp only [hbo, ↓reduceIte]
      split
      · next heq => exact storeAt (castArgBits heq.symm v) ptr (CtxExtends.refl Γ) (ArgNormal.cast heq.symm hvarg) hptr
      · next hne =>
        by_cases hlt : 8 * c < w
        · simp only [hlt, ↓reduceIte]
          refine isLegal_let_op1_normal target (.trunc w (8 * c)) v _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hcw, hlt]) hvarg hlegCw ?_
          exact storeAt (.var Γ.length) ptr (CtxExtends.cons _ _) (ArgNormal.head target Γ hlegCw)
            (hptr.mono (CtxExtends.cons _ _))
        · have hgt : w < 8 * c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
          simp only [hlt, ↓reduceIte]
          refine isLegal_let_op1_normal target (.zext w (8 * c)) v _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hcw, hgt]) hvarg hlegCw ?_
          exact storeAt (.var Γ.length) ptr (CtxExtends.cons _ _) (ArgNormal.head target Γ hlegCw)
            (hptr.mono (CtxExtends.cons _ _))
    · simp only [hbo, Bool.false_eq_true, ↓reduceIte]
      refine isLegal_let_op2_normal target (.lshr (.bits w)) v (.imm _) _ rfl
        (by simp [LegalTarget.isLegalOp, hw]) hvarg hlegW hlegW ?_
      let Γ1 := (.bits w, VarKind.normal) :: Γ
      have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
      have hsv := ArgNormal.head target Γ hlegW
      split
      · next heq =>
        refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
          (by simp [LegalTarget.isLegalOp, h64]) (hptr.mono hExt1) hleg64 hleg64 ?_
        let Γ2 := (i64, VarKind.normal) :: Γ1
        exact storeAt (castArgBits heq.symm (.var Γ.length)) (.var Γ1.length) (hExt1.trans (CtxExtends.cons _ _))
          ((ArgNormal.cast heq.symm hsv).mono (CtxExtends.cons _ _)) (ArgNormal.head target Γ1 hleg64)
      · next hne =>
        by_cases hlt : 8 * c < w
        · simp only [hlt, ↓reduceIte]
          refine isLegal_let_op1_normal target (.trunc w (8 * c)) (.var Γ.length) _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hcw, hlt]) hsv hlegCw ?_
          let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ1
          have hExt12 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
          refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, h64]) (hptr.mono hExt12) hleg64 hleg64 ?_
          let Γ3 := (i64, VarKind.normal) :: Γ2
          exact storeAt (.var Γ1.length) (.var Γ2.length) (hExt12.trans (CtxExtends.cons _ _))
            ((ArgNormal.head target Γ1 hlegCw).mono (CtxExtends.cons _ _)) (ArgNormal.head target Γ2 hleg64)
        · have hgt : w < 8 * c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne)
          simp only [hlt, ↓reduceIte]
          refine isLegal_let_op1_normal target (.zext w (8 * c)) (.var Γ.length) _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hcw, hgt]) hsv hlegCw ?_
          let Γ2 := (.bits (8 * c), VarKind.normal) :: Γ1
          have hExt12 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
          refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, h64]) (hptr.mono hExt12) hleg64 hleg64 ?_
          let Γ3 := (i64, VarKind.normal) :: Γ2
          exact storeAt (.var Γ1.length) (.var Γ2.length) (hExt12.trans (CtxExtends.cons _ _))
            ((ArgNormal.head target Γ1 hlegCw).mono (CtxExtends.cons _ _)) (ArgNormal.head target Γ2 hleg64)

theorem emitStoreBits_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) {n w : Nat} (hw : w ∈ target.bitWidths)
    {Γ : List (Ty × VarKind)} (v : Arg K (.bits w)) (ptr : Arg K i64) {k : Expr K KL rs}
    (hvarg : ArgNormal target Γ (.bits w) v) (hptr : ArgNormal target Γ i64 ptr)
    (hk : ∀ Γ', CtxExtends Γ Γ' → (toTFlat k Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    (toTFlat (emitStoreBits target.bitWidths n w v ptr k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  simp only [emitStoreBits]
  by_cases hb0 : ((n + 7) / 8 == 0) = true
  · simp only [hb0, ↓reduceIte]; exact hk Γ (CtxExtends.refl Γ)
  · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
    refine emitStoreBits_go_isLegal target hv hw v ptr 0 _ hvarg hptr ?_ hk
    exact (chunkBytes_pos_mem_sum target.bitWidths (valid_mem8 hv) ((n + 7) / 8)).1

theorem legalLoad_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)} (ptr : Arg K i64),
      target.supportsTy t = true → ArgNormal target Γ i64 ptr →
      ∀ {k : LVar target K t → Expr K KL rs},
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalLoad target t ptr k) Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, ptr, _, hptr, k, hk => by
    simp only [legalLoad]
    refine isLegal_load_normal target .bool ptr _ rfl hptr ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ rfl, trivial⟩
  | .bits n, Γ, ptr, hsupp, hptr, k, hk => by
    have hw := widenWidth_mem_of_supports hsupp
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalLoad]
    by_cases hnw : (n == target.widenWidth n) = true
    · simp only [hnw, ↓reduceIte]
      refine isLegal_load_normal target (.bits (target.widenWidth n)) ptr _ hlegW hptr ?_
      exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
    · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
      exact emitLoadBits_isLegal target hv hw ptr hptr fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .float f, Γ, ptr, hsupp, hptr, k, hk => by
    have hsuppf : f ∈ target.floatFmts ∧ f.width ≤ 64 := by simpa [LegalTarget.supportsTy] using hsupp
    have hf := hsuppf.1
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [legalLoad]
    refine isLegal_load_normal target (.float f) ptr _ hlegF hptr ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegF, trivial⟩
  | .pair a b, Γ, ptr, hsupp, hptr, k, hk => by
    have hsupp' := hsupp
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hsupp'
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    simp only [legalLoad]
    split
    · next hp =>
      have hlegP : target.isLegalTy (.pair a b) = true := hp
      refine isLegal_load_normal target (.pair a b) ptr _ hlegP hptr ?_
      exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
        (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hlegP, trivial⟩)
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      split
      · refine legalLoad_isLegal target hv a ptr hsupp'.1 hptr fun Γ1 la hExt1 hla => ?_
        have afterPtr2 : ∀ {Γ2 : List (Ty × VarKind)} (p2 : Arg K i64),
            CtxExtends Γ1 Γ2 → ArgNormal target Γ2 i64 p2 →
            (toTFlat (legalLoad target b p2 fun lb => k (tupToSplit hf (tupAppend la lb)))
              Γ2.length Δ.length).isLegal target Γ2 Δ = true := by
          intro Γ2 p2 hExt2 hp2
          have hExt12 := hExt1.trans hExt2
          exact legalLoad_isLegal target hv b p2 hsupp'.2 hp2 fun Γ3 lb hExt3 hlb =>
            hk Γ3 (tupToSplit hf (tupAppend la lb)) (hExt12.trans hExt3)
              (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hla.mono hExt2 |>.mono hExt3) hlb))
        by_cases hab : (a.bytes == 0) = true
        · simp only [hab, ↓reduceIte]; exact afterPtr2 ptr (CtxExtends.refl Γ1) (hptr.mono hExt1)
        · simp only [hab, Bool.false_eq_true, ↓reduceIte]
          refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, h64]) (hptr.mono hExt1) hleg64 hleg64 ?_
          exact afterPtr2 (.var Γ1.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ1 hleg64)
      · by_cases hb0 : ((a.pair b).bytes == 0) = true
        · simp only [hb0, ↓reduceIte]
          refine unpackWords64ToLeaves_isLegal target hv [] (fun _ h => by cases h) 0 (.pair a b) hsupp
            fun Γ1 fres hExt1 hfres => ?_
          exact packLeavesToLegal_isLegal target (.pair a b) fres hfres
            fun Γ2 res hExt2 hres => hk Γ2 res (hExt1.trans hExt2) hres
        · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
          refine loadByteChunksToWords64_isLegal target hv ptr 0 _ [] (.imm 0#64) 0 hptr ?_
            (fun _ h => by cases h) hleg64 fun Γ1 words hExt1 hwords => ?_
          · exact (chunkBytes_pos_mem_sum target.bitWidths (valid_mem8 hv) (a.pair b).bytes).1
          · refine unpackWords64ToLeaves_isLegal target hv words hwords 0 (.pair a b) hsupp
              fun Γ2 fres hExt2 hfres => ?_
            exact packLeavesToLegal_isLegal target (.pair a b) fres hfres
              fun Γ3 res hExt3 hres => hk Γ3 res ((hExt1.trans hExt2).trans hExt3) hres

theorem legalStore_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)} (v : LVar target K t) (ptr : Arg K i64) {k : Expr K KL rs},
      target.supportsTy t = true → ArgsNormal target Γ v → ArgNormal target Γ i64 ptr →
      (∀ Γ', CtxExtends Γ Γ' → (toTFlat k Γ'.length Δ.length).isLegal target Γ' Δ = true) →
      (toTFlat (legalStore target t v ptr k) Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, (v, ()), ptr, k, _, hvarg, hptr, hk => by
    simp only [legalStore]
    exact isLegal_store_normal target .bool v ptr k rfl hvarg.1 hptr (hk Γ (CtxExtends.refl Γ))
  | .bits n, Γ, (v, ()), ptr, k, hsupp, hvarg, hptr, hk => by
    have hw := widenWidth_mem_of_supports hsupp
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by simpa [LegalTarget.isLegalTy] using hw
    simp only [legalStore]
    by_cases hnw : (n == target.widenWidth n) = true
    · simp only [hnw, ↓reduceIte]
      exact isLegal_store_normal target (.bits (target.widenWidth n)) v ptr k hlegW hvarg.1 hptr (hk Γ (CtxExtends.refl Γ))
    · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
      exact emitStoreBits_isLegal target hv hw v ptr hvarg.1 hptr hk
  | .float f, Γ, (v, ()), ptr, k, hsupp, hvarg, hptr, hk => by
    have hsuppf : f ∈ target.floatFmts ∧ f.width ≤ 64 := by simpa [LegalTarget.supportsTy] using hsupp
    have hf := hsuppf.1
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [legalStore]
    exact isLegal_store_normal target (.float f) v ptr k hlegF hvarg.1 hptr (hk Γ (CtxExtends.refl Γ))
  | .pair a b, Γ, xs, ptr, k, hsupp, hxs, hptr, hk => by
    have hsupp' := hsupp
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hsupp'
    have h64 := valid_mem64 hv
    have hleg64 : target.isLegalTy i64 = true := by simpa [LegalTarget.isLegalTy] using h64
    simp only [legalStore]
    split
    · next hp =>
      have hlegP : target.isLegalTy (.pair a b) = true := hp
      exact isLegal_store_normal target (.pair a b) (packedToTup hp xs).1 ptr k hlegP
        (ArgsNormal_packedToTup hp hxs).1 hptr (hk Γ (CtxExtends.refl Γ))
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      split
      · obtain ⟨hla, hlb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
        refine legalStore_isLegal target hv a (tupSplit (splitToTup hf xs)).1 ptr hsupp'.1 hla hptr fun Γ1 hExt1 => ?_
        by_cases hab : (a.bytes == 0) = true
        · simp only [hab, ↓reduceIte]
          exact legalStore_isLegal target hv b (tupSplit (splitToTup hf xs)).2 ptr hsupp'.2 (hlb.mono hExt1) (hptr.mono hExt1)
            fun Γ2 hExt2 => hk Γ2 (hExt1.trans hExt2)
        · simp only [hab, Bool.false_eq_true, ↓reduceIte]
          refine isLegal_let_op2_normal target (.add i64) ptr (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, h64]) (hptr.mono hExt1) hleg64 hleg64 ?_
          let Γ2 := (i64, VarKind.normal) :: Γ1
          have hExt12 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
          exact legalStore_isLegal target hv b (tupSplit (splitToTup hf xs)).2 (.var Γ1.length) hsupp'.2 (hlb.mono hExt12)
            (ArgNormal.head target Γ1 hleg64) fun Γ3 hExt3 => hk Γ3 (hExt12.trans hExt3)
      · by_cases hb0 : ((a.pair b).bytes == 0) = true
        · simp only [hb0, ↓reduceIte]; exact hk Γ (CtxExtends.refl Γ)
        · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
          refine splitLegalToLeaves_isLegal target (.pair a b) xs hxs fun Γ1 fx hExt1 hfx => ?_
          refine packLeavesToWords64_isLegal target hv (.pair a b) hsupp fx hfx
            fun Γ2 words hExt2 hwords => ?_
          have hExt12 := hExt1.trans hExt2
          refine storeByteChunksFromWords64_isLegal target hv words ptr 0 _ hwords (hptr.mono hExt12) ?_
            fun Γ3 hExt3 => hk Γ3 (hExt12.trans hExt3)
          exact (chunkBytes_pos_mem_sum target.bitWidths (valid_mem8 hv) (a.pair b).bytes).1

theorem legalFloatBit2_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true)
    (mkOp : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    (mkFOp : (f : Fmt) → OpCode [.float f, .float f] [.float f])
    (hmkOp : ∀ w unif, w ∈ target.bitWidths → target.isLegalOp (mkOp w) unif = true)
    (hmkFOp : ∀ f unif, target.scalarFloatBitwise = true → f ∈ target.floatFmts →
      target.isLegalOp (mkFOp f) unif = true)
    (hmkNe : ∀ w, (mkOp w).isPackBridge = false)
    (hmkFNe : ∀ f, (mkFOp f).isPackBridge = false)
    {Γ : List (Ty × VarKind)} (f : Fmt) (hf : f ∈ target.floatFmts)
    (x y : Arg K (.float f)) (hx : ArgNormal target Γ (.float f) x) (hy : ArgNormal target Γ (.float f) y)
    {k : Arg K (.float f) → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.float f) r) k) :
    (toTFlat (legalFloatBit2 target mkOp mkFOp f x y k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  have ⟨hfw, _⟩ := valid_float_spec hv hf
  have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
  have hlegFw : target.isLegalTy (.bits f.width) = true := by simpa [LegalTarget.isLegalTy] using hfw
  simp only [legalFloatBit2]
  by_cases hsb : target.scalarFloatBitwise = true
  · simp only [hsb, ↓reduceIte]
    refine isLegal_let_op2_normal target (mkFOp f) x y _ (hmkFNe f) (hmkFOp f _ hsb hf) hx hy hlegF ?_
    exact hk _ (.var Γ.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ hlegF)
  · simp only [hsb, Bool.false_eq_true, ↓reduceIte]
    refine isLegal_let_op1_normal target (.bitcast (.float f) (.bits f.width) rfl) x _ rfl
      (by simp [LegalTarget.isLegalOp, hlegF, hlegFw, bne_iff_ne]) hx hlegFw ?_
    let Γ1 := (.bits f.width, VarKind.normal) :: Γ
    have hExt1 : CtxExtends Γ Γ1 := CtxExtends.cons _ _
    refine isLegal_let_op1_normal target (.bitcast (.float f) (.bits f.width) rfl) y _ rfl
      (by simp [LegalTarget.isLegalOp, hlegF, hlegFw, bne_iff_ne]) (hy.mono hExt1) hlegFw ?_
    let Γ2 := (.bits f.width, VarKind.normal) :: Γ1
    have hExt2 : CtxExtends Γ Γ2 := hExt1.trans (CtxExtends.cons _ _)
    refine isLegal_let_op2_normal target (mkOp f.width) (.var Γ.length) (.var Γ1.length) _ (hmkNe f.width)
      (hmkOp f.width _ hfw)
      ((ArgNormal.head target Γ hlegFw).mono (CtxExtends.cons _ _)) (ArgNormal.head target Γ1 hlegFw) hlegFw ?_
    let Γ3 := (.bits f.width, VarKind.normal) :: Γ2
    have hExt3 : CtxExtends Γ Γ3 := hExt2.trans (CtxExtends.cons _ _)
    refine isLegal_let_op1_normal target (.bitcast (.bits f.width) (.float f) rfl) (.var Γ2.length) _ rfl
      (by simp [LegalTarget.isLegalOp, hlegFw, hlegF, bne_iff_ne]) (ArgNormal.head target Γ2 hlegFw) hlegF ?_
    exact hk _ (.var Γ3.length) (hExt3.trans (CtxExtends.cons _ _)) (ArgNormal.head target Γ3 hlegF)


end LegalIsLegal

end LeanQbe.T
