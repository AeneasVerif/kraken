module

public import LeanQbe.T.LegalBaseLemmas
public import LeanQbe.T.LegalLemmas

/-!
# Target legality proofs for `LeanQbe.T.Legal` (Part 1: Invariants, Bridges, Memory & Scalar
Helpers)

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
@[simp] theorem idxArgs_cons (nv : Nat) {t : Ty} {ts : List Ty} (x : Arg K t) (xs : Tup (Arg K) ts)
  :
    idxArgs nv (ts := t :: ts) (x, xs) = (idxArg nv x, idxArgs nv xs) := rfl

@[simp] theorem idxArgs_single (nv : Nat) {t : Ty} (x : Arg K t) :
    idxArgs nv (ts := [t]) (x, ()) = (idxArg nv x, ()) := rfl

@[simp] theorem idxArgs_pair (nv : Nat) {t₁ t₂ : Ty} (x₁ : Arg K t₁) (x₂ : Arg K t₂) :
    idxArgs nv (ts := [t₁, t₂]) (x₁, x₂, ()) = (idxArg nv x₁, idxArg nv x₂, ()) := rfl

@[simp] theorem idxArgs_triple (nv : Nat) {t₁ t₂ t₃ : Ty} (x₁ : Arg K t₁) (x₂ : Arg K t₂)
  (x₃ : Arg K t₃) :
    idxArgs nv (ts := [t₁, t₂, t₃]) (x₁, x₂, x₃, ()) =
      (idxArg nv x₁, idxArg nv x₂, idxArg nv x₃, ()) := rfl

@[simp] theorem checkLegalArgs_nil (Γ : List (Ty × VarKind)) :
  checkLegalArgs Γ (ts := []) () = true := rfl
@[simp] theorem checkLegalArgs_cons (Γ : List (Ty × VarKind)) {t : Ty} {ts : List Ty}
    (x : Arg K t) (xs : Tup (Arg K) ts) :
    checkLegalArgs Γ (ts := t :: ts) (x, xs) = (checkLegalArg Γ t x && checkLegalArgs Γ xs) := rfl

theorem checkLegalArgs_single (Γ : List (Ty × VarKind)) {t : Ty} (x : Arg K t) :
    checkLegalArgs Γ (ts := [t]) (x, ()) = checkLegalArg Γ t x := by
  change (checkLegalArg Γ t x && checkLegalArgs Γ (ts := []) ()) = checkLegalArg Γ t x
  rw [checkLegalArgs_nil, Bool.and_true]

theorem checkLegalArgs_pair (Γ : List (Ty × VarKind)) {t₁ t₂ : Ty} (x₁ : Arg K t₁) (x₂ : Arg K t₂) :
    checkLegalArgs Γ (ts := [t₁, t₂]) (x₁, x₂, ()) =
      (checkLegalArg Γ t₁ x₁ && checkLegalArg Γ t₂ x₂) := by
  change (checkLegalArg Γ t₁ x₁ && (checkLegalArg Γ t₂ x₂ && checkLegalArgs Γ (ts := []) ())) = _
  rw [checkLegalArgs_nil, Bool.and_true]

theorem checkLegalArgs_triple (Γ : List (Ty × VarKind)) {t₁ t₂ t₃ : Ty}
    (x₁ : Arg K t₁) (x₂ : Arg K t₂) (x₃ : Arg K t₃) :
    checkLegalArgs Γ (ts := [t₁, t₂, t₃]) (x₁, x₂, x₃, ()) =
      (checkLegalArg Γ t₁ x₁ && checkLegalArg Γ t₂ x₂ && checkLegalArg Γ t₃ x₃) := by
  change (checkLegalArg Γ t₁ x₁ &&
    (checkLegalArg Γ t₂ x₂ && (checkLegalArg Γ t₃ x₃ && checkLegalArgs Γ (ts := []) ()))) = _
  rw [checkLegalArgs_nil, Bool.and_true, Bool.and_assoc]

@[simp] theorem toTFlat_let {rs ts : List Ty} (op : Op K ts) (k : Tup K ts → Expr K KL rs)
  (nv nl : Nat) :
    toTFlat (.let_ op k) nv nl =
      .let_ { sig := op.sig, code := op.code, args := idxArgs nv op.args }
        (toTFlat (k (Tup.levels ts nv)) (nv + ts.length) nl) := rfl

@[simp] theorem toTFlat_load {rs : List Ty} (t : Ty) (a : Arg K i64) (k : K t → Expr K KL rs)
  (nv nl : Nat) :
    toTFlat (.load t a k) nv nl = .load t (idxArg nv a) (toTFlat (k nv) (nv + 1) nl) := rfl

@[simp] theorem toTFlat_store {rs : List Ty} (t : Ty) (v : Arg K t) (a : Arg K i64)
  (k : Expr K KL rs) (nv nl : Nat) :
    toTFlat (.store v a k) nv nl = .store (idxArg nv v) (idxArg nv a) (toTFlat k nv nl) := rfl

@[simp] theorem toTFlat_call {rs : List Ty} (f : String) {as bs : List Ty}
    (args : Tup (Arg K) as) (k : Tup K bs → Expr K KL rs) (nv nl : Nat) :
    toTFlat (.call (bs := bs) f args k) nv nl =
      .call f bs (idxArgs nv args) (toTFlat (k (Tup.levels bs nv)) (nv + bs.length) nl) := rfl

@[simp] theorem toTFlat_jnz {rs : List Ty} (c : Arg K .bool) (t e : Expr K KL rs) (nv nl : Nat) :
    toTFlat (.jnz c t e) nv nl = .jnz (idxArg nv c) (toTFlat t nv nl) (toTFlat e nv nl) := rfl

@[simp] theorem toTFlat_jump {rs ts : List Ty} (j : KL ts) (args : Tup (Arg K) ts) (nv nl : Nat) :
    toTFlat (.jump (rs := rs) j args) nv nl = .jump (if j < nl then nl - 1 - j else nl)
      (idxArgs nv args) := rfl

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
    toTBlocks (.cons b bs) nv nl = .cons (toTFlat (b (Tup.levels ts nv)) (nv + ts.length) nl)
      (toTBlocks bs nv nl) := rfl

theorem TFlat.isLegal_let_unpair (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
    {rs : List Ty} (a b : Ty) (p : Arg K (.pair a b)) (k : TFlat rs) :
    (TFlat.let_ { sig := [.pair a b], code := .unpair a b, args := (p, ()) } k).isLegal target Γ Δ =
      (target.allowPackBridge && target.hasLegalLeaves (.pair a b) &&
        (match p with
         | .var idx =>
             checkVarKind Γ (.pair a b)
             (fun vk => (vk == .normal && target.isLegalTy (.pair a b)) || vk == .unpackedBridge)
             idx
         | .imm _ => false) &&
        k.isLegal target (pushTypes [(a, if target.isLegalTy a then .normal else .unpackedBridge),
          (b, if target.isLegalTy b then .normal else .unpackedBridge)] Γ) Δ) := rfl

theorem TFlat.isLegal_let_mkpair (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
    {rs : List Ty} (a b : Ty) (va : Arg K a) (vb : Arg K b) (k : TFlat rs) :
    (TFlat.let_ { sig := [a, b], code := .mkpair a b, args := (va, vb, ()) } k).isLegal target Γ Δ =
      (target.allowPackBridge && target.hasLegalLeaves (.pair a b) &&
        (match va with
         | .var idx =>
             checkVarKind Γ a
             (fun vk => (vk == .normal && target.isLegalTy a) || vk == .packedBridge) idx
         | .imm _ => target.isLegalTy a) &&
        (match vb with
         | .var idx =>
             checkVarKind Γ b
             (fun vk => (vk == .normal && target.isLegalTy b) || vk == .packedBridge) idx
         | .imm _ => target.isLegalTy b) &&
        k.isLegal target
          ((.pair a b, if target.isLegalTy (.pair a b) then .normal else .packedBridge) :: Γ) Δ) :=
          rfl

@[simp] theorem TFlat.isLegal_load (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
    {rs : List Ty} (t : Ty) (a : Arg K i64) (k : TFlat rs) :
    (TFlat.load t a k).isLegal target Γ Δ =
      (target.isLegalTy t && checkLegalArg Γ i64 a && k.isLegal target ((t, .normal) :: Γ) Δ) := rfl

@[simp] theorem TFlat.isLegal_store (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
    {rs : List Ty} (t : Ty) (v : Arg K t) (a : Arg K i64) (k : TFlat rs) :
    (TFlat.store v a k).isLegal target Γ Δ =
      (target.isLegalTy t && checkLegalArg Γ t v && checkLegalArg Γ i64 a &&
        k.isLegal target Γ Δ) := rfl

@[simp] theorem TFlat.isLegal_call (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
    {rs as : List Ty} (f : String) (bs : List Ty) (args : Tup (Arg K) as) (k : TFlat rs) :
    (TFlat.call f bs args k).isLegal target Γ Δ =
      (target.isLegalSig as && target.isLegalSig bs && checkLegalArgs Γ args &&
        k.isLegal target (pushNormal bs Γ) Δ) := rfl

@[simp] theorem TFlat.isLegal_jnz (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
    {rs : List Ty} (c : Arg K .bool) (t e : TFlat rs) :
    (TFlat.jnz c t e).isLegal target Γ Δ =
      (checkLegalArg Γ .bool c && t.isLegal target Γ Δ && e.isLegal target Γ Δ) := rfl

@[simp] theorem TFlat.isLegal_jump (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
    {rs ts : List Ty} (j : Nat) (args : Tup (Arg K) ts) :
    (TFlat.jump (rs := rs) (ts := ts) j args).isLegal target Γ Δ =
      (target.isLegalSig ts &&
        (match listGet? Δ j with
         | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
         | none => false) &&
        checkLegalArgs Γ args) := rfl

@[simp] theorem TFlat.isLegal_ret (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
    {rs : List Ty} (vs : Tup (Arg K) rs) :
    (TFlat.ret vs).isLegal target Γ Δ = (target.isLegalSig rs && checkLegalArgs Γ vs) := rfl

@[simp] theorem TFlat.isLegal_exit (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
    {rs as : List Ty} (f : String) (args : Tup (Arg K) as) :
    (TFlat.exit (rs := rs) f args).isLegal target Γ Δ =
      (target.isLegalSig as && checkLegalArgs Γ args) := rfl

@[simp] theorem TFlat.isLegal_hlt (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
    {rs : List Ty} :
    (TFlat.hlt (rs := rs)).isLegal target Γ Δ = true := rfl

@[simp] theorem TFlat.isLegal_group (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
    {rs : List Ty} {sig : List (List Ty)} (bodies : TBlocks rs sig) (k : TFlat rs) :
    (TFlat.group bodies k).isLegal target Γ Δ =
      (sig.all target.isLegalSig && bodies.isLegal target Γ (pushTypes sig Δ) &&
        k.isLegal target Γ (pushTypes sig Δ)) := rfl

@[simp] theorem TBlocks.isLegal_nil (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
    {rs : List Ty} :
    (TBlocks.nil (rs := rs)).isLegal target Γ Δ = true := rfl

@[simp] theorem TBlocks.isLegal_cons (target : LegalTarget) (Γ : List (Ty × VarKind))
  (Δ : List (List Ty))
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
  | .bits n, ht, _ =>
      ⟨by simp [ArgNormal, LegalTarget.isLegalTy, widenWidth_mem_of_supports ht], trivial⟩
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
    exact ⟨by simp [ArgNormal, LegalTarget.isLegalTy, widenWidth_eq_self_of_mem target hmem, hmem],
      trivial⟩
  | .float f, hl, _ =>
      ⟨by simpa [ArgNormal, LegalTarget.isLegalTy, LegalTarget.hasLegalLeaves] using hl, trivial⟩
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

theorem legalArg_isNormal {target : LegalTarget} {Γ : List (Ty × VarKind)}
  {LG : Ctx K (LVar target K)}
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

theorem joinArgs_isNormal {target : LegalTarget} {Γ : List (Ty × VarKind)}
  {LG : Ctx K (LVar target K)}
    (hc : CLegal target Γ LG) :
    ∀ {ts : List Ty} {xs₁ : Tup (Arg K) ts} {xs₂ : Tup (Arg (LVar target K)) ts},
      ts.all target.supportsTy = true → TRel (ArgRel LG) xs₁ xs₂ →
      ArgsNormal target Γ (joinArgs target xs₂)
  | [], (), (), _, _ => trivial
  | t :: ts, (_, _), (_, _), hts, .cons h1 h2 => by
    simp only [List.all_cons, Bool.and_eq_true] at hts
    exact ArgsNormal_tupAppend (legalArg_isNormal hc hts.1 h1) (joinArgs_isNormal hc hts.2 h2)

theorem tupSplit_levels {α : Type} : (as bs : List α) → (n : Nat) →
    tupSplit (as := as) (bs := bs) (Tup.levels (as ++ bs) n) =
      (Tup.levels as n, Tup.levels bs (n + as.length))
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
      CLegal target Γ
        (Tup.zip xs₁ (splitParams target ts (Tup.levels (target.legalSig ts) n)) ++ LG)
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
    l₂ < Δ.length ∧ listGet? Δ (Δ.length - 1 - l₂) = some (target.legalSig ts) ∧
      ts.all target.supportsTy = true

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
        l₂ < Δ.length ∧ listGet? Δ (Δ.length - 1 - l₂) = some (target.legalSig ts) ∧
          ts.all target.supportsTy = true
  | [], _, _, _, _, _, _, _, _, hm => by cases hm
  | ts₀ :: sig', Δ₀, Δ, hΔ, hsig, nl₁, ts, l₁, l₂, hm => by
    simp only [List.all_cons, Bool.and_eq_true] at hsig
    rw [Tup.levels_cons, tupLiftMap_levels_cons] at hm
    simp only [Tup.zip] at hm
    have hΔ' : Δ = (sig'.map target.legalSig).reverse ++ (target.legalSig ts₀ :: Δ₀) := by
      simp [hΔ, List.reverse_cons, List.append_assoc]
    rcases List.mem_cons.1 hm with ⟨rfl, rfl, rfl⟩ | htail
    · have hex : CtxExtends (target.legalSig ts₀ :: Δ₀) Δ :=
        ⟨(sig'.map target.legalSig).reverse, hΔ'⟩
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
    (sig : List (List Ty)) (hsig : sig.all (fun ts => ts.all target.supportsTy) = true) (nl₁ : Nat)
      :
    DLegal target (LeanQbe.T.pushTypes (sig.map target.legalSig) Δ)
      (Tup.zip (Tup.levels sig nl₁)
        (tupLiftMap target.legalSig KL (Tup.levels (sig.map target.legalSig) Δ.length)) ++ LD) := by
  intro ts l₁ l₂ hm
  rcases List.mem_append.1 hm with h | h
  · exact DLegal.pushLiftMap_aux target sig Δ (LeanQbe.T.pushTypes (sig.map target.legalSig) Δ)
      (pushTypes_eq_reverse_append _ _) hsig h
  · exact hd.mono (CtxExtends.pushTypes _ _) ts l₁ l₂ h

/-! ### Unpack/pack bridge lemmas (`unpackToLeaves`, `packFromLegal`, `unpackToLegal`) -/

def UnpackBridgeArg (target : LegalTarget) (Γ : List (Ty × VarKind)) (u : Ty) : Arg K u → Prop
  | .imm _ => True
  | .var lvl =>
    LvlOk Γ u (fun vk => (vk == .normal && target.isLegalTy u) || vk == .unpackedBridge) lvl ∧
      (target.isLegalTy u = true → LvlNormal Γ u lvl)

theorem UnpackBridgeArg.mono {target : LegalTarget} {Γ Γ' : List (Ty × VarKind)}
  (hExt : CtxExtends Γ Γ')
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
  | .var lvl =>
      LvlOk Γ u (fun vk => (vk == .normal && target.isLegalTy u) || vk == .packedBridge) lvl

theorem PackBridgeArg.mono {target : LegalTarget} {Γ Γ' : List (Ty × VarKind)}
  (hExt : CtxExtends Γ Γ')
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
    | imm c =>
        exact hk Γ _ (CtxExtends.refl Γ) (ArgsNormal_leafImm_hasLegalLeaves target (.pair a b) hl c)
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
      exact hk Γ (castArgBits heq.symm x) (CtxExtends.refl Γ)
        (PackBridgeArg.of_normal (ArgNormal.cast heq.symm hxs.1))
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
      exact hk Γ (packedToTup hp xs).1 (CtxExtends.refl Γ)
        (PackBridgeArg.of_normal (ArgsNormal_packedToTup hp hxs).1)
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
           | .var idx =>
               checkVarKind Γ2 u
               (fun vk => (vk == .normal && target.isLegalTy u) || vk == .packedBridge) idx
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
      exact LvlOk.of_head (k := kres)
        (by by_cases hL : target.isLegalTy (.pair a b) = true <;> simp [kres, hL])

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
           | .var idx =>
               checkVarKind Γ4 u
               (fun vk => (vk == .normal && target.isLegalTy u) || vk == .packedBridge) idx
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
          unpackToLegal target b (.var (Γ.length + 1)) fun lb =>
            k (tupToSplit hf (tupAppend la lb)))
            Γ1.length Δ.length).isLegal target Γ1 Δ = true
        refine unpackToLegal_isLegal target hv ha a hl'.1 (.var Γ.length) hUa fun Γ2 la hExt12
          hla => ?_
        refine unpackToLegal_isLegal target hv ha b hl'.2 (.var (Γ.length + 1)) (hUb.mono hExt12)
          fun Γ3 lb hExt23 hlb => ?_
        exact hk Γ3 (tupToSplit hf (tupAppend la lb)) (hExt1.trans (hExt12.trans hExt23))
          (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hla.mono hExt23) hlb))

/-! ### Generic single-instruction & memory emitters -/

theorem isLegal_let_op2_2res (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} {t₁ t₂ r₁ r₂ : Ty} (code : OpCode [t₁, t₂] [r₁, r₂]) (x : Arg K t₁)
      (y : Arg K t₂)
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
  have hchk : checkLegalArgs Γ (ts := [t₁, t₂]) (idxArg Γ.length x, idxArg Γ.length y, ()) = true :=
    by
    rw [← idxArgs_pair]; exact ArgsNormal.checkLegalArgs ⟨hx, hy, trivial⟩
  simp only
    [hunif, hcode, LegalTarget.isLegalSig, List.all_cons, List.all_nil, hr₁, hr₂, Bool.and_true,
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
    (hk : (toTFlat (k (Γ.length, ())) ((r, .normal) :: Γ).length Δ.length).isLegal target
      ((r, .normal) :: Γ) Δ = true) :
    (toTFlat (.let_ (op3 code x y z) k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  rw [toTFlat_let]; dsimp only [op3, Tup.levels_cons, Tup.levels_nil]
  rw [idxArgs_triple, TFlat.isLegal_let_of_normal target Γ Δ _ _ hne]
  have hunif :
    isUniformImmShift code (idxArg Γ.length x, idxArg Γ.length y, idxArg Γ.length z, ()) = false :=
    by
    cases code <;> rfl
  have hchk :
    checkLegalArgs Γ (ts := [t₁, t₂, t₃])
    (idxArg Γ.length x, idxArg Γ.length y, idxArg Γ.length z, ()) = true := by
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
  have hunif :
    isUniformImmShift code (idxArg Γ.length x, idxArg Γ.length y, idxArg Γ.length z, ()) = false :=
    by
    cases code <;> rfl
  have hchk :
    checkLegalArgs Γ (ts := [t₁, t₂, t₃])
    (idxArg Γ.length x, idxArg Γ.length y, idxArg Γ.length z, ()) = true := by
    rw [← idxArgs_triple]; exact ArgsNormal.checkLegalArgs ⟨hx, hy, hz, trivial⟩
  simp only
    [hunif, hcode, LegalTarget.isLegalSig, List.all_cons, List.all_nil, hr₁, hr₂, Bool.and_true,
    hchk, Bool.true_and]
  have hlen : (pushNormal [r₁, r₂] Γ).length = Γ.length + [r₁, r₂].length := by
    simp [pushNormal_length, Nat.add_comm]
  rw [← hlen]
  exact hk

theorem isLegal_load_normal (target : LegalTarget) {Γ : List (Ty × VarKind)} {Δ : List (List Ty)}
    {rs : List Ty} (t : Ty) (a : Arg K i64) (k : K t → Expr K KL rs)
    (ht : target.isLegalTy t = true) (ha : ArgNormal target Γ i64 a)
    (hk : (toTFlat (k Γ.length) ((t, .normal) :: Γ).length Δ.length).isLegal target
      ((t, .normal) :: Γ) Δ = true) :
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


end LegalIsLegal

end LeanQbe.T
