module

public import LeanQbe.T.Legal
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.WPLemmas

/-!
# Base lemmas for `LeanQbe.T.LegalBase` and `LeanQbe.T.LegalEmit`

Provides the `LegalBase`-only helpers sitting strictly below `LegalEmit`, `LegalWfBaseLemmas1`,
`LegalWpBaseLemmas1`, and `LegalCheck1a`:

* Pure `BitVec`, `Bool`, and `ternaryLogic` arithmetic lemmas (`lowMask_and`, `bitVec0_eq_zero`,
  `setWidth_zero_setWidth`, `signExtend_eq_shl_ashr`, `boolCmp_spec`, `ternaryLogic_allOnes`,
  `ternaryLogic_zero`).
* Tuple evaluation and single-op `Wf` combinators (`valsTup`, `TRel_argRel_weaken'`, `sub_trans`,
  `Wf.let1`, `Wf.let2`).
* `TFlat.isLegal` context-extension invariants and single-instruction normal-op lemmas
  (`CtxExtends`, `LvlOk`, `ArgNormal`, `ArgsNormal`, `IsLegalCont`, `OpCode.isPackBridge`,
  `isLegal_let_op1_normal`, `isLegal_let_op2_normal`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## Pure `BitVec`, `Bool`, and `ternaryLogic` helpers -/

theorem lowMask_and {n w : Nat} (hnw : n ≤ w) (x : BitVec w) :
    x &&& lowMask n w = (x.setWidth n).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, lowMask, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_setWidth]
  by_cases hin : i < n
  · have hiw : w - n + i < w := by omega
    simp [hi, hin, hiw]
  · have hiw : ¬ (w - n + i < w) := by omega
    simp [hi, hin, hiw]

theorem bitVec0_eq_zero (x : BitVec 0) : x = 0#0 := Subsingleton.elim _ _

theorem setWidth_zero_setWidth {w : Nat} (x : BitVec w) :
    (x.setWidth 0).setWidth w = 0#w := by
  rw [bitVec0_eq_zero (x.setWidth 0)]; rfl

theorem signExtend_eq_shl_ashr {n w : Nat} (hn0 : 0 < n) (hnw : n < w) (a : BitVec n) :
    (a.setWidth w <<< (w - n)).sshiftRight (w - n) = a.signExtend w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi]
  have hmsb : ((a.setWidth w) <<< (w - n)).msb = a.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last]
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    have hd1 : decide (w - 1 < w) = true := decide_eq_true (by omega)
    have hd2 : decide (w - 1 < w - n) = false := decide_eq_false (by omega)
    have hd3 : decide (n - 1 < w) = true := decide_eq_true (by omega)
    have hcancel : w - 1 - (w - n) = n - 1 := by omega
    simp only [hd1, hd2, hd3, hcancel, Bool.not_false, Bool.true_and]
  by_cases hin : i < n
  · have hltw : w - n + i < w := by omega
    have hnot2 : ¬ (w ≤ i) := by omega
    have hge : ¬ (w - n + i < w - n) := by omega
    have hcancel : w - n + i - (w - n) = i := by omega
    simp [hltw, hnot2, hge, hcancel, hin, hi]
  · have hge : ¬ (w - n + i < w) := by omega
    have hnot2 : ¬ (w ≤ i) := by omega
    simp [hge, hin, hmsb, hnot2]

theorem boolCmp_spec (o : CmpOp) (a b : Bool) :
    (match o with
     | .eq => !(a ^^ b)
     | .ne => a ^^ b
     | .ult | .sgt => !a && b
     | .ule | .sge => !a || b
     | .ugt | .slt => a && !b
     | .uge | .sle => a || !b) = o.evalBool a b := by
  cases o <;> cases a <;> cases b <;> rfl

theorem ternaryLogic_allOnes {w : Nat} (a b c : BitVec w) :
    ternaryLogic a b c 0xff#8 = BitVec.allOnes w := by
  ext i hi
  rw [show (0xff#8 : BitVec 8) = BitVec.allOnes 8 from rfl]
  simp only [← BitVec.getLsbD_eq_getElem, ternaryLogic, BitVec.getLsbD_allOnes, hi, decide_true]
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  cases ha : a[i] <;> cases hb : b[i] <;> cases hc : c[i] <;>
    simp [hi, ha, hb, hc]

theorem ternaryLogic_zero {w : Nat} (a b c : BitVec w) :
    ternaryLogic a b c 0#8 = 0#w := by
  simp [ternaryLogic, List.range_succ]

/-! ## Tuple evaluation and `Wf` single-op combinators -/

@[expose]
def valsTup {ts : List Ty} (xs : Tup (Arg Val) ts) : Tup Val ts :=
  xs.map (fun _ a => a.val)

theorem TRel_argRel_weaken' {V₁ V₂ : Ty → Type} {G G' : Ctx V₁ V₂}
    (hG : ∀ p ∈ G, p ∈ G') {ts : List Ty} {as₁ : Tup (Arg V₁) ts} {as₂ : Tup (Arg V₂) ts}
    (h : TRel (ArgRel G) as₁ as₂) : TRel (ArgRel G') as₁ as₂ :=
  TRel.argRel_weaken hG h

theorem sub_trans {α : Type} {G₁ G₂ G₃ : List α}
    (h₁ : ∀ p ∈ G₁, p ∈ G₂) (h₂ : ∀ p ∈ G₂, p ∈ G₃) : ∀ p ∈ G₁, p ∈ G₃ :=
  fun p hp => h₂ p (h₁ p hp)

theorem Wf.let1 {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a u : Ty} (code : OpCode [a] [u])
    {x₁ : Arg V₁ a} {x₂ : Arg V₂ a} (hx : ArgRel G a x₁ x₂)
    {k₁ : Arg V₁ u → Expr V₁ L₁ rs} {k₂ : Arg V₂ u → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' u y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (.let_ (op1 code x₁) fun r => k₁ (.var r.fst))
           (.let_ (op1 code x₂) fun r => k₂ (.var r.fst)) :=
  .let_ (.mk code (.cons hx .nil)) fun r₁ r₂ =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) (.var r₁.fst) (.var r₂.fst) (.var List.mem_cons_self)

theorem Wf.let2 {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a b u : Ty} (code : OpCode [a, b] [u])
    {x₁ : Arg V₁ a} {x₂ : Arg V₂ a} {y₁ : Arg V₁ b} {y₂ : Arg V₂ b}
    (hx : ArgRel G a x₁ x₂) (hy : ArgRel G b y₁ y₂)
    {k₁ : Arg V₁ u → Expr V₁ L₁ rs} {k₂ : Arg V₂ u → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' u r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (.let_ (op2 code x₁ y₁) fun r => k₁ (.var r.fst))
           (.let_ (op2 code x₂ y₂) fun r => k₂ (.var r.fst)) :=
  .let_ (.mk code (.cons hx (.cons hy .nil))) fun r₁ r₂ =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) (.var r₁.fst) (.var r₂.fst) (.var List.mem_cons_self)

/-! ## `TFlat.isLegal` context invariants and single-op normal helpers -/

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

@[expose]
def OpCode.isPackBridge : {as rs : List Ty} → OpCode as rs → Bool
  | _, _, .unpair _ _ => true
  | _, _, .mkpair _ _ => true
  | _, _, _ => false

theorem TFlat.isLegal_let_of_normal (target : LegalTarget) (Γ : List (Ty × VarKind))
    (Δ : List (List Ty)) {rs ts : List Ty} (op : Op K ts) (k : TFlat rs)
    (hne : op.code.isPackBridge = false) :
    (TFlat.let_ op k).isLegal target Γ Δ =
      (target.isLegalOp op.code (isUniformImmShift op.code op.args) && target.isLegalSig ts &&
        checkLegalArgs Γ op.args && k.isLegal target (pushNormal ts Γ) Δ) := by
  rcases op with @⟨sig, code, args⟩
  cases code <;>
    (try (dsimp only [OpCode.isPackBridge] at hne; contradiction)) <;>
    dsimp only [TFlat.isLegal, TFlat.isLegal._f]

@[expose]
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

theorem CtxExtends.pushTypes {α : Type} (xs acc : List α) :
    CtxExtends acc (LeanQbe.T.pushTypes xs acc) :=
  ⟨xs.reverse, pushTypes_eq_reverse_append xs acc⟩

theorem CtxExtends.pushNormal (ts : List Ty) (Γ : List (Ty × VarKind)) :
    CtxExtends Γ (LeanQbe.T.pushNormal ts Γ) :=
  CtxExtends.pushTypes _ Γ

@[expose]
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
    LeanQbe.T.checkVarKind Γ t allowed (if lvl < Γ.length then Γ.length - 1 - lvl else Γ.length) =
      true := by
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

@[expose]
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

theorem ArgNormal.checkLegalArg {target : LegalTarget} {Γ : List (Ty × VarKind)} {t : Ty}
    {a : Arg K t} (h : ArgNormal target Γ t a) :
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

@[expose]
def ArgsNormal (target : LegalTarget) (Γ : List (Ty × VarKind)) :
    {ts : List Ty} → Tup (Arg K) ts → Prop
  | [], () => True
  | _ :: _, (x, xs) => ArgNormal target Γ _ x ∧ ArgsNormal target Γ xs

theorem ArgsNormal.mono {target : LegalTarget} {Γ Γ' : List (Ty × VarKind)}
    (hExt : CtxExtends Γ Γ') :
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
    change (LeanQbe.T.checkLegalArg Γ _ (idxArg Γ.length _) &&
      LeanQbe.T.checkLegalArgs Γ (idxArgs Γ.length _)) = true
    rw [Bool.and_eq_true]
    exact ⟨h.1.checkLegalArg, ArgsNormal.checkLegalArgs h.2⟩

abbrev IsLegalCont (target : LegalTarget) (Γ : List (Ty × VarKind)) (Δ : List (List Ty))
    {α : Type} {rs : List Ty} (P : List (Ty × VarKind) → α → Prop) (k : α → Expr K KL rs) : Prop :=
  ∀ (Γ' : List (Ty × VarKind)) (x : α),
    CtxExtends Γ Γ' → P Γ' x → (toTFlat (k x) Γ'.length Δ.length).isLegal target Γ' Δ = true

theorem isLegal_let_op1_normal (target : LegalTarget) {Γ : List (Ty × VarKind)}
    {Δ : List (List Ty)} {rs : List Ty} {t r : Ty} (code : OpCode [t] [r]) (x : Arg K t)
    (k : Tup K [r] → Expr K KL rs)
    (hne : code.isPackBridge = false)
    (hcode : target.isLegalOp code false = true)
    (hx : ArgNormal target Γ t x) (hr : target.isLegalTy r = true)
    (hk : (toTFlat (k (Γ.length, ())) ((r, .normal) :: Γ).length Δ.length).isLegal target
      ((r, .normal) :: Γ) Δ = true) :
    (toTFlat (.let_ (op1 code x) k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  change (TFlat.let_ { sig := [t], code := code, args := (idxArg Γ.length x, ()) }
    (toTFlat (k (Γ.length, ())) (Γ.length + [r].length) Δ.length)).isLegal target Γ Δ = true
  rw [TFlat.isLegal_let_of_normal target Γ Δ _ _ hne]
  have hunif : isUniformImmShift code (idxArg Γ.length x, ()) = false := by
    cases code <;> rfl
  have hchk : checkLegalArgs Γ (ts := [t]) (idxArg Γ.length x, ()) = true :=
    ArgsNormal.checkLegalArgs (target := target) (ts := [t]) (xs := (x, ())) ⟨hx, trivial⟩
  simp only [hunif, hcode, LegalTarget.isLegalSig, List.all_cons, List.all_nil, hr, Bool.and_true,
    hchk, Bool.true_and]
  have hlen : ((r, .normal) :: Γ).length = Γ.length + [r].length := by simp
  rw [pushNormal, pushTypes_eq_reverse_append]
  simpa [hlen] using hk

theorem isLegal_let_op2_normal (target : LegalTarget) {Γ : List (Ty × VarKind)}
    {Δ : List (List Ty)} {rs : List Ty} {t₁ t₂ r : Ty} (code : OpCode [t₁, t₂] [r])
    (x : Arg K t₁) (y : Arg K t₂) (k : Tup K [r] → Expr K KL rs)
    (hne : code.isPackBridge = false)
    (hcode : target.isLegalOp code
      (isUniformImmShift code (idxArg Γ.length x, idxArg Γ.length y, ())) = true)
    (hx : ArgNormal target Γ t₁ x) (hy : ArgNormal target Γ t₂ y) (hr : target.isLegalTy r = true)
    (hk : (toTFlat (k (Γ.length, ())) ((r, .normal) :: Γ).length Δ.length).isLegal target
      ((r, .normal) :: Γ) Δ = true) :
    (toTFlat (.let_ (op2 code x y) k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  let op : Op K [r] :=
    { sig := [t₁, t₂], code := code, args := (idxArg Γ.length x, idxArg Γ.length y, ()) }
  change (TFlat.let_ op
    (toTFlat (k (Γ.length, ())) (Γ.length + [r].length) Δ.length)).isLegal target Γ Δ = true
  rw [TFlat.isLegal_let_of_normal target Γ Δ op _ hne]
  have hchk : checkLegalArgs Γ (ts := [t₁, t₂]) (idxArg Γ.length x, idxArg Γ.length y, ()) = true :=
    ArgsNormal.checkLegalArgs (target := target) (ts := [t₁, t₂]) (xs := (x, y, ()))
      ⟨hx, hy, trivial⟩
  simp only [op, hcode, LegalTarget.isLegalSig, List.all_cons, List.all_nil, hr, Bool.and_true,
    hchk, Bool.true_and]
  have hlen : ((r, .normal) :: Γ).length = Γ.length + [r].length := by simp
  rw [pushNormal, pushTypes_eq_reverse_append]
  simpa [hlen] using hk

end LeanQbe.T
